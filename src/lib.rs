use std::collections::HashMap;

#[derive(Hash, Eq, PartialEq, Debug)]
enum Key {
    Literal(String),
    Param(String),
    IntParam(String),
    Wildcard
}

fn to_key(s: &str) -> Key {
    if s.starts_with("<") {
        let i: String = s.chars().skip(1).take_while(|c| c != &'>').collect();
        let sp: Vec<&str> = i.split(":").collect();
        if sp.len() == 1 {
            return Key::Param(sp[0].into());
        } else if sp.len() == 2 {
            match sp[1] {
                "int" => {
                    return Key::IntParam(sp[0].into());
                },
                _ => panic!("what -- see below..,")
            }
        } else {
            panic!("what to do. must return Result");
        }
        // Key::Param(s.chars().skip(1).take_while(|c| c != &'>').collect())
    } else if s == "*" {
        Key::Wildcard
    } else {
        Key::Literal(s.into())
    }
}

#[derive(Debug)]
struct RouteData<T> {
    value: T,
    trailing: bool
}

#[derive(Debug)]
pub struct TrieRouterRecognizer<T> {
    data: Option<RouteData<T>>,
    literals: HashMap<String, TrieRouterRecognizer<T>>,
    int_params: HashMap<String, TrieRouterRecognizer<T>>,
    params: HashMap<String, TrieRouterRecognizer<T>>,
    wildcard: Option<Box<TrieRouterRecognizer<T>>>,
}

#[derive(Eq, PartialEq, Debug)]
pub enum Param {
    Str(String),
    Int(i64)
}

impl<T> TrieRouterRecognizer<T> {
    pub fn new() -> TrieRouterRecognizer<T> {
        TrieRouterRecognizer {
            data: None,
            literals: HashMap::new(),
            int_params: HashMap::new(),
            params: HashMap::new(),
            wildcard: None
        }
    }

    pub fn add(&mut self, path: &str, value: T) {
        let path = path.split("/").skip(1).into_iter();
        self.add_internal(path, value);
    }

    pub fn recognize<'a>(&'a self, path: &str) -> Option<(&'a T, Vec<(String, Param)>)> {
        if path == "" || path == "/" {
            return self.data.as_ref().map(|&RouteData{value: ref v, ..}| (v, vec![]));
        }

        let path = path.split("/").skip(1).into_iter();
        self.recognize_internal(path, vec![])
    }

    fn recognize_internal<'a, 'b, I>(&'a self, mut path: I, mut params: Vec<(String, Param)>) -> Option<(&'a T, Vec<(String, Param)>)>
        where I: ::std::iter::Iterator<Item = &'b str> + Clone
    {
        match path.next() {
            Some("") => {
                if let Some(RouteData{trailing: true, ..}) = self.data {
                    self.data.as_ref().map(|&RouteData{value: ref v, ..}| (v, params))
                } else {
                    None
                }
            },
            None => {
                self.data.as_ref().map(|&RouteData{value: ref v, ..}| (v, params))
            },
            Some(part) => {
                if let Some((_, child_trie)) = self.literals.iter().find(|&(k, _)| k == part) {
                    return child_trie.recognize_internal(path, params);
                }

                if self.int_params.len() > 1 {
                    let mut p = self.int_params.iter();
                    while let Some((k, child_trie)) = p.next() {
                        let i: Result<i64, _> = part.parse();
                        if let Err(_) = i {
                            continue;
                        }
                        let res = child_trie
                                    .recognize_internal(
                                        path.clone(),
                                        vec![(k.to_string(), Param::Int(i.unwrap()))]);
                        match res {
                            Some((v, child_params)) => {
                                params.extend(child_params);
                                return Some((v, params));
                            },
                            None => continue
                        }
                    }
                } else if let Some((k, child_trie)) = self.int_params.iter().next() {
                    if let Ok(i) = part.parse() {
                        params.push((k.to_string(), Param::Int(i)));
                        return child_trie.recognize_internal(path, params);
                    }
                }

                if self.params.len() > 1 {
                    let mut p = self.params.iter();
                    while let Some((k, child_trie)) = p.next() {
                        let res = child_trie
                                    .recognize_internal(
                                        path.clone(),
                                        vec![(k.to_string(), Param::Str(part.to_string()))]);
                        match res {
                            Some((v, child_params)) => {
                                params.extend(child_params);
                                return Some((v, params));
                            },
                            None => continue
                        }
                    }
                } else if let Some((k, child_trie)) = self.params.iter().next() {
                    params.push((k.to_string(), Param::Str(part.to_string())));
                    return child_trie.recognize_internal(path, params);
                }

                if let Some(ref child_trie) = self.wildcard {
                    return child_trie.recognize_internal(path, params);
                }

                None
            }
        }
    }

    fn add_internal<'a, I>(&'a mut self, mut path: I, value: T)
        where I: ::std::iter::Iterator<Item = &'a str>
    {
        match path.next() {
            Some("") => {
                self.data = Some(RouteData {
                    value: value,
                    trailing: true,
                });
            },
            None => {
                self.data = Some(RouteData {
                    value: value,
                    trailing: false,
                });
            },
            Some(part) => {

                match to_key(part) {
                    Key::Literal(literal) =>
                        self.literals
                            .entry(literal)
                            .or_insert(TrieRouterRecognizer::new())
                            .add_internal(path, value),
                    Key::Param(param) =>
                        self.params
                            .entry(param)
                            .or_insert(TrieRouterRecognizer::new())
                            .add_internal(path, value),
                    Key::IntParam(param) =>
                        self.int_params
                            .entry(param)
                            .or_insert(TrieRouterRecognizer::new())
                            .add_internal(path, value),
                    Key::Wildcard => {
                        if self.wildcard.is_none() {
                            self.wildcard = Some(Box::new(TrieRouterRecognizer::new()));
                        }

                        self.wildcard
                            .as_mut()
                            .expect("just initialized 'wildcard'. Something's very wrong.")
                            .add_internal(path, value)
                    }
                }

            }
        }
    }
}

#[test]
fn root_slash() {
    let mut router = TrieRouterRecognizer::new();
    router.add("/", 1);
    assert_eq!(router.recognize("/").unwrap(), (&1, vec![]));
    assert_eq!(router.recognize("").unwrap(), (&1, vec![]));
}

// #[test]
// fn root_empty() {
//     let mut router = TrieRouterRecognizer::new();
//     router.add("", 1);
//     // should fail in some way
//     // builder pattern with Result?

//     // assert_eq!(router.recognize("").unwrap(), (&1, vec![]));
//     // assert_eq!(router.recognize("/"), None);
// }

#[test]
fn trailing_nontrailing() {
    let mut router = TrieRouterRecognizer::new();
    router.add("/trailing/", 1);
    router.add("/non-trailing", 2);

    assert_eq!(router.recognize("/trailing/").unwrap(), (&1, vec![]));
    assert_eq!(router.recognize("/trailing").unwrap(), (&1, vec![]));
    assert_eq!(router.recognize("/non-trailing").unwrap(), (&2, vec![]));
    assert_eq!(router.recognize("/non-trailing/"), None);
}

#[test]
fn params() {
    let mut router = TrieRouterRecognizer::new();
    router.add("/foo/<bar>", 1);
    router.add("/foo/<bar>/rall/<snall>", 2);

    assert_eq!(
        router.recognize("/foo/11").unwrap(),
        (&1, vec![("bar".into(), Param::Str("11".into()))]));
    assert_eq!(
        router.recognize("/foo/21/rall/22").unwrap(),
        (&2, vec![("bar".into(), Param::Str("21".into())), ("snall".into(), Param::Str("22".into()))]));
}

#[test]
fn int_params() {
    let mut router = TrieRouterRecognizer::new();
    router.add("/foo/<bar:int>", 1);

    assert_eq!(
        router.recognize("/foo/11").unwrap(),
        (&1, vec![("bar".into(), Param::Int(11))]));
}

#[test]
fn multiple_params_on_same_depth() {
    let mut router = TrieRouterRecognizer::new();
    router.add("/foo/<foo1>/first", 1);
    router.add("/foo/<foo2>/second", 2);
    router.add("/foo/<foo3>/second/<bar1>/third", 3);
    router.add("/foo/<foo4>/second/<bar2>/forth", 4);

    assert_eq!(
        router.recognize("/foo/11/first").unwrap(),
        (&1, vec![("foo1".into(), Param::Str("11".into()))]));
    assert_eq!(
        router.recognize("/foo/21/second").unwrap(),
        (&2, vec![("foo2".into(), Param::Str("21".into()))]));
    assert_eq!(
        router.recognize("/foo/31/second/32/third").unwrap(),
        (&3, vec![("foo3".into(), Param::Str("31".into())), ("bar1".into(), Param::Str("32".into()))]));
    assert_eq!(
        router.recognize("/foo/41/second/42/forth").unwrap(),
        (&4, vec![("foo4".into(), Param::Str("41".into())), ("bar2".into(), Param::Str("42".into()))]));
}

#[test]
fn multiple_params_with_same_name() {
    // test to highlight a problem with returning params as map over param name.
    let mut router = TrieRouterRecognizer::new();
    router.add("/foo/<foo>/bar/<foo>", 1);

    assert_eq!(
        router.recognize("/foo/11/bar/12").unwrap(),
        (&1, vec![("foo".into(), Param::Str("11".into())), ("foo".into(), Param::Str("12".into()))]));
}

#[test]
fn wildcard() {
    let mut router = TrieRouterRecognizer::new();
    router.add("/foo/*", 1);

    assert_eq!(
        router.recognize("/foo/11").unwrap(),
        (&1, vec![]));
}

#[test]
fn literal_before_params() {
    let mut router = TrieRouterRecognizer::new();
    router.add("/foo/literal", 1);
    router.add("/foo/<param>", 2);

    assert_eq!(
        router.recognize("/foo/literal").unwrap(),
        (&1, vec![]));
    assert_eq!(
        router.recognize("/foo/21").unwrap(),
        (&2, vec![("param".into(), Param::Str("21".into()))]));
}