use std::collections::HashMap;

#[derive(Hash, Eq, PartialEq, Debug)]
enum Key {
    Literal(String),
    Param(String),
    IntParam(String),
    Wildcard
}

fn to_key(s: &str) -> Result<Key, String> {
    if s.starts_with("<") {
        let i: String = s.chars().skip(1).take_while(|c| c != &'>').collect();
        let sp: Vec<&str> = i.split(":").collect();
        if sp.len() == 1 {
            return Ok(Key::Param(sp[0].into()));
        } else if sp.len() == 2 {
            match sp[1] {
                "int" => {
                    return Ok(Key::IntParam(sp[0].into()));
                },
                unknown_type => return Err(format!("Unkown type: {0}.", unknown_type))
            }
        } else {
            return Err("Syntax error on path part.".into());
        }
    } else if s == "*" {
        Ok(Key::Wildcard)
    } else {
        Ok(Key::Literal(s.into()))
    }
}

#[derive(Debug)]
struct RouteData<T> {
    value: T,
    trailing: bool
}

#[derive(Debug)]
pub struct TrieRouterRecognizerBuilder<T> {
    data: Option<RouteData<T>>,
    literals: HashMap<String, TrieRouterRecognizerBuilder<T>>,
    int_params: HashMap<String, TrieRouterRecognizerBuilder<T>>,
    params: HashMap<String, TrieRouterRecognizerBuilder<T>>,
    wildcard: Option<Box<TrieRouterRecognizerBuilder<T>>>,
}

#[derive(Debug)]
pub struct TrieRouterRecognizer<T>
{
    data: Option<RouteData<T>>,
    children: Vec<(Key, TrieRouterRecognizer<T>)>
}

impl<T> TrieRouterRecognizer<T> {

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

                for &(ref key, ref child_trie) in self.children.iter() {
                    match *key {
                        Key::Literal(ref literal) if literal == part => {
                            return child_trie.recognize_internal(path, params);
                        },
                        Key::IntParam(ref int_param) => {
                            let i: Result<i64, _> = part.parse();
                            if let Err(_) = i {
                                continue;
                            }
                            let res = child_trie
                                        .recognize_internal(
                                            path.clone(),
                                            vec![(int_param.to_string(), Param::Int(i.unwrap()))]);
                            match res {
                                Some((v, child_params)) => {
                                    params.extend(child_params);
                                    return Some((v, params));
                                },
                                None => continue
                            }
                        },
                        Key::Param(ref param) => {
                            let res = child_trie
                                        .recognize_internal(
                                            path.clone(),
                                            vec![(param.to_string(), Param::Str(part.to_string()))]);
                            match res {
                                Some((v, child_params)) => {
                                    params.extend(child_params);
                                    return Some((v, params));
                                },
                                None => continue
                            }
                        },
                        Key::Wildcard => {
                            return child_trie.recognize_internal(path, params);
                        },
                        Key::Literal(_) => continue
                    }
                }

                None
            }
        }
    }
}

#[derive(Eq, PartialEq, Debug)]
pub enum Param {
    Str(String),
    Int(i64)
}

impl<T> TrieRouterRecognizerBuilder<T> {

    pub fn build(self) -> Result<TrieRouterRecognizer<T>, String>
    {
        let mut literals =
            self.literals
                .into_iter()
                .map(|(k, v)| (v.build().map(|v| (Key::Literal(k), v))))
                .collect::<Result<Vec<_>, _>>()?;

        let int_params =
            self.int_params
                .into_iter()
                .map(|(k, v)| (v.build().map(|v| (Key::IntParam(k), v))))
                .collect::<Result<Vec<_>, _>>()?;

        let params =
            self.params
                .into_iter()
                .map(|(k, v)| (v.build().map(|v| (Key::Param(k), v))))
                .collect::<Result<Vec<_>, _>>()?;

        literals.extend(int_params);
        literals.extend(params);

        if let Some(trie) = self.wildcard {
            literals.push((Key::Wildcard, trie.build()?));
        }

        Ok(TrieRouterRecognizer {
            data: self.data,
            children: literals
        })
    }

    pub fn new() -> TrieRouterRecognizerBuilder<T> {
        TrieRouterRecognizerBuilder {
            data: None,
            literals: HashMap::new(),
            int_params: HashMap::new(),
            params: HashMap::new(),
            wildcard: None
        }
    }

    pub fn add(mut self, path: &str, value: T) -> Result<Self, String> {
        if !path.starts_with("/") {
            Err("Route must start with '/'.".into())
        } else {
            {
                let path = path.split("/").skip(1).into_iter();
                self.add_internal(path, value)?;
            }
            Ok(self)
        }
    }

    fn add_internal<'a, I>(&'a mut self, mut path: I, value: T) -> Result<&mut Self, String>
        where I: ::std::iter::Iterator<Item = &'a str>
    {
        match path.next() {
            Some("") => {
                self.data = Some(RouteData {
                    value: value,
                    trailing: true,
                });
                Ok(self)
            },
            None => {
                self.data = Some(RouteData {
                    value: value,
                    trailing: false,
                });
                Ok(self)
            },
            Some(part) => {

                match to_key(part)? {
                    Key::Literal(literal) => {
                        self.literals
                            .entry(literal)
                            .or_insert(TrieRouterRecognizerBuilder::new())
                            .add_internal(path, value)
                    },
                    Key::Param(param) => {
                        self.params
                            .entry(param)
                            .or_insert(TrieRouterRecognizerBuilder::new())
                            .add_internal(path, value)
                    },
                    Key::IntParam(param) => {
                        self.int_params
                            .entry(param)
                            .or_insert(TrieRouterRecognizerBuilder::new())
                            .add_internal(path, value)
                    }
                    Key::Wildcard => {
                        if self.wildcard.is_none() {
                            self.wildcard = Some(Box::new(TrieRouterRecognizerBuilder::new()));
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
    let router =
        TrieRouterRecognizerBuilder::new()
        .add("/", 1).unwrap()
        .build().unwrap();

    assert_eq!(router.recognize("/").unwrap(), (&1, vec![]));
    assert_eq!(router.recognize("").unwrap(), (&1, vec![]));
}

#[test]
fn root_empty() {
    match TrieRouterRecognizerBuilder::new().add("", 1) {
        Err(err) => assert_eq!(err, "Route must start with '/'.".to_string()),
        Ok(_) => panic!("Routes that doesn't start with '/' should fail.")
    }
}

#[test]
fn trailing_nontrailing() {
    let router =
        TrieRouterRecognizerBuilder::new()
        .add("/trailing/", 1).unwrap()
        .add("/non-trailing", 2).unwrap()
        .build().unwrap();

    assert_eq!(router.recognize("/trailing/").unwrap(), (&1, vec![]));
    assert_eq!(router.recognize("/trailing").unwrap(), (&1, vec![]));
    assert_eq!(router.recognize("/non-trailing").unwrap(), (&2, vec![]));
    assert_eq!(router.recognize("/non-trailing/"), None);
}

#[test]
fn params() {
    let router =
        TrieRouterRecognizerBuilder::new()
        .add("/foo/<bar>", 1).unwrap()
        .add("/foo/<bar>/rall/<snall>", 2).unwrap()
        .build().unwrap();

    assert_eq!(
        router.recognize("/foo/11").unwrap(),
        (&1, vec![("bar".into(), Param::Str("11".into()))]));
    assert_eq!(
        router.recognize("/foo/21/rall/22").unwrap(),
        (&2, vec![("bar".into(), Param::Str("21".into())), ("snall".into(), Param::Str("22".into()))]));
}

#[test]
fn int_params() {
    let router =
        TrieRouterRecognizerBuilder::new()
        .add("/foo/<bar:int>", 1).unwrap()
        .build().unwrap();

    assert_eq!(
        router.recognize("/foo/11").unwrap(),
        (&1, vec![("bar".into(), Param::Int(11))]));
}

#[test]
fn multiple_params_on_same_depth() {
    let router =
        TrieRouterRecognizerBuilder::new()
        .add("/foo/<foo1>/first", 1).unwrap()
        .add("/foo/<foo2>/second", 2).unwrap()
        .add("/foo/<foo3>/second/<bar1>/third", 3).unwrap()
        .add("/foo/<foo4>/second/<bar2>/forth", 4).unwrap()
        .build().unwrap();

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
    let router =
        TrieRouterRecognizerBuilder::new()
        .add("/foo/<foo>/bar/<foo>", 1).unwrap()
        .build().unwrap();

    assert_eq!(
        router.recognize("/foo/11/bar/12").unwrap(),
        (&1, vec![("foo".into(), Param::Str("11".into())), ("foo".into(), Param::Str("12".into()))]));
}

#[test]
fn wildcard() {
    let router =
        TrieRouterRecognizerBuilder::new()
        .add("/foo/*", 1).unwrap()
        .add("/foo/*/bar", 2).unwrap()
        .build().unwrap();

    assert_eq!(
        router.recognize("/foo/11").unwrap(),
        (&1, vec![]));
    assert_eq!(
        router.recognize("/foo/11/bar").unwrap(),
        (&2, vec![]));
}

#[test]
fn literal_before_params() {
    let router =
        TrieRouterRecognizerBuilder::new()
        .add("/foo/literal", 1).unwrap()
        .add("/foo/<param>", 2).unwrap()
        .build().unwrap();

    assert_eq!(
        router.recognize("/foo/literal").unwrap(),
        (&1, vec![]));
    assert_eq!(
        router.recognize("/foo/21").unwrap(),
        (&2, vec![("param".into(), Param::Str("21".into()))]));
}