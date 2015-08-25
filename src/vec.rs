use std::cmp::Ordering;
use std::collections::vec_deque::VecDeque;

#[derive (Debug, PartialEq, Eq)]
enum Action<T> {
    /// Skip the next n characters.
    Retain(usize),
    /// Delete the next n characters.
    Delete(usize),
    /// Insert the given text at the current position.
    Insert(Vec<T>)
}

pub struct Operation<T>(VecDeque<Action<T>>);

impl<T> Operation<T> {

    pub fn new() -> Operation<T> {
        Operation(VecDeque::new())
    }

    pub fn add_retain(&mut self, n: usize) {
        match self.0.pop_back() {
            Option::None => self.0.push_back(Action::Retain(n)),
            Option::Some(a) => match a {
                Action::Retain(m) => self.0.push_back(Action::Retain(n+m)),
                _ => {
                    self.0.push_back(a);
                    self.0.push_back(Action::Retain(n));
                }
            }
        }
    }

    pub fn add_insert(&mut self, s: Vec<T>) {
        match self.0.pop_back() {
            Option::None => self.0.push_back(Action::Insert(s)),
            Option::Some(a) => match a {
                Action::Delete(n) => {
                    self.add_insert(s);
                    self.0.push_back(Action::Delete(n));
                },
                Action::Insert(mut t) => {
                    t.extend(s);
                    self.0.push_back(Action::Insert(t));
                },
                _ => {
                    self.0.push_back(a);
                    self.0.push_back(Action::Insert(s));
                }
            }
        }
    }

    pub fn add_delete(&mut self, n: usize) {
        match self.0.pop_back() {
            Option::None => self.0.push_back(Action::Delete(n)),
            Option::Some(a) => match a {
                Action::Delete(m) => self.0.push_back(Action::Delete(n+m)),
                _ => {
                    self.0.push_back(a);
                    self.0.push_back(Action::Delete(n));
                }
            }
        }
    }

}

#[test]
fn add_retain() {
    let mut o = Operation::new();
    o.add_retain(5);
    assert_eq!(
        o.0.into_iter().collect::<Vec<Action<i32>>>(),
        vec![Action::Retain(5)]
    );
}

#[test]
fn add_retain_add_retain() {
    let mut o = Operation::new();
    o.add_retain(5);
    o.add_retain(3);
    assert_eq!(
        o.0.into_iter().collect::<Vec<Action<i32>>>(),
        vec![Action::Retain(8)]
    );
}

#[test]
fn add_insert() {
    let mut o = Operation::new();
    o.add_insert(vec![1,2,3]);
    assert_eq!(
        o.0.into_iter().collect::<Vec<Action<i32>>>(),
        vec![Action::Insert(vec![1,2,3])]
    );
}

#[test]
fn add_insert_add_retain() {
    let mut o = Operation::new();
    o.add_insert(vec![1,2,3]);
    o.add_retain(3);
    assert_eq!(
        o.0.into_iter().collect::<Vec<Action<i32>>>(),
        vec![Action::Insert(vec![1,2,3]), Action::Retain(3)]
    );
}

#[test]
fn add_insert_add_insert() {
    let mut o = Operation::new();
    o.add_insert(vec![1,2,3]);
    o.add_insert(vec![4,5]);
    assert_eq!(
        o.0.into_iter().collect::<Vec<Action<i32>>>(),
        vec![Action::Insert(vec![1,2,3,4,5])]
    );
}

#[test]
fn add_insert_add_delete() {
    let mut o = Operation::new();
    o.add_insert(vec![1,2,3]);
    o.add_delete(2);
    assert_eq!(
        o.0.into_iter().collect::<Vec<Action<i32>>>(),
        vec![Action::Insert(vec![1,2,3]), Action::Delete(2)]
    );
}

#[test]
fn add_retain_add_insert() {
    let mut o = Operation::new();
    o.add_retain(3);
    o.add_insert(vec![1,2,3]);
    assert_eq!(
        o.0.into_iter().collect::<Vec<Action<i32>>>(),
        vec![Action::Retain(3), Action::Insert(vec![1,2,3])]
    );
}

#[test]
fn add_delete() {
    let mut o = Operation::new();
    o.add_delete(2);
    assert_eq!(
        o.0.into_iter().collect::<Vec<Action<i32>>>(),
        vec![Action::Delete(2)]
    );
}

#[test]
fn add_delete_add_delete() {
    let mut o = Operation::new();
    o.add_delete(2);
    o.add_delete(3);
    assert_eq!(
        o.0.into_iter().collect::<Vec<Action<i32>>>(),
        vec![Action::Delete(5)]
    );
}

#[test]
fn add_delete_add_insert() {
    let mut o = Operation::new();
    o.add_delete(2);
    o.add_insert(vec![1,2,3]);
    assert_eq!(
        o.0.into_iter().collect::<Vec<Action<i32>>>(),
        vec![Action::Insert(vec![1,2,3]), Action::Delete(2)]
    );
}

fn split_off<T: Clone>(v: &mut Vec<T>, n: usize) -> Vec<T> {
    let new_vector = v.split_at(n).1.into();
    v.truncate(n);
    new_vector
}

#[test]
fn split_off_3_of_5() {
    let mut v = vec![1,2,3,4,5];
    let w = split_off(&mut v, 3);
    assert_eq!(v, [1,2,3]);
    assert_eq!(w, [4,5]);
}

#[test]
fn split_off_0_of_3() {
    let mut v = vec![1,2,3];
    let w = split_off(&mut v, 0);
    assert_eq!(v, []);
    assert_eq!(w, [1,2,3]);
}

#[test]
fn split_off_1_of_3() {
    let mut v = vec![1,2,3];
    let w = split_off(&mut v, 1);
    assert_eq!(v, [1]);
    assert_eq!(w, [2,3]);
}

#[test]
fn split_off_3_of_3() {
    let mut v = vec![1,2,3];
    let w = split_off(&mut v, 3);
    assert_eq!(v, [1,2,3]);
    assert_eq!(w, []);
}

pub fn compose<T: Clone>(aa: &mut Operation<T>, bb: &mut Operation<T>) -> Option<Operation<T>> {
    let mut res = Operation::new();
    loop {
        match (aa.0.pop_back(), bb.0.pop_back()) {
            (Option::None, Option::None) => return Option::Some(res),
            (Option::Some(a), Option::Some(b)) => {
                match (a, b) {
                    (Action::Delete(n), b) => {
                        bb.0.push_back(b);
                        res.add_delete(n);
                    },
                    (a, Action::Insert(s)) => {
                        aa.0.push_back(a);
                        res.add_insert(s);
                    },
                    (Action::Retain(n), Action::Retain(m)) => match n.cmp(&m) {
                        Ordering::Less => {
                            bb.0.push_back(Action::Retain(m-n));
                            res.add_retain(n);
                        },
                        Ordering::Equal => {
                            res.add_retain(n);
                        },
                        Ordering::Greater => {
                            aa.0.push_back(Action::Retain(n-m));
                            res.add_retain(m);
                        }
                    },
                    (Action::Retain(r), Action::Delete(d)) => match r.cmp(&d) {
                        Ordering::Less => {
                            bb.0.push_back(Action::Delete(d-r));
                            res.add_delete(r);
                        },
                        Ordering::Equal => {
                            res.add_delete(d);
                        },
                        Ordering::Greater => {
                            aa.0.push_back(Action::Retain(r-d));
                            res.add_delete(d)
                        }
                    },
                    (Action::Insert(mut i), Action::Retain(m)) => match i.len().cmp(&m) {
                        Ordering::Less => {
                            bb.0.push_back(Action::Retain(m-i.len()));
                            res.add_insert(i);
                        },
                        Ordering::Equal => {
                            res.add_insert(i);
                        },
                        Ordering::Greater => {
                            let after = split_off(&mut i, m);
                            aa.0.push_back(Action::Insert(after));
                            res.add_insert(i);
                        }
                    },
                    (Action::Insert(mut i), Action::Delete(d)) => match i.len().cmp(&d) {
                        Ordering::Less => {
                            bb.0.push_back(Action::Delete(d-i.len()));
                        },
                        Ordering::Equal => (),
                        Ordering::Greater => {
                            bb.0.push_back(Action::Insert(split_off(&mut i, d)))
                        }
                    }
                }
            },
            (Option::Some(Action::Delete(d)), Option::None) => res.add_delete(d),
            (Option::None, Option::Some(Action::Insert(i))) => res.add_insert(i),
            (_, _) => return Option::None
        }
    }
}
