#![crate_name = "red_black_tree"]

use std::cell::RefCell;
use std::rc::{Rc, Weak};

pub enum COLOR {
    RED,
    BLACK,
}

pub struct Node {
    key: i32,
    parent: RefCell<Weak<Node>>,
    left: RefCell<Option<Rc<Node>>>,
    right: RefCell<Option<Rc<Node>>>,
    color: COLOR,
}

impl Node {
    pub fn new(
        key: i32,
        left: Option<&Rc<Node>>,
        right: Option<&Rc<Node>>,
        color: COLOR,
    ) -> Rc<Node> {
        let node = Rc::new(Node {
            key,
            parent: RefCell::new(Weak::new()),
            left: RefCell::new(None),
            right: RefCell::new(None),
            color,
        });
        if let Some(left) = left {
            *left.parent.borrow_mut() = Rc::downgrade(&node);
            *node.left.borrow_mut() = Some(Rc::clone(&left));
        }
        if let Some(right) = right {
            *right.parent.borrow_mut() = Rc::downgrade(&node);
            *node.right.borrow_mut() = Some(Rc::clone(&right));
        }
        node
    }
}

/// Return the parent of the node
/// ```
/// use red_black_tree::{Node, COLOR};
/// use std::rc::Rc;
///
/// let left = Node::new(10, None, None, COLOR::RED);
/// let right = Node::new(30, None, None, COLOR::RED);
/// let root = Node::new(20, Some(&left), Some(&right), COLOR::BLACK);
///
/// assert!(Rc::ptr_eq(&root, &red_black_tree::get_parent(&left).unwrap()));
/// assert!(Rc::ptr_eq(&root, &red_black_tree::get_parent(&right).unwrap()));
/// assert!(red_black_tree::get_parent(&root).is_none());
/// ```
pub fn get_parent(node: &Node) -> Option<Rc<Node>> {
    node.parent.borrow().upgrade()
}

/// Return the grandparent of the node
/// ```
/// use red_black_tree::{Node, COLOR};
/// use std::rc::Rc;
///
/// let left_left = Node::new(0, None, None, COLOR::BLACK);
/// let left = Node::new(10, Some(&left_left), None, COLOR::RED);
/// let right = Node::new(30, None, None, COLOR::RED);
/// let root = Node::new(20, Some(&left), Some(&right), COLOR::BLACK);
///
/// assert!(Rc::ptr_eq(&root, &red_black_tree::get_grandparent(&left_left).unwrap()));
/// assert!(red_black_tree::get_grandparent(&left).is_none());
/// assert!(red_black_tree::get_grandparent(&right).is_none());
/// assert!(red_black_tree::get_grandparent(&root).is_none());
/// ```
pub fn get_grandparent(node: &Node) -> Option<Rc<Node>> {
    get_parent(node).and_then(|parent| get_parent(parent.as_ref()))
}

/// Return the sibling of the node
/// ```
/// use red_black_tree::{Node, COLOR};
/// use std::rc::Rc;
///
/// let left_left = Node::new(0, None, None, COLOR::BLACK);
/// let right_right = Node::new(40, None, None, COLOR::BLACK);
/// let left = Node::new(10, Some(&left_left), None, COLOR::RED);
/// let right = Node::new(30, None, Some(&right_right), COLOR::RED);
/// let root = Node::new(20, Some(&left), Some(&right), COLOR::BLACK);
///
/// assert!(Rc::ptr_eq(&right, &red_black_tree::get_sibling(Rc::clone(&left)).unwrap()));
/// assert!(Rc::ptr_eq(&left, &red_black_tree::get_sibling(Rc::clone(&right)).unwrap()));
/// assert!(red_black_tree::get_sibling(Rc::clone(&left_left)).is_none());
/// assert!(red_black_tree::get_sibling(Rc::clone(&right_right)).is_none());
/// assert!(red_black_tree::get_sibling(Rc::clone(&root)).is_none());
/// ```
pub fn get_sibling(node: Rc<Node>) -> Option<Rc<Node>> {
    get_parent(node.as_ref()).and_then(|parent| {
        parent
            .left
            .borrow()
            .as_ref()
            .and(parent.right.borrow().as_ref())
            .and_then(|right| {
                if Rc::ptr_eq(&node, &right) {
                    Some(Rc::clone(parent.left.borrow().as_ref().unwrap()))
                } else {
                    Some(Rc::clone(right))
                }
            })
    })
}

/// Return the uncle of the node
/// ```
/// use red_black_tree::{Node, COLOR};
/// use std::rc::Rc;
///
/// let left_left = Node::new(0, None, None, COLOR::BLACK);
/// let right_right = Node::new(40, None, None, COLOR::BLACK);
/// let left = Node::new(10, Some(&left_left), None, COLOR::RED);
/// let right = Node::new(30, None, Some(&right_right), COLOR::RED);
/// let root = Node::new(20, Some(&left), Some(&right), COLOR::BLACK);
///
/// assert!(Rc::ptr_eq(&right, &red_black_tree::get_uncle(Rc::clone(&left_left)).unwrap()));
/// assert!(Rc::ptr_eq(&left, &red_black_tree::get_uncle(Rc::clone(&right_right)).unwrap()));
/// assert!(red_black_tree::get_uncle(Rc::clone(&left)).is_none());
/// assert!(red_black_tree::get_uncle(Rc::clone(&right)).is_none());
/// assert!(red_black_tree::get_uncle(Rc::clone(&root)).is_none());
/// ```
pub fn get_uncle(node: Rc<Node>) -> Option<Rc<Node>> {
    get_parent(node.as_ref()).and_then(|parent| get_sibling(Rc::clone(&parent)))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
