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
    get_parent(node).and_then(|parent| get_parent(&*parent))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
