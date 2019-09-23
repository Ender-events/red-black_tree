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

    pub fn valid(&self) -> bool {
        self.is_black() && self.valid_rec().0
    }

    fn is_red(&self) -> bool {
        match self.color {
            COLOR::RED => true,
            COLOR::BLACK => false,
        }
    }

    fn is_black(&self) -> bool {
        !self.is_red()
    }

    fn valid_rec(&self) -> (bool, u32) {
        let (left_bool, left_black) = if let Some(left) = self.left.borrow().as_ref() {
            left.valid_rec()
        } else {
            (true, 0)
        };
        let (right_bool, right_black) = if let Some(right) = self.right.borrow().as_ref() {
            right.valid_rec()
        } else {
            (true, 0)
        };
        let color_child = if self.is_red() {
            let left_color = if let Some(left) = self.left.borrow().as_ref() {
                left.is_black()
            } else {
                true
            };
            let right_color = if let Some(right) = self.right.borrow().as_ref() {
                right.is_black()
            } else {
                true
            };
            left_color && right_color
        } else {
            true
        };

        (
            left_bool && right_bool && left_black == right_black && color_child,
            left_black + self.is_black() as u32,
        )
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
///
/// assert!(root.valid());
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
///
/// assert!(!root.valid());
/// ```
pub fn get_grandparent(node: &Node) -> Option<Rc<Node>> {
    get_parent(node).and_then(|parent| get_parent(parent.as_ref()))
}

/// Return the sibling of the node
/// ```
/// use red_black_tree::{Node, COLOR};
/// use std::rc::Rc;
///
/// let left_left = Node::new(0, None, None, COLOR::RED);
/// let right_right = Node::new(40, None, None, COLOR::RED);
/// let left = Node::new(10, Some(&left_left), None, COLOR::BLACK);
/// let right = Node::new(30, None, Some(&right_right), COLOR::BLACK);
/// let root = Node::new(20, Some(&left), Some(&right), COLOR::BLACK);
///
/// assert!(Rc::ptr_eq(&right, &red_black_tree::get_sibling(Rc::clone(&left)).unwrap()));
/// assert!(Rc::ptr_eq(&left, &red_black_tree::get_sibling(Rc::clone(&right)).unwrap()));
/// assert!(red_black_tree::get_sibling(Rc::clone(&left_left)).is_none());
/// assert!(red_black_tree::get_sibling(Rc::clone(&right_right)).is_none());
/// assert!(red_black_tree::get_sibling(Rc::clone(&root)).is_none());
///
/// assert!(root.valid());
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
///
/// assert!(!root.valid());
/// ```
pub fn get_uncle(node: Rc<Node>) -> Option<Rc<Node>> {
    get_parent(node.as_ref()).and_then(|parent| get_sibling(Rc::clone(&parent)))
}

/// Perform a right rotation
fn rotate_right(node: Rc<Node>) -> Rc<Node> {
    let nroot = Rc::clone(node.left.borrow().as_ref().unwrap());
    let parent = get_parent(node.as_ref());
    *node.left.borrow_mut() = nroot
        .right
        .borrow()
        .as_ref()
        .and_then(|right| Some(Rc::clone(&right)));
    *nroot.right.borrow_mut() = Some(Rc::clone(&node));
    *node.parent.borrow_mut() = Rc::downgrade(&nroot);

    if let Some(left) = node.left.borrow().as_ref() {
        *left.parent.borrow_mut() = Rc::downgrade(&node);
    }
    if let Some(parent) = parent {
        if let Some(left) = parent.left.borrow().as_ref() {
            if Rc::ptr_eq(&left, &node) {
                *parent.left.borrow_mut() = Some(Rc::clone(&nroot));
            } else {
                *parent.right.borrow_mut() = Some(Rc::clone(&nroot));
            }
        }
    }
    nroot
}

/// Perform a left rotation
fn rotate_left(node: Rc<Node>) -> Rc<Node> {
    let nroot = Rc::clone(node.right.borrow().as_ref().unwrap());
    let parent = get_parent(node.as_ref());
    *node.right.borrow_mut() = nroot
        .left
        .borrow()
        .as_ref()
        .and_then(|left| Some(Rc::clone(&left)));
    *nroot.left.borrow_mut() = Some(Rc::clone(&node));
    *node.parent.borrow_mut() = Rc::downgrade(&nroot);

    if let Some(right) = node.right.borrow().as_ref() {
        *right.parent.borrow_mut() = Rc::downgrade(&node);
    }
    if let Some(parent) = parent {
        if let Some(left) = parent.left.borrow().as_ref() {
            if Rc::ptr_eq(&left, &node) {
                *parent.left.borrow_mut() = Some(Rc::clone(&nroot));
            } else {
                *parent.right.borrow_mut() = Some(Rc::clone(&nroot));
            }
        }
    }
    nroot
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_rotate_right() {
        let left_left = Node::new(0, None, None, COLOR::BLACK);
        let left_right = Node::new(15, None, None, COLOR::BLACK);
        let left = Node::new(10, Some(&left_left), Some(&left_right), COLOR::RED);
        let right = Node::new(30, None, None, COLOR::RED);
        let root = Node::new(20, Some(&left), Some(&right), COLOR::BLACK);

        assert!(!root.valid());

        let nroot = rotate_right(Rc::clone(&root));

        assert!(Rc::ptr_eq(&nroot.right.borrow().as_ref().unwrap(), &root));
        assert!(Rc::ptr_eq(&nroot, &left));
        assert!(Rc::ptr_eq(
            &root.left.borrow().as_ref().unwrap(),
            &left_right
        ));
        assert!(Rc::ptr_eq(
            &left_right.parent.borrow().upgrade().unwrap(),
            &root
        ));
        assert!(Rc::ptr_eq(&root.parent.borrow().upgrade().unwrap(), &nroot));
    }

    #[test]
    fn test_rotate_left() {
        let right_left = Node::new(25, None, None, COLOR::BLACK);
        let right_right = Node::new(40, None, None, COLOR::BLACK);
        let left = Node::new(10, None, None, COLOR::RED);
        let right = Node::new(30, Some(&right_left), Some(&right_right), COLOR::RED);
        let root = Node::new(20, Some(&left), Some(&right), COLOR::BLACK);

        assert!(!root.valid());

        let nroot = rotate_left(Rc::clone(&root));

        assert!(Rc::ptr_eq(&nroot.left.borrow().as_ref().unwrap(), &root));
        assert!(Rc::ptr_eq(&nroot, &right));
        assert!(Rc::ptr_eq(
            &root.right.borrow().as_ref().unwrap(),
            &right_left
        ));
        assert!(Rc::ptr_eq(
            &right_left.parent.borrow().upgrade().unwrap(),
            &root
        ));
        assert!(Rc::ptr_eq(&root.parent.borrow().upgrade().unwrap(), &nroot));
    }

    #[test]
    fn test_valid() {
        let left_left = Node::new(0, None, None, COLOR::BLACK);
        let left_right = Node::new(15, None, None, COLOR::BLACK);
        let right_left = Node::new(25, None, None, COLOR::BLACK);
        let right_right = Node::new(40, None, None, COLOR::BLACK);
        let left = Node::new(10, Some(&left_left), Some(&left_right), COLOR::RED);
        let right = Node::new(30, Some(&right_left), Some(&right_right), COLOR::RED);
        let root = Node::new(20, Some(&left), Some(&right), COLOR::BLACK);

        assert!(root.valid());
    }

    #[test]
    fn test_invalid_color() {
        let left_left = Node::new(0, None, None, COLOR::RED);
        let left = Node::new(10, Some(&left_left), None, COLOR::RED);
        let right = Node::new(30, None, None, COLOR::RED);
        let root = Node::new(20, Some(&left), Some(&right), COLOR::BLACK);

        assert!(!root.valid());
    }
}
