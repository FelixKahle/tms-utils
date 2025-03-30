// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use std::collections::VecDeque;

/// A stack data structure implemented using a [`VecDeque`].
///
/// The `Stack` provides the typical stack operations such as pushing, popping,
/// peeking, and iterating over elements. It is a generic data structure that can
/// store elements of any type.
///
/// # Examples
///
/// ```rust
/// use xml_parser::stack::Stack;
///
/// let mut stack: Stack<i32> = Stack::new();
/// stack.push(10);
/// stack.push(20);
///
/// assert_eq!(stack.peek(), Some(&20));
/// assert_eq!(stack.len(), 2);
/// ```
pub struct Stack<T> {
    elements: VecDeque<T>,
}

impl<T> Stack<T> {
    /// Creates a new `Stack`.
    ///
    /// # Returns
    ///
    /// A new instance of `Stack`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::stack::Stack;
    ///
    /// let stack: Stack<i32> = Stack::new();
    /// ```
    pub fn new() -> Stack<T> {
        Stack {
            elements: VecDeque::new(),
        }
    }

    /// Creates a new `Stack` with the specified capacity.
    ///
    /// # Arguments
    ///
    /// * `capacity` - A [`usize`] representing the stack's capacity.
    ///
    /// # Returns
    ///
    /// A new instance of `Stack`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::stack::Stack;
    ///
    /// let stack: Stack<i32> = Stack::with_capacity(10);
    ///
    /// assert_eq!(stack.capacity(), 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Stack<T> {
        Stack {
            elements: VecDeque::with_capacity(capacity),
        }
    }

    /// Creates a new `Stack` from an iterator.
    ///
    /// # Arguments
    ///
    /// * `iter` - An iterator yielding elements to push onto the stack.
    ///
    /// # Returns
    ///
    /// A new instance of `Stack` containing the elements from the iterator.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::stack::Stack;
    ///
    /// let stack = Stack::from_iter(vec![1, 2, 3]);
    ///
    /// assert_eq!(stack.len(), 3);
    /// ```
    pub fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Stack<T> {
        Stack {
            elements: VecDeque::from_iter(iter),
        }
    }

    /// Pushes an element onto the stack.
    ///
    /// # Arguments
    ///
    /// * `element` - The element to push onto the stack.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::stack::Stack;
    ///
    /// let mut stack: Stack<i32> = Stack::new();
    /// stack.push(1);
    /// stack.push(2);
    ///
    /// assert_eq!(stack.len(), 2);
    /// ```
    pub fn push(&mut self, element: T) {
        self.elements.push_back(element);
    }

    /// Pops an element from the stack.
    ///
    /// # Returns
    ///
    /// An [`Option`] containing the popped element. Returns [`None`] if the stack is empty.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::stack::Stack;
    ///
    /// let mut stack: Stack<i32> = Stack::new();
    /// stack.push(1);
    /// stack.push(2);
    ///
    /// assert_eq!(stack.pop(), Some(2));
    /// assert_eq!(stack.pop(), Some(1));
    /// assert_eq!(stack.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.elements.pop_back()
    }

    /// Peeks at the top element of the stack without removing it.
    ///
    /// # Returns
    ///
    /// An [`Option`] containing a reference to the top element, or [`None`] if the stack is empty.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::stack::Stack;
    ///
    /// let mut stack: Stack<i32> = Stack::new();
    /// stack.push(1);
    /// stack.push(2);
    ///
    /// assert_eq!(stack.peek(), Some(&2));
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.elements.back()
    }

    /// Checks whether the stack is empty.
    ///
    /// # Returns
    ///
    /// A boolean indicating whether the stack contains no elements.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::stack::Stack;
    ///
    /// let mut stack: Stack<i32> = Stack::new();
    /// assert!(stack.is_empty());
    /// stack.push(1);
    /// assert!(!stack.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Returns the number of elements in the stack.
    ///
    /// # Returns
    ///
    /// A [`usize`] representing the number of elements.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::stack::Stack;
    ///
    /// let mut stack: Stack<i32> = Stack::new();
    /// stack.push(1);
    /// stack.push(2);
    ///
    /// assert_eq!(stack.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Returns the current capacity of the stack.
    ///
    /// This capacity represents the number of elements the stack can hold without reallocating.
    ///
    /// # Returns
    ///
    /// A [`usize`] representing the stack's capacity.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::stack::Stack;
    ///
    /// let stack: Stack<i32> = Stack::with_capacity(10);
    /// assert!(stack.capacity() >= 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.elements.capacity()
    }

    /// Clears all elements from the stack.
    ///
    /// After calling this method, the stack will be empty.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::stack::Stack;
    ///
    /// let mut stack: Stack<i32> = Stack::new();
    /// stack.push(1);
    /// stack.push(2);
    /// stack.clear();
    /// assert!(stack.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.elements.clear();
    }

    /// Returns an iterator over the elements of the stack.
    ///
    /// The iterator yields references to the elements in the order they were pushed.
    ///
    /// # Returns
    ///
    /// An iterator over the stack's elements.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::stack::Stack;
    ///
    /// let mut stack: Stack<i32> = Stack::new();
    /// stack.push(1);
    /// stack.push(2);
    ///
    /// let mut iter = stack.iter();
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&2));
    /// ```
    pub fn iter(&self) -> std::collections::vec_deque::Iter<T> {
        self.elements.iter()
    }

    /// Returns a mutable iterator over the elements of the stack.
    ///
    /// This iterator allows modifying the elements in place.
    ///
    /// # Returns
    ///
    /// A mutable iterator over the stack's elements.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::stack::Stack;
    ///
    /// let mut stack: Stack<i32> = Stack::new();
    /// stack.push(1);
    /// stack.push(2);
    ///
    /// for elem in stack.iter_mut() {
    ///     *elem *= 2;
    /// }
    ///
    /// let mut iter = stack.iter();
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&4));
    /// ```
    pub fn iter_mut(&mut self) -> std::collections::vec_deque::IterMut<T> {
        self.elements.iter_mut()
    }

    /// Shrinks the capacity of the stack to fit its current size.
    ///
    /// This method reduces the stack's capacity to the number of elements it contains.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::stack::Stack;
    ///
    /// let mut stack: Stack<i32> = Stack::with_capacity(10);
    /// stack.push(1);
    /// stack.push(2);
    /// stack.shrink_to_fit();
    ///
    /// assert_eq!(stack.capacity(), 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.elements.shrink_to_fit();
    }
}

impl<T> Iterator for Stack<T> {
    type Item = T;

    /// Returns the next element in the stack.
    ///
    /// # Returns
    ///
    /// An [`Option`] containing the next element in the stack. Returns [`None`] if the stack is empty.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::stack::Stack;
    ///
    /// let mut stack: Stack<i32> = Stack::new();
    /// stack.push(1);
    /// stack.push(2);
    ///
    /// assert_eq!(stack.next(), Some(2));
    /// assert_eq!(stack.next(), Some(1));
    /// assert_eq!(stack.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        self.pop()
    }
}
