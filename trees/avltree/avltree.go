// Copyright (c) 2017, Benjamin Scher Purcell. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package avltree implements an AVL balanced binary tree.
//
// Structure is not thread safe.
//
// References: https://en.wikipedia.org/wiki/AVL_tree
package avltree

import (
	"cmp"
	"fmt"

	"github.com/BabelCodePerks/go-ds/trees"
	"github.com/BabelCodePerks/go-ds/utils"
)

// Assert Tree implementation
var _ trees.Tree[int] = (*Tree[string, int, string])(nil)

// Tree holds elements of the AVL tree.
type Tree[K comparable, V any, S any] struct {
	Root        *Node[K, V]             // Root node
	Comparator  utils.Comparator[K]     // Node comparator
	Comparator2 utils.Comparator2[K, S] // Search criteria comparator. To work as expected, must sort in the same order as Comparator.

	size int // Total number of keys in the tree
}

// Node is a single element within the tree
type Node[K comparable, V any] struct {
	Key      K
	Value    V
	Parent   *Node[K, V]    // Parent node
	Children [2]*Node[K, V] // Children nodes
	b        int8
}

// New instantiates an AVL tree with the built-in comparator for K
func New[K cmp.Ordered, V any, S any]() *Tree[K, V, S] {
	return &Tree[K, V, S]{Comparator: cmp.Compare[K]}
}

// NewWith instantiates an AVL tree with the custom comparator.
func NewWith[K comparable, V any, S any](comparator utils.Comparator[K]) *Tree[K, V, S] {
	return &Tree[K, V, S]{Comparator: comparator}
}

// Put inserts node into the tree.
// Key should adhere to the comparator's type assertion, otherwise method panics.
func (tree *Tree[K, V, S]) Put(key K, value V) {
	tree.put(key, value, nil, &tree.Root)
}

// Get returns the value of the node found by GetNode(key), if any. Returns with found true if there was a
// match, otherwise false, in that case value is the zero value of the tree's value type.
func (tree *Tree[K, V, S]) Get(key K) (value V, found bool) {
	n := tree.GetNode(key)
	if n != nil {
		return n.Value, true
	}
	return value, false
}

// Get2 returns the key of the node found by GetNode2(search), if any. Returns with found true if there was
// a match, otherwise false, in that case key is the zero value of the tree's key type.
func (tree *Tree[K, V, S]) Get2(search S) (key K, found bool) {
	var zeroK K
	n := tree.GetNode2(search)
	if n != nil {
		return n.Key, true
	}
	return zeroK, false
}

// GetNode descends the tree based on Comparator(key, node.key) and returns the (first encountered) node for
// which Comparator reports a match. Iff Comparator(key) distinguishes all nodes GetNode will find a specific
// node (or none), otherwise it's undefined which (of multiple matching nodes) is returned. Returns nil if
// Comparator does not report a match.
func (tree *Tree[K, V, S]) GetNode(key K) *Node[K, V] {
	n := tree.Root
	for n != nil {
		cmp := tree.Comparator(key, n.Key)
		switch {
		case cmp == 0:
			return n
		case cmp < 0:
			n = n.Children[0]
		case cmp > 0:
			n = n.Children[1]
		}
	}
	return n
}

// GetNode2 descends the tree based on Comparator2(search, node.key) and returns the (first encountered) node for
// which Comparator2 reports a match. Iff Comparator2(search) distinguishes all nodes, GetNode2 will find a
// specific node (or none), otherwise it's undefined which (of multiple matching nodes) is returned. Returns nil
// if Comparator2 does not report a match.
func (tree *Tree[K, V, S]) GetNode2(search S) *Node[K, V] {
	n := tree.Root
	for n != nil {
		cmp := tree.Comparator2(search, n.Key)
		switch {
		case cmp == 0:
			return n
		case cmp < 0:
			n = n.Children[0]
		case cmp > 0:
			n = n.Children[1]
		}
	}
	return n
}

// Remove remove the node from the tree by key.
// Key should adhere to the comparator's type assertion, otherwise method panics.
func (tree *Tree[K, V, S]) Remove(key K) {
	tree.remove(key, &tree.Root)
}

// Empty returns true if tree does not contain any nodes.
func (tree *Tree[K, V, S]) Empty() bool {
	return tree.size == 0
}

// Size returns the number of elements stored in the tree.
func (tree *Tree[K, V, S]) Size() int {
	return tree.size
}

// Size returns the number of elements stored in the subtree.
// Computed dynamically on each call, i.e. the subtree is traversed to count the number of the nodes.
func (n *Node[K, V]) Size() int {
	if n == nil {
		return 0
	}
	size := 1
	if n.Children[0] != nil {
		size += n.Children[0].Size()
	}
	if n.Children[1] != nil {
		size += n.Children[1].Size()
	}
	return size
}

// Keys returns all keys in-order
func (tree *Tree[K, V, S]) Keys() []K {
	keys := make([]K, tree.size)
	it := tree.Iterator()
	for i := 0; it.Next(); i++ {
		keys[i] = it.Key()
	}
	return keys
}

// Values returns all values in-order based on the key.
func (tree *Tree[K, V, S]) Values() []V {
	values := make([]V, tree.size)
	it := tree.Iterator()
	for i := 0; it.Next(); i++ {
		values[i] = it.Value()
	}
	return values
}

// Left returns the minimum element of the AVL tree
// or nil if the tree is empty.
func (tree *Tree[K, V, S]) Left() *Node[K, V] {
	return tree.bottom(0)
}

// Right returns the maximum element of the AVL tree
// or nil if the tree is empty.
func (tree *Tree[K, V, S]) Right() *Node[K, V] {
	return tree.bottom(1)
}

// Floor Finds floor node of the input key, return the floor node or nil if no floor is found.
// Second return parameter is true if floor was found, otherwise false.
//
// Floor node is defined as the largest node that is smaller than or equal to the given node.
// A floor node may not be found, either because the tree is empty, or because
// all nodes in the tree is larger than the given node.
//
// Key should adhere to the comparator's type assertion, otherwise method panics.
func (tree *Tree[K, V, S]) Floor(key K) (floor *Node[K, V], found bool) {
	found = false
	n := tree.Root
	for n != nil {
		c := tree.Comparator(key, n.Key)
		switch {
		case c == 0:
			return n, true
		case c < 0:
			n = n.Children[0]
		case c > 0:
			floor, found = n, true
			n = n.Children[1]
		}
	}
	if found {
		return
	}
	return nil, false
}

func (tree *Tree[K, V, S]) Floor2(search S) (floor *Node[K, V], found bool) {
	found = false
	n := tree.Root
	for n != nil {
		c := tree.Comparator2(search, n.Key)
		switch {
		case c == 0:
			return n, true
		case c < 0:
			n = n.Children[0]
		case c > 0:
			floor, found = n, true
			n = n.Children[1]
		}
	}
	if found {
		return
	}
	return nil, false
}

// Ceiling finds ceiling node of the input key, return the ceiling node or nil if no ceiling is found.
// Second return parameter is true if ceiling was found, otherwise false.
//
// Ceiling node is defined as the smallest node that is larger than or equal to the given node.
// A ceiling node may not be found, either because the tree is empty, or because
// all nodes in the tree is smaller than the given node.
//
// Key should adhere to the comparator's type assertion, otherwise method panics.
func (tree *Tree[K, V, S]) Ceiling(key K) (ceil *Node[K, V], found bool) {
	found = false
	n := tree.Root
	for n != nil {
		c := tree.Comparator(key, n.Key)
		switch {
		case c == 0:
			return n, true
		case c < 0:
			ceil, found = n, true
			n = n.Children[0]
		case c > 0:
			n = n.Children[1]
		}
	}
	if found {
		return
	}
	return nil, false
}

func (tree *Tree[K, V, S]) Ceiling2(search S) (ceil *Node[K, V], found bool) {
	found = false
	n := tree.Root
	for n != nil {
		c := tree.Comparator2(search, n.Key)
		switch {
		case c == 0:
			return n, true
		case c < 0:
			ceil, found = n, true
			n = n.Children[0]
		case c > 0:
			n = n.Children[1]
		}
	}
	if found {
		return
	}
	return nil, false
}

// Clear removes all nodes from the tree.
func (tree *Tree[K, V, S]) Clear() {
	tree.Root = nil
	tree.size = 0
}

// String returns a string representation of container
func (tree *Tree[K, V, S]) String() string {
	str := "AVLTree\n"
	if !tree.Empty() {
		output(tree.Root, "", true, &str)
	}
	return str
}

func (n *Node[K, V]) String() string {
	return fmt.Sprintf("%v", n.Key)
}

func (tree *Tree[K, V, S]) put(key K, value V, p *Node[K, V], qp **Node[K, V]) bool {
	q := *qp
	if q == nil {
		tree.size++
		*qp = &Node[K, V]{Key: key, Value: value, Parent: p}
		return true
	}

	c := tree.Comparator(key, q.Key)
	if c == 0 {
		q.Key = key
		q.Value = value
		return false
	}

	if c < 0 {
		c = -1
	} else {
		c = 1
	}
	a := (c + 1) / 2
	var fix bool
	fix = tree.put(key, value, q, &q.Children[a])
	if fix {
		return putFix(int8(c), qp)
	}
	return false
}

func (tree *Tree[K, V, S]) remove(key K, qp **Node[K, V]) bool {
	q := *qp
	if q == nil {
		return false
	}

	c := tree.Comparator(key, q.Key)
	if c == 0 {
		tree.size--
		if q.Children[1] == nil {
			if q.Children[0] != nil {
				q.Children[0].Parent = q.Parent
			}
			*qp = q.Children[0]
			return true
		}
		fix := removeMin(&q.Children[1], &q.Key, &q.Value)
		if fix {
			return removeFix(-1, qp)
		}
		return false
	}

	if c < 0 {
		c = -1
	} else {
		c = 1
	}
	a := (c + 1) / 2
	fix := tree.remove(key, &q.Children[a])
	if fix {
		return removeFix(int8(-c), qp)
	}
	return false
}

func removeMin[K comparable, V any](qp **Node[K, V], minKey *K, minVal *V) bool {
	q := *qp
	if q.Children[0] == nil {
		*minKey = q.Key
		*minVal = q.Value
		if q.Children[1] != nil {
			q.Children[1].Parent = q.Parent
		}
		*qp = q.Children[1]
		return true
	}
	fix := removeMin(&q.Children[0], minKey, minVal)
	if fix {
		return removeFix(1, qp)
	}
	return false
}

func putFix[K comparable, V any](c int8, t **Node[K, V]) bool {
	s := *t
	if s.b == 0 {
		s.b = c
		return true
	}

	if s.b == -c {
		s.b = 0
		return false
	}

	if s.Children[(c+1)/2].b == c {
		s = singlerot(c, s)
	} else {
		s = doublerot(c, s)
	}
	*t = s
	return false
}

func removeFix[K comparable, V any](c int8, t **Node[K, V]) bool {
	s := *t
	if s.b == 0 {
		s.b = c
		return false
	}

	if s.b == -c {
		s.b = 0
		return true
	}

	a := (c + 1) / 2
	if s.Children[a].b == 0 {
		s = rotate(c, s)
		s.b = -c
		*t = s
		return false
	}

	if s.Children[a].b == c {
		s = singlerot(c, s)
	} else {
		s = doublerot(c, s)
	}
	*t = s
	return true
}

func singlerot[K comparable, V any](c int8, s *Node[K, V]) *Node[K, V] {
	s.b = 0
	s = rotate(c, s)
	s.b = 0
	return s
}

func doublerot[K comparable, V any](c int8, s *Node[K, V]) *Node[K, V] {
	a := (c + 1) / 2
	r := s.Children[a]
	s.Children[a] = rotate(-c, s.Children[a])
	p := rotate(c, s)

	switch {
	default:
		s.b = 0
		r.b = 0
	case p.b == c:
		s.b = -c
		r.b = 0
	case p.b == -c:
		s.b = 0
		r.b = c
	}

	p.b = 0
	return p
}

func rotate[K comparable, V any](c int8, s *Node[K, V]) *Node[K, V] {
	a := (c + 1) / 2
	r := s.Children[a]
	s.Children[a] = r.Children[a^1]
	if s.Children[a] != nil {
		s.Children[a].Parent = s
	}
	r.Children[a^1] = s
	r.Parent = s.Parent
	s.Parent = r
	return r
}

func (tree *Tree[K, V, S]) bottom(d int) *Node[K, V] {
	n := tree.Root
	if n == nil {
		return nil
	}

	for c := n.Children[d]; c != nil; c = n.Children[d] {
		n = c
	}
	return n
}

// Prev returns the previous element in an inorder
// walk of the AVL tree.
func (n *Node[K, V]) Prev() *Node[K, V] {
	return n.walk1(0)
}

// Next returns the next element in an inorder
// walk of the AVL tree.
func (n *Node[K, V]) Next() *Node[K, V] {
	return n.walk1(1)
}

func (n *Node[K, V]) walk1(a int) *Node[K, V] {
	if n == nil {
		return nil
	}

	if n.Children[a] != nil {
		n = n.Children[a]
		for n.Children[a^1] != nil {
			n = n.Children[a^1]
		}
		return n
	}

	p := n.Parent
	for p != nil && p.Children[a] == n {
		n = p
		p = p.Parent
	}
	return p
}

func output[K comparable, V any](node *Node[K, V], prefix string, isTail bool, str *string) {
	if node.Children[1] != nil {
		newPrefix := prefix
		if isTail {
			newPrefix += "│   "
		} else {
			newPrefix += "    "
		}
		output(node.Children[1], newPrefix, false, str)
	}
	*str += prefix
	if isTail {
		*str += "└── "
	} else {
		*str += "┌── "
	}
	*str += node.String() + "\n"
	if node.Children[0] != nil {
		newPrefix := prefix
		if isTail {
			newPrefix += "    "
		} else {
			newPrefix += "│   "
		}
		output(node.Children[0], newPrefix, true, str)
	}
}
