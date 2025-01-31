// Copyright (c) 2015, Emir Pasic. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package avltree

import (
	"encoding/json"

	"github.com/BabelCodePerks/go-ds/containers"
)

// Assert Serialization implementation
var _ containers.JSONSerializer = (*Tree[string, int, string])(nil)
var _ containers.JSONDeserializer = (*Tree[string, int, string])(nil)

// ToJSON outputs the JSON representation of the tree.
func (tree *Tree[K, V, S]) ToJSON() ([]byte, error) {
	elements := make(map[K]V)
	it := tree.Iterator()
	for it.Next() {
		elements[it.Key()] = it.Value()
	}
	return json.Marshal(&elements)
}

// FromJSON populates the tree from the input JSON representation.
func (tree *Tree[K, V, S]) FromJSON(data []byte) error {
	elements := make(map[K]V)
	err := json.Unmarshal(data, &elements)
	if err != nil {
		return err
	}

	tree.Clear()
	for key, value := range elements {
		tree.Put(key, value)
	}

	return nil
}

// UnmarshalJSON @implements json.Unmarshaler
func (tree *Tree[K, V, S]) UnmarshalJSON(bytes []byte) error {
	return tree.FromJSON(bytes)
}

// MarshalJSON @implements json.Marshaler
func (tree *Tree[K, V, S]) MarshalJSON() ([]byte, error) {
	return tree.ToJSON()
}
