// Copyright (c) 2015, Emir Pasic. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package utils

import "time"

type Comparator[K any] func(key1, key2 K) int

// A Comparator2 is used by Get(Node)2, Ceiling2 and Floor2. The actual comparator function must assert,
// convert or otherwise parse search as needed.
type Comparator2[K any, S any] func(search S, key K) int

// TimeComparator provides a basic comparison on time.Time
func TimeComparator(a, b time.Time) int {
	switch {
	case a.After(b):
		return 1
	case a.Before(b):
		return -1
	default:
		return 0
	}
}
