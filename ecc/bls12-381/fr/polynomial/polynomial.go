// Copyright 2020 ConsenSys Software Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Code generated by consensys/gnark-crypto DO NOT EDIT

package polynomial

import (
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
)

// Polynomial polynomial represented by coefficients bn254 fr field.
type Polynomial []fr.Element

// Degree returns the degree of the polynomial, which is the length of Data.
func (p *Polynomial) Degree() uint64 {
	return uint64(len(*p) - 1)
}

// Eval evaluates p at v
// returns a fr.Element
func (p *Polynomial) Eval(v *fr.Element) fr.Element {

	res := (*p)[len(*p)-1]
	for i := len(*p) - 2; i >= 0; i-- {
		res.Mul(&res, v)
		res.Add(&res, &(*p)[i])
	}

	return res
}

// Clone returns a copy of the polynomial
func (p *Polynomial) Clone() Polynomial {
	_p := make(Polynomial, len(*p))
	copy(_p, *p)
	return _p
}

// AddConstantInPlace adds a constant to the polynomial, modifying p
func (p *Polynomial) AddConstantInPlace(c *fr.Element) {
	for i := 0; i < len(*p); i++ {
		(*p)[i].Add(&(*p)[i], c)
	}
}

// SubConstantInPlace subs a constant to the polynomial, modifying p
func (p *Polynomial) SubConstantInPlace(c *fr.Element) {
	for i := 0; i < len(*p); i++ {
		(*p)[i].Sub(&(*p)[i], c)
	}
}

// ScaleInPlace multiplies p by v, modifying p
func (p *Polynomial) ScaleInPlace(c *fr.Element) {
	for i := 0; i < len(*p); i++ {
		(*p)[i].Mul(&(*p)[i], c)
	}
}

// Add adds p1 to p2
// This function allocates a new slice unless p == p1 or p == p2
func (p *Polynomial) Add(p1, p2 Polynomial) *Polynomial {

	bigger := p1
	smaller := p2
	if len(bigger) < len(smaller) {
		bigger, smaller = smaller, bigger
	}

	if len(*p) == len(bigger) && (&(*p)[0] == &bigger[0]) {
		for i := 0; i < len(smaller); i++ {
			(*p)[i].Add(&(*p)[i], &smaller[i])
		}
		return p
	}

	if len(*p) == len(smaller) && (&(*p)[0] == &smaller[0]) {
		for i := 0; i < len(smaller); i++ {
			(*p)[i].Add(&(*p)[i], &bigger[i])
		}
		*p = append(*p, bigger[len(smaller):]...)
		return p
	}

	res := make(Polynomial, len(bigger))
	copy(res, bigger)
	for i := 0; i < len(smaller); i++ {
		res[i].Add(&res[i], &smaller[i])
	}
	*p = res
	return p
}

// Equal checks equality between two polynomials
func (p *Polynomial) Equal(p1 Polynomial) bool {
	if (*p == nil) != (p1 == nil) {
		return false
	}

	if len(*p) != len(p1) {
		return false
	}

	for i := range p1 {
		if !(*p)[i].Equal(&p1[i]) {
			return false
		}
	}

	return true
}
