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
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/leanovate/gopter"
	"github.com/leanovate/gopter/gen"
	"github.com/leanovate/gopter/prop"
	"github.com/stretchr/testify/assert"
	"testing"
)

// TODO: Property based tests?
func TestFoldBilinear(t *testing.T) {

	for i := 0; i < 100; i++ {

		// f = c₀ + c₁ X₁ + c₂ X₂ + c₃ X₁ X₂
		var coefficients [4]fr.Element
		for i := 0; i < 4; i++ {
			if _, err := coefficients[i].SetRandom(); err != nil {
				t.Error(err)
			}
		}

		var r fr.Element
		if _, err := r.SetRandom(); err != nil {
			t.Error(err)
		}

		// interpolate at {0,1}²:
		m := make(MultiLin, 4)
		m[0] = coefficients[0]
		m[1].Add(&coefficients[0], &coefficients[2])
		m[2].Add(&coefficients[0], &coefficients[1])
		m[3].
			Add(&m[1], &coefficients[1]).
			Add(&m[3], &coefficients[3])

		m.Fold(r)

		// interpolate at {r}×{0,1}:
		var expected0, expected1 fr.Element
		expected0.
			Mul(&r, &coefficients[1]).
			Add(&expected0, &coefficients[0])

		expected1.
			Mul(&r, &coefficients[3]).
			Add(&expected1, &coefficients[2]).
			Add(&expected0, &expected1)

		if !m[0].Equal(&expected0) || !m[1].Equal(&expected1) {
			t.Fail()
		}
	}
}

func TestPrecomputeLagrange(t *testing.T) {

	testForDomainSize := func(domainSize uint8) bool {
		polys := computeLagrangeBasis(domainSize)

		for l := uint8(0); l < domainSize; l++ {
			for i := uint8(0); i < domainSize; i++ {
				var I fr.Element
				I.SetUint64(uint64(i))
				y := polys[l].Eval(&I)

				if i == l && !y.IsOne() || i != l && !y.IsZero() {
					t.Errorf("domainSize = %d: p_%d(%d) = %s", domainSize, l, i, y.Text(10))
					return false
				}
			}
		}
		return true
	}

	t.Parallel()
	parameters := gopter.DefaultTestParameters()

	parameters.MinSuccessfulTests = int(maxLagrangeDomainSize)

	properties := gopter.NewProperties(parameters)

	properties.Property("l'th lagrange polynomials must evaluate to 1 on l and 0 on other values in the domain", prop.ForAll(
		testForDomainSize,
		gen.UInt8Range(2, maxLagrangeDomainSize),
	))

	properties.TestingRun(t, gopter.ConsoleReporter(false))
}

// TODO: Benchmark folding? Algorithms is pretty straightforward; unless we want to measure how well memory management is working

func TestFoldedEqTable(t *testing.T) {
	q := make([]fr.Element, 2)
	q[0].SetInt64(2)
	q[1].SetInt64(3)

	m := make(MultiLin, 4)
	m[0].SetOne()
	m.Eq(q)

	eq := make([]fr.Element, 4)
	p := make([]fr.Element, 2)

	var one fr.Element
	one.SetOne()

	for p0 := 0; p0 < 2; p0++ {
		p[1].SetZero()
		for p1 := 0; p1 < 2; p1++ {
			eq[p0*2+p1] = EvalEq(q, p)
			p[1].Add(&p[1], &one)
		}
		p[0].Add(&p[0], &one)
	}

	for i := 0; i < 4; i++ {
		assert.Equal(t, eq[i], m[i], "folded table disagrees with EqEval", i)
	}

}
