// Copyright 2020 ConsenSys AG
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

// Code generated by gurvy DO NOT EDIT

package bls381

import (
	"testing"

	"github.com/consensys/gurvy/bls381/fp"
	"github.com/leanovate/gopter"
	"github.com/leanovate/gopter/prop"
)

// ------------------------------------------------------------
// tests

func TestE2ReceiverIsOperand(t *testing.T) {

	parameters := gopter.DefaultTestParameters()
	parameters.MinSuccessfulTests = 100

	properties := gopter.NewProperties(parameters)

	genA := GenE2()
	genB := GenE2()
	genfp := GenFp()

	properties.Property("[BLS381] Having the receiver as operand (addition) should output the same result", prop.ForAll(
		func(a, b *E2) bool {
			var c, d E2
			d.Set(a)
			c.Add(a, b)
			a.Add(a, b)
			b.Add(&d, b)
			return a.Equal(b) && a.Equal(&c) && b.Equal(&c)
		},
		genA,
		genB,
	))

	properties.Property("[BLS381] Having the receiver as operand (sub) should output the same result", prop.ForAll(
		func(a, b *E2) bool {
			var c, d E2
			d.Set(a)
			c.Sub(a, b)
			a.Sub(a, b)
			b.Sub(&d, b)
			return a.Equal(b) && a.Equal(&c) && b.Equal(&c)
		},
		genA,
		genB,
	))

	properties.Property("[BLS381] Having the receiver as operand (mul) should output the same result", prop.ForAll(
		func(a, b *E2) bool {
			var c, d E2
			d.Set(a)
			c.Mul(a, b)
			a.Mul(a, b)
			b.Mul(&d, b)
			return a.Equal(b) && a.Equal(&c) && b.Equal(&c)
		},
		genA,
		genB,
	))

	properties.Property("[BLS381] Having the receiver as operand (square) should output the same result", prop.ForAll(
		func(a *E2) bool {
			var b E2
			b.Square(a)
			a.Square(a)
			return a.Equal(&b)
		},
		genA,
	))

	properties.Property("[BLS381] Having the receiver as operand (neg) should output the same result", prop.ForAll(
		func(a *E2) bool {
			var b E2
			b.Neg(a)
			a.Neg(a)
			return a.Equal(&b)
		},
		genA,
	))

	properties.Property("[BLS381] Having the receiver as operand (double) should output the same result", prop.ForAll(
		func(a *E2) bool {
			var b E2
			b.Double(a)
			a.Double(a)
			return a.Equal(&b)
		},
		genA,
	))

	properties.Property("[BLS381] Having the receiver as operand (mul by non residue) should output the same result", prop.ForAll(
		func(a *E2) bool {
			var b E2
			b.MulByNonResidue(a)
			a.MulByNonResidue(a)
			return a.Equal(&b)
		},
		genA,
	))

	properties.Property("[BLS381] Having the receiver as operand (mul by non residue inverse) should output the same result", prop.ForAll(
		func(a *E2) bool {
			var b E2
			b.MulByNonResidueInv(a)
			a.MulByNonResidueInv(a)
			return a.Equal(&b)
		},
		genA,
	))

	properties.Property("[BLS381] Having the receiver as operand (Inverse) should output the same result", prop.ForAll(
		func(a *E2) bool {
			var b E2
			b.Inverse(a)
			a.Inverse(a)
			return a.Equal(&b)
		},
		genA,
	))

	properties.Property("[BLS381] Having the receiver as operand (Conjugate) should output the same result", prop.ForAll(
		func(a *E2) bool {
			var b E2
			b.Conjugate(a)
			a.Conjugate(a)
			return a.Equal(&b)
		},
		genA,
	))

	properties.Property("[BLS381] Having the receiver as operand (mul by element) should output the same result", prop.ForAll(
		func(a *E2, b fp.Element) bool {
			var c E2
			c.MulByElement(a, &b)
			a.MulByElement(a, &b)
			return a.Equal(&c)
		},
		genA,
		genfp,
	))

	properties.Property("[BLS381] Having the receiver as operand (Sqrt) should output the same result", prop.ForAll(
		func(a *E2) bool {
			var b, c, d, s E2

			s.Square(a)
			a.Set(&s)
			b.Set(&s)

			a.Sqrt(a)
			b.Sqrt(&b)

			c.Square(a)
			d.Square(&b)
			return c.Equal(&d)
		},
		genA,
	))

	properties.TestingRun(t, gopter.ConsoleReporter(false))
}

func TestE2Ops(t *testing.T) {

	parameters := gopter.DefaultTestParameters()
	parameters.MinSuccessfulTests = 100

	properties := gopter.NewProperties(parameters)

	genA := GenE2()
	genB := GenE2()
	genfp := GenFp()

	properties.Property("[BLS381] sub & add should leave an element invariant", prop.ForAll(
		func(a, b *E2) bool {
			var c E2
			c.Set(a)
			c.Add(&c, b).Sub(&c, b)
			return c.Equal(a)
		},
		genA,
		genB,
	))

	properties.Property("[BLS381] mul & inverse should leave an element invariant", prop.ForAll(
		func(a, b *E2) bool {
			var c, d E2
			d.Inverse(b)
			c.Set(a)
			c.Mul(&c, b).Mul(&c, &d)
			return c.Equal(a)
		},
		genA,
		genB,
	))

	properties.Property("[BLS381] inverse twice should leave an element invariant", prop.ForAll(
		func(a *E2) bool {
			var b E2
			b.Inverse(a).Inverse(&b)
			return a.Equal(&b)
		},
		genA,
	))

	properties.Property("[BLS381] neg twice should leave an element invariant", prop.ForAll(
		func(a *E2) bool {
			var b E2
			b.Neg(a).Neg(&b)
			return a.Equal(&b)
		},
		genA,
	))

	properties.Property("[BLS381] square and mul should output the same result", prop.ForAll(
		func(a *E2) bool {
			var b, c E2
			b.Mul(a, a)
			c.Square(a)
			return b.Equal(&c)
		},
		genA,
	))

	properties.Property("[BLS381] MulByElement MulByElement inverse should leave an element invariant", prop.ForAll(
		func(a *E2, b fp.Element) bool {
			var c E2
			var d fp.Element
			d.Inverse(&b)
			c.MulByElement(a, &b).MulByElement(&c, &d)
			return c.Equal(a)
		},
		genA,
		genfp,
	))

	properties.Property("[BLS381] Double and mul by 2 should output the same result", prop.ForAll(
		func(a *E2) bool {
			var b E2
			var c fp.Element
			c.SetUint64(2)
			b.Double(a)
			a.MulByElement(a, &c)
			return a.Equal(&b)
		},
		genA,
	))

	properties.Property("[BLS381] Mulbynonres mulbynonresinv should leave the element invariant", prop.ForAll(
		func(a *E2) bool {
			var b E2
			b.MulByNonResidue(a).MulByNonResidueInv(&b)
			return a.Equal(&b)
		},
		genA,
	))

	properties.Property("[BLS381] a + pi(a), a-pi(a) should be real", prop.ForAll(
		func(a *E2) bool {
			var b, c, d E2
			var e, f fp.Element
			b.Conjugate(a)
			c.Add(a, &b)
			d.Sub(a, &b)
			e.Double(&a.A0)
			f.Double(&a.A1)
			return c.A1.IsZero() && d.A0.IsZero() && e.Equal(&c.A0) && f.Equal(&d.A1)
		},
		genA,
	))

	properties.Property("[BLS381] Legendre on square should output 1", prop.ForAll(
		func(a *E2) bool {
			var b E2
			b.Square(a)
			c := b.Legendre()
			return c == 1
		},
		genA,
	))

	properties.Property("[BLS381] square(sqrt) should leave an element invariant", prop.ForAll(
		func(a *E2) bool {
			var b, c, d, e E2
			b.Square(a)
			c.Sqrt(&b)
			d.Square(&c)
			e.Neg(a)
			return (c.Equal(a) || c.Equal(&e)) && d.Equal(&b)
		},
		genA,
	))

	properties.TestingRun(t, gopter.ConsoleReporter(false))
}

// ------------------------------------------------------------
// benches

func BenchmarkE2Add(b *testing.B) {
	var a, c E2
	a.SetRandom()
	c.SetRandom()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		a.Add(&a, &c)
	}
}

func BenchmarkE2Sub(b *testing.B) {
	var a, c E2
	a.SetRandom()
	c.SetRandom()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		a.Sub(&a, &c)
	}
}

func BenchmarkE2Mul(b *testing.B) {
	var a, c E2
	a.SetRandom()
	c.SetRandom()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		a.Mul(&a, &c)
	}
}

func BenchmarkE2MulByElement(b *testing.B) {
	var a E2
	var c fp.Element
	c.SetRandom()
	a.SetRandom()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		a.MulByElement(&a, &c)
	}
}

func BenchmarkE2Square(b *testing.B) {
	var a E2
	a.SetRandom()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		a.Square(&a)
	}
}

func BenchmarkE2Inverse(b *testing.B) {
	var a E2
	a.SetRandom()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		a.Inverse(&a)
	}
}

func BenchmarkE2MulNonRes(b *testing.B) {
	var a E2
	a.SetRandom()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		a.MulByNonResidue(&a)
	}
}

func BenchmarkE2MulNonResInv(b *testing.B) {
	var a E2
	a.SetRandom()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		a.MulByNonResidueInv(&a)
	}
}

func BenchmarkE2Conjugate(b *testing.B) {
	var a E2
	a.SetRandom()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		a.Conjugate(&a)
	}
}
