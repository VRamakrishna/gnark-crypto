package bls12381

import (
	"fmt"
	"math/big"
	"crypto/rand"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
)

type G1 = G1Affine
type G2 = G2Affine

type PK struct{
	P1 []G1
	P2 []G2
	Q G2
	N uint64
}

type DK struct{
	partyID uint64
	dk G2
}

type CT struct{
	h1 G1
	h2 G2
	// also include a symmetric-key ciphertext C
}

func randBigInt() (*big.Int){
	max := new(big.Int)
	max.Exp(big.NewInt(2), big.NewInt(256), nil).Sub(max, big.NewInt(1))
	n, err := rand.Int(rand.Reader, max)
	if err != nil {
		panic("failed to get random big integer")
	}
	return n
}

/*
func randFieldElement() (*fr.Element){
	bytes := make([]byte, 32)
	_, err := rand.Read(bytes)
	if err != nil {
		panic("failed to get random field element")
	}
	var r fr.Element
	r.SetBytes(bytes)

	return &r
}
*/

func GenPK(numParties uint64, gen1Aff G1, gen2Aff G2, bAlpha *big.Int, bX *big.Int) (PK){
	var pk PK
	var alpha fr.Element
	var i uint64
	pk.N = numParties
	pk.P1 = make([]G1, 2*numParties)
	pk.P2 = make([]G2, 2*numParties)
	alpha.SetBigInt(bAlpha)
	pk.P1[0] = gen1Aff
	pk.P2[0] = gen2Aff
	alphas := make([]fr.Element, 2*numParties-1)
	alphas[0] = alpha
	for i = 1; i < 2*numParties-1; i++ {
		alphas[i].Mul(&alphas[i-1], &alpha)
		if i == numParties{
			alphas[i].Mul(&alphas[i], &alpha)
		}
	}
	tempP1 := BatchScalarMultiplicationG1(&gen1Aff, alphas)
	tempP2 := BatchScalarMultiplicationG2(&gen2Aff, alphas)
	copy(pk.P1[1:], tempP1)
	copy(pk.P2[1:], tempP2)
	pk.Q.ScalarMultiplication(&gen2Aff, bX)
	return pk
}

func GenSK(partyID uint64, gen2Aff G2, bAlpha *big.Int) (DK){
	var dk DK
	dk.partyID = partyID
	var j uint64
	var powerAlpha *big.Int
	powerAlpha = bAlpha
	for j = 1; j < partyID; j++{
		powerAlpha.Mul(powerAlpha, bAlpha)
	}
	dk.dk.ScalarMultiplication(&gen2Aff, powerAlpha)
	return dk
}

func KeyGen(numParties uint64) (PK, []DK){
	_, _, gen1Aff, gen2Aff := Generators()
	var bAlpha *big.Int
	var bX *big.Int
	var pk PK
	var i uint64
	bAlpha = randBigInt()
	bX = randBigInt()
	pk = GenPK(numParties, gen1Aff, gen2Aff, bAlpha, bX)
	dkArray := make([]DK, numParties)
	for i = 0; i < numParties; i++{
		dkArray[i] = GenSK(i+1, gen2Aff, bAlpha)
	}
	return pk, dkArray
}

func Encrypt(pk PK, setR []uint64) (CT, GT){
	var bR *big.Int
	var ct CT
	var h2Temp G2
	var omegaDummy GT
	bR = randBigInt()
	ct.h1.ScalarMultiplication(&pk.P1[0], bR)
	h2Temp.ScalarMultiplication(&pk.Q, bR)
	for i:= 0; i < len(setR); i++{
		if setR[i] > pk.N || setR[i] < 0{
			fmt.Println("Subset index out of bound")
			return ct, omegaDummy
		}
		h2Temp.Add(&h2Temp, &pk.P2[pk.N - setR[i]])
	}
	ct.h2 = h2Temp
	var aux G1
	//var omega GT
	aux.ScalarMultiplication(&pk.P1[1], bR)
	omega, _ := Pair([]G1{aux}, []G2{pk.P2[2]})
	return ct, omega
}

func Decrypt(pk PK, dk DK, ct CT, setR []uint64) (GT){
	var omegaDummy GT
	if dk.partyID > pk.N || dk.partyID < 0{
		fmt.Println("Decryption index out of bounds")
		return omegaDummy
	}
	var aux G2
	aux.Set(&dk.dk)
	for i := 0; i < len(setR); i++{
		if setR[i] > pk.N || setR[i] < 0{
			fmt.Println("Subset index out of bound")
			return omegaDummy
		}
		if setR[i] != dk.partyID{
			aux.Add(&aux, &pk.P2[pk.N + dk.partyID - setR[i]])
		}
	}
	var omegaDec GT
	omega1, _ := Pair([]G1{pk.P1[dk.partyID]}, []G2{ct.h2})
	omega2, _ := Pair([]G1{ct.h1}, []G2{aux})
	omegaDec.Sub(&omega1, &omega2)
	return omegaDec
}

func testBEncDec(){
	var numParties uint64
	numParties = 5
	setR := []uint64{1, 3}
	pk, dkArray := KeyGen(numParties)
	ct, omegaEnc := Encrypt(pk, setR)
	omegaDec :=Decrypt(pk, dkArray[3], ct, setR)
	//Decrypt(pk, dkArray[2], ct, setR)
	if omegaEnc.Equal(&omegaDec){
		fmt.Println("Decryption success")
	}else{
		fmt.Println("Decryption failed")
	}
}



