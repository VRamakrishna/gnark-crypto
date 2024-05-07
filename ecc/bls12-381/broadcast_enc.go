package bls12381

import (
	"fmt"
	"os"
	"time"
	"bytes"
	"math/big"
	mrand "math/rand"
	"crypto/sha256"
	"crypto/rand"
	"crypto/aes"
	"crypto/cipher"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
)

type G1 = G1Affine
type G2 = G2Affine


//a BE public key consists of 2n group elements (powers of P) in G1 and G2, and an additional G2 element Q. We also include the number of parties as part of the public key

type PK struct{
	P1 []G1
	P2 []G2
	Q G2
	N int
}

//a BE decryption key consists of the party id and a G2 element dk

type DK struct{
	partyID int
	dk G2
}

// a BE ciphertext consists of two header elements in G1 and G2, and a symmetric-key ciphertext

type CT struct{
	h1 G1
	h2 G2
	ct []byte
}

// symmetric-key encryption implemented using AES-GCM

func SymEncrypt(key []byte, plaintextBytes []byte) ([]byte){
	//plaintextBytes := []byte(plaintext)
	block, _ := aes.NewCipher(key)
	gcm, _ := cipher.NewGCM(block)
	nonce := make([]byte, gcm.NonceSize())
	ciphertext := gcm.Seal(nonce, nonce, plaintextBytes, nil)
	return ciphertext
}

// symmetric-key decryption implemented using AES-GCM

func SymDecrypt(key []byte, ciphertext []byte) (string){
	block, _ := aes.NewCipher(key)
	gcm, _ := cipher.NewGCM(block)
	nonceSize := gcm.NonceSize()
	nonce, ciphertext := ciphertext[:nonceSize], ciphertext[nonceSize:]
	plaintextBytes, _ := gcm.Open(nil, nonce, ciphertext, nil)
	plaintext := string(plaintextBytes)
	return plaintext

}

// function to generate a random 256-bit big integer

func randBigInt() (*big.Int){
	max := new(big.Int)
	max.Exp(big.NewInt(2), big.NewInt(256), nil).Sub(max, big.NewInt(1))
	n, err := rand.Int(rand.Reader, max)
	if err != nil {
		panic("failed to get random big integer")
	}
	return n
}

func randSet(max int, setSize int) ([]int){
	if max <= 0 || setSize <= 0{
		return []int{}
	}
	set := make([]int, setSize)
	for i := 0; i < setSize; i++{
		for true {
			set[i] = mrand.Intn(max) + 1
			present := false
			for j := 0 ; j < i ; j++ {
				if set[i] == set[j] {
					present = true
					break
				}
			}
			if !present {
				break
			}
			// Element already exists in the set. Need to regenerate a random value.
		}
	}
	return set
}

// function to generate a BE public key

func GenPK(numParties int, gen1Aff G1, gen2Aff G2, bAlpha *big.Int, bX *big.Int) (PK){
	var pk PK
	var alpha fr.Element
	var i int
	pk.N = numParties
	pk.P1 = make([]G1, 2*numParties)
	pk.P2 = make([]G2, 2*numParties)
	alpha.SetBigInt(bAlpha)
	// we store the generators for G1 and G2 as the first elements in each set
	pk.P1[0] = gen1Aff
	pk.P2[0] = gen2Aff
	// generate powers of alpha
	alphas := make([]fr.Element, 2*numParties-1)
	alphas[0] = alpha
	for i = 1; i < 2*numParties-1; i++ {
		alphas[i].Mul(&alphas[i-1], &alpha)
		if i == numParties{
			alphas[i].Mul(&alphas[i], &alpha)  // skip alpha^{N+1}
		}
	}
	// generate powers of P in G1 and G2
	tempP1 := BatchScalarMultiplicationG1(&gen1Aff, alphas)
	tempP2 := BatchScalarMultiplicationG2(&gen2Aff, alphas)
	copy(pk.P1[1:], tempP1)
	copy(pk.P2[1:], tempP2)
	// generate Q
	pk.Q.ScalarMultiplication(&gen2Aff, bX)
	return pk
}

// function to generate a BE secret key

func GenSK(partyID int, Q G2, bAlpha *big.Int) (DK){
	var dk DK
	dk.partyID = partyID
	var j int
	dk.dk = Q
	for j = 0; j < partyID; j++{
		dk.dk.ScalarMultiplication(&dk.dk, bAlpha)

	}
	return dk
}

// BE key generation function. Takes as input the number of parties

func KeyGen(numParties int) (PK, []DK){
	_, _, gen1Aff, gen2Aff := Generators()
	var bAlpha *big.Int
	var bX *big.Int
	var pk PK
	var i int
	// generate uniform (secret) alpha and x
	bAlpha = randBigInt()
	bX = randBigInt()
	// generate pk
	pk = GenPK(numParties, gen1Aff, gen2Aff, bAlpha, bX)
	// generate an array of decryption keys --- one for each party
	dkArray := make([]DK, numParties)
	for i = 0; i < numParties; i++{
		dkArray[i] = GenSK(i+1, pk.Q, bAlpha)
	}
	return pk, dkArray
}

// BE encryption. Takes as input the public key, the plaintext and the target set of parties

func Encrypt(pk PK, plaintext []byte, setR []int) (CT){
	var bR *big.Int
	var ct CT
	var h2Temp G2
	var j int
	// generate r (encryption randomness)
	bR = randBigInt()
	// h1 = P^r
	ct.h1.ScalarMultiplication(&pk.P1[0], bR)
	// set h2
	h2Temp.Set(&pk.Q)
	for i:= 0; i < len(setR); i++{
		if setR[i] > pk.N || setR[i] < 0{
			fmt.Println("Subset index out of bound")
			return ct
		}
		j = pk.N + 1 - setR[i]
		h2Temp.Add(&h2Temp, &pk.P2[j])
	}
	ct.h2.ScalarMultiplication(&h2Temp, bR)
	// set omega = pair(P^r_1, P_n)
	var aux G1
	aux.ScalarMultiplication(&pk.P1[1], bR)
	omegaEnc, _ := Pair([]G1{aux}, []G2{pk.P2[pk.N]})
	// serialize omega
	omegaEncBytes := omegaEnc.Bytes()
	// K = Hash(omega)
	keyEnc := sha256.New()
	keyEnc.Write(omegaEncBytes[:])
	keyEncBytes := keyEnc.Sum(nil)
	// create ct = SymEncrypt(K, plaintext)
	ct.ct = SymEncrypt(keyEncBytes, plaintext)
	return ct
}

// BE decryption function. Takes as input the public key, a decryption key, a ciphertext and the target set

func Decrypt(pk PK, dk DK, ct CT, setR []int) (string){
	if dk.partyID > pk.N || dk.partyID < 0{
		fmt.Println("Decryption index out of bounds")
		return ""
	}
	var aux G2
	var j int
	// generate Q_i.P*
	aux.Set(&dk.dk)
	for i := 0; i < len(setR); i++{
		if setR[i] > pk.N || setR[i] < 0{
			fmt.Println("Subset index out of bound")
			return ""
		}
		if setR[i] != dk.partyID{
			j = pk.N + 1 + dk.partyID - setR[i]
			if j > pk.N{
				j = j - 1
			}
			aux.Add(&aux, &pk.P2[j])
		}
	}
	// pairing computations
	var omegaDec GT
	omega1, _ := Pair([]G1{pk.P1[dk.partyID]}, []G2{ct.h2})
	omega2, _ := Pair([]G1{ct.h1}, []G2{aux})
	// recover omega
	omegaDec.Div(&omega1, &omega2)
	// serialize omega
	omegaDecBytes := omegaDec.Bytes()
	// K = Hash(Omega)
	keyDec := sha256.New()
	keyDec.Write(omegaDecBytes[:])
	keyDecBytes := keyDec.Sum(nil)
	// recover plaintext = SymDecrypt(K, ct)
	plaintext := SymDecrypt(keyDecBytes, ct.ct)
	return plaintext
}

func BenchmarkEncAndDec(numParties int, subsetSize int, numTests int, pk PK, dkArray []DK, plaintext []byte, keyGenTime int64){
	/*const numTests = 10
	fmt.Println("Starting keygen.......")
	pk, _ := KeyGen(numParties)
	fmt.Println("Key generated.......\n")
	fmt.Println("Starting encryptions.......")*/
	totalTimeEnc := int64(0)
	totalTimeDec := int64(0)
	for test := 0; test < numTests; test++{
		setR := randSet(numParties, subsetSize)
		// timing code start for encryption
		startTime := time.Now()
		ct := Encrypt(pk, plaintext, setR)
		endTime := time.Now()
		elapsedTime := endTime.Sub(startTime)
		//fmt.Println(elapsedTime.Milliseconds())
		totalTimeEnc += elapsedTime.Milliseconds()

		// timing code start for decryption
		startTime = time.Now()
		plaintextDec := Decrypt(pk, dkArray[setR[0] - 1], ct, setR) // pass decrypting id-1 as parameter to dkArray
		endTime = time.Now()
		elapsedTime = endTime.Sub(startTime)
		totalTimeDec += elapsedTime.Milliseconds()

		if !bytes.Equal(plaintext, []byte(plaintextDec)) {
			fmt.Printf("Decrypted ciphertext '%s' does not match original plaintext '%s'. Exiting!!!\n", string(plaintextDec), string(plaintext))
			os.Exit(1)
		}
	}
	fmt.Printf("%d,%d,%d,%d,%d,%d\n", numParties, subsetSize, totalTimeEnc, totalTimeDec, numTests, keyGenTime)
}

// sample BE test for 500 parties and a subset of size 10

func TestBEncDec(){
	var numParties int
	numParties = 500
	pk, dkArray := KeyGen(numParties)

	plaintext := "Hello World"
	setR := []int{3, 15, 27, 61, 93, 119, 235, 356, 489, 497}
	ct := Encrypt(pk, []byte(plaintext), setR)
	fmt.Println("Plaintext encrypted: ", plaintext, "\n")

	plaintextDec := Decrypt(pk, dkArray[234], ct, setR) // pass decrypting id-1 as parameter to dkArray
	fmt.Println("Plaintext decrypted: ", plaintextDec, "\n")
	if plaintext == plaintextDec{
		fmt.Println("Decryption was successful\n")
	}else{
		fmt.Println("Decryption failed\n")
	}
}




