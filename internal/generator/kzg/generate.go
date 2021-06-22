package kzg

import (
	"path/filepath"

	"github.com/consensys/bavard"
	"github.com/consensys/gnark-crypto/internal/generator/config"
)

func Generate(conf config.Curve, baseDir string, bgen *bavard.BatchGenerator) error {

	// kzg commitment scheme
	conf.Package = "kzg"
	entries := []bavard.Entry{
		{File: filepath.Join(baseDir, "doc.go"), Templates: []string{"doc.go.tmpl"}},
		{File: filepath.Join(baseDir, "kzg.go"), Templates: []string{"kzg.go.tmpl"}},
		{File: filepath.Join(baseDir, "kzg_test.go"), Templates: []string{"kzg.test.go.tmpl"}},
		{File: filepath.Join(baseDir, "fuzz.go"), Templates: []string{"fuzz.go.tmpl"}, BuildTag: "gofuzz"},
		{File: filepath.Join(baseDir, "fuzz_test.go"), Templates: []string{"fuzz.test.go.tmpl"}, BuildTag: "gofuzz"},
	}
	return bgen.Generate(conf, conf.Package, "./kzg/template/", entries...)

}
