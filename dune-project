(lang dune 3.19)

(name bitvectorset)

(generate_opam_files true)

(source
 (github PaulRaUnite/bitvectorset))

(authors "Pavlo Tokariev <pavlo.tokariev@gmail.com>")

(license LICENSE)

(package
 (name bitvectorset)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  (ocaml
   (>= 5.0.0))
  fast_bitvector
  (iter
   (>= 1.3))
  (sexplib0
   (>= 0.17))
  (ppx_inline_test
   (>= 0.17.0))
  (crowbar :with-test)
  (ocaml-option-afl :with-test))
 (tags
  ("bitvector" "set")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
