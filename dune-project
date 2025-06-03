(lang dune 3.19)

(name bitvectorset)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name bitvectorset)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  ocaml
  fast_bitvector
  iter
  (sexplib0
   (>= 0.17))
  ppx_assert
  ppx_inline_test
  ppx_compare
  ppx_sexp_conv
  )
 (tags
  ("add topics" "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
