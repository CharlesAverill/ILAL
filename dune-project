(lang dune 3.21)
(using rocq 0.11)

(name rocq-ilal)

(generate_opam_files true)

(source
 (github CharlesAverill/ILAL))

(authors
 "Charles Averill <charles@utdallas.edu>")

(maintainers
 "Charles Averill <charles@utdallas.edu>")

(license GPL-3.0)

(documentation https://github.com/CharlesAverill/ILAL)

(package
 (name rocq-ilal)
 (synopsis "Incompleteness and Adversarial Logics")
 (description "Encodings of Incompleteness Logic and Adversarial Logic in Rocq")
 (depends
   (dune (>= 3.21.0))
   (rocq (>= 9.0.0))))
