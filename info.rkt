#lang info
(define collection 'multi)
(define deps '(("base" #:version "6.7") ("cur-lib" #:version "0.34") "chk" "debug-scopes" "redex-lib"))
(define pkg-desc "An implementation of (delimited) call/cc for Cur.")
(define compile-omit-paths '("paper"))
(define pkg-authors '(wilbowma YouyouCong))
