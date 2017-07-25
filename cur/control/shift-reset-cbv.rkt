#lang cur

(require
 cur/stdlib/sugar
 #;(for-syntax debug-scopes)
 (for-syntax racket/trace))

(provide
 cps
 shift
 reset)

(begin-for-syntax
  (require
   (only-in
    cur/curnel/racket-impl/equiv
    [unsafe-I-promise-I-know-what-I-am-doing-please-give-me-the-ability-to-introduce-bugs-by-using-cur-current-identifier=?
     cur-current-identifier=?]))
  ;; As we use gensym, this is hopefully safeish.
  (cur-current-identifier=? (lambda (x y)
                              (eq? (syntax->datum x) (syntax->datum y))))
  (require
   (for-template
    (only-in cur/main
             [#%app base-app]
             [elim base-elim]
             [Π base-Π]
             [λ base-λ]
             [Type base-Unv])))

  ;; answer type is fixed to Type 0
  ;; TODO: should answer-type be a syntax-parameter?
  (define answer-type (make-parameter #'(Type 0)))
  (define cpsing (make-parameter #f))
  (define captured-cont (make-parameter '()))

  (define (extend-env env var type)
    (cons (cons var type) env))

  ; gensym
  (define gensym1
    (let ([n 0])
      (lambda (ctx s)
        (set! n (add1 n))
        (format-id ctx "~a~a" s n))))

  ;; TODO: can we do better by using immutable-free-id-set?
  (define constants (make-parameter '()))
  
  (define (constant? x [env '()])
    (ormap (lambda (y) (cur-equal? x y #:local-env env)) (constants)))

  ;; list of (constant, CPS constant) pairs
  ;; (contains only constants that accept higher-order arguments)
  (define cps-constants-list
    (cons (cons #`EqV #`EqVc) (cons (cons #`EqV2 #`EqV2c) '())))

  ;; search for CPS counterpart of constant c
  (define (lookup-cps c l)
    (if (empty? l)
        c
        (if (cur-equal? c (car (first l)))
            (cdr (first l))
            (lookup-cps c (rest l)))))

  ;; apply constant c to variable vs
  (define (app-vs c vs)
    (if (empty? vs)
        c
        #`(base-app #,(app-vs c (rest vs)) #,(first vs))))

  ;; is-member function; used to check if an identifier is a captured continuation
  (define (member? x l [env '()])
    (if (empty? l)
        #f
        (if (cur-equal? x (first l) #:local-env env) #t (member? x (rest l)))))

  ;; CPS transformation of terms
  (define (cps-obj t [env '()])
    (syntax-parse (cur-expand t #:local-env env #'shift #'reset)
      #:literals (base-app base-elim base-Π base-λ base-Unv shift reset)
      [(base-λ (var : type) body)
       (let* ([k (gensym1 t "k")]
              [new-type0 (cps-constr2 (cur-type-infer t #:local-env env) env)]
              [new-env (extend-env env #'var #'type)]
              [new-type (cps-type #'type env)]
              [new-body (cps-obj #'body new-env)])
       #`(base-λ (#,k : (base-Π (_ : #,new-type0) #,(answer-type)))
                 (base-app #,k (base-λ (var : #,new-type) #,new-body))))]
      [(base-app e1 e2)
       (let ([k (gensym1 t "k")]
             [m (gensym1 t "m")]
             [n (gensym1 t "n")]
             [new-type0 (cps-constr2 (cur-type-infer t #:local-env env) env)]
             [new-type1 (cps-constr2 (cur-type-infer #'e1 #:local-env env) env)]
             [new-type2 (cps-type (cur-type-infer #'e2 #:local-env env) env)]
             [new-e1 (cps-obj #'e1 env)]
             [new-e2 (cps-top #'e2 env)])
       #`(base-λ (#,k : (base-Π (_ : #,new-type0) #,(answer-type)))
                 (base-app #,new-e1
                           (base-λ (#,m : #,new-type1)
                                   (base-app #,new-e2
                                             (base-λ (#,n : #,new-type2)
                                                     (base-app (base-app #,m #,n) #,k)))))))]
      [x:id
       #:when (constant? #'x env)
       (cps-constant #'x env)]
      [x:id
       #:when (not (constant? #'x env))
       (let ([k (gensym1 t "k")]
             [new-type (cps-constr2 (cur-type-infer #'x #:local-env env))])
         #`(base-λ (#,k : (base-Π (_ : #,new-type) #,(answer-type))) (base-app #,k x)))]
      [(shift _ ...) (cps-shift this-syntax env)]
      [(reset _ ...) (error 'cps-obj "I don't know how to do object-level reset")]))

  ;; translation of type annotation
  (define (cps-type e [env '()]) 
    (if (is-constr? e env)
        (cps-constr2 e env)
        (cps-unv2 e env)))

  ;; CPS translation of types
  (define (cps-constr t [env '()])
    (syntax-parse (cur-expand t #:local-env env #'shift #'reset)
      #:literals (base-app base-elim base-Π base-λ base-Unv shift reset)
      [(base-λ (var : type) body)
       (let* ([k (gensym1 t "k")]
              [new-env (extend-env env #'var #'type)]
              [new-type0 (cps-unv2 (cur-type-infer t #:local-env env) env)]
              [new-type (cps-type #'type env)]
              [new-body (cps-constr #'body new-env)])
         #`(base-λ (#,k : (base-Π (_ : #,new-type0) #,(answer-type)))
                   (base-app #,k (base-λ (var : #,new-type) #,new-body))))]
      [(base-app e1 e2)
       (if (member? #'e1 (captured-cont) env) ;; application of a captured continuation
           (let* ([k (gensym1 t "k")]
                  [v (gensym1 t "v")]
                  [type2 (cur-type-infer #'e2 #:local-env env)])
               #`(base-λ (#,k : (base-Π (_ : #,(answer-type)) #,(answer-type)))
                         (base-app #,(cps-top #'e2 env)
                                   (base-λ (#,v : #,(cps-type type2 env))
                                           (base-app (base-app e1 #,v) #,k)))))
           (let* ([k (gensym1 t "k")] ;; normal application
                  [m (gensym1 t "m")]
                  [n (gensym1 t "n")]
                  [type0 (cur-type-infer t #:local-env env)]
                  [new-type0 (cps-unv2 type0 env)]
                  [new-type1 (cps-unv2 (cur-type-infer #'e1 #:local-env env) env)]
                  [type2 (cur-type-infer #'e2 #:local-env env)]
                  [new-type2 (if (is-obj? #'e2 env)
                                 (cps-constr2 type2 env)
                                 (cps-unv2 type2 env))]
                  [new-e1 (cps-constr #'e1 env)]
                  [new-e2 (cps-top #'e2 env)])
             #`(base-λ (#,k : (base-Π (_ : #,new-type0) #,(answer-type)))
                       (base-app
                        #,new-e1 
                        (base-λ (#,m : #,new-type1)
                                (base-app
                                 #,new-e2 
                                 (base-λ (#,n : #,new-type2)
                                         (base-app (base-app #,m #,n) #,k))))))))]
      [(base-Π (var : type) body)
       (let* ([k (gensym1 t "k")]
              [x (gensym1 t "x")]
              [new-type (cps-type #'type env)]
              [new-env (extend-env env #'var #'type)]
              [new-body #`(base-app #,(cps-constr #'body new-env) ;; locally run the body
                                    (base-λ (#,x : (base-Unv 0)) #,x))])
         #`(base-λ (#,k : (base-Π (_ : (base-Unv 0)) #,(answer-type)))
                   (base-app #,k (base-Π (var : #,new-type) #,new-body))))]
      [a:id
       #:when (constant? #'a env)
       (cps-constant #'a env)]
      [a:id
       #:when (not (constant? #'a env))
       (let ([k (gensym1 t "k")]
             [new-type (cps-unv2 (cur-type-infer #'a #:local-env env) env)])
         #`(base-λ (#,k : (base-Π (_ : #,new-type) #,(answer-type))) (base-app #,k a)))]
      [(shift _ ...) (cps-shift this-syntax env)]
      [(reset _ ...) (cps-reset this-syntax env)]))

  ;; value-translation of types (used when CPS translating terms)
  (define (cps-constr2 t [env '()])
    (syntax-parse (cur-expand t)
      #:literals (base-app base-elim base-Π base-λ base-Unv)
      [(base-λ (var : type) body)
       (let* ([new-env (extend-env env #'var #'type)]
              [new-type (cps-type #'type env)]
              [new-body (cps-constr2 #'body new-env)])
         #`(base-λ (var : #,new-type) #,new-body))]
      [(base-app e1 e2)
       (let ([new-e1 (cps-constr2 #'e1 env)]
             [new-e2 (if (is-obj? #'e2 env)
                         #'e2  ;; should be the translation of e2 applied to id,
                               ;; but impossible since the answer type is fixed to Type 0
                               ;; i.e., translation of A e is type-safe only if e is of base type
                         (cps-constr2 #'e2 env))])
         #`(base-app #,new-e1 #,new-e2))]     
      [(base-Π (var : type) body)
       (let* ([new-env (extend-env env #'var #'type)]
              [new-type (cps-type #'type env)]
              [new-body (cps-top2 #'body new-env)])
         #`(base-Π (var : #,new-type) #,new-body))]
      [a:id #`a]))

  ;; translation of universes (used when CPS translating terms)
  (define (cps-unv t [env '()])
    (syntax-parse (cur-expand t)
      #:literals (base-app base-elim base-Π base-λ base-Unv)
      [(base-Unv i) #`(base-Unv i)]
      [(base-Π (var : type) body)
       (let* ([new-env (extend-env env #'var #'type)]
              [new-type (cps-type #'type env)]
              [new-body (cps-unv #'body new-env)])
       #`(base-Π (var : #,new-type) #,new-body))]))

  ;; value-translation of universes (used when CPS translating types)
  (define (cps-unv2 t [env '()])
    (syntax-parse (cur-expand t)
      #:literals (base-app base-elim base-Π base-λ base-Unv)
      [(base-Unv i) #`(base-Unv i)]
      [(base-Π (var : type) body)
       (let* ([new-env (extend-env env #'var #'type)]
              [new-type (if (is-constr? #'type env)
                            (cps-constr2 #'type env)
                            (cps-unv2 #'type env))]
              [new-body (cps-top #'body new-env)])
         #`(base-Π (var : #,new-type) #,new-body))]))

  ;; translation of constants
  (define (cps-constant c env)
    (cps-const c c '() env))

  (define (cps-const c c0 vs env)
    (let ([type (cur-type-infer c #:local-env env)])
      (syntax-parse (cur-expand type)
        #:literals (base-Π)
        [(base-Π (var : ann) result)
         (let* ([k (gensym1 c "k")]
                [new-type (cps-unv2 type env)]
                [new-ann (cps-type #'ann env)]
                [new-env (extend-env env #'var #'ann)])
           #`(base-λ (#,k : (base-Π (_ : #,new-type) #,(answer-type)))
                     (base-app #,k (base-λ (var : #,new-ann)
                                           #,(cps-const (cur-normalize #`(base-app #,c var)
                                                        #:local-env new-env)
                                                        c0
                                                        (cons #'var vs)
                                                        new-env)))))]
        [result
         (let ([k (gensym1 c "k")]
               [new-type0 (if (is-constr? #'result env)
                              (cps-constr2 #'result env)
                              (cps-unv2 #'result env))]
               [r (app-vs (lookup-cps c0 cps-constants-list) vs)])
           #`(base-λ (#,k : (base-Π (_ : #,new-type0) #,(answer-type)))
                     (base-app #,k #,r)))])))

  ;; top translation (when CPS translating types)
  (define (cps-top t [env '()])
    (cond
      [(is-obj? t env) (cps-obj t env)]
      [(is-constr? t env) (cps-constr t env)]
      [(is-unv? t env) ;; double-negation at universe level
       #`(base-Π (_ : (base-Π (_ : #,(cps-unv2 t env)) #,(answer-type))) #,(answer-type))]
      [else (error 'cps-top "Something terrible happened: ~a is not anything I know about.~n" t)]))

  ;; top translation (when CPS translating terms)
  (define (cps-top2 t [env '()])
    (cond
      [(is-obj? t env) (cps-obj t env)]
      [(is-constr? t env) ;; double-negation at type level
       #`(base-Π (_ : (base-Π (_ : #,(cps-constr2 t env)) #,(answer-type))) #,(answer-type))]
      [(is-unv? t env) (cps-unv t env)]
      [else (error 'cps-top2 "Something terrible happened: ~a is not anything I know about.~n" t)]))

  ;; translation of shift
  (define (cps-shift syn [env '()])
    (syntax-parse syn
      [(_ hole e)
       (syntax-parse #'e
         #:literals (base-app base-elim base-Π base-λ base-Unv)
         #:datum-literals (:)
       [(λ (var : (Π (_ : type) ans)) body)
        (let* ([alpha (gensym1 syn "a")]
               [k (gensym1 syn "k")]
               [k2 (gensym1 syn "k")]
               [v (gensym1 syn "v")]
               [x (gensym1 syn "x")]
               [new-type0 (cps-type #'type env)]
               [new-type #`(Π (_ : #,new-type0) ans)]
               [new-env (extend-env env #'var #`(base-Π (_ : type) ans))]
               [new-body (parameterize ([captured-cont (cons #'var (captured-cont))])
                           (cps-top #'body new-env))]
               [new-hole-type (cps-type #'type env)]) 
          #`(base-λ (#,k : (base-Π (_ : #,new-hole-type) ;; continuation to be captured
                                   #,(answer-type)))
                    (base-app
                     (base-app
                      (base-λ (var : (base-Π (_ : #,new-hole-type)
                                             (base-Π (_ : (base-Π (_ : #,(answer-type)) #,(answer-type)))
                                                     #,(answer-type))))
                              #,new-body)
                      (base-λ (#,v : #,new-hole-type)
                              (base-λ (#,k2 : (base-Π (_ : #,(answer-type)) #,(answer-type)))
                                      (base-app #,k2 (base-app #,k #,v)))))
                     (base-λ (#,x : #,(answer-type)) #,x))))])]))

  ;; translation of reset
  (define (cps-reset syn [env '()])
    (syntax-parse syn
      #:literals (base-app base-elim base-Π base-λ base-Unv)
      #:datum-literals (:)
      [(_ _ e)
       #:do [(define k (gensym1 syn "k"))
             (define x (gensym1 syn "x"))
             (define new-e (cps-top #'e env))]
       #`(base-λ (#,k : (base-Π (_ : #,(answer-type)) #,(answer-type)))
                 (base-app
                  #,k
                  (base-app #,new-e (base-λ (#,x : #,(answer-type)) #,x))))]))
  
  ;; check if an expression is a term, a type, or a universe
  (define (is-obj? t [env '()])
    (syntax-parse (cur-expand t #:local-env env)
      #:literals (base-app base-elim base-Π base-λ base-Unv)
      [(base-Unv i) false]
      [(base-Π (var : type) body) false]
      [(base-λ (var : type) body)
       (and (or (is-constr? #'type env) (is-unv? #'type env))
            (is-obj? #'body (extend-env env #'var #'type)))]
      [(base-app e1 e2)
     (or (and (is-obj? #'e1 env) (is-obj? #'e2 env))
         (and (is-obj? #'e1 env) (is-constr? #'e2 env)))]
      [(base-elim type motive methods e) true]
      [x:id (is-constr? (cur-type-infer #'x #:local-env env) env)]))
  
  (define (is-constr? t env)
    (syntax-parse (cur-expand t #:local-env env)
      #:literals (base-app base-elim base-Π base-λ base-Unv)
      [(base-Unv i) false]
      [(base-Π (var : type) body)
     (and (or (is-constr? #'type env) (is-unv? #'type env))
          (is-constr? #'body (extend-env env #'var #'type)))]
      [(base-λ (var : type) body)
       (and (or (is-constr? #'type env) (is-unv? #'type env))
            (is-constr? #'body (extend-env env #'var #'type)))]
      [(base-app e1 e2)
       (is-constr? #'e1 env)]
      [(base-elim type motive methods e) false]
      [a:id 
       (syntax-parse (cur-expand (cur-type-infer #'a #:local-env env) #:local-env env)
         #:literals (base-app base-elim base-Π base-λ base-Unv)
         [(base-Unv 0) true]
         [(base-Unv i) false]
         [(base-Π (var : type) body) true])]))
  
  (define (is-unv? t env)
    (syntax-parse (cur-expand t #:local-env env)
      #:literals (base-app base-elim base-Π base-λ base-Unv)
      [(base-Unv i) true]
      [(base-Π (var : type) body)
       (and (or (is-constr? #'type env) (is-unv? #'type env))
            (is-unv? #'body (extend-env env #'var #'type)))]
      [(base-app e1 e2)
       (syntax-parse (cur-expand (cur-type-infer t #:local-env env) #:local-env env)
         #:literals (base-app base-elim base-Π base-λ base-Unv)
         [(base-Unv 0) false]
         [(base-Unv i) true])]
      [a:id
       (syntax-parse (cur-expand (cur-type-infer #'a #:local-env env) #:local-env env)
         #:literals (base-app base-elim base-Π base-λ base-Unv)
         [(base-Unv 0) false]
         [(base-Unv i) true])]))
  )

;; debugging macros
(begin-for-syntax
  (require racket/trace (for-template racket/trace))
  (define (maybe-syntax->datum x)
    (if (syntax? x)
        (syntax->datum x)#; (read (open-input-string (+scopes x)))
        x))
  (current-trace-print-args
   (let ([ctpa (current-trace-print-args)])
     (lambda (s l kw l2 n)
       (ctpa s (map maybe-syntax->datum l) kw l2 n))))
  (current-trace-print-results
   (let ([ctpr (current-trace-print-results)])
     (lambda (s l n)
       (ctpr s (map maybe-syntax->datum l) n)))))

;; User interface
(define-syntax (reset syn)
  (syntax-parse syn
    [(_ hole e)
     #'hole]))

(define-syntax (shift syn)
  (syntax-parse syn
    [(_ hole e)
     #'hole]))

(define-syntax (cps syn)
  (syntax-parse syn
    [(_ (~optional (~seq #:constants (x:id ...)) #:defaults ([(x 1) null]))
        (~optional (~seq #:return ans:id) #:defaults ([ans #'(Type 0)]))
        e)
     (parameterize ([constants (attribute x) #;(immutable-free-id-set (attribute x))]
                    [answer-type (attribute ans)])
       (cps-top #'e '()))]))

(define-syntax (observe syn)
  (syntax-parse syn
    [(_ syn)
     (displayln (cur->datum (cur-normalize #'syn)))
     #'syn]))

;; tests. sort of
;; NB: We can only run terms of type (Type 0)
(axiom Entity : (Type 0))
(axiom Walk : (Pi (x : Entity) (Type 0)))
(axiom Love : (Pi (y : Entity) (Pi (x : Entity) (Type 0))))
(axiom Iff : (Pi (p1 : (Type 0)) (Pi (q1 : (Type 0)) (Type 0))))
(axiom EqNP : (Pi (x : Entity) (Pi (y : Entity) (Type 0))))
(axiom EqV : (Pi (p : (Pi (x : Entity) (Type 0)))
                 (Pi (q : (Pi (x : Entity) (Type 0))) (Type 0))))
(axiom EqVc : (Pi (p :
                     (Pi (x : Entity)
                         (Pi (_ : (Pi (_ : (Type 0)) (Type 0))) (Type 0))))
                  (Pi (q :
                         (Pi (x : Entity)
                             (Pi (_ : (Pi (_ : (Type 0)) (Type 0))) (Type 0))))
                      (Type 0))))
(axiom EqV2 : (Pi (p : (Pi (y : Entity) (Pi (x : Entity) (Type 0))))
                  (Pi (q : (Pi (y : Entity) (Pi (x : Entity) (Type 0)))) (Type 0))))
(axiom EqV2c : (Pi (p :
                      (Pi (y : Entity)
                          (Pi (_ :
                                 (Pi (_ :
                                        (Pi (x : Entity)
                                            (Pi (_ : (Pi (_ : (Type 0)) (Type 0))) (Type 0))))
                                     (Type 0)))
                              (Type 0))))
                   (Pi (q :
                          (Pi (y : Entity)
                              (Pi (_ :
                                     (Pi (_ :
                                            (Pi (x : Entity)
                                                (Pi (_ : (Pi (_ : (Type 0)) (Type 0))) (Type 0))))
                                         (Type 0)))
                                  (Type 0))))
                       (Type 0))))
(axiom Sigma : (Pi (A : (Type 0)) (P : (Pi (a : A) (Type 0))) (Type 0)))
(axiom Sigmac : (Pi (A : (Type 0))
                    (Pi (P :
                           (Pi (a : A)
                               (Pi (_ : (Pi (_ : (Type 0)) (Type 0))) (Type 0))))
                        (Type 0))))
(axiom j : Entity)
(axiom m : Entity)
(axiom hole : (Type 0))

#;(begin-for-syntax
  (trace cps-constant)
  )

;; application
(cps
 #:constants (Entity)
 (λ (f : (Π (_ : Entity) Entity))
   (λ (x : Entity) (f x))))

;; John walks
((cps
  #:constants (j Entity Walk)
  (Walk j))
 (λ (x : (Type 0)) x))

;; John loves Mary
((cps
  #:constants (j m Entity Love)
  (Love m j))
 (λ (x : (Type 0)) x))

;; term-level computation
(cps
 #:constants (j Entity)
 ((λ (x : Entity) x) j))

(cps
 #:constants (j Entity Walk)
 ((λ (p : (Π (x : Entity) (Type 0))) j) Walk))

(cps
 #:constants (j Entity Walk)
 (λ (p : (Walk j)) p))

;; trivial term-to-type shift
((cps
  #:constants (j Entity Walk)
  (reset
   hole
   (Walk
    (shift
     j
     (λ (k : (Π (_ : Entity) (Type 0))) (k j))))))
 (λ (x : (Type 0)) x))

;; John only loves MARY
(observe
 ((cps
   #:constants (j m Entity Love Iff EqNP)
   (reset
    hole
    (Love
     (shift m
            (λ (k : (Π (x : Entity) (Type 0)))
              (Π (x : Entity) (Iff (k x) (EqNP x m)))))
     j)))
  (λ (x : (Type 0)) x)))

;; John loves everyone
(observe
 ((cps
   #:constants (Entity Love m j)
   (reset
    hole
    (Love (shift m
                 (λ (k : (Π (x : Entity) (Type 0)))
                   (Π (x : Entity) (k x))))
          j)))
  (λ (x : (Type 0)) x)))

;; trivial type-to-type shift
(observe
 ((cps
   #:constants (j Entity Walk Walkc)
   (reset
    hole
    ((shift Walk
            (λ (k : (Π (f : (Π (x : Entity) (Type 0)))
                       (Type 0)))
              (k Walk)))
     j)))
  (λ (x : (Type 0)) x)))

(observe
 ((cps
   #:constants (j Entity Walk)
   (reset
    hole
    ((shift Walk
            (λ (k : (Π (f : (Π (x : Entity) (Type 0)))
                       (Type 0)))
              (Π (p : (Π (x : Entity) (Type 0)))
                 (k p))))
     j)))
  (λ (x : (Type 0)) x)))

;; John only WALKS
(observe
 ((cps
   #:constants (j Entity Walk Iff EqV EqVc)
   (reset
    hole
    ((shift Walk
            (λ (k : (Π (f : (Π (x : Entity) (Type 0)))
                       (Type 0)))
              (Π (p : (Π (x : Entity) (Type 0)))
                 (Iff (k p) (EqV p Walk)))))
     j)))
  (λ (x : (Type 0)) x)))

;; John only LOVES Mary
(observe
 ((cps
   #:constants (j m Entity Love Iff EqV2 EqV2c)
   (reset
    hole
    ((shift Love
            (λ (k : (Π (f : (Π (y : Entity) (Π (x : Entity) (Type 0))))
                       (Type 0)))
              (Π (p : (Π (y : Entity) (Π (x : Entity) (Type 0))))
                 (Iff (k p) (EqV2 p Love)))))
     m
     j)))
  (λ (x : (Type 0)) x)))

;; tests for Sigma; not yet supported
#;(require cur/stdlib/sigma)
;(axiom fst : (Pi (A : (Type 0)) (P : (Pi (a : A) (Type 0))) (p : (Sigma A P)) A))
;(axiom fstc : (cps #:constants (Sigma) (Pi (A : (Type 0)) (P : (Pi (a : A) (Type 0))) (p : (Sigma A P)) A)))

#;(observe
   (cps
    #:constants (j m Entity Love Sigma)
    (reset
     hole
     (Sigma Entity (λ (x : Entity) (Love j x))))))

#;(observe
   (cps
    #:constants (j m Entity Σ1 pair1 fst1 snd1 Σ0 pair0 fst0 snd0)
    (reset
     hole
     (λ (x : (Σ (x : Entity) (Love j x)))
       (fst x)))))
