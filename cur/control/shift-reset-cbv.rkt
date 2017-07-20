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

  (define (member? x l [env '()])
    (if (empty? l)
        #f
        (if (cur-equal? x (first l) #:local-env env) #t (member? x (rest l)))))

  ; CPS transformation
  ; env contains original type (for type inference)
  ; env2 contains CPSed type
  (define (cps-obj t [env '()] [env2 '()])
    (syntax-parse (cur-expand t #:local-env env #'shift #'reset)
      #:literals (base-app base-elim base-Π base-λ base-Unv shift reset)
      [(base-λ (var : type) body)
       (let* ([k (gensym1 t "k")]
              [new-type0 (cps-constr2 (cur-type-infer t #:local-env env) env env2)]
              [new-env (extend-env env #'var #'type)]
              [new-type (cps-type #'type env)]
              [new-env2 (extend-env env2 #'var new-type)]
              [new-body (cps-obj #'body new-env new-env2)])
       #`(base-λ (#,k : (base-Π (_ : #,new-type0) #,(answer-type)))
                 (base-app #,k (base-λ (var : #,new-type) #,new-body))))]
      [(base-app e1 e2)
       (let ([k (gensym1 t "k")]
             [m (gensym1 t "m")]
             [n (gensym1 t "n")]
             [new-type0 (cps-constr2 (cur-type-infer t #:local-env env) env env2)]
             [new-type1 (cps-constr2 (cur-type-infer #'e1 #:local-env env) env env2)]
             [new-type2 (cps-type (cur-type-infer #'e2 #:local-env env) env env2)]
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
       (cps-constant #'x env env2)]
      [x:id
       #:when (not (constant? #'x env))
       (let ([k (gensym1 t "k")]
             [new-type (cps-constr2 (cur-type-infer #'x #:local-env env))])
         #`(base-λ (#,k : (base-Π (_ : #,new-type) #,(answer-type))) (base-app #,k x)))]
      [(shift _ ...) (cps-shift this-syntax env env2)]
      [(reset _ ...) (error 'cps-obj "I don't know how to do object-level reset")]))

  (define (cps-type e [env '()] [env2 '()]) ;; value translation
    (if (is-constr? e env)
        (cps-constr2 e env env2)
        (cps-unv e env env2)))

  (define (cps-constr t [env '()] [env2 '()])
    (syntax-parse (cur-expand t #:local-env env #'shift #'reset)
      #:literals (base-app base-elim base-Π base-λ base-Unv shift reset)
      [(base-λ (var : type) body)
       (let* ([k (gensym1 t "k")]
              [new-env (extend-env env #'var #'type)]
              [new-type0 (cps-unv (cur-type-infer t #:local-env env) env env2)]
              [new-type (cps-type #'type env env2)]
              [new-env2 (extend-env env2 #'var new-type)]
              [new-body (cps-constr #'body new-env new-env2)])
         #`(base-λ (#,k : (base-Π (_ : #,new-type0) #,(answer-type)))
                   (base-app #,k (base-λ (var : #,new-type) #,new-body))))]
      [(base-app e1 e2)
       (if (member? #'e1 (captured-cont) env)
           (let* ([k (gensym1 t "k")]
                  [v (gensym1 t "v")]
                  [type2 (cur-type-infer #'e2 #:local-env env)])
               #`(base-λ (#,k : (base-Π (_ : #,(answer-type)) #,(answer-type)))
                         (base-app #,(cps-top #'e2 env env2) #;e1
                                   (base-λ (#,v : #,(cps-type type2 env env2))
                                           (base-app (base-app e1 #,v) #,k)))))
           (let* ([k (gensym1 t "k")]
                  [m (gensym1 t "m")]
                  [n (gensym1 t "n")]
                  [type0 (cur-type-infer t #:local-env env)]
                  [new-type0 (cps-unv type0 env env2)]
                  [new-type1 (cps-unv (cur-type-infer #'e1 #:local-env env) env env2)]
                  [new-type2 (cps-unv (cur-type-infer #'e2 #:local-env env) env env2)]
                  [new-e1 (cps-constr #'e1 env env2)]
                  [new-e2 (cps-top #'e2 env env2)])
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
              [new-type (cps-type #'type env env2)]
              [new-env (extend-env env #'var #'type)]
              [new-env2 (extend-env env2 #'var new-type)]
              [new-body #`(base-app #,(cps-constr #'body new-env new-env2)
                                    (base-λ (#,x : (base-Unv 0)) #,x))])
                        ;; locally run the body
         #`(base-λ (#,k : (base-Π (_ : (base-Unv 0)) #,(answer-type)))
                   (base-app #,k (base-Π (var : #,new-type) #,new-body))))]
      [a:id
       #:when (constant? #'a env)
       (cond
         [(cur-equal? #'a #`EqV #:local-env env)
          (cps-eqv env env2)]
         [(cur-equal? #'a #`EqV2 #:local-env env)
          (cps-eqv2 env env2)]
         [(cur-equal? #'a #`Sigma #:local-env env)
          (cps-sigma env env2)]
         [else (cps-constant #'a env env2)])]
      [x:id
       #:when (not (constant? #'x env))
       (let ([k (gensym1 t "k")]
             [new-type (cps-unv (cur-type-infer #'x #:local-env env))])
         #`(base-λ (#,k : (base-Π (_ : #,new-type) #,(answer-type))) (base-app #,k x)))]
      [(shift _ ...) (cps-shift this-syntax env env2)]
      [(reset _ ...) (cps-reset this-syntax env env2)]))

  (define (cps-constr2 t [env '()] [env2 '()])
    (syntax-parse (cur-expand t)
      #:literals (base-app base-elim base-Π base-λ base-Unv)
      [(base-λ (var : type) body)
       (let* ([new-env (extend-env env #'var #'type)]
              [new-type (cps-type #'type env env2)]
              [new-env2 (extend-env env2 #'var new-type)]
              [new-body (cps-constr2 #'body new-env new-env2)])
         #`(base-λ (var : #,new-type) #,new-body))]
      [(base-app e1 e2)
       (let ([new-e1 (cps-constr2 #'e1 env env2)]
             [new-e2 (if (is-obj? #'e2 env)
                         #'e2
                         (cps-constr2 #'e2 env env2))])
         #`(base-app #,new-e1 #,new-e2))]     
      [(base-Π (var : type) body)
       (let* ([new-env (extend-env env #'var #'type)]
              [new-type (cps-type #'type env env2)]
              [new-env2 (extend-env env2 #'var #'type)]
              [new-body (cps-top2 #'body new-env new-env2)])
         #`(base-Π (var : #,new-type) #,new-body))]
      [a:id #`a]))
  
  (define (cps-unv t [env '()] [env2 '()])
    (syntax-parse (cur-expand t)
      #:literals (base-app base-elim base-Π base-λ base-Unv)
      [(base-Unv i) #`(base-Unv i)]
      [(base-Π (var : type) body)
       (let* ([new-env (extend-env env #'var #'type)]
              [new-type (cps-type #'type env env2)]
              [new-env2 (extend-env env2 #'var new-type)]
              [new-body (cps-top #'body new-env new-env2)])
       #`(base-Π (var : #,new-type) #,new-body))]
      [a:id #'a]))

  (define (cps-unv2 t [env '()] [env2 '()])
    (syntax-parse (cur-expand t)
      #:literals (base-app base-elim base-Π base-λ base-Unv)
      [(base-Unv i) #`(base-Unv i)]
      [(base-Π (var : type) body)
       (let* ([new-env (extend-env env #'var #'type)]
              [new-type (cps-top2 #'type env env2)]
              [new-env2 (extend-env env2 #'var #'type2)]
              [new-body (cps-unv2 #'body new-env new-env2)])
         #`(base-Π (var : #,new-type) #,new-body))]))

  (define (cps-constant c env env2)
    (let ([type (cur-type-infer c #:local-env env)])
      (syntax-parse (cur-expand type)
        #:literals (base-Π)
        [(base-Π (var : ann) result)
         (let* ([k (gensym1 c "k")]
                [x (gensym1 c "x")]
                [new-type (cps-unv type env env2)]
                [new-ann (cps-type #'ann env env2)]
                [new-env (extend-env env #'var #'ann)]
                [new-env2 (extend-env env #'var new-ann)]
                [new-c (cps-constant (cur-normalize #`(base-app #,c var)
                                                        #:local-env new-env2)
                                     new-env
                                     new-env2)])
           #`(base-λ (#,k : (base-Π (_ : #,new-type) #,(answer-type)))
                     (base-app #,k (base-λ (var : #,new-ann) #,new-c))))]
        [result
         (let ([k (gensym1 c "k")])
           #`(base-λ (#,k : (base-Π (_ : #,type) #,(answer-type)))
                     (base-app #,k #,c)))])))

  (define (cps-top t [env '()] [env2 '()])
    (cond
      [(is-obj? t env) (cps-obj t env env2)]
      [(is-constr? t env) (cps-constr t env env2)]
      [(is-unv? t env)
       #`(base-Π (_ : (base-Π (_ : #,(cps-unv t env)) #,(answer-type))) #,(answer-type))]
      [else (error 'cps-top "Something terrible happened: ~a is not anything I know about.~n" t)]))

  (define (cps-top2 t [env '()] [env2 '()])
    (cond
      [(is-obj? t env) (cps-obj t env env2)]
      [(is-constr? t env)
       #`(base-Π (_ : (base-Π (_ : #,(cps-constr2 t env env2)) #,(answer-type))) #,(answer-type))]
      [(is-unv? t env) (cps-unv2 t env env2)]
      [else (error 'cps-top2 "Something terrible happened: ~a is not anything I know about.~n" t)]))

  (define (cps-shift syn [env '()] [env2 '()])
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
               [new-type #`(Π (_ : #,(cps-unv #'type env env2)) ans)]
               [new-env (extend-env env #'var #`(base-Π (_ : type) ans))]
               [new-env2 (extend-env env2 #'var new-type)]
               [new-body (parameterize ([captured-cont (cons #'var (captured-cont))])
                           (cps-top #'body new-env new-env2))]
               [new-hole-type (cps-type #'type env env2)]) 
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

(define (cps-reset syn [env '()] [env2 '()])
  (syntax-parse syn
    #:literals (base-app base-elim base-Π base-λ base-Unv)
    #:datum-literals (:)
    [(_ _ e)
     #:do [(define k (gensym1 syn "k"))
           (define x (gensym1 syn "x"))
           (define new-e (cps-top #'e env env2))]
     #`(base-λ (#,k : (base-Π (_ : #,(answer-type)) #,(answer-type)))
               (base-app
                #,k
                (base-app #,new-e (base-λ (#,x : #,(answer-type)) #,x))))]))

(define (cps-eqv [env '()] [env2 '()])
     (let* ([k0 (gensym1 #`EqV "k")]
            [k1 (gensym1 #`EqV "k")]
            [k2 (gensym1 #`EqV "k")]
            [p (gensym1 #`EqV "p")]
            [q (gensym1 #`EqV "q")]
            [new-type0
             (cps-unv (cur-type-infer #`EqV #:local-env env) env env2)]
            [new-type1
             (cps-unv #`(base-Π (q : (base-Π (x : Entity) (base-Unv 0))) (base-Unv 0)) env env2)]
            [new-ann (cps-unv #`(base-Π (x : Entity) (base-Unv 0)) env env2)])
       #`(base-λ (#,k0 : (base-Π (_ : #,new-type0) #,(answer-type)))
               (base-app #,k0
                         (base-λ (#,p : #,new-ann)
                                 (base-λ (#,k1 : (base-Π (_ : #,new-type1) #,(answer-type)))
                                         (base-app #,k1
                                                   (base-λ (#,q : #,new-ann)
                                                           (base-λ (#,k2 : (base-Π (_ : (base-Unv 0)) (base-Unv 0)))
                                                                   (base-app #,k2 (base-app (base-app EqVc #,p) #,q)))))))))))

;; TODO: Need better mechanism for adding new constants.
(define (cps-eqv2 [env '()] [env2 '()])
     (let* ([k0 (gensym1 #`EqV2 "k")]
            [k1 (gensym1 #`EqV2 "k")]
            [k2 (gensym1 #`EqV2 "k")]
            [p (gensym1 #`EqV2 "p")]
            [q (gensym1 #`EqV2 "q")]
            [new-type0
             (cps-unv (cur-type-infer #`EqV2 #:local-env env) env env2)]
            [type1 #`(base-Π (q : (base-Π (y : Entity) (base-Π (x : Entity) (base-Unv 0)))) (base-Unv 0))]
            [new-type1 
             (cps-unv #`(Π (q : (Π (y : Entity) (Π (x : Entity) (Type 0)))) (Type 0)) env env2)]
            [new-ann (cps-unv #`(base-Π (y : Entity) (base-Π (x : Entity) (base-Unv 0))) env env2)])
       #`(base-λ (#,k0 : (base-Π (_ : #,new-type0) #,(answer-type)))
               (base-app #,k0
                         (base-λ (#,p : #,new-ann)
                                 (base-λ (#,k1 : (base-Π (_ : #,new-type1) #,(answer-type)))
                                         (base-app #,k1
                                                   (base-λ (#,q : #,new-ann)
                                                           (base-λ (#,k2 : (base-Π (_ : (base-Unv 0)) (base-Unv 0)))
                                                                   (base-app #,k2 (base-app (base-app EqV2c #,p) #,q)))))))))))

(define (cps-sigma [env '()] [env2 '()])
     (let* ([k0 (gensym1 #`Sigma "k")]
            [k1 (gensym1 #`Sigma "k")]
            [k2 (gensym1 #`Sigma "k")]
            [a (gensym1 #`Sigma "a")]
            [p (gensym1 #`Sigma "p")]
            [new-env (extend-env env a #`(base-Unv 0))]
            [new-env2 (extend-env env2 a #`(base-Unv 0))]
            [new-type0 (cps-unv #`(base-Π (#,a : (base-Unv 0))
                                          (base-Π (#,p : (base-Π (_ : #,a) (base-Unv 0))) (base-Unv 0)))
                                env
                                env2)]
            [new-type1 (cps-unv #`(base-Π (#,p : (base-Π (_ : #,a) (base-Unv 0))) (base-Unv 0)) new-env new-env2)]
            [new-ann2 (cps-unv #`(base-Π (_ : #,a) (base-Unv 0)) new-env new-env2)])
       #`(base-λ (#,k0 : (base-Π (_ : #,new-type0) #,(answer-type)))
               (base-app #,k0
                         (base-λ (#,a : (base-Unv 0))
                                 (base-λ (#,k1 : (base-Π (_ : #,new-type1) #,(answer-type)))
                                         (base-app #,k1
                                                   (base-λ (#,p : #,new-ann2)
                                                           (base-λ (#,k2 : (base-Π (_ : (base-Unv 0)) (base-Unv 0)))
                                                                   (base-app #,k2 (base-app (base-app Sigmac #,a) #,p)))))))))))

; unCPS transformation

(define (uncps-obj t [env '()])
    (syntax-parse (cur-expand t #:local-env env #'shift)
      #:literals (base-app base-elim base-Π base-λ base-Unv)
      [(base-λ (var : type) body)
       (let* ([new-env (extend-env env #'var #'type)]
              [new-type (uncps-type #'type env)]
              [new-body (uncps-obj #'body new-env)])
       #`(base-λ (var : type) #,new-body))]
      [(base-app e1 e2)
       (let ([new-e1 (uncps-obj #'e1 env)]
             [new-e2 (uncps-top #'e2 env)])
       #`(base-app #,new-e1 #,new-e2))]
      [(shift _ ...) this-syntax]
      [x:id #'x]))

(define (uncps-constr-com t [env '()])
  (syntax-parse (cur-expand t)
    #:literals (base-app base-elim base-Π base-λ base-Unv :)
    [x:id
     #:when (not (constant? #'x env))
     #'x]
    [(base-λ (a : type) body)
     (syntax-parse (cur-expand #'body)
       #:literals (base-app base-elim base-Π base-λ base-Unv :)
       [(base-λ (k : type2) ans)
        (uncps-constr-ans #'ans
                          (extend-env (extend-env env #'a #'type) #'k #'type2))])]
    [(base-app m n)
     #`(base-app #,(uncps-constr-val #'m env)
                 #,(uncps-constr-arg #'n env))]))

(define (uncps-constr-val t [env '()])
  (syntax-parse (cur-expand t)
    #:literals (base-app base-elim base-Π base-λ base-Unv)
    [(base-λ (var : type) body)
     (let ([new-type (uncps-type #'type env)])
       #`(base-λ (var : #,new-type)
                 #,(uncps-constr-com #'body (extend-env env #'var new-type))))]
    [(base-Π (var : type) body)
     (let ([new-type (uncps-type #'type env)])
       #`(base-Π (var : #,new-type)
                 #,(uncps-type #'body (extend-env env #'var #'type))))]
    [c:id
     #:when (constant? #'c env)
     #'c]
    [(base-app c e) ;; c x1 x2 ...
     t]))

(define (uncps-constr-arg t [env '()])
  (syntax-parse (cur-expand t)
    #:literals (base-app base-elim base-Π base-λ base-Unv)
    [(base-λ (k : type) ans)
     (uncps-constr-ans #'ans env)]
    [x:id #'x]))

(define (uncps-constr-ans t [env '()])
  (syntax-parse (cur-expand t)
    #:literals (base-app base-elim base-Π base-λ base-Unv)
    [(base-app e1 e2)
       (if (is-cnt? #'e1 env)
           (plug (uncps-constr-val #'e2 env) (uncps-constr-cnt #'e1 env))
           (plug (uncps-constr-com #'e1 env) (uncps-constr-cnt #'e2 env)))]))

(define (uncps-constr-cnt t [env '()])
  (syntax-parse (cur-expand t)
    #:literals (base-app base-elim base-Π base-λ base-Unv)
    [k:id '()]
    [(base-λ (var : type) body)
     (syntax-parse (cur-expand #'body)
       #:literals (base-app base-elim base-Π base-λ base-Unv)
       [(base-app (base-app m n) k)
        (cons (uncps-constr-arg #'n env) (uncps-constr-cnt #'k env))])]))

(define (plug t k)
  (if (empty? k)
      t
      (plug #`(base-app #,t #,(first k)) (rest k))))

(define (uncps-type t [env '()])
  (if (is-constr? t env)
      (syntax-parse (cur-expand t)
        #:literals (base-app base-elim base-Π base-λ base-Unv)
        [(base-app e id)
         (uncps-constr-com #'e env)]
        [a:id #'a])
      (uncps-unv-top t env)))

(define (uncps-unv t [env '()])
  (syntax-parse (cur-expand t)
    #:literals (base-app base-elim base-Π base-λ base-Unv)
    [(base-Unv i) t]
    [(base-Π (var : type) body)
     (let ([new-type (uncps-type #'type env)])
       #`(base-Π (var : #,new-type) #,(uncps-unv-top #'body (extend-env env #'var #'type))))]
    [a:id #'a]))

(define (uncps-unv-top t [env '()])
  (syntax-parse (cur-expand t)
    #:literals (base-app base-elim base-Π base-λ base-Unv)
    #:datum-literals (:)
       [(base-Π (k : (base-Π (_ : type) ans)) ans2)
        (uncps-unv #'type env)])) 

(define (uncps-top t [env '()])
  (cond
    [(is-obj? t env) (uncps-obj t env)]
    [(is-constr? t env) (uncps-constr-com t env)]
    [(is-unv? t env) (uncps-unv-top t env)]))

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

(define (is-cnt? t env)
  (syntax-parse (cur-expand t #:local-env env)
    #:literals (base-app base-elim base-Π base-λ base-Unv)
    #:datum-literals (:)
    [(base-λ (m : type) (base-app (base-app m2 n) k)) true]
    [k:id true]
    [else false])))

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
       (cps-top #'e '() '()))]))

(define-syntax (uncps syn)
  (syntax-parse syn
    [(_ (~optional (~seq #:constants (x:id ...)) #:defaults ([(x 1) null]))
        e)
     (parameterize ([constants (attribute x)])
       (uncps-top #'e '()))]))

(define-syntax (observe syn)
  (syntax-parse syn
    [(_ syn)
     (displayln (cur->datum (cur-normalize #'syn)))
     #'syn]))

;; tests. sort of
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
(axiom hole-e : Entity)

#;(begin-for-syntax
    (trace cps-obj)
    (trace cps-constr))

;;application
(cps
 #:constants (Entity)
 (λ (f : (Π (_ : Entity) Entity))
   (λ (x : Entity) (f x))))

((cps
  #:constants (j Entity Walk)
  (Walk j))
 (λ (x : (Type 0)) x))

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
