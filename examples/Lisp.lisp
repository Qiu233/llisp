(defun caar (xs) (car (car xs)))
(defun cdar (xs) (cdr (car xs)))
(defun cddr (xs) (cdr (cdr xs)))
(defun cddar (xs) (cdr (cdr (car xs))))
(defun cadar (xs) (car (cdr (car xs))))
(defun caddar (xs) (car (cdr (cdr (car xs)))))
(defun cadddr (xs) (car (cdr (cdr (cdr xs)))))
(defun caddr (xs) (car (cdr (cdr xs))))
(defun cadr (xs) (car (cdr xs)))

(defun lookup (x env)
  (cond ((null? env) (error -1))
        ((eq? x (caar env)) (cdar env))
        (else (lookup x (cdr env)))))

(defun pairlis (xs ys env)
  (if (null? xs)
      env
      (cons (cons (car xs) (car ys))
            (pairlis (cdr xs) (cdr ys) env))))

(defun evlis (exps env)
  (if (null? exps)
      '()
      (cons (car (eval (car exps) env))
            (evlis (cdr exps) env))))

;; eval_seq : exp list -> env -> (value . env)
(defun evcon (clauses env)
  (cond ((null? clauses) (error -2))
        ((car (eval (caar clauses) env))
         (eval_seq (cdar clauses) env))
        (else
         (evcon (cdr clauses) env))))

;; eval_seq : exp list -> env -> (value . env)
(defun eval_seq (clauses env)
  (cond ((null? clauses) (error -4))
        ((null? (cdr clauses)) (eval (car clauses) env))
        (else
          (seq
            (define result (eval (car clauses) env))
            (eval_seq (cdr clauses) (cdr result))
          )
        )
         ))

(defun eval* (exp env) (car (eval exp env)))

;; eval : exp -> env -> (value . env)
(defun eval (exp env)
  (seq '()
  (cond
    ((num? exp)
      (cons exp env))

    ((symbol? exp)
      (cond ((eq? exp 'else) (cons 0 env))
            ((eq? exp 'true) (cons 0 env))
            ((eq? exp 'false) (cons '() env))
            ((eq? exp 'layer) (cons 0 env))
            (else (cons (lookup exp env) env))
            ))

    ((pair? exp)
      (seq
        (define head (car exp))
        (cond
          ((symbol? head)
            (cond
              ((eq? head 'quote)
                (cons (cadr exp) env))
              ((eq? head 'repr)
                (cons (cons 'quote (cons (cadr exp) '())) env))
              ((eq? head 'print)
                (cons (print (eval* (cadr exp) env)) env))

              ((eq? head 'seq)
                (eval_seq (cdr exp) env))

              ;; (define v val)
              ((eq? head 'define)
                (seq
                  (define vname  (cadr exp))
                  (define val    (eval* (caddr exp) env))
                  (define env_   (cons (cons vname val) env))
                  (cons '() env_)))

              ;; (defun f (x y) body1 body2)
              ((eq? head 'defun)
                (seq
                  (define fname  (cadr exp))
                  (define lam_body  (cddr exp))
                  (define val    (cons 'lambda lam_body))
                  (define env_   (cons (cons fname val) env))
                  (cons '() env_)))

              ((eq? head 'lambda) (cons exp env)) ;; return directly

              ((and (eq? head 'and)
                    (pair? (cdr exp)))
              (if (eval* (cadr exp) env)
                  (if (eval* (caddr exp) env)
                      (cons true env)
                      (cons false env))
                  (cons false env)))

              ((and (eq? head 'if) (pair? (cdr exp))
                    (pair? (cddr exp)))
                  (if (eval* (cadr exp) env)
                        (eval (caddr exp) env)
                        (eval (cadddr exp) env)))

              ((eq? head 'null?)
                (cons (null? (eval* (cadr exp) env)) env))

              ((eq? head 'error)
                (error (eval* (cadr exp) env)))

              ((eq? head 'pair?)
                (cons (pair? (eval* (cadr exp) env)) env))

              ((eq? head 'symbol?)
                (cons (symbol? (eval* (cadr exp) env)) env))

              ((eq? head 'num?)
                (cons (num? (eval* (cadr exp) env)) env))

              ((eq? head 'atom?)
                (cons (atom? (eval* (cadr exp) env)) env))

              ((eq? head 'eq?)
                (cons (eq?
                      (eval* (cadr exp) env)
                      (eval* (caddr exp) env)) env))

              ((eq? head 'car)
                (cons (car (eval* (cadr exp) env)) env))

              ((eq? head 'cdr)
                (cons (cdr (eval* (cadr exp) env)) env))

              ((eq? head 'cons)
                (cons (cons
                      (eval* (cadr exp) env)
                      (eval* (caddr exp) env)) env))

              ((eq? head 'cond)
                (evcon (cdr exp) env))

              ((eq? head '+)
                (cons (+
                      (eval* (cadr exp) env)
                      (eval* (caddr exp) env)) env))
              ((eq? head '-)
                (cons (-
                      (eval* (cadr exp) env)
                      (eval* (caddr exp) env)) env))
              ((eq? head '*)
                (cons (*
                      (eval* (cadr exp) env)
                      (eval* (caddr exp) env)) env))
              ((eq? head '/)
                (cons (/
                      (eval* (cadr exp) env)
                      (eval* (caddr exp) env)) env))

              (else
                (eval (cons (lookup head env) (cdr exp)) env))))

          ;; ((lambda (x y) body1 body2) a1 a2)
          ((and (pair? head)
                (eq? (caar exp) 'lambda))
            (seq
              (define params (cadar exp))
              (define body   (cddar exp))
              (define args   (evlis (cdr exp) env))
              (define env_   (pairlis params args env))
              (eval_seq body env_)))
          (else
            (error -3)))))
    (else
     (error -5)
     ))))

(defun wrap (layer code)

`(seq

(defun caar (xs) (car (car xs)))
(defun cdar (xs) (cdr (car xs)))
(defun cddr (xs) (cdr (cdr xs)))
(defun cddar (xs) (cdr (cdr (car xs))))
(defun cadar (xs) (car (cdr (car xs))))
(defun caddar (xs) (car (cdr (cdr (car xs)))))
(defun cadddr (xs) (car (cdr (cdr (cdr xs)))))
(defun caddr (xs) (car (cdr (cdr xs))))
(defun cadr (xs) (car (cdr xs)))

(defun lookup (x env)
  (cond ((null? env) (error -1))
        ((eq? x (caar env)) (cdar env))
        (else (lookup x (cdr env)))))

(defun pairlis (xs ys env)
  (if (null? xs)
      env
      (cons (cons (car xs) (car ys))
            (pairlis (cdr xs) (cdr ys) env))))

(defun evlis (exps env)
  (if (null? exps)
      '()
      (cons (car (eval (car exps) env))
            (evlis (cdr exps) env))))

;; eval_seq : exp list -> env -> (value . env)
(defun evcon (clauses env)
  (cond ((null? clauses) (error -2))
        ((car (eval (caar clauses) env))
         (eval_seq (cdar clauses) env))
        (else
         (evcon (cdr clauses) env))))

;; eval_seq : exp list -> env -> (value . env)
(defun eval_seq (clauses env)
  (cond ((null? clauses) (error -4))
        ((null? (cdr clauses)) (eval (car clauses) env))
        (else
          (seq
            (define result (eval (car clauses) env))
            (eval_seq (cdr clauses) (cdr result))
          )
        )
         ))

(defun eval* (exp env) (car (eval exp env)))

;; eval : exp -> env -> (value . env)
(defun eval (exp env)
  (seq '()
  (cond
    ((num? exp)
      (cons exp env))

    ((symbol? exp)
      (cond ((eq? exp 'else) (cons 0 env))
            ((eq? exp 'true) (cons 0 env))
            ((eq? exp 'false) (cons '() env))
            ((eq? exp 'layer) (cons ,layer env))
            (else (cons (lookup exp env) env))
            ))

    ((pair? exp)
      (seq
        (define head (car exp))
        (cond
          ((symbol? head)
            (cond
              ((eq? head 'quote)
                (cons (cadr exp) env))
              ((eq? head 'repr)
                (cons (cons 'quote (cons (cadr exp) '())) env))
              ((eq? head 'print)
                (cons (print (eval* (cadr exp) env)) env))

              ((eq? head 'seq)
                (eval_seq (cdr exp) env))

              ;; (define v val)
              ((eq? head 'define)
                (seq
                  (define vname  (cadr exp))
                  (define val    (eval* (caddr exp) env))
                  (define env_   (cons (cons vname val) env))
                  (cons '() env_)))

              ;; (defun f (x y) body1 body2)
              ((eq? head 'defun)
                (seq
                  (define fname  (cadr exp))
                  (define lam_body  (cddr exp))
                  (define val    (cons 'lambda lam_body))
                  (define env_   (cons (cons fname val) env))
                  (cons '() env_)))

              ((eq? head 'lambda) (cons exp env)) ;; return directly

              ((and (eq? head 'and)
                    (pair? (cdr exp)))
              (if (eval* (cadr exp) env)
                  (if (eval* (caddr exp) env)
                      (cons true env)
                      (cons false env))
                  (cons false env)))

              ((and (eq? head 'if) (pair? (cdr exp))
                    (pair? (cddr exp)))
                  (if (eval* (cadr exp) env)
                        (eval (caddr exp) env)
                        (eval (cadddr exp) env)))

              ((eq? head 'null?)
                (cons (null? (eval* (cadr exp) env)) env))

              ((eq? head 'error)
                (error (eval* (cadr exp) env)))

              ((eq? head 'pair?)
                (cons (pair? (eval* (cadr exp) env)) env))

              ((eq? head 'symbol?)
                (cons (symbol? (eval* (cadr exp) env)) env))

              ((eq? head 'num?)
                (cons (num? (eval* (cadr exp) env)) env))

              ((eq? head 'atom?)
                (cons (atom? (eval* (cadr exp) env)) env))

              ((eq? head 'eq?)
                (cons (eq?
                      (eval* (cadr exp) env)
                      (eval* (caddr exp) env)) env))

              ((eq? head 'car)
                (cons (car (eval* (cadr exp) env)) env))

              ((eq? head 'cdr)
                (cons (cdr (eval* (cadr exp) env)) env))

              ((eq? head 'cons)
                (cons (cons
                      (eval* (cadr exp) env)
                      (eval* (caddr exp) env)) env))

              ((eq? head 'cond)
                (evcon (cdr exp) env))

              ((eq? head '+)
                (cons (+
                      (eval* (cadr exp) env)
                      (eval* (caddr exp) env)) env))
              ((eq? head '-)
                (cons (-
                      (eval* (cadr exp) env)
                      (eval* (caddr exp) env)) env))
              ((eq? head '*)
                (cons (*
                      (eval* (cadr exp) env)
                      (eval* (caddr exp) env)) env))
              ((eq? head '/)
                (cons (/
                      (eval* (cadr exp) env)
                      (eval* (caddr exp) env)) env))

              (else
                (eval (cons (lookup head env) (cdr exp)) env))))

          ;; ((lambda (x y) body1 body2) a1 a2)
          ((and (pair? head)
                (eq? (caar exp) 'lambda))
            (seq
              (define params (cadar exp))
              (define body   (cddar exp))
              (define args   (evlis (cdr exp) env))
              (define env_   (pairlis params args env))
              (eval_seq body env_)))
          (else
            (error -3)))))
    (else
     (error -5)
     ))))

(eval* (quote ,code) '())

))

;; (eval* (wrap 2 (wrap 1 '((lambda (x) (car x)) (cons layer 2)))) '())

(eval* $CODE '())
