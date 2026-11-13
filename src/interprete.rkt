#lang eopl
;Autores: Juan Felipe Aristizabal 2459364-3743, Juan Sebastian Huertas 2459505-3743

#|
  Taller 3 — Cauca con referencias y tipos.
  Evaluación y punto de entrada.

  evaluar-expresion recorre el árbol con cases y apply-procedure liga
  los parámetros de una clausura antes de evaluar su cuerpo. Las dos se
  llaman mutuamente, así que comparten módulo, y con ellas la copia por
  valor de los argumentos, que describe cómo entra un valor a apply y no
  cómo está hecha la clausura.

  El evaluador ignora las anotaciones de tipo: las lee el parser, quedan
  en el árbol y solo las usa el chequeador.

  Las cláusulas de newref-exp, deref-exp, setref-exp, swap-exp y
  begin-exp van en evaluar-expresion, junto a las demás variantes.
  Las tres que verifican con referencia? antes de tocar el almacén son
  deref-exp, setref-exp y swap-exp; si el valor no es una referencia,
  levantan eopl:error.
|#

(require "sintaxis.rkt")
(require "almacen.rkt")
(require "ambiente.rkt")
(require "primitivas.rkt")

;; copia-por-valor : valor -> valor
;; El paso por valor entrega una copia del argumento. Para un número, un
;; booleano o un procedimiento la copia es el mismo valor; para una
;; referencia es una celda nueva con el mismo contenido. applyref no usa
;; esta función: ahí el parámetro queda ligado a la misma celda.
(define copia-por-valor
  (lambda (val)
    (if (referencia? val)
        (newref! (deref val))
        val)))

;; apply-procedure : procval x lista de valores -> valor
;; Verifica la aridad y evalúa el cuerpo en el ambiente de la clausura
;; extendido con los parámetros.
(define apply-procedure
  (lambda (proc args)
    (cases procval proc
      (cerradura (ids body env)
        (if (= (length ids) (length args))
            (evaluar-expresion body (ambiente-extendido ids args env))
            (eopl:error 'apply-procedure
                        "el procedimiento espera ~s argumento(s) y recibio ~s"
                        (length ids) (length args)))))))

;; evaluar-rands : lista de expresiones x ambiente -> lista de valores
;; Evalúa las expresiones de izquierda a derecha en el mismo ambiente.
(define evaluar-rands
  (lambda (rands env)
    (if (null? rands)
        '()
        (let ((primero (evaluar-expresion (car rands) env)))
          (cons primero (evaluar-rands (cdr rands) env))))))

;; seleccionar-caso : num x lista de num x lista de expresiones x expresion x ambiente -> valor
;; Evalúa la rama cuyo literal coincide con el control, o la de otherwise.
(define seleccionar-caso
  (lambda (control valores acciones default env)
    (cond ((null? valores) (evaluar-expresion default env))
          ((= control (car valores)) (evaluar-expresion (car acciones) env))
          (else (seleccionar-caso control (cdr valores) (cdr acciones) default env)))))

;; exigir-referencia : valor x symbol -> referencia
;; Retorna el valor si es una referencia; si no, levanta eopl:error.
(define exigir-referencia
  (lambda (val quien)
    (if (referencia? val)
        val
        (eopl:error quien "se esperaba una referencia y llego ~s" val))))

;; evaluar-begin : expresion x lista de expresiones x ambiente -> valor
;; Evalúa en orden y retorna el valor de la última.
(define evaluar-begin
  (lambda (exp exps env)
    (let ((val (evaluar-expresion exp env)))
      (if (null? exps)
          val
          (evaluar-begin (car exps) (cdr exps) env)))))

;; buscar-referencias : lista de symbol x ambiente -> lista de referencias
;; Busca cada identificador y verifica que esté ligado a una referencia.
(define buscar-referencias
  (lambda (ids env)
    (if (null? ids)
        '()
        (let ((val (apply-env env (car ids))))
          (if (referencia? val)
              (cons val (buscar-referencias (cdr ids) env))
              (eopl:error 'applyref
                          "el paso por referencia exige variables ligadas a referencias: ~s no lo es"
                          (car ids)))))))

;; evaluar-expresion : expresion x ambiente -> valor
;; Una cláusula por variante de la gramática. La condición de un if se
;; verifica con boolean? antes de ramificar.
(define evaluar-expresion
  (lambda (exp env)
    (cases expresion exp
      (lit-exp (dato) dato)
      (var-exp (id) (apply-env env id))
      (true-exp () #t)
      (false-exp () #f)
      (prim-exp (prim rands)
        (evaluar-primitiva prim (evaluar-rands rands env)))
      (if-exp (test true-exp false-exp)
        (let ((test-value (evaluar-expresion test env)))
          (if (boolean? test-value)
              (if test-value
                  (evaluar-expresion true-exp env)
                  (evaluar-expresion false-exp env))
              (eopl:error 'if-exp "la condicion debe ser booleana y llego ~s" test-value))))
      (let-exp (ids rands body)
        (let ((valores (evaluar-rands rands env)))
          (evaluar-expresion body (ambiente-extendido ids valores env))))
      (proc-exp (ids tipos body)
        (cerradura ids body env))
      (app-exp (rator rands)
        (let ((proc (evaluar-expresion rator env)))
          (if (procval? proc)
              (apply-procedure proc (map copia-por-valor (evaluar-rands rands env)))
              (eopl:error 'app-exp "~s no es un procedimiento" proc))))
      (letrec-exp (tipos-res proc-names idss tipos-args bodies letrec-body)
        (evaluar-expresion letrec-body
                           (ambiente-recursivo proc-names idss bodies env)))
      (case-exp (exp valores acciones default)
        (let ((control (evaluar-expresion exp env)))
          (if (number? control)
              (seleccionar-caso control valores acciones default env)
              (eopl:error 'case "el control debe ser numero y llego ~s" control))))
      (newref-exp (exp)
        (newref! (evaluar-expresion exp env)))
      (deref-exp (exp)
        (deref (exigir-referencia (evaluar-expresion exp env) 'deref)))
      (setref-exp (ref-exp val-exp)
        (let* ((ref (evaluar-expresion ref-exp env))
               (val (evaluar-expresion val-exp env)))
          (setref! (exigir-referencia ref 'setref) val)
          1))
      (swap-exp (exp1 exp2)
        (let* ((ref1 (exigir-referencia (evaluar-expresion exp1 env) 'swap))
               (ref2 (exigir-referencia (evaluar-expresion exp2 env) 'swap))
               (val1 (deref ref1))
               (val2 (deref ref2)))
          (setref! ref1 val2)
          (setref! ref2 val1)
          val2))
      (begin-exp (exp exps)
        (evaluar-begin exp exps env))
      (app-ref-exp (rator ids)
        (let ((proc (evaluar-expresion rator env)))
          (if (procval? proc)
              (apply-procedure proc (buscar-referencias ids env))
              (eopl:error 'applyref "~s no es un procedimiento" proc)))))))

;; evaluar-programa : programa -> valor
;; Deja el almacén vacío y evalúa el cuerpo en el ambiente inicial.
(define evaluar-programa
  (lambda (pgm)
    (initialize-store!)
    (cases programa pgm
      (a-program (exp)
        (evaluar-expresion exp (ambiente-inicial))))))

;; interpretar : string -> valor
;; Analiza el texto con el parser y lo evalúa.
(define interpretar
  (lambda (texto)
    (evaluar-programa (parser texto))))

;; interpretador : -> void
;; El ciclo de lectura, con sllgen:make-rep-loop sobre evaluar-programa.
(define interpretador
  (lambda ()
    ((sllgen:make-rep-loop "--> " evaluar-programa
                           (sllgen:make-stream-parser especificacion-lexica
                                                      especificacion-gramatical)))))

(provide (all-defined-out))
