#lang eopl
;Autores: Juan Felipe Aristizabal 2459364-3743, Juan Sebastian Huertas 2459505-3743

#|
  Taller 3 — Cauca con referencias y tipos.
  Reglas de tipado y chequeo del programa (Parte 3).

  type-of recorre el árbol con cases sobre un ambiente de tipos y no
  evalúa nada: una regla por variante de expresión, tal como están
  escritas en el cuadro del enunciado.

  Los mensajes de error se distinguen uno de otro. Son los nueve del
  cuadro «Mensajes de error», con ese texto. Los casos que el cuadro no
  nombra (case, swap, setref y applyref sobre algo que no es una celda)
  llevan un mensaje propio.

  El módulo requiere sintaxis.rkt y tipos.rkt, y ningún otro módulo del
  intérprete: el árbol que recorre es el que produjo el parser, con las
  anotaciones de tipo adentro.
|#

(require "sintaxis.rkt")
(require "tipos.rkt")

;; tipos-de-rands : lista de expresiones x tenv -> lista de tipos
;; El tipo de cada expresión, de izquierda a derecha, en el mismo ambiente.
(define tipos-de-rands
  (lambda (rands amb)
    (if (null? rands)
        '()
        (let ((primero (type-of (car rands) amb)))
          (cons primero (tipos-de-rands (cdr rands) amb))))))

;; verificar-argumentos : lista de tipos x lista de tipos x int -> boolean
;; Compara cada argumento con su parámetro. El i empieza en 1 y es el
;; que aparece en el mensaje. Retorna #t o levanta eopl:error.
(define verificar-argumentos
  (lambda (esperados encontrados i)
    (cond ((null? esperados) #t)
          ((tipos-iguales? (car esperados) (car encontrados))
           (verificar-argumentos (cdr esperados) (cdr encontrados) (+ i 1)))
          (else (eopl:error 'apply "El argumento ~a debe ser ~a, se encontro ~a"
                            i
                            (tipo->texto (car esperados))
                            (tipo->texto (car encontrados)))))))

;; type-of-application : tipo x lista de tipos -> tipo
;; Regla de apply y de applyref: el operador debe ser un procedimiento,
;; la aridad debe coincidir y cada argumento debe tener el tipo de su
;; parámetro, en ese orden. Retorna el tipo del resultado.
(define type-of-application
  (lambda (tipo-rator tipos-rands)
    (cases tipo tipo-rator
      (proc-tipo (args res)
                 (if (= (length args) (length tipos-rands))
                     (and (verificar-argumentos args tipos-rands 1)
                          res)
                     (eopl:error 'apply "El procedimiento espera ~a argumentos y recibio ~a"
                                 (length args) (length tipos-rands))))
      (else
       (eopl:error 'apply "Se intento aplicar un valor de tipo ~a"
                   (tipo->texto tipo-rator))))))

;; tipos-de-procs : lista de listas de tipos x lista de tipos -> lista de tipos
;; El tipo (t1 * ... -> r) de cada procedimiento de un letrec, a partir
;; de los tipos de sus parámetros y del tipo de su resultado.
(define tipos-de-procs
  (lambda (tipos-args tipos-res)
    (if (null? tipos-args)
        '()
        (cons (proc-tipo (car tipos-args) (car tipos-res))
              (tipos-de-procs (cdr tipos-args) (cdr tipos-res))))))

;; verificar-cuerpos : lista de symbol x lista de listas de symbol x
;;   lista de listas de tipos x lista de tipos x lista de expresiones x tenv
;;   -> boolean
;; Chequea cada cuerpo del letrec en el ambiente recursivo extendido con
;; sus parámetros, y compara su tipo con el resultado declarado.
(define verificar-cuerpos
  (lambda (proc-names idss tipos-args tipos-res bodies amb-rec)
    (if (null? proc-names)
        #t
        (let ((tipo-cuerpo (type-of (car bodies)
                                    (tenv-extendido (car idss) (car tipos-args) amb-rec))))
          (if (tipos-iguales? (car tipos-res) tipo-cuerpo)
              (verificar-cuerpos (cdr proc-names) (cdr idss) (cdr tipos-args)
                                 (cdr tipos-res) (cdr bodies) amb-rec)
              (eopl:error 'letrec "El procedimiento ~a declara ~a y su cuerpo da ~a"
                          (car proc-names)
                          (tipo->texto (car tipos-res))
                          (tipo->texto tipo-cuerpo)))))))

;; verificar-ramas-case : tipo x lista de expresiones x tenv -> boolean
;; Cada rama del case debe tener el tipo de la rama otherwise.
(define verificar-ramas-case
  (lambda (tipo-default acciones amb)
    (if (null? acciones)
        #t
        (let ((tipo-rama (type-of (car acciones) amb)))
          (if (tipos-iguales? tipo-default tipo-rama)
              (verificar-ramas-case tipo-default (cdr acciones) amb)
              (eopl:error 'case "Las ramas del case deben coincidir: ~a vs ~a"
                          (tipo->texto tipo-default) (tipo->texto tipo-rama)))))))

;; contenido-de-ref : tipo x symbol -> tipo
;; El tipo t de un refto(t). Si no es una referencia, levanta eopl:error
;; a nombre de quien lo pidió (deref, setref o swap).
(define contenido-de-ref
  (lambda (t quien)
    (cases tipo t
      (ref-tipo (contenido) contenido)
      (else
       (eopl:error quien "~a espera refto(t), se encontro ~a" quien (tipo->texto t))))))

;; type-of-begin : expresion x lista de expresiones x tenv -> tipo
;; Chequea todas las expresiones en orden y retorna el tipo de la última.
(define type-of-begin
  (lambda (exp exps amb)
    (let ((tipo-exp (type-of exp amb)))
      (if (null? exps)
          tipo-exp
          (type-of-begin (car exps) (cdr exps) amb)))))

;; tipos-de-referencias : lista de symbol x tenv -> lista de tipos
;; El tipo de cada identificador de un applyref, que debe ser refto(t).
;; Si alguno no lo es, levanta eopl:error.
(define tipos-de-referencias
  (lambda (ids amb)
    (if (null? ids)
        '()
        (let ((tipo-id (apply-tenv amb (car ids))))
          (cases tipo tipo-id
            (ref-tipo (contenido)
                      (cons tipo-id (tipos-de-referencias (cdr ids) amb)))
            (else
             (eopl:error 'applyref "applyref exige variables de tipo refto(t): ~a es ~a"
                         (car ids) (tipo->texto tipo-id))))))))

;; type-of : expresion x tenv -> tipo
;; El tipo de la expresión bajo el ambiente de tipos, o eopl:error con
;; el mensaje que explique el conflicto.
(define type-of
  (lambda (exp amb)
    (cases expresion exp
      (lit-exp (dato) (num-tipo))
      (var-exp (id) (apply-tenv amb id))
      (true-exp () (bool-tipo))
      (false-exp () (bool-tipo))
      (prim-exp (prim rands)
                (tipo-de-primitiva prim (tipos-de-rands rands amb)))
      (if-exp (test true-exp false-exp)
              (let ((tipo-test (type-of test amb)))
                (if (tipos-iguales? tipo-test (bool-tipo))
                    (let ((tipo-then (type-of true-exp amb))
                          (tipo-else (type-of false-exp amb)))
                      (if (tipos-iguales? tipo-then tipo-else)
                          tipo-then
                          (eopl:error 'if-exp "Las ramas del if deben coincidir: ~a vs ~a"
                                      (tipo->texto tipo-then) (tipo->texto tipo-else))))
                    (eopl:error 'if-exp "La condicion del if debe ser bool, se encontro ~a"
                                (tipo->texto tipo-test)))))
      (let-exp (ids rands body)
               (type-of body (tenv-extendido ids (tipos-de-rands rands amb) amb)))
      (proc-exp (ids tipos body)
                (proc-tipo tipos (type-of body (tenv-extendido ids tipos amb))))
      (app-exp (rator rands)
               (let ((tipo-rator (type-of rator amb)))
                 (type-of-application tipo-rator (tipos-de-rands rands amb))))
      (letrec-exp (tipos-res proc-names idss tipos-args bodies letrec-body)
                  (let ((amb-rec (tenv-recursivo proc-names
                                                 (tipos-de-procs tipos-args tipos-res)
                                                 amb)))
                    (and (verificar-cuerpos proc-names idss tipos-args tipos-res bodies amb-rec)
                         (type-of letrec-body amb-rec))))
      (case-exp (control valores acciones default)
                (let ((tipo-control (type-of control amb)))
                  (if (tipos-iguales? tipo-control (num-tipo))
                      (let ((tipo-default (type-of default amb)))
                        (and (verificar-ramas-case tipo-default acciones amb)
                             tipo-default))
                      (eopl:error 'case "El control del case debe ser num, se encontro ~a"
                                  (tipo->texto tipo-control)))))
      (newref-exp (e)
                  (ref-tipo (type-of e amb)))
      (deref-exp (e)
                 (contenido-de-ref (type-of e amb) 'deref))
      (setref-exp (ref-e val-e)
                  (let* ((tipo-celda (contenido-de-ref (type-of ref-e amb) 'setref))
                         (tipo-valor (type-of val-e amb)))
                    (if (tipos-iguales? tipo-celda tipo-valor)
                        (num-tipo)
                        (eopl:error 'setref "La celda guarda ~a y se intento escribir ~a"
                                    (tipo->texto tipo-celda) (tipo->texto tipo-valor)))))
      (swap-exp (e1 e2)
                (let* ((tipo1 (contenido-de-ref (type-of e1 amb) 'swap))
                       (tipo2 (contenido-de-ref (type-of e2 amb) 'swap)))
                  (if (tipos-iguales? tipo1 tipo2)
                      tipo1
                      (eopl:error 'swap "swap exige celdas del mismo tipo: refto(~a) vs refto(~a)"
                                  (tipo->texto tipo1) (tipo->texto tipo2)))))
      (begin-exp (e es)
                 (type-of-begin e es amb))
      (app-ref-exp (rator ids)
                   (let* ((tipo-rator (type-of rator amb))
                          (tipos-celdas (tipos-de-referencias ids amb)))
                     (type-of-application tipo-rator tipos-celdas))))))

;; type-of-program : programa -> tipo
;; Chequea el programa en el ambiente de tipos inicial.
(define type-of-program
  (lambda (pgm)
    (cases programa pgm
      (a-program (exp)
                 (type-of exp (tenv-inicial))))))

;; tipo-de-texto : string -> string
;; Analiza el texto, lo chequea y describe el tipo resultante.
(define tipo-de-texto
  (lambda (texto)
    (tipo->texto (type-of-program (parser texto)))))

(provide (all-defined-out))
