#lang eopl
;Autores: Juan Felipe Aristizabal 2459364-3743, Juan Sebastian Huertas 2459505-3743

#|
  Taller 3 — Cauca con referencias y tipos.
  TAD ambiente y valor procedimiento.

  Las dos definiciones van en el mismo módulo porque se nombran entre
  sí: el campo del ambiente dentro de una clausura pide ambiente?, y
  apply-env construye una clausura cuando resuelve un nombre ligado por
  letrec. Separarlas deja uno de los dos campos sin predicado.

  ambiente tiene las variantes ambiente-vacio, ambiente-extendido y
  ambiente-recursivo; procval tiene la clausura con los parámetros, el
  cuerpo y el ambiente donde se creó.

  El cuerpo de una clausura es una expresion?, que viene de sintaxis.rkt.
|#

(require "sintaxis.rkt")

(define-datatype ambiente ambiente?
  (ambiente-vacio)
  (ambiente-extendido
   (ids (list-of symbol?))
   (valores list?)
   (env ambiente?))
  (ambiente-recursivo
   (proc-names (list-of symbol?))
   (idss list?)
   (bodies (list-of expresion?))
   (env ambiente?)))

(define-datatype procval procval?
  (cerradura
   (ids (list-of symbol?))
   (body expresion?)
   (env ambiente?)))

;; posicion : symbol x lista de symbol x int -> int o #f
;; Da la posicion de id en ids, o #f si no esta.
(define posicion
  (lambda (id ids i)
    (cond ((null? ids) #f)
          ((eqv? id (car ids)) i)
          (else (posicion id (cdr ids) (+ i 1))))))

;; apply-env : ambiente x symbol -> valor
;; Busca la ligadura del identificador. Sobre el ambiente vacío levanta
;; eopl:error; sobre el recursivo construye la clausura del procedimiento.
(define apply-env
  (lambda (env id)
    (cases ambiente env
      (ambiente-vacio ()
        (eopl:error 'apply-env "la variable ~s no esta ligada" id))
      (ambiente-extendido (ids valores env-externo)
        (let ((pos (posicion id ids 0)))
          (if pos
              (list-ref valores pos)
              (apply-env env-externo id))))
      (ambiente-recursivo (proc-names idss bodies env-externo)
        (let ((pos (posicion id proc-names 0)))
          (if pos
              (cerradura (list-ref idss pos) (list-ref bodies pos) env)
              (apply-env env-externo id)))))))

;; ambiente-inicial : -> ambiente
;; El del enunciado: n = 10, m = 3, p = 7, q = 2, r = 5.
(define ambiente-inicial
  (lambda ()
    (ambiente-extendido '(n m p q r)
                        '(10 3 7 2 5)
                        (ambiente-vacio))))

(provide (all-defined-out))
