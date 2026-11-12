#lang eopl
;Autores: Juan Felipe Aristizabal 2459364-3743, Juan Sebastian Huertas 2459505-3743

#|
  Taller 3 — Cauca con referencias y tipos.
  TAD referencia y almacén (Parte 1).

  El módulo no requiere ningún otro: el almacén guarda valores
  cualesquiera y no necesita la gramática.

  La referencia es un define-datatype y el almacén es una lista guardada
  en la variable global the-store. Es el único lugar del curso donde se
  usa set!.

  Invariante que las operaciones tienen que preservar, y que se demuestra
  en la Parte 5:
    1. toda referencia entregada por newref! apunta a una celda existente
    2. el almacén solo crece por newref!
    3. setref! cambia una celda y deja las demás intactas
    4. deref sobre una referencia fuera de rango levanta eopl:error
|#

;; referencia: tipo abstracto, no un entero desnudo.
(define-datatype referencia referencia?
  (a-ref (pos integer?)))

;; empty-store : -> almacen
;; El almacén sin celdas.
(define empty-store
  (lambda () '()))

;; the-store: el almacén global, una lista de valores indexada por posición.
(define the-store (empty-store))

;; initialize-store! : -> void
;; Deja el almacén vacío. Se llama al empezar cada programa.
(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))

;; get-store : -> almacen
;; Retorna el almacén actual, sin modificarlo.
(define get-store
  (lambda () the-store))

;; ref->pos : referencia -> int
;; Retorna la posición que nombra la referencia.
(define ref->pos
  (lambda (ref)
    (cases referencia ref
      (a-ref (pos) pos))))

;; posicion-valida? : int -> boolean
;; #t si la posición es una celda existente del almacén.
(define posicion-valida?
  (lambda (pos)
    (and (>= pos 0) (< pos (length the-store)))))

;; newref! : valor -> referencia
;; Agrega una celda con el valor y retorna la referencia que la nombra.
(define newref!
  (lambda (val)
    (let ((pos (length the-store)))
      (set! the-store (append the-store (list val)))
      (a-ref pos))))

;; deref : referencia -> valor
;; Lee la celda. Si la referencia está fuera de rango, levanta eopl:error.
(define deref
  (lambda (ref)
    (let ((pos (ref->pos ref)))
      (if (posicion-valida? pos)
          (list-ref the-store pos)
          (eopl:error 'deref "referencia fuera de rango: ~s" pos)))))

;; reemplazar : lista x int x valor -> lista
;; Copia de la lista con el elemento de la posición i cambiado por val.
(define reemplazar
  (lambda (lst i val)
    (if (zero? i)
        (cons val (cdr lst))
        (cons (car lst) (reemplazar (cdr lst) (- i 1) val)))))

;; setref! : referencia x valor -> void
;; Escribe el valor en la celda y deja las demás intactas.
(define setref!
  (lambda (ref val)
    (let ((pos (ref->pos ref)))
      (if (posicion-valida? pos)
          (set! the-store (reemplazar the-store pos val))
          (eopl:error 'setref! "referencia fuera de rango: ~s" pos)))))

(provide (all-defined-out))
