#lang eopl
;Autores: Juan Felipe Aristizabal 2459364-3743, Juan Sebastian Huertas 2459505-3743

#|
  Taller 3 — Cauca con referencias y tipos.
  El tipo y el ambiente de tipos (Parte 3).

  El datatype tipo lo genera la gramática, porque las anotaciones se
  escriben dentro del programa. Aquí van la comparación estructural de
  dos tipos, el texto con que un tipo aparece en los mensajes de error y
  el ambiente de tipos.

  Falta el datatype del ambiente de tipos, con las mismas tres variantes
  del ambiente de valores: tenv-vacio, tenv-extendido y tenv-recursivo.
  La recursiva guarda el tipo declarado de cada procedimiento, que es lo
  que permite chequear el cuerpo de un letrec sin evaluarlo.

  El módulo requiere sintaxis.rkt y ningún otro del intérprete.
|#

(require "sintaxis.rkt")

;; tipo->texto : tipo -> string
;; La forma en que los tipos aparecen en los mensajes de error:
;; "num", "bool", "refto(num)", "(num * num -> bool)".
(define tipo->texto
  (lambda (t)
    (cases tipo t
      (num-tipo () "num")
      (bool-tipo () "bool")
      (ref-tipo (t1)
        (string-append "refto(" (tipo->texto t1) ")"))
      (proc-tipo (args res)
        (if (null? args)
            (string-append "(-> " (tipo->texto res) ")")
            (string-append "(" (tipos->texto args) " -> " (tipo->texto res) ")"))))))

;; tipos->texto : lista de tipos -> string
;; Los tipos separados por " * ", como van en la lista de argumentos de
;; un procedimiento. La lista vacía da la cadena vacía.
(define tipos->texto
  (lambda (ts)
    (cond ((null? ts) "")
          ((null? (cdr ts)) (tipo->texto (car ts)))
          (else (string-append (tipo->texto (car ts)) " * " (tipos->texto (cdr ts)))))))

;; tipos-iguales? : tipo x tipo -> boolean
;; Compara dos tipos por estructura, no por identidad.
(define tipos-iguales?
  (lambda (t1 t2)
    (cases tipo t1
      (num-tipo ()
        (cases tipo t2
          (num-tipo () #t)
          (else #f)))
      (bool-tipo ()
        (cases tipo t2
          (bool-tipo () #t)
          (else #f)))
      (ref-tipo (u1)
        (cases tipo t2
          (ref-tipo (u2) (tipos-iguales? u1 u2))
          (else #f)))
      (proc-tipo (args1 res1)
        (cases tipo t2
          (proc-tipo (args2 res2)
            (and (listas-de-tipos-iguales? args1 args2)
                 (tipos-iguales? res1 res2)))
          (else #f))))))

;; listas-de-tipos-iguales? : lista de tipos x lista de tipos -> boolean
;; #t si tienen la misma longitud y los tipos coinciden uno a uno.
(define listas-de-tipos-iguales?
  (lambda (ts1 ts2)
    (cond ((null? ts1) (null? ts2))
          ((null? ts2) #f)
          (else (and (tipos-iguales? (car ts1) (car ts2))
                     (listas-de-tipos-iguales? (cdr ts1) (cdr ts2)))))))

(define-datatype tenv tenv?
  (tenv-vacio)
  (tenv-extendido
   (ids (list-of symbol?))
   (tipos (list-of tipo?))
   (amb tenv?))
  (tenv-recursivo
   (proc-names (list-of symbol?))
   (tipos-procs (list-of tipo?))
   (amb tenv?)))

;; indice-de : symbol x lista de symbol x int -> int o #f
;; Da la posición de id en ids, o #f si no está.
(define indice-de
  (lambda (id ids i)
    (cond ((null? ids) #f)
          ((eqv? id (car ids)) i)
          (else (indice-de id (cdr ids) (+ i 1))))))

;; apply-tenv : tenv x symbol -> tipo
;; Busca el tipo del identificador. Si no está declarado levanta
;; eopl:error con «Variable no declarada: <x>».
(define apply-tenv
  (lambda (amb id)
    (cases tenv amb
      (tenv-vacio ()
        (eopl:error 'apply-tenv "Variable no declarada: ~a" id))
      (tenv-extendido (ids tipos amb-externo)
        (let ((pos (indice-de id ids 0)))
          (if pos
              (list-ref tipos pos)
              (apply-tenv amb-externo id))))
      (tenv-recursivo (proc-names tipos-procs amb-externo)
        (let ((pos (indice-de id proc-names 0)))
          (if pos
              (list-ref tipos-procs pos)
              (apply-tenv amb-externo id)))))))

;; tenv-inicial : -> tenv
;; Declara como num las cinco variables del ambiente inicial.
(define tenv-inicial
  (lambda ()
    (tenv-extendido '(n m p q r)
                    (list (num-tipo) (num-tipo) (num-tipo) (num-tipo) (num-tipo))
                    (tenv-vacio))))

(define tipos-exigir-cantidad
  (lambda (tipos n quien)
    (if (= (length tipos) n)
        #t
        (eopl:error quien "La primitiva espera ~a argumento(s) y recibio ~a"
                    n (length tipos)))))

(define tipos-exigir-minimo
  (lambda (tipos n quien)
    (if (>= (length tipos) n)
        #t
        (eopl:error quien "La primitiva espera al menos ~a argumento(s) y recibio ~a"
                    n (length tipos)))))

(define tipos-exigir-todos
  (lambda (tipos esperado quien)
    (cond ((null? tipos) #t)
          ((tipos-iguales? (car tipos) esperado)
           (tipos-exigir-todos (cdr tipos) esperado quien))
          (else (eopl:error quien "La primitiva espera argumentos de tipo ~a y recibio ~a"
                            (tipo->texto esperado) (tipo->texto (car tipos)))))))

(define tipo-num-exacto
  (lambda (tipos n quien)
    (and (tipos-exigir-cantidad tipos n quien)
         (tipos-exigir-todos tipos (num-tipo) quien)
         (num-tipo))))

(define tipo-num-minimo
  (lambda (tipos n quien)
    (and (tipos-exigir-minimo tipos n quien)
         (tipos-exigir-todos tipos (num-tipo) quien)
         (num-tipo))))

(define tipo-relacional
  (lambda (tipos n quien)
    (and (tipos-exigir-cantidad tipos n quien)
         (tipos-exigir-todos tipos (num-tipo) quien)
         (bool-tipo))))

(define tipo-booleano
  (lambda (tipos n quien)
    (and (tipos-exigir-cantidad tipos n quien)
         (tipos-exigir-todos tipos (bool-tipo) quien)
         (bool-tipo))))

;; tipo-de-primitiva : primitiva x lista de tipos -> tipo
;; Lo que cada primitiva exige de sus argumentos y lo que retorna: las
;; aritméticas retornan num; las relacionales, las booleanas y entre
;; retornan bool.
(define tipo-de-primitiva
  (lambda (prim tipos)
    (cases primitiva prim
      (sum-prim () (tipo-num-minimo tipos 1 '+))
      (minus-prim () (tipo-num-minimo tipos 1 '-))
      (mult-prim () (tipo-num-minimo tipos 1 '*))
      (div-prim () (tipo-num-minimo tipos 1 '/))
      (add-prim () (tipo-num-exacto tipos 1 'add1))
      (sub-prim () (tipo-num-exacto tipos 1 'sub1))
      (abs-prim () (tipo-num-exacto tipos 1 'abs))
      (mcd-prim () (tipo-num-minimo tipos 2 'mcd))
      (mcm-prim () (tipo-num-minimo tipos 2 'mcm))
      (promedio-prim () (tipo-num-minimo tipos 1 'promedio))
      (mayor-prim () (tipo-relacional tipos 2 '>))
      (mayorigual-prim () (tipo-relacional tipos 2 '>=))
      (menor-prim () (tipo-relacional tipos 2 '<))
      (menorigual-prim () (tipo-relacional tipos 2 '<=))
      (igual-prim () (tipo-relacional tipos 2 '==))
      (entre-prim () (tipo-relacional tipos 3 'entre))
      (not-prim () (tipo-booleano tipos 1 'not))
      (and-prim () (tipo-booleano tipos 2 'and))
      (or-prim () (tipo-booleano tipos 2 'or))
      (xor-prim () (tipo-booleano tipos 2 'xor))
      (implica-prim () (tipo-booleano tipos 2 'implica)))))