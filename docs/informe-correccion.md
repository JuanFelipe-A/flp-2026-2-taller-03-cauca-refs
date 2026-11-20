# Informe de corrección — Taller 3: Memoria y disciplina

**Curso:** Fundamentos de Interpretación y Compilación de Lenguajes
de Programación — Universidad del Valle, Sede Tuluá.

**Integrantes del grupo:**

| Nombre | Código | Correo institucional |
|--------|--------|----------------------|
| Juan Felipe Aristizabal | 2459364-3743 | juan.felipe.aristizabal@correounivalle.edu.co |
| Juan Sebastian Huertas | 2459505-3743 | huertas.juan@correounivalle.edu.co |

---

## 1. Marco formal

### 1.1 Corrección de programas recursivos

Sea $f : A \to B$ una función y $A$ un conjunto definido
recursivamente. Sea $P_f$ un programa recursivo en Racket que
pretende calcular $f$. Decimos que $P_f$ es correcto con respecto a
su especificación si se cumple:

$$
\forall a \in A \,:\, P_f(a) = f(a)
$$

La estrategia de demostración es la **inducción estructural**
sobre $A$:

- **Caso base:** para cada valor básico $a_0 \in A$ se verifica
  $P_f(a_0) = f(a_0)$.
- **Caso inductivo:** asumiendo la **hipótesis de inducción**
  $P_f(a') = f(a')$ para las subestructuras $a'$ que forman $a$, se
  demuestra $P_f(a) = f(a)$.

### 1.2 Corrección de programas iterativos

Para un programa iterativo se formalizan:

- Un estado $s$ con componentes relevantes.
- Un estado inicial $s_0$.
- Un estado final reconocido por un predicado $\text{es-final?}(s)$.
- Una **invariante** $\text{Inv}(s)$ que se mantiene entre pasos.
- Una transformación $\text{transformar}(s)$.

La corrección se argumenta demostrando:

1. $\text{Inv}(s_0)$ se cumple al inicio.
2. $\text{Inv}(s) \,\land\, \lnot\text{es-final?}(s)\Rightarrow
   \text{Inv}(\text{transformar}(s))$.
3. $\text{Inv}(s) \,\land\, \text{es-final?}(s)\Rightarrow
   \text{respuesta}(s) = f(\text{entrada})$.
4. El proceso termina (argumentar una función de cota estrictamente
   decreciente sobre $\mathbb{N}$).

### 1.3 Modelo del almacén

En `src/almacen.rkt` el almacén es la lista `the-store`. La
modelamos como una secuencia finita $\sigma = [v_0, v_1, \ldots, v_{k-1}]$
con longitud $|\sigma| = k$, y escribimos $\sigma(\ell)$ para el
elemento de la posición $\ell$, definido solo cuando
$0 \le \ell < |\sigma|$.

Una referencia es `(a-ref ℓ)`; en el informe la identificamos con
su posición $\ell$. Como `referencia` es un `define-datatype` y Cauca
no tiene ninguna expresión que construya una `a-ref` a partir de un
número, **la única forma de obtener una referencia es `newref!`**.
Sea $R$ el conjunto de posiciones que `newref!` ha entregado desde el
último `initialize-store!`. Toda referencia que aparece en un
programa en ejecución pertenece a $R$.

Notación: $\sigma[\ell \mapsto v]$ es el almacén igual a $\sigma$
salvo en la posición $\ell$, que vale $v$.

---

## 2. Funciones analizadas

### 2.1 El almacén preserva su invariante (sección 5.1)

**Especificación.** Las cuatro condiciones del enunciado se dividen
en una propiedad del estado $(\sigma, R)$ y tres propiedades de las
operaciones:

$$
\text{Inv}(\sigma, R) \;\equiv\; \forall \ell \in R \,:\; 0 \le \ell < |\sigma|
\qquad \text{(condición 1)}
$$

- **Condición 2 (solo crece por `newref!`):** si una operación pasa
  de $\sigma$ a $\sigma'$ y $|\sigma'| \ne |\sigma|$, la operación es
  `newref!`, y en ese caso $|\sigma'| = |\sigma| + 1$.
- **Condición 3 (`setref!` toca una sola celda):** si
  $\sigma' = \text{setref!}(\sigma, \ell, v)$, entonces
  $\sigma'(\ell) = v$ y $\sigma'(\ell') = \sigma(\ell')$ para todo
  $\ell' \ne \ell$. Es decir, $\sigma' = \sigma[\ell \mapsto v]$.
- **Condición 4 (rango):** si $\ell < 0$ o $\ell \ge |\sigma|$,
  entonces $\text{deref}(\sigma, \ell)$ levanta `eopl:error`.

Lo que hay que demostrar: $\text{Inv}$ vale al inicio, cada
operación la preserva y cada operación cumple las condiciones 2 a 4.

**Código.**

```racket
;; newref! : valor -> referencia
(define newref!
  (lambda (val)
    (let ((pos (length the-store)))
      (set! the-store (append the-store (list val)))
      (a-ref pos))))

;; deref : referencia -> valor
(define deref
  (lambda (ref)
    (let ((pos (ref->pos ref)))
      (if (posicion-valida? pos)
          (list-ref the-store pos)
          (eopl:error 'deref "referencia fuera de rango: ~s" pos)))))

;; reemplazar : lista x int x valor -> lista
(define reemplazar
  (lambda (lst i val)
    (if (zero? i)
        (cons val (cdr lst))
        (cons (car lst) (reemplazar (cdr lst) (- i 1) val)))))

;; setref! : referencia x valor -> void
(define setref!
  (lambda (ref val)
    (let ((pos (ref->pos ref)))
      (if (posicion-valida? pos)
          (set! the-store (reemplazar the-store pos val))
          (eopl:error 'setref! "referencia fuera de rango: ~s" pos)))))
```

`posicion-valida?` es exactamente $0 \le \ell < |\sigma|$.

**Estrategia de demostración:** el almacén se trata como el estado de
un programa iterativo (sección 1.2). Cada operación es un paso, y se
demuestra que el paso preserva $\text{Inv}$. Para `setref!` se usa
además un lema por inducción sobre la posición.

**Demostración.**

- **Estado inicial.** `initialize-store!` deja
  $\sigma_0 = [\,]$ y $R_0 = \varnothing$. $\text{Inv}(\sigma_0, R_0)$
  se cumple trivialmente, porque no hay ningún $\ell \in R_0$.

- **`newref!(v)`.** Supongamos $\text{Inv}(\sigma, R)$. La función
  calcula $\ell = |\sigma|$ y deja $\sigma' = \sigma \mathbin{+\!\!+} [v]$.
  Entonces:
  - $|\sigma'| = |\sigma| + 1$, lo que cumple la condición 2.
  - Para $i < |\sigma|$, $\sigma'(i) = \sigma(i)$, porque `append`
    conserva el prefijo. Las celdas existentes no cambian.
  - $\sigma'(\ell) = v$, y la referencia entregada cumple
    $0 \le \ell = |\sigma| < |\sigma| + 1 = |\sigma'|$: es válida.
  - El nuevo conjunto es $R' = R \cup \{\ell\}$. Para
    $\ell' \in R$, por hipótesis $\ell' < |\sigma| < |\sigma'|$; para
    $\ell$ ya se vio. Luego $\text{Inv}(\sigma', R')$.

- **Lema (de `reemplazar`).** Para toda lista $l$ y todo
  $0 \le i < |l|$, si $l' = \text{reemplazar}(l, i, v)$ entonces
  $|l'| = |l|$, $l'(i) = v$ y $l'(j) = l(j)$ para todo $j \ne i$.

  Por inducción sobre $i$:
  - **Caso base** ($i = 0$): $l' = \text{cons}(v, \text{cdr}(l))$.
    Tiene la misma longitud, $l'(0) = v$, y para $j > 0$,
    $l'(j) = \text{cdr}(l)(j-1) = l(j)$.
  - **Caso inductivo** ($i > 0$): como $i < |l|$, la lista no es
    vacía y $i - 1 < |\text{cdr}(l)|$. Por hipótesis de inducción,
    $m = \text{reemplazar}(\text{cdr}(l), i-1, v)$ cumple el lema
    sobre $\text{cdr}(l)$. Entonces
    $l' = \text{cons}(\text{car}(l), m)$ y:

    $$
    |l'| = 1 + |m| = 1 + |\text{cdr}(l)| = |l|, \qquad
    l'(0) = \text{car}(l) = l(0),
    $$

    $$
    l'(j) = m(j-1) =
    \begin{cases}
      v & \text{si } j - 1 = i - 1 \text{, es decir } j = i \\
      \text{cdr}(l)(j-1) = l(j) & \text{si } j \ne i
    \end{cases}
    \quad (j > 0).
    $$

  - **Terminación:** $i$ baja en 1 en cada llamada y el caso
    $i = 0$ corta la recursión.

- **`setref!(ℓ, v)`.** Supongamos $\text{Inv}(\sigma, R)$.
  - Si $0 \le \ell < |\sigma|$, se deja
    $\sigma' = \text{reemplazar}(\sigma, \ell, v)$. Por el lema,
    $\sigma'(\ell) = v$ y $\sigma'(\ell') = \sigma(\ell')$ para todo
    $\ell' \ne \ell$. Esa es la condición 3:
    $\sigma' = \sigma[\ell \mapsto v]$. También por el lema,
    $|\sigma'| = |\sigma|$, así que la longitud no cambia (condición
    2), $R$ no cambia y $\text{Inv}(\sigma', R)$ se cumple.
  - Si $\ell$ está fuera de rango, se levanta `eopl:error` antes del
    `set!`: el almacén no cambia.

- **`deref(ℓ)`.** No contiene ningún `set!`, así que
  $\sigma' = \sigma$ y la invariante se conserva sin más. Si
  $0 \le \ell < |\sigma|$ retorna `(list-ref the-store ℓ)`, que es
  $\sigma(\ell)$. Si no, la rama `else` del `if` levanta
  `eopl:error`, que es la condición 4. Por la condición 1, esa rama
  nunca se toma con una referencia de $R$.

- **Condición 2, completa.** `set!` sobre `the-store` aparece solo en
  `initialize-store!`, `newref!` y `setref!`. `initialize-store!`
  solo se llama al empezar un programa, `setref!` conserva la
  longitud y `newref!` la aumenta en exactamente 1. Ninguna otra
  función del intérprete cambia el almacén.

**Conclusión:** $\text{Inv}(\sigma, R)$ vale al inicio de todo
programa y cada operación la preserva. Las condiciones 2, 3 y 4 se
cumplen en cada paso. Por inducción sobre el número de operaciones
ejecutadas, el invariante se cumple durante toda la ejecución.

---

### 2.2 Corrección de `swap-exp` (sección 5.2)

**Especificación.** Sea $\sigma$ el almacén **después** de evaluar
las dos subexpresiones, que pueden haber modificado el almacén (por
ejemplo con un `newref` adentro), y sean $\ell_1, \ell_2 \in R$ las
referencias que produjeron. Si $\sigma'$ es el almacén después del
intercambio y $r$ el valor retornado:

$$
\sigma'(\ell_1) = \sigma(\ell_2), \qquad
\sigma'(\ell_2) = \sigma(\ell_1), \qquad
\sigma'(\ell) = \sigma(\ell) \;\; \forall \ell \notin \{\ell_1, \ell_2\},
\qquad r = \sigma(\ell_2).
$$

Si alguna de las dos no es una referencia, se levanta `eopl:error`
sin escribir en el almacén.

**Código** (cláusula de `evaluar-expresion` en `src/interprete.rkt`):

```racket
(swap-exp (exp1 exp2)
  (let* ((ref1 (exigir-referencia (evaluar-expresion exp1 env) 'swap))
         (ref2 (exigir-referencia (evaluar-expresion exp2 env) 'swap))
         (val1 (deref ref1))
         (val2 (deref ref2)))
    (setref! ref1 val2)
    (setref! ref2 val1)
    val2))
```

**Estrategia de demostración:** se sigue el `let*` paso a paso y se
usa la condición 3 de la sección 2.1, $\text{setref!}(\sigma, \ell, v)
= \sigma[\ell \mapsto v]$, que ya está demostrada.

**Demostración.**

1. **Errores.** `exigir-referencia` revisa los dos valores antes de
   cualquier `deref` o `setref!`. Si alguno no es referencia levanta
   `eopl:error` y la cláusula no escribe nada. Si los dos lo son, el
   error no ocurre. Así que el error se da en ese caso y solo en ese.

2. **Lecturas.** `deref` no modifica el almacén (sección 2.1), luego
   después de las dos lecturas el almacén sigue siendo $\sigma$ y

   $$
   \text{val1} = \sigma(\ell_1), \qquad \text{val2} = \sigma(\ell_2).
   $$

   Las dos referencias están en $R$, así que por la condición 1 las
   lecturas no levantan error.

3. **Primera escritura.** $\sigma_1 = \text{setref!}(\sigma, \ell_1,
   \text{val2}) = \sigma[\ell_1 \mapsto \sigma(\ell_2)]$.

4. **Segunda escritura.** $\sigma' = \text{setref!}(\sigma_1, \ell_2,
   \text{val1}) = \sigma_1[\ell_2 \mapsto \sigma(\ell_1)]$.

5. **Caso $\ell_1 \ne \ell_2$.**
   - $\sigma'(\ell_2) = \sigma(\ell_1)$, por el paso 4.
   - $\sigma'(\ell_1) = \sigma_1(\ell_1) = \sigma(\ell_2)$: el paso 4
     no toca $\ell_1$ porque $\ell_1 \ne \ell_2$, y el paso 3 la dejó
     en $\sigma(\ell_2)$.
   - Para $\ell \notin \{\ell_1, \ell_2\}$:
     $\sigma'(\ell) = \sigma_1(\ell) = \sigma(\ell)$, porque ninguna de
     las dos escrituras toca $\ell$.

   **El valor original de la primera celda no se pierde.** El paso 3
   sobrescribe $\ell_1$, pero su valor anterior $\sigma(\ell_1)$ ya
   estaba guardado en `val1`, una variable del `let*` que vive fuera
   del almacén. El paso 4 escribe `val1`, no
   $\text{deref}(\sigma_1, \ell_1)$. Si la implementación leyera la
   primera celda después de escribirla,

   $$
   \text{setref!}(\ell_1, \sigma(\ell_2));\;
   \text{setref!}(\ell_2, \text{deref}(\ell_1))
   $$

   las dos celdas terminarían con $\sigma(\ell_2)$ y el valor
   $\sigma(\ell_1)$ se perdería. Leer las dos celdas antes de la
   primera escritura es lo que lo evita.

6. **Caso $\ell_1 = \ell_2 = \ell$ (una referencia consigo misma).**
   La especificación pide $\sigma'(\ell) = \sigma(\ell)$, porque las
   dos ecuaciones dicen lo mismo, y que las demás celdas no cambien.
   Es decir, exige $\sigma' = \sigma$ y $r = \sigma(\ell)$.

   En la implementación, $\text{val1} = \text{val2} = \sigma(\ell)$.
   El paso 3 escribe $\sigma(\ell)$ en $\ell$, que ya tenía ese valor,
   así que $\sigma_1 = \sigma$. El paso 4 hace lo mismo y
   $\sigma' = \sigma$. Se cumple la especificación. La prueba
   «swap de una celda consigo misma no cambia nada» de
   `pruebas-cauca-refs.rkt` lo comprueba: `swap(a, a)` deja
   `deref(a)` en 8.

7. **Valor retornado.** La última expresión del `let*` es `val2`, y
   por el paso 2, $\text{val2} = \sigma(\ell_2)$: el contenido de la
   segunda celda antes del intercambio, que coincide con
   $\sigma'(\ell_1)$, lo que quedó en la primera. En el ejemplo guía,
   `swap(a, b)` con $\sigma = [0 \mapsto 7, 1 \mapsto 2]$ retorna 2.

8. **Terminación.** No hay recursión en la cláusula, fuera de las dos
   llamadas a `evaluar-expresion` sobre subárboles de `swap-exp`, y
   `reemplazar` termina (sección 2.1).

**Conclusión:** la cláusula `swap-exp` cumple su especificación,
también cuando $\ell_1 = \ell_2$, y retorna el contenido anterior de
la segunda celda.

---

### 2.3 Solidez del chequeador (sección 5.3)

**Especificación.** El chequeador dice que una expresión tiene tipo
$t$ sin evaluarla. La solidez es la promesa de que, si lo dice, la
evaluación no se va a quejar de un tipo. Hay que fijar tres cosas
antes de enunciarla.

*Concordancia entre ambiente y ambiente de tipos.* Sean $\rho$ un
ambiente de valores y $\Gamma$ un ambiente de tipos. Decimos
$\rho \models \Gamma$ si y solo si $\text{dom}(\rho)=\text{dom}(\Gamma)$
y para todo $x$, $\rho(x)$ es un valor de tipo $\Gamma(x)$. Para un
procedimiento, «valor de tipo $(t_1 \ast\cdots\ast t_n \to t)$» significa
una clausura que, aplicada a valores de tipo $t_i$, da un valor de tipo
$t$; en concreto, una clausura $\langle x_1,\ldots,x_n;\, b;\, \rho_c\rangle$
con $\rho_c \models \Gamma_c$ y
$\Gamma_c[x_i \mapsto t_i] \vdash b : t$ para algún $\Gamma_c$.

*Tipado del almacén.* Un valor de tipo $\text{refto}(t)$ es solo una
posición $\ell$. Que $\ell$ «sea de tipo $\text{refto}(t)$» depende de lo
que hay en el almacén, y el almacén cambia durante la ejecución. Por eso
se introduce un tipado del almacén $\Sigma$, una función de posiciones a
tipos, con

$$
v : t \;[\Sigma] \;\text{ para }\; v=\ell \text{ si y solo si } t = \text{refto}(t') \text{ y } \Sigma(\ell)=t',
$$

y para números, booleanos y clausuras como arriba, usando $\Sigma$ en el
tipado de los valores que la clausura guarda en $\rho_c$. Un almacén
$\sigma$ concuerda con $\Sigma$, escrito $\sigma \models \Sigma$, si
$\text{dom}(\sigma)=\text{dom}(\Sigma)$ y para todo $\ell$,
$\sigma(\ell) : \Sigma(\ell)\;[\Sigma]$. Decimos que $\Sigma'$ *extiende*
a $\Sigma$ si $\text{dom}(\Sigma)\subseteq\text{dom}(\Sigma')$ y
$\Sigma'(\ell)=\Sigma(\ell)$ para todo $\ell\in\text{dom}(\Sigma)$.

*Enunciado.* Si $\Gamma \vdash e : t$, $\rho \models_\Sigma \Gamma$ y
$\sigma \models \Sigma$, entonces `evaluar-expresion`$(e, \rho)$ con
almacén $\sigma$ cumple una de estas tres cosas:

1. no termina;
2. levanta un error aritmético, que es de valores y no de tipos: división
   por cero, o `mcd` o `mcm` con un número que no es entero (el tipo
   $\text{num}$ no distingue enteros de decimales);
3. retorna un valor $v$ y deja un almacén $\sigma'$ tales que existe un
   $\Sigma'$ que extiende a $\Sigma$ con $\sigma' \models \Sigma'$ y
   $v : t\;[\Sigma']$.

En particular, nunca se levanta ninguno de los otros errores del
evaluador: condición del `if` no booleana, aplicación de algo que no es
un procedimiento, aridad incorrecta, argumento primitivo del tipo
equivocado, `deref`, `setref`, `swap` o `applyref` sobre algo que no es
una referencia, control del `case` que no es número, variable sin ligar
o referencia fuera de rango.

**Código** (las dos reglas que usa la demostración, en
`src/chequeador.rkt`):

```racket
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

(setref-exp (ref-e val-e)
  (let* ((tipo-celda (contenido-de-ref (type-of ref-e amb) 'setref))
         (tipo-valor (type-of val-e amb)))
    (if (tipos-iguales? tipo-celda tipo-valor)
        (num-tipo)
        (eopl:error 'setref "La celda guarda ~a y se intento escribir ~a"
                    (tipo->texto tipo-celda) (tipo->texto tipo-valor)))))
```

**Estrategia de demostración:** inducción sobre la derivación de
$\Gamma \vdash e : t$, con una regla por variante de `expresion`. Se
usa el lema siguiente.

*Lema (debilitamiento).* Si $v : t\;[\Sigma]$ y $\Sigma'$ extiende a
$\Sigma$, entonces $v : t\;[\Sigma']$; y si $\rho \models_\Sigma \Gamma$,
entonces $\rho \models_{\Sigma'} \Gamma$. *Prueba:* por casos sobre $v$.
Para un número o un booleano no interviene $\Sigma$. Para una posición
$\ell$, $\Sigma'(\ell)=\Sigma(\ell)$ porque $\Sigma'$ extiende a $\Sigma$.
Para una clausura, se aplica lo mismo al ambiente $\rho_c$ que guarda.
$\square$

**Demostración.** Cada caso usa la hipótesis de inducción (HI) sobre
las subderivaciones y el lema para llevar lo ya calculado al almacén más
grande.

- **Caso `lit-exp`, `true-exp` y `false-exp`.** La regla da $\text{num}$
  o $\text{bool}$ y el evaluador retorna un número o un booleano. No
  toca el almacén, así que $\Sigma'=\Sigma$.

- **Caso `var-exp`.** La regla da $\Gamma(x)$. Como
  $\rho\models\Gamma$, $x$ está ligada y $\rho(x)$ es un valor de tipo
  $\Gamma(x)$. Si $x$ es un procedimiento de un `letrec`,
  `apply-env` arma la clausura sobre el ambiente recursivo completo;
  su tipo es el declarado por la regla de `letrec` (ver ese caso).

- **Caso `prim-exp`.** Por HI, cada argumento da un valor de su tipo, y
  `tipo-de-primitiva` exige exactamente lo que exige `evaluar-primitiva`:
  la misma aridad y el mismo tipo de argumentos. Los chequeos de
  `primitivas.rkt` (`exigir-numeros`, `exigir-booleanos`,
  `exigir-cantidad`, `exigir-minimo`) no se cumplen solo si el tipo está
  mal, así que no fallan. Quedan solo `dividir` con divisor cero y
  `exigir-enteros` en `mcd` y `mcm`, que son los errores de la alternativa
  2 del enunciado. El resultado es de tipo $\text{num}$ o $\text{bool}$,
  según la tabla de `tipo-de-primitiva`.

- **Caso `if-exp`.** Por HI sobre la condición, el valor es de tipo
  $\text{bool}$, así que `boolean?` se cumple y el `eopl:error` de
  «condición no booleana» nunca ocurre. Se evalúa solo una de las dos
  ramas. Cualquiera de las dos da un valor de tipo $t$, porque la regla
  exige que las dos ramas tengan el mismo tipo $t$ (si no, el chequeador
  levanta «Las ramas del if deben coincidir»), y por HI el valor de la
  rama elegida es de tipo $t$ con un $\Sigma'$ que extiende a $\Sigma$.

- **Caso `let-exp`.** Por HI, cada expresión de la lista se evalúa en
  $\rho$ (el ambiente de afuera, igual que en la regla) y da un valor
  $v_i : t_i$; los almacenes sucesivos concuerdan con extensiones
  sucesivas de $\Sigma$ y el lema lleva los $v_i$ a la última. Entonces
  $\rho[x_i\mapsto v_i] \models \Gamma[x_i\mapsto t_i]$ y la HI sobre el
  cuerpo da el resultado de tipo $t$.

- **Caso `proc-exp`.** El evaluador crea la clausura
  $\langle x_i;\, b;\, \rho\rangle$ sin evaluar el cuerpo. La regla da
  $(t_1\ast\cdots\ast t_n\to t)$ con $\Gamma[x_i\mapsto t_i]\vdash b:t$
  y $\rho\models\Gamma$: es exactamente la definición de «valor de tipo
  $(t_1\ast\cdots\ast t_n\to t)$».

- **Caso `app-exp`.**
  - Por HI, el operador es una clausura de tipo
    $(t_1\ast\cdots\ast t_n\to t)$, de modo que `procval?` se cumple, y
    cada argumento es un valor de tipo $t_i$. La regla además garantiza
    la aridad ($n$ parámetros y $n$ argumentos), de modo que el error de
    `apply-procedure` nunca ocurre.
  - `copia-por-valor` no cambia los tipos: para un número, un booleano o
    una clausura es el mismo valor, y para una posición $\ell$ crea una
    celda nueva $\ell'$ con el mismo contenido, así que
    $\Sigma'=\Sigma[\ell'\mapsto\Sigma(\ell)]$ extiende a $\Sigma$ y
    $\ell' : \text{refto}(\Sigma(\ell))\;[\Sigma']$.
  - El cuerpo se evalúa en $\rho'=\rho_c[x_i\mapsto v_i]$, que concuerda
    con $\Gamma_c[x_i\mapsto t_i]$.
  - Por HI sobre la derivación del cuerpo, el resultado es de tipo $t$.

- **Caso `letrec-exp`.** Sea $\Gamma'$ el ambiente recursivo que arma la
  regla, con el tipo $(t_1\ast\cdots\to r)$ declarado de cada
  procedimiento, y sea $\rho'$ el `ambiente-recursivo` que arma el
  evaluador sobre $\rho$. La regla verifica cada cuerpo en $\Gamma'$ extendido
  con sus parámetros y compara con el resultado declarado, de modo que
  la clausura que `apply-env` entrega para cada nombre es de su tipo
  declarado. Así $\rho'\models\Gamma'$ y la HI sobre el cuerpo del
  `letrec` da el resultado. No hay un círculo en el argumento: el tipo de
  cada procedimiento viene escrito en el programa y la regla lo usa como
  hipótesis para chequear los cuerpos, no lo calcula a partir de ellos.

- **Caso `case-exp`.** Por HI, el control es de tipo $\text{num}$, así
  que `number?` se cumple. Se evalúa una sola rama, y todas, también la
  de `otherwise`, tienen el mismo tipo $t$.

  - **Casos con referencias.**
  - **`newref-exp`.** Por HI, $v:t\;[\Sigma_1]$. `newref!` agrega una
    celda en $\ell=|\sigma|$, así que $\ell\notin\text{dom}(\Sigma_1)$.
    Con $\Sigma'=\Sigma_1[\ell\mapsto t]$, $\sigma'\models\Sigma'$ y
    $\ell:\text{refto}(t)\;[\Sigma']$.
  - **`deref-exp`.** Por HI, el valor es una posición $\ell$ con
    $\Sigma(\ell)=t$. Como $\text{dom}(\sigma)=\text{dom}(\Sigma)$,
    $\ell$ está en rango y el error de `deref` por rango nunca ocurre.
    Por $\sigma\models\Sigma$, $\sigma(\ell):t$.
  - **`setref-exp`.** Por HI, $\ell:\text{refto}(t)$ y el valor $v:t'$,
    y la regla exige $t=t'$ («La celda guarda $t$ y se intento escribir
    $t'$» si no). Entonces $\sigma'=\sigma[\ell\mapsto v]$ cumple
    $\sigma'\models\Sigma$: la celda $\ell$ tiene ahora un valor de
    tipo $\Sigma(\ell)$ y las demás no cambian. El valor retornado es
    $1$, de tipo $\text{num}$, que es lo que da la regla.
  - **`swap-exp`.** Por HI, $\ell_1:\text{refto}(t)$ y
    $\ell_2:\text{refto}(t)$ con el mismo $t$, porque la regla lo exige.
    Ambos contenidos son de tipo $t$, así que escribir cada uno en la
    celda del otro conserva $\sigma'\models\Sigma$, también cuando
    $\ell_1=\ell_2$ (el almacén no cambia). El valor retornado es
    $\sigma(\ell_2):t$.
  - **`begin-exp`.** Por HI sobre cada expresión en orden, con el lema
    para pasar de un almacén al siguiente; el resultado es el de la
    última, de tipo $t$.
  - **`app-ref-exp`.** La regla busca el tipo de cada identificador con
    `apply-tenv` y exige que sea $\text{refto}(t_i)$; por
    $\rho\models\Gamma$, $\rho(x_i)=\ell_i$ con $\Sigma(\ell_i)=t_i$, de
    modo que `buscar-referencias` no falla. El operador es una
    clausura de tipo $(\text{refto}(t_1)\ast\cdots\to t)$ y no se copia
    nada: el cuerpo se evalúa en
    
---

## 3. Propiedades adicionales

### 3.1 Paso por referencia frente a paso por valor (Parte 2)

**Propiedad.** Sea `f` una clausura con parámetros
$u_1, \ldots, u_n$ y sean $x_1, \ldots, x_n$ identificadores con
$\rho(x_i) = \ell_i \in R$.

- Con `applyref f (x1, ..., xn)`, el cuerpo se evalúa en un ambiente
  con $u_i \mapsto \ell_i$: la **misma** referencia. Toda escritura
  $\text{setref!}(\ell_i, v)$ que haga el cuerpo a través de $u_i$
  se observa después con `deref(x_i)`.
- Con `apply f (x1, ..., xn)`, `copia-por-valor` hace
  $\ell'_i = \text{newref!}(\sigma(\ell_i))$, y el cuerpo se evalúa
  con $u_i \mapsto \ell'_i$. Como `newref!` entrega una posición
  $\ell'_i = |\sigma| \notin R$, se tiene $\ell'_i \ne \ell_j$ para
  todo $j$. Por la condición 3 de la sección 2.1, las escrituras del
  cuerpo sobre $\ell'_i$ dejan intactas las celdas $\ell_j$, así que
  `deref(x_i)` da lo mismo que antes de la llamada (si el cuerpo solo
  escribe a través de sus parámetros).

La ligadura con `let` no copia: `let otro = celda` liga `otro` a la
misma referencia. Por eso el tercer ejemplo de la Parte 1 da 99.

**El programa que separa los dos mecanismos.**

```text
let x = newref(11)
    y = newref(4)
in
  let intercambiar = proc (u : refto(num), v : refto(num))
                       swap(u, v)
                     end
  in
    begin
      applyref intercambiar (x, y);     // o: apply intercambiar (x, y);
      -(deref(x), deref(y))
    end
  end
end
```

Antes de la llamada, $\rho(x) = 0$, $\rho(y) = 1$ y
$\sigma = [0 \mapsto 11,\ 1 \mapsto 4]$.

| | `applyref intercambiar (x, y)` | `apply intercambiar (x, y)` |
|---|---|---|
| Ligaduras del cuerpo | $u \mapsto 0,\ v \mapsto 1$ | $u \mapsto 2,\ v \mapsto 3$ (celdas nuevas) |
| Almacén al entrar | $[0 \mapsto 11,\ 1 \mapsto 4]$ | $[0 \mapsto 11,\ 1 \mapsto 4,\ 2 \mapsto 11,\ 3 \mapsto 4]$ |
| Almacén al salir | $[0 \mapsto 4,\ 1 \mapsto 11]$ | $[0 \mapsto 11,\ 1 \mapsto 4,\ 2 \mapsto 4,\ 3 \mapsto 11]$ |
| `deref(x)`, `deref(y)` | 4, 11 | 11, 4 |
| Resultado | $4 - 11 = -7$ | $11 - 4 = 7$ |

```mermaid
graph LR
  subgraph conApplyref ["applyref: se comparten las celdas"]
    x1[x] --> c0["0: 11 → 4"]
    y1[y] --> c1["1: 4 → 11"]
    u1[u] --> c0
    v1[v] --> c1
  end
  subgraph conApply ["apply: el procedimiento recibe copias"]
    x2[x] --> d0["0: 11"]
    y2[y] --> d1["1: 4"]
    u2[u] --> d2["2: 11 → 4"]
    v2[v] --> d3["3: 4 → 11"]
  end
```

**Por qué con `apply` da 7.** `apply` pasa por valor, y copiar una
referencia es reservar una celda nueva con el mismo contenido. `u` y
`v` quedan ligados a las celdas 2 y 3, el `swap` intercambia esas
copias, y las celdas 0 y 1, que son las de `x` y `y`, nunca se
escriben. El resultado es $11 - 4 = 7$. Con `applyref`, `u` y `v`
son las celdas 0 y 1 mismas, el intercambio se ve desde afuera y el
resultado es $4 - 11 = -7$. Las pruebas «applyref deja que el
procedimiento escriba en la celda del que llama» y «el mismo programa
con apply no toca las celdas del que llama» comprueban los dos
valores.

Sin `copia-por-valor` los dos mecanismos serían indistinguibles: la
referencia ya es un valor de primera clase, y pasarla por valor
compartiría la celda igual que `applyref`. También se ve en otro
programa de nuestras pruebas: `f (x, x)` escribe 100 en `u` y lee `v`.
Con `applyref`, `u` y `v` son la misma celda y da 100; con `apply`
son dos copias distintas y da 5.

---

## 4. Referencias

- Friedman, D. P., & Wand, M. *Essentials of Programming Languages*,
  3.ª ed., MIT Press, 2008. Sección 4.2 (EXPLICIT-REFS, Figura 4.3),
  sección 4.3 (paso por referencia) y capítulo 7 (chequeo de tipos).
- Pierce, B. C. *Types and Programming Languages*, MIT Press, 2002.
  Capítulos 8 y 13.
