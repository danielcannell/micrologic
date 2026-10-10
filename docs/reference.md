# micrologic language reference

micrologic is a proof assistant for intuitionistic propositional logic, based on
the Curry–Howard correspondence: propositions are types, proofs are terms, and
checking a proof means type-checking its term.

A source file goes through four stages:

```
source ──parse──▶ surface AST ──lower──▶ kernel types/terms ──check──▶ ok / admitted / error
                                   │                              ▲
                                   └── tactic script ──elaborate──┘
```

1. **Parsing** reads the [surface language](#1-surface-language).
2. **Lowering** resolves proposition names and [desugars](#5-desugaring) the
   surface language into the smaller [kernel language](#3-kernel-language).
3. **Elaboration** turns a [tactic script](#2-tactics) into a kernel term,
   following the [elaboration rules](#6-elaboration).
4. **Checking** type-checks the kernel term against the theorem's statement,
   using the [kernel typing rules](#4-kernel-typing-rules).

Only the kernel is trusted. Lowering and elaboration can reject a program, but a
mistake in either can't make a false theorem check, because every proof ends up
as a kernel term that the kernel checks.

---

## 1. Surface language

### 1.1 Lexical structure

- **Whitespace** separates tokens and is otherwise ignored.
- **Comments** start with `--` and run to the end of the line.
- **Identifiers** are one or more letters, digits, `_` or `'` (letters and digits
  in the Unicode sense), e.g. `A`, `knave_alice`, `h'`, `_`. An identifier may
  start with a digit.
- **Keywords** can't be used as identifiers:

  ```
  axiom theorem proposition
  and or not True False
  fun case of inl inr fst snd absurd trustme
  by as
  ```

- **Punctuation**:

  ```
  ( ) [ ] { } . | , ; : := = => -> <->
  ```

Tactic names (`intro`, `split`, `left`, …) are *not* keywords. They are ordinary
identifiers that are only special where a tactic is expected, so `left` can still
be a hypothesis name. `absurd` is the one tactic name that is also a keyword,
because it is a term too.

### 1.2 Modules and items

A file is a sequence of items, each ending in `.`:

```
module      := item*
item        := axiom | theorem | proposition
axiom       := "axiom" IDENT IDENT* ":" type "."
theorem     := "theorem" IDENT IDENT* ":" type ":=" theorem_body "."
proposition := "proposition" IDENT IDENT* ":=" type "."
theorem_body := "by" script | term
```

The identifiers after an item's name are its **parameters**: the propositions it
is generic over.

```
axiom excluded_middle A : A or not A.

proposition Knave A := not A.

theorem swap A B : A and B -> B and A :=
    fun (p : A and B) => (snd p, fst p).

theorem swap' A B : A and B -> B and A := by
    intro p; destruct p as a b; split; exact b; exact a.
```

- **`axiom`** assumes a statement without proof.
- **`theorem`** states a proposition and proves it, either with a term or, after
  `by`, with a tactic script.
- **`proposition`** names a proposition, optionally with parameters. It's an
  abbreviation (see [§5.3](#53-propositions)).

Items are checked in order. Each item can use the items before it, but not itself
or later items. Theorems, axioms and propositions share one set of names, so
defining a name twice is an error, even across kinds.

### 1.3 Types (propositions)

```
type        := type_lambda ("<->" type)?
type_lambda := type_or ("->" type)?
type_or     := type_and ("or" type_or)?
type_and    := type_not ("and" type_and)?
type_not    := "not" type_not | type_app
type_app    := IDENT type_atom+ | type_atom
type_atom   := "(" type ")" | "True" | "False" | IDENT
```

| Syntax | Meaning |
| --- | --- |
| `A` | a parameter, or a proposition with no parameters |
| `F A B` | a proposition `F` applied to arguments |
| `A -> B` | implication |
| `A <-> B` | equivalence |
| `A and B` | conjunction |
| `A or B` | disjunction |
| `not A` | negation |
| `True`, `False` | truth and falsehood |

Operators from lowest to highest precedence:

| Operator | Associativity |
| --- | --- |
| `<->` | right |
| `->` | right |
| `or` | right |
| `and` | right |
| `not` | prefix |
| application `F A B` | — |

For example:
- `A and B or C -> D` is `((A and B) or C) -> D`.
- `not A and B` is `(not A) and B`.
- `A <-> B <-> C` is `A <-> (B <-> C)`.

Application arguments are atoms, so `F G A` is `F` applied to *two* arguments, `G`
and `A`; write `F (G A)` to nest. Every name in a type must be a parameter of the
enclosing item or a proposition defined earlier. A parameter hides a proposition
with the same name.

### 1.4 Terms (proofs)

```
term       := "fun" "(" IDENT ":" type ")" "=>" term
            | "case" term "of" "|" "inl" IDENT "=>" term "|" "inr" IDENT "=>" term
            | term_atom+                            -- application
term_atom  := "(" term ")"
            | "(" term ("," term)+ ")"              -- pair / tuple
            | "fst" term_atom
            | "snd" term_atom
            | "inl" "[" type "]" term_atom
            | "inr" "[" type "]" term_atom
            | "absurd" "[" type "]" term_atom
            | "trustme" "[" type "]"
            | IDENT ("[" type "]")*                 -- variable, with type arguments
```

| Term | Proves | Logical rule |
| --- | --- | --- |
| `x` | the type of hypothesis or theorem `x` | assumption |
| `f [A] [B]` | theorem `f` instantiated at `A`, `B` | ∀-elimination |
| `fun (x : A) => t` | `A -> B`, if `t` proves `B` using `x : A` | →-introduction |
| `t u` | `B`, if `t` proves `A -> B` and `u` proves `A` | →-elimination |
| `(t, u)` | `A and B` | ∧-introduction |
| `fst t`, `snd t` | `A`, `B` from `t : A and B` | ∧-elimination |
| `inl [B] t` | `A or B` from `t : A` | ∨-introduction |
| `inr [A] t` | `A or B` from `t : B` | ∨-introduction |
| `case t of \| inl x => u \| inr y => v` | `C` from `t : A or B` and both branches proving `C` | ∨-elimination |
| `absurd [C] t` | `C` from `t : False` | ⊥-elimination |
| `trustme [C]` | `C`, unproved (see [§4.5](#45-trust)) | — |

Notes:

- Application is **left**-associative: `f a b` is `(f a) b`. `fun` and `case`
  extend as far right as possible, so to pass one as an argument, put it in
  parentheses.
- `fst`, `snd`, `inl`, `inr` and `absurd` take a single atom: `fst p q` is
  `(fst p) q`.
- `(a, b, c)` is shorthand for `(a, (b, c))`, and so on for longer tuples.
- `inl [B] t` annotates the **other** side of the disjunction: the side `t`
  doesn't prove.
- A theorem with parameters must be given one type argument per parameter at
  every use (`swap [B] [A]`). Type arguments are never inferred.

### 1.5 Tactic scripts

```
script := (tactic (";" tactic)*)?
tactic := "{" script "}"
        | "intro" IDENT
        | "exact" term
        | "split" | "left" | "right"
        | "assumption" | "admit" | "exfalso"
        | "destruct" IDENT "as" IDENT IDENT
        | "cases" IDENT "as" IDENT IDENT
        | "have" IDENT ":" type (":=" term)?
        | "apply" term
        | "absurd" term
```

- Tactics are separated by `;`. A trailing `;` is an error.
- A script can be empty (`by .`, `{ }`). It proves nothing, so the error it
  produces shows the goal and its hypotheses, which is a quick way to see where a
  proof stands.
- A term inside a tactic ends at `;`, `}` or `.`.

---

## 2. Tactics

A tactic proof works backwards from the goal. At any point there is a list of
**open goals**, each made of hypotheses and a target:

```
a : A
b : B
⊢ B and A
```

Each tactic works on the **first** open goal. It either proves it outright, or
replaces it with new goals that are (one hopes) easier. The proof is finished
when no goals are left.

| Tactic | Goal | New goals | Logical rule |
| --- | --- | --- | --- |
| `intro x` | `A -> B` | `x : A ⊢ B` | →-introduction |
| `exact t` | `C` | — (`t` must prove `C`) | |
| `split` | `A and B` | `⊢ A`, then `⊢ B` | ∧-introduction |
| `left` | `A or B` | `⊢ A` | ∨-introduction |
| `right` | `A or B` | `⊢ B` | ∨-introduction |
| `assumption` | `C` | — (a hypothesis of type `C`) | |
| `exfalso` | `C` | `⊢ False` | ⊥-elimination |
| `absurd h` | `C` | as `apply h` on `False` | ⊥-elimination |
| `apply f` | `C` | `⊢ P1`, …, `⊢ Pn`, where `f : P1 -> … -> Pn -> C` | →-elimination |
| `destruct h as x y` | `C`, with `h : A and B` | `x : A, y : B ⊢ C` | ∧-elimination |
| `cases h as x y` | `C`, with `h : A or B` | `x : A ⊢ C`, then `y : B ⊢ C` | ∨-elimination |
| `have h : T` | `C` | `⊢ T`, then `h : T ⊢ C` | cut |
| `have h : T := t` | `C` | `h : T ⊢ C` (`t` must prove `T`) | cut |
| `admit` | `C` | — (unproved; see [§4.5](#45-trust)) | |
| `{ script }` | `C` | — (`script` must prove `C`) | |

Details:

- **`intro`** also works on `not A` (which means `A -> False`) and on `True`
  (which means `False -> False`). **`split`** also works on `A <-> B`, which is
  a pair of implications. See [§5](#5-desugaring).
- **`apply f`** strips off as *few* arguments as possible. With
  `f : A -> B -> C` on the goal `B -> C`, it leaves just `⊢ A`. If `f`'s type
  already equals the goal, it leaves nothing, like `exact f`. Applying a
  negation is common: `apply h` with `h : not A` turns the goal `False` into `A`.
- **`apply`** and **`absurd`** take a *name*: a hypothesis, or a theorem or axiom
  with its type arguments (`apply swap [B] [A]`). To use a more complex term,
  name it first with `have h : T := term`.
- **`absurd h`** is `exfalso; apply h`. `h` must lead to `False`, e.g.
  `h : not A` leaves the goal `A`.
- **`destruct`** and **`cases`** work on hypotheses only, not on theorems or
  axioms.
- **`have h : T`** proves `T` first. `h` is not available while proving `T`.
- **Names:** the new names in `intro`, `destruct`, `cases` and `have` can reuse
  existing names, including the name being taken apart (`destruct h as h b`).
  A hypothesis hidden by a later one with the same name can no longer be
  referred to. `assumption` won't use it, and error messages don't show it.
- **Blocks:** `{ script }` runs `script` on the first goal *only*, and it is an
  error if that goal isn't fully proved by the `}`. Blocks make branching proofs
  easier to read:

  ```
  theorem or_comm A B : A or B -> B or A := by
      intro h;
      cases h as a b;
      { right; exact a };
      { left; exact b }.
  ```

- **Unfinished proofs:** if goals remain at the end of the script (or a block),
  the error lists them in the order the next tactics would work on them.

---

## 3. Kernel language

The kernel language is the surface language with the abbreviations removed.

### 3.1 Types

```
A, B, C ::= X           atom (a parameter)
          | A -> B      implication          (Type::Lambda)
          | A and B     conjunction          (Type::Pair)
          | A or B      disjunction          (Type::Either)
          | False       falsehood            (Type::False)
```

There is no `True`, `not` or `<->` in the kernel: they are abbreviations (see
[§5](#5-desugaring)). Two types are equal only if they are written the same way,
atom for atom. There is no unfolding, because by the time types reach the kernel
there is nothing left to unfold. Atoms are **rigid**: `A` equals only `A`, never
some other type.

Error messages print kernel types in surface syntax. `A -> False` prints as
`not A`, `False -> False` as `True`, and `(A -> B) and (B -> A)` as `A <-> B`.
Named propositions can't be recovered, so they print as their expansion.

### 3.2 Terms

```
t, u, v ::= x [A1] … [An]                         variable, n ≥ 0
          | fun (x : A) => t
          | t u
          | (t, u)
          | fst t | snd t
          | inl [B] t | inr [A] t
          | case t of | inl x => u | inr y => v
          | absurd [C] t
          | trustme [C]
```

Every term carries its source location, for error messages.

### 3.3 Schemes and contexts

A **scheme** `∀X1 … Xn. A` is a type that is generic over the parameters
`X1 … Xn`. Theorems and axioms have schemes. Hypotheses bound by `fun` and `case`
have plain types, which are schemes with no parameters.

A scheme must be **closed**: every atom in `A` must be one of `X1 … Xn`, and the
`Xi` must be distinct. Lowering checks this with proper error messages. The
kernel refuses to build a scheme that breaks it as a last line of defence. This
is the side condition of ∀-introduction. It guarantees that a theorem can't
capture a proposition that isn't one of its own parameters.

**Instantiating** `∀X1 … Xn. A` with `B1 … Bn` replaces each `Xi` by `Bi`, all at
once. So instantiating `∀A B. A and B -> B and A` with `B`, `A` gives
`B and A -> A and B`. Types have no binders, so substitution can't capture
anything. The number of type arguments must equal `n`.

A **context** `Γ` is a list of bindings `x : σ`, each tagged as *proved* or
*admitted* (see [§4.5](#45-trust)). Looking up `x` finds the most recent binding,
so later bindings hide earlier ones.

---

## 4. Kernel typing rules

`Γ ⊢ t : A` means "in context `Γ`, term `t` proves `A`". For a theorem, `Γ`
contains the axioms and earlier theorems. The theorem's own parameters are
rigid atoms.

### 4.1 Rules

```
 (x : ∀X1…Xn. A) is the most recent binding of x in Γ
───────────────────────────────────────────────────────── Var
      Γ ⊢ x [B1] … [Bn] : A[X1 := B1, …, Xn := Bn]


       Γ, x : A ⊢ t : B
───────────────────────────── Fun
 Γ ⊢ fun (x : A) => t : A -> B


 Γ ⊢ t : A -> B     Γ ⊢ u : A
──────────────────────────────── App
          Γ ⊢ t u : B


 Γ ⊢ t : A     Γ ⊢ u : B
───────────────────────────── Pair
    Γ ⊢ (t, u) : A and B


 Γ ⊢ t : A and B           Γ ⊢ t : A and B
──────────────── Fst      ──────────────── Snd
  Γ ⊢ fst t : A             Γ ⊢ snd t : B


     Γ ⊢ t : A                    Γ ⊢ t : B
───────────────────── Inl    ───────────────────── Inr
 Γ ⊢ inl [B] t : A or B      Γ ⊢ inr [A] t : A or B


 Γ ⊢ t : A or B     Γ, x : A ⊢ u : C     Γ, y : B ⊢ v : C
─────────────────────────────────────────────────────────── Case
        Γ ⊢ case t of | inl x => u | inr y => v : C


    Γ ⊢ t : False
───────────────────── Absurd
 Γ ⊢ absurd [C] t : C


───────────────────── TrustMe   (marks the proof as admitted)
 Γ ⊢ trustme [C] : C
```

In **Var**, `n` must equal the number of the scheme's parameters, including
`n = 0`. A hypothesis bound by `fun` or `case` has no parameters, so it takes no
type arguments.

The annotations in `inl [B]`, `inr [A]`, `absurd [C]` and `trustme [C]` give the
types that the term itself doesn't determine. With them, every term has exactly
one type, which the kernel can compute bottom-up.

### 4.2 Items

```
 X1…Xn are distinct, and A mentions no other atoms
────────────────────────────────────────────────────  axiom name X1…Xn : A.
        bind  name : ∀X1…Xn. A   (proved)


 X1…Xn are distinct, A mentions no other atoms, and  Γ ⊢ t : A
──────────────────────────────────────────────────────────────────  theorem name X1…Xn : A := t.
     bind  name : ∀X1…Xn. A   (proved, or admitted if t is)
```

Generalising over `X1…Xn` is ∀-introduction. It's sound because nothing in `Γ`
mentions the `Xi`: every scheme in `Γ` is closed, and the `Xi` are atoms local to
this theorem. A `proposition` adds nothing to `Γ`; see [§5.3](#53-propositions).

### 4.3 Checking a theorem

The kernel checks `t` against the statement `A` with `check`. The simplest way to
do that would be to compute `t`'s type with the rules above and compare it with
`A`. The kernel accepts **exactly** the same terms as that, but it passes the
expected type down into the term so that a mistake is reported at the innermost
part that is wrong:

| Term, against expected type | Checks instead |
| --- | --- |
| `fun (x : A') => t` against `A -> B` | `A' = A`, then `t` against `B` with `x : A` |
| `(t, u)` against `A and B` | `t` against `A`, `u` against `B` |
| `inl [B'] t` against `A or B` | `B' = B`, then `t` against `A` |
| `inr [A'] t` against `A or B` | `A' = A`, then `t` against `B` |
| `case t of …` against `C` | compute `t`'s type, `A or B`; then each branch against `C` |
| `absurd [C'] t` against `C` | `C' = C`, then `t` against `False` |
| `(fun (x : A) => u) t` against `C` | `t` against `A`, then `u` against `C` with `x : A` |
| anything else | compute its type and compare with the expected type |

The last row is what `have` builds. Because of it, a `have` whose proof has the
wrong type is reported at the proof.

### 4.4 Soundness

The rules are exactly natural deduction for intuitionistic propositional logic,
with prenex (outermost) quantification over propositions. In particular,
excluded middle (`A or not A`) and double-negation elimination
(`not not A -> A`) are **not** provable; to use them, declare them as axioms.

### 4.5 Trust

`trustme [C]` (written by the user, or produced by the `admit` tactic) proves
anything, so the kernel keeps track of it:

- A proof containing `trustme` is **admitted** rather than proved.
- Each binding in `Γ` records whether it is proved or admitted. Using an admitted
  theorem makes the proof that uses it admitted too, so this spreads through
  everything that depends on it.
- An axiom counts as proved: it's a deliberate assumption, not a gap in a proof.
  Hypotheses bound by `fun` and `case` are proved too.

An admitted theorem is reported as `admitted`, not `ok`, but isn't an error.

---

## 5. Desugaring

Lowering turns surface types and terms into kernel types and terms. It resolves
every proposition name, expands named propositions, and removes the abbreviations.

### 5.1 Types

`⟦A⟧` is the kernel type for the surface type `A`, inside an item with
parameters `P` and the propositions defined so far.

| Surface | Kernel |
| --- | --- |
| `⟦X⟧`, with `X` a parameter in `P` | `X` |
| `⟦F⟧`, with `F` a proposition with no parameters | `F`'s body |
| `⟦F A1 … An⟧`, with `proposition F X1 … Xn := B` | `B[X1 := ⟦A1⟧, …, Xn := ⟦An⟧]` |
| `⟦A -> B⟧` | `⟦A⟧ -> ⟦B⟧` |
| `⟦A and B⟧` | `⟦A⟧ and ⟦B⟧` |
| `⟦A or B⟧` | `⟦A⟧ or ⟦B⟧` |
| `⟦A <-> B⟧` | `(⟦A⟧ -> ⟦B⟧) and (⟦B⟧ -> ⟦A⟧)` |
| `⟦not A⟧` | `⟦A⟧ -> False` |
| `⟦True⟧` | `False -> False` |
| `⟦False⟧` | `False` |

When looking up a name, parameters come first, then propositions. It is an error
if:

- a name is neither a parameter nor a proposition defined earlier;
- a parameter is given arguments;
- a proposition is given the wrong number of arguments (including none, for one
  with parameters);
- an item lists the same parameter twice.

`True` is `False -> False` because that is a type the kernel already has which is
always provable (by `fun (x : False) => x`), so no extra kernel construct is
needed.

### 5.2 Terms

Terms are already in kernel form, apart from:

- **Tuples:** `(t1, t2, …, tn)` is `(t1, (t2, (…, tn)))`. The parser does this.
- **Types inside terms:** the type in `fun (x : A)` and in the annotations of
  `inl`, `inr`, `absurd` and `trustme`, and type arguments `x [A]`, are lowered
  as in [§5.1](#51-types).

Lowering doesn't resolve the names of hypotheses and theorems in terms. The
elaborator and the kernel do that.

### 5.3 Propositions

`proposition F X1 … Xn := B` checks `B` with parameters `X1 … Xn` and stores
`∀X1 … Xn. ⟦B⟧` as the meaning of `F`. Every later use of `F` is replaced by
that meaning, so the kernel never sees `F`. Two consequences:

- **No recursion.** `B` is lowered before `F` is defined, so `B` can only
  mention propositions defined earlier.
- **Transparency.** `Knave A` and `not A` are the same kernel type, so a proof of
  one is a proof of the other.

### 5.4 Tactics

Lowering a tactic script lowers each type and term inside it as above (the type
in `have`, and the terms in `exact`, `have … :=`, `apply` and `absurd`), and keeps
the names and their locations for error messages.

---

## 6. Elaboration

The elaborator turns a tactic script into a kernel term, which is then checked
like any other proof ([§4.3](#43-checking-a-theorem)). The elaborator is not
trusted. It tries to build a correct term, and catches some mistakes early for
better error messages, but the kernel has the final say.

### 6.1 Goals and the proof state

A **goal** `Γ ⊢ C` is a hole `?` in the term being built that still needs a
proof of `C`. `Γ` is its list of hypotheses.

> **Invariant:** a goal's hypotheses `Γ` are exactly the binders in scope at its
> hole, in order.

Every tactic that adds a hypothesis also wraps the new hole in a binder for it.
That's why a term filling the hole can refer to the hypotheses by name.

The **proof state** is:

- a stack of goal lists, one per enclosing `{ … }` block, the top being the
  innermost. The tactics in a block only see the goals on top.
- the **solutions** recorded so far, where each solution is a partial term for
  one goal, possibly with holes for newer goals.

Elaborating `theorem name P : C := by script` starts with the single goal `⊢ C`,
with no hypotheses and with the parameters `P` as rigid atoms. Theorems and
axioms are looked up in `Γglobal`, the context of items checked so far.

### 6.2 Running a script

- **`t1; t2; …; tn`** runs each tactic on the **first** goal. A tactic replaces
  that goal with its new goals, in the order listed in [§6.3](#63-tactic-rules).
  The new goals come before any goals that were already open.
- **`{ s }`** takes the first goal `g`, runs `s` on a new level containing only
  `g`, and requires that level to be empty at the end. `g`'s solution is whatever
  `s` builds.
- **End of a script or block:** any goals left are an error ("N unsolved goals"),
  listing each one. An empty script leaves its goal unsolved, so it reports that
  goal.
- **Running out:** running a tactic when there are no goals is an error ("no
  goals left").

When the whole script succeeds, the root hole is filled with its solution, each
hole in that with its own solution, and so on, until no holes are left.

### 6.3 Tactic rules

Each rule takes the goal `Γ ⊢ C` and gives:
- the new goals, in order, as `?1`, `?2`, …;
- the term recorded for the goal, in which `?i` stands for new goal `i`;
- the conditions that must hold, which are otherwise errors.

`visible(Γ)` is `Γ` without the hypotheses hidden by a later one with the same
name.

| Tactic | Requires | New goals | Term |
| --- | --- | --- | --- |
| `intro x` | `C = A -> B` | `Γ, x : A ⊢ B` | `fun (x : A) => ?1` |
| `exact t` | each free name of `t` in `visible(Γ)` or `Γglobal` | — | `t` |
| `split` | `C = A and B` | `Γ ⊢ A`; `Γ ⊢ B` | `(?1, ?2)` |
| `left` | `C = A or B` | `Γ ⊢ A` | `inl [B] ?1` |
| `right` | `C = A or B` | `Γ ⊢ B` | `inr [A] ?1` |
| `assumption` | some `x : C` in `visible(Γ)`; the newest is used | — | `x` |
| `admit` | — | — | `trustme [C]` |
| `exfalso` | — | `Γ ⊢ False` | `absurd [C] ?1` |
| `destruct h as x y` | `h : A and B` in `visible(Γ)` | `Γ, x : A, y : B ⊢ C` | `(fun (x : A) => fun (y : B) => ?1) (fst h) (snd h)` |
| `cases h as x y` | `h : A or B` in `visible(Γ)` | `Γ, x : A ⊢ C`; `Γ, y : B ⊢ C` | `case h of \| inl x => ?1 \| inr y => ?2` |
| `have h : T` | — | `Γ ⊢ T`; `Γ, h : T ⊢ C` | `(fun (h : T) => ?2) ?1` |
| `have h : T := t` | as `exact t` | `Γ, h : T ⊢ C` | `(fun (h : T) => ?1) t` |
| `apply f [B̄]` | `f`'s type is `P1 -> … -> Pn -> C`, `n` smallest | `Γ ⊢ P1`; …; `Γ ⊢ Pn` | `f [B̄] ?1 … ?n` |
| `absurd f [B̄]` | `f`'s type is `P1 -> … -> Pn -> False`, `n` smallest | `Γ ⊢ P1`; …; `Γ ⊢ Pn` | `absurd [C] (f [B̄] ?1 … ?n)` |

Notes on the rules:

- **`exact`** and **`have … :=`** check only that the term's names exist. Whether
  `t` really proves `C` (or `T`) is left to the kernel. Since `t` fills a hole
  inside the binders for `Γ`, the kernel checks it with exactly those hypotheses.
- **`destruct`** and **`have`** bind names with a function applied straight to
  its argument (a *redex*), because the kernel has no `let`.
  - In `destruct`, `fst h` and `snd h` sit outside the binders, so they still
    refer to the pair even if `x` or `y` is also called `h`.
  - In `have`, the proof of `T` (`?1`, or `t`) sits outside the binder for `h`,
    so it can't use `h`.
- **`apply f`** looks for `f` among `visible(Γ)`, then `Γglobal`.
  - A hypothesis takes no type arguments.
  - A theorem or axiom must be given exactly its number of type arguments, and
    its type is instantiated with them.
  - It then takes `n = 0, 1, 2, …` in turn, until stripping `n` arguments off
    `f`'s type leaves exactly `C`. It's an error if no `n` works.
  - `f` must be a name. Any other term is rejected, because working out its type
    would need type inference.
- **`absurd f`** is the same with `False` in place of `C`, wrapped in
  `absurd [C]`. It's `exfalso; apply f` in a single step.
- Terms that a tactic builds take that tactic's source location. So if the kernel
  ever rejects one, the error points at the tactic responsible, and that would
  mean the elaborator has a bug.

### 6.4 Example

```
theorem and_swap A B : A and B -> B and A := by
    intro h; destruct h as a b; split; { exact b }; { exact a }.
```

| Step | Goals after it | Term so far |
| --- | --- | --- |
| start | `⊢ A and B -> B and A` | `?0` |
| `intro h` | `h : A and B ⊢ B and A` | `fun (h : A and B) => ?1` |
| `destruct h as a b` | `h, a : A, b : B ⊢ B and A` | `… (fun (a : A) => fun (b : B) => ?2) (fst h) (snd h)` |
| `split` | `… ⊢ B`; `… ⊢ A` | `… (?3, ?4)` |
| `{ exact b }` | `… ⊢ A` | `… (b, ?4)` |
| `{ exact a }` | none | `… (b, a)` |

The final term,

```
fun (h : A and B) =>
    (fun (a : A) => fun (b : B) => (b, a)) (fst h) (snd h)
```

is then checked by the kernel against `A and B -> B and A`.
