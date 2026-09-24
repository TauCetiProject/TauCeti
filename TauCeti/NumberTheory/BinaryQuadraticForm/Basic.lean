/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import TauCeti.Algebra.QuadraticDiscriminant
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Binary quadratic forms and the action of `SL(2, R)`

A binary quadratic form over a commutative ring `R` is a polynomial `a x² + b x y + c y²`; here it
is recorded by its three coefficients, as `TauCeti.BinaryQuadraticForm R`. The group `SL(2, R)` acts
on such forms by linear change of variables, and over `ℤ` the forms that are positive definite of a
fixed discriminant `-D < 0` form a sub-action. Its orbits are the classes counted, with weights, by
the Hurwitz class number `H(D)` (`TauCeti.hurwitzClassNumber`). Through the form `v ↦ det(v, M v)`
attached to an integer matrix `M`, they also describe the `SL(2, ℤ)`-conjugacy classes of integer
matrices of fixed trace and determinant, which is how they enter the Eichler–Selberg trace formula.
This file supplies the action on which both descriptions are built.

The action is on the left, by `γ • f = f ∘ γ⁻¹`. For `γ = !![p, q; r, s]` the inverse is the
adjugate `!![s, -q; -r, p]` (Mathlib's `Matrix.SpecialLinearGroup.SL2_inv_expl`), so
`(γ • f)(x, y) = f(s x - q y, -r x + p y)` and the new coefficients are
```
a' = a s² - b r s + c r²
b' = b (p s + q r) - 2 a q s - 2 c p r
c' = a q² - b p q + c p².
```
Only the entries of the adjugate occur, so the action laws are polynomial identities and need no
determinant hypothesis. The substitution `f ↦ f ∘ γ` found in much of the classical literature is
a right action; composing with `γ⁻¹` instead gives the left action that `MulAction` expects, with
the same orbits. With this convention `T • ⟨a, b, c⟩ = ⟨a, b - 2 a, a - b + c⟩` and
`S • ⟨a, b, c⟩ = ⟨c, -b, a⟩`, where `S` and `T` are Mathlib's `ModularGroup.S = !![0, -1; 1, 0]`
and `ModularGroup.T = !![1, 1; 0, 1]`; the examples at the end of the file check both formulas.
It is also the convention for which the root `(-b + √(-D)) / (2 a)` of a positive definite form
moves by the Möbius action of `γ` on the upper half-plane.

The discriminant `discrim a b c = b² - 4 a c` changes by the factor `(det γ)² = 1`. Positivity of
the leading coefficient is then preserved: `(γ • f).a = f(s, -r)` is a value of the non-negative
form `f`, and a form of negative discriminant with non-negative leading coefficient has positive
leading coefficient. This needs `D ≠ 0`: the form `⟨1, 2, 1⟩` of discriminant `0` is sent by
`!![1, 0; 1, 1]` to a form with leading coefficient `0`.

Mathlib's `QuadraticForm R (Fin 2 → R)` is not used, because its discriminant is built from the
associated bilinear form and so requires `2` to be invertible in `R`, which fails over `ℤ`.

## Main definitions

* `TauCeti.BinaryQuadraticForm R`: the binary quadratic form `a x² + b x y + c y²` over `R`.
* `TauCeti.BinaryQuadraticForm.equivProd`: a form is its triple of coefficients `(a, b, c)`.
* `TauCeti.BinaryQuadraticForm.discrim`: its discriminant `b² - 4 a c`.
* `TauCeti.BinaryQuadraticForm.eval`: its value `a x² + b x y + c y²` at `(x, y)`.
* The instance `MulAction SL(2, R) (TauCeti.BinaryQuadraticForm R)`: the action
  `γ • f = f ∘ γ⁻¹`, for a commutative ring `R`.
* `TauCeti.BinaryQuadraticForm.posDef D`: for `D ≠ 0`, the positive definite integral forms of
  discriminant `-D`, as a sub-action of `SL(2, ℤ)`.

## Main results

* `TauCeti.BinaryQuadraticForm.smul_a`, `TauCeti.BinaryQuadraticForm.smul_b` and
  `TauCeti.BinaryQuadraticForm.smul_c`: the coefficients of `γ • f`.
* `TauCeti.BinaryQuadraticForm.eval_smul`: `γ • f` is `f ∘ γ⁻¹`.
* `TauCeti.BinaryQuadraticForm.discrim_smul`: the discriminant is invariant under `SL(2, R)`.
* `TauCeti.BinaryQuadraticForm.mem_posDef`: membership in `posDef D`.

## Implementation notes

`discrim` and `equivProd` are exposed, so that the kernel can evaluate them, as `decide` does for
the values of `TauCeti.hurwitzClassNumber`; the other definitions are not.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, Graduate Texts in Mathematics
  138, Springer, 1993, §5.2–5.3.
* D. A. Buell, *Binary Quadratic Forms: Classical Theory and Modern Computations*, Springer, 1989.
* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti

/-- A binary quadratic form `a x² + b x y + c y²` over `R`, recorded by its three coefficients. -/
@[ext]
structure BinaryQuadraticForm (R : Type*) where
  /-- The coefficient of `x²`. -/
  a : R
  /-- The coefficient of `x y`. -/
  b : R
  /-- The coefficient of `y²`. -/
  c : R
  deriving DecidableEq

namespace BinaryQuadraticForm

/-- A binary quadratic form is its triple of coefficients `(a, b, c)`. -/
@[expose, simps]
def equivProd {R : Type*} : BinaryQuadraticForm R ≃ R × R × R where
  toFun f := (f.a, f.b, f.c)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩

section Semiring

variable {R : Type*} [Semiring R]

/-- The value `a x² + b x y + c y²` of the form `f` at `(x, y)`. -/
def eval (f : BinaryQuadraticForm R) (x y : R) : R :=
  f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2

/-- The value of `f` at `(x, y)` is `a x² + b x y + c y²`. -/
theorem eval_def (f : BinaryQuadraticForm R) (x y : R) :
    f.eval x y = f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2 :=
  (rfl)

/-- The value of the form `⟨a, b, c⟩` at `(x, y)` is `a x² + b x y + c y²`. -/
@[simp]
theorem eval_mk (a b c x y : R) :
    (⟨a, b, c⟩ : BinaryQuadraticForm R).eval x y = a * x ^ 2 + b * x * y + c * y ^ 2 :=
  (rfl)

/-- The value of `f` at `(1, 0)` is its first coefficient `a`. -/
@[simp]
theorem eval_one_zero (f : BinaryQuadraticForm R) : f.eval 1 0 = f.a := by
  simp [eval_def]

/-- The value of `f` at `(0, 1)` is its last coefficient `c`. -/
@[simp]
theorem eval_zero_one (f : BinaryQuadraticForm R) : f.eval 0 1 = f.c := by
  simp [eval_def]

end Semiring

variable {R : Type*} [CommRing R]

/-- The discriminant `b² - 4 a c` of the form `a x² + b x y + c y²`. -/
@[expose]
protected def discrim (f : BinaryQuadraticForm R) : R :=
  discrim f.a f.b f.c

/-- The discriminant of a form is Mathlib's `discrim` of its coefficients. -/
theorem discrim_def (f : BinaryQuadraticForm R) : f.discrim = discrim f.a f.b f.c :=
  rfl

/-- `γ • f` is the form `f ∘ γ⁻¹` (`eval_smul`). The coefficients are written through the entries
of the adjugate `γ⁻¹ = !![s, -q; -r, p]` of `γ = !![p, q; r, s]`, so each is a polynomial in the
entries of `γ`. -/
instance : SMul SL(2, R) (BinaryQuadraticForm R) where
  smul γ f :=
    { a := f.a * γ 1 1 ^ 2 - f.b * γ 1 0 * γ 1 1 + f.c * γ 1 0 ^ 2
      b := f.b * (γ 0 0 * γ 1 1 + γ 0 1 * γ 1 0) - 2 * f.a * γ 0 1 * γ 1 1 -
        2 * f.c * γ 0 0 * γ 1 0
      c := f.a * γ 0 1 ^ 2 - f.b * γ 0 0 * γ 0 1 + f.c * γ 0 0 ^ 2 }

/-- The `x²`-coefficient of `γ • f` is `f(s, -r) = a s² - b r s + c r²`, for
`γ = !![p, q; r, s]`. -/
@[simp]
theorem smul_a (γ : SL(2, R)) (f : BinaryQuadraticForm R) :
    (γ • f).a = f.a * γ 1 1 ^ 2 - f.b * γ 1 0 * γ 1 1 + f.c * γ 1 0 ^ 2 :=
  rfl

/-- The `x y`-coefficient of `γ • f` is `b (p s + q r) - 2 a q s - 2 c p r`, for
`γ = !![p, q; r, s]`. -/
@[simp]
theorem smul_b (γ : SL(2, R)) (f : BinaryQuadraticForm R) :
    (γ • f).b = f.b * (γ 0 0 * γ 1 1 + γ 0 1 * γ 1 0) - 2 * f.a * γ 0 1 * γ 1 1 -
      2 * f.c * γ 0 0 * γ 1 0 :=
  rfl

/-- The `y²`-coefficient of `γ • f` is `f(-q, p) = a q² - b p q + c p²`, for
`γ = !![p, q; r, s]`. -/
@[simp]
theorem smul_c (γ : SL(2, R)) (f : BinaryQuadraticForm R) :
    (γ • f).c = f.a * γ 0 1 ^ 2 - f.b * γ 0 0 * γ 0 1 + f.c * γ 0 0 ^ 2 :=
  rfl

/-- `γ • f` is `f ∘ γ⁻¹`: its value at `(x, y)` is `f(s x - q y, -r x + p y)`, for
`γ = !![p, q; r, s]`. -/
@[simp]
theorem eval_smul (γ : SL(2, R)) (f : BinaryQuadraticForm R) (x y : R) :
    (γ • f).eval x y = f.eval (γ 1 1 * x - γ 0 1 * y) (-γ 1 0 * x + γ 0 0 * y) := by
  simp only [eval_def, smul_a, smul_b, smul_c]
  ring

/-- `f ↦ f ∘ γ⁻¹` is a left action of `SL(2, R)` on binary quadratic forms. -/
instance : MulAction SL(2, R) (BinaryQuadraticForm R) where
  one_smul f := by simp [BinaryQuadraticForm.ext_iff]
  mul_smul γ δ f := by
    simp only [BinaryQuadraticForm.ext_iff, smul_a, smul_b, smul_c, SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨?_, ?_, ?_⟩ <;> ring

/-- The discriminant `b² - 4 a c` of a binary quadratic form is invariant under `SL(2, R)`. -/
@[simp]
theorem discrim_smul (γ : SL(2, R)) (f : BinaryQuadraticForm R) : (γ • f).discrim = f.discrim := by
  simp only [discrim_def, discrim, smul_a, smul_b, smul_c]
  linear_combination (f.b ^ 2 - 4 * f.a * f.c) * congr($(γ.fin_two_mul_sub_mul_eq_one) ^ 2)

/-- The positive definite integral binary quadratic forms of discriminant `-D`, for `D ≠ 0`, as a
sub-action of `SL(2, ℤ)`: the forms of discriminant `-D` whose leading coefficient is positive. -/
def posDef (D : ℕ) [NeZero D] : SubMulAction SL(2, ℤ) (BinaryQuadraticForm ℤ) where
  carrier := {f | f.discrim = -D ∧ 0 < f.a}
  smul_mem' γ f := by
    rintro ⟨hD, ha⟩
    have hd : f.discrim < 0 := by simp [hD, NeZero.pos]
    refine ⟨(discrim_smul γ f).trans hD, pos_of_nonneg_of_discrim_lt_zero ?_ <|
      (discrim_def (γ • f)).symm.trans_lt <| (discrim_smul γ f).trans_lt hd⟩
    -- `(γ • f).a` is the value of `γ • f` at `(1, 0)`, that is the value of `f` at `(s, -r)`
    calc
      0 ≤ f.eval (γ 1 1) (-γ 1 0) := by
        rw [eval_def]
        exact nonneg_of_discrim_le_zero ha ((discrim_def f).symm.trans_lt hd).le _ _
      _ = (γ • f).eval 1 0 := by
        rw [eval_smul]
        simp
      _ = (γ • f).a := eval_one_zero _

/-- A form lies in `posDef D` exactly when its discriminant is `-D` and its leading coefficient is
positive. -/
@[simp]
theorem mem_posDef {D : ℕ} [NeZero D] {f : BinaryQuadraticForm ℤ} :
    f ∈ posDef D ↔ f.discrim = -D ∧ 0 < f.a :=
  Iff.rfl

/-! The convention `γ • f = f ∘ γ⁻¹` on the generators `T` and `S`: the formulas of the module
docstring. -/

example (a b c : ℤ) :
    ModularGroup.T • (⟨a, b, c⟩ : BinaryQuadraticForm ℤ) = ⟨a, b - 2 * a, a - b + c⟩ := by
  ext <;> simp [ModularGroup.coe_T]

example (a b c : ℤ) : ModularGroup.S • (⟨a, b, c⟩ : BinaryQuadraticForm ℤ) = ⟨c, -b, a⟩ := by
  ext <;> simp [ModularGroup.coe_S]

end BinaryQuadraticForm

end TauCeti
