/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import TauCeti.NumberTheory.BinaryQuadraticForm.Reduced

/-!
# Hurwitz class numbers

The Hurwitz class number `H D` of a natural number `D` counts the positive-definite integral binary
quadratic forms `a x² + b x y + c y²` of discriminant `b² - 4 a c = -D` up to
`SL₂(ℤ)`-equivalence, where the classes of the multiples of `x² + y²` count with weight `1/2` and
those of the multiples of `x² + x y + y²` with weight `1/3`, and where `H 0 = -1/12`. These are
the class numbers that enter the Eichler–Selberg trace formula for the Hecke operators on
`S_k(SL₂(ℤ))`.

Here `H D` is *defined* combinatorially, as a weighted count of the **reduced** forms
`TauCeti.reducedForms D` of `TauCeti.NumberTheory.BinaryQuadraticForm.Reduced`: those with
`|b| ≤ a ≤ c`, and with `0 ≤ b` whenever `|b| = a` or `a = c`. Every positive-definite form is
equivalent to exactly one reduced form, so the count is the class count; that comparison is
separate. The definition involves no class groups, and it is a finite, decidable sum.

## Main definitions

* `TauCeti.reducedFormWeight f`: the weight `1/2`, `1/3` or `1` with which a reduced form counts.
* `TauCeti.hurwitzClassNumber D`: the Hurwitz class number `H D`.

## Main results

* `TauCeti.hurwitzClassNumber_eq_zero_of_mod_four_eq_one_or_two`: `H D = 0` when
  `D ≡ 1, 2 (mod 4)`, since a discriminant `b² - 4 a c` is `0` or `1` modulo `4`
  (`Int.discrim_emod_four`).
* The first values `H 3 = 1/3`, `H 4 = 1/2`, `H 7 = 1`, `H 8 = 1`, `H 12 = 4/3` and `H 16 = 3/2`,
  the last two exercising the two weights on non-primitive forms.

## References

* D. Zagier, *Nombres de classes et formes modulaires de poids 3/2*, C. R. Acad. Sci. Paris
  Sér. A-B **281** (1975).
* H. Cohen, *A Course in Computational Algebraic Number Theory*, GTM 138, §5.3.
* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327.
-/

@[expose] public section

open Finset

namespace TauCeti

/-- The weight with which a reduced form `f = a x² + b x y + c y²` counts in the Hurwitz class
number: `1/2` for the multiples `⟨a, 0, a⟩` of `x² + y²`, `1/3` for the nonzero multiples
`⟨a, a, a⟩` of `x² + x y + y²`, and `1` for every other form. -/
def reducedFormWeight (f : BinaryQuadraticForm ℤ) : ℚ :=
  if f.b = 0 ∧ f.a = f.c then 1 / 2
  else if f.a = f.b ∧ f.b = f.c then 1 / 3
  else 1

/-- The multiples `⟨a, 0, a⟩` of `x² + y²` count `1/2`. -/
@[simp] theorem reducedFormWeight_self_zero_self (a : ℤ) : reducedFormWeight ⟨a, 0, a⟩ = 1 / 2 :=
  ite_eq_left ⟨rfl, rfl⟩

/-- The nonzero multiples `⟨a, a, a⟩` of `x² + x y + y²` count `1/3`. -/
@[simp] theorem reducedFormWeight_self_self_self {a : ℤ} (ha : a ≠ 0) :
    reducedFormWeight ⟨a, a, a⟩ = 1 / 3 :=
  (ite_eq_right fun h ↦ ha h.1).trans <| ite_eq_left ⟨rfl, rfl⟩

/-- Every form other than the multiples `⟨a, 0, a⟩` of `x² + y²` and `⟨a, a, a⟩` of
`x² + x y + y²` counts `1`. -/
@[simp] theorem reducedFormWeight_eq_one {f : BinaryQuadraticForm ℤ} (h₁ : ¬(f.b = 0 ∧ f.a = f.c))
    (h₂ : ¬(f.a = f.b ∧ f.b = f.c)) : reducedFormWeight f = 1 :=
  (ite_eq_right h₁).trans <| ite_eq_right h₂

/-- **The Hurwitz class number** `H D`: `H 0 = -1/12`, and for `D ≠ 0` the number of reduced forms
of discriminant `-D`, primitive or not, each counted with its `reducedFormWeight`.

The value `H 0 = -1/12` is Zagier's normalisation, the one in which the `t² = 4 n` terms of the
Eichler–Selberg trace formula absorb the contribution of the scalar matrices. `H D` vanishes for
`D ≡ 1, 2 (mod 4)` (`hurwitzClassNumber_eq_zero_of_mod_four_eq_one_or_two`). -/
def hurwitzClassNumber (D : ℕ) : ℚ :=
  if D = 0 then -1 / 12 else ∑ f ∈ reducedForms D, reducedFormWeight f

/-- `H 0 = -1/12` is Zagier's normalisation, not a weighted count of reduced forms as `H D` is for
`D ≠ 0` (`hurwitzClassNumber_of_ne_zero`). -/
@[simp] theorem hurwitzClassNumber_zero : hurwitzClassNumber 0 = -1 / 12 := rfl

/-- `H D` for `D ≠ 0` is the weighted count of the reduced forms of discriminant `-D`. -/
theorem hurwitzClassNumber_of_ne_zero {D : ℕ} (hD : D ≠ 0) :
    hurwitzClassNumber D = ∑ f ∈ reducedForms D, reducedFormWeight f :=
  ite_eq_right hD

/-- The Hurwitz class number `H D` is `0` for `D ≡ 1, 2 (mod 4)`. -/
@[simp]
theorem hurwitzClassNumber_eq_zero_of_mod_four_eq_one_or_two {D : ℕ} (hD : D % 4 = 1 ∨ D % 4 = 2) :
    hurwitzClassNumber D = 0 := by
  rw [hurwitzClassNumber_of_ne_zero (by lia), reducedForms_eq_empty_of_mod_four_eq_one_or_two hD,
    sum_empty]

/-! ### The first values -/

/-- `H 3 = 1/3`: the only reduced form of discriminant `-3` is `x² + x y + y²`, which counts
`1/3`. -/
@[simp] theorem hurwitzClassNumber_three : hurwitzClassNumber 3 = 1 / 3 := by decide +kernel

/-- `H 4 = 1/2`: the only reduced form of discriminant `-4` is `x² + y²`, which counts `1/2`. -/
@[simp] theorem hurwitzClassNumber_four : hurwitzClassNumber 4 = 1 / 2 := by decide +kernel

/-- `H 7 = 1`: the only reduced form of discriminant `-7` is `x² + x y + 2 y²`. -/
@[simp] theorem hurwitzClassNumber_seven : hurwitzClassNumber 7 = 1 := by decide +kernel

/-- `H 8 = 1`: the only reduced form of discriminant `-8` is `x² + 2 y²`. -/
@[simp] theorem hurwitzClassNumber_eight : hurwitzClassNumber 8 = 1 := by decide +kernel

/-- `H 12 = 4/3`: the reduced forms of discriminant `-12` are `x² + 3 y²` and the non-primitive
`2 (x² + x y + y²)`, which counts `1/3`. -/
@[simp] theorem hurwitzClassNumber_twelve : hurwitzClassNumber 12 = 4 / 3 := by decide +kernel

/-- `H 16 = 3/2`: the reduced forms of discriminant `-16` are `x² + 4 y²` and the non-primitive
`2 (x² + y²)`, which counts `1/2`. -/
@[simp] theorem hurwitzClassNumber_sixteen : hurwitzClassNumber 16 = 3 / 2 := by decide +kernel

end TauCeti
