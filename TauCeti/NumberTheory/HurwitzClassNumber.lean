/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Interval
public import TauCeti.NumberTheory.BinaryQuadraticForm.Basic
import TauCeti.Algebra.QuadraticDiscriminant

/-!
# Hurwitz class numbers

The Hurwitz class number `H D` of a natural number `D` counts the positive-definite integral binary
quadratic forms `a x² + b x y + c y²` of discriminant `b² - 4 a c = -D` up to
`SL₂(ℤ)`-equivalence, where the classes of the multiples of `x² + y²` count with weight `1/2` and
those of the multiples of `x² + x y + y²` with weight `1/3`, and where `H 0 = -1/12`. These are
the class numbers that enter the Eichler–Selberg trace formula for the Hecke operators on
`S_k(SL₂(ℤ))`.

Here `H D` is *defined* combinatorially, as a weighted count of **reduced** forms: those with
`|b| ≤ a ≤ c`, and with `0 ≤ b` whenever `|b| = a` or `a = c`. Every positive-definite form is
equivalent to exactly one reduced form, the boundary conditions being what removes the double
count on the edges of the fundamental domain, so the count is the class count; that comparison is
separate. The definition involves no class groups, and it is a finite, decidable sum: a reduced
form of discriminant `-D` has `|b| ≤ a ≤ √(D / 3)` and `c ≤ D / 3`.

## Main definitions

* `TauCeti.IsReducedForm f`: the form `f = a x² + b x y + c y²` is reduced.
* `TauCeti.reducedForms D`: for `D ≠ 0`, the finite set of reduced forms of discriminant `-D`.
* `TauCeti.reducedFormWeight f`: the weight `1/2`, `1/3` or `1` with which a reduced form counts.
* `TauCeti.hurwitzClassNumber D`: the Hurwitz class number `H D`.

## Main results

* `TauCeti.mem_reducedForms`: for `D ≠ 0`, the reduced forms of discriminant `-D` are exactly the
  reduced forms `f` with `f.discrim = -D`; the box the definition searches is no restriction.
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

/-- The integral binary quadratic form `f = a x² + b x y + c y²` is **reduced**: `|b| ≤ a ≤ c`,
and `0 ≤ b` whenever `|b| = a` or `a = c` (Cohen, Definition 5.3.2).

For a positive-definite form this picks exactly one representative of each `SL₂(ℤ)`-class: the
inequalities place the root `τ = (-b + i √(4 a c - b²)) / (2 a)` of `a τ² + b τ + c` in
`ModularGroup.fd`, and the sign condition chooses one of the two boundary points that `SL₂(ℤ)`
identifies. Definiteness is not part of the predicate (`IsReducedForm ⟨0, 0, 1⟩` holds), but a
reduced form with `f.discrim < 0` has `0 < f.a` (`pos_of_nonneg_of_discrim_lt_zero`). -/
def IsReducedForm (f : BinaryQuadraticForm ℤ) : Prop :=
  |f.b| ≤ f.a ∧ f.a ≤ f.c ∧ (|f.b| = f.a ∨ f.a = f.c → 0 ≤ f.b)
deriving Decidable

/-- `a x² + b x y + c y²` is reduced exactly when `|b| ≤ a ≤ c`, and `0 ≤ b` whenever `|b| = a` or
`a = c`. -/
theorem isReducedForm_iff {f : BinaryQuadraticForm ℤ} :
    IsReducedForm f ↔ |f.b| ≤ f.a ∧ f.a ≤ f.c ∧ (|f.b| = f.a ∨ f.a = f.c → 0 ≤ f.b) :=
  Iff.rfl

/-- The reduced forms `a x² + b x y + c y²` of discriminant `b² - 4 a c = -D`.

The definition searches the box `1 ≤ a ≤ √(D / 3)`, `|b| ≤ √(D / 3)`, `1 ≤ c ≤ D / 3` (with
`Nat.sqrt`), which makes it a finite, decidable set; `mem_reducedForms` shows that for `D ≠ 0` this
box loses nothing. For `D = 0` the box is empty, so `reducedForms 0 = ∅`, although every `c y²`
with `0 ≤ c` is a reduced form of discriminant `0`. -/
def reducedForms (D : ℕ) : Finset (BinaryQuadraticForm ℤ) :=
  {f ∈ (Icc 1 ((D / 3).sqrt : ℤ) ×ˢ Icc (-(D / 3).sqrt : ℤ) (D / 3).sqrt ×ˢ
      Icc 1 (D / 3 : ℤ)).map BinaryQuadraticForm.equivProd.symm.toEmbedding |
    f.discrim = -D ∧ IsReducedForm f}

/-- **The reduced forms of discriminant `-D`**: for `D ≠ 0`, `f ∈ reducedForms D` exactly when
`f.discrim = -D` and `f` is reduced, so the box that `reducedForms` searches loses nothing. -/
@[simp] theorem mem_reducedForms {D : ℕ} (hD : D ≠ 0) {f : BinaryQuadraticForm ℤ} :
    f ∈ reducedForms D ↔ f.discrim = -D ∧ IsReducedForm f := by
  refine mem_filter.trans <| and_iff_right_of_imp fun ⟨hd, hr⟩ ↦ mem_map_equiv.2 ?_
  obtain ⟨a, b, c⟩ := f
  simp only [BinaryQuadraticForm.discrim_def, isReducedForm_iff] at hd hr
  simp only [Equiv.symm_symm, BinaryQuadraticForm.equivProd_apply, mem_product, mem_Icc]
  have ha := pos_of_nonneg_of_discrim_lt_zero ((abs_nonneg b).trans hr.1) (hd.trans_lt <| by lia)
  obtain ⟨hb, hac, -⟩ := hr
  rw [discrim] at hd
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  -- `3 a² ≤ 3 a c ≤ 4 a c - b² = D`, as `b² ≤ a² ≤ a c`; so `|b| ≤ a ≤ √(D / 3)` and `c ≤ D / 3`
  have hbb := mul_self_le_mul_self_of_le_of_neg_le hb₂ (neg_le.mp hb₁)
  have hac' := mul_le_mul_of_nonneg_left hac ha.le
  have : 3 * c ≤ D := by linarith [le_mul_of_one_le_left (ha.le.trans hac) ha]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha.le
  have hn : n ≤ (D / 3).sqrt := Nat.le_sqrt.2 <| (Nat.le_div_iff_mul_le three_pos).2 <| by
    zify; linarith
  lia

/-- The search box of `reducedForms 0` is empty. -/
@[simp] theorem reducedForms_zero : reducedForms 0 = ∅ := rfl

/-- There are no reduced forms of discriminant `-D` when `D ≡ 1, 2 (mod 4)`: a discriminant
`b² - 4 a c` is `0` or `1` modulo `4` (`Int.discrim_emod_four`). -/
@[simp]
theorem reducedForms_eq_empty_of_mod_four_eq_one_or_two {D : ℕ} (hD : D % 4 = 1 ∨ D % 4 = 2) :
    reducedForms D = ∅ :=
  filter_eq_empty_iff.mpr fun f _ ⟨h, _⟩ ↦ by
    have := Int.discrim_emod_four f.a f.b f.c
    rw [BinaryQuadraticForm.discrim_def] at h
    lia

/-- The weight with which a reduced form `f = a x² + b x y + c y²` counts in the Hurwitz class
number: `1/2` for the multiples `⟨a, 0, a⟩` of `x² + y²`, `1/3` for the multiples `⟨a, a, a⟩` of
`x² + x y + y²`, and `1` for every other form. -/
def reducedFormWeight (f : BinaryQuadraticForm ℤ) : ℚ :=
  if f.b = 0 ∧ f.a = f.c then 1 / 2
  else if f.a = f.b ∧ f.b = f.c then 1 / 3
  else 1

/-- The multiples `⟨a, 0, a⟩` of `x² + y²` count `1/2`. -/
@[simp] theorem reducedFormWeight_self_zero_self (a : ℤ) : reducedFormWeight ⟨a, 0, a⟩ = 1 / 2 :=
  ite_eq_left ⟨rfl, rfl⟩

/-- The nonzero multiples `⟨a, a, a⟩` of `x² + x y + y²` count `1/3`. -/
@[simp] theorem reducedFormWeight_self_self_self {a : ℤ} (ha : a ≠ 0) :
    reducedFormWeight ⟨a, a, a⟩ = 1 / 3 := by
  simp [reducedFormWeight, ha]

/-- Every other form counts `1`. -/
@[simp] theorem reducedFormWeight_eq_one {a b c : ℤ} (h₁ : ¬(b = 0 ∧ a = c))
    (h₂ : ¬(a = b ∧ b = c)) : reducedFormWeight ⟨a, b, c⟩ = 1 := by
  simp [reducedFormWeight, h₁, h₂]

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
