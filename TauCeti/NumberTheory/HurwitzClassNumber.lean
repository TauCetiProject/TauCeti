/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Rat.Defs

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
form of discriminant `-D` has `3 a² ≤ D`.

## Main definitions

* `TauCeti.IsReducedForm a b c`: the form `a x² + b x y + c y²` is reduced.
* `TauCeti.reducedForms D`: the finite set of reduced forms of discriminant `-D`, as triples
  `(a, b, c)`.
* `TauCeti.hurwitzClassNumber D`: the Hurwitz class number `H D`.

## Main results

* `TauCeti.mem_reducedForms`: for `0 < D`, the reduced forms of discriminant `-D` are exactly the
  reduced triples with `discrim a b c = -D`; the box the definition searches is no restriction.
* `TauCeti.hurwitzClassNumber_eq_zero_of_mod_four`: `H D = 0` when `D ≡ 1, 2 (mod 4)`, since a
  discriminant `b² - 4 a c` is `0` or `1` modulo `4`.
* The first values `H 3 = 1/3`, `H 4 = 1/2`, `H 7 = 1`, `H 8 = 1`, `H 12 = 4/3` and `H 16 = 3/2`,
  the last two exercising the two weights on non-primitive forms.

## References

* D. Zagier, *Nombres de classes et formes modulaires de poids 3/2*, C. R. Acad. Sci. Paris
  Sér. A-B **281** (1975).
* H. Cohen, *A Course in Computational Algebraic Number Theory*, GTM 138, §5.3.
* A. Popa and D. Zagier, *A simple proof of the Eichler–Selberg trace formula*,
  J. Ramanujan Math. Soc. (2019), arXiv:1711.00327.
-/

@[expose] public section

open Finset

namespace TauCeti

/-- The integral binary quadratic form `a x² + b x y + c y²` is **reduced**: `|b| ≤ a ≤ c`, and
`0 ≤ b` whenever `|b| = a` or `a = c` (Cohen, Definition 5.3.2).

For a positive-definite form this picks exactly one representative of each `SL₂(ℤ)`-class: the
inequalities place the root `τ = (-b + i √(4 a c - b²)) / (2 a)` of `a τ² + b τ + c` in
`ModularGroup.fd`, and the sign condition chooses one of the two boundary points that `SL₂(ℤ)`
identifies. Definiteness is not part of the predicate (`IsReducedForm 0 0 1` holds), but a reduced
form with `discrim a b c < 0` has `0 < a`. -/
def IsReducedForm (a b c : ℤ) : Prop :=
  |b| ≤ a ∧ a ≤ c ∧ (|b| = a ∨ a = c → 0 ≤ b)

instance (a b c : ℤ) : Decidable (IsReducedForm a b c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The reduced forms `a x² + b x y + c y²` of discriminant `b² - 4 a c = -D`, as triples
`(a, b, c)`.

The definition searches the box `1 ≤ a, c ≤ D / 3`, `|b| ≤ D / 3`, which makes it a finite,
decidable set; `mem_reducedForms` shows that for `0 < D` this box loses nothing. For `D = 0` the box
is empty, so `reducedForms 0 = ∅`, although every `c y²` with `0 ≤ c` is a reduced form of
discriminant `0`. -/
def reducedForms (D : ℕ) : Finset (ℤ × ℤ × ℤ) := {t ∈ Icc 1 (D / 3 : ℤ) ×ˢ
    Icc (-(D / 3) : ℤ) (D / 3) ×ˢ Icc 1 (D / 3 : ℤ) | discrim t.1 t.2.1 t.2.2 = -D ∧
    IsReducedForm t.1 t.2.1 t.2.2}

/-- **The reduced forms of discriminant `-D`** are the reduced triples `(a, b, c)` with
`discrim a b c = -D`, for `0 < D`: a reduced form of negative discriminant has `1 ≤ a` and
`3 a c ≤ D`, so the box that `reducedForms` searches contains all of them. -/
theorem mem_reducedForms {D : ℕ} (hD : 0 < D) {a b c : ℤ} :
    (a, b, c) ∈ reducedForms D ↔ discrim a b c = -D ∧ IsReducedForm a b c := by
  simp only [reducedForms, mem_filter, mem_product, mem_Icc]
  refine ⟨fun h ↦ h.2, fun ⟨hd, hb, hac, h⟩ ↦ ⟨?_, hd, hb, hac, h⟩⟩
  rw [discrim] at hd
  have hD' : (0 : ℤ) < D := by exact_mod_cast hD
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  have hb2 : b ^ 2 ≤ a ^ 2 := by nlinarith
  -- `a = 0` would force `b = 0` and discriminant `0`; so `1 ≤ a`, and then `3 a c ≤ D`
  have ha : 1 ≤ a := by nlinarith
  have hc : 3 * (a * c) ≤ D := by nlinarith
  have h3a : 3 * a ≤ D := by nlinarith
  have h3c : 3 * c ≤ D := by nlinarith
  refine ⟨⟨ha, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega⟩

/-- A discriminant `b² - 4 a c` is `0` or `1` modulo `4`, so there are no reduced forms of
discriminant `-D` when `D ≡ 1, 2 (mod 4)`. -/
theorem reducedForms_eq_empty_of_mod_four {D : ℕ} (hD : D % 4 = 1 ∨ D % 4 = 2) :
    reducedForms D = ∅ := by
  refine eq_empty_of_forall_notMem fun ⟨a, b, c⟩ h ↦ ?_
  replace h := (mem_filter.mp h).2.1
  rw [discrim] at h
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' b
  · have : (D : ℤ) = 4 * (a * c - k ^ 2) := by linear_combination h
    generalize a * c - k ^ 2 = m at this
    omega
  · have : (D : ℤ) = 4 * (a * c - k ^ 2 - k) - 1 := by linear_combination h
    generalize a * c - k ^ 2 - k = m at this
    omega

/-- **The Hurwitz class number** `H D`: `H 0 = -1/12`, and for `0 < D` the number of reduced forms
of discriminant `-D`, the multiples of `x² + y²` (the forms `(a, 0, a)`) weighted by `1/2` and the
multiples of `x² + x y + y²` (the forms `(a, a, a)`) by `1/3`.

This is Zagier's normalisation, the one in which the `t² = 4 n` terms of the Eichler–Selberg trace
formula absorb the identity contribution through `H 0`. It vanishes for `D ≡ 1, 2 (mod 4)`
(`hurwitzClassNumber_eq_zero_of_mod_four`). -/
def hurwitzClassNumber (D : ℕ) : ℚ :=
  if D = 0 then -1 / 12 else
    ∑ t ∈ reducedForms D,
      if t.2.1 = 0 ∧ t.1 = t.2.2 then 1 / 2 else if t.1 = t.2.1 ∧ t.2.1 = t.2.2 then 1 / 3 else 1

@[simp] theorem hurwitzClassNumber_zero : hurwitzClassNumber 0 = -1 / 12 := rfl

/-- **`H D = 0` for `D ≡ 1, 2 (mod 4)`**: no discriminant `b² - 4 a c` is `-1` or `-2`
modulo `4`. -/
theorem hurwitzClassNumber_eq_zero_of_mod_four {D : ℕ} (hD : D % 4 = 1 ∨ D % 4 = 2) :
    hurwitzClassNumber D = 0 := by
  have : D ≠ 0 := by omega
  simp [hurwitzClassNumber, this, reducedForms_eq_empty_of_mod_four hD]

/-! ### The first values -/

/-- `H 3 = 1/3`: the only reduced form of discriminant `-3` is `x² + x y + y²`. -/
theorem hurwitzClassNumber_three : hurwitzClassNumber 3 = 1 / 3 := by decide +kernel

/-- `H 4 = 1/2`: the only reduced form of discriminant `-4` is `x² + y²`. -/
theorem hurwitzClassNumber_four : hurwitzClassNumber 4 = 1 / 2 := by decide +kernel

/-- `H 7 = 1`: the only reduced form of discriminant `-7` is `x² + x y + 2 y²`. -/
theorem hurwitzClassNumber_seven : hurwitzClassNumber 7 = 1 := by decide +kernel

/-- `H 8 = 1`: the only reduced form of discriminant `-8` is `x² + 2 y²`. -/
theorem hurwitzClassNumber_eight : hurwitzClassNumber 8 = 1 := by decide +kernel

/-- `H 12 = 4/3`: the reduced forms of discriminant `-12` are `x² + 3 y²` and the non-primitive
`2 (x² + x y + y²)`, which counts `1/3`. -/
theorem hurwitzClassNumber_twelve : hurwitzClassNumber 12 = 4 / 3 := by decide +kernel

/-- `H 16 = 3/2`: the reduced forms of discriminant `-16` are `x² + 4 y²` and the non-primitive
`2 (x² + y²)`, which counts `1/2`. -/
theorem hurwitzClassNumber_sixteen : hurwitzClassNumber 16 = 3 / 2 := by decide +kernel

end TauCeti
