/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.WPlusMonotone

/-!
# w⁺-monotonicity of products of spheres

Let `M = ∏_{i ∈ ι} S²` be a finite product of two-spheres with a product symplectic form giving
the `i`-th factor, with its standard orientation, the area `a i > 0`. Its spherical classes are
`ℤ^ι`, with area `ω(A) = ∑ i, a i * A i` (`TauCeti.Floer.WPlusMonotoneExample.area`) and first
Chern number `c₁(A) = 2 ∑ i, A i` (`TauCeti.Floer.WPlusMonotoneExample.chern`), since
`c₁(TS²)[S²] = 2`. This file decides for which positive areas these data are w⁺-monotone
(`TauCeti.Floer.IsWPlusMonotone`), the strict form of the condition, which implies the weak form
under which Lee constructs the Floer–Novikov torsion. It works with the class group `ℤ^ι` and
these two homomorphisms directly; the homology of the product is not computed here. The
homomorphisms are defined for every `a : ι → ℝ`, but only positive `a` are the data of a product
symplectic form: a factor of negative area would carry the conjugate complex structure and first
Chern number `-2`. Statements without a positivity hypothesis are about the pair
`(area a, chern)` as abstract period data.

* In dimension at most `6`, that is `n ≤ 3`, they always are, because every first Chern number is
  even (`TauCeti.Floer.WPlusMonotoneExample.isWPlusMonotone_of_le_three`).
* With all areas equal to `τ > 0` the data are positively monotone, `ω = (τ / 2) c₁`
  (`TauCeti.Floer.WPlusMonotoneExample.area_const_eq_mul_chern`), hence w⁺-monotone in every
  dimension (`TauCeti.Floer.WPlusMonotoneExample.isWPlusMonotone_const`).
* From dimension `8` on, that is `n ≥ 4`, nothing else is: for positive areas the data are
  w⁺-monotone exactly when all the areas are equal
  (`TauCeti.Floer.WPlusMonotoneExample.isWPlusMonotone_iff_forall_eq`). Two factors of areas
  `a i < a j` give the classes `(N + 1) Aᵢ - N Aⱼ`, of first Chern number `2` and area
  `a i - N (a j - a i)`, which is negative for large `N`
  (`TauCeti.Floer.WPlusMonotoneExample.not_isWPlusMonotone_of_lt`).

For `(S²)⁴` with areas `1, 3, 1, 1` the class `A₁ - A₂ + A₃` has first Chern number
`2 - 2 + 2 = 2 = n - 2` and area `1 - 3 + 1 = -1`
(`TauCeti.Floer.WPlusMonotoneExample.chern_one_neg_one_one_zero`,
`TauCeti.Floer.WPlusMonotoneExample.area_one_three_one_one`), so this form is not w⁺-monotone
(`TauCeti.Floer.WPlusMonotoneExample.not_isWPlusMonotone_one_three_one_one`). So for products of
two-spheres, w⁺-monotonicity is a genuine restriction in dimension `8`, unlike in dimensions `2`,
`4` and `6`.

## References

* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, J. Symplectic Geom. 3 (2005), 221–311, arXiv:math/0111313, the w⁺-monotonicity
  assumption.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, §6.4 (monotonicity and semipositivity).
-/

public section

noncomputable section

namespace TauCeti.Floer.WPlusMonotoneExample

variable {ι : Type*} [Fintype ι]

/-- The area `∑ i, a i * A i` of the spherical class `A ∈ ℤ^ι` of a product of two-spheres whose
`i`-th factor has area `a i`. Together with `chern` these are the spherical data of a product
symplectic form when every `a i` is positive. -/
def area (a : ι → ℝ) : (ι → ℤ) →+ ℝ where
  toFun A := ∑ i, a i * A i
  map_zero' := by simp
  map_add' A B := by simp [mul_add, Finset.sum_add_distrib]

@[simp]
theorem area_apply (a : ι → ℝ) (A : ι → ℤ) : area a A = ∑ i, a i * A i :=
  (rfl)

/-- The first Chern number `2 ∑ i, A i` of the spherical class `A ∈ ℤ^ι` of a product of
two-spheres with positive areas: each factor contributes `c₁(TS²)[S²] = 2`. -/
def chern : (ι → ℤ) →+ ℤ where
  toFun A := 2 * ∑ i, A i
  map_zero' := by simp
  map_add' A B := by simp [mul_add, Finset.sum_add_distrib]

@[simp]
theorem chern_apply (A : ι → ℤ) : chern A = 2 * ∑ i, A i :=
  (rfl)

/-- The class of the `i`-th factor, counted `x` times, has area `x` times the area of the
factor. -/
theorem area_single [DecidableEq ι] (a : ι → ℝ) (i : ι) (x : ℤ) :
    area a (Pi.single i x) = a i * x := by
  simp [Pi.single_apply]

/-- The class of the `i`-th factor, counted `x` times, has first Chern number `2 x`. -/
theorem chern_single [DecidableEq ι] (i : ι) (x : ℤ) : chern (Pi.single i x : ι → ℤ) = 2 * x := by
  simp

/-- Every first Chern number of a product of two-spheres is even. -/
theorem even_chern (A : ι → ℤ) : Even (chern A) :=
  ⟨∑ i, A i, by rw [chern_apply]; ring⟩

/-- **A product of two-spheres is w⁺-monotone in dimension at most `6`**: its first Chern numbers
are even, and no even integer lies in `(0, n - 2]` for `n ≤ 3`. As abstract data this needs no
positivity of the areas `a`. -/
theorem isWPlusMonotone_of_le_three (a : ι → ℝ) {n : ℕ} (hn : n ≤ 3) :
    IsWPlusMonotone (area a) chern n :=
  isWPlusMonotone_of_even_of_le_three even_chern hn

/-- **Equal areas make the area proportional to the first Chern number**: if every factor has area
`τ`, the area of a class is `τ / 2` times its first Chern number. For `τ > 0` the data are
positively monotone. -/
theorem area_const_eq_mul_chern (τ : ℝ) (A : ι → ℤ) :
    area (fun _ ↦ τ) A = τ / 2 * chern A := by
  simp only [area_apply, chern_apply]
  push_cast
  rw [← Finset.mul_sum]
  ring

/-- **A product of two-spheres of equal positive areas is w⁺-monotone** in every dimension, being
positively monotone. -/
theorem isWPlusMonotone_const {τ : ℝ} (hτ : 0 < τ) (n : ℕ) :
    IsWPlusMonotone (area fun _ : ι ↦ τ) chern n :=
  isWPlusMonotone_of_area_eq_mul_chern (area_const_eq_mul_chern τ) (half_pos hτ)

/-- **Two factors of different areas break w⁺-monotonicity** from dimension `8` on: if
`a i < a j`, then for large `N` the class `(N + 1) Aᵢ - N Aⱼ` has first Chern number `2 ≤ n - 2`
and negative area `a i - N (a j - a i)`. As abstract data this needs no positivity of the areas
`a`. -/
theorem not_isWPlusMonotone_of_lt {a : ι → ℝ} {n : ℕ} (hn : 4 ≤ n) {i j : ι} (hij : a i < a j) :
    ¬ IsWPlusMonotone (area a) chern n := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (a i / (a j - a i))
  have hN' : a i < N * (a j - a i) := (div_lt_iff₀ (sub_pos.2 hij)).1 hN
  rw [not_isWPlusMonotone_iff]
  refine ⟨Pi.single i ((N : ℤ) + 1) - Pi.single j (N : ℤ), ?_, ?_, ?_⟩
  · simp
  · simp only [map_sub, chern_single]
    omega
  · simp only [map_sub, area_single]
    push_cast
    linarith

/-- **w⁺-monotonicity of a product of two-spheres from dimension `8` on**: for `n ≥ 4` and
positive areas the data are w⁺-monotone exactly when all the areas are equal. -/
theorem isWPlusMonotone_iff_forall_eq {a : ι → ℝ} (ha : ∀ i, 0 < a i) {n : ℕ} (hn : 4 ≤ n) :
    IsWPlusMonotone (area a) chern n ↔ ∀ i j, a i = a j := by
  refine ⟨fun h i j ↦ ?_, fun h ↦ ?_⟩
  · rcases lt_trichotomy (a i) (a j) with hlt | heq | hgt
    · exact absurd h (not_isWPlusMonotone_of_lt hn hlt)
    · exact heq
    · exact absurd h (not_isWPlusMonotone_of_lt hn hgt)
  · cases isEmpty_or_nonempty ι with
    | inl _ =>
      rw [show a = fun _ ↦ 1 from funext isEmptyElim]
      exact isWPlusMonotone_const one_pos n
    | inr hι =>
      obtain ⟨i₀⟩ := hι
      rw [show a = fun _ ↦ a i₀ from funext fun i ↦ h i i₀]
      exact isWPlusMonotone_const (ha i₀) n

/-! ### The product `(S²)⁴` with areas `1, 3, 1, 1` -/

/-- On `(S²)⁴`, the class `A₁ - A₂ + A₃` has first Chern number `2`. -/
theorem chern_one_neg_one_one_zero : chern ![(1 : ℤ), -1, 1, 0] = 2 := by
  simp [Fin.sum_univ_four]

/-- On `(S²)⁴` with areas `1, 3, 1, 1`, the class `A₁ - A₂ + A₃` has area `-1`. -/
theorem area_one_three_one_one : area ![(1 : ℝ), 3, 1, 1] ![1, -1, 1, 0] = -1 := by
  simp [Fin.sum_univ_four]
  norm_num

/-- **`(S²)⁴` with areas `1, 3, 1, 1` is not w⁺-monotone**: the class `A₁ - A₂ + A₃` has first
Chern number `2 = n - 2` and area `-1`. -/
theorem not_isWPlusMonotone_one_three_one_one :
    ¬ IsWPlusMonotone (area ![(1 : ℝ), 3, 1, 1]) chern 4 := by
  rw [not_isWPlusMonotone_iff]
  refine ⟨![1, -1, 1, 0], ?_, ?_, ?_⟩ <;>
    simp only [chern_one_neg_one_one_zero, area_one_three_one_one] <;> norm_num

end TauCeti.Floer.WPlusMonotoneExample
