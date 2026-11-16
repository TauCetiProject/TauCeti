/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SU2.BinaryTetrahedral
import Mathlib.GroupTheory.IndexNormal
import TauCeti.Algebra.Quaternion.Basic

/-!
# The binary octahedral subgroup of SU(2)

In unit-quaternion coordinates the **binary octahedral group** of order `48` is obtained from the
`24`-element binary tetrahedral group by adjoining the `24` unit quaternions with exactly two
nonzero coordinates, both `±1 / √2`:

* the `24` Hurwitz units `(±1, 0, 0, 0)` (and coordinate permutations) and `(±1 ± i ± j ± k) / 2`
  of `TauCeti.SU2.binaryTetrahedralSubgroup`, and
* the `24` points `(w₀ + w₁ i + w₂ j + w₃ k) / √2` where two of `w₀, w₁, w₂, w₃` are `±1` and two
  are `0`.

This file records the `24` adjoined `√2`-scaled coordinate vectors as the finite set
`TauCeti.SU2.binaryOctahedralSqrtTwoCoords` of integer vectors `w : Fin 4 → ℤ` with two nonzero
entries in `{-1, 1}`, equivalently the integer solutions of `w₀² + w₁² + w₂² + w₃² = 2`
(`TauCeti.SU2.mem_binaryOctahedralSqrtTwoCoords_iff`), and constructs the binary octahedral
subgroup `TauCeti.SU2.binaryOctahedralSubgroup` of the native matrix group `SU(2)` through
`Quaternion.toComplexMatrix`.

Closure under multiplication reflects a `ℤ / 2`-grading over the binary tetrahedral group:

* the product of two `ℤ / √2` quaternions has coordinates in `ℤ / 2`, hence lies in
  `TauCeti.SU2.binaryTetrahedralSubgroup`;
* for `v` in `TauCeti.SU2.binaryTetrahedralCoords` and `w` in
  `TauCeti.SU2.binaryOctahedralSqrtTwoCoords`, the four coordinates of `v` share a parity while
  `w₀ + w₁ + w₂ + w₃` is even, so the integer quaternion product `v * w` (and `w * v`) has all even
  coordinates; halving gives a `ℤ / √2` unit quaternion.

No `ℤ / √2` unit quaternion can have half-integer coordinates because `2` is not a square in `ℤ`,
so the two sets of `24` points are disjoint (`TauCeti.SU2.binaryOctahedralCoordsEquiv`) and the
subgroup has order `48` (`TauCeti.SU2.natCard_binaryOctahedralSubgroup`). Consequently
`TauCeti.SU2.binaryTetrahedralSubgroup` has index two in `TauCeti.SU2.binaryOctahedralSubgroup`,
hence is normal, and the nontrivial coset is `r · 2T` for the eighth-turn generator
`r = (1 + i) / √2 = TauCeti.SU2.binaryDihedralRotation 4`.

The coordinate and presentation generators are matched directly:

* `r = TauCeti.SU2.binaryDihedralRotation 4 = (1 + i) / √2` and `s = j = weylElement⁻¹` generate
  `TauCeti.SU2.binaryDihedralSubgroup 4` of order `16` inside the binary octahedral group, and
  together with `ω = (-1 + i + j + k) / 2` (or `r` and `ω` alone, since `(ω r)² = -j`) generate the
  whole group;
* the edge, face and vertex generators `a = (i + j) / √2`, `b = (1 + i + j + k) / 2` and
  `c = (1 + i) / √2` satisfy the binary polyhedral relations `a² = b³ = c⁴ = a b c = -1` and
  generate the subgroup.

Every element satisfies `g ^ 8 = 1 ∨ g ^ 6 = 1`, so all element orders are at most `8` while the
group exponent is `24`. This separates the binary octahedral group from the other two isomorphism
classes of finite subgroups of `SU(2)` and `SL₂(ℂ)` of order `48`: it is neither cyclic nor
isomorphic to `QuaternionGroup 12` (which has an element of order `24`).

## Main definitions

* `TauCeti.SU2.binaryOctahedralSqrtTwoCoords`: the `24` `√2`-scaled coordinate vectors with two
  entries `±1` and two entries `0`.
* `TauCeti.SU2.binaryOctahedralSubgroup`: the binary octahedral subgroup of `SU(2)`.
* `TauCeti.SU2.binaryOctahedralCoordsEquiv`: its `48`-point coordinate parametrization
  `binaryTetrahedralCoords ⊕ binaryOctahedralSqrtTwoCoords ≃ binaryOctahedralSubgroup`.
* `TauCeti.SU2.binaryOctahedralEdgeGen`, `TauCeti.SU2.binaryOctahedralFaceGen`: the `<2, 3, 4>`
  presentation generators `(i + j) / √2` and `(1 + i + j + k) / 2`.

## Main results

* `TauCeti.SU2.mem_binaryOctahedralSubgroup_iff_two_nonzero_coords` and
  `TauCeti.SU2.mem_binaryOctahedralSubgroup_iff_exists_int`: geometric and arithmetic membership
  criteria.
* `TauCeti.SU2.natCard_binaryOctahedralSubgroup`: the subgroup has order `48`.
* `TauCeti.SU2.relIndex_binaryTetrahedralSubgroup_binaryOctahedralSubgroup` and normality of
  `binaryTetrahedralSubgroup` as an index-two subgroup, with coset decomposition by
  `binaryDihedralRotation 4`.
* `TauCeti.SU2.binaryOctahedralSubgroup_eq_closure`,
  `TauCeti.SU2.binaryOctahedralSubgroup_eq_closure_pair`, and
  `TauCeti.SU2.binaryOctahedralSubgroup_eq_closure_polyhedral`: generation by presentation
  generators and the `<2, 3, 4>` relations `a² = b³ = c⁴ = a b c = -1`.
* `TauCeti.SU2.not_isCyclic_binaryOctahedralSubgroup` and
  `TauCeti.SU2.isEmpty_binaryOctahedralSubgroup_mulEquiv_quaternionGroup`: non-cyclicity and
  non-isomorphism with `QuaternionGroup 12`.

## References

* J. H. Conway and D. A. Smith, *On Quaternions and Octonions*, A K Peters, 2003, Chapter 3 and
  §6.5.
-/

public section

namespace TauCeti.SU2

open Quaternion
open scoped Real

/-! ### The 24 `√2`-scaled coordinate vectors -/

/-- The `√2`-scaled coordinate vectors `√2 q = (w₀, w₁, w₂, w₃)` of the `24` points `q` adjoined to
the binary tetrahedral group: the vectors in `{-1, 0, 1}⁴` with exactly two nonzero coordinates, so
that both nonzero coordinates of `q` are `±1 / √2`. -/
def binaryOctahedralSqrtTwoCoords : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ => ({-1, 0, 1} : Finset ℤ)).filter fun w =>
    (Finset.univ.filter fun i => w i ≠ 0).card = 2

/-- **The 24 `√2`-scaled coordinate vectors are distinct.** -/
@[simp]
theorem card_binaryOctahedralSqrtTwoCoords : binaryOctahedralSqrtTwoCoords.card = 24 := by
  decide

/-- A vector lies in `binaryOctahedralSqrtTwoCoords` precisely when it has two nonzero coordinates
and every nonzero coordinate is `±1`. -/
theorem mem_binaryOctahedralSqrtTwoCoords_iff_card_ne_zero {w : Fin 4 → ℤ} :
    w ∈ binaryOctahedralSqrtTwoCoords ↔
      (∀ i, w i ≠ 0 → w i = 1 ∨ w i = -1) ∧
        (Finset.univ.filter fun i => w i ≠ 0).card = 2 := by
  simp only [binaryOctahedralSqrtTwoCoords, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_insert, Finset.mem_singleton]
  refine and_congr_left' ⟨fun h i hi => ?_, fun h i => ?_⟩
  · rcases h i with h0 | h0 | h0
    · exact .inr h0
    · exact absurd h0 hi
    · exact .inl h0
  · by_cases hi : w i = 0
    · exact .inr (.inl hi)
    · rcases h i hi with h1 | h1
      · exact .inr (.inr h1)
      · exact .inl h1

/-- **The `√2`-scaled coordinate vectors are the integer solutions of `w₀² + w₁² + w₂² + w₃² = 2`.**
-/
theorem mem_binaryOctahedralSqrtTwoCoords_iff {w : Fin 4 → ℤ} :
    w ∈ binaryOctahedralSqrtTwoCoords ↔ ∑ i, w i ^ 2 = 2 := by
  refine ⟨fun hw => (by decide : ∀ w ∈ binaryOctahedralSqrtTwoCoords, ∑ i, w i ^ 2 = 2) w hw,
    fun hw => ?_⟩
  have hb (i : Fin 4) : w i ∈ Finset.Icc (-1 : ℤ) 1 := by
    have hle : w i ^ 2 ≤ 2 := hw ▸
      Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
    have habs : |w i| < 2 := by nlinarith [sq_abs (w i), abs_nonneg (w i)]
    obtain ⟨h1, h2⟩ := abs_lt.mp habs
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have key : ∀ a ∈ Finset.Icc (-1 : ℤ) 1, ∀ b ∈ Finset.Icc (-1 : ℤ) 1,
      ∀ c ∈ Finset.Icc (-1 : ℤ) 1, ∀ d ∈ Finset.Icc (-1 : ℤ) 1,
        a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 2 → ![a, b, c, d] ∈ binaryOctahedralSqrtTwoCoords := by
    decide
  have hw' := key _ (hb 0) _ (hb 1) _ (hb 2) _ (hb 3) (by simpa [Fin.sum_univ_four] using hw)
  convert hw' using 1
  ext i
  fin_cases i <;> simp

/-- Every `√2`-scaled coordinate vector has even coordinate sum. -/
private theorem even_sum_of_mem_binaryOctahedralSqrtTwoCoords {w : Fin 4 → ℤ}
    (hw : w ∈ binaryOctahedralSqrtTwoCoords) : Even (w 0 + w 1 + w 2 + w 3) :=
  (by decide : ∀ w ∈ binaryOctahedralSqrtTwoCoords, Even (w 0 + w 1 + w 2 + w 3)) w hw

/-! ### Arithmetic of `ℤ / √2` unit quaternions -/

/-- An element of `SU(2)` with quaternion coordinates in `ℤ / √2` has `√2`-scaled coordinates in
`binaryOctahedralSqrtTwoCoords`, since its determinant is one. -/
private theorem mem_binaryOctahedralSqrtTwoCoords_of_coe_eq {g : SU2} {w : Fin 4 → ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) =
      toComplexMatrix ⟨w 0 / √2, w 1 / √2, w 2 / √2, w 3 / √2⟩) :
    w ∈ binaryOctahedralSqrtTwoCoords := by
  have hdet := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
  rw [hg, det_toComplexMatrix, normSq_mk_div, Real.sq_sqrt zero_le_two, ← Complex.ofReal_one,
    Complex.ofReal_inj, div_eq_one_iff_eq two_ne_zero] at hdet
  rw [mem_binaryOctahedralSqrtTwoCoords_iff, Fin.sum_univ_four]
  exact_mod_cast hdet

/-- Every vector in `binaryOctahedralSqrtTwoCoords` gives a unit quaternion, hence a matrix in
`SU(2)`. -/
private theorem toComplexMatrix_mem_of_mem_binaryOctahedralSqrtTwoCoords {w : Fin 4 → ℤ}
    (hw : w ∈ binaryOctahedralSqrtTwoCoords) :
    toComplexMatrix ⟨w 0 / √2, w 1 / √2, w 2 / √2, w 3 / √2⟩ ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine mem_specialUnitaryGroup_toComplexMatrix ((mem_unitary_iff_normSq_eq_one _).mpr ?_)
  have hw := mem_binaryOctahedralSqrtTwoCoords_iff.mp hw
  rw [Fin.sum_univ_four] at hw
  rw [normSq_mk_div, Real.sq_sqrt zero_le_two, div_eq_one_iff_eq two_ne_zero]
  exact_mod_cast hw

/-- No quaternion with half-integer coordinates equals a `√2`-scaled coordinate quaternion: a
nonzero entry `±1 / √2` would force `vᵢ² = 2` in `ℤ`. -/
private theorem toComplexMatrix_half_ne_div_sqrt_two (v : Fin 4 → ℤ) {w : Fin 4 → ℤ}
    (hw : w ∈ binaryOctahedralSqrtTwoCoords) :
    toComplexMatrix ⟨v 0 / 2, v 1 / 2, v 2 / 2, v 3 / 2⟩ ≠
      toComplexMatrix ⟨w 0 / √2, w 1 / √2, w 2 / √2, w 3 / √2⟩ := by
  intro h
  have hq := toComplexMatrix_injective h
  simp only [QuaternionAlgebra.mk.injEq] at hq
  obtain ⟨h0, h1, h2, h3⟩ := hq
  -- Look at a nonzero coordinate of `w`: `(v i / 2)² = (±1 / √2)² = 1 / 2` gives `(v i)² = 2`.
  obtain ⟨i, hi⟩ :=
    (by decide : ∀ w ∈ binaryOctahedralSqrtTwoCoords, ∃ i : Fin 4, w i ^ 2 = 1) w hw
  have hvi_real : ((v i : ℝ) / 2) ^ 2 = ((w i : ℝ) / √2) ^ 2 := by
    fin_cases i <;> simp [h0, h1, h2, h3]
  have hvi_sq : (v i : ℝ) ^ 2 = 2 := by
    have hwi : (w i : ℝ) ^ 2 = 1 := by exact_mod_cast hi
    simp only [div_pow, Real.sq_sqrt zero_le_two, hwi] at hvi_real
    linarith
  have hvi_int : v i ^ 2 = 2 := by exact_mod_cast hvi_sq
  have hbounds : v i ≤ -2 ∨ v i = -1 ∨ v i = 0 ∨ v i = 1 ∨ 2 ≤ v i := by omega
  rcases hbounds with hb | hb | hb | hb | hb <;> nlinarith

/-- The product of two `ℤ / √2` quaternions has half-integer coordinates. -/
private theorem exists_div_sqrt_two_mul_eq_half (w₁ w₂ : Fin 4 → ℤ) :
    ∃ u : Fin 4 → ℤ,
      (⟨w₁ 0 / √2, w₁ 1 / √2, w₁ 2 / √2, w₁ 3 / √2⟩ : ℍ[ℝ]) *
        ⟨w₂ 0 / √2, w₂ 1 / √2, w₂ 2 / √2, w₂ 3 / √2⟩ =
      ⟨u 0 / 2, u 1 / 2, u 2 / 2, u 3 / 2⟩ := by
  have hinv : (√2 : ℝ)⁻¹ * (√2)⁻¹ = 2⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt zero_le_two]
  refine ⟨![w₁ 0 * w₂ 0 - w₁ 1 * w₂ 1 - w₁ 2 * w₂ 2 - w₁ 3 * w₂ 3,
      w₁ 0 * w₂ 1 + w₁ 1 * w₂ 0 + w₁ 2 * w₂ 3 - w₁ 3 * w₂ 2,
      w₁ 0 * w₂ 2 - w₁ 1 * w₂ 3 + w₁ 2 * w₂ 0 + w₁ 3 * w₂ 1,
      w₁ 0 * w₂ 3 + w₁ 1 * w₂ 2 - w₁ 2 * w₂ 1 + w₁ 3 * w₂ 0], ?_⟩
  ext <;> simp only [re_mul, imI_mul, imJ_mul, imK_mul, Matrix.cons_val, Int.cast_add,
    Int.cast_sub, Int.cast_mul, div_eq_mul_inv]
  · linear_combination ((w₁ 0 : ℝ) * w₂ 0 - w₁ 1 * w₂ 1 - w₁ 2 * w₂ 2 - w₁ 3 * w₂ 3) * hinv
  · linear_combination ((w₁ 0 : ℝ) * w₂ 1 + w₁ 1 * w₂ 0 + w₁ 2 * w₂ 3 - w₁ 3 * w₂ 2) * hinv
  · linear_combination ((w₁ 0 : ℝ) * w₂ 2 - w₁ 1 * w₂ 3 + w₁ 2 * w₂ 0 + w₁ 3 * w₂ 1) * hinv
  · linear_combination ((w₁ 0 : ℝ) * w₂ 3 + w₁ 1 * w₂ 2 - w₁ 2 * w₂ 1 + w₁ 3 * w₂ 0) * hinv

/-- The product of a binary tetrahedral quaternion and a `√2`-scaled coordinate quaternion lies in
`ℤ / √2`. -/
private theorem exists_half_mul_div_sqrt_two {v w : Fin 4 → ℤ}
    (hv : v ∈ binaryTetrahedralCoords) (hw : w ∈ binaryOctahedralSqrtTwoCoords) :
    ∃ u : Fin 4 → ℤ,
      (⟨v 0 / 2, v 1 / 2, v 2 / 2, v 3 / 2⟩ : ℍ[ℝ]) *
        ⟨w 0 / √2, w 1 / √2, w 2 / √2, w 3 / √2⟩ =
      ⟨u 0 / √2, u 1 / √2, u 2 / √2, u 3 / √2⟩ := by
  set x : ℍ[ℤ] := ⟨v 0, v 1, v 2, v 3⟩ * ⟨w 0, w 1, w 2, w 3⟩ with hx
  have hpv := even_iff_even_of_mem_binaryTetrahedralCoords hv
  have hpw := even_sum_of_mem_binaryOctahedralSqrtTwoCoords hw
  have heven : Even x.re ∧ Even x.imI ∧ Even x.imJ ∧ Even x.imK := by
    by_cases hv0 : Even (v 0)
    · simp [hx, Int.even_add, Int.even_sub, hpv 1, hpv 2, hpv 3, hv0]
    · simp only [Int.even_add] at hpw
      by_cases hw0 : Even (w 0) <;> by_cases hw1 : Even (w 1) <;> by_cases hw2 : Even (w 2) <;>
        simp only [hw0, hw1, hw2, iff_true, true_iff, iff_false, false_iff,
          not_true_eq_false] at hpw <;>
        simp [hx, Int.even_add, Int.even_sub, Int.even_mul, hpv 1, hpv 2, hpv 3,
          hv0, hw0, hw1, hw2, hpw]
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩ := heven
  simp only [hx, re_mul, imI_mul, imJ_mul, imK_mul] at ha hb hc hd
  rify at ha hb hc hd
  refine ⟨![a, b, c, d], ?_⟩
  ext <;> simp only [re_mul, imI_mul, imJ_mul, imK_mul, Matrix.cons_val, div_eq_mul_inv]
  · linear_combination (2⁻¹ * (√2)⁻¹) * ha
  · linear_combination (2⁻¹ * (√2)⁻¹) * hb
  · linear_combination (2⁻¹ * (√2)⁻¹) * hc
  · linear_combination (2⁻¹ * (√2)⁻¹) * hd

/-- The product of a `√2`-scaled coordinate quaternion and a binary tetrahedral quaternion lies in
`ℤ / √2`. -/
private theorem exists_div_sqrt_two_mul_half {w v : Fin 4 → ℤ}
    (hw : w ∈ binaryOctahedralSqrtTwoCoords) (hv : v ∈ binaryTetrahedralCoords) :
    ∃ u : Fin 4 → ℤ,
      (⟨w 0 / √2, w 1 / √2, w 2 / √2, w 3 / √2⟩ : ℍ[ℝ]) *
        ⟨v 0 / 2, v 1 / 2, v 2 / 2, v 3 / 2⟩ =
      ⟨u 0 / √2, u 1 / √2, u 2 / √2, u 3 / √2⟩ := by
  have hv' : ![v 0, -v 1, -v 2, -v 3] ∈ binaryTetrahedralCoords := by
    rw [mem_binaryTetrahedralCoords_iff, Fin.sum_univ_four] at hv ⊢
    simpa using hv
  have hw' : ![w 0, -w 1, -w 2, -w 3] ∈ binaryOctahedralSqrtTwoCoords := by
    rw [mem_binaryOctahedralSqrtTwoCoords_iff, Fin.sum_univ_four] at hw ⊢
    simpa using hw
  obtain ⟨u, hu⟩ := exists_half_mul_div_sqrt_two hv' hw'
  refine ⟨![u 0, -u 1, -u 2, -u 3], ?_⟩
  have hstar := congrArg star hu
  rw [star_mul] at hstar
  simpa [QuaternionAlgebra.ext_iff, neg_div] using hstar

/-! ### The binary octahedral subgroup -/

/-- **The binary octahedral subgroup of `SU(2)`**: the `48` matrices obtained by adjoining to the
`24`-element binary tetrahedral subgroup the `24` unit quaternions with two nonzero coordinates,
both `±1 / √2`. -/
noncomputable def binaryOctahedralSubgroup : Subgroup SU2 where
  carrier := {g | g ∈ binaryTetrahedralSubgroup ∨ ∃ w ∈ binaryOctahedralSqrtTwoCoords,
    (g : Matrix (Fin 2) (Fin 2) ℂ) = toComplexMatrix ⟨w 0 / √2, w 1 / √2, w 2 / √2, w 3 / √2⟩}
  mul_mem' := by
    rintro g h (hg | ⟨w₁, hw₁, hg⟩) (hh | ⟨w₂, hw₂, hh⟩)
    · exact .inl (mul_mem hg hh)
    · obtain ⟨v, hv, hg⟩ := mem_binaryTetrahedralSubgroup_iff.mp hg
      obtain ⟨u, hu⟩ := exists_half_mul_div_sqrt_two hv hw₂
      have hmul : ((g * h : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
          toComplexMatrix ⟨u 0 / √2, u 1 / √2, u 2 / √2, u 3 / √2⟩ := by
        rw [Submonoid.coe_mul, hg, hh, ← map_mul, hu]
      exact .inr ⟨u, mem_binaryOctahedralSqrtTwoCoords_of_coe_eq hmul, hmul⟩
    · obtain ⟨v, hv, hh⟩ := mem_binaryTetrahedralSubgroup_iff.mp hh
      obtain ⟨u, hu⟩ := exists_div_sqrt_two_mul_half hw₁ hv
      have hmul : ((g * h : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
          toComplexMatrix ⟨u 0 / √2, u 1 / √2, u 2 / √2, u 3 / √2⟩ := by
        rw [Submonoid.coe_mul, hg, hh, ← map_mul, hu]
      exact .inr ⟨u, mem_binaryOctahedralSqrtTwoCoords_of_coe_eq hmul, hmul⟩
    · obtain ⟨u, hu⟩ := exists_div_sqrt_two_mul_eq_half w₁ w₂
      refine .inl (mem_binaryTetrahedralSubgroup_iff_exists_int.mpr ⟨u, ?_⟩)
      rw [Submonoid.coe_mul, hg, hh, ← map_mul, hu]
  one_mem' := .inl binaryTetrahedralSubgroup.one_mem
  inv_mem' := by
    rintro g (hg | ⟨w, -, hg⟩)
    · exact .inl (inv_mem hg)
    · set u : Fin 4 → ℤ := ![w 0, -w 1, -w 2, -w 3]
      have hinv : ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
          toComplexMatrix ⟨u 0 / √2, u 1 / √2, u 2 / √2, u 3 / √2⟩ := by
        rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star, hg, ← map_star]
        congr 1
        ext <;> simp [u, neg_div]
      exact .inr ⟨u, mem_binaryOctahedralSqrtTwoCoords_of_coe_eq hinv, hinv⟩

/-- Membership in the binary octahedral subgroup: either in the binary tetrahedral subgroup or one
of the `24` `√2`-scaled coordinate points. -/
theorem mem_binaryOctahedralSubgroup_iff {g : SU2} :
    g ∈ binaryOctahedralSubgroup ↔
      g ∈ binaryTetrahedralSubgroup ∨ ∃ w ∈ binaryOctahedralSqrtTwoCoords,
        (g : Matrix (Fin 2) (Fin 2) ℂ) =
          toComplexMatrix ⟨w 0 / √2, w 1 / √2, w 2 / √2, w 3 / √2⟩ :=
  Iff.rfl

/-- Coordinate membership in the binary octahedral subgroup, written directly in terms of the two
`24`-element integer coordinate sets. -/
theorem mem_binaryOctahedralSubgroup_iff_exists_coords {g : SU2} :
    g ∈ binaryOctahedralSubgroup ↔
      (∃ v ∈ binaryTetrahedralCoords,
        (g : Matrix (Fin 2) (Fin 2) ℂ) =
          toComplexMatrix ⟨v 0 / 2, v 1 / 2, v 2 / 2, v 3 / 2⟩) ∨
      (∃ w ∈ binaryOctahedralSqrtTwoCoords,
        (g : Matrix (Fin 2) (Fin 2) ℂ) =
          toComplexMatrix ⟨w 0 / √2, w 1 / √2, w 2 / √2, w 3 / √2⟩) := by
  rw [mem_binaryOctahedralSubgroup_iff, mem_binaryTetrahedralSubgroup_iff]

/-- **Arithmetic characterization of the binary octahedral subgroup**: an element of `SU(2)` lies in
it precisely when its quaternion coordinates all belong to `ℤ / 2` or all belong to `ℤ / √2`. -/
theorem mem_binaryOctahedralSubgroup_iff_exists_int {g : SU2} :
    g ∈ binaryOctahedralSubgroup ↔
      (∃ v : Fin 4 → ℤ,
        (g : Matrix (Fin 2) (Fin 2) ℂ) =
          toComplexMatrix ⟨v 0 / 2, v 1 / 2, v 2 / 2, v 3 / 2⟩) ∨
      (∃ w : Fin 4 → ℤ,
        (g : Matrix (Fin 2) (Fin 2) ℂ) =
          toComplexMatrix ⟨w 0 / √2, w 1 / √2, w 2 / √2, w 3 / √2⟩) := by
  rw [mem_binaryOctahedralSubgroup_iff, mem_binaryTetrahedralSubgroup_iff_exists_int]
  exact or_congr_right ⟨fun ⟨w, _, hg⟩ => ⟨w, hg⟩,
    fun ⟨w, hg⟩ => ⟨w, mem_binaryOctahedralSqrtTwoCoords_of_coe_eq hg, hg⟩⟩

/-- **Geometric coordinate characterization**: an element of `SU(2)` lies in the binary octahedral
subgroup precisely when it lies in the binary tetrahedral subgroup or its quaternion has exactly two
nonzero real coordinates, both equal to `±1 / √2`. -/
theorem mem_binaryOctahedralSubgroup_iff_two_nonzero_coords {g : SU2} :
    g ∈ binaryOctahedralSubgroup ↔
      g ∈ binaryTetrahedralSubgroup ∨
        ∃ c : Fin 4 → ℝ,
          (∀ i, c i ≠ 0 → c i = 1 / √2 ∨ c i = -(1 / √2)) ∧
          (Finset.univ.filter fun i => c i ≠ 0).card = 2 ∧
          (g : Matrix (Fin 2) (Fin 2) ℂ) = toComplexMatrix ⟨c 0, c 1, c 2, c 3⟩ := by
  have hsqrt_ne : (√2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr zero_lt_two
  rw [mem_binaryOctahedralSubgroup_iff]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨w, hw, hg⟩
    obtain ⟨hsign, hcard⟩ := mem_binaryOctahedralSqrtTwoCoords_iff_card_ne_zero.mp hw
    refine ⟨fun i => w i / √2, fun i hi => ?_, ?_, hg⟩
    · have hwi : w i ≠ 0 := fun h0 => hi (by simp [h0])
      rcases hsign i hwi with h1 | h1 <;> simp [h1, neg_div]
    · convert hcard using 2
      ext i
      simp [div_eq_zero_iff, hsqrt_ne]
  · rintro ⟨c, hsign, -, hg⟩
    classical
    let w : Fin 4 → ℤ := fun i => if c i = 1 / √2 then 1 else if c i = -(1 / √2) then -1 else 0
    have hcw (i : Fin 4) : c i = w i / √2 := by
      dsimp only [w]
      split_ifs with h1 h2
      · simp [h1]
      · simp [h2, neg_div]
      · have h0 : c i = 0 := by
          by_contra hne
          exact (hsign i hne).elim h1 h2
        simp [h0]
    have hw_eq : (g : Matrix (Fin 2) (Fin 2) ℂ) =
        toComplexMatrix ⟨w 0 / √2, w 1 / √2, w 2 / √2, w 3 / √2⟩ := by
      simpa [hcw 0, hcw 1, hcw 2, hcw 3] using hg
    exact ⟨w, mem_binaryOctahedralSqrtTwoCoords_of_coe_eq hw_eq, hw_eq⟩

/-- None of the `24` `√2`-scaled unit quaternions lies in the binary tetrahedral subgroup. -/
private theorem notMem_binaryTetrahedralSubgroup_of_coe_eq_div_sqrt_two {g : SU2} {w : Fin 4 → ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) =
      toComplexMatrix ⟨w 0 / √2, w 1 / √2, w 2 / √2, w 3 / √2⟩) :
    g ∉ binaryTetrahedralSubgroup := by
  intro hmem
  obtain ⟨v, -, hv⟩ := mem_binaryTetrahedralSubgroup_iff.mp hmem
  exact toComplexMatrix_half_ne_div_sqrt_two v
    (mem_binaryOctahedralSqrtTwoCoords_of_coe_eq hg) (hv.symm.trans hg)

/-! ### Coordinate parametrization and order 48 -/

/-- The `48`-element map from the disjoint union of the `24` tetrahedral and `24` `√2`-scaled
coordinate vectors into the binary octahedral subgroup. -/
private noncomputable def binaryOctahedralCoordsFun :
    binaryTetrahedralCoords ⊕ binaryOctahedralSqrtTwoCoords → binaryOctahedralSubgroup
  | .inl v => ⟨binaryTetrahedralCoordsEquiv v, .inl (binaryTetrahedralCoordsEquiv v).2⟩
  | .inr w => ⟨⟨_, toComplexMatrix_mem_of_mem_binaryOctahedralSqrtTwoCoords w.2⟩,
      .inr ⟨w, w.2, rfl⟩⟩

private theorem binaryOctahedralCoordsFun_bijective :
    Function.Bijective binaryOctahedralCoordsFun := by
  have hsqrt_ne : (√2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr zero_lt_two
  refine ⟨?_, fun g => ?_⟩
  · rintro (v | w₁) (v' | w₂) h
    · have hv : binaryTetrahedralCoordsEquiv v = binaryTetrahedralCoordsEquiv v' :=
        Subtype.ext (congrArg (fun x : binaryOctahedralSubgroup => (x : SU2)) h)
      exact congrArg Sum.inl (binaryTetrahedralCoordsEquiv.injective hv)
    · exfalso
      have hmat := congrArg (fun x : binaryOctahedralSubgroup =>
        ((x : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) h
      dsimp only [binaryOctahedralCoordsFun] at hmat
      rw [coe_binaryTetrahedralCoordsEquiv_apply] at hmat
      exact toComplexMatrix_half_ne_div_sqrt_two v w₂.2 hmat
    · exfalso
      have hmat := (congrArg (fun x : binaryOctahedralSubgroup =>
        ((x : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) h).symm
      dsimp only [binaryOctahedralCoordsFun] at hmat
      rw [coe_binaryTetrahedralCoordsEquiv_apply] at hmat
      exact toComplexMatrix_half_ne_div_sqrt_two v' w₁.2 hmat
    · have hq := toComplexMatrix_injective (congrArg (fun x : binaryOctahedralSubgroup =>
        ((x : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) h)
      simp only [QuaternionAlgebra.mk.injEq, div_left_inj₀ hsqrt_ne, Int.cast_inj] at hq
      obtain ⟨h0, h1, h2, h3⟩ := hq
      congr 1
      ext i
      fin_cases i
      exacts [h0, h1, h2, h3]
  · rcases g.2 with hg | ⟨w, hw, hg⟩
    · refine ⟨.inl (binaryTetrahedralCoordsEquiv.symm ⟨g, hg⟩), ?_⟩
      apply Subtype.ext
      exact congrArg (fun x : binaryTetrahedralSubgroup => (x : SU2))
        (binaryTetrahedralCoordsEquiv.apply_symm_apply ⟨g, hg⟩)
    · exact ⟨.inr ⟨w, hw⟩, Subtype.ext (Subtype.ext hg.symm)⟩

/-- **The 48 coordinate vectors parametrize the binary octahedral subgroup**: the 24 doubled
tetrahedral vectors `v` give `(v₀ + v₁ i + v₂ j + v₃ k) / 2` and the 24 `√2`-scaled vectors `w`
give `(w₀ + w₁ i + w₂ j + w₃ k) / √2`. -/
noncomputable def binaryOctahedralCoordsEquiv :
    binaryTetrahedralCoords ⊕ binaryOctahedralSqrtTwoCoords ≃ binaryOctahedralSubgroup :=
  Equiv.ofBijective _ binaryOctahedralCoordsFun_bijective

@[simp]
theorem coe_binaryOctahedralCoordsEquiv_inl (v : binaryTetrahedralCoords) :
    (binaryOctahedralCoordsEquiv (.inl v) : SU2) = binaryTetrahedralCoordsEquiv v := (rfl)

@[simp]
theorem coe_binaryOctahedralCoordsEquiv_inr (w : binaryOctahedralSqrtTwoCoords) :
    ((binaryOctahedralCoordsEquiv (.inr w) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      toComplexMatrix ⟨(w : Fin 4 → ℤ) 0 / √2, (w : Fin 4 → ℤ) 1 / √2,
        (w : Fin 4 → ℤ) 2 / √2, (w : Fin 4 → ℤ) 3 / √2⟩ := (rfl)

@[simp]
theorem coe_binaryOctahedralCoordsEquiv_inr_notMem_binaryTetrahedralSubgroup
    (w : binaryOctahedralSqrtTwoCoords) :
    (binaryOctahedralCoordsEquiv (.inr w) : SU2) ∉ binaryTetrahedralSubgroup :=
  notMem_binaryTetrahedralSubgroup_of_coe_eq_div_sqrt_two (coe_binaryOctahedralCoordsEquiv_inr w)

instance : Finite binaryOctahedralSubgroup :=
  Finite.of_equiv _ binaryOctahedralCoordsEquiv

/-- **The binary octahedral subgroup has exactly 48 elements.** -/
@[simp]
theorem natCard_binaryOctahedralSubgroup : Nat.card binaryOctahedralSubgroup = 48 := by
  rw [← Nat.card_congr binaryOctahedralCoordsEquiv, Nat.card_eq_fintype_card, Fintype.card_sum,
    Fintype.card_coe, Fintype.card_coe, card_binaryTetrahedralCoords,
    card_binaryOctahedralSqrtTwoCoords]

/-! ### Contained subgroups, index-two normality and coset decomposition -/

/-- **The binary octahedral subgroup contains the binary tetrahedral subgroup.** -/
theorem binaryTetrahedralSubgroup_le_binaryOctahedralSubgroup :
    binaryTetrahedralSubgroup ≤ binaryOctahedralSubgroup :=
  fun _ => Or.inl

/-- **The binary tetrahedral subgroup has index two in the binary octahedral subgroup.** -/
@[simp]
theorem relIndex_binaryTetrahedralSubgroup_binaryOctahedralSubgroup :
    binaryTetrahedralSubgroup.relIndex binaryOctahedralSubgroup = 2 := by
  have h := binaryTetrahedralSubgroup.relIndex_mul_card binaryOctahedralSubgroup
  rw [inf_of_le_left binaryTetrahedralSubgroup_le_binaryOctahedralSubgroup,
    natCard_binaryTetrahedralSubgroup, natCard_binaryOctahedralSubgroup] at h
  omega

/-- The binary tetrahedral subgroup is normal in the binary octahedral subgroup. -/
instance : (binaryTetrahedralSubgroup.subgroupOf binaryOctahedralSubgroup).Normal :=
  Subgroup.normal_of_index_eq_two relIndex_binaryTetrahedralSubgroup_binaryOctahedralSubgroup

@[simp]
theorem binaryDihedralRotation_four_mem_binaryOctahedralSubgroup :
    binaryDihedralRotation 4 ∈ binaryOctahedralSubgroup := by
  refine .inr ⟨![1, 1, 0, 0], by decide, ?_⟩
  rw [coe_binaryDihedralRotation_four]
  congr 1
  ext <;> simp

/-- **The binary octahedral subgroup contains the binary dihedral subgroup of order 16**, generated
by `r = (1 + i) / √2` and `s = j`. -/
theorem binaryDihedralSubgroup_four_le_binaryOctahedralSubgroup :
    binaryDihedralSubgroup 4 ≤ binaryOctahedralSubgroup := by
  rw [binaryDihedralSubgroup_eq_closure, Subgroup.closure_le, Set.insert_subset_iff,
    Set.singleton_subset_iff]
  exact ⟨binaryDihedralRotation_four_mem_binaryOctahedralSubgroup,
    binaryTetrahedralSubgroup_le_binaryOctahedralSubgroup
      (binaryDihedralSubgroup_two_le_binaryTetrahedralSubgroup
        (inv_mem (weylElement_mem_binaryDihedralSubgroup 2)))⟩

/-- The binary octahedral subgroup contains the quaternion group `Q₈` of order eight. -/
theorem binaryDihedralSubgroup_two_le_binaryOctahedralSubgroup :
    binaryDihedralSubgroup 2 ≤ binaryOctahedralSubgroup :=
  binaryDihedralSubgroup_two_le_binaryTetrahedralSubgroup.trans
    binaryTetrahedralSubgroup_le_binaryOctahedralSubgroup

/-- **Coset decomposition over the binary tetrahedral subgroup**: an element of `SU(2)` lies in the
binary octahedral subgroup precisely when either it or `(binaryDihedralRotation 4)⁻¹ * g` lies in
the binary tetrahedral subgroup. -/
theorem mem_binaryOctahedralSubgroup_iff_or_inv_mul_mem_binaryTetrahedralSubgroup {g : SU2} :
    g ∈ binaryOctahedralSubgroup ↔
      g ∈ binaryTetrahedralSubgroup ∨
        (binaryDihedralRotation 4)⁻¹ * g ∈ binaryTetrahedralSubgroup := by
  refine ⟨fun hg => ?_, fun h => ?_⟩
  · rcases hg with hg | ⟨w, -, hg⟩
    · exact .inl hg
    · refine .inr ?_
      have hinv : (((binaryDihedralRotation 4)⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
          toComplexMatrix ⟨(1 : ℤ) / √2, (-1 : ℤ) / √2, (0 : ℤ) / √2, (0 : ℤ) / √2⟩ := by
        rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star,
          coe_binaryDihedralRotation_four, ← map_star]
        congr 1
        ext <;> simp [neg_div]
      obtain ⟨u, hu⟩ := exists_div_sqrt_two_mul_eq_half ![1, -1, 0, 0] w
      refine mem_binaryTetrahedralSubgroup_iff_exists_int.mpr ⟨u, ?_⟩
      rw [Submonoid.coe_mul, hinv, hg, ← map_mul]
      exact congrArg toComplexMatrix hu
  · rcases h with hg | hg
    · exact binaryTetrahedralSubgroup_le_binaryOctahedralSubgroup hg
    · have hmem := mul_mem binaryDihedralRotation_four_mem_binaryOctahedralSubgroup
        (binaryTetrahedralSubgroup_le_binaryOctahedralSubgroup hg)
      simpa using hmem

/-! ### Presentation generators and `<2, 3, 4>` relations -/

/-- **The binary octahedral subgroup is generated by `r = (1 + i) / √2`, `s = j` and
`ω = (-1 + i + j + k) / 2`**, that is, by the generators of `binaryDihedralSubgroup 4` together
with the order-three generator of `binaryTetrahedralSubgroup`. -/
theorem binaryOctahedralSubgroup_eq_closure :
    binaryOctahedralSubgroup = Subgroup.closure
      {binaryDihedralRotation 4, weylElement⁻¹, binaryTetrahedralOmega} := by
  set H := Subgroup.closure {binaryDihedralRotation 4, weylElement⁻¹, binaryTetrahedralOmega}
  have hle : H ≤ binaryOctahedralSubgroup := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    exact ⟨binaryDihedralRotation_four_mem_binaryOctahedralSubgroup,
      binaryDihedralSubgroup_two_le_binaryOctahedralSubgroup
        (inv_mem (weylElement_mem_binaryDihedralSubgroup 2)),
      binaryTetrahedralSubgroup_le_binaryOctahedralSubgroup
        binaryTetrahedralOmega_mem_binaryTetrahedralSubgroup⟩
  have : Finite H := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have h16 : 16 ∣ Nat.card H := by
    have hD : binaryDihedralSubgroup 4 ≤ H := by
      rw [binaryDihedralSubgroup_eq_closure]
      exact Subgroup.closure_mono (Set.insert_subset_insert (Set.singleton_subset_iff.mpr
        (Set.mem_insert _ _)))
    simpa using Subgroup.card_dvd_of_le hD
  have h3 : 3 ∣ Nat.card H := by
    simpa using H.orderOf_dvd_natCard (Subgroup.subset_closure (by simp) :
      binaryTetrahedralOmega ∈ H)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [natCard_binaryOctahedralSubgroup]
  exact Nat.le_of_dvd Nat.card_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h16 h3)

/-- **Two-generator presentation**: `r = (1 + i) / √2` and `ω = (-1 + i + j + k) / 2` already
generate the binary octahedral subgroup, since `(ω r)² = -j = weylElement`. -/
theorem binaryOctahedralSubgroup_eq_closure_pair :
    binaryOctahedralSubgroup =
      Subgroup.closure {binaryDihedralRotation 4, binaryTetrahedralOmega} := by
  have hsq : (binaryTetrahedralOmega * binaryDihedralRotation 4) ^ 2 = weylElement := by
    have hweyl : (weylElement : Matrix (Fin 2) (Fin 2) ℂ) = toComplexMatrix ⟨0, 0, -1, 0⟩ := by
      rw [coe_weylElement, weylMatrix_def, toComplexMatrix_apply]
      ext a b
      fin_cases a <;> fin_cases b <;> simp
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, Submonoid.coe_mul, coe_binaryTetrahedralOmega,
      coe_binaryDihedralRotation_four, ← map_mul, ← map_pow, hweyl]
    congr 1
    ext <;> simp only [sq, re_mul, imI_mul, imJ_mul, imK_mul] <;>
      (field_simp [Real.sqrt_ne_zero'.mpr zero_lt_two]; simp only [Real.sq_sqrt zero_le_two]; ring)
  rw [binaryOctahedralSubgroup_eq_closure]
  refine le_antisymm ?_ (Subgroup.closure_mono ?_)
  · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    refine ⟨Subgroup.subset_closure (by simp), ?_, Subgroup.subset_closure (by simp)⟩
    rw [← hsq]
    exact inv_mem (pow_mem (mul_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
      (Subgroup.subset_closure (Set.mem_insert _ _))) 2)
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp

/-- The `<2, 3, 4>` edge generator `a = (i + j) / √2` of the binary octahedral group, lifting a
half-turn about an octahedral edge midpoint. -/
noncomputable def binaryOctahedralEdgeGen : SU2 :=
  ⟨toComplexMatrix ⟨0, 1 / √2, 1 / √2, 0⟩,
    mem_specialUnitaryGroup_toComplexMatrix ((mem_unitary_iff_normSq_eq_one _).mpr (by
      rw [normSq_def']
      simp [Real.sq_sqrt zero_le_two]
      norm_num))⟩

/-- The `<2, 3, 4>` face generator `b = (1 + i + j + k) / 2` of the binary octahedral group, lifting
a one-third turn about an octahedral face centre. -/
noncomputable def binaryOctahedralFaceGen : SU2 :=
  ⟨toComplexMatrix ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩,
    mem_specialUnitaryGroup_toComplexMatrix
      ((mem_unitary_iff_normSq_eq_one _).mpr (by rw [normSq_def']; norm_num))⟩

/-- The matrix of the `<2, 3, 4>` edge generator is that of `(i + j) / √2`. -/
theorem coe_binaryOctahedralEdgeGen :
    (binaryOctahedralEdgeGen : Matrix (Fin 2) (Fin 2) ℂ) =
      toComplexMatrix ⟨0, 1 / √2, 1 / √2, 0⟩ := (rfl)

/-- The matrix of the `<2, 3, 4>` face generator is that of `(1 + i + j + k) / 2`. -/
theorem coe_binaryOctahedralFaceGen :
    (binaryOctahedralFaceGen : Matrix (Fin 2) (Fin 2) ℂ) =
      toComplexMatrix ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ := (rfl)

@[simp]
theorem binaryOctahedralEdgeGen_mem_binaryOctahedralSubgroup :
    binaryOctahedralEdgeGen ∈ binaryOctahedralSubgroup := by
  refine .inr ⟨![0, 1, 1, 0], by decide, ?_⟩
  rw [coe_binaryOctahedralEdgeGen]
  congr 1
  ext <;> simp

@[simp]
theorem binaryOctahedralFaceGen_mem_binaryTetrahedralSubgroup :
    binaryOctahedralFaceGen ∈ binaryTetrahedralSubgroup := by
  rw [mem_binaryTetrahedralSubgroup_iff]
  refine ⟨![1, 1, 1, 1], mem_binaryTetrahedralCoords_iff.mpr (by decide), ?_⟩
  rw [coe_binaryOctahedralFaceGen]
  congr 1
  ext <;> simp

@[simp]
theorem binaryOctahedralFaceGen_mem_binaryOctahedralSubgroup :
    binaryOctahedralFaceGen ∈ binaryOctahedralSubgroup :=
  binaryTetrahedralSubgroup_le_binaryOctahedralSubgroup
    binaryOctahedralFaceGen_mem_binaryTetrahedralSubgroup

/-- The square of `b = (1 + i + j + k) / 2` is `ω = (-1 + i + j + k) / 2`. -/
theorem binaryOctahedralFaceGen_sq : binaryOctahedralFaceGen ^ 2 = binaryTetrahedralOmega := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, coe_binaryOctahedralFaceGen, coe_binaryTetrahedralOmega, ← map_pow]
  congr 1
  ext <;> norm_num [sq]

/-- The product of the `<2, 3, 4>` face generator `b = (1 + i + j + k) / 2` and vertex generator
`c = (1 + i) / √2` is the edge generator `a = (i + j) / √2`. -/
theorem binaryOctahedralFaceGen_mul_binaryDihedralRotation_four :
    binaryOctahedralFaceGen * binaryDihedralRotation 4 = binaryOctahedralEdgeGen := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, coe_binaryOctahedralFaceGen, coe_binaryDihedralRotation_four,
    coe_binaryOctahedralEdgeGen, ← map_mul]
  congr 1
  ext <;> simp only [re_mul, imI_mul, imJ_mul, imK_mul, div_eq_mul_inv] <;> ring

/-- In the `<2, 3, 4>` presentation, `a² = -1`. -/
theorem binaryOctahedralEdgeGen_sq : binaryOctahedralEdgeGen ^ 2 = torusHom (-1) := by
  rw [← weylElement_inv_sq_eq_torusHom_neg_one]
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, coe_binaryOctahedralEdgeGen, coe_weylElement_inv_sq,
    ← map_pow, ← map_one toComplexMatrix, ← map_neg]
  congr 1
  ext <;> simp only [sq, re_mul, imI_mul, imJ_mul, imK_mul, re_neg, imI_neg, imJ_neg, imK_neg,
    re_one, imI_one, imJ_one, imK_one] <;>
    (field_simp [Real.sqrt_ne_zero'.mpr zero_lt_two]; (repeat rw [Real.sq_sqrt zero_le_two]); ring)

/-- In the `<2, 3, 4>` presentation, `b³ = -1`. -/
theorem binaryOctahedralFaceGen_pow_three : binaryOctahedralFaceGen ^ 3 = torusHom (-1) := by
  rw [← weylElement_inv_sq_eq_torusHom_neg_one]
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, coe_binaryOctahedralFaceGen, coe_weylElement_inv_sq,
    ← map_pow, ← map_one toComplexMatrix, ← map_neg]
  congr 1
  ext <;> norm_num [pow_succ]

/-- The `<2, 3, 4>` edge generator `a = (i + j) / √2` has order four. -/
@[simp]
theorem orderOf_binaryOctahedralEdgeGen : orderOf binaryOctahedralEdgeGen = 4 := by
  have hpow4 : binaryOctahedralEdgeGen ^ 4 = 1 := by
    calc binaryOctahedralEdgeGen ^ 4 = (binaryOctahedralEdgeGen ^ 2) ^ 2 := by rw [← pow_mul]
      _ = torusHom (-1) ^ 2 := by rw [binaryOctahedralEdgeGen_sq]
      _ = torusHom ((-1) ^ 2) := by rw [← map_pow]
      _ = 1 := by rw [neg_one_sq, map_one]
  have hdvd4 : orderOf binaryOctahedralEdgeGen ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hpow4
  have hne2 : ¬ orderOf binaryOctahedralEdgeGen ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, binaryOctahedralEdgeGen_sq]
    intro h
    have hc := congrArg Subtype.val (torusHom_injective (h.trans torusHom.map_one.symm))
    simp only [Circle.coe_neg, Circle.coe_one] at hc
    norm_num at hc
  have hle4 : orderOf binaryOctahedralEdgeGen ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd4
  have hpos : 0 < orderOf binaryOctahedralEdgeGen :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by norm_num, hpow4⟩)
  interval_cases orderOf binaryOctahedralEdgeGen <;>
    first | rfl | exact absurd hdvd4 (by decide) | exact absurd (by decide) hne2

/-- The `<2, 3, 4>` face generator `b = (1 + i + j + k) / 2` has order six. -/
@[simp]
theorem orderOf_binaryOctahedralFaceGen : orderOf binaryOctahedralFaceGen = 6 := by
  have hpow6 : binaryOctahedralFaceGen ^ 6 = 1 := by
    calc binaryOctahedralFaceGen ^ 6 = (binaryOctahedralFaceGen ^ 2) ^ 3 := by rw [← pow_mul]
      _ = binaryTetrahedralOmega ^ 3 := by rw [binaryOctahedralFaceGen_sq]
      _ = 1 := binaryTetrahedralOmega_pow_three
  have hdvd6 : orderOf binaryOctahedralFaceGen ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr hpow6
  have hne2 : ¬ orderOf binaryOctahedralFaceGen ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, binaryOctahedralFaceGen_sq]
    intro h
    have hord := orderOf_binaryTetrahedralOmega
    rw [h, orderOf_one] at hord
    omega
  have hne3 : ¬ orderOf binaryOctahedralFaceGen ∣ 3 := by
    rw [orderOf_dvd_iff_pow_eq_one, binaryOctahedralFaceGen_pow_three]
    intro h
    have hc := congrArg Subtype.val (torusHom_injective (h.trans torusHom.map_one.symm))
    simp only [Circle.coe_neg, Circle.coe_one] at hc
    norm_num at hc
  have hle6 : orderOf binaryOctahedralFaceGen ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
  have hpos : 0 < orderOf binaryOctahedralFaceGen :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by norm_num, hpow6⟩)
  interval_cases orderOf binaryOctahedralFaceGen <;>
    first | rfl | exact absurd hdvd6 (by decide) | exact absurd (by decide) hne2 |
      exact absurd (by decide) hne3

/-- **The `<2, 3, 4>` product relation**: `a b c = -1`, where `c = binaryDihedralRotation 4`
satisfies `c⁴ = -1` (`TauCeti.SU2.binaryDihedralRotation_pow_self`). -/
theorem binaryOctahedralEdgeGen_mul_faceGen_mul_rotation :
    binaryOctahedralEdgeGen * binaryOctahedralFaceGen * binaryDihedralRotation 4 =
      torusHom (-1) := by
  rw [mul_assoc, binaryOctahedralFaceGen_mul_binaryDihedralRotation_four, ← sq,
    binaryOctahedralEdgeGen_sq]

/-- **The `<2, 3, 4>` generators `a`, `b`, `c` generate the binary octahedral subgroup.** -/
theorem binaryOctahedralSubgroup_eq_closure_polyhedral :
    binaryOctahedralSubgroup = Subgroup.closure
      {binaryOctahedralEdgeGen, binaryOctahedralFaceGen, binaryDihedralRotation 4} := by
  refine le_antisymm ?_ ?_
  · rw [binaryOctahedralSubgroup_eq_closure_pair, Subgroup.closure_le, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    refine ⟨Subgroup.subset_closure (by simp), ?_⟩
    rw [← binaryOctahedralFaceGen_sq]
    exact pow_mem (Subgroup.subset_closure (by simp)) 2
  · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    exact ⟨binaryOctahedralEdgeGen_mem_binaryOctahedralSubgroup,
      binaryOctahedralFaceGen_mem_binaryOctahedralSubgroup,
      binaryDihedralRotation_four_mem_binaryOctahedralSubgroup⟩

/-! ### Element orders, exponent and distinguishing order-48 subgroups -/

/-- Every element of `SU(2)` with quaternion coordinates in `ℤ / √2` satisfies `g⁸ = 1`: its real
part is `0` (`g² = -1`, order `4`) or `±1 / √2` (`g⁴ = -1`, order `8`). -/
private theorem pow_eight_eq_one_of_coe_eq_div_sqrt_two {g : SU2} {w : Fin 4 → ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) =
      toComplexMatrix ⟨w 0 / √2, w 1 / √2, w 2 / √2, w 3 / √2⟩) :
    g ^ 8 = 1 := by
  have hw := mem_binaryOctahedralSqrtTwoCoords_of_coe_eq hg
  set q : ℍ[ℝ] := ⟨w 0 / √2, w 1 / √2, w 2 / √2, w 3 / √2⟩
  have hq : normSq q = 1 := by
    have hw' := mem_binaryOctahedralSqrtTwoCoords_iff.mp hw
    rw [Fin.sum_univ_four] at hw'
    rw [normSq_mk_div, Real.sq_sqrt zero_le_two, div_eq_one_iff_eq two_ne_zero]
    exact_mod_cast hw'
  set t : ℝ := 2 * q.re with ht_def
  have hsq : q ^ 2 = t • q - 1 := by
    simpa [← ht_def, hq] using sq_eq_two_re_smul_sub_normSq q
  have hw_cases := (by decide : ∀ w ∈ binaryOctahedralSqrtTwoCoords, w 0 = 0 ∨ w 0 ^ 2 = 1) w hw
  have hq8 : q ^ 8 = 1 := by
    rcases hw_cases with h0 | h1
    · have ht0 : t = 0 := by simp [ht_def, q, h0]
      have hq2 : q ^ 2 = -1 := by simp [hsq, ht0]
      calc q ^ 8 = (q ^ 2) ^ 4 := by rw [← pow_mul]
        _ = (-1) ^ 4 := by rw [hq2]
        _ = 1 := by norm_num
    · have ht2 : t ^ 2 = 2 := by
        have h1' : (w 0 : ℝ) ^ 2 = 1 := by exact_mod_cast h1
        simp only [ht_def, q, mul_pow, div_pow, Real.sq_sqrt zero_le_two, h1']
        ring
      have hq3 : q ^ 3 = q - ↑t := by
        have h21 : (2 : ℝ) - 1 = 1 := by norm_num
        have h := pow_three_eq_smul_sub q
        rwa [← ht_def, hq, ht2, h21, one_smul, mul_one] at h
      have hq4 : q ^ 4 = -1 := by
        calc q ^ 4 = q * q ^ 3 := by rw [pow_succ']
          _ = q * (q - ↑t) := by rw [hq3]
          _ = q ^ 2 - t • q := by
            rw [mul_sub, ← sq, ← coe_commutes, coe_mul_eq_smul]
          _ = -1 := by rw [hsq, sub_right_comm, sub_self, zero_sub]
      calc q ^ 8 = (q ^ 4) ^ 2 := by rw [← pow_mul]
        _ = (-1) ^ 2 := by rw [hq4]
        _ = 1 := by norm_num
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, hg, ← map_pow, hq8, map_one, OneMemClass.coe_one]

/-- Every element of the binary octahedral subgroup outside the binary tetrahedral subgroup
satisfies `g⁸ = 1`: its quaternion real part is `0` (order `4`) or `±1 / √2` (order `8`). -/
theorem pow_eight_eq_one_of_mem_binaryOctahedralSubgroup_of_notMem {g : SU2}
    (hg : g ∈ binaryOctahedralSubgroup) (hnot : g ∉ binaryTetrahedralSubgroup) : g ^ 8 = 1 := by
  rcases hg with hg | ⟨_, -, hg⟩
  · exact absurd hg hnot
  · exact pow_eight_eq_one_of_coe_eq_div_sqrt_two hg

/-- **Every element of the binary octahedral subgroup satisfies `g⁸ = 1` or `g⁶ = 1`.** -/
theorem pow_eight_eq_one_or_pow_six_eq_one_of_mem_binaryOctahedralSubgroup {g : SU2}
    (hg : g ∈ binaryOctahedralSubgroup) : g ^ 8 = 1 ∨ g ^ 6 = 1 := by
  rcases hg with hg | ⟨_, -, hg⟩
  · refine (pow_four_eq_one_or_pow_six_eq_one_of_mem_binaryTetrahedralSubgroup hg).imp
      (fun h4 => ?_) id
    calc g ^ 8 = (g ^ 4) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [h4, one_pow]
  · exact .inl (pow_eight_eq_one_of_coe_eq_div_sqrt_two hg)

/-- **Every element of the binary octahedral subgroup has order at most 8.** -/
theorem orderOf_le_eight_of_mem_binaryOctahedralSubgroup {g : SU2}
    (hg : g ∈ binaryOctahedralSubgroup) : orderOf g ≤ 8 := by
  rcases pow_eight_eq_one_or_pow_six_eq_one_of_mem_binaryOctahedralSubgroup hg with h8 | h6
  · exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr h8)
  · exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr h6)).trans (by norm_num)

/-- **The exponent of the binary octahedral subgroup is 24.** -/
@[simp]
theorem exponent_binaryOctahedralSubgroup : Monoid.exponent binaryOctahedralSubgroup = 24 := by
  refine Nat.dvd_antisymm ?_ ?_
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rcases pow_eight_eq_one_or_pow_six_eq_one_of_mem_binaryOctahedralSubgroup g.2 with h8 | h6
    · calc (g : SU2) ^ 24 = ((g : SU2) ^ 8) ^ 3 := by group
        _ = 1 := by rw [h8, one_pow]
    · calc (g : SU2) ^ 24 = ((g : SU2) ^ 6) ^ 4 := by group
        _ = 1 := by rw [h6, one_pow]
  · have h8 : 8 ∣ Monoid.exponent binaryOctahedralSubgroup := by
      have hord := Monoid.order_dvd_exponent
        (⟨binaryDihedralRotation 4, binaryDihedralRotation_four_mem_binaryOctahedralSubgroup⟩ :
          binaryOctahedralSubgroup)
      rwa [← Subgroup.orderOf_coe, orderOf_binaryDihedralRotation] at hord
    have h3 : 3 ∣ Monoid.exponent binaryOctahedralSubgroup := by
      have hord := Monoid.order_dvd_exponent
        (⟨binaryTetrahedralOmega, binaryTetrahedralSubgroup_le_binaryOctahedralSubgroup
          binaryTetrahedralOmega_mem_binaryTetrahedralSubgroup⟩ : binaryOctahedralSubgroup)
      rwa [← Subgroup.orderOf_coe, orderOf_binaryTetrahedralOmega] at hord
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h3

/-- **The binary octahedral subgroup is not cyclic.** -/
theorem not_isCyclic_binaryOctahedralSubgroup : ¬IsCyclic binaryOctahedralSubgroup := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := binaryOctahedralSubgroup)
  rw [← Subgroup.orderOf_coe, natCard_binaryOctahedralSubgroup] at hg
  have hle := orderOf_le_eight_of_mem_binaryOctahedralSubgroup g.2
  omega

/-- **The binary octahedral subgroup is not isomorphic to `QuaternionGroup 12`**: every element of
`binaryOctahedralSubgroup` has order at most `8`, whereas `QuaternionGroup.a 1` has order `24`. -/
instance isEmpty_binaryOctahedralSubgroup_mulEquiv_quaternionGroup :
    IsEmpty (binaryOctahedralSubgroup ≃* QuaternionGroup 12) := by
  refine ⟨fun e => ?_⟩
  set g : binaryOctahedralSubgroup := e.symm (.a 1)
  have hord : orderOf (g : SU2) = 24 := by
    rw [Subgroup.orderOf_coe, ← e.orderOf_eq g, e.apply_symm_apply, QuaternionGroup.orderOf_a_one]
  have hle := orderOf_le_eight_of_mem_binaryOctahedralSubgroup g.2
  omega

end TauCeti.SU2
