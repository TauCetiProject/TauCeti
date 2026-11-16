/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import TauCeti.Analysis.CStarAlgebra.Basic
public import TauCeti.Analysis.CStarAlgebra.Projection.Stability

/-!
# Norm stability of partial isometries in C⋆-algebras

For star projections `p, q` and a corner-compressed element `z` (`q * z = z`, `z * p = z`) with
`‖star z * z - p‖ < η`, `‖z * star z - q‖ < η` (`η ≤ 1 / 32`), polar normalization yields an exact
partial isometry `v` with `star v * v = p`, `v * star v = q`, and `‖v - z‖ < 10 * η` in every
closed non-unital `ℂ`-`⋆`-subalgebra containing `z` — the key off-diagonal step for lifting
partial isometries and stabilizing matrix units.

## Main results

* `TauCeti.exists_isPartialIsometry_mem_of_approx`, `TauCeti.exists_isPartialIsometry_of_approx`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.8.3.23.
-/

public section

open scoped NonUnitalContinuousFunctionalCalculus

namespace TauCeti
variable {A : Type*} [NonUnitalCStarAlgebra A]

private def projCornerSubalgebra (s : NonUnitalStarSubalgebra ℂ A) (p : A)
    (hp : IsStarProjection p) : NonUnitalStarSubalgebra ℂ A where
  carrier := {a : A | a ∈ s ∧ p * a = a ∧ a * p = a}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by simp [mul_add, ha.2.1, hb.2.1],
    by simp [add_mul, ha.2.2, hb.2.2]⟩
  zero_mem' := ⟨zero_mem s, mul_zero p, zero_mul p⟩
  mul_mem' ha hb := ⟨mul_mem ha.1 hb.1, by rw [← mul_assoc, ha.2.1], by rw [mul_assoc, hb.2.2]⟩
  smul_mem' c _ ha := ⟨SMulMemClass.smul_mem c ha.1, by simp [mul_smul_comm, ha.2.1],
    by simp [smul_mul_assoc, ha.2.2]⟩
  star_mem' ha := ⟨star_mem ha.1, by rw [← hp.isSelfAdjoint.star_eq, ← star_mul, ha.2.2],
    by rw [← hp.isSelfAdjoint.star_eq, ← star_mul, ha.2.1]⟩

private lemma coe_projCornerSubalgebra (s : NonUnitalStarSubalgebra ℂ A) (p : A)
    (hp : IsStarProjection p) :
    (projCornerSubalgebra s p hp : Set A) = {a : A | a ∈ s ∧ p * a = a ∧ a * p = a} := rfl

private lemma mem_projCornerSubalgebra {s : NonUnitalStarSubalgebra ℂ A} {p : A}
    {hp : IsStarProjection p} {a : A} :
    a ∈ projCornerSubalgebra s p hp ↔ a ∈ s ∧ p * a = a ∧ a * p = a := Iff.rfl

private lemma isClosed_projCornerSubalgebra {s : NonUnitalStarSubalgebra ℂ A}
    (hs : IsClosed (s : Set A)) (p : A) (hp : IsStarProjection p) :
    IsClosed (projCornerSubalgebra s p hp : Set A) :=
  coe_projCornerSubalgebra s p hp ▸ hs.and
    ((isClosed_eq (continuous_const.mul continuous_id) continuous_id).and
      (isClosed_eq (continuous_id.mul continuous_const) continuous_id))

/-- **Quantitative polar perturbation of an approximate partial isometry** in a closed non-unital
`ℂ`-`⋆`-subalgebra `s`: for star projections `p, q` and `z ∈ s` with `q * z = z`, `z * p = z`,
`‖star z * z - p‖ < η`, `‖z * star z - q‖ < η` (`η ≤ 1 / 32`), there exists a partial isometry
`v ∈ s` with `star v * v = p`, `v * star v = q`, and `‖v - z‖ < 10 * η`. -/
theorem exists_isPartialIsometry_mem_of_approx {S : Type*} [SetLike S A]
    [NonUnitalSubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A] {s : S}
    [hs : IsClosed (s : Set A)] {η : ℝ} (hη : η ≤ 1 / 32) {p q z : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hzs : z ∈ s) (hqz : q * z = z)
    (hzp : z * p = z) (hinit : ‖star z * z - p‖ < η) (hfin : ‖z * star z - q‖ < η) :
    ∃ v ∈ s, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q ∧ ‖v - z‖ < 10 * η := by
  -- Step 1: Work in the closed corner `p * s * p`, where `h = star z * z` is close to `p`.
  let corner := projCornerSubalgebra (NonUnitalStarSubalgebra.ofClass s) p hp
  have : IsClosed (corner : Set A) := isClosed_projCornerSubalgebra hs p hp
  set h : A := star z * z; have hh_sa : IsSelfAdjoint h := IsSelfAdjoint.star_mul_self z
  have hph : p * h = h := by rw [← hp.isSelfAdjoint.star_eq, ← mul_assoc, ← star_mul, hzp]
  have hhp : h * p = h := by rw [mul_assoc, hzp]
  have hh_corner : h ∈ corner := mem_projCornerSubalgebra.mpr ⟨mul_mem (star_mem hzs) hzs, hph, hhp⟩
  have hh_defect : ‖h * h - h‖ ≤ ‖h - p‖ ^ 2 + ‖h - p‖ := by
    rw [show h * h - h = (h - p) * (h - p) + (h - p) by
      simp only [sub_mul, mul_sub, hph, hhp, hp.isIdempotentElem.eq]; abel, sq]
    linarith [norm_mul_le (h - p) (h - p), norm_add_le ((h - p) * (h - p)) (h - p)]
  have hh_lt_quarter : ‖h * h - h‖ < 1 / 4 := by nlinarith [norm_nonneg (h - p)]
  -- Step 2: Identify the `(1 / 2, ∞)` spectral projection of `h` with `p`.
  obtain ⟨-, -, hsp_mul_p⟩ :=
    mem_projCornerSubalgebra.mp (spectralProjectionIoiHalf_mem (𝕜' := ℂ) hh_corner)
  have hsp_eq_p : spectralProjectionIoiHalf h = p :=
    (isStarProjection_spectralProjectionIoiHalf h).eq_of_mul_eq_left_of_norm_sub_lt_one hp hsp_mul_p
      (by linarith [hh_sa.norm_spectralProjectionIoiHalf_sub_le hh_lt_quarter,
        norm_sub_le_norm_sub_add_norm_sub (spectralProjectionIoiHalf h) h p])
  -- Step 3: Form `v = z * w` using the truncated inverse square root `w` of `h`.
  set g : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹; set w : A := cfcₙ g h
  obtain ⟨hw_mem_s, -, hwp⟩ := mem_projCornerSubalgebra.mp (cfcₙ_mem (𝕜' := ℂ) g hh_corner)
  set v : A := z * w
  have hv_init : star v * v = p := by
    have hw_sa : IsSelfAdjoint w := cfcₙ_predicate g h
    rw [show star v * v = w * h * w by simp only [v, h, star_mul, hw_sa.star_eq, mul_assoc]]
    simpa [w, g, hsp_eq_p] using hh_sa.cfcₙ_indicator_Ioi_half_inv_sqrt_mul_self_mul hh_lt_quarter
  have hv_pi : IsPartialIsometry v := by
    rw [isPartialIsometry_iff, mul_assoc, hv_init]; dsimp [v]; rw [mul_assoc, hwp]
  -- Step 4: Bound `‖v - z‖ < 10 * η` and deduce `v * star v = q` by projection rigidity.
  have hz_norm : ‖z‖ ≤ 2 := by
    nlinarith [norm_nonneg z, show ‖h‖ = ‖z‖ * ‖z‖ from CStarRing.norm_star_mul_self,
      hp.norm_le p, norm_le_norm_add_norm_sub' h p]
  have hw_sub_p : ‖w - p‖ ≤ 4 * ‖h * h - h‖ := by simpa [w, g, hsp_eq_p] using
    hh_sa.norm_cfcₙ_indicator_Ioi_half_inv_sqrt_sub_spectralProjectionIoiHalf_le hh_lt_quarter
  have hv_sub_z : ‖v - z‖ < 10 * η := by
    rw [show v - z = z * (w - p) by dsimp [v]; rw [mul_sub, hzp]]
    exact (norm_mul_le_of_le hz_norm le_rfl).trans_lt (by nlinarith [norm_nonneg (h - p)])
  have hv_fin_q : (v * star v) * q = v * star v := by
    rw [← hq.isSelfAdjoint.star_eq, mul_assoc, ← star_mul, show q * v = v by
      dsimp [v]; rw [← mul_assoc, hqz]]
  have hv_fin_dist : ‖v * star v - q‖ < 1 := by
    rw [show v * star v - q = (v - z) * star v + z * star (v - z) + (z * star z - q) by
      simp only [sub_mul, mul_sub, star_sub]; abel]
    refine norm_add₃_le.trans_lt ?_
    linarith [norm_mul_le_of_le hv_sub_z.le ((norm_star v).le.trans hv_pi.norm_le_one),
      norm_mul_le_of_le hz_norm ((norm_star (v - z)).le.trans hv_sub_z.le)]
  exact ⟨v, mul_mem hzs hw_mem_s, hv_pi, hv_init,
    hv_pi.isStarProjection_mul_star_self.eq_of_mul_eq_left_of_norm_sub_lt_one hq hv_fin_q
      hv_fin_dist, hv_sub_z⟩

/-- **Quantitative polar perturbation of an approximate partial isometry**: for star projections
`p, q` and `z : A` with `q * z = z`, `z * p = z`, `‖star z * z - p‖ < η`, `‖z * star z - q‖ < η`
(`η ≤ 1 / 32`), there is a partial isometry `v` with `star v * v = p`, `v * star v = q`, and
`‖v - z‖ < 10 * η`. -/
theorem exists_isPartialIsometry_of_approx {η : ℝ} (hη : η ≤ 1 / 32) {p q z : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hqz : q * z = z) (hzp : z * p = z)
    (hinit : ‖star z * z - p‖ < η) (hfin : ‖z * star z - q‖ < η) :
    ∃ v : A, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q ∧ ‖v - z‖ < 10 * η := by
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨v, -, h⟩ := exists_isPartialIsometry_mem_of_approx
    (s := (⊤ : NonUnitalStarSubalgebra ℂ A)) hη hp hq trivial hqz hzp hinit hfin
  exact ⟨v, h⟩
end TauCeti
