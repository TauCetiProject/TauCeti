/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import TauCeti.Analysis.CStarAlgebra.Basic
import Mathlib.Algebra.Star.NonUnitalSubalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.Topology.Algebra.NonUnitalStarAlgebra

/-!
# Norm stability of partial isometries in C⋆-algebras

For star projections `p, q` and a corner-compressed element `z` (`q * z = z`, `z * p = z`) with
`‖star z * z - p‖ < η`, `‖z * star z - q‖ < η` (`η ≤ 1 / 32`), polar normalization yields a partial
isometry `v` (`star v * v = p`, `v * star v = q`, `‖v - z‖ < 10 * η`) in every closed non-unital
`𝕜'`-`⋆`-subalgebra (for any scalar monoid `𝕜'` over `ℝ`) containing `z`.

## Main results

* `TauCeti.exists_isPartialIsometry_mem_of_approx`, `TauCeti.exists_isPartialIsometry_of_approx`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.8.3.23.
-/

public section
open scoped NonUnitalContinuousFunctionalCalculus
open NonUnitalStarSubalgebra (mem_corner mem_ofClass)
namespace TauCeti
variable {A : Type*} [NonUnitalCStarAlgebra A]
/-- **Quantitative polar perturbation of an approximate partial isometry** in a closed non-unital
`𝕜'`-`⋆`-subalgebra `s` (scalar monoid `𝕜'` over `ℝ`): for star projections `p, q` and `z ∈ s`
with `q * z = z`, `z * p = z`, `‖star z * z - p‖ < η`, `‖z * star z - q‖ < η` (`η ≤ 1 / 32`), some
partial isometry `v ∈ s` has `star v * v = p`, `v * star v = q`, `‖v - z‖ < 10 * η`. -/
theorem exists_isPartialIsometry_mem_of_approx {𝕜' S : Type*} [Monoid 𝕜'] [MulAction 𝕜' A]
    [SetLike S A] [NonUnitalSubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A]
    [SMulMemClass S 𝕜' A] [StarMemClass S A] {s : S} [hs : IsClosed (s : Set A)] {η : ℝ}
    (hη : η ≤ 1 / 32) {p q z : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hzs : z ∈ s) (hqz : q * z = z) (hzp : z * p = z) (hinit : ‖star z * z - p‖ < η)
    (hfin : ‖z * star z - q‖ < η) :
    ∃ v ∈ s, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q ∧ ‖v - z‖ < 10 * η := by
  have : SMulMemClass S ℝ A := SMulMemClass.ofIsScalarTower S ℝ 𝕜' A
  let s' : NonUnitalStarSubalgebra ℝ A := NonUnitalStarSubalgebra.ofClass s
  have hs'_coe : (s' : Set A) = (s : Set A) := Set.ext fun _ ↦ mem_ofClass
  have : IsClosed (s' : Set A) := hs'_coe ▸ hs
  let corner := s'.corner hp.isSelfAdjoint
  set h : A := star z * z; have hh_sa : IsSelfAdjoint h := IsSelfAdjoint.star_mul_self z
  have hph : p * h = h := by rw [← hp.isSelfAdjoint.star_eq, ← mul_assoc, ← star_mul, hzp]
  have hhp : h * p = h := by rw [mul_assoc, hzp]
  have hh_corner : h ∈ corner := mem_corner.mpr
    ⟨mem_ofClass.mpr (mul_mem (star_mem hzs) hzs), hph, hhp⟩
  have hh_defect : ‖h * h - h‖ ≤ ‖h - p‖ ^ 2 + ‖h - p‖ :=
    hp.isIdempotentElem.norm_mul_self_sub_le_of_mul_eq hph hhp
  have hh_lt_quarter : ‖h * h - h‖ < 1 / 4 := by nlinarith [norm_nonneg (h - p)]
  obtain ⟨-, -, hsp_mul_p⟩ := mem_corner.mp (spectralProjectionIoiHalf_mem (𝕜' := ℝ) hh_corner)
  have hsp_eq_p : spectralProjectionIoiHalf h = p :=
    (isStarProjection_spectralProjectionIoiHalf h).eq_of_mul_eq_left_of_norm_sub_lt_one hp hsp_mul_p
      (by linarith [hh_sa.norm_spectralProjectionIoiHalf_sub_le hh_lt_quarter,
        norm_sub_le_norm_sub_add_norm_sub (spectralProjectionIoiHalf h) h p])
  set g : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹; set w : A := cfcₙ g h
  obtain ⟨hw_mem_s', -, hwp⟩ := mem_corner.mp (cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℝ) g hh_corner)
  set v : A := z * w
  have hv_init : star v * v = p := by
    have hw_sa : IsSelfAdjoint w := cfcₙ_predicate g h
    have hv_star_v : star v * v = w * h * w := by
      simp only [v, h, star_mul, hw_sa.star_eq, mul_assoc]
    rw [hv_star_v]
    simpa [w, g, hsp_eq_p] using hh_sa.cfcₙ_indicator_Ioi_half_inv_sqrt_mul_self_mul hh_lt_quarter
  have hv_pi : IsPartialIsometry v := by
    rw [isPartialIsometry_iff, mul_assoc, hv_init]; dsimp [v]; rw [mul_assoc, hwp]
  have hz_norm : ‖z‖ ≤ 2 := by
    have hnorm_sq : ‖h‖ = ‖z‖ * ‖z‖ := CStarRing.norm_star_mul_self
    nlinarith [norm_nonneg z, hp.norm_le p, norm_le_norm_add_norm_sub' h p]
  have hw_sub_p : ‖w - p‖ ≤ 4 * ‖h * h - h‖ := by simpa [w, g, hsp_eq_p] using
    hh_sa.norm_cfcₙ_indicator_Ioi_half_inv_sqrt_sub_spectralProjectionIoiHalf_le hh_lt_quarter
  have hv_sub_z : ‖v - z‖ < 10 * η := by
    have hvz : v - z = z * (w - p) := by dsimp [v]; rw [mul_sub, hzp]
    rw [hvz]
    exact (norm_mul_le_of_le hz_norm le_rfl).trans_lt (by nlinarith [norm_nonneg (h - p)])
  have hv_fin_q : (v * star v) * q = v * star v := by
    have hqv : q * v = v := by dsimp [v]; rw [← mul_assoc, hqz]
    rw [← hq.isSelfAdjoint.star_eq, mul_assoc, ← star_mul, hqv]
  have hv_fin_dist : ‖v * star v - q‖ < 1 := by
    have hprod_diff : ‖v * star v - z * star z‖ ≤
        ‖v - z‖ * ‖star v‖ + ‖z‖ * ‖star v - star z‖ :=
      norm_mul_sub_mul_le v (star v) z (star z)
    rw [norm_star, ← star_sub, norm_star] at hprod_diff
    have h1 : ‖v - z‖ * ‖v‖ ≤ (10 * η) * 1 :=
      mul_le_mul hv_sub_z.le hv_pi.norm_le_one (norm_nonneg _) (by linarith [norm_nonneg (v - z)])
    have h2 : ‖z‖ * ‖v - z‖ ≤ 2 * (10 * η) :=
      mul_le_mul hz_norm hv_sub_z.le (norm_nonneg _) (by positivity)
    linarith [norm_sub_le_norm_sub_add_norm_sub (v * star v) (z * star z) q]
  exact ⟨v, mul_mem hzs (mem_ofClass.mp hw_mem_s'), hv_pi, hv_init,
    hv_pi.isStarProjection_mul_star_self.eq_of_mul_eq_left_of_norm_sub_lt_one hq hv_fin_q
      hv_fin_dist, hv_sub_z⟩
/-- **Quantitative polar perturbation of an approximate partial isometry**: for projections `p, q`
and `z` (`q * z = z`, `z * p = z`, `‖star z * z - p‖ < η`, `‖z * star z - q‖ < η`, `η ≤ 1 / 32`),
a partial isometry `v` has `star v * v = p`, `v * star v = q`, `‖v - z‖ < 10 * η`. -/
theorem exists_isPartialIsometry_of_approx {η : ℝ} (hη : η ≤ 1 / 32) {p q z : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hqz : q * z = z) (hzp : z * p = z)
    (hinit : ‖star z * z - p‖ < η) (hfin : ‖z * star z - q‖ < η) :
    ∃ v : A, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q ∧ ‖v - z‖ < 10 * η := by
  let t : NonUnitalStarSubalgebra ℝ A := ⊤; have : IsClosed (t : Set A) := by simp [t]
  obtain ⟨v, -, h⟩ := exists_isPartialIsometry_mem_of_approx (𝕜' := ℝ) (s := t)
    hη hp hq NonUnitalStarAlgebra.mem_top hqz hzp hinit hfin; exact ⟨v, h⟩
end TauCeti
