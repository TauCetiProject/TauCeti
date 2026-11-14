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

When lifting partial isometries or Murray–von Neumann equivalences from quotients, passing to
inductive limits of C⋆-algebras, or perturbing off-diagonal approximate matrix units once the
diagonal projections have been stabilized, one obtains an element `z` already compressed to a corner
`q * A * p` (`q * z = z` and `z * p = z`) whose initial and final projection defects
`‖star z * z - p‖` and `‖z * star z - q‖` are small.

This file proves quantitative polar perturbation for such approximate partial isometries: whenever
`p` and `q` are star projections and `z` satisfies `q * z = z`, `z * p = z`,
`‖star z * z - p‖ < η`, and `‖z * star z - q‖ < η` with `η ≤ 1 / 32`, functional-calculus polar
normalization produces an exact partial isometry `v` with initial projection `star v * v = p`,
final projection `v * star v = q`, and `‖v - z‖ < 10 * η`, inside every closed non-unital
`ℂ`-`⋆`-subalgebra containing `z`.

## Main results

* `TauCeti.exists_isPartialIsometry_mem_of_approx`: quantitative polar perturbation of an
  approximate partial isometry inside a closed non-unital `ℂ`-`⋆`-subalgebra.
* `TauCeti.exists_isPartialIsometry_of_approx`: whole-algebra specialization of
  `TauCeti.exists_isPartialIsometry_mem_of_approx`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.8.3.23.
-/

public section

open scoped NonUnitalContinuousFunctionalCalculus

namespace TauCeti

section PartialIsometry

variable {A : Type*} [NonUnitalCStarAlgebra A]

private def projCornerSubalgebra (s : NonUnitalStarSubalgebra ℂ A) (p : A)
    (hp : IsStarProjection p) : NonUnitalStarSubalgebra ℂ A where
  carrier := {a : A | a ∈ s ∧ p * a = a ∧ a * p = a}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by rw [mul_add, ha.2.1, hb.2.1],
    by rw [add_mul, ha.2.2, hb.2.2]⟩
  zero_mem' := ⟨zero_mem s, mul_zero p, zero_mul p⟩
  mul_mem' ha hb := ⟨mul_mem ha.1 hb.1, by rw [← mul_assoc, ha.2.1], by rw [mul_assoc, hb.2.2]⟩
  smul_mem' c _ ha := ⟨SMulMemClass.smul_mem c ha.1, by rw [mul_smul_comm, ha.2.1],
    by rw [smul_mul_assoc, ha.2.2]⟩
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
    IsClosed (projCornerSubalgebra s p hp : Set A) := by
  rw [coe_projCornerSubalgebra]
  exact hs.and
    ((isClosed_eq (continuous_const.mul continuous_id) continuous_id).and
      (isClosed_eq (continuous_id.mul continuous_const) continuous_id))

/-- **Quantitative polar perturbation of an approximate partial isometry** in a closed non-unital
`ℂ`-`⋆`-subalgebra `s`: if `p` and `q` are star projections and `z ∈ s` satisfies `q * z = z`,
`z * p = z`, `‖star z * z - p‖ < η`, and `‖z * star z - q‖ < η` with `η ≤ 1 / 32`, there exists a
partial isometry `v ∈ s` with `star v * v = p`, `v * star v = q`, and `‖v - z‖ < 10 * η`. -/
theorem exists_isPartialIsometry_mem_of_approx {S : Type*} [SetLike S A]
    [NonUnitalSubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A] {s : S}
    [hs : IsClosed (s : Set A)] {η : ℝ} (hη : η ≤ 1 / 32) {p q z : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hzs : z ∈ s)
    (hqz : q * z = z) (hzp : z * p = z)
    (hinit : ‖star z * z - p‖ < η) (hfin : ‖z * star z - q‖ < η) :
    ∃ v ∈ s, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q ∧ ‖v - z‖ < 10 * η := by
  -- Step 1: Work in the closed corner `p * s * p`, where `h = star z * z` is close to `p`.
  let corner := projCornerSubalgebra (NonUnitalStarSubalgebra.ofClass s) p hp
  have : IsClosed (corner : Set A) := isClosed_projCornerSubalgebra hs p hp
  set h : A := star z * z
  have hh_sa : IsSelfAdjoint h := IsSelfAdjoint.star_mul_self z
  have hph : p * h = h := by rw [← hp.isSelfAdjoint.star_eq, ← mul_assoc, ← star_mul, hzp]
  have hhp : h * p = h := by rw [mul_assoc, hzp]
  have hh_corner : h ∈ corner :=
    mem_projCornerSubalgebra.mpr ⟨mul_mem (star_mem hzs) hzs, hph, hhp⟩
  have hh_defect : ‖h * h - h‖ ≤ ‖h - p‖ ^ 2 + ‖h - p‖ := by
    rw [show h * h - h = (h - p) * (h - p) + (h - p) by
      simp only [sub_mul, mul_sub, hph, hhp, hp.isIdempotentElem.eq]; abel, sq]
    linarith [norm_mul_le (h - p) (h - p), norm_add_le ((h - p) * (h - p)) (h - p)]
  have hsq_lt : ‖h - p‖ ^ 2 ≤ (1 / 32) * ‖h - p‖ := by nlinarith [norm_nonneg (h - p)]
  have hh_lt_quarter : ‖h * h - h‖ < 1 / 4 := by linarith [norm_nonneg (h - p)]
  -- Step 2: Identify the `(1 / 2, ∞)` spectral projection of `h` with `p`.
  obtain ⟨-, -, hsp_mul_p⟩ :=
    mem_projCornerSubalgebra.mp (spectralProjectionIoiHalf_mem (𝕜' := ℂ) hh_corner)
  have hsp_dist_p : ‖spectralProjectionIoiHalf h - p‖ < 1 := by
    linarith [hh_sa.norm_spectralProjectionIoiHalf_sub_le hh_lt_quarter,
      norm_sub_le_norm_sub_add_norm_sub (spectralProjectionIoiHalf h) h p]
  have hsp_eq_p : spectralProjectionIoiHalf h = p :=
    (isStarProjection_spectralProjectionIoiHalf h).eq_of_mul_eq_left_of_norm_sub_lt_one
      hp hsp_mul_p hsp_dist_p
  -- Step 3: Form `v = z * w` using the truncated inverse square root `w` of `h`.
  set g : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹
  set w : A := cfcₙ g h
  obtain ⟨hw_mem_s, -, hwp⟩ := mem_projCornerSubalgebra.mp (cfcₙ_mem (𝕜' := ℂ) g hh_corner)
  have hw_sa : IsSelfAdjoint w := IsSelfAdjoint.cfcₙ
  have hwhw : w * h * w = p := by
    simpa [w, g, hsp_eq_p] using hh_sa.cfcₙ_indicator_Ioi_half_inv_sqrt_mul_self_mul hh_lt_quarter
  set v : A := z * w
  have hv_mem : v ∈ s := mul_mem hzs hw_mem_s
  have hv_init : star v * v = p := by
    dsimp [v]; rw [star_mul, hw_sa.star_eq, mul_assoc w, ← mul_assoc (star z), ← hwhw]
    simp [h, mul_assoc]
  have hv_pi : IsPartialIsometry v := by
    rw [isPartialIsometry_iff, mul_assoc, hv_init]; dsimp [v]; rw [mul_assoc, hwp]
  -- Step 4: Bound `‖v - z‖ < 10 * η` and deduce `v * star v = q` by projection rigidity.
  have hz_norm : ‖z‖ ≤ 2 := by
    have hnorm_h : ‖h‖ ≤ 2 := by linarith [hp.norm_le p, norm_le_norm_add_norm_sub' h p]
    rw [CStarRing.norm_star_mul_self] at hnorm_h; nlinarith [norm_nonneg z]
  have hw_sub_p : ‖w - p‖ ≤ 4 * ‖h * h - h‖ := by
    simpa [w, g, hsp_eq_p] using
      hh_sa.norm_cfcₙ_indicator_Ioi_half_inv_sqrt_sub_spectralProjectionIoiHalf_le hh_lt_quarter
  have hv_sub_z : ‖v - z‖ < 10 * η := by
    rw [show v - z = z * (w - p) by dsimp [v]; rw [mul_sub, hzp]]
    have hwp_lt : ‖w - p‖ < 5 * η := by linarith [norm_nonneg (h - p)]
    exact (norm_mul_le_of_le hz_norm le_rfl).trans_lt (by linarith)
  have hv_fin_q : (v * star v) * q = v * star v := by
    have hqv : q * v = v := by dsimp [v]; rw [← mul_assoc, hqz]
    rw [← hq.isSelfAdjoint.star_eq, mul_assoc, ← star_mul, hqv]
  have hv_fin_dist : ‖v * star v - q‖ < 1 := by
    rw [show v * star v - q = (v - z) * star v + z * star (v - z) + (z * star z - q) by
      simp only [sub_mul, mul_sub, star_sub]; abel]
    refine norm_add₃_le.trans_lt ?_
    linarith [norm_mul_le_of_le hv_sub_z.le ((norm_star v).le.trans hv_pi.norm_le_one),
      norm_mul_le_of_le hz_norm ((norm_star (v - z)).le.trans hv_sub_z.le)]
  exact ⟨v, hv_mem, hv_pi, hv_init,
    hv_pi.isStarProjection_mul_star_self.eq_of_mul_eq_left_of_norm_sub_lt_one hq hv_fin_q
      hv_fin_dist,
    hv_sub_z⟩

/-- **Quantitative polar perturbation of an approximate partial isometry**: if `p` and `q` are star
projections and `z : A` satisfies `q * z = z`, `z * p = z`, `‖star z * z - p‖ < η`, and
`‖z * star z - q‖ < η` with `η ≤ 1 / 32`, there exists a partial isometry `v : A` with
`star v * v = p`, `v * star v = q`, and `‖v - z‖ < 10 * η`. -/
theorem exists_isPartialIsometry_of_approx {η : ℝ} (hη : η ≤ 1 / 32) {p q z : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqz : q * z = z) (hzp : z * p = z)
    (hinit : ‖star z * z - p‖ < η) (hfin : ‖z * star z - q‖ < η) :
    ∃ v : A, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q ∧ ‖v - z‖ < 10 * η := by
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨v, -, hv_pi, hv_init, hv_fin, hv_dist⟩ :=
    exists_isPartialIsometry_mem_of_approx (s := (⊤ : NonUnitalStarSubalgebra ℂ A))
      hη hp hq trivial hqz hzp hinit hfin
  exact ⟨v, hv_pi, hv_init, hv_fin, hv_dist⟩

end PartialIsometry

end TauCeti
