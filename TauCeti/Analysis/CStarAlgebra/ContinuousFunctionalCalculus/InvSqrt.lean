/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import TauCeti.Analysis.Normed.Algebra.Spectrum
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.Analysis.Real.Sqrt

/-!
# Renormalizing an element close to `1` by `k^{-1/2}`

A self-adjoint element `k` of a C⋆-algebra with `‖k - 1‖ ≤ ε ≤ 1/4` has its spectrum in
`[3/4, 5/4]` (`spectrum.norm_sub_one_le_of_mem`), where `t ↦ t^{-1/2}` moves a point by at
most its distance to `1` (`Real.abs_one_sub_inv_sqrt_le_abs_sub_one`). So the continuous
functional calculus gives a self-adjoint `g = k^{-1/2}` with `gkg = 1` and `‖g - 1‖ ≤ ε`.
Applied to `k = QhQ + (1 - Q)` for a projection `Q` commuting with a self-adjoint `h` close to
`Q`, this renormalizes the compression `QhQ` to `Q`.

## Main declarations

* `IsSelfAdjoint.exists_isSelfAdjoint_mul_mul_eq_one`: the renormalizing element `g = k^{-1/2}`.
* `IsStarProjection.exists_isSelfAdjoint_mul_compress_mul_eq`: renormalizing a compression.
-/

public section

open scoped CStarAlgebra

namespace TauCeti

variable {B : Type*} [CStarAlgebra B]

/-- **Renormalizing an element close to `1`.** A self-adjoint `k` with `‖k - 1‖ ≤ ε ≤ 1/4` has
a self-adjoint `g = k^{-1/2}` with `gkg = 1` and `‖g - 1‖ ≤ ε`, commuting with everything that
commutes with `k`. -/
theorem _root_.IsSelfAdjoint.exists_isSelfAdjoint_mul_mul_eq_one {k : B} (hk : IsSelfAdjoint k)
    {ε : ℝ} (hε : ‖k - 1‖ ≤ ε) (hε4 : ε ≤ 1 / 4) :
    ∃ g : B, IsSelfAdjoint g ∧ g * k * g = 1 ∧ ‖g - 1‖ ≤ ε ∧
      ∀ b : B, Commute k b → Commute g b := by
  have hspec : ∀ t ∈ spectrum ℝ k, |t - 1| ≤ ε := fun t ht ↦
    (Real.norm_eq_abs _ ▸ spectrum.norm_sub_one_le_of_mem ht).trans hε
  have hpos : ∀ t ∈ spectrum ℝ k, 0 < t := fun t ht ↦ by
    linarith [abs_le.mp ((hspec t ht).trans hε4)]
  have hcont : ContinuousOn (fun t : ℝ ↦ (√t)⁻¹) (spectrum ℝ k) :=
    Real.continuous_sqrt.continuousOn.inv₀ fun t ht ↦ (Real.sqrt_pos.mpr (hpos t ht)).ne'
  refine ⟨cfc (fun t : ℝ ↦ (√t)⁻¹) k, cfc_predicate _ k, ?_, ?_, fun b hb ↦ hb.cfc_real _⟩
  · nth_rewrite 2 [← cfc_id' ℝ k]
    rw [← cfc_mul _ _ k, ← cfc_mul _ _ k, ← cfc_const_one ℝ k]
    refine cfc_congr fun t ht ↦ ?_
    have h0 := (Real.sqrt_pos.mpr (hpos t ht)).ne'
    field_simp
    exact (Real.sq_sqrt (hpos t ht).le).symm
  · have he : cfc (fun t : ℝ ↦ (√t)⁻¹ - 1) k = cfc (fun t : ℝ ↦ (√t)⁻¹) k - 1 := by
      rw [cfc_sub _ _ k, cfc_const_one ℝ k]
    rw [← he]
    refine norm_cfc_le ((norm_nonneg _).trans hε) fun t ht ↦ ?_
    rw [Real.norm_eq_abs]
    have h4 := abs_le.mp ((hspec t ht).trans hε4)
    have hs : 1 / 2 ≤ √t := Real.le_sqrt_of_sq_le (by linarith)
    rw [abs_sub_comm]
    exact (Real.abs_one_sub_inv_sqrt_le_abs_sub_one t (by linarith)).trans (hspec t ht)

/-- **Renormalizing a compression.** If `Q` is a projection commuting with a self-adjoint `h`
with `‖h - Q‖ ≤ ε ≤ 1/4`, then some self-adjoint `g` commuting with `Q`, with `‖g - 1‖ ≤ ε`,
renormalizes the compression: `g(QhQ)g = Q`. Here `g = k^{-1/2}` for `k = QhQ + (1 - Q)`. -/
theorem _root_.IsStarProjection.exists_isSelfAdjoint_mul_compress_mul_eq {Q h : B}
    (hQ : IsStarProjection Q) (hh : IsSelfAdjoint h) (hQh : Commute Q h) {ε : ℝ}
    (hε : ‖h - Q‖ ≤ ε) (hε4 : ε ≤ 1 / 4) :
    ∃ g : B, IsSelfAdjoint g ∧ Commute g Q ∧ g * (Q * h * Q) * g = Q ∧ ‖g - 1‖ ≤ ε := by
  have hQQ : Q * Q = Q := hQ.isIdempotentElem.eq
  have hksa : IsSelfAdjoint (Q * h + (1 - Q)) := by
    refine IsSelfAdjoint.add ?_ hQ.one_sub.isSelfAdjoint
    rw [IsSelfAdjoint, star_mul, hh.star_eq, hQ.isSelfAdjoint.star_eq]
    exact hQh.eq.symm
  have hk1 : ‖Q * h + (1 - Q) - 1‖ ≤ ε := by
    have : Q * h + (1 - Q) - 1 = Q * (h - Q) := by
      rw [mul_sub, hQQ]
      abel
    rw [this]
    exact (norm_mul_le_of_norm_le_one_left hQ.norm_le _).trans hε
  obtain ⟨g, hgsa, hgkg, hg1, hgc⟩ := hksa.exists_isSelfAdjoint_mul_mul_eq_one hk1 hε4
  have hgQ : Commute g Q := hgc Q (((Commute.refl Q).mul_left hQh.symm).add_left
    ((Commute.one_left Q).sub_left (Commute.refl Q)))
  have hQk : Q * h * Q = Q * (Q * h + (1 - Q)) := by
    rw [mul_assoc, ← hQh.eq, ← mul_assoc, hQQ]
    simp only [mul_add, mul_sub, mul_one, ← mul_assoc, hQQ, sub_self, add_zero]
  refine ⟨g, hgsa, hgQ, ?_, hg1⟩
  calc g * (Q * h * Q) * g = Q * (g * (Q * h + (1 - Q)) * g) := by
        rw [hQk, ← mul_assoc, hgQ.eq]; simp only [mul_assoc]
    _ = Q := by rw [hgkg, mul_one]

end TauCeti
