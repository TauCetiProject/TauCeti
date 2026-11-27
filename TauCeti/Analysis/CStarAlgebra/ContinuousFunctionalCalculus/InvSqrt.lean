/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Renormalizing an element close to `1` by `k^{-1/2}`

A self-adjoint element `k` of a C⋆-algebra with `‖k - 1‖ ≤ ε ≤ 1/4` has its spectrum in
`[3/4, 5/4]`, where `t ↦ t^{-1/2}` moves a point by at most its distance to `1`. So the
continuous functional calculus gives a self-adjoint `g = k^{-1/2}` with `gkg = 1` and
`‖g - 1‖ ≤ ε`. Applied to `k = QhQ + (1 - Q)` for a projection `Q` commuting with a self-adjoint
`h` close to `Q`, this renormalizes the compression `QhQ` to `Q`.

## Main declarations

* `TauCeti.abs_inv_sqrt_sub_one_le`: `|t^{-1/2} - 1| ≤ |t - 1|` when `|t - 1| ≤ 1/4`.
* `TauCeti.abs_sub_one_le_of_mem_spectrum`: the real spectrum of `k` lies within `‖k - 1‖`
  of `1`.
* `TauCeti.exists_isSelfAdjoint_mul_mul_eq_one`: the renormalizing element `g = k^{-1/2}`.
* `IsStarProjection.exists_isSelfAdjoint_mul_compress_mul_eq`: renormalizing a compression.
-/

public section

open scoped CStarAlgebra

namespace TauCeti

/-- On `[3/4, 5/4]`, `t ↦ t^{-1/2}` moves a point by at most its distance to `1`. -/
theorem abs_inv_sqrt_sub_one_le {t : ℝ} (ht : |t - 1| ≤ 1 / 4) :
    |(√t)⁻¹ - 1| ≤ |t - 1| := by
  have ht' : 3 / 4 ≤ t := by linarith [abs_le.mp ht]
  have hs : 7 / 10 ≤ √t := Real.le_sqrt_of_sq_le (by linarith)
  have hsq : √t ^ 2 = t := Real.sq_sqrt (by linarith)
  have key : (√t)⁻¹ - 1 = -(t - 1) / (√t * (1 + √t)) := by
    field_simp
    nlinarith
  rw [key, abs_div, abs_neg, abs_of_pos (by positivity : 0 < √t * (1 + √t))]
  exact div_le_self (abs_nonneg _) (by nlinarith)

variable {B : Type*} [CStarAlgebra B]

/-- The real spectrum of `k` lies within `‖k - 1‖` of `1`. -/
theorem abs_sub_one_le_of_mem_spectrum {k : B} {t : ℝ} (ht : t ∈ spectrum ℝ k) :
    |t - 1| ≤ ‖k - 1‖ := by
  have h : t - 1 ∈ spectrum ℝ (k - algebraMap ℝ B 1) := by
    rw [← spectrum.sub_singleton_eq]
    exact Set.sub_mem_sub ht rfl
  rw [map_one] at h
  exact spectrum.norm_le_norm_of_mem h

/-- **Renormalizing an element close to `1`.** A self-adjoint `k` with `‖k - 1‖ ≤ ε ≤ 1/4` has
a self-adjoint `g = k^{-1/2}` with `gkg = 1` and `‖g - 1‖ ≤ ε`, commuting with everything that
commutes with `k`. -/
theorem exists_isSelfAdjoint_mul_mul_eq_one {k : B} (hk : IsSelfAdjoint k) {ε : ℝ}
    (hε : ‖k - 1‖ ≤ ε) (hε4 : ε ≤ 1 / 4) :
    ∃ g : B, IsSelfAdjoint g ∧ g * k * g = 1 ∧ ‖g - 1‖ ≤ ε ∧
      ∀ b : B, Commute k b → Commute g b := by
  have hspec : ∀ t ∈ spectrum ℝ k, |t - 1| ≤ ε := fun t ht ↦
    (abs_sub_one_le_of_mem_spectrum ht).trans hε
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
    exact (abs_inv_sqrt_sub_one_le ((hspec t ht).trans hε4)).trans (hspec t ht)

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
  obtain ⟨g, hgsa, hgkg, hg1, hgc⟩ := exists_isSelfAdjoint_mul_mul_eq_one hksa hk1 hε4
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
