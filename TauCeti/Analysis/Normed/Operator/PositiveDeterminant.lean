/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.PositiveDeterminant
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smooth paths of orientation-preserving linear maps

In finite dimension, transport the smooth positive-determinant matrix path through a finite
basis. The resulting family of continuous linear maps starts at the identity, ends at the given
map, and remains invertible for every real parameter. It supplies linear isotopies fixing the
origin. In infinite dimensions every determinant is `1` by convention, so the positive-determinant
conclusion is trivial there and the maps of the path need not be invertible.

Conversely, the determinant cannot change sign along a segment of injective maps: if every map
`f + t • (g - f)`, `0 ≤ t ≤ 1`, of a finite-dimensional real space is injective, then `f` and `g`
have determinants of the same sign (`LinearMap.det_mul_det_pos_of_forall_injective`), by the
intermediate value theorem. In particular two isomorphisms `G₀`, `G₁ : K ≃ Y` joined by a segment
of injective maps differ by an automorphism `G₁⁻¹ ∘ G₀` of positive determinant
(`LinearEquiv.det_trans_symm_pos_of_forall_injective`).

Reference: M. Hirsch, *Differential Topology*, Chapter 4, §6, Theorem 6.6.
-/

public section

open scoped ContDiff Matrix.Norms.Elementwise

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real continuous linear map of positive determinant admits a smooth path from the identity
through linear maps of positive determinant, on the whole real parameter line. In an
infinite-dimensional space every determinant is `1` by convention, so the conclusion is trivial
there and the maps `γ t` need not be invertible. -/
theorem exists_contDiff_det_pos (L : E →L[ℝ] E) (hL : 0 < L.det) :
    ∃ γ : ℝ → E →L[ℝ] E, ContDiff ℝ ∞ γ ∧ γ 0 = ContinuousLinearMap.id ℝ E ∧
      γ 1 = L ∧ ∀ t, 0 < (γ t).det := by
  classical
  by_cases hfin : FiniteDimensional ℝ E
  swap
  · refine ⟨fun t => (1 - t) • ContinuousLinearMap.id ℝ E + t • L, by fun_prop, by simp, by simp,
      fun t => ?_⟩
    simp [ContinuousLinearMap.det, LinearMap.det_eq_one_of_not_module_finite hfin]
  let b := Module.finBasis ℝ E
  let T := ((Matrix.toLin b b).trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv
  -- Compute the locally constructed transport through the chosen finite basis.
  have hT (A) : T A = LinearMap.toContinuousLinearMap (Matrix.toLin b b A) := rfl
  have hdet (A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) :
      (T A).det = A.det := by
    simp only [hT, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin]
  obtain ⟨δ, hδ, hδ0, hδ1, hδdet⟩ :=
    Matrix.exists_contDiff_det_pos (T.symm L) (by simpa only [← hdet, T.apply_symm_apply] using hL)
  refine ⟨fun t => T (δ t), T.contDiff.comp hδ, ?_, ?_, ?_⟩
  · simp only [hδ0, hT, Matrix.toLin_one]
    rfl
  · simp only [hδ1, T.apply_symm_apply]
  · intro t
    rw [hdet]
    exact hδdet t

end ContinuousLinearMap

namespace LinearMap

/-- **The determinant keeps its sign along a segment of injective maps.** Let `f` and `g` be
linear endomorphisms of a finite-dimensional real vector space such that every map
`f + t • (g - f)` with `0 ≤ t ≤ 1` is injective. Then `f` and `g` have determinants of the same
sign. -/
theorem det_mul_det_pos_of_forall_injective {K : Type*} [AddCommGroup K] [Module ℝ K]
    [FiniteDimensional ℝ K] (f g : K →ₗ[ℝ] K)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (f + t • (g - f))) :
    0 < LinearMap.det f * LinearMap.det g := by
  classical
  let b := Module.finBasis ℝ K
  -- In the basis `b` the determinant along the segment is a polynomial in `t`, so continuous.
  have hdet (t : ℝ) : LinearMap.det (f + t • (g - f)) =
      (toMatrix b b f + t • (toMatrix b b g - toMatrix b b f)).det := by
    rw [← LinearMap.det_toMatrix b, map_add, map_smul, map_sub]
  have hcont : ContinuousOn (fun t : ℝ ↦ LinearMap.det (f + t • (g - f))) (Set.Icc 0 1) := by
    simp only [hdet]
    exact (Continuous.matrix_det (by fun_prop)).continuousOn
  -- The determinant does not vanish on the segment, so it keeps its sign there.
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, LinearMap.det (f + t • (g - f)) ≠ 0 := fun t ht h0 ↦
    LinearMap.det_eq_zero_iff_ker_ne_bot.1 h0 (LinearMap.ker_eq_bot.2 (h t ht))
  have hsign := isPreconnected_Icc.sign_eq_of_continuousOn hcont hne
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  have h₀ : f + (0 : ℝ) • (g - f) = f := by simp
  have h₁ : f + (1 : ℝ) • (g - f) = g := by simp
  rw [h₀, h₁] at hsign
  rcases (hne 0 (Set.left_mem_Icc.2 zero_le_one)).lt_or_gt with hf | hf <;> rw [h₀] at hf
  · exact mul_pos_of_neg_of_neg hf (sign_eq_neg_one_iff.1 (hsign ▸ sign_neg hf))
  · exact mul_pos hf (sign_eq_one_iff.1 (hsign ▸ sign_pos hf))

end LinearMap

namespace LinearEquiv

/-- **Isomorphisms joined by a segment of injective maps.** Let `G₀` and `G₁` be linear
isomorphisms from a finite-dimensional real vector space `K` to `Y` such that every map
`k ↦ G₀ k + t • (G₁ k - G₀ k)` with `0 ≤ t ≤ 1` is injective. Then the automorphism `G₁⁻¹ ∘ G₀` of
`K` has positive determinant. -/
theorem det_trans_symm_pos_of_forall_injective {K Y : Type*} [AddCommGroup K] [Module ℝ K]
    [FiniteDimensional ℝ K] [AddCommGroup Y] [Module ℝ Y] (G₀ G₁ : K ≃ₗ[ℝ] Y)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective fun k ↦ G₀ k + t • (G₁ k - G₀ k)) :
    0 < LinearMap.det (G₀.trans G₁.symm).toLinearMap := by
  have hpos := LinearMap.det_mul_det_pos_of_forall_injective (G₀.trans G₁.symm).toLinearMap
    LinearMap.id fun t ht k k' hkk' ↦ h t ht (G₁.symm.injective (by simpa using hkk'))
  rwa [LinearMap.det_id, mul_one] at hpos

end LinearEquiv
