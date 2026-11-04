/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Reflection
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace

/-!
# Reflected quadratic-form bounds

Centering between two form bounds and reflecting across the invariant upper subspace
gives the quadratic-form lower bound `(b - a) / 2`. A positive gap therefore gives uniform
coercivity. Together with reflection anticommutation, this is the quarter-angle input.

Adapted from `DavisKahan/InfiniteDimensional/TanTwoTheta/QuarterAcuteFormGap.lean`
in the Kitware DKPS formalization (Jon Crall, OpenAI GPT-5.6 Thinking and Claude Opus 5;
Apache-2.0). No completeness or finite-dimensionality is required here.
-/

public section

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The reflected centered operator has quadratic-form lower bound `(b - a) / 2`. -/
theorem reflection_centered_form_lower
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (A : E →L[𝕜] E)
    (hA : A.toLinearMap.IsSymmetric) (hAU : ∀ x ∈ U, A x ∈ U)
    {a b : ℝ}
    (hUhigh : ∀ x ∈ U,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUperpLow : ∀ x ∈ Uᗮ,
      RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (x : E) :
    (b - a) / 2 * ‖x‖ ^ 2 ≤
      RCLike.re ⟪((U.reflection : E →L[𝕜] E) ∘L
        (A - (((a + b) / 2 : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E)) x, x⟫_𝕜 := by
  have hUperp : ∀ y ∈ Uᗮ, A y ∈ Uᗮ := by
    intro y hy
    exact LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule hA (p := U) hAU hy
  let p : E := U.starProjection x
  let m : E := x - U.starProjection x
  have hp : p ∈ U := U.starProjection_apply_mem x
  have hm : m ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
  have hxpm : x = p + m := by simp only [p, m]; abel
  have hAp : A p - (((a + b) / 2 : ℝ) : 𝕜) • p ∈ U :=
    U.sub_mem (hAU p hp) (U.smul_mem _ hp)
  have hAm : A m - (((a + b) / 2 : ℝ) : 𝕜) • m ∈ Uᗮ :=
    Uᗮ.sub_mem (hUperp m hm) (Uᗮ.smul_mem _ hm)
  have hsplit :
      A x - (((a + b) / 2 : ℝ) : 𝕜) • x =
        (A p - (((a + b) / 2 : ℝ) : 𝕜) • p) +
        (A m - (((a + b) / 2 : ℝ) : 𝕜) • m) := by
    rw [hxpm, map_add, smul_add]
    module
  have hJAp :
      (U.reflection : E →L[𝕜] E) (A p - (((a + b) / 2 : ℝ) : 𝕜) • p) =
        A p - (((a + b) / 2 : ℝ) : 𝕜) • p := by
    simpa only [LinearIsometryEquiv.coe_coe''] using U.reflection_mem_subspace_eq_self hAp
  have hJAm :
      (U.reflection : E →L[𝕜] E) (A m - (((a + b) / 2 : ℝ) : 𝕜) • m) =
        -(A m - (((a + b) / 2 : ℝ) : 𝕜) • m) := by
    simpa only [LinearIsometryEquiv.coe_coe''] using
      U.reflection_mem_subspace_orthogonalComplement_eq_neg hAm
  have hreflect :
      (U.reflection : E →L[𝕜] E)
          (A x - (((a + b) / 2 : ℝ) : 𝕜) • x) =
        (A p - (((a + b) / 2 : ℝ) : 𝕜) • p) -
        (A m - (((a + b) / 2 : ℝ) : 𝕜) • m) := by
    rw [hsplit, map_add, hJAp, hJAm]
    module
  have hAp_m :
      ⟪A p - (((a + b) / 2 : ℝ) : 𝕜) • p, m⟫_𝕜 = 0 :=
    Submodule.inner_right_of_mem_orthogonal hAp hm
  have hAm_p :
      ⟪A m - (((a + b) / 2 : ℝ) : 𝕜) • m, p⟫_𝕜 = 0 :=
    Submodule.inner_left_of_mem_orthogonal hp hAm
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, smul_apply]
  rw [hreflect, hxpm, inner_sub_left, inner_add_right,
    inner_add_right, hAp_m, hAm_p]
  simp only [add_zero, zero_add, inner_sub_left, inner_smul_left, map_sub]
  have hpBound := hUhigh p hp
  have hmBound := hUperpLow m hm
  have hpyth := (Submodule.norm_sq_eq_add_norm_sq_starProjection x U).symm
  rw [Submodule.starProjection_orthogonal_val] at hpyth
  -- Name the projection components in the native Pythagoras identity.
  change ‖p‖ ^ 2 + ‖m‖ ^ 2 = ‖x‖ ^ 2 at hpyth
  have hnormpm : ‖p + m‖ ^ 2 = ‖x‖ ^ 2 := by rw [← hxpm]
  simp only [RCLike.conj_ofReal, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  rw [hnormpm]
  calc
    (b - a) / 2 * ‖x‖ ^ 2 =
        (b - a) / 2 * (‖p‖ ^ 2 + ‖m‖ ^ 2) := by rw [hpyth]
    _ = (b * ‖p‖ ^ 2 - (a + b) / 2 * ‖p‖ ^ 2) +
        ((a + b) / 2 * ‖m‖ ^ 2 - a * ‖m‖ ^ 2) := by ring
    _ ≤ (RCLike.re ⟪A p, p⟫_𝕜 - (a + b) / 2 * ‖p‖ ^ 2) +
        ((a + b) / 2 * ‖m‖ ^ 2 - RCLike.re ⟪A m, m⟫_𝕜) :=
      add_le_add
        (sub_le_sub_right hpBound ((a + b) / 2 * ‖p‖ ^ 2))
        (sub_le_sub_left hmBound ((a + b) / 2 * ‖m‖ ^ 2))
    _ = RCLike.re ⟪A p, p⟫_𝕜 - (a + b) / 2 * ‖p‖ ^ 2 -
        (RCLike.re ⟪A m, m⟫_𝕜 - (a + b) / 2 * ‖m‖ ^ 2) := by ring

end Submodule
