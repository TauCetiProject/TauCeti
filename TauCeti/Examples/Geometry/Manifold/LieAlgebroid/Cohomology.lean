/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LieAlgebroid.Cohomology
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Geometry.Manifold.VectorField.Derivation

/-!
# Example: the rescaled tangent Lie algebroid on `ℝ`

We construct the Lie algebroid `scaledTangentReal` on `Tℝ` whose anchor is `ρ(∂_x) = x ∂_x` and
whose bracket is `[f ∂_x, g ∂_x] = x (f g' - g f') ∂_x`, and compute its degree-zero
Chevalley–Eilenberg differential `d_A f (∂_x) = x f'(x)`. Its degree-zero cocycles are precisely
the constant functions (`scaledTangentReal_extDeriv_zero_eq_zero_iff`).
-/

public section
noncomputable section

open Bundle Manifold VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti.LieAlgebroid

/-- The global unit vector field `∂_x` on `ℝ`. -/
def realUnitVectorField : Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯ :=
  ⟨fun x ↦ (NormedSpace.fromTangentSpace x).symm (1 : ℝ),
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const⟩

/-- Under `NormedSpace.fromTangentSpace`, `realUnitVectorField` takes the value `1`
at every point. -/
theorem realUnitVectorField_apply (x : ℝ) :
    realUnitVectorField x = (NormedSpace.fromTangentSpace x).symm (1 : ℝ) := (rfl)

local notation "VFℝ" => Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯
local notation "C∞ℝ" => C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯

private def realFieldCoord (u : VFℝ) : C∞ℝ :=
  ⟨fun x ↦ NormedSpace.fromTangentSpace x (u x),
    (contMDiff_vectorSpace_iff_contDiff.mp u.contMDiff).contMDiff⟩

@[simp] private theorem realFieldCoord_apply (u : VFℝ) (x : ℝ) :
    realFieldCoord u x = NormedSpace.fromTangentSpace x (u x) := (rfl)

private theorem eq_realFieldCoord_smul (u : VFℝ) :
    u = realFieldCoord u • realUnitVectorField := by
  ext x; apply (NormedSpace.fromTangentSpace x).injective
  simp [ContMDiffSection.smul_apply, realUnitVectorField_apply]

private theorem tangent_anchorDeriv_realUnitVectorField (g : C∞ℝ) :
    (tangent 𝓘(ℝ, ℝ) ℝ).anchorDeriv realUnitVectorField g = lineDerivation ℝ 1 g := by
  ext x; simp [anchorDeriv_apply, mvfderiv_eq_fderiv, realUnitVectorField_apply,
    lineDerivation_apply_apply]

private theorem tangent_real_bracket_eq (u v : VFℝ) :
    (tangent 𝓘(ℝ, ℝ) ℝ).bracket u v =
      (realFieldCoord u * lineDerivation ℝ 1 (realFieldCoord v) -
        realFieldCoord v * lineDerivation ℝ 1 (realFieldCoord u)) • realUnitVectorField := by
  have hskew (a b : VFℝ) : (tangent 𝓘(ℝ, ℝ) ℝ).bracket a b = -(tangent 𝓘(ℝ, ℝ) ℝ).bracket b a :=
    ContMDiffSection.ext fun x ↦ by
      rw [tangent_bracket_apply, ContMDiffSection.coe_neg, Pi.neg_apply, tangent_bracket_apply,
        VectorField.mlieBracket_swap_apply]
  conv_lhs => rw [eq_realFieldCoord_smul u, eq_realFieldCoord_smul v]
  simp only [(tangent 𝓘(ℝ, ℝ) ℝ).bracket_smul_right, hskew (_ • _) _,
    (tangent 𝓘(ℝ, ℝ) ℝ).bracket_self, (tangent 𝓘(ℝ, ℝ) ℝ).anchorDeriv_smul_left,
    tangent_anchorDeriv_realUnitVectorField]; module

/-- The Lie algebroid on `Tℝ` with rescaled anchor `ρ(∂_x) = x ∂_x` and bracket
`[f ∂_x, g ∂_x] = x (f g' - g f') ∂_x`. -/
def scaledTangentReal : LieAlgebroid 𝓘(ℝ, ℝ) ℝ (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _) where
  anchor := (ContMDiffMap.id : C∞ℝ) • (tangent 𝓘(ℝ, ℝ) ℝ).anchor
  bracket := LinearMap.mk₂ ℝ (fun u v ↦ (ContMDiffMap.id : C∞ℝ) • (tangent 𝓘(ℝ, ℝ) ℝ).bracket u v)
    (fun _ _ _ ↦ by simp [map_add, smul_add]) (fun c _ _ ↦ by simp [smul_comm c])
    (fun _ _ _ ↦ by simp [map_add, smul_add]) (fun c _ _ ↦ by simp [smul_comm c])
  bracket_self _ := by simp [(tangent 𝓘(ℝ, ℝ) ℝ).bracket_self]
  bracket_bracket u v w := by
    have hmul (f : C∞ℝ) : realFieldCoord (f • realUnitVectorField) = f := by
      ext y; simp [ContMDiffSection.smul_apply, realUnitVectorField_apply]
    simp only [LinearMap.mk₂_apply, tangent_real_bracket_eq, ← mul_smul, hmul, ← add_smul,
      Derivation.leibniz, map_sub, smul_eq_mul]; congr 1; ring
  bracket_smul_apply u v f x := by
    simp only [LinearMap.mk₂_apply, ContMDiffSection.smul_apply,
      (tangent 𝓘(ℝ, ℝ) ℝ).bracket_smul_apply, tangent_anchor_apply, FunLike.coe_smul,
      Pi.smul_apply, map_smul]; simp only [ContMDiffMap.id, ContMDiffMap.coeFn_mk, id_eq]; module

@[simp] theorem scaledTangentReal_anchor_apply (x : ℝ) (v : TangentSpace 𝓘(ℝ, ℝ) x) :
    scaledTangentReal.anchor x v = x • v := by
  dsimp only [scaledTangentReal]; rw [ContMDiffSection.smul_apply, ContMDiffMap.id,
    ContMDiffMap.coeFn_mk, id_eq, FunLike.coe_smul, Pi.smul_apply, tangent_anchor_apply]

/-- The Lie bracket of `scaledTangentReal` rescales the vector-field Lie bracket by `x`. -/
theorem scaledTangentReal_bracket (u v : VFℝ) :
    scaledTangentReal.bracket u v = (ContMDiffMap.id : C∞ℝ) • (tangent 𝓘(ℝ, ℝ) ℝ).bracket u v := by
  simp [scaledTangentReal]

@[simp] theorem scaledTangentReal_bracket_apply (u v : VFℝ) (x : ℝ) :
    scaledTangentReal.bracket u v x = x • mlieBracket 𝓘(ℝ, ℝ) u v x := by
  rw [scaledTangentReal_bracket, ContMDiffSection.smul_apply, ContMDiffMap.id,
    ContMDiffMap.coeFn_mk, id_eq, tangent_bracket_apply]

/-- Degree-zero Chevalley–Eilenberg differential on `scaledTangentReal`:
`d_A f (∂_x) = x f'(x)`. -/
theorem scaledTangentReal_extDeriv_zero_apply (f : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯) (x : ℝ) :
    (scaledTangentReal.extDeriv 0 (scaledTangentReal.cochainZeroEquiv.symm f)) x
        ![realUnitVectorField x] = x * fderiv ℝ f x 1 := by
  rw [scaledTangentReal.extDeriv_zero_apply, LinearEquiv.apply_symm_apply,
    scaledTangentReal_anchor_apply, map_smul, smul_eq_mul, mvfderiv_eq_fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, realUnitVectorField_apply,
    ContinuousLinearEquiv.apply_symm_apply]

/-- `d_A x` on `scaledTangentReal` evaluates on `∂_x` to `x` and vanishes at `0`. -/
theorem scaledTangentReal_extDeriv_zero_id (x : ℝ) :
    (scaledTangentReal.extDeriv 0 (scaledTangentReal.cochainZeroEquiv.symm ContMDiffMap.id)) x
        ![realUnitVectorField x] = x := by
  rw [scaledTangentReal_extDeriv_zero_apply, ContMDiffMap.id, ContMDiffMap.coeFn_mk, fderiv_id,
    ContinuousLinearMap.id_apply, mul_one]

/-- Degree-zero cocycles of `scaledTangentReal` on `ℝ` are precisely the constant functions. -/
theorem scaledTangentReal_extDeriv_zero_eq_zero_iff (η : scaledTangentReal.Cochain 0) :
    scaledTangentReal.extDeriv 0 η = 0 ↔
      ∃ c : ℝ, η = scaledTangentReal.cochainZeroEquiv.symm (ContMDiffMap.const c) := by
  constructor
  · intro hη
    let f := scaledTangentReal.cochainZeroEquiv η
    have hηf : η = scaledTangentReal.cochainZeroEquiv.symm f :=
      (scaledTangentReal.cochainZeroEquiv.symm_apply_apply η).symm
    have hcompl : ∀ x ∈ ({0}ᶜ : Set ℝ), lineDerivation ℝ (1 : ℝ) f x = 0 := fun x hx ↦ by
      have hx' := congr($hη x ![realUnitVectorField x])
      rw [hηf, scaledTangentReal_extDeriv_zero_apply, ← lineDerivation_apply_apply] at hx'
      exact (mul_eq_zero.mp hx').resolve_left hx
    have hfderiv (x : ℝ) : fderiv ℝ f x = 0 := by
      ext; rw [← lineDerivation_apply_apply]
      exact congr_fun ((lineDerivation ℝ (1 : ℝ) f).contMDiff.continuous.ext_on
        (dense_compl_singleton (0 : ℝ)) continuous_const hcompl) x
    refine ⟨f 0, ?_⟩; rw [hηf]; congr 1; ext x
    exact is_const_of_fderiv_eq_zero (f.contMDiff.contDiff.differentiable (by simp)) hfderiv x 0
  · rintro ⟨c, rfl⟩
    refine ContMDiffSection.ext_of_interior fun a ↦ scaledTangentReal.cochainZeroEquiv.injective ?_
    simp [anchorDeriv_const_right]

end TauCeti.LieAlgebroid
