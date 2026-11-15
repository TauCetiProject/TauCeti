/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import TauCeti.Analysis.Normed.Module.ContinuousInverse
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorField.Immersion

/-!
# Sections of the tangent bundle of the unit sphere from ambient maps

The differential of the inclusion `ι : Sⁿ → E` identifies each tangent space `TangentSpace (𝓡 n) x`
of the unit sphere `Sⁿ` of a real inner product space `E` of dimension `n + 1` isometrically with
the hyperplane `(ℝ ∙ (x : E))ᗮ` (`TauCeti.sphereTangentEquiv`). Pointwise, any ambient map
`w : sphere (0 : E) 1 → E` orthogonal to the position vector (`∀ x, ⟪w x, (x : E)⟫ = 0`) therefore
determines a unique section `TauCeti.sphereTangentSection n w hw` of the tangent bundle of `Sⁿ`
whose image under `dι` is `w`.

Because `ι` is analytic with split-injective differential everywhere, this pointwise bijection
preserves regularity at every order `m : ℕ∞ω`: `TauCeti.sphereTangentSection n w hw` is `C^m` into
`TangentBundle (𝓡 n) (sphere (0 : E) 1)` if and only if `w` is `C^m` into `E`
(`TauCeti.contMDiff_sphereTangentSection_iff`), and in particular continuous if and only if `w` is
continuous (`TauCeti.continuous_sphereTangentSection_iff`).

## Main definitions

* `TauCeti.sphereTangentSection`: the section of the tangent bundle of `Sⁿ` corresponding to an
  ambient map `w : sphere (0 : E) 1 → E` satisfying `∀ x, ⟪w x, (x : E)⟫ = 0`.

## Main statements

* `TauCeti.mvfderiv_subtypeVal_sphereTangentSection`,
  `TauCeti.mfderiv_subtypeVal_sphereTangentSection`: the differential of the inclusion sends
  `sphereTangentSection n w hw x` back to `w x`.
* `TauCeti.norm_sphereTangentSection`, `TauCeti.sphereTangentSection_eq_zero_iff`: its round norm
  is `‖w x‖`, so it vanishes at `x` exactly when `w x = 0`.
* `TauCeti.sphereTangentSection_mvfderiv_subtypeVal`: every section `V` is recovered from its
  ambient image `x ↦ mvfderiv (𝓡 n) Subtype.val x (V x)`.
* `TauCeti.continuous_mvfderiv_subtypeVal_sphere_section`: pushing a continuous section forward by
  `dι` gives a continuous map into `E`.
* `TauCeti.contMDiff_sphereTangentSection_iff`, `TauCeti.continuous_sphereTangentSection_iff`:
  `sphereTangentSection n w hw` is `C^m` (respectively continuous) if and only if `w` is.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 8
  (tangent vector fields to embedded submanifolds).
-/

public section

open Bundle Metric Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section ExplicitDim

variable (n : ℕ) [Fact (finrank ℝ E = n + 1)]

/-- The section of the tangent bundle of the unit sphere `Sⁿ` determined by an ambient map
`w : sphere (0 : E) 1 → E` orthogonal to the radius vector at every point. -/
def sphereTangentSection (w : sphere (0 : E) 1 → E)
    (hw : ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0) (x : sphere (0 : E) 1) :
    TangentSpace (𝓡 n) x :=
  (sphereTangentEquiv (n := n) x).symm
    ⟨w x, Submodule.mem_orthogonal_singleton_iff_inner_left.2 (hw x)⟩

/-- Defining formula for `TauCeti.sphereTangentSection` through `TauCeti.sphereTangentEquiv`. -/
theorem sphereTangentSection_def (w : sphere (0 : E) 1 → E)
    (hw : ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0) (x : sphere (0 : E) 1) :
    sphereTangentSection n w hw x =
      (sphereTangentEquiv (n := n) x).symm
        ⟨w x, Submodule.mem_orthogonal_singleton_iff_inner_left.2 (hw x)⟩ :=
  (rfl)

/-- `TauCeti.sphereTangentEquiv` sends `TauCeti.sphereTangentSection n w hw x` to `w x` in
`(x : E)ᗮ`. -/
theorem coe_sphereTangentEquiv_sphereTangentSection (w : sphere (0 : E) 1 → E)
    (hw : ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0) (x : sphere (0 : E) 1) :
    (sphereTangentEquiv (n := n) x (sphereTangentSection n w hw x) : E) = w x := by
  rw [sphereTangentSection_def, LinearIsometryEquiv.apply_symm_apply]

/-- The manifold differential of the sphere inclusion sends `TauCeti.sphereTangentSection n w hw x`
to `w x`. -/
@[simp]
theorem mfderiv_subtypeVal_sphereTangentSection (w : sphere (0 : E) 1 → E)
    (hw : ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0) (x : sphere (0 : E) 1) :
    mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (sphereTangentSection n w hw x) = w x := by
  rw [← coe_sphereTangentEquiv_apply, coe_sphereTangentEquiv_sphereTangentSection]

/-- The vector-valued differential `mvfderiv` of the sphere inclusion sends
`TauCeti.sphereTangentSection n w hw x` to `w x`. -/
theorem mvfderiv_subtypeVal_sphereTangentSection (w : sphere (0 : E) 1 → E)
    (hw : ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0) (x : sphere (0 : E) 1) :
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (sphereTangentSection n w hw x) = w x := by
  rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_subtypeVal_sphereTangentSection]

/-- For the round metric, `TauCeti.sphereTangentSection n w hw x` has norm `‖w x‖`. -/
theorem norm_sphereTangentSection (w : sphere (0 : E) 1 → E)
    (hw : ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0) (x : sphere (0 : E) 1) :
    ‖sphereTangentSection n w hw x‖ = ‖w x‖ := by
  rw [norm_tangentSpace_sphere (n := n), mvfderiv_subtypeVal_sphereTangentSection]

/-- `TauCeti.sphereTangentSection n w hw` vanishes at `x` if and only if `w x = 0`. -/
@[simp]
theorem sphereTangentSection_eq_zero_iff (w : sphere (0 : E) 1 → E)
    (hw : ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0) (x : sphere (0 : E) 1) :
    sphereTangentSection n w hw x = 0 ↔ w x = 0 := by
  rw [← norm_eq_zero, norm_sphereTangentSection, norm_eq_zero]

end ExplicitDim

section ImplicitDim

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- The ambient vector `mvfderiv (𝓡 n) Subtype.val x v` of any tangent vector to `Sⁿ` is
orthogonal to `(x : E)`. -/
theorem inner_mvfderiv_subtypeVal_sphere_coe (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v, (x : E)⟫ = 0 := by
  rw [real_inner_comm]
  exact inner_coe_mvfderiv_subtypeVal_sphere x v

/-- Every section of the tangent bundle of `Sⁿ` is recovered from its ambient image under the
differential of the inclusion. -/
@[simp]
theorem sphereTangentSection_mvfderiv_subtypeVal
    (V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x) :
    sphereTangentSection n (fun x ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (V x))
      (fun x ↦ inner_mvfderiv_subtypeVal_sphere_coe x (V x)) = V := by
  funext x
  exact injective_mvfderiv_subtypeVal_sphere x (mvfderiv_subtypeVal_sphereTangentSection n _ _ x)

/-- Pushing a continuous section of the tangent bundle of `Sⁿ` forward by the differential of the
inclusion gives a continuous map into `E`. -/
theorem continuous_mvfderiv_subtypeVal_sphere_section
    {V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (hV : Continuous (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)))) :
    Continuous (fun x ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (V x)) := by
  rw [← contMDiff_zero_iff (I := 𝓡 n) (I' := (𝓡 n).tangent)] at hV
  rw [← contMDiff_zero_iff (I := 𝓡 n) (I' := 𝓘(ℝ, E))]
  exact (contMDiff_coe_sphere (m := 1)).mvfderiv hV le_rfl

/-- `TauCeti.sphereTangentSection n w hw` is `C^m` into the tangent bundle of `Sⁿ` if and only if
`w` is `C^m` into `E`, at every regularity `m : ℕ∞ω`. -/
@[simp]
theorem contMDiff_sphereTangentSection_iff {m : ℕ∞ω} (w : sphere (0 : E) 1 → E)
    (hw : ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0) :
    ContMDiff (𝓡 n) (𝓡 n).tangent m
        (fun x ↦ (⟨x, sphereTangentSection n w hw x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ↔
      ContMDiff (𝓡 n) 𝓘(ℝ, E) m w := by
  constructor
  · intro h
    simpa only [mvfderiv_subtypeVal_sphereTangentSection] using
      (contMDiff_coe_sphere (m := ω)).mvfderiv h le_top
  · intro h x
    have hinj : (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x).HasLeftInverse :=
      .of_injective_of_finiteDimensional_domain fun v₁ v₂ hv ↦
        injective_mvfderiv_subtypeVal_sphere x <| by
          rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply]
          exact hv
    have hpair : ContMDiff (𝓡 n) 𝓘(ℝ, E).tangent m (fun y : sphere (0 : E) 1 ↦ ((y : E), w y)) :=
      contMDiff_coe_sphere.prodMk h
    rw [chartedSpaceSelf_prod] at hpair
    have htot : ContMDiff (𝓡 n) 𝓘(ℝ, E).tangent m
        (fun y : sphere (0 : E) 1 ↦
          (⟨(y : E), mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) y
            (sphereTangentSection n w hw y)⟩ : TangentBundle 𝓘(ℝ, E) E)) := by
      refine (contMDiff_tangentBundleModelSpaceHomeomorph_symm.comp hpair).congr fun y ↦ ?_
      simp only [tangentBundleModelSpaceHomeomorph_coe_symm, TotalSpace.toProd,
        mfderiv_subtypeVal_sphereTangentSection]
      rfl
    exact (contMDiff_coe_sphere (m := ω) x).vectorField_of_mfderiv le_top hinj (htot x)

/-- `TauCeti.sphereTangentSection n w hw` is a continuous section of the tangent bundle of `Sⁿ` if
and only if `w` is continuous. -/
@[simp]
theorem continuous_sphereTangentSection_iff (w : sphere (0 : E) 1 → E)
    (hw : ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0) :
    Continuous
        (fun x ↦ (⟨x, sphereTangentSection n w hw x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ↔
      Continuous w := by
  rw [← contMDiff_zero_iff (I := 𝓡 n) (I' := (𝓡 n).tangent),
    ← contMDiff_zero_iff (I := 𝓡 n) (I' := 𝓘(ℝ, E)), contMDiff_sphereTangentSection_iff]

end ImplicitDim

end TauCeti
