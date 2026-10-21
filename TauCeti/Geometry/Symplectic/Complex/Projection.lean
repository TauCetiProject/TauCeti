/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Complexification
public import TauCeti.LinearAlgebra.Complex.Conjugation

/-!
# Type projections of an almost complex structure

The complexification of a real almost complex structure `J` splits into its `i`- and
`-i`-eigenspaces. The projections onto these summands are `(1 - i J) / 2` and
`(1 + i J) / 2`, respectively. We use Mathlib's submodule projections, so their images and
kernels are the existing eigenspaces, rather than new carriers for the type components.

Conjugation exchanges the projections, and scalar extension of a map intertwining almost
complex structures commutes with both. The pure-tensor formulas fix the normalization of
`v ↦ v^(1,0)`; its restriction to the real vectors is injective. These are the fibrewise
operations for complex tangent type decompositions.

The conventions follow Demailly, *Complex Analytic and Differential Geometry*, Chapter I,
the decomposition of the complexified tangent space of an almost complex manifold.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti.AlmostComplexStructure

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Projection onto the `(1,0)` vectors, along the `(0,1)` vectors, in the complexification. -/
def holomorphicProjection (J : AlmostComplexStructure V) :
    (ℂ ⊗[ℝ] V) →ₗ[ℂ] (ℂ ⊗[ℝ] V) :=
  (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I).projection
    (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I))
    J.isCompl_eigenspace_baseChange_I_neg_I

/-- Projection onto the `(0,1)` vectors, along the `(1,0)` vectors, in the complexification. -/
def antiholomorphicProjection (J : AlmostComplexStructure V) :
    (ℂ ⊗[ℝ] V) →ₗ[ℂ] (ℂ ⊗[ℝ] V) :=
  (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I)).projection
    (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I)
    J.isCompl_eigenspace_baseChange_I_neg_I.symm

/-- The holomorphic projection is the native projection onto the positive eigenspace. -/
theorem holomorphicProjection_def (J : AlmostComplexStructure V) :
    J.holomorphicProjection =
      (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I).projection
        (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I))
        J.isCompl_eigenspace_baseChange_I_neg_I :=
  (rfl)

/-- The antiholomorphic projection is the native projection onto the negative eigenspace. -/
theorem antiholomorphicProjection_def (J : AlmostComplexStructure V) :
    J.antiholomorphicProjection =
      (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I)).projection
        (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I)
        J.isCompl_eigenspace_baseChange_I_neg_I.symm :=
  (rfl)

/-- Every complexified vector is the sum of its two type components. -/
theorem holomorphicProjection_add_antiholomorphicProjection (J : AlmostComplexStructure V)
    (u : ℂ ⊗[ℝ] V) : J.holomorphicProjection u + J.antiholomorphicProjection u = u :=
  Submodule.projection_add_projection_eq_self J.isCompl_eigenspace_baseChange_I_neg_I u

/-- The antiholomorphic component is the complement of the holomorphic component. -/
theorem antiholomorphicProjection_apply_eq_sub (J : AlmostComplexStructure V)
    (u : ℂ ⊗[ℝ] V) : J.antiholomorphicProjection u = u - J.holomorphicProjection u :=
  Submodule.projection_eq_self_sub_projection J.isCompl_eigenspace_baseChange_I_neg_I u

/-- The explicit `(1,0)` projection is `(u - i J u) / 2`. -/
theorem holomorphicProjection_apply (J : AlmostComplexStructure V) (u : ℂ ⊗[ℝ] V) :
    J.holomorphicProjection u =
      (2 : ℂ)⁻¹ • (u - Complex.I • J.toLinearMap.baseChange ℂ u) := by
  rw [holomorphicProjection_def]
  exact projection_eigenspace_I_neg_I_apply _ J.baseChange_comp_self u

/-- The explicit `(0,1)` projection is `(u + i J u) / 2`. -/
theorem antiholomorphicProjection_apply (J : AlmostComplexStructure V) (u : ℂ ⊗[ℝ] V) :
    J.antiholomorphicProjection u =
      (2 : ℂ)⁻¹ • (u + Complex.I • J.toLinearMap.baseChange ℂ u) := by
  rw [antiholomorphicProjection_def]
  exact projection_eigenspace_neg_I_I_apply _ J.baseChange_comp_self u

@[simp]
theorem range_holomorphicProjection (J : AlmostComplexStructure V) :
    LinearMap.range J.holomorphicProjection =
      Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I :=
  Submodule.range_projection _

@[simp]
theorem range_antiholomorphicProjection (J : AlmostComplexStructure V) :
    LinearMap.range J.antiholomorphicProjection =
      Module.End.eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I) :=
  Submodule.range_projection _

/-- The holomorphic component lies in the `i`-eigenspace of the complexified structure. -/
theorem holomorphicProjection_apply_mem (J : AlmostComplexStructure V) (u : ℂ ⊗[ℝ] V) :
    J.holomorphicProjection u ∈ Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I :=
  Submodule.projection_apply_mem J.isCompl_eigenspace_baseChange_I_neg_I u

/-- The antiholomorphic component lies in the `-i`-eigenspace of the complexified structure. -/
theorem antiholomorphicProjection_apply_mem (J : AlmostComplexStructure V) (u : ℂ ⊗[ℝ] V) :
    J.antiholomorphicProjection u ∈
      Module.End.eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I) :=
  Submodule.projection_apply_mem J.isCompl_eigenspace_baseChange_I_neg_I.symm u

/-- The complexified structure acts by `i` on the holomorphic component. -/
@[simp]
theorem baseChange_apply_holomorphicProjection (J : AlmostComplexStructure V) (u : ℂ ⊗[ℝ] V) :
    J.toLinearMap.baseChange ℂ (J.holomorphicProjection u) =
      Complex.I • J.holomorphicProjection u :=
  Module.End.mem_eigenspace_iff.mp (J.holomorphicProjection_apply_mem u)

/-- The complexified structure acts by `-i` on the antiholomorphic component. -/
@[simp]
theorem baseChange_apply_antiholomorphicProjection (J : AlmostComplexStructure V)
    (u : ℂ ⊗[ℝ] V) : J.toLinearMap.baseChange ℂ (J.antiholomorphicProjection u) =
      -Complex.I • J.antiholomorphicProjection u :=
  Module.End.mem_eigenspace_iff.mp (J.antiholomorphicProjection_apply_mem u)

@[simp]
theorem ker_holomorphicProjection (J : AlmostComplexStructure V) :
    LinearMap.ker J.holomorphicProjection =
      Module.End.eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I) :=
  Submodule.ker_projection _

@[simp]
theorem ker_antiholomorphicProjection (J : AlmostComplexStructure V) :
    LinearMap.ker J.antiholomorphicProjection =
      Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I :=
  Submodule.ker_projection _

/-- A vector is of type `(1,0)` exactly when the holomorphic projection fixes it. -/
@[simp]
theorem holomorphicProjection_eq_self_iff (J : AlmostComplexStructure V) (u : ℂ ⊗[ℝ] V) :
    J.holomorphicProjection u = u ↔ J.toLinearMap.baseChange ℂ u = Complex.I • u := by
  rw [holomorphicProjection_def, Submodule.projection_eq_self_iff,
    Module.End.mem_eigenspace_iff]

/-- A vector is of type `(0,1)` exactly when the antiholomorphic projection fixes it. -/
@[simp]
theorem antiholomorphicProjection_eq_self_iff (J : AlmostComplexStructure V) (u : ℂ ⊗[ℝ] V) :
    J.antiholomorphicProjection u = u ↔ J.toLinearMap.baseChange ℂ u = -Complex.I • u := by
  rw [antiholomorphicProjection_def, Submodule.projection_eq_self_iff,
    Module.End.mem_eigenspace_iff]

@[simp]
theorem holomorphicProjection_eq_zero_iff (J : AlmostComplexStructure V) (u : ℂ ⊗[ℝ] V) :
    J.holomorphicProjection u = 0 ↔ J.toLinearMap.baseChange ℂ u = -Complex.I • u := by
  rw [holomorphicProjection_def, Submodule.projection_apply_eq_zero_iff,
    Module.End.mem_eigenspace_iff]

@[simp]
theorem antiholomorphicProjection_eq_zero_iff (J : AlmostComplexStructure V) (u : ℂ ⊗[ℝ] V) :
    J.antiholomorphicProjection u = 0 ↔ J.toLinearMap.baseChange ℂ u = Complex.I • u := by
  rw [antiholomorphicProjection_def, Submodule.projection_apply_eq_zero_iff,
    Module.End.mem_eigenspace_iff]

@[simp]
theorem holomorphicProjection_holomorphicProjection (J : AlmostComplexStructure V)
    (u : ℂ ⊗[ℝ] V) : J.holomorphicProjection (J.holomorphicProjection u) =
      J.holomorphicProjection u := by
  rw [holomorphicProjection_def]
  exact Submodule.projection_apply_of_mem_left _ (Submodule.projection_apply_mem _ u)

@[simp]
theorem antiholomorphicProjection_antiholomorphicProjection (J : AlmostComplexStructure V)
    (u : ℂ ⊗[ℝ] V) : J.antiholomorphicProjection (J.antiholomorphicProjection u) =
      J.antiholomorphicProjection u := by
  rw [antiholomorphicProjection_def]
  exact Submodule.projection_apply_of_mem_left _ (Submodule.projection_apply_mem _ u)

@[simp]
theorem holomorphicProjection_antiholomorphicProjection (J : AlmostComplexStructure V)
    (u : ℂ ⊗[ℝ] V) : J.holomorphicProjection (J.antiholomorphicProjection u) = 0 := by
  rw [holomorphicProjection_def, antiholomorphicProjection_def]
  exact Submodule.projection_apply_of_mem_right _ (Submodule.projection_apply_mem _ u)

@[simp]
theorem antiholomorphicProjection_holomorphicProjection (J : AlmostComplexStructure V)
    (u : ℂ ⊗[ℝ] V) : J.antiholomorphicProjection (J.holomorphicProjection u) = 0 := by
  rw [holomorphicProjection_def, antiholomorphicProjection_def]
  exact Submodule.projection_apply_of_mem_right _ (Submodule.projection_apply_mem _ u)

/-- On a pure tensor, the `(1,0)` projection is `(c ⊗ v - (i c) ⊗ J v) / 2`. -/
theorem holomorphicProjection_tmul (J : AlmostComplexStructure V) (c : ℂ) (v : V) :
    J.holomorphicProjection (c ⊗ₜ[ℝ] v) =
      (2 : ℂ)⁻¹ • (c ⊗ₜ[ℝ] v - (Complex.I * c) ⊗ₜ[ℝ] J v) := by
  simp [holomorphicProjection_apply, TensorProduct.smul_tmul', smul_eq_mul]

/-- On a pure tensor, the `(0,1)` projection is `(c ⊗ v + (i c) ⊗ J v) / 2`. -/
theorem antiholomorphicProjection_tmul (J : AlmostComplexStructure V) (c : ℂ) (v : V) :
    J.antiholomorphicProjection (c ⊗ₜ[ℝ] v) =
      (2 : ℂ)⁻¹ • (c ⊗ₜ[ℝ] v + (Complex.I * c) ⊗ₜ[ℝ] J v) := by
  simp [antiholomorphicProjection_apply, TensorProduct.smul_tmul', smul_eq_mul]

/-- Canonical conjugation exchanges the two type projections. -/
@[simp]
theorem tmulConj_holomorphicProjection (J : AlmostComplexStructure V) (u : ℂ ⊗[ℝ] V) :
    tmulConj V (J.holomorphicProjection u) = J.antiholomorphicProjection (tmulConj V u) := by
  rw [holomorphicProjection_apply, antiholomorphicProjection_apply]
  have htwo : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  simp [map_smulₛₗ, tmulConj_baseChange, smul_sub, htwo]

/-- Canonical conjugation exchanges the two type projections in the reverse direction. -/
@[simp]
theorem tmulConj_antiholomorphicProjection (J : AlmostComplexStructure V) (u : ℂ ⊗[ℝ] V) :
    tmulConj V (J.antiholomorphicProjection u) = J.holomorphicProjection (tmulConj V u) := by
  rw [antiholomorphicProjection_apply, holomorphicProjection_apply]
  have htwo : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  simp [map_smulₛₗ, tmulConj_baseChange, sub_eq_add_neg, htwo]

/-- Scalar extension of an intertwining map preserves the holomorphic projection. -/
theorem baseChange_holomorphicProjection (J : AlmostComplexStructure V)
    (K : AlmostComplexStructure W) (f : V →ₗ[ℝ] W) (hf : IsComplexLinearMap J K f)
    (u : ℂ ⊗[ℝ] V) :
    f.baseChange ℂ (J.holomorphicProjection u) = K.holomorphicProjection (f.baseChange ℂ u) := by
  have h := congrArg (LinearMap.baseChange ℂ) hf
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h
  rw [holomorphicProjection_apply, holomorphicProjection_apply, map_smul, map_sub,
    map_smul, ← LinearMap.comp_apply, h, LinearMap.comp_apply]

/-- Scalar extension of an intertwining map preserves the antiholomorphic projection. -/
theorem baseChange_antiholomorphicProjection (J : AlmostComplexStructure V)
    (K : AlmostComplexStructure W) (f : V →ₗ[ℝ] W) (hf : IsComplexLinearMap J K f)
    (u : ℂ ⊗[ℝ] V) :
    f.baseChange ℂ (J.antiholomorphicProjection u) =
      K.antiholomorphicProjection (f.baseChange ℂ u) := by
  rw [antiholomorphicProjection_apply_eq_sub, antiholomorphicProjection_apply_eq_sub, map_sub,
    baseChange_holomorphicProjection J K f hf]

/-- Projection to `(1,0)` vectors is injective on the embedded real vector space. -/
theorem holomorphicProjection_one_tmul_injective (J : AlmostComplexStructure V) :
    Function.Injective (fun v : V ↦ J.holomorphicProjection (1 ⊗ₜ[ℝ] v)) := by
  intro v w h
  have hc := congrArg (tmulConj V) h
  simp only [tmulConj_holomorphicProjection, tmulConj_tmul, map_one] at hc
  have hreal : (1 : ℂ) ⊗ₜ[ℝ] v = 1 ⊗ₜ[ℝ] w := by
    calc
      (1 : ℂ) ⊗ₜ[ℝ] v = J.holomorphicProjection (1 ⊗ₜ[ℝ] v) +
          J.antiholomorphicProjection (1 ⊗ₜ[ℝ] v) :=
        (J.holomorphicProjection_add_antiholomorphicProjection _).symm
      _ = J.holomorphicProjection (1 ⊗ₜ[ℝ] w) +
          J.antiholomorphicProjection (1 ⊗ₜ[ℝ] w) := congrArg₂ (· + ·) h hc
      _ = 1 ⊗ₜ[ℝ] w := J.holomorphicProjection_add_antiholomorphicProjection _
  simpa using congrArg (realPart V) hreal

end TauCeti.AlmostComplexStructure
