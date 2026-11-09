/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
public import TauCeti.Geometry.Symplectic.Lagrangian.Opens

/-!
# Transport and localization of Lagrangian immersions

Lagrangian immersions are preserved and reflected by diffeomorphisms of the source and
symplectomorphisms of the target. They also restrict to arbitrary open submanifolds of the
source or target. The source restriction criterion retains the explicit half-dimension
condition, including for an empty open set. Consequently the condition is local on any open
cover once this dimension condition is imposed.

None of these results requires the immersion to be injective, the ambient form to be closed,
or the source to be nonempty.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Section 3.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public noncomputable section

open Manifold Module TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {f : N → M}

section Reparametrization

variable {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J ∞ P]

/-- Reparametrizing by a diffeomorphism preserves and reflects Lagrangian immersions,
including their possible self-intersections. -/
@[simp]
theorem _root_.Diffeomorph.isLagrangianImmersion_comp_diffeomorph_iff
    (φ : P ≃ₘ⟮J, J⟯ N) :
    hσ.IsLagrangianImmersion J (f ∘ φ) ↔ hσ.IsLagrangianImmersion J f := by
  constructor
  · intro h
    exact ⟨(TauCeti.isImmersion_comp_diffeomorph_iff φ).mp h.isImmersion,
      (isIsotropicMap_comp_diffeomorph_iff φ (by simp)).mp h.isIsotropicMap,
      h.two_mul_finrank⟩
  · intro h
    exact ⟨TauCeti.isImmersion_comp_diffeomorph φ h.isImmersion,
      (isIsotropicMap_comp_diffeomorph_iff φ (by simp)).mpr h.isIsotropicMap,
      h.two_mul_finrank⟩

end Reparametrization

section Transport

variable {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂] [IsManifold I ∞ M₂]
  {σ₂ : SmoothTwoForm I M₂} {hσ₂ : σ₂.IsNondegenerate}

omit [IsManifold J ∞ N] in
/-- A diffeomorphism pulling the target form back to the source form preserves and reflects
Lagrangian immersions. -/
theorem _root_.Diffeomorph.isLagrangianImmersion_diffeomorph_comp_iff
    (ψ : M ≃ₘ⟮I, I⟯ M₂) (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) :
    hσ₂.IsLagrangianImmersion J (ψ ∘ f) ↔ hσ.IsLagrangianImmersion J f := by
  constructor
  · intro h
    exact ⟨(TauCeti.isImmersion_diffeomorph_comp_iff ψ).mp h.isImmersion,
      (isIsotropicMap_diffeomorph_comp_iff ψ hψ).mp h.isIsotropicMap,
      h.two_mul_finrank⟩
  · intro h
    exact ⟨h.isImmersion.comp_diffeomorph ψ,
      (isIsotropicMap_diffeomorph_comp_iff ψ hψ).mpr h.isIsotropicMap,
      h.two_mul_finrank⟩

end Transport

section Source

variable (hσ) in
/-- Restriction to an open source is Lagrangian exactly when the map is an isotropic
immersion at its points and the source model has half the ambient dimension. In particular,
an empty restriction still retains the dimension condition. -/
theorem isLagrangianImmersion_comp_subtype_val_iff (U : Opens N) :
    hσ.IsLagrangianImmersion J (f ∘ (Subtype.val : U → N)) ↔
      (∀ x ∈ U, IsImmersionAt J I ∞ f x) ∧
        (∀ x ∈ U, (hσ.symplecticFormAt (f x)).IsIsotropic
          (LinearMap.range (mfderiv J I f x).toLinearMap)) ∧
        2 * finrank ℝ F = finrank ℝ E := by
  have hi := TauCeti.isImmersion_comp_subtypeVal_iff (n := ∞) (I := J) (J := I) (f := f) (U := U)
  constructor
  · intro h
    exact ⟨hi.mp h.isImmersion,
      (hσ.isIsotropicMap_comp_subtype_val_iff U (fun x hx ↦
        (hi.mp h.isImmersion x hx).contMDiffAt.mdifferentiableAt (by simp))).mp
          h.isIsotropicMap,
      h.two_mul_finrank⟩
  · rintro ⟨himm, hiso, hdim⟩
    exact ⟨hi.mpr himm, (hσ.isIsotropicMap_comp_subtype_val_iff U (fun x hx ↦
      (himm x hx).contMDiffAt.mdifferentiableAt (by simp))).mpr hiso, hdim⟩

/-- A Lagrangian immersion restricts to every open subset of its source. -/
theorem IsLagrangianImmersion.comp_subtype_val (h : hσ.IsLagrangianImmersion J f)
    (U : Opens N) : hσ.IsLagrangianImmersion J (f ∘ (Subtype.val : U → N)) := by
  apply (hσ.isLagrangianImmersion_comp_subtype_val_iff U).mpr
  exact ⟨fun x _ ↦ h.isImmersion.isImmersionAt x,
    fun x _ ↦ isIsotropicMap_iff_forall.mp h.isIsotropicMap x,
    h.two_mul_finrank⟩

variable (hσ) in
/-- Lagrangian immersions can be checked on an arbitrary open cover. The explicit dimension
condition also handles an empty source covered by an empty family. -/
theorem isLagrangianImmersion_iff_of_isOpenCover {ι : Type*} {U : ι → Opens N}
    (hU : IsOpenCover U) (hdim : 2 * finrank ℝ F = finrank ℝ E) :
    hσ.IsLagrangianImmersion J f ↔
      ∀ i, hσ.IsLagrangianImmersion J (f ∘ (Subtype.val : U i → N)) := by
  refine ⟨fun h i ↦ h.comp_subtype_val (U i), fun h ↦ ?_⟩
  have himm := (TauCeti.isImmersion_iff_of_isOpenCover hU).mpr fun i ↦ (h i).isImmersion
  refine ⟨himm, ?_, hdim⟩
  exact (hσ.isIsotropicMap_iff_of_isOpenCover
    (himm.contMDiff.mdifferentiable (by simp)) hU).mpr fun i ↦ (h i).isIsotropicMap

end Source

section Target

variable {U : Opens M} {g : N → U}

omit [IsManifold J ∞ N] in
/-- A map into an open submanifold is a Lagrangian immersion for the restricted form
exactly when its ambient inclusion is a Lagrangian immersion. -/
@[simp]
theorem isLagrangianImmersion_subtype_val_comp_iff :
    hσ.IsLagrangianImmersion J ((Subtype.val : U → M) ∘ g) ↔
      (hσ.mpullback_subtype_val U).IsLagrangianImmersion J g := by
  have hi := TauCeti.isImmersion_subtypeVal_comp_iff (n := ∞) (I := J) (J := I) (g := g)
  constructor
  · intro h
    have hg := hi.mp h.isImmersion
    exact ⟨hg, (hσ.isIsotropicMap_subtype_val_comp_iff
      (hg.contMDiff.mdifferentiable (by simp))).mp h.isIsotropicMap, h.two_mul_finrank⟩
  · intro h
    exact ⟨hi.mpr h.isImmersion, (hσ.isIsotropicMap_subtype_val_comp_iff
      (h.isImmersion.contMDiff.mdifferentiable (by simp))).mpr h.isIsotropicMap,
      h.two_mul_finrank⟩

end Target

end TauCeti.SmoothTwoForm.IsNondegenerate
