/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sets.OpenCover
public import TauCeti.Geometry.Manifold.MFDeriv.Opens
public import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent
public import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# Isotropic, coisotropic, Lagrangian and symplectic tangent images on open submanifolds

Restricting the source of a differentiable map to an open subset restricts its tangent-image
condition to the points of that subset. These conditions can therefore be checked on any open
cover of the source. If a map takes values in an open submanifold, its isotropic, coisotropic,
Lagrangian and symplectic tangent-image conditions for the restricted form agree with those of its
ambient inclusion.
Together these statements permit local calculations without changing the geometric condition.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Section 3.
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]
  {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)

section Source

variable {f : N → M}

/-- Isotropy of an open source restriction is precisely isotropy of the original tangent
images at the points of that open set. -/
theorem isIsotropicMap_comp_subtype_val_iff (U : Opens N)
    (hf : ∀ x ∈ U, MDifferentiableAt J I f x) :
    hσ.IsIsotropicMap J (f ∘ (Subtype.val : U → N)) ↔
      ∀ x ∈ U, (hσ.symplecticFormAt (f x)).IsIsotropic
        (LinearMap.range (mfderiv J I f x).toLinearMap) := by
  rw [isIsotropicMap_iff_forall]
  simp only [Manifold.range_mfderiv_comp_subtype_val _ (hf _ (Subtype.property _)),
    Function.comp_apply, Subtype.forall]

/-- Coisotropy of an open source restriction is precisely coisotropy of the original tangent
images at the points of that open set. -/
theorem isCoisotropicMap_comp_subtype_val_iff (U : Opens N)
    (hf : ∀ x ∈ U, MDifferentiableAt J I f x) :
    hσ.IsCoisotropicMap J (f ∘ (Subtype.val : U → N)) ↔
      ∀ x ∈ U, (hσ.symplecticFormAt (f x)).IsCoisotropic
        (LinearMap.range (mfderiv J I f x).toLinearMap) := by
  rw [isCoisotropicMap_iff]
  simp only [Manifold.range_mfderiv_comp_subtype_val _ (hf _ (Subtype.property _)),
    Function.comp_apply, Subtype.forall]

/-- The Lagrangian condition on an open source restriction is precisely the condition on the
original tangent images at the points of that open set. -/
theorem isLagrangianMap_comp_subtype_val_iff (U : Opens N)
    (hf : ∀ x ∈ U, MDifferentiableAt J I f x) :
    hσ.IsLagrangianMap J (f ∘ (Subtype.val : U → N)) ↔
      ∀ x ∈ U, (hσ.symplecticFormAt (f x)).IsLagrangian
        (LinearMap.range (mfderiv J I f x).toLinearMap) := by
  rw [isLagrangianMap_iff_forall]
  simp only [Manifold.range_mfderiv_comp_subtype_val _ (hf _ (Subtype.property _)),
    Function.comp_apply, Subtype.forall]

/-- The symplectic tangent-image condition on an open source restriction is precisely the
condition on the original tangent images at the points of that open set. -/
theorem hasSymplecticTangentImages_comp_subtype_val_iff (U : Opens N)
    (hf : ∀ x ∈ U, MDifferentiableAt J I f x) :
    hσ.HasSymplecticTangentImages J (f ∘ (Subtype.val : U → N)) ↔
      ∀ x ∈ U, (hσ.symplecticFormAt (f x)).IsSymplectic
        (LinearMap.range (mfderiv J I f x).toLinearMap) := by
  rw [hasSymplecticTangentImages_iff_forall]
  simp only [Manifold.range_mfderiv_comp_subtype_val _ (hf _ (Subtype.property _)),
    Function.comp_apply, Subtype.forall]

/-- Isotropy can be checked on any open cover of the source. -/
theorem isIsotropicMap_iff_of_isOpenCover (hf : MDifferentiable J I f)
    {ι : Type*} {U : ι → Opens N} (hU : IsOpenCover U) :
    hσ.IsIsotropicMap J f ↔
      ∀ i, hσ.IsIsotropicMap J (f ∘ (Subtype.val : U i → N)) := by
  rw [isIsotropicMap_iff_forall]
  simp only [hσ.isIsotropicMap_comp_subtype_val_iff _ (fun x _ ↦ hf x)]
  constructor
  · exact fun h i x _ ↦ h x
  · intro h x
    obtain ⟨i, hi⟩ := hU.exists_mem x
    exact h i x hi

/-- Coisotropy can be checked on any open cover of the source. -/
theorem isCoisotropicMap_iff_of_isOpenCover (hf : MDifferentiable J I f)
    {ι : Type*} {U : ι → Opens N} (hU : IsOpenCover U) :
    hσ.IsCoisotropicMap J f ↔
      ∀ i, hσ.IsCoisotropicMap J (f ∘ (Subtype.val : U i → N)) := by
  rw [isCoisotropicMap_iff]
  simp only [hσ.isCoisotropicMap_comp_subtype_val_iff _ (fun x _ ↦ hf x)]
  constructor
  · exact fun h i x _ ↦ h x
  · intro h x
    obtain ⟨i, hi⟩ := hU.exists_mem x
    exact h i x hi

/-- The Lagrangian condition can be checked on any open cover of the source. -/
theorem isLagrangianMap_iff_of_isOpenCover (hf : MDifferentiable J I f)
    {ι : Type*} {U : ι → Opens N} (hU : IsOpenCover U) :
    hσ.IsLagrangianMap J f ↔
      ∀ i, hσ.IsLagrangianMap J (f ∘ (Subtype.val : U i → N)) := by
  rw [isLagrangianMap_iff_forall]
  simp only [hσ.isLagrangianMap_comp_subtype_val_iff _ (fun x _ ↦ hf x)]
  constructor
  · exact fun h i x _ ↦ h x
  · intro h x
    obtain ⟨i, hi⟩ := hU.exists_mem x
    exact h i x hi

/-- Symplectic tangent images can be checked on any open cover of the source. -/
theorem hasSymplecticTangentImages_iff_of_isOpenCover (hf : MDifferentiable J I f)
    {ι : Type*} {U : ι → Opens N} (hU : IsOpenCover U) :
    hσ.HasSymplecticTangentImages J f ↔
      ∀ i, hσ.HasSymplecticTangentImages J (f ∘ (Subtype.val : U i → N)) := by
  rw [hasSymplecticTangentImages_iff_forall]
  simp only [hσ.hasSymplecticTangentImages_comp_subtype_val_iff _ (fun x _ ↦ hf x)]
  constructor
  · exact fun h i x _ ↦ h x
  · intro h x
    obtain ⟨i, hi⟩ := hU.exists_mem x
    exact h i x hi

variable {hσ}

/-- Restricting an isotropic map to an open subset of its source gives an isotropic map. -/
theorem IsIsotropicMap.comp_subtype_val (h : hσ.IsIsotropicMap J f) (U : Opens N)
    (hf : ∀ x ∈ U, MDifferentiableAt J I f x) :
    hσ.IsIsotropicMap J (f ∘ (Subtype.val : U → N)) :=
  (hσ.isIsotropicMap_comp_subtype_val_iff U hf).2 fun x _ ↦ isIsotropicMap_iff_forall.1 h x

/-- Restricting a coisotropic map to an open subset of its source gives a coisotropic map. -/
theorem IsCoisotropicMap.comp_subtype_val (h : hσ.IsCoisotropicMap J f) (U : Opens N)
    (hf : ∀ x ∈ U, MDifferentiableAt J I f x) :
    hσ.IsCoisotropicMap J (f ∘ (Subtype.val : U → N)) :=
  (hσ.isCoisotropicMap_comp_subtype_val_iff U hf).2 fun x _ ↦ isCoisotropicMap_iff.1 h x

/-- Restricting a Lagrangian map to an open subset of its source gives a Lagrangian map. -/
theorem IsLagrangianMap.comp_subtype_val (h : hσ.IsLagrangianMap J f) (U : Opens N)
    (hf : ∀ x ∈ U, MDifferentiableAt J I f x) :
    hσ.IsLagrangianMap J (f ∘ (Subtype.val : U → N)) :=
  (hσ.isLagrangianMap_comp_subtype_val_iff U hf).2 fun x _ ↦ isLagrangianMap_iff_forall.1 h x

/-- Restricting a map with symplectic tangent images to an open subset of its source keeps its
tangent images symplectic. -/
theorem HasSymplecticTangentImages.comp_subtype_val (h : hσ.HasSymplecticTangentImages J f)
    (U : Opens N) (hf : ∀ x ∈ U, MDifferentiableAt J I f x) :
    hσ.HasSymplecticTangentImages J (f ∘ (Subtype.val : U → N)) :=
  (hσ.hasSymplecticTangentImages_comp_subtype_val_iff U hf).2 fun x _ ↦
    hasSymplecticTangentImages_iff_forall.1 h x

end Source

section Target

variable {U : Opens M} {f : N → U}

/-- A map into an open submanifold is isotropic for the restricted form exactly when its
ambient inclusion is isotropic. -/
@[simp]
theorem isIsotropicMap_subtype_val_comp_iff (hf : MDifferentiable J I f) :
    hσ.IsIsotropicMap J ((Subtype.val : U → M) ∘ f) ↔
      (hσ.mpullback_subtype_val U).IsIsotropicMap J f := by
  rw [isIsotropicMap_iff, isIsotropicMap_iff]
  simp only [mfderiv_comp _ (contMDiff_subtype_val.mdifferentiableAt one_ne_zero) (hf _),
    ContinuousLinearMap.comp_apply, SmoothForm.eval₂_mpullback, Function.comp_apply]

/-- A map into an open submanifold is coisotropic for the restricted form exactly when its
ambient inclusion is coisotropic. -/
@[simp]
theorem isCoisotropicMap_subtype_val_comp_iff (hf : MDifferentiable J I f) :
    hσ.IsCoisotropicMap J ((Subtype.val : U → M) ∘ f) ↔
      (hσ.mpullback_subtype_val U).IsCoisotropicMap J f := by
  rw [isCoisotropicMap_iff, isCoisotropicMap_iff]
  refine forall_congr' fun x ↦ ?_
  rw [Manifold.range_mfderiv_subtype_val_comp x (hf x), Function.comp_apply,
    ← hσ.symplecticFormAt_mpullback_subtype_val_transport,
    SymplecticForm.isCoisotropic_map_transport_iff]

/-- A map into an open submanifold is Lagrangian for the restricted form exactly when its
ambient inclusion is Lagrangian. -/
@[simp]
theorem isLagrangianMap_subtype_val_comp_iff (hf : MDifferentiable J I f) :
    hσ.IsLagrangianMap J ((Subtype.val : U → M) ∘ f) ↔
      (hσ.mpullback_subtype_val U).IsLagrangianMap J f := by
  rw [isLagrangianMap_iff_forall, isLagrangianMap_iff_forall]
  refine forall_congr' fun x ↦ ?_
  rw [Manifold.range_mfderiv_subtype_val_comp x (hf x), Function.comp_apply,
    ← hσ.symplecticFormAt_mpullback_subtype_val_transport,
    SymplecticForm.isLagrangian_map_transport_iff]

/-- A map into an open submanifold has symplectic tangent images for the restricted form exactly
when its ambient inclusion has symplectic tangent images. -/
@[simp]
theorem hasSymplecticTangentImages_subtype_val_comp_iff (hf : MDifferentiable J I f) :
    hσ.HasSymplecticTangentImages J ((Subtype.val : U → M) ∘ f) ↔
      (hσ.mpullback_subtype_val U).HasSymplecticTangentImages J f := by
  rw [hasSymplecticTangentImages_iff_forall, hasSymplecticTangentImages_iff_forall]
  refine forall_congr' fun x ↦ ?_
  rw [Manifold.range_mfderiv_subtype_val_comp x (hf x), Function.comp_apply,
    ← hσ.symplecticFormAt_mpullback_subtype_val_transport,
    SymplecticForm.isSymplectic_map_transport_iff]

end Target

end TauCeti.SmoothTwoForm.IsNondegenerate
