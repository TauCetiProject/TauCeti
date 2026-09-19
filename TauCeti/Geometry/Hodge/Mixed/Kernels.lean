/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import TauCeti.Geometry.Hodge.Mixed.Category
public import TauCeti.Geometry.Hodge.Mixed.Quotient
public import TauCeti.Geometry.Hodge.Mixed.Subobject

/-!
# Kernels and cokernels of mixed Hodge structures

The category of mixed Hodge structures has kernels and cokernels, and both are computed on the
underlying rational vector spaces. The kernel of a morphism `f` is the mixed Hodge structure
induced on the rational kernel of `f`, and its cokernel is the quotient of the target by the
rational image of `f`. Both constructions are available because the kernel and the image are
sub-mixed Hodge structures: this is where the Deligne bigrading, through the functoriality of its
pieces, enters the categorical structure.

Consequently a morphism of mixed Hodge structures is a monomorphism exactly when its rational map
is injective, and an epimorphism exactly when its rational map is surjective.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructureCat.kernelCone`: the kernel fork given by the inclusion of
  the induced structure on the rational kernel.
* `TauCeti.Hodge.MixedHodgeStructureCat.kernelIsLimit`: this fork is a limit.
* `TauCeti.Hodge.MixedHodgeStructureCat.cokernelCocone`: the cokernel cofork given by the
  projection onto the quotient by the rational image.
* `TauCeti.Hodge.MixedHodgeStructureCat.cokernelIsColimit`: this cofork is a colimit.
* `TauCeti.Hodge.MixedHodgeStructureCat.mono_iff_injective`,
  `TauCeti.Hodge.MixedHodgeStructureCat.epi_iff_surjective`: monomorphisms and epimorphisms are
  detected on rational maps.

## References

Deligne, *Théorie de Hodge II*, §2.3; Peters–Steenbrink, *Mixed Hodge Structures*, Chapter 3.

The kernel and cokernel constructions adapt the corresponding formalization in
`Mathlib.Algebra.Category.ModuleCat.Kernels`, by Markus Himmel.
-/

public section

namespace TauCeti.Hodge.MixedHodgeStructureCat

open CategoryTheory Limits

universe u

variable {X Y : MixedHodgeStructureCat.{u}} (f : X ⟶ Y)

/-- The kernel fork of a morphism of mixed Hodge structures: the inclusion of the mixed Hodge
structure induced on the kernel of its rational map. -/
-- Exposure is required for the dependent point and structure-map lemmas below to elaborate.
@[expose]
noncomputable def kernelCone : KernelFork f :=
  KernelFork.ofι (Z := .of _ _ (MixedHodgeStructure.Hom.isSubstructure_ker f).hodgeStructure)
    (MixedHodgeStructure.Hom.isSubstructure_ker f).inclusion <| by
      apply hom_ext
      ext x
      simp

/-- The point of the kernel fork is the structure induced on the rational kernel. -/
@[simp]
theorem kernelCone_pt :
    (kernelCone f).pt =
      .of _ _ (MixedHodgeStructure.Hom.isSubstructure_ker f).hodgeStructure :=
  rfl

/-- The kernel inclusion is the inclusion of the structure induced on the rational kernel. -/
@[simp]
theorem kernelCone_ι :
    (kernelCone f).ι = (MixedHodgeStructure.Hom.isSubstructure_ker f).inclusion :=
  (rfl)

/-- The inclusion of the induced structure on the rational kernel is a kernel. -/
noncomputable def kernelIsLimit : IsLimit (kernelCone f) :=
  KernelFork.IsLimit.ofι _ (kernelCone f).condition
    (fun g hg ↦ (MixedHodgeStructure.Hom.isSubstructure_ker f).codRestrict g fun x ↦ by
      simpa using LinearMap.congr_fun (congrArg MixedHodgeStructure.Hom.toRatLinearMap hg) x)
    (fun _ _ ↦ MixedHodgeStructure.IsSubstructure.inclusion_comp_codRestrict _ _ _)
    (fun _ _ _ hm ↦ MixedHodgeStructure.IsSubstructure.eq_codRestrict _ hm)

/-- The cokernel cofork of a morphism of mixed Hodge structures: the projection onto the quotient
of the target by the image of its rational map. -/
-- Exposure is required for the dependent point and structure-map lemmas below to elaborate.
@[expose]
noncomputable def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (Z := .of _ _ (MixedHodgeStructure.Hom.isSubstructure_range f).quotient)
    (MixedHodgeStructure.Hom.isSubstructure_range f).projection <| by
      apply hom_ext
      ext x
      simp

/-- The point of the cokernel cofork is the quotient by the rational image. -/
@[simp]
theorem cokernelCocone_pt :
    (cokernelCocone f).pt =
      .of _ _ (MixedHodgeStructure.Hom.isSubstructure_range f).quotient :=
  rfl

/-- The cokernel projection is the projection onto the quotient by the rational image. -/
@[simp]
theorem cokernelCocone_π :
    (cokernelCocone f).π = (MixedHodgeStructure.Hom.isSubstructure_range f).projection :=
  (rfl)

/-- The projection onto the quotient by the rational image is a cokernel. -/
noncomputable def cokernelIsColimit : IsColimit (cokernelCocone f) :=
  CokernelCofork.IsColimit.ofπ _ (cokernelCocone f).condition
    (fun g hg ↦ (MixedHodgeStructure.Hom.isSubstructure_range f).lift g <| by
      rintro _ ⟨x, rfl⟩
      simpa using LinearMap.congr_fun (congrArg MixedHodgeStructure.Hom.toRatLinearMap hg) x)
    (fun _ _ ↦ MixedHodgeStructure.IsSubstructure.lift_comp_projection _ _ _)
    (fun _ _ _ hm ↦ MixedHodgeStructure.IsSubstructure.eq_lift _ hm)

/-- The category of mixed Hodge structures has kernels. -/
instance : HasKernels MixedHodgeStructureCat.{u} :=
  ⟨fun f ↦ HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

/-- The category of mixed Hodge structures has cokernels. -/
instance : HasCokernels MixedHodgeStructureCat.{u} :=
  ⟨fun f ↦ HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

variable {f}

/-- A morphism of mixed Hodge structures is a monomorphism if and only if its rational map is
injective. -/
theorem mono_iff_injective : Mono f ↔ Function.Injective f.toRatLinearMap := by
  refine ⟨fun _ ↦ ?_, fun hf ↦ ⟨fun g h hgh ↦ hom_ext <| LinearMap.ext fun x ↦ hf ?_⟩⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    -- The kernel inclusion is killed by `f`, hence is zero once `f` is a monomorphism.
    have h : (MixedHodgeStructure.Hom.isSubstructure_ker f).inclusion = 0 :=
      (cancel_mono f).1 ((kernelCone f).condition.trans zero_comp.symm)
    simpa using LinearMap.congr_fun (congrArg MixedHodgeStructure.Hom.toRatLinearMap h) ⟨x, hx⟩
  · simpa using LinearMap.congr_fun (congrArg MixedHodgeStructure.Hom.toRatLinearMap hgh) x

/-- A morphism of mixed Hodge structures is an epimorphism if and only if its rational map is
surjective. -/
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f.toRatLinearMap := by
  refine ⟨fun _ ↦ ?_, fun hf ↦ ⟨fun g h hgh ↦ hom_ext <| LinearMap.ext fun x ↦ ?_⟩⟩
  · rw [← LinearMap.range_eq_top, eq_top_iff]
    intro y _
    -- The cokernel projection kills `f`, hence is zero once `f` is an epimorphism.
    have h : (MixedHodgeStructure.Hom.isSubstructure_range f).projection = 0 :=
      (cancel_epi f).1 ((cokernelCocone f).condition.trans comp_zero.symm)
    simpa using LinearMap.congr_fun (congrArg MixedHodgeStructure.Hom.toRatLinearMap h) y
  · obtain ⟨y, rfl⟩ := hf x
    simpa using LinearMap.congr_fun (congrArg MixedHodgeStructure.Hom.toRatLinearMap hgh) y

end TauCeti.Hodge.MixedHodgeStructureCat
