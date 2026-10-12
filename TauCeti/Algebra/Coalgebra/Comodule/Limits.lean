/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Preadditive
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
public import TauCeti.Algebra.Coalgebra.Subcomodule.Quotient
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Kernels and cokernels of comodules

For a flat coalgebra over a commutative ring, kernels of comodule morphisms carry the
induced coaction. Cokernels carry the quotient coaction, without a flatness assumption.
These concrete constructions satisfy the categorical universal properties, and the
forgetful functor to modules preserves them. This allows exact sequences of representations
to be computed on their underlying modules.

The constructions use `Subcomodule.subtype`, `Comodule.Hom.codRestrict`, and
`Subcomodule.liftQ`. The categorical packaging follows Mathlib's
`ModuleCat.kernelIsLimit` and `ModuleCat.cokernelIsColimit`.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.ComoduleCat

universe u v w

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]

noncomputable section

variable {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N)

section Kernel

variable [Module.Flat R C]

/-- The kernel fork given by the kernel subcomodule. -/
def kernelCone : KernelFork f :=
  KernelFork.ofι (ofHom (R := R) (C := C) (Subcomodule.subtype f.ker)) (by
    apply Comodule.Hom.ext
    intro x
    -- Expose categorical composition; the inclusion itself is computed by its public lemma.
    change f (Subcomodule.subtype f.ker x) = 0
    rw [Subcomodule.subtype_apply]
    exact (Comodule.Hom.mem_ker (f := f)).mp x.property)

/-- The kernel subcomodule is a categorical kernel. -/
def kernelIsLimit : IsLimit (kernelCone f) :=
  Fork.IsLimit.mk _
    (fun s ↦ ofHom (R := R) (C := C) (s.ι.codRestrict f.ker fun x ↦ Comodule.Hom.mem_ker.mpr
      (congrArg (fun g : s.pt ⟶ N ↦ g x) s.condition)))
    (fun s ↦ Comodule.Hom.subtype_comp_codRestrict s.ι f.ker _)
    (fun s m h ↦ by
      ext x
      apply Subtype.ext
      have hx : Subcomodule.subtype f.ker (m x) = s.ι x :=
        congrArg (fun g : s.pt ⟶ M ↦ g x) h
      exact (Subcomodule.subtype_apply f.ker (m x)).symm.trans
        (hx.trans (Comodule.Hom.codRestrict_apply s.ι f.ker _ x).symm))

instance : HasKernels (ComoduleCat.{u, v, w} R C) :=
  ⟨fun f ↦ HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

/-- The categorical kernel is the concrete kernel subcomodule. -/
def kernelIsoKer : kernel f ≅ of R C f.ker :=
  limit.isoLimitCone ⟨_, kernelIsLimit f⟩

@[simp]
theorem kernelIsoKer_inv_kernel_ι :
    (kernelIsoKer f).inv ≫ kernel.ι f = ofHom (R := R) (C := C) (Subcomodule.subtype f.ker) :=
  limit.isoLimitCone_inv_π _ _

instance : PreservesLimit (parallelPair f 0)
    (forget₂ (ComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)) := by
  let F := forget₂ (ComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)
  apply preservesLimit_of_preserves_limit_cone (kernelIsLimit f)
  apply (isLimitMapConeForkEquiv' F (kernelCone f).condition).symm.toFun
  have hι : (F.map (kernelCone f).ι).hom = SMulMemClass.subtype f.ker :=
    Subcomodule.subtype_toLinearMap _
  apply ModuleCat.isLimitKernelFork
  · rw [hι]
    intro x
    exact ⟨fun hx ↦ ⟨⟨x, (Comodule.Hom.mem_ker (f := f)).mpr hx⟩, rfl⟩,
      fun ⟨y, hy⟩ ↦ hy ▸ (Comodule.Hom.mem_ker (f := f)).mp y.property⟩
  · rw [hι]
    exact Subtype.val_injective

end Kernel

/-- The cokernel cofork given by the quotient by the range subcomodule. -/
def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (ofHom (R := R) (C := C) f.range.mkQ) (by
    ext x
    exact (f.range.mkQ_eq_zero_iff (f x)).mpr (Comodule.Hom.mem_range_self f x))

/-- The quotient by the range subcomodule is a categorical cokernel. -/
def cokernelIsColimit : IsColimit (cokernelCocone f) :=
  Cofork.IsColimit.mk _
    (fun s ↦ ofHom (R := R) (C := C) (f.range.liftQ s.π (by
      rw [Comodule.Hom.range_toSubmodule, LinearMap.range_le_ker_iff]
      simpa only [toLinearMap_comp, toLinearMap_zero, LinearMap.comp_zero] using
        congrArg Comodule.Hom.toLinearMap s.condition)))
    (fun s ↦ by ext x; exact Subcomodule.liftQ_apply f.range s.π _ x)
    (fun s m h ↦ by
      ext x
      obtain ⟨y, rfl⟩ := f.range.mkQ_surjective x
      exact (congrArg (fun g : N ⟶ s.pt ↦ g y) h).trans
        (Subcomodule.liftQ_apply _ _ _ y).symm)

instance : HasCokernels (ComoduleCat.{u, v, w} R C) :=
  ⟨fun f ↦ HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

/-- The categorical cokernel is the quotient by the concrete range subcomodule. -/
def cokernelIsoRangeQuotient : cokernel f ≅ of R C (N ⧸ f.range.toSubmodule) :=
  colimit.isoColimitCocone ⟨_, cokernelIsColimit f⟩

@[simp]
theorem cokernel_π_cokernelIsoRangeQuotient_hom :
    cokernel.π f ≫ (cokernelIsoRangeQuotient f).hom = ofHom (R := R) (C := C) f.range.mkQ :=
  colimit.isoColimitCocone_ι_hom _ _

instance : PreservesColimit (parallelPair f 0)
    (forget₂ (ComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)) := by
  let F := forget₂ (ComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)
  apply preservesColimit_of_preserves_colimit_cocone (cokernelIsColimit f)
  apply (isColimitMapCoconeCoforkEquiv' F (cokernelCocone f).condition).symm.toFun
  apply ModuleCat.isColimitCokernelCofork
  · intro x
    exact (f.range.mkQ_eq_zero_iff x).trans Comodule.Hom.mem_range
  · exact f.range.mkQ_surjective

end

end TauCeti.ComoduleCat
