/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Kernel
import TauCeti.CategoryTheory.Monoidal.Grp.Cokernel
import TauCeti.CategoryTheory.EffectiveEpi.Over
import TauCeti.CategoryTheory.Monoidal.Grp.KernelPair
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Faithfully flat homomorphisms as cokernels

A quasi-compact faithfully flat homomorphism of group schemes is the categorical
cokernel of its scheme-theoretic kernel. Thus a homomorphism killing that kernel factors
uniquely through the quotient. No smoothness or reducedness is required.

The proof uses the kernel-pair translation square and Mathlib's effective-epimorphism
theorem for fpqc morphisms, via `Grp.isColimitCokernelCoforkOfTorsor`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.4.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry

universe u

namespace TauCeti.GroupScheme

variable {S : Scheme.{u}} {G H : Grp (Over S)} (f : G ⟶ H)
  [QuasiCompact f.hom.hom.left] [Flat f.hom.hom.left]
  [Surjective f.hom.hom.left]

/-- A quasi-compact faithfully flat homomorphism of group schemes is the
cokernel of its kernel inclusion. -/
noncomputable def isColimitKernelCofork :
    IsColimit (CokernelCofork.ofπ f (kernel.condition f)) := by
  have : Epi (f.hom.hom ⊗ₘ f.hom.hom) := by
    have hflat : Flat (f.hom.hom ⊗ₘ f.hom.hom).left := by
      rw [Over.tensorHom_left]
      exact MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance
        (Over.w f.hom.hom).symm (Over.w f.hom.hom).symm
    have hsurj : Surjective (f.hom.hom ⊗ₘ f.hom.hom).left := by
      have : MorphismProperty.IsStableUnderComposition @Surjective.{u} :=
        MorphismProperty.IsMultiplicative.toIsStableUnderComposition
      rw [Over.tensorHom_left]
      exact MorphismProperty.pullbackMap (P := @Surjective) inferInstance inferInstance
        (Over.w f.hom.hom).symm (Over.w f.hom.hom).symm
    have := Flat.epi_of_flat_of_surjective (f.hom.hom ⊗ₘ f.hom.hom).left
    exact Over.epi_of_epi_left _
  apply Grp.isColimitCokernelCoforkOfTorsor
  have h := (isPullback_mul_of_isPullback_one f.hom.hom (kernel.ι f).hom.hom
    (isPullback_kernel_hom f)).flip
  -- Inverting both coordinates turns left translation into right translation.
  exact h.of_iso ((β_ (kernel f).X G.X) ≪≫ (asIso ι[G.X] ⊗ᵢ asIso ι[(kernel f).X]))
    (asIso ι[G.X]) (asIso ι[G.X]) (asIso ι[H.X])
    (by simp [GrpObj.inv_eq_inv, GrpObj.comp_inv])
    (by simp [MonObj.comp_mul, GrpObj.inv_eq_inv, GrpObj.comp_inv, GrpObj.inv_comp])
    (by simp [GrpObj.inv_eq_inv, GrpObj.comp_inv, GrpObj.inv_comp])
    (by simp [GrpObj.inv_eq_inv, GrpObj.comp_inv, GrpObj.inv_comp])

end TauCeti.GroupScheme
