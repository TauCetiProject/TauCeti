/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Tilde
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Finite presentation of relative spectra of symmetric algebras

The relative spectrum of the symmetric algebra of a finitely presented quasicoherent module
is locally of finite presentation over the base. This allows points of these spectra to be
approximated at finite stages of inverse limits.
-/

public section

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

/-- The spectrum of the symmetric algebra of a finitely presented module is locally of finite
presentation over the spectrum of the coefficient ring. -/
instance locallyOfFinitePresentation_specSymmetricAlgebraOver {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    LocallyOfFinitePresentation (specSymmetricAlgebraOver M).hom := by
  rw [specSymmetricAlgebraOver_hom]
  exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (RingHom.finitePresentation_algebraMap.mpr (SymmetricAlgebra.instFinitePresentation R M))

/-- The structure morphism of `Spec_X (Sym F)` is locally of finite presentation if the
quasicoherent module `F` is of finite presentation. -/
instance locallyOfFinitePresentation_relativeSpecSymmetricAlgebra {X : Scheme.{u}}
    (F : QuasicoherentSheaf X) [F.obj.IsFinitePresentation] :
    LocallyOfFinitePresentation ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F))).hom := by
  have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.FinitePresentation)
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFinitePresentation) X.affineCover]
  intro i
  let f : Spec _ ⟶ X := X.affineCover.f i
  let G := (QuasicoherentSheaf.pullback f).obj F
  let e := (relativeSpecSymmetricAlgebraBaseChangeIso f).app (op F)
  let M := tildeEquiv.inverse.obj G
  let a := (relativeSpec _).mapIso ((symmetricAlgebra _).mapIso
    (tildeEquiv.counitIso.app G)).op
  let b := relativeSpecSymmetricAlgebraTildeIso M
  have hG : G.obj.IsFinitePresentation :=
    (QuasicoherentSheaf.pullback_obj_obj f F).symm ▸
      Scheme.Modules.isFinitePresentation_pullback f F.obj
  have hM := Scheme.Modules.finitePresentation_moduleSpecΓ G.obj
  have hb := @locallyOfFinitePresentation_specSymmetricAlgebraOver _ M hM
  let iso := e.symm ≪≫ a ≪≫ b
  let forgetToScheme := MorphismProperty.Over.forget @IsAffineHom ⊤ (X.affineCover.X i) ⋙
    Over.forget _
  let iso' := forgetToScheme.mapIso iso
  have h := MorphismProperty.Over.w iso.hom
  -- The cover pullback is the underlying base change of the affine scheme over `X`.
  have ha : LocallyOfFinitePresentation iso'.hom := inferInstance
  have hcomp : LocallyOfFinitePresentation
      (iso.hom.left ≫ (specSymmetricAlgebraOver M).hom) :=
    @locallyOfFinitePresentation_comp _ _ _ iso'.hom (specSymmetricAlgebraOver M).hom ha hb
  rw [h] at hcomp
  exact hcomp

end TauCeti.AlgebraicGeometry
