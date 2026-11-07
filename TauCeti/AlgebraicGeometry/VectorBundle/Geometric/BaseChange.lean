/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.Geometric.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.LinearScheme.BaseChange

/-!
# Base change of geometric vector bundles

Base change of a linear scheme preserves finite local freeness of its degree-one sheaf.
It therefore restricts to `GeometricVectorBundle.pullback`, with no flatness or constant-rank
assumption. Forgetting the grading identifies this construction with the actual fibre product
of schemes. The restricted linear-spectrum anti-equivalence and the covariant total-space
equivalence commute with this structured base change.

The comparisons use base change of linear spectra and the canonical comparison between
pullback of a dual and the dual of a pullback.

## References

* The Stacks Project, Section 27.6, Tag 01M1.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.7.
-/

public section

open CategoryTheory Opposite
open _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {X Y Z : Scheme.{u}} (f : Y ⟶ X)

/-- Base change of a geometric vector bundle is again a geometric vector bundle. -/
theorem isGeometricVectorBundle_pullback (V : QuasicoherentLinearScheme X)
    (hV : isGeometricVectorBundle X V) :
    isGeometricVectorBundle Y ((QuasicoherentLinearScheme.pullback f).obj V) := by
  rw [QuasicoherentLinearScheme.pullback_obj, isGeometricVectorBundle_linearSpec_obj_iff]
  let E := ((QuasicoherentLinearScheme.degreeOne X).obj V).unop
  have hE : Scheme.Modules.isFiniteLocallyFree X E.obj :=
    (isGeometricVectorBundle_iff V).mp hV
  have := hE.1
  have := hE.2
  dsimp only [Functor.op_obj, unop_op]
  rw [QuasicoherentSheaf.pullback_obj_obj]
  exact ⟨Scheme.Modules.isLocallyFree_pullback f E.obj,
    Scheme.Modules.isFinitePresentation_pullback f E.obj⟩

namespace GeometricVectorBundle

/-- Pullback of geometric vector bundles, retaining their gradings. -/
-- Exposed to compute the underlying linear schemes and type their comparison maps.
@[expose]
def pullback : GeometricVectorBundle X ⥤ GeometricVectorBundle Y :=
  (isGeometricVectorBundle Y).lift
    ((isGeometricVectorBundle X).ι ⋙ QuasicoherentLinearScheme.pullback f)
    fun V ↦ isGeometricVectorBundle_pullback f V.obj V.property

/-- The linear scheme underlying a pulled-back bundle is its structured linear base change. -/
@[simp]
theorem pullback_obj_obj (V : GeometricVectorBundle X) :
    ((pullback f).obj V).obj = (QuasicoherentLinearScheme.pullback f).obj V.obj :=
  (rfl)

/-- Pullback of a bundle morphism is pullback of its graded linear-scheme morphism. -/
@[simp]
theorem pullback_map_hom {V W : GeometricVectorBundle X} (a : V ⟶ W) :
    ((pullback f).map a).hom = (QuasicoherentLinearScheme.pullback f).map a.hom :=
  (rfl)

/-- After forgetting the grading, pullback is the actual fibre product of schemes. -/
def pullbackForgetIso :
    pullback f ⋙ (isGeometricVectorBundle Y).ι ⋙ QuasicoherentLinearScheme.forget Y ≅
      (isGeometricVectorBundle X).ι ⋙ QuasicoherentLinearScheme.forget X ⋙
        baseChangeAffineSchemeOver f :=
  Functor.isoWhiskerLeft (isGeometricVectorBundle X).ι
    (QuasicoherentLinearScheme.pullbackForgetIso f)

/-- The underlying-scheme comparison is the comparison for linear schemes. -/
@[simp]
theorem pullbackForgetIso_hom_app (V : GeometricVectorBundle X) :
    (pullbackForgetIso f).hom.app V =
      (QuasicoherentLinearScheme.pullbackForgetIso f).hom.app V.obj :=
  (rfl)

/-- The inverse underlying-scheme comparison is the comparison for linear schemes. -/
@[simp]
theorem pullbackForgetIso_inv_app (V : GeometricVectorBundle X) :
    (pullbackForgetIso f).inv.app V =
      (QuasicoherentLinearScheme.pullbackForgetIso f).inv.app V.obj :=
  (rfl)

/-- Pullback along the identity preserves a geometric vector bundle, including its grading. -/
def pullbackId (X : Scheme.{u}) : pullback (𝟙 X) ≅ 𝟭 (GeometricVectorBundle X) :=
  NatIso.ofComponents
    (fun V ↦ (isGeometricVectorBundle X).isoMk
      ((QuasicoherentLinearScheme.pullbackId X).app V.obj))
    fun a ↦ ObjectProperty.hom_ext _
      ((QuasicoherentLinearScheme.pullbackId X).hom.naturality a.hom)

/-- The identity comparison is inherited from structured linear schemes. -/
@[simp]
theorem pullbackId_hom_app_hom (V : GeometricVectorBundle X) :
    ((pullbackId X).hom.app V).hom =
      (QuasicoherentLinearScheme.pullbackId X).hom.app V.obj :=
  (rfl)

/-- The inverse identity comparison is inherited from structured linear schemes. -/
@[simp]
theorem pullbackId_inv_app_hom (V : GeometricVectorBundle X) :
    ((pullbackId X).inv.app V).hom =
      (QuasicoherentLinearScheme.pullbackId X).inv.app V.obj :=
  (rfl)

/-- Successive base changes of geometric vector bundles agree with base change along the
composite, retaining the grading. -/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  NatIso.ofComponents
    (fun V ↦ (isGeometricVectorBundle X).isoMk
      ((QuasicoherentLinearScheme.pullbackComp f g).app V.obj))
    fun a ↦ ObjectProperty.hom_ext _
      ((QuasicoherentLinearScheme.pullbackComp f g).hom.naturality a.hom)

/-- The composition comparison is inherited from structured linear schemes. -/
@[simp]
theorem pullbackComp_hom_app_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (V : GeometricVectorBundle Z) :
    ((pullbackComp f g).hom.app V).hom =
      (QuasicoherentLinearScheme.pullbackComp f g).hom.app V.obj :=
  (rfl)

/-- The inverse composition comparison is inherited from structured linear schemes. -/
@[simp]
theorem pullbackComp_inv_app_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (V : GeometricVectorBundle Z) :
    ((pullbackComp f g).inv.app V).hom =
      (QuasicoherentLinearScheme.pullbackComp f g).inv.app V.obj :=
  (rfl)

end GeometricVectorBundle

/-- The linear-spectrum anti-equivalence for finite locally free sheaves commutes with
structured base change. -/
def linearSpecFiniteLocallyFreePullbackIso :
    (linearSpecFiniteLocallyFreeEquiv X).functor ⋙ GeometricVectorBundle.pullback f ≅
      (FiniteLocallyFreeSheaf.pullback f).op ⋙ (linearSpecFiniteLocallyFreeEquiv Y).functor := by
  let e := Functor.isoWhiskerLeft (FiniteLocallyFreeSheaf.toQuasicoherent X).op
      (QuasicoherentLinearScheme.linearSpecPullbackIso f) ≪≫
    Functor.isoWhiskerRight (NatIso.op (FiniteLocallyFreeSheaf.pullbackToQuasicoherentIso f))
      (linearSpec Y)
  exact NatIso.ofComponents (fun E ↦ (isGeometricVectorBundle Y).isoMk (e.app E))
    fun a ↦ ObjectProperty.hom_ext _ (e.hom.naturality a)

/-- On linear schemes the finite locally free comparison is the linear-spectrum comparison
followed by the identification of the two quasicoherent pullbacks. -/
@[simp]
theorem linearSpecFiniteLocallyFreePullbackIso_hom_app_hom
    (E : (FiniteLocallyFreeSheaf X)ᵒᵖ) :
    ((linearSpecFiniteLocallyFreePullbackIso f).hom.app E).hom =
      (QuasicoherentLinearScheme.linearSpecPullbackIso f).hom.app
          (op ((FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.unop)) ≫
        (linearSpec Y).map ((FiniteLocallyFreeSheaf.pullbackToQuasicoherentIso f).hom.app
          E.unop).op :=
  (rfl)

/-- On linear schemes the inverse comparison reverses the pullback identification and the
linear-spectrum comparison. -/
@[simp]
theorem linearSpecFiniteLocallyFreePullbackIso_inv_app_hom
    (E : (FiniteLocallyFreeSheaf X)ᵒᵖ) :
    ((linearSpecFiniteLocallyFreePullbackIso f).inv.app E).hom =
      (linearSpec Y).map ((FiniteLocallyFreeSheaf.pullbackToQuasicoherentIso f).inv.app
          E.unop).op ≫
        (QuasicoherentLinearScheme.linearSpecPullbackIso f).inv.app
          (op ((FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.unop)) :=
  (rfl)

/-- The covariant total-space equivalence commutes with base change as geometric vector
bundles, not merely as ungraded schemes. -/
def totalSpacePullbackIso :
    totalSpace X ⋙ GeometricVectorBundle.pullback f ≅
      FiniteLocallyFreeSheaf.pullback f ⋙ totalSpace Y := by
  let d : FiniteLocallyFreeSheaf.pullback f ⋙ FiniteLocallyFreeSheaf.dualFunctor.rightOp ≅
      FiniteLocallyFreeSheaf.dualFunctor.rightOp ⋙ (FiniteLocallyFreeSheaf.pullback f).op :=
    NatIso.ofComponents (fun E ↦ (FiniteLocallyFreeSheaf.pullbackDualIso f E).op)
      fun a ↦ Quiver.Hom.unop_inj
        (FiniteLocallyFreeSheaf.pullbackDualIso_naturality f a).symm
  exact Functor.isoWhiskerLeft FiniteLocallyFreeSheaf.dualFunctor.rightOp
      (linearSpecFiniteLocallyFreePullbackIso f) ≪≫
    Functor.isoWhiskerRight d.symm (linearSpecFiniteLocallyFreeEquiv Y).functor

/-- The structured total-space comparison first commutes linear spectrum with pullback and
then identifies the pulled-back dual with the dual of the pulled-back sheaf. -/
@[simp]
theorem totalSpacePullbackIso_hom_app (E : FiniteLocallyFreeSheaf X) :
    (totalSpacePullbackIso f).hom.app E =
      (linearSpecFiniteLocallyFreePullbackIso f).hom.app
          (op (FiniteLocallyFreeSheaf.dual E)) ≫
        (linearSpecFiniteLocallyFreeEquiv Y).functor.map
          (FiniteLocallyFreeSheaf.pullbackDualIso f E).inv.op :=
  (rfl)

/-- The inverse structured total-space comparison reverses dual base change and then
linear-spectrum base change. -/
@[simp]
theorem totalSpacePullbackIso_inv_app (E : FiniteLocallyFreeSheaf X) :
    (totalSpacePullbackIso f).inv.app E =
      (linearSpecFiniteLocallyFreeEquiv Y).functor.map
          (FiniteLocallyFreeSheaf.pullbackDualIso f E).hom.op ≫
        (linearSpecFiniteLocallyFreePullbackIso f).inv.app
          (op (FiniteLocallyFreeSheaf.dual E)) :=
  (rfl)

end

end TauCeti.AlgebraicGeometry
