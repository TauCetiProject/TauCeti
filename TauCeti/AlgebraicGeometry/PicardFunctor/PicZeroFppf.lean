/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.Fppf
public import TauCeti.AlgebraicGeometry.PicardFunctor.PicZero
public import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# The degree-zero relative Picard fppf sheaf

For a smooth proper geometrically connected family of curves `f : X ⟶ S`, the degree-zero
relative Picard presheaf consists of the line-bundle classes having degree zero on every
geometric fibre. This file defines its fppf sheafification and embeds it into the relative Picard
fppf sheaf.

The inclusion is a monomorphism: the degree-zero presheaf is a subgroup presheaf of the relative
Picard presheaf, and sheafification of additive commutative groups preserves finite limits and
hence monomorphisms. The resulting subsheaf is the functorial `Pic⁰` used before representability.
Identifying it with an open-and-closed identity component of a representing Picard scheme needs
the geometric representability and local-constancy theorems and is not asserted here.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativePicardDegreeZeroFppfSheaf`: the fppf sheafification of the
  degree-zero relative Picard presheaf;
* `TauCeti.AlgebraicGeometry.relativePicardDegreeZeroToFppfSheaf`: its sheafification map;
* `TauCeti.AlgebraicGeometry.relativePicardDegreeZeroFppfSheafι`: the monomorphism from the
  degree-zero sheaf to the relative Picard fppf sheaf;
* `TauCeti.AlgebraicGeometry.relativePicardDegreeZeroFppfSheafHomEquiv`: the universal property
  of the degree-zero sheafification.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Sections 9.4--9.5.
* The Stacks Project, Tag 0B9R.
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)
variable [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]

/-- The degree-zero relative Picard presheaf, transported from multiplicative to additive
notation before fppf sheafification. -/
def relativePicardDegreeZeroAddPresheaf : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  relativePicardDegreeZeroFunctor f ⋙ CommGrpCat.toAddCommGrp

/-- The additive degree-zero relative Picard presheaf is obtained from the multiplicative one by
the equivalence between commutative groups and additive commutative groups. -/
theorem relativePicardDegreeZeroAddPresheaf_eq :
    relativePicardDegreeZeroAddPresheaf f =
      relativePicardDegreeZeroFunctor f ⋙ CommGrpCat.toAddCommGrp := by
  rw [relativePicardDegreeZeroAddPresheaf]

private instance : Mono (Functor.whiskerRight (relativePicardDegreeZeroFunctorι f)
    CommGrpCat.toAddCommGrp) := by
  suffices ∀ T, Mono ((Functor.whiskerRight (relativePicardDegreeZeroFunctorι f)
      CommGrpCat.toAddCommGrp).app T) from NatTrans.mono_of_mono_app _
  intro T
  exact ConcreteCategory.mono_of_injective _
    (relativePicardDegreeZeroFunctorι_app_injective f T)

/-- The inclusion of the additive degree-zero relative Picard presheaf into the additive relative
Picard presheaf. -/
def relativePicardDegreeZeroAddPresheafι :
    relativePicardDegreeZeroAddPresheaf f ⟶ relativePicardAddPresheaf f :=
  eqToHom (relativePicardDegreeZeroAddPresheaf_eq f) ≫
    Functor.whiskerRight (relativePicardDegreeZeroFunctorι f) CommGrpCat.toAddCommGrp ≫
    eqToHom (relativePicardAddPresheaf_eq f).symm

/-- The inclusion of the additive degree-zero relative Picard presheaf is a monomorphism. -/
instance : Mono (relativePicardDegreeZeroAddPresheafι f) := by
  unfold relativePicardDegreeZeroAddPresheafι
  infer_instance

/-- The **degree-zero relative Picard fppf sheaf** of a smooth proper geometrically connected
family of curves, obtained by sheafifying the presheaf of classes having degree zero on every
geometric fibre. -/
def relativePicardDegreeZeroFppfSheaf :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
    (relativePicardDegreeZeroAddPresheaf f)

/-- The degree-zero relative Picard fppf sheaf is the fppf sheafification of the additive
degree-zero presheaf. -/
theorem relativePicardDegreeZeroFppfSheaf_eq :
    relativePicardDegreeZeroFppfSheaf f =
      (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
        (relativePicardDegreeZeroAddPresheaf f) := by
  rw [relativePicardDegreeZeroFppfSheaf]

/-- The underlying presheaf of the degree-zero relative Picard fppf sheaf is the sheafification
of the additive degree-zero presheaf. -/
@[simp]
theorem relativePicardDegreeZeroFppfSheaf_obj :
    (relativePicardDegreeZeroFppfSheaf f).obj =
      sheafify (Scheme.fppfTopology.over S) (relativePicardDegreeZeroAddPresheaf f) := by
  exact congrArg (fun F : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} ↦ F.obj)
    (relativePicardDegreeZeroFppfSheaf_eq f)

/-- The canonical map from the degree-zero relative Picard presheaf to its fppf
sheafification. -/
def relativePicardDegreeZeroToFppfSheaf :
    relativePicardDegreeZeroAddPresheaf f ⟶ (relativePicardDegreeZeroFppfSheaf f).obj :=
  (toSheafify (Scheme.fppfTopology.over S) (relativePicardDegreeZeroAddPresheaf f) :
      relativePicardDegreeZeroAddPresheaf f ⟶
        sheafify (Scheme.fppfTopology.over S) (relativePicardDegreeZeroAddPresheaf f)) ≫
    eqToHom (relativePicardDegreeZeroFppfSheaf_obj f).symm

/-- The canonical map to the degree-zero relative Picard fppf sheaf is the unit of fppf
sheafification. -/
theorem relativePicardDegreeZeroToFppfSheaf_eq :
    relativePicardDegreeZeroToFppfSheaf f =
      toSheafify (Scheme.fppfTopology.over S) (relativePicardDegreeZeroAddPresheaf f) ≫
        eqToHom (relativePicardDegreeZeroFppfSheaf_obj f).symm := by
  rw [relativePicardDegreeZeroToFppfSheaf]

/-- The inclusion of the degree-zero relative Picard fppf sheaf into the full relative Picard
fppf sheaf, obtained by sheafifying the inclusion of presheaves. -/
def relativePicardDegreeZeroFppfSheafι :
    relativePicardDegreeZeroFppfSheaf f ⟶ relativePicardFppfSheaf f :=
  eqToHom (relativePicardDegreeZeroFppfSheaf_eq f) ≫
    (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).map
      (relativePicardDegreeZeroAddPresheafι f) ≫
    eqToHom (relativePicardFppfSheaf_eq f).symm

/-- The inclusion of degree-zero fppf sheaves is obtained by applying sheafification to the
inclusion of additive Picard presheaves and transporting along the defining equalities. -/
theorem relativePicardDegreeZeroFppfSheafι_eq :
    relativePicardDegreeZeroFppfSheafι f =
      eqToHom (relativePicardDegreeZeroFppfSheaf_eq f) ≫
        (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).map
          (relativePicardDegreeZeroAddPresheafι f) ≫
        eqToHom (relativePicardFppfSheaf_eq f).symm := by
  rw [relativePicardDegreeZeroFppfSheafι]

/-- The inclusion of the degree-zero relative Picard fppf sheaf is a monomorphism. -/
instance : Mono (relativePicardDegreeZeroFppfSheafι f) := by
  unfold relativePicardDegreeZeroFppfSheafι
  infer_instance

/-- **Universal property of the degree-zero relative Picard fppf sheaf.** Maps from its
sheafification to an fppf sheaf `F` are naturally equivalent to maps from the additive
degree-zero presheaf to the underlying presheaf of `F`. -/
def relativePicardDegreeZeroFppfSheafHomEquiv
    (F : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}) :
    (relativePicardDegreeZeroFppfSheaf f ⟶ F) ≃
      (relativePicardDegreeZeroAddPresheaf f ⟶ F.obj) :=
  (Iso.homCongr (eqToIso (relativePicardDegreeZeroFppfSheaf_eq f)) (Iso.refl F)).trans <|
    (sheafificationAdjunction (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).homEquiv
      (relativePicardDegreeZeroAddPresheaf f) F

/-- The universal-property equivalence restricts a sheaf morphism along the canonical map from
the degree-zero relative Picard presheaf. -/
@[simp]
theorem relativePicardDegreeZeroFppfSheafHomEquiv_apply
    (F : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})
    (g : relativePicardDegreeZeroFppfSheaf f ⟶ F) :
    relativePicardDegreeZeroFppfSheafHomEquiv f F g =
      relativePicardDegreeZeroToFppfSheaf f ≫ g.hom := by
  rw [relativePicardDegreeZeroFppfSheafHomEquiv]
  dsimp only [Equiv.trans_apply, Iso.homCongr_apply]
  rw [Adjunction.homEquiv_unit]
  simp [relativePicardDegreeZeroToFppfSheaf, Category.assoc]

end

end TauCeti.AlgebraicGeometry
