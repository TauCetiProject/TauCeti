/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Algebra.Pushforward

/-!
# Algebras of functions under pushforward

The lax symmetric monoidal pushforward of module sheaves carries commutative algebras to
commutative algebras. Its sections on an open are the sections of the original algebra on the
inverse image, with the same ring operations. In particular, pushing forward the tensor-unit
algebra gives the algebra of regular functions of a scheme over its base, on the actual
pushforward of its structure sheaf.

The construction uses Mathlib's `Functor.mapCommMon` and `CommMon.trivial`, together with the
canonical lax monoidal pushforward of sheaves of modules. The section calculation identifies
its multiplication with multiplication of regular functions; it is needed to recover coordinate
algebras from affine morphisms.

## References

* The Stacks Project, Tag 01LL (quasi-coherent algebras and relative spectra).
-/

public section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

-- Expose the object construction so that section-ring carriers compute on inverse images;
-- all ring operations and restriction comparisons are characterized by the public API.
-- The `_one`, `_apply`, `_symm_apply`, and `_algebraMap` statements need this computation
-- to type-check. The propositional `_X` equality cannot supply it during elaboration.
/-- The algebra of regular functions of `X` over `Y`, carried by the actual pushforward
`f_* 𝒪_X`. The algebra structure is induced by lax symmetric monoidal pushforward. -/
@[expose]
def _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebra : CommMon Y.Modules :=
  (Scheme.Modules.pushforward f).mapCommMon.obj (CommMon.trivial X.Modules)

/-- The underlying module of the function algebra is the pushforward of the structure sheaf. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebra_X :
    f.pushforwardStructureAlgebra.X =
      (Scheme.Modules.pushforward f).obj (𝟙_ X.Modules) :=
  (rfl)

/-- The unit of the function algebra is the map on regular functions induced by `f`. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebra_one :
    MonObj.one (X := f.pushforwardStructureAlgebra.X) =
      _root_.SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
  (congrArg (Functor.LaxMonoidal.ε (Scheme.Modules.pushforward f) ≫ ·)
    ((Scheme.Modules.pushforward f).map_id (𝟙_ X.Modules))).trans
      ((Category.comp_id _).trans (Scheme.Modules.pushforward_ε f))

/-- On each open of the base, the function algebra is the ordinary ring of regular functions
on the inverse image. -/
def _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv (U : Y.Opens) :
    Γ(f.pushforwardStructureAlgebra.X, U) ≃+* Γ(X, f ⁻¹ᵁ U) :=
  f.pushforwardSectionsRingEquiv (CommMon.trivial X.Modules) U |>.trans
    (X.structureAlgebraSectionsRingEquiv (f ⁻¹ᵁ U))

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_apply
    (U : Y.Opens) (x : Γ(f.pushforwardStructureAlgebra.X, U)) :
    f.pushforwardStructureAlgebraSectionsRingEquiv U x = x := by
  exact (X.structureAlgebraSectionsRingEquiv_apply (f ⁻¹ᵁ U)
    (f.pushforwardSectionsRingEquiv (CommMon.trivial X.Modules) U x)).trans
      (f.pushforwardSectionsRingEquiv_apply (CommMon.trivial X.Modules) U x)

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_symm_apply
    (U : Y.Opens) (x : Γ(X, f ⁻¹ᵁ U)) :
    (f.pushforwardStructureAlgebraSectionsRingEquiv U).symm x = x := by
  exact (f.pushforwardSectionsRingEquiv_symm_apply (CommMon.trivial X.Modules) U
    ((X.structureAlgebraSectionsRingEquiv (f ⁻¹ᵁ U)).symm x)).trans
      (X.structureAlgebraSectionsRingEquiv_symm_apply (f ⁻¹ᵁ U) x)

/-- The structure map on sections of the function algebra is pullback of regular functions
along the scheme morphism. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebra_algebraMap
    (U : Y.Opens) (r : Γ(Y, U)) :
    algebraMap Γ(Y, U) Γ(f.pushforwardStructureAlgebra.X, U) r = f.app U r := by
  rw [CommMon.sections_algebraMap_def,
    Scheme.Hom.pushforwardStructureAlgebra_one, Scheme.Modules.sectionsFunctor_ε]
  rfl

/-- The presheaf of rings underlying the function algebra is naturally the direct image of
the structure presheaf. -/
def _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraPresheafIso :
    f.pushforwardStructureAlgebra.sectionsPresheaf ≅
      (TopologicalSpace.Opens.map f.base).op ⋙ X.presheaf :=
  f.pushforwardSectionsPresheafIso (CommMon.trivial X.Modules) ≪≫
    Functor.isoWhiskerLeft (TopologicalSpace.Opens.map f.base).op
      X.structureAlgebraSectionsPresheafIso

/-- The comparison with regular functions is given on each open by the section-ring
equivalence of the function algebra. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraPresheafIso_hom_app
    (U : Y.Opensᵒᵖ) :
    f.pushforwardStructureAlgebraPresheafIso.hom.app U =
      (f.pushforwardStructureAlgebraSectionsRingEquiv U.unop).toCommRingCatIso.hom := by
  dsimp +instances only [Scheme.Hom.pushforwardStructureAlgebra,
    Scheme.Hom.pushforwardStructureAlgebraPresheafIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  erw [Scheme.Hom.pushforwardSectionsPresheafIso_hom_app,
    Scheme.structureAlgebraSectionsPresheafIso_hom_app]
  rfl

/-- The inverse comparison with regular functions is given on each open by the inverse
section-ring equivalence of the function algebra. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraPresheafIso_inv_app
    (U : Y.Opensᵒᵖ) :
    f.pushforwardStructureAlgebraPresheafIso.inv.app U =
      (f.pushforwardStructureAlgebraSectionsRingEquiv U.unop).toCommRingCatIso.inv := by
  dsimp +instances only [Scheme.Hom.pushforwardStructureAlgebra,
    Scheme.Hom.pushforwardStructureAlgebraPresheafIso, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app]
  erw [Scheme.Hom.pushforwardSectionsPresheafIso_inv_app,
    Scheme.structureAlgebraSectionsPresheafIso_inv_app]
  rfl

/-- The presheaf comparison identifies the algebra's structure map with the actual
structure-presheaf morphism of the scheme map. -/
@[reassoc (attr := simp)]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebra_toSectionsPresheaf_comp :
    f.pushforwardStructureAlgebra.toSectionsPresheaf ≫
      f.pushforwardStructureAlgebraPresheafIso.hom = f.c := by
  ext U r
  rw [NatTrans.comp_app, CommMon.toSectionsPresheaf_app,
    Scheme.Hom.pushforwardStructureAlgebraPresheafIso_hom_app]
  exact (f.pushforwardStructureAlgebraSectionsRingEquiv_apply U _).trans
    (f.pushforwardStructureAlgebra_algebraMap U r)

end

end TauCeti
