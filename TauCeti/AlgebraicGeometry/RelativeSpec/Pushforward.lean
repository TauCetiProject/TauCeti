/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

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

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (A : CommMon X.Modules)

/-- Sections of a pushed-forward commutative algebra have exactly the ring structure of the
sections of the original algebra on the inverse image. -/
def _root_.AlgebraicGeometry.Scheme.Hom.pushforwardSectionsRingEquiv (U : Y.Opens) :
    Γ(((Scheme.Modules.pushforward f).mapCommMon.obj A).X, U) ≃+*
      Γ(A.X, f ⁻¹ᵁ U) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' x y := by
    have h := SheafOfModules.pushforward_μ_app_tmul.{u}
      f.toRingCatSheafHom A.X A.X (op U) x y
    rw [CommMon.sections_mul_def ((Scheme.Modules.pushforward f).mapCommMon.obj A) U]
    exact congrArg ((MonObj.mul (X := A.X)).app (f ⁻¹ᵁ U)) h

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardSectionsRingEquiv_apply
    (U : Y.Opens) (x : Γ(((Scheme.Modules.pushforward f).mapCommMon.obj A).X, U)) :
    f.pushforwardSectionsRingEquiv A U x = x :=
  (rfl)

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardSectionsRingEquiv_symm_apply
    (U : Y.Opens) (x : Γ(A.X, f ⁻¹ᵁ U)) :
    (f.pushforwardSectionsRingEquiv A U).symm x = x :=
  (rfl)

/-- The section-ring comparison for pushforward commutes with restriction to smaller opens. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardSectionsRingEquiv_restrictSections
    {U V : Y.Opens} (i : V ⟶ U)
    (x : Γ(((Scheme.Modules.pushforward f).mapCommMon.obj A).X, U)) :
    f.pushforwardSectionsRingEquiv A V
        (((Scheme.Modules.pushforward f).mapCommMon.obj A).restrictSections i x) =
      A.restrictSections ((TopologicalSpace.Opens.map f.base).map i)
        (f.pushforwardSectionsRingEquiv A U x) := by
  -- Apply the component equations as terms: the two section rings have the same carrier
  -- but different algebra instances, which prevents rewriting both restrictions together.
  exact (f.pushforwardSectionsRingEquiv_apply A V _).trans
    ((CommMon.restrictSections_apply _ i x).trans
      ((congrArg (fun p ↦ p x)
        (Scheme.Modules.pushforward_obj_presheaf_map (M := A.X) f i)).trans
          ((CommMon.restrictSections_apply A _ x).symm.trans
            (congrArg (A.restrictSections _)
              (f.pushforwardSectionsRingEquiv_apply A U x).symm))))

/-- The presheaf of sections of a pushed-forward commutative algebra is naturally the direct
image of its presheaf of sections. -/
def _root_.AlgebraicGeometry.Scheme.Hom.pushforwardSectionsPresheafIso :
    ((Scheme.Modules.pushforward f).mapCommMon.obj A).sectionsPresheaf ≅
      (TopologicalSpace.Opens.map f.base).op ⋙ A.sectionsPresheaf :=
  NatIso.ofComponents
    (fun U ↦ (f.pushforwardSectionsRingEquiv A U.unop).toCommRingCatIso)
    (fun {U V} i ↦ by
      ext x
      -- Evaluate the bundled maps to use the restriction equation on sections.
      change f.pushforwardSectionsRingEquiv A V.unop
          (((Scheme.Modules.pushforward f).mapCommMon.obj A).restrictSections i.unop x) =
        A.restrictSections ((TopologicalSpace.Opens.map f.base).map i.unop)
          (f.pushforwardSectionsRingEquiv A U.unop x)
      exact f.pushforwardSectionsRingEquiv_restrictSections A i.unop x)

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardSectionsPresheafIso_hom_app
    (U : Y.Opensᵒᵖ) :
    (f.pushforwardSectionsPresheafIso A).hom.app U =
      (f.pushforwardSectionsRingEquiv A U.unop).toCommRingCatIso.hom :=
  (rfl)

variable (X) in
/-- The structure map of the tensor-unit algebra acts identically on regular functions. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.structureAlgebraSections_algebraMap
    (U : X.Opens) (r : Γ(X, U)) :
    algebraMap Γ(X, U) Γ((CommMon.trivial X.Modules).X, U) r = r := by
  rw [CommMon.sections_algebraMap_def, Scheme.Modules.sectionsFunctor_ε]
  rfl

variable (X) in
/-- The tensor-unit algebra has the ordinary ring of regular functions as its sections. -/
def _root_.AlgebraicGeometry.Scheme.structureAlgebraSectionsRingEquiv (U : X.Opens) :
    Γ((CommMon.trivial X.Modules).X, U) ≃+* Γ(X, U) :=
  (RingEquiv.ofBijective (algebraMap Γ(X, U) Γ((CommMon.trivial X.Modules).X, U))
    ⟨fun a b h ↦ (X.structureAlgebraSections_algebraMap U a).symm.trans
      (h.trans (X.structureAlgebraSections_algebraMap U b)),
      fun a ↦ ⟨a, X.structureAlgebraSections_algebraMap U a⟩⟩).symm

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.structureAlgebraSectionsRingEquiv_apply
    (X : Scheme.{u}) (U : X.Opens) (x : Γ((CommMon.trivial X.Modules).X, U)) :
    X.structureAlgebraSectionsRingEquiv U x = x := by
  unfold Scheme.structureAlgebraSectionsRingEquiv
  exact (RingEquiv.symm_apply_eq _).mpr (X.structureAlgebraSections_algebraMap U x).symm

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.structureAlgebraSectionsRingEquiv_symm_apply
    (X : Scheme.{u}) (U : X.Opens) (x : Γ(X, U)) :
    (X.structureAlgebraSectionsRingEquiv U).symm x = x :=
  X.structureAlgebraSections_algebraMap U x

variable (X) in
/-- The presheaf of sections of the tensor-unit algebra is the structure presheaf. -/
def _root_.AlgebraicGeometry.Scheme.structureAlgebraSectionsPresheafIso :
    (CommMon.trivial X.Modules).sectionsPresheaf ≅ X.presheaf :=
  NatIso.ofComponents
    (fun U ↦ (X.structureAlgebraSectionsRingEquiv U.unop).toCommRingCatIso)
    (fun {U V} i ↦ by
      ext x
      -- Evaluate the bundled maps to compare restriction of regular functions.
      change X.structureAlgebraSectionsRingEquiv V.unop
          ((CommMon.trivial X.Modules).restrictSections i.unop x) =
        X.presheaf.map i (X.structureAlgebraSectionsRingEquiv U.unop x)
      exact (X.structureAlgebraSectionsRingEquiv_apply V.unop _).trans
        ((CommMon.restrictSections_apply _ i.unop x).trans
          (congrArg (X.presheaf.map i)
            (X.structureAlgebraSectionsRingEquiv_apply U.unop x).symm)))

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.structureAlgebraSectionsPresheafIso_hom_app
    (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    X.structureAlgebraSectionsPresheafIso.hom.app U =
      (X.structureAlgebraSectionsRingEquiv U.unop).toCommRingCatIso.hom :=
  (rfl)

-- Expose the object construction so that section-ring carriers compute on inverse images;
-- all ring operations and restriction comparisons are characterized by the public API.
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
      (f.pushforwardStructureAlgebraSectionsRingEquiv U.unop).toCommRingCatIso.hom :=
  (rfl)

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
