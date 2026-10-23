/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Algebra.Sections
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Sections of pushed-forward commutative algebras

The lax symmetric monoidal pushforward of module sheaves carries commutative algebras to
commutative algebras. On each open, its sections are the sections of the original algebra on
the inverse image, with the same ring operations and compatible restrictions. The tensor-unit
algebra has the structure presheaf as its presheaf of sections.

The comparisons use Mathlib's `Functor.mapCommMon`, `CommMon.trivial`, `RingEquiv.ofBijective`
and `NatIso.ofComponents`, together with the canonical lax monoidal pushforward of module sheaves.
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
-- Not a simp lemma: `pushforwardSectionsRingEquiv_apply` and `restrictSections_apply`
-- already simplify its left-hand side, so adding `[simp]` would violate `simpNF`.
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

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardSectionsPresheafIso_inv_app
    (U : Y.Opensᵒᵖ) :
    (f.pushforwardSectionsPresheafIso A).inv.app U =
      (f.pushforwardSectionsRingEquiv A U.unop).toCommRingCatIso.inv :=
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

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.structureAlgebraSectionsPresheafIso_inv_app
    (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    X.structureAlgebraSectionsPresheafIso.inv.app U =
      (X.structureAlgebraSectionsRingEquiv U.unop).toCommRingCatIso.inv :=
  (rfl)

end

end TauCeti
