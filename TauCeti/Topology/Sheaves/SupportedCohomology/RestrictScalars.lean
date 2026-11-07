/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.SupportedCohomology.Sections
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.CategoryTheory.Sites.CoefficientEquivalence
public import TauCeti.CategoryTheory.Abelian.RightDerived

/-!
# Scalar change for supported sections

Restriction of scalars does not change the support of a section: vanishing after restriction
is a condition on the underlying additive group. Consequently it commutes with the sheaf of
sections supported in a closed subset, and with supported sections on each open. The
comparisons leave sections unchanged and respect the inclusions into the coefficient sheaf.

For a ring isomorphism, coefficient change is an exact equivalence of sheaf categories and
preserves injective objects. The supported-section comparisons therefore extend to all right
derived functors, both sheaf-valued and module-valued. In particular the derived construction
is independent of replacing the scalar ring by an isomorphic coefficient model.

The derived comparisons use `CategoryTheory.Functor.rightDerivedCompIso`; the equivalence of
sheaf categories is `CategoryTheory.Equivalence.sheafCongrRight` applied to Mathlib's
`ModuleCat.restrictScalarsEquivalenceOfRingEquiv`.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

noncomputable section

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R A : Type u} [CommRing R] [CommRing A]
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (S : Closeds X)
  (f : A →+* R)

/-- Restricting scalars commutes with the sheaf of sections supported in a closed set. -/
def supportedSubmoduleSheafRestrictScalarsIso :
    (sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars.{u} f)).obj
        (F.supportedSubmoduleSheaf S) ≅
      supportedSubmoduleSheaf
        ((sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars.{u} f)).obj F) S :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents (fun W ↦
    (LinearEquiv.toModuleIso
      (X₁ := (ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of R
        (F.supportedSubmodule S W.unop)))
      (X₂ := ((sheafCompose (Opens.grothendieckTopology X)
        (ModuleCat.restrictScalars.{u} f)).obj F).supportedSubmodule S W.unop)
      (m₁ := ((ModuleCat.restrictScalars.{u} f).obj
        (ModuleCat.of R (F.supportedSubmodule S W.unop))).isModule)
      { toFun := fun s ↦ ⟨s.1,
          (mem_supportedSubmodule_iff _).2 ((F.mem_supportedSubmodule_iff).1 s.2)⟩
        invFun := fun s ↦ ⟨s.1,
          (F.mem_supportedSubmodule_iff).2
            ((((sheafCompose (Opens.grothendieckTopology X)
              (ModuleCat.restrictScalars.{u} f)).obj F).mem_supportedSubmodule_iff).1 s.2)⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl } :
      (ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of R (F.supportedSubmodule S W.unop)) ≅
        ModuleCat.of A (((sheafCompose (Opens.grothendieckTopology X)
          (ModuleCat.restrictScalars.{u} f)).obj F).supportedSubmodule S W.unop)))
    (fun _ ↦ rfl)

/-- Scalar restriction leaves the ambient section unchanged under the support comparison. -/
@[simp]
lemma coe_supportedSubmoduleSheafRestrictScalarsIso_hom_app_apply (W : (Opens X)ᵒᵖ)
    (s : (ModuleCat.restrictScalars f).obj (ModuleCat.of R (F.supportedSubmodule S W.unop))) :
    ((F.supportedSubmoduleSheafRestrictScalarsIso S f).hom.hom.app W s).val = s.val :=
  (rfl)

/-- The inverse scalar-change comparison also leaves the ambient section unchanged. -/
@[simp]
lemma coe_supportedSubmoduleSheafRestrictScalarsIso_inv_app_apply (W : (Opens X)ᵒᵖ)
    (s : ((sheafCompose (Opens.grothendieckTopology X)
      (ModuleCat.restrictScalars.{u} f)).obj F).supportedSubmodule S W.unop) :
    ((F.supportedSubmoduleSheafRestrictScalarsIso S f).inv.hom.app W s).val = s.val :=
  (rfl)

/-- Scalar change for supported sections respects the inclusion into the coefficient sheaf. -/
@[reassoc (attr := simp)]
lemma supportedSubmoduleSheafRestrictScalarsIso_hom_ι :
    (F.supportedSubmoduleSheafRestrictScalarsIso S f).hom ≫
        ((sheafCompose (Opens.grothendieckTopology X)
          (ModuleCat.restrictScalars.{u} f)).obj F).supportedSubmoduleι S =
      (sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars.{u} f)).map
        (F.supportedSubmoduleι S) := by
  ext W s
  exact (((sheafCompose (Opens.grothendieckTopology X)
    (ModuleCat.restrictScalars.{u} f)).obj F).supportedSubmoduleι_hom_app_apply S W _).trans
      ((F.coe_supportedSubmoduleSheafRestrictScalarsIso_hom_app_apply S f W s).trans
        (F.supportedSubmoduleι_hom_app_apply S W s).symm)

end CategoryTheory.Sheaf

namespace RingHom

variable {X : TopCat.{u}} {R A : Type u} [CommRing R] [CommRing A]

/-- Restriction of scalars commutes naturally with the supported-section sheaf functor. -/
def supportedSubmoduleFunctorRestrictScalarsIso (f : A →+* R) (S : Closeds X) :
    Sheaf.supportedSubmoduleFunctor S ⋙
        sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars.{u} f) ≅
      sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars.{u} f) ⋙
        Sheaf.supportedSubmoduleFunctor S :=
  NatIso.ofComponents (fun F ↦ F.supportedSubmoduleSheafRestrictScalarsIso S f)
    (fun {F G} g ↦ by
      apply (cancel_mono (((sheafCompose (Opens.grothendieckTopology X)
        (ModuleCat.restrictScalars.{u} f)).obj G).supportedSubmoduleι S)).1
      simp [Functor.comp_map, ← Functor.map_comp])

@[simp]
lemma supportedSubmoduleFunctorRestrictScalarsIso_hom_app (f : A →+* R) (S : Closeds X)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (f.supportedSubmoduleFunctorRestrictScalarsIso S).hom.app F =
      (F.supportedSubmoduleSheafRestrictScalarsIso S f).hom :=
  (rfl)

@[simp]
lemma supportedSubmoduleFunctorRestrictScalarsIso_inv_app (f : A →+* R) (S : Closeds X)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (f.supportedSubmoduleFunctorRestrictScalarsIso S).inv.app F =
      (F.supportedSubmoduleSheafRestrictScalarsIso S f).inv :=
  (rfl)

/-- On each open, supported sections commute naturally with restriction of scalars. -/
def supportedSubmoduleSectionsFunctorRestrictScalarsIso (f : A →+* R) (S : Closeds X)
    (W : Opens X) :
    Sheaf.supportedSubmoduleSectionsFunctor S W ⋙ ModuleCat.restrictScalars.{u} f ≅
      sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars.{u} f) ⋙
        Sheaf.supportedSubmoduleSectionsFunctor S W :=
  NatIso.ofComponents
    (fun F ↦ ((sheafSections _ _).obj (Opposite.op W)).mapIso
      (F.supportedSubmoduleSheafRestrictScalarsIso S f))
    (fun g ↦ congrArg (fun k ↦ k.hom.app (Opposite.op W))
      ((f.supportedSubmoduleFunctorRestrictScalarsIso S).hom.naturality g))

/-- The sectionwise scalar-change comparison is evaluation of the sheaf comparison. -/
@[simp]
lemma supportedSubmoduleSectionsFunctorRestrictScalarsIso_hom_app (f : A →+* R)
    (S : Closeds X) (W : Opens X)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (f.supportedSubmoduleSectionsFunctorRestrictScalarsIso S W).hom.app F =
      (F.supportedSubmoduleSheafRestrictScalarsIso S f).hom.hom.app (Opposite.op W) :=
  (rfl)

/-- The inverse sectionwise comparison is evaluation of the inverse sheaf comparison. -/
@[simp]
lemma supportedSubmoduleSectionsFunctorRestrictScalarsIso_inv_app (f : A →+* R)
    (S : Closeds X) (W : Opens X)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (f.supportedSubmoduleSectionsFunctorRestrictScalarsIso S W).inv.app F =
      (F.supportedSubmoduleSheafRestrictScalarsIso S f).inv.hom.app (Opposite.op W) :=
  (rfl)

end RingHom

namespace RingEquiv

variable {X : TopCat.{u}} {R A : Type u} [CommRing R] [CommRing A]

/-- Coefficient change along a ring isomorphism is additive on sheaves. -/
instance additive_sheafCompose_restrictScalars (e : A ≃+* R) :
    (sheafCompose (Opens.grothendieckTopology X)
      (ModuleCat.restrictScalars.{u} e.toRingHom)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- A ring isomorphism transports all sheaf-valued right derived supported-section functors.
The isomorphism is natural in the coefficient sheaf. -/
def rightDerivedSupportedSubmoduleRestrictScalarsIso (e : A ≃+* R) (S : Closeds X) (n : ℕ) :
    (Sheaf.supportedSubmoduleFunctor (R := R) S).rightDerived n ⋙
        sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars.{u} e.toRingHom) ≅
      sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars.{u} e.toRingHom) ⋙
        (Sheaf.supportedSubmoduleFunctor (R := A) S).rightDerived n :=
  Functor.rightDerivedCompIso _ _ _ _
    (e.toRingHom.supportedSubmoduleFunctorRestrictScalarsIso S) n

/-- A ring isomorphism transports all module-valued right derived functors of supported
sections on an open, naturally in the coefficient sheaf. -/
def rightDerivedSupportedSubmoduleSectionsRestrictScalarsIso (e : A ≃+* R)
    (S : Closeds X) (W : Opens X) (n : ℕ) :
    (Sheaf.supportedSubmoduleSectionsFunctor (R := R) S W).rightDerived n ⋙
        ModuleCat.restrictScalars.{u} e.toRingHom ≅
      sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars.{u} e.toRingHom) ⋙
        (Sheaf.supportedSubmoduleSectionsFunctor (R := A) S W).rightDerived n :=
  Functor.rightDerivedCompIso _ _ _ _
    (e.toRingHom.supportedSubmoduleSectionsFunctorRestrictScalarsIso S W) n

end RingEquiv
