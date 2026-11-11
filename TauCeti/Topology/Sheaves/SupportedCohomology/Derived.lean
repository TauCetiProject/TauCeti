/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.SupportedCohomology.Sections
public import TauCeti.CategoryTheory.Abelian.Injective.Ext
public import TauCeti.CategoryTheory.Abelian.RightDerived

/-!
# Derived supported sections and supported Ext groups

For a closed subset `S` and an open `W`, the supported-section functor
`F ↦ Γ_S(W,F)` is represented by the relative free module sheaf `Q_S(W)`.
Right deriving this representation identifies its native right derived functors
with the existing supported cohomology groups `Extⁿ(Q_S(W),F)`, naturally in `F`.
Thus supported Ext groups and derived supported sections are two computations of
the same functor, rather than unrelated cohomology carriers.

The construction uses `Closeds.supportedFreeModuleSheafHomEquiv` for the
representation, `NatIso.rightDerived` for its transport, and
`CategoryTheory.rightDerivedLinearCoyonedaIsoExt` for the injective-resolution
computation of Ext. No flasqueness hypothesis on the coefficient sheaf is needed.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R] (S : Closeds X) (W : Opens X)

noncomputable section

/-- The relative free module sheaf `Q_S(W)` represents sections on `W` supported in `S`,
naturally in the coefficient sheaf. -/
def supportedSubmoduleSectionsRepresentableIso :
    (linearCoyoneda R _).obj (op ((S.supportedFreeModuleSheafFunctor R).obj W)) ≅
      supportedSubmoduleSectionsFunctor (R := R) S W :=
  NatIso.ofComponents (fun F ↦ (S.supportedFreeModuleSheafHomEquiv R W F).toModuleIso)
    fun {F G} f ↦ by
      ext g
      apply Subtype.ext
      -- The functor's section object is bundled by evaluation; the ambient-section
      -- computation lemma avoids unfolding the supported-section lift.
      change (S.supportedFreeModuleSheafHomEquiv R W G (g ≫ f) : G.obj.obj (op W)) =
        Subtype.val (p := (· ∈ G.supportedSubmodule S W))
          ((supportedSubmoduleSectionsFunctor S W).map f
            (S.supportedFreeModuleSheafHomEquiv R W F g))
      exact (S.coe_supportedFreeModuleSheafHomEquiv_comp R W g f).trans
        (coe_supportedSubmoduleFunctor_map_hom_app_apply S f (op W) _).symm

/-- The representing isomorphism sends a morphism out of `Q_S(W)` to its supported section. -/
-- Rewrite before functor evaluation simplifies the bundled section object.
@[simp↓]
lemma supportedSubmoduleSectionsRepresentableIso_hom_app_apply
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (g : (S.supportedFreeModuleSheafFunctor R).obj W ⟶ F) :
    (supportedSubmoduleSectionsRepresentableIso (R := R) S W).hom.app F g =
      S.supportedFreeModuleSheafHomEquiv R W F g :=
  (rfl)

/-- The inverse representing isomorphism recovers the morphism associated with a supported
section. -/
-- Rewrite before functor evaluation simplifies the bundled section object.
@[simp↓]
lemma supportedSubmoduleSectionsRepresentableIso_inv_app_apply
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (s : F.supportedSubmodule S W) :
    (supportedSubmoduleSectionsRepresentableIso (R := R) S W).inv.app F s =
      (S.supportedFreeModuleSheafHomEquiv R W F).symm s :=
  (rfl)

/-- Right derived supported sections are the supported Ext groups, naturally in the
coefficient sheaf. The target evaluates the existing supported cohomology presheaf on `W`. -/
def rightDerivedSupportedSubmoduleSectionsIso (n : ℕ) :
    (supportedSubmoduleSectionsFunctor (R := R) S W).rightDerived n ≅
      supportedModuleHPresheafFunctor (R := R) S n ⋙
        (evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj (op W) :=
  (NatIso.rightDerived (supportedSubmoduleSectionsRepresentableIso (R := R) S W) n).symm ≪≫
    rightDerivedLinearCoyonedaIsoExt R
    ((S.supportedFreeModuleSheafFunctor R).obj W) n

/-- The derived comparison is the transport of the canonical derived Hom-to-Ext
comparison along the supported-section representation. This characterizes its normalization. -/
@[reassoc (attr := simp)]
lemma rightDerivedSupportedSubmoduleSectionsIso_hom_comp (n : ℕ) :
    (supportedSubmoduleSectionsRepresentableIso (R := R) S W).hom.rightDerived n ≫
        (rightDerivedSupportedSubmoduleSectionsIso (R := R) S W n).hom =
      (rightDerivedLinearCoyonedaIsoExt R
        ((S.supportedFreeModuleSheafFunctor R).obj W) n).hom := by
  have h :=
    (NatIso.rightDerived (supportedSubmoduleSectionsRepresentableIso S W) n).hom_inv_id_assoc
      (rightDerivedLinearCoyonedaIsoExt R ((S.supportedFreeModuleSheafFunctor R).obj W) n).hom
  rw [NatIso.rightDerived_hom] at h
  exact h

end

end CategoryTheory.Sheaf
