/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Functor.Balanced
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Functor.Braided

/-!
# Equivalence of twist-preserving and pivotal-preserving braided functor groupoids

On a braided rigid category, pivotal structures and balanced structures correspond bijectively via
`TauCeti.pivotalBalancedEquiv`, sending a pivotal structure `φ` to the twist `θ_X = φ_X ≫ u_X⁻¹`
(`TauCeti.balancedOfBraidedPivotal`) and a twist `θ` to `φ_X = θ_X ≫ u_X`
(`TauCeti.pivotalOfBalanced`), where `u_X` is the Drinfeld isomorphism. At the level of a single
strong braided functor `F : C ⥤ D`, `CategoryTheory.Functor.isBalanced_iff_isPivotal` and
`CategoryTheory.Functor.isPivotal_pivotalOfBalanced_iff` show that `F` preserves twists if and only
if it preserves pivotal structures.

This file upgrades that preservation criterion to an equivalence of bundled functor categories and
hence of functor groupoids (with monoidal natural isomorphisms as morphisms). Rather than
transporting categories along propositional equalities of `PivotalCategory` or `BalancedCategory`
instances—which would introduce `eqToHom` casts—we first establish the equivalence
`TauCeti.braidedPivotalBalancedFunctorEquivOfEq` for any braided rigid categories equipped with
compatible pivotal and balanced instances (`B = balancedOfBraidedPivotal _`). Because the
compatibility hypotheses are used only inside the `Prop`-valued preservation equivalence, both round
trips on `TauCeti.BraidedPivotalFunctor C D` and `TauCeti.BalancedFunctor C D` hold definitionally,
with identity unit and counit isomorphisms.

Specializing `braidedPivotalBalancedFunctorEquivOfEq` yields:
* `TauCeti.braidedPivotalBalancedFunctorEquiv` and
  `TauCeti.braidedPivotalBalancedFunctorCoreEquiv` when `C` and `D` carry given pivotal structures
  and the induced twists `balancedOfBraidedPivotal`;
* `TauCeti.balancedBraidedPivotalFunctorEquiv` and
  `TauCeti.balancedBraidedPivotalFunctorCoreEquiv` when `C` and `D` carry given balanced structures
  and the induced pivotal structures `pivotalOfBalanced`;
* mixed comparisons where one category is presented by a pivotal structure and the other by a
  primitive twist (for instance, a ribbon category), directly via
  `braidedPivotalBalancedFunctorEquivOfEq` and `braidedPivotalBalancedFunctorCoreEquivOfEq`.

All equivalences commute strictly with forgetting to `TauCeti.BraidedFunctor C D` (and to
`Core (BraidedFunctor C D)`), as well as with identity functors, functor composition, and left and
right whiskering.

## Main declarations

* `CategoryTheory.Functor.isBalanced_iff_isPivotal_of_eq`: twist preservation and pivotal
  preservation agree for any compatible pairs of pivotal and balanced structures;
* `TauCeti.braidedPivotalBalancedFunctorEquivOfEq` and
  `TauCeti.braidedPivotalBalancedFunctorCoreEquivOfEq`: equivalence of functor categories and
  functor groupoids for compatible pivotal and balanced structures, covering pivotal-pivotal,
  balanced-balanced, and mixed cases without `eqToHom`;
* `TauCeti.braidedPivotalBalancedFunctorEquiv` and
  `TauCeti.braidedPivotalBalancedFunctorCoreEquiv`: the functor-category and functor-groupoid
  equivalences for braided pivotal categories with their induced twists;
* `TauCeti.balancedBraidedPivotalFunctorEquiv` and
  `TauCeti.balancedBraidedPivotalFunctorCoreEquiv`: the functor-category and functor-groupoid
  equivalences for balanced rigid categories with their induced pivotal structures.

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.1, eq. (3)
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §8.10
-/

public section

open CategoryTheory MonoidalCategory TauCeti

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  [RigidCategory C] [PivotalCategory C] [BalancedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  [RigidCategory D] [PivotalCategory D] [BalancedCategory D]

/-- When the balanced structures on `C` and `D` agree with those induced by their pivotal
structures, a strong braided functor `F : C ⥤ D` is balanced if and only if it is pivotal. -/
theorem isBalanced_iff_isPivotal_of_eq (F : C ⥤ D) [F.Braided]
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D) :
    F.IsBalanced ↔ F.IsPivotal := by
  subst hC; subst hD
  exact F.isBalanced_iff_isPivotal

end CategoryTheory.Functor

namespace TauCeti

universe v₁ v₂ v₃ u₁ u₂ u₃

/-! ### General equivalence for compatible pivotal and balanced structures -/

section Compatible

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  [RigidCategory C] [PivotalCategory C] [BalancedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  [RigidCategory D] [PivotalCategory D] [BalancedCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
  [RigidCategory E] [PivotalCategory E] [BalancedCategory E]

/-- View a bundled pivotal-preserving braided functor as a balanced functor along compatibility of
the balanced and pivotal structures. -/
abbrev BraidedPivotalFunctor.toBalancedFunctorOfEq
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D)
    (F : BraidedPivotalFunctor C D) : BalancedFunctor C D where
  toBraidedFunctor := F.toBraidedFunctor
  isBalanced := (F.toFunctor.isBalanced_iff_isPivotal_of_eq hC hD).mpr F.isPivotal

/-- View a bundled balanced functor as a pivotal-preserving braided functor along compatibility of
the balanced and pivotal structures. -/
abbrev BalancedFunctor.toBraidedPivotalFunctorOfEq
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D)
    (F : BalancedFunctor C D) : BraidedPivotalFunctor C D where
  toBraidedFunctor := F.toBraidedFunctor
  isPivotal := (F.toFunctor.isBalanced_iff_isPivotal_of_eq hC hD).mp F.isBalanced

/-- Converting a pivotal braided functor to a balanced functor and back is the identity. -/
@[simp]
theorem BalancedFunctor.toBraidedPivotalFunctorOfEq_toBalancedFunctorOfEq
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D)
    (F : BraidedPivotalFunctor C D) :
    (F.toBalancedFunctorOfEq hC hD).toBraidedPivotalFunctorOfEq hC hD = F :=
  (rfl)

/-- Converting a balanced functor to a pivotal braided functor and back is the identity. -/
@[simp]
theorem BraidedPivotalFunctor.toBalancedFunctorOfEq_toBraidedPivotalFunctorOfEq
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D)
    (F : BalancedFunctor C D) :
    (F.toBraidedPivotalFunctorOfEq hC hD).toBalancedFunctorOfEq hC hD = F :=
  (rfl)

/-- Converting the identity pivotal braided functor gives the identity balanced functor. -/
@[simp]
theorem BraidedPivotalFunctor.toBalancedFunctorOfEq_id
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C) :
    (BraidedPivotalFunctor.id C).toBalancedFunctorOfEq hC hC = BalancedFunctor.id C :=
  (rfl)

/-- Converting the identity balanced functor gives the identity pivotal braided functor. -/
@[simp]
theorem BalancedFunctor.toBraidedPivotalFunctorOfEq_id
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C) :
    (BalancedFunctor.id C).toBraidedPivotalFunctorOfEq hC hC = BraidedPivotalFunctor.id C :=
  (rfl)

/-- Converting pivotal braided functors to balanced functors commutes with composition. -/
@[simp]
theorem BraidedPivotalFunctor.toBalancedFunctorOfEq_comp
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D)
    (hE : (inferInstance : BalancedCategory E) = balancedOfBraidedPivotal E)
    (F : BraidedPivotalFunctor C D) (G : BraidedPivotalFunctor D E) :
    (F.comp G).toBalancedFunctorOfEq hC hE =
      (F.toBalancedFunctorOfEq hC hD).comp (G.toBalancedFunctorOfEq hD hE) :=
  (rfl)

/-- Converting balanced functors to pivotal braided functors commutes with composition. -/
@[simp]
theorem BalancedFunctor.toBraidedPivotalFunctorOfEq_comp
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D)
    (hE : (inferInstance : BalancedCategory E) = balancedOfBraidedPivotal E)
    (F : BalancedFunctor C D) (G : BalancedFunctor D E) :
    (F.comp G).toBraidedPivotalFunctorOfEq hC hE =
      (F.toBraidedPivotalFunctorOfEq hC hD).comp (G.toBraidedPivotalFunctorOfEq hD hE) :=
  (rfl)

/-- The functor from pivotal-preserving strong braided functors to twist-preserving strong braided
functors, for compatible pivotal and balanced structures. -/
@[expose]
def braidedPivotalToBalancedFunctorOfEq
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D) :
    BraidedPivotalFunctor C D ⥤ BalancedFunctor C D where
  obj F := F.toBalancedFunctorOfEq hC hD
  map α := InducedCategory.homMk α.hom

/-- `braidedPivotalToBalancedFunctorOfEq` acts on objects via `toBalancedFunctorOfEq`. -/
@[simp]
theorem braidedPivotalToBalancedFunctorOfEq_obj
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D)
    (F : BraidedPivotalFunctor C D) :
    (braidedPivotalToBalancedFunctorOfEq hC hD).obj F = F.toBalancedFunctorOfEq hC hD :=
  (rfl)

/-- `braidedPivotalToBalancedFunctorOfEq` preserves the underlying morphism in
`BraidedFunctor C D`. -/
@[simp]
theorem braidedPivotalToBalancedFunctorOfEq_map_hom
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D)
    {F G : BraidedPivotalFunctor C D} (α : F ⟶ G) :
    ((braidedPivotalToBalancedFunctorOfEq hC hD).map α).hom = α.hom :=
  (rfl)

/-- The functor from twist-preserving strong braided functors to pivotal-preserving strong braided
functors, for compatible pivotal and balanced structures. -/
@[expose]
def balancedToBraidedPivotalFunctorOfEq
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D) :
    BalancedFunctor C D ⥤ BraidedPivotalFunctor C D where
  obj F := F.toBraidedPivotalFunctorOfEq hC hD
  map α := InducedCategory.homMk α.hom

/-- `balancedToBraidedPivotalFunctorOfEq` acts on objects via `toBraidedPivotalFunctorOfEq`. -/
@[simp]
theorem balancedToBraidedPivotalFunctorOfEq_obj
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D)
    (F : BalancedFunctor C D) :
    (balancedToBraidedPivotalFunctorOfEq hC hD).obj F = F.toBraidedPivotalFunctorOfEq hC hD :=
  (rfl)

/-- `balancedToBraidedPivotalFunctorOfEq` preserves the underlying morphism in
`BraidedFunctor C D`. -/
@[simp]
theorem balancedToBraidedPivotalFunctorOfEq_map_hom
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D)
    {F G : BalancedFunctor C D} (α : F ⟶ G) :
    ((balancedToBraidedPivotalFunctorOfEq hC hD).map α).hom = α.hom :=
  (rfl)

/-- The two conversion functors compose strictly to the identity on `BraidedPivotalFunctor C D`. -/
@[simp]
theorem braidedPivotalToBalancedFunctorOfEq_comp_inv
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D) :
    braidedPivotalToBalancedFunctorOfEq hC hD ⋙ balancedToBraidedPivotalFunctorOfEq hC hD =
      𝟭 (BraidedPivotalFunctor C D) :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq rfl

/-- The two conversion functors compose strictly to the identity on `BalancedFunctor C D`. -/
@[simp]
theorem balancedToBraidedPivotalFunctorOfEq_comp_inv
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D) :
    balancedToBraidedPivotalFunctorOfEq hC hD ⋙ braidedPivotalToBalancedFunctorOfEq hC hD =
      𝟭 (BalancedFunctor C D) :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq rfl

/-- Passing from pivotal braided functors to balanced functors commutes with forgetting to
`BraidedFunctor C D`. -/
@[simp]
theorem braidedPivotalToBalancedFunctorOfEq_comp_forget
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D) :
    braidedPivotalToBalancedFunctorOfEq hC hD ⋙ BalancedFunctor.forget C D =
      BraidedPivotalFunctor.forget C D :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq rfl

/-- Passing from balanced functors to pivotal braided functors commutes with forgetting to
`BraidedFunctor C D`. -/
@[simp]
theorem balancedToBraidedPivotalFunctorOfEq_comp_forget
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D) :
    balancedToBraidedPivotalFunctorOfEq hC hD ⋙ BraidedPivotalFunctor.forget C D =
      BalancedFunctor.forget C D :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq rfl

/-- Precomposition of pivotal braided functors intertwines with precomposition of balanced
functors. -/
theorem whiskeringLeft_comp_braidedPivotalToBalancedFunctorOfEq
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D)
    (hE : (inferInstance : BalancedCategory E) = balancedOfBraidedPivotal E)
    (F : BraidedPivotalFunctor C D) :
    BraidedPivotalFunctor.whiskeringLeft F E ⋙ braidedPivotalToBalancedFunctorOfEq hC hE =
      braidedPivotalToBalancedFunctorOfEq hD hE ⋙
        BalancedFunctor.whiskeringLeft (F.toBalancedFunctorOfEq hC hD) E :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq rfl

/-- Postcomposition of pivotal braided functors intertwines with postcomposition of balanced
functors. -/
theorem whiskeringRight_comp_braidedPivotalToBalancedFunctorOfEq
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D)
    (hE : (inferInstance : BalancedCategory E) = balancedOfBraidedPivotal E)
    (G : BraidedPivotalFunctor D E) :
    BraidedPivotalFunctor.whiskeringRight C G ⋙ braidedPivotalToBalancedFunctorOfEq hC hE =
      braidedPivotalToBalancedFunctorOfEq hC hD ⋙
        BalancedFunctor.whiskeringRight C (G.toBalancedFunctorOfEq hD hE) :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq rfl

/-- **Equivalence of pivotal-preserving and twist-preserving braided functor categories** for any
braided rigid categories equipped with compatible pivotal and balanced structures. -/
@[expose]
def braidedPivotalBalancedFunctorEquivOfEq
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D) :
    BraidedPivotalFunctor C D ≌ BalancedFunctor C D where
  functor := braidedPivotalToBalancedFunctorOfEq hC hD
  inverse := balancedToBraidedPivotalFunctorOfEq hC hD
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := Category.id_comp _

/-- **Equivalence of pivotal-preserving and twist-preserving braided functor groupoids** for any
braided rigid categories equipped with compatible pivotal and balanced structures. -/
@[expose]
def braidedPivotalBalancedFunctorCoreEquivOfEq
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D) :
    Core (BraidedPivotalFunctor C D) ≌ Core (BalancedFunctor C D) :=
  (braidedPivotalBalancedFunctorEquivOfEq hC hD).core

/-- On functor groupoids, converting pivotal preservation to twist preservation commutes with
forgetting to `Core (BraidedFunctor C D)`. -/
@[simp]
theorem braidedPivotalBalancedFunctorCoreEquivOfEq_functor_comp_forget
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D) :
    (braidedPivotalBalancedFunctorCoreEquivOfEq hC hD).functor ⋙ (BalancedFunctor.forget C D).core =
      (BraidedPivotalFunctor.forget C D).core :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq (Core.hom_ext rfl)

/-- On functor groupoids, converting twist preservation to pivotal preservation commutes with
forgetting to `Core (BraidedFunctor C D)`. -/
@[simp]
theorem braidedPivotalBalancedFunctorCoreEquivOfEq_inverse_comp_forget
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D) :
    (braidedPivotalBalancedFunctorCoreEquivOfEq hC hD).inverse ⋙
        (BraidedPivotalFunctor.forget C D).core =
      (BalancedFunctor.forget C D).core :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq (Core.hom_ext rfl)

/-- On functor groupoids, precomposition intertwines the equivalence between pivotal-preserving and
twist-preserving braided functors. -/
theorem whiskeringLeft_core_comp_braidedPivotalBalancedFunctorCoreEquivOfEq
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D)
    (hE : (inferInstance : BalancedCategory E) = balancedOfBraidedPivotal E)
    (F : BraidedPivotalFunctor C D) :
    (BraidedPivotalFunctor.whiskeringLeft F E).core ⋙
        (braidedPivotalBalancedFunctorCoreEquivOfEq hC hE).functor =
      (braidedPivotalBalancedFunctorCoreEquivOfEq hD hE).functor ⋙
        (BalancedFunctor.whiskeringLeft (F.toBalancedFunctorOfEq hC hD) E).core :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq (Core.hom_ext rfl)

/-- On functor groupoids, postcomposition intertwines the equivalence between pivotal-preserving and
twist-preserving braided functors. -/
theorem whiskeringRight_core_comp_braidedPivotalBalancedFunctorCoreEquivOfEq
    (hC : (inferInstance : BalancedCategory C) = balancedOfBraidedPivotal C)
    (hD : (inferInstance : BalancedCategory D) = balancedOfBraidedPivotal D)
    (hE : (inferInstance : BalancedCategory E) = balancedOfBraidedPivotal E)
    (G : BraidedPivotalFunctor D E) :
    (BraidedPivotalFunctor.whiskeringRight C G).core ⋙
        (braidedPivotalBalancedFunctorCoreEquivOfEq hC hE).functor =
      (braidedPivotalBalancedFunctorCoreEquivOfEq hC hD).functor ⋙
        (BalancedFunctor.whiskeringRight C (G.toBalancedFunctorOfEq hD hE)).core :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq (Core.hom_ext rfl)

end Compatible

/-! ### Specialization to braided pivotal categories -/

section Pivotal

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  [RigidCategory C] [PivotalCategory C]
  (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  [RigidCategory D] [PivotalCategory D]
  (E : Type u₃) [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
  [RigidCategory E] [PivotalCategory E]

/-- For braided pivotal categories `C` and `D` equipped with their induced twists
`balancedOfBraidedPivotal`, the category of pivotal-preserving strong braided functors is equivalent
to the category of twist-preserving strong braided functors. -/
@[expose]
noncomputable def braidedPivotalBalancedFunctorEquiv :
    letI := balancedOfBraidedPivotal C
    letI := balancedOfBraidedPivotal D
    BraidedPivotalFunctor C D ≌ BalancedFunctor C D :=
  letI := balancedOfBraidedPivotal C
  letI := balancedOfBraidedPivotal D
  braidedPivotalBalancedFunctorEquivOfEq rfl rfl

/-- **Equivalence of pivotal-preserving and twist-preserving braided functor groupoids** for braided
pivotal categories `C` and `D` equipped with their induced twists `balancedOfBraidedPivotal`. -/
@[expose]
noncomputable def braidedPivotalBalancedFunctorCoreEquiv :
    letI := balancedOfBraidedPivotal C
    letI := balancedOfBraidedPivotal D
    Core (BraidedPivotalFunctor C D) ≌ Core (BalancedFunctor C D) :=
  letI := balancedOfBraidedPivotal C
  letI := balancedOfBraidedPivotal D
  braidedPivotalBalancedFunctorCoreEquivOfEq rfl rfl

/-- `braidedPivotalBalancedFunctorCoreEquiv` sends the identity pivotal braided functor to the
identity balanced functor. -/
@[simp]
theorem braidedPivotalBalancedFunctorCoreEquiv_functor_id :
    letI := balancedOfBraidedPivotal C
    (braidedPivotalBalancedFunctorCoreEquiv C C).functor.obj (.mk (.id C)) = .mk (.id C) :=
  (rfl)

/-- `braidedPivotalBalancedFunctorCoreEquiv` sends a composite of pivotal braided functors to the
composite of the corresponding balanced functors. -/
@[simp]
theorem braidedPivotalBalancedFunctorCoreEquiv_functor_comp
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [RigidCategory C] [PivotalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
    [RigidCategory D] [PivotalCategory D]
    {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
    [RigidCategory E] [PivotalCategory E]
    (F : BraidedPivotalFunctor C D) (G : BraidedPivotalFunctor D E) :
    letI := balancedOfBraidedPivotal C
    letI := balancedOfBraidedPivotal D
    letI := balancedOfBraidedPivotal E
    (braidedPivotalBalancedFunctorCoreEquiv C E).functor.obj (.mk (F.comp G)) =
      .mk (((braidedPivotalBalancedFunctorEquiv C D).functor.obj F).comp
        ((braidedPivotalBalancedFunctorEquiv D E).functor.obj G)) :=
  (rfl)

/-- `braidedPivotalBalancedFunctorEquiv` commutes strictly with forgetting to
`BraidedFunctor C D`. -/
@[simp]
theorem braidedPivotalBalancedFunctorEquiv_functor_comp_forget :
    letI := balancedOfBraidedPivotal C
    letI := balancedOfBraidedPivotal D
    (braidedPivotalBalancedFunctorEquiv C D).functor ⋙ BalancedFunctor.forget C D =
      BraidedPivotalFunctor.forget C D := by
  let := balancedOfBraidedPivotal C
  let := balancedOfBraidedPivotal D
  exact braidedPivotalToBalancedFunctorOfEq_comp_forget rfl rfl

/-- The inverse of `braidedPivotalBalancedFunctorEquiv` commutes strictly with forgetting to
`BraidedFunctor C D`. -/
@[simp]
theorem braidedPivotalBalancedFunctorEquiv_inverse_comp_forget :
    letI := balancedOfBraidedPivotal C
    letI := balancedOfBraidedPivotal D
    (braidedPivotalBalancedFunctorEquiv C D).inverse ⋙ BraidedPivotalFunctor.forget C D =
      BalancedFunctor.forget C D := by
  let := balancedOfBraidedPivotal C
  let := balancedOfBraidedPivotal D
  exact balancedToBraidedPivotalFunctorOfEq_comp_forget rfl rfl

/-- `braidedPivotalBalancedFunctorCoreEquiv` commutes strictly with forgetting to
`Core (BraidedFunctor C D)`. -/
@[simp]
theorem braidedPivotalBalancedFunctorCoreEquiv_functor_comp_forget :
    letI := balancedOfBraidedPivotal C
    letI := balancedOfBraidedPivotal D
    (braidedPivotalBalancedFunctorCoreEquiv C D).functor ⋙ (BalancedFunctor.forget C D).core =
      (BraidedPivotalFunctor.forget C D).core := by
  let := balancedOfBraidedPivotal C
  let := balancedOfBraidedPivotal D
  exact braidedPivotalBalancedFunctorCoreEquivOfEq_functor_comp_forget rfl rfl

/-- The inverse of `braidedPivotalBalancedFunctorCoreEquiv` commutes strictly with forgetting to
`Core (BraidedFunctor C D)`. -/
@[simp]
theorem braidedPivotalBalancedFunctorCoreEquiv_inverse_comp_forget :
    letI := balancedOfBraidedPivotal C
    letI := balancedOfBraidedPivotal D
    (braidedPivotalBalancedFunctorCoreEquiv C D).inverse ⋙
        (BraidedPivotalFunctor.forget C D).core =
      (BalancedFunctor.forget C D).core := by
  let := balancedOfBraidedPivotal C
  let := balancedOfBraidedPivotal D
  exact braidedPivotalBalancedFunctorCoreEquivOfEq_inverse_comp_forget rfl rfl

end Pivotal

/-! ### Specialization to balanced rigid categories -/

section Balanced

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  [RigidCategory C] [BalancedCategory C]
  (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  [RigidCategory D] [BalancedCategory D]
  (E : Type u₃) [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
  [RigidCategory E] [BalancedCategory E]

/-- For balanced rigid categories `C` and `D` equipped with their induced pivotal structures
`pivotalOfBalanced`, the category of twist-preserving strong braided functors is equivalent to the
category of pivotal-preserving strong braided functors. -/
@[expose]
noncomputable def balancedBraidedPivotalFunctorEquiv :
    letI := pivotalOfBalanced C
    letI := pivotalOfBalanced D
    BalancedFunctor C D ≌ BraidedPivotalFunctor C D :=
  letI := pivotalOfBalanced C
  letI := pivotalOfBalanced D
  (braidedPivotalBalancedFunctorEquivOfEq
    (balancedOfBraidedPivotal_pivotalOfBalanced _).symm
    (balancedOfBraidedPivotal_pivotalOfBalanced _).symm).symm

/-- **Equivalence of twist-preserving and pivotal-preserving braided functor groupoids** for
balanced rigid categories `C` and `D` equipped with their induced pivotal structures
`pivotalOfBalanced`. -/
@[expose]
noncomputable def balancedBraidedPivotalFunctorCoreEquiv :
    letI := pivotalOfBalanced C
    letI := pivotalOfBalanced D
    Core (BalancedFunctor C D) ≌ Core (BraidedPivotalFunctor C D) :=
  letI := pivotalOfBalanced C
  letI := pivotalOfBalanced D
  (balancedBraidedPivotalFunctorEquiv C D).core

/-- `balancedBraidedPivotalFunctorCoreEquiv` sends the identity balanced functor to the identity
pivotal braided functor. -/
@[simp]
theorem balancedBraidedPivotalFunctorCoreEquiv_functor_id :
    letI := pivotalOfBalanced C
    (balancedBraidedPivotalFunctorCoreEquiv C C).functor.obj (.mk (.id C)) = .mk (.id C) :=
  (rfl)

/-- `balancedBraidedPivotalFunctorCoreEquiv` sends a composite of balanced functors to the composite
of the corresponding pivotal braided functors. -/
@[simp]
theorem balancedBraidedPivotalFunctorCoreEquiv_functor_comp
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [RigidCategory C] [BalancedCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
    [RigidCategory D] [BalancedCategory D]
    {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
    [RigidCategory E] [BalancedCategory E]
    (F : BalancedFunctor C D) (G : BalancedFunctor D E) :
    letI := pivotalOfBalanced C
    letI := pivotalOfBalanced D
    letI := pivotalOfBalanced E
    (balancedBraidedPivotalFunctorCoreEquiv C E).functor.obj (.mk (F.comp G)) =
      .mk (((balancedBraidedPivotalFunctorEquiv C D).functor.obj F).comp
        ((balancedBraidedPivotalFunctorEquiv D E).functor.obj G)) :=
  (rfl)

/-- `balancedBraidedPivotalFunctorEquiv` commutes strictly with forgetting to
`BraidedFunctor C D`. -/
@[simp]
theorem balancedBraidedPivotalFunctorEquiv_functor_comp_forget :
    letI := pivotalOfBalanced C
    letI := pivotalOfBalanced D
    (balancedBraidedPivotalFunctorEquiv C D).functor ⋙ BraidedPivotalFunctor.forget C D =
      BalancedFunctor.forget C D := by
  let := pivotalOfBalanced C
  let := pivotalOfBalanced D
  exact balancedToBraidedPivotalFunctorOfEq_comp_forget
    (balancedOfBraidedPivotal_pivotalOfBalanced _).symm
    (balancedOfBraidedPivotal_pivotalOfBalanced _).symm

/-- The inverse of `balancedBraidedPivotalFunctorEquiv` commutes strictly with forgetting to
`BraidedFunctor C D`. -/
@[simp]
theorem balancedBraidedPivotalFunctorEquiv_inverse_comp_forget :
    letI := pivotalOfBalanced C
    letI := pivotalOfBalanced D
    (balancedBraidedPivotalFunctorEquiv C D).inverse ⋙ BalancedFunctor.forget C D =
      BraidedPivotalFunctor.forget C D := by
  let := pivotalOfBalanced C
  let := pivotalOfBalanced D
  exact braidedPivotalToBalancedFunctorOfEq_comp_forget
    (balancedOfBraidedPivotal_pivotalOfBalanced _).symm
    (balancedOfBraidedPivotal_pivotalOfBalanced _).symm

/-- `balancedBraidedPivotalFunctorCoreEquiv` commutes strictly with forgetting to
`Core (BraidedFunctor C D)`. -/
@[simp]
theorem balancedBraidedPivotalFunctorCoreEquiv_functor_comp_forget :
    letI := pivotalOfBalanced C
    letI := pivotalOfBalanced D
    (balancedBraidedPivotalFunctorCoreEquiv C D).functor ⋙ (BraidedPivotalFunctor.forget C D).core =
      (BalancedFunctor.forget C D).core := by
  let := pivotalOfBalanced C
  let := pivotalOfBalanced D
  exact braidedPivotalBalancedFunctorCoreEquivOfEq_inverse_comp_forget
    (balancedOfBraidedPivotal_pivotalOfBalanced _).symm
    (balancedOfBraidedPivotal_pivotalOfBalanced _).symm

/-- The inverse of `balancedBraidedPivotalFunctorCoreEquiv` commutes strictly with forgetting to
`Core (BraidedFunctor C D)`. -/
@[simp]
theorem balancedBraidedPivotalFunctorCoreEquiv_inverse_comp_forget :
    letI := pivotalOfBalanced C
    letI := pivotalOfBalanced D
    (balancedBraidedPivotalFunctorCoreEquiv C D).inverse ⋙
        (BalancedFunctor.forget C D).core =
      (BraidedPivotalFunctor.forget C D).core := by
  let := pivotalOfBalanced C
  let := pivotalOfBalanced D
  exact braidedPivotalBalancedFunctorCoreEquivOfEq_functor_comp_forget
    (balancedOfBraidedPivotal_pivotalOfBalanced _).symm
    (balancedOfBraidedPivotal_pivotalOfBalanced _).symm

end Balanced

end TauCeti
