/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.EquivalencePseudoabelian

/-!
# Normalized chains as a retract of the alternating face map complex

In an idempotent-complete preadditive category `C` with finite coproducts, the pseudoabelian
Dold–Kan normalized chain functor `CategoryTheory.Idempotents.DoldKan.N` is a retract of the
alternating face map complex functor `AlgebraicTopology.alternatingFaceMapComplex C`, cut out by
the idempotent `PInfty`.

This file defines the natural inclusion `CategoryTheory.Idempotents.DoldKan.inclusionN`, the
projection `CategoryTheory.Idempotents.DoldKan.PInftyToN`, the bundled retract
`CategoryTheory.Idempotents.DoldKan.retractN`, and the resulting chain homotopy equivalence
`CategoryTheory.Idempotents.DoldKan.homotopyEquivNAlternatingFaceMapComplex`.

## Main definitions and results

* `CategoryTheory.Idempotents.DoldKan.inclusionN`: inclusion `N ⟶ alternatingFaceMapComplex C`.
* `CategoryTheory.Idempotents.DoldKan.PInftyToN`: projection `alternatingFaceMapComplex C ⟶ N`.
* `CategoryTheory.Idempotents.DoldKan.retractN`: `Retract N (alternatingFaceMapComplex C)`.
* `CategoryTheory.Idempotents.DoldKan.N_map_eq_inclusionN_comp_PInftyToN`,
  `CategoryTheory.Idempotents.DoldKan.PInfty_comp_alternatingFaceMapComplex_map_eq`:
  factorization of `N.map f` and `PInfty ≫ K.map f`.
* `CategoryTheory.Idempotents.DoldKan.homotopyEquivNAlternatingFaceMapComplex`: chain homotopy
  equivalence `N.obj X ≃ K[X]`.
* `CategoryTheory.Idempotents.DoldKan.N.fullyFaithful`: full faithfulness of `N`.
-/

public noncomputable section

open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.DoldKan Idempotents

universe v u

namespace CategoryTheory.Idempotents.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C] [IsIdempotentComplete C]
  [HasFiniteCoproducts C]

omit [HasFiniteCoproducts C] in
/-- The counit of `toKaroubiEquivalence` at `N₁.obj X` lands in the summand cut out by
`PInfty`. -/
private lemma counitIso_hom_app_N₁_obj_f_comp_PInfty (X : SimplicialObject C) :
    ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom.app (N₁.obj X)).f ≫ PInfty =
      ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom.app (N₁.obj X)).f := by
  have h := Karoubi.comp_p ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom.app (N₁.obj X))
  simp only [Functor.id_obj, N₁_obj_p] at h
  exact h

omit [HasFiniteCoproducts C] in
/-- The inverse counit of `toKaroubiEquivalence` at `N₁.obj X` only depends on the summand cut
out by `PInfty`. -/
private lemma PInfty_comp_counitIso_inv_app_N₁_obj_f (X : SimplicialObject C) :
    PInfty ≫ ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.inv.app (N₁.obj X)).f =
      ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.inv.app (N₁.obj X)).f := by
  have h := Karoubi.p_comp ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.inv.app (N₁.obj X))
  simp only [Functor.id_obj, N₁_obj_p] at h
  exact h

/-- The inclusion of the normalized chains `N X` of the pseudoabelian Dold–Kan correspondence
into the alternating face map complex of `X`, as the direct summand cut out by `PInfty`.

By definition `N = N₁ ⋙ (toKaroubiEquivalence _).inverse`, so `N.obj X` is the object of chain
complexes corresponding to the formal direct summand `N₁.obj X` of the Karoubi envelope, whose
underlying complex is the alternating face map complex of `X` with idempotent `PInfty`
(`AlgebraicTopology.DoldKan.N₁_obj_p`); the counit of `toKaroubiEquivalence` identifies the two.
-/
def inclusionN : (N : SimplicialObject C ⥤ _) ⟶ alternatingFaceMapComplex C where
  app X := ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom.app (N₁.obj X)).f
  naturality X Y f := by
    have h := congrArg Karoubi.Hom.f
      ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom.naturality (N₁.map f))
    simp only [Karoubi.comp_f, Functor.comp_map, Functor.id_map, N₁_map_f,
      reassoc_of% (counitIso_hom_app_N₁_obj_f_comp_PInfty X)] at h
    exact h

/-- The projection of the alternating face map complex of `X` onto the normalized chains `N X`
of the pseudoabelian Dold–Kan correspondence. -/
def PInftyToN : alternatingFaceMapComplex C ⟶ (N : SimplicialObject C ⥤ _) where
  app X := ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.inv.app (N₁.obj X)).f
  naturality X Y f := by
    have h := congrArg Karoubi.Hom.f
      ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.inv.naturality (N₁.map f))
    have hn : PInfty ≫ AlternatingFaceMapComplex.map f =
        AlternatingFaceMapComplex.map f ≫ PInfty := by
      have h := ((natTransPInfty C).naturality f).symm
      simp only [natTransPInfty_app] at h
      exact h
    simp only [Karoubi.comp_f, Functor.comp_map, Functor.id_map, N₁_map_f, hn, Category.assoc,
      PInfty_comp_counitIso_inv_app_N₁_obj_f Y] at h
    exact h

private lemma inclusionN_app (X : SimplicialObject C) :
    inclusionN.app X = ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom.app (N₁.obj X)).f :=
  rfl

private lemma PInftyToN_app (X : SimplicialObject C) :
    PInftyToN.app X = ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.inv.app (N₁.obj X)).f :=
  rfl

/-- The normalized chains are a retract of the alternating face map complex. -/
@[reassoc (attr := simp)]
lemma inclusionN_app_comp_PInftyToN_app (X : SimplicialObject C) :
    inclusionN.app X ≫ PInftyToN.app X = 𝟙 (N.obj X) := by
  rw [inclusionN_app, PInftyToN_app]
  have h := congrArg Karoubi.Hom.f
    ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.hom_inv_id_app (N₁.obj X))
  simp only [Karoubi.comp_f, Karoubi.id_f, Functor.comp_obj, toKaroubiEquivalence,
    Functor.asEquivalence_functor, toKaroubi_obj_p] at h
  exact h

/-- The idempotent of the alternating face map complex cutting out the normalized chains is
`PInfty`. -/
@[reassoc (attr := simp)]
lemma PInftyToN_app_comp_inclusionN_app (X : SimplicialObject C) :
    PInftyToN.app X ≫ inclusionN.app X = PInfty := by
  rw [inclusionN_app, PInftyToN_app]
  have h := congrArg Karoubi.Hom.f
    ((toKaroubiEquivalence (ChainComplex C ℕ)).counitIso.inv_hom_id_app (N₁.obj X))
  simp only [Karoubi.comp_f, Karoubi.id_f, Functor.id_obj, N₁_obj_p] at h
  exact h

/-- The projection onto normalized chains is unchanged by first applying `PInfty`. -/
@[reassoc (attr := simp)]
lemma PInfty_comp_PInftyToN_app (X : SimplicialObject C) :
    PInfty ≫ PInftyToN.app X = PInftyToN.app X :=
  PInfty_comp_counitIso_inv_app_N₁_obj_f X

/-- Normalized chains are fixed by `PInfty`. -/
@[reassoc (attr := simp)]
lemma inclusionN_app_comp_PInfty (X : SimplicialObject C) :
    inclusionN.app X ≫ PInfty = inclusionN.app X :=
  counitIso_hom_app_N₁_obj_f_comp_PInfty X

/-- `N.map f` is obtained by restricting `(alternatingFaceMapComplex C).map f` to normalized
chains via `inclusionN` and projecting back via `PInftyToN`. -/
lemma N_map_eq_inclusionN_comp_PInftyToN {X Y : SimplicialObject C} (f : X ⟶ Y) :
    N.map f = inclusionN.app X ≫ (alternatingFaceMapComplex C).map f ≫ PInftyToN.app Y := by
  rw [PInftyToN.naturality, inclusionN_app_comp_PInftyToN_app_assoc]

/-- The projection `PInfty` followed by `(alternatingFaceMapComplex C).map f` factors through
`N.map f` via `PInftyToN` and `inclusionN`. -/
lemma PInfty_comp_alternatingFaceMapComplex_map_eq {X Y : SimplicialObject C} (f : X ⟶ Y) :
    PInfty ≫ (alternatingFaceMapComplex C).map f =
      PInftyToN.app X ≫ N.map f ≫ inclusionN.app Y := by
  rw [inclusionN.naturality, PInftyToN_app_comp_inclusionN_app_assoc]

/-- The normalized chain functor is a retract of the alternating face map complex functor, with
inclusion `CategoryTheory.Idempotents.DoldKan.inclusionN` and projection
`CategoryTheory.Idempotents.DoldKan.PInftyToN`. -/
def retractN : Retract (N : SimplicialObject C ⥤ _) (alternatingFaceMapComplex C) where
  i := inclusionN
  r := PInftyToN
  retract := by
    ext X : 2
    exact inclusionN_app_comp_PInftyToN_app X

/-- The inclusion of the normalized chains retract. -/
@[simp]
lemma retractN_i : (retractN (C := C)).i = inclusionN :=
  (rfl)

/-- The projection of the normalized chains retract. -/
@[simp]
lemma retractN_r : (retractN (C := C)).r = PInftyToN :=
  (rfl)

/-- In an idempotent-complete preadditive category with finite coproducts, the inclusion
`inclusionN.app X` and projection `PInftyToN.app X` form a chain homotopy equivalence between the
normalized chains `N.obj X` and the alternating face map complex `K[X]`. -/
def homotopyEquivNAlternatingFaceMapComplex (X : SimplicialObject C) :
    HomotopyEquiv (N.obj X) ((alternatingFaceMapComplex C).obj X) where
  hom := inclusionN.app X
  inv := PInftyToN.app X
  homotopyHomInvId := Homotopy.ofEq (inclusionN_app_comp_PInftyToN_app X)
  homotopyInvHomId :=
    (Homotopy.ofEq (PInftyToN_app_comp_inclusionN_app X)).trans (homotopyPInftyToId X)

@[simp]
lemma homotopyEquivNAlternatingFaceMapComplex_hom (X : SimplicialObject C) :
    (homotopyEquivNAlternatingFaceMapComplex X).hom = inclusionN.app X := (rfl)

@[simp]
lemma homotopyEquivNAlternatingFaceMapComplex_inv (X : SimplicialObject C) :
    (homotopyEquivNAlternatingFaceMapComplex X).inv = PInftyToN.app X := (rfl)

/-- The pseudoabelian Dold–Kan normalized chain functor `N` is fully faithful. -/
def N.fullyFaithful : (N (C := C)).FullyFaithful :=
  (equivalence (C := C)).fullyFaithfulFunctor.ofIso (CategoryTheory.eqToIso equivalence_functor)

/-- The pseudoabelian Dold–Kan normalized chain functor `N` is full. -/
instance N.full : (N (C := C)).Full :=
  N.fullyFaithful.full

/-- The pseudoabelian Dold–Kan normalized chain functor `N` is faithful. -/
instance N.faithful : (N (C := C)).Faithful :=
  N.fullyFaithful.faithful

end CategoryTheory.Idempotents.DoldKan
