/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.RootSystem.SimpleReflections
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# The Weyl-group action on the Geck torus

The pinned simple Weyl points of the Geck carrier act on its represented split torus by the
corresponding simple reflections. Products of those points were initially indexed by words in the
Bourbaki nodes. This file proves that the resulting action on the torus depends only on the element
of the Weyl group spelled by the word, and hence defines an action for every Weyl-group element.

The key calculation is contravariant on characters: if a word spells `w`, evaluating a character
at the transformed torus point is the same as evaluating `w⁻¹` applied to that character at the
original point. Characters separate the points of a split torus, so this identifies the action
without any assumption on the coefficient ring. The resulting comparison is the input for
transporting the numbered simple root subgroups to all roots and for comparing the torus normalizer
with the abstract Weyl group.

## Main declarations

* `TauCeti.DynkinType.geckWeylWord`: the abstract Weyl-group element spelled by a word in the
  Bourbaki nodes.
* `TauCeti.DynkinType.torusCharacter_geckWeylWordTorusAction`: the contravariant character formula
  for the word-level action.
* `TauCeti.DynkinType.geckWeylWordTorusAction_eq_of_geckWeylWord_eq`: two words spelling the same
  Weyl element induce the same torus action.
* `TauCeti.DynkinType.geckWeylTorusAction`: the resulting action of an abstract Weyl-group element
  on points of the split torus.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§7.1--7.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/

public section

namespace TauCeti.DynkinType

universe v v'

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-! ## Words in the abstract Weyl group -/

/-- **The abstract Weyl-group element spelled by a word in the Bourbaki nodes.** The node indices
are transported to the support of the pinned simply connected base before multiplying the simple
reflections. -/
def geckWeylWord (l : List (Fin t.rank)) : (t.simplyConnectedRootDatum ht).weylGroup :=
  TauCeti.wordProd (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
    (l.map (t.simpleSupportEquivSimplyConnectedBase ht))

/-- The empty word spells the identity Weyl-group element. -/
@[simp]
theorem geckWeylWord_nil : t.geckWeylWord ht [] = 1 := by
  simp [geckWeylWord]

/-- Prepending a node multiplies the corresponding simple reflection on the left. -/
@[simp]
theorem geckWeylWord_cons (i : Fin t.rank) (l : List (Fin t.rank)) :
    t.geckWeylWord ht (i :: l) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) *
        t.geckWeylWord ht l := by
  simp [geckWeylWord]

/-- Concatenation of node words spells the product of their Weyl-group elements. -/
@[simp]
theorem geckWeylWord_append (l l' : List (Fin t.rank)) :
    t.geckWeylWord ht (l ++ l') = t.geckWeylWord ht l * t.geckWeylWord ht l' := by
  simp [geckWeylWord]

/-- Every Weyl-group element is spelled by a word in the Bourbaki nodes. -/
theorem geckWeylWord_surjective : Function.Surjective (t.geckWeylWord ht) := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  intro w
  obtain ⟨l, hl⟩ := TauCeti.exists_wordProd_eq
    (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) w
  refine ⟨l.map (t.simpleSupportEquivSimplyConnectedBase ht).symm, ?_⟩
  have hmap :
      (l.map (t.simpleSupportEquivSimplyConnectedBase ht).symm).map
          (t.simpleSupportEquivSimplyConnectedBase ht) = l := by
    simp
  rw [geckWeylWord, hmap]
  exact hl

/-! ## Characters of the word-level action -/

private theorem coroot'_simpleIndex_apply (i : Fin t.rank) (mu : Fin t.rank → ℤ) :
    (t.simplyConnectedRootDatum ht).coroot' (t.simpleIndex ht i) mu = mu i := by
  -- `coroot'` reduces through the coercion of a root pairing to two nested linear maps.
  change (t.simplyConnectedRootDatum ht).toLinearMap mu
    ((t.simplyConnectedRootDatum ht).coroot (t.simpleIndex ht i)) = mu i
  rw [t.toLinearMap_simplyConnectedRootDatum ht,
    t.coroot_simpleIndex ht i, dotProduct_single, mul_one]

/-- A simple Geck reflection acts contravariantly on characters by the corresponding simple
reflection of the pinned root datum. -/
theorem torusCharacter_geckSimpleReflectionTorusPoint (i : Fin t.rank)
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) (mu : Fin t.rank → ℤ) :
    TauCeti.torusCharacter (t.geckSimpleReflectionTorusPoint ht i A s) mu =
      TauCeti.torusCharacter s
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht)
          (t.simpleIndex ht i) • mu) := by
  rw [t.geckSimpleReflectionTorusPoint_def ht,
    TauCeti.torusCharacter_weylReflectTorusPoint,
    RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_smul,
    RootPairing.reflection_apply, t.coroot'_simpleIndex_apply ht]

/-- **The character formula for a Geck Weyl word.** If the word spells `w`, its action on torus
points is dual to the action of `w⁻¹` on the character lattice. -/
theorem torusCharacter_geckWeylWordTorusAction (l : List (Fin t.rank))
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) (mu : Fin t.rank → ℤ) :
    TauCeti.torusCharacter (t.geckWeylWordTorusAction ht l A s) mu =
      TauCeti.torusCharacter s ((t.geckWeylWord ht l)⁻¹ • mu) := by
  induction l generalizing mu with
  | nil => simp
  | cons i l ih =>
      rw [geckWeylWordTorusAction_cons, MonoidHom.comp_apply,
        t.torusCharacter_geckSimpleReflectionTorusPoint ht, ih,
        geckWeylWord_cons, mul_inv_rev, RootPairing.weylGroup.ofIdx_inv_eq, mul_smul]

/-- **Weyl words spelling the same abstract element induce the same action on the split torus.**
This holds over every commutative coefficient ring: the coordinate characters already separate
torus points. -/
theorem geckWeylWordTorusAction_eq_of_geckWeylWord_eq
    {l l' : List (Fin t.rank)} (h : t.geckWeylWord ht l = t.geckWeylWord ht l')
    (A : Type v) [CommRing A] :
    t.geckWeylWordTorusAction ht l A = t.geckWeylWordTorusAction ht l' A := by
  apply MonoidHom.ext
  intro s
  funext i
  rw [← TauCeti.weightChar_single A i (t.geckWeylWordTorusAction ht l A s),
    ← TauCeti.weightChar_single A i (t.geckWeylWordTorusAction ht l' A s),
    TauCeti.weightChar_apply, TauCeti.weightChar_apply,
    t.torusCharacter_geckWeylWordTorusAction ht,
    t.torusCharacter_geckWeylWordTorusAction ht, h]

/-! ## The action of an abstract Weyl-group element -/

private noncomputable def geckWeylWordRepresentative
    (w : (t.simplyConnectedRootDatum ht).weylGroup) :
    List (Fin t.rank) :=
  Classical.choose (t.geckWeylWord_surjective ht w)

private theorem geckWeylWord_geckWeylWordRepresentative
    (w : (t.simplyConnectedRootDatum ht).weylGroup) :
    t.geckWeylWord ht (t.geckWeylWordRepresentative ht w) = w :=
  Classical.choose_spec (t.geckWeylWord_surjective ht w)

/-- **The action of an abstract Weyl-group element on points of the represented split torus.**
It is characterized by `geckWeylTorusAction_eq_word`, so callers need not choose a word. -/
noncomputable def geckWeylTorusAction (w : (t.simplyConnectedRootDatum ht).weylGroup)
    (A : Type v) [CommRing A] : (Fin t.rank → Aˣ) →* (Fin t.rank → Aˣ) :=
  t.geckWeylWordTorusAction ht (t.geckWeylWordRepresentative ht w) A

/-- The abstract Weyl action agrees with the word-level action of any word spelling the element. -/
theorem geckWeylTorusAction_eq_word {w : (t.simplyConnectedRootDatum ht).weylGroup}
    {l : List (Fin t.rank)} (hl : t.geckWeylWord ht l = w)
    (A : Type v) [CommRing A] :
    t.geckWeylTorusAction ht w A = t.geckWeylWordTorusAction ht l A := by
  apply t.geckWeylWordTorusAction_eq_of_geckWeylWord_eq ht
  rw [t.geckWeylWord_geckWeylWordRepresentative ht, hl]

/-- The identity Weyl-group element acts identically on torus points. -/
@[simp]
theorem geckWeylTorusAction_one (A : Type v) [CommRing A] :
    t.geckWeylTorusAction ht 1 A = MonoidHom.id _ := by
  rw [t.geckWeylTorusAction_eq_word ht (l := []) (by simp), geckWeylWordTorusAction_nil]

/-- The abstract action of a simple reflection is the pinned simple reflection on torus points. -/
@[simp]
theorem geckWeylTorusAction_ofIdx (i : Fin t.rank) (A : Type v) [CommRing A] :
    t.geckWeylTorusAction ht
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht)
          (t.simpleIndex ht i)) A =
      t.geckSimpleReflectionTorusPoint ht i A := by
  rw [t.geckWeylTorusAction_eq_word ht (l := [i]) (by simp),
    geckWeylWordTorusAction_cons, geckWeylWordTorusAction_nil]
  rfl

/-- Multiplication in the Weyl group corresponds to composition of its actions on torus points. -/
@[simp]
theorem geckWeylTorusAction_mul
    (w w' : (t.simplyConnectedRootDatum ht).weylGroup)
    (A : Type v) [CommRing A] :
    t.geckWeylTorusAction ht (w * w') A =
      (t.geckWeylTorusAction ht w A).comp (t.geckWeylTorusAction ht w' A) := by
  obtain ⟨l, rfl⟩ := t.geckWeylWord_surjective ht w
  obtain ⟨l', rfl⟩ := t.geckWeylWord_surjective ht w'
  rw [t.geckWeylTorusAction_eq_word ht (l := l ++ l') (by simp),
    geckWeylWordTorusAction_append,
    t.geckWeylTorusAction_eq_word ht (l := l) rfl,
    t.geckWeylTorusAction_eq_word ht (l := l') rfl]

/-- The abstract Weyl action is natural in the commutative ring of torus-point values. -/
@[simp]
theorem map_geckWeylTorusAction {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) (w : (t.simplyConnectedRootDatum ht).weylGroup)
    (s : Fin t.rank → Aˣ) (i : Fin t.rank) :
    Units.map (f : A →* B) (t.geckWeylTorusAction ht w A s i) =
      t.geckWeylTorusAction ht w B (fun j ↦ Units.map (f : A →* B) (s j)) i := by
  obtain ⟨l, rfl⟩ := t.geckWeylWord_surjective ht w
  rw [t.geckWeylTorusAction_eq_word ht (l := l) rfl,
    t.geckWeylTorusAction_eq_word ht (l := l) rfl]
  exact t.map_geckWeylWordTorusAction ht f l s i

/-- Characters transform contravariantly under the abstract Weyl action. -/
theorem torusCharacter_geckWeylTorusAction
    (w : (t.simplyConnectedRootDatum ht).weylGroup)
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) (mu : Fin t.rank → ℤ) :
    TauCeti.torusCharacter (t.geckWeylTorusAction ht w A s) mu =
      TauCeti.torusCharacter s (w⁻¹ • mu) := by
  obtain ⟨l, rfl⟩ := t.geckWeylWord_surjective ht w
  rw [t.geckWeylTorusAction_eq_word ht (l := l) rfl]
  exact t.torusCharacter_geckWeylWordTorusAction ht l A s mu

end

end TauCeti.DynkinType
