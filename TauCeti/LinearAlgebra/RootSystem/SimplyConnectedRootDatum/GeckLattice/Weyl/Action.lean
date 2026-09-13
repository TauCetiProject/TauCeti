/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.RootSystem.SimpleReflections
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic
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
over every commutative coefficient ring. The resulting comparison is the input for
transporting the numbered simple root subgroups to all roots and for comparing the torus normalizer
with the abstract Weyl group.

## Main declarations

* `TauCeti.DynkinType.geckWeylWordProd`: the abstract Weyl-group element spelled by a word in the
  Bourbaki nodes.
* `TauCeti.DynkinType.torusCharacter_geckWeylWordTorusAction`: the contravariant character formula
  for the word-level action.
* `TauCeti.DynkinType.geckWeylWordTorusAction_eq_of_geckWeylWordProd_eq`: two words spelling the
  same Weyl element induce the same torus action.
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
def geckWeylWordProd (l : List (Fin t.rank)) : (t.simplyConnectedRootDatum ht).weylGroup :=
  TauCeti.wordProd (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
    (l.map (t.simpleSupportEquivSimplyConnectedBase ht))

/-- The empty word spells the identity Weyl-group element. -/
@[simp]
theorem geckWeylWordProd_nil : t.geckWeylWordProd ht [] = 1 := by
  simp [geckWeylWordProd]

/-- Prepending a node multiplies the corresponding simple reflection on the left. -/
@[simp]
theorem geckWeylWordProd_cons (i : Fin t.rank) (l : List (Fin t.rank)) :
    t.geckWeylWordProd ht (i :: l) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) *
        t.geckWeylWordProd ht l := by
  simp [geckWeylWordProd]

/-- Concatenation of node words spells the product of their Weyl-group elements. -/
@[simp]
theorem geckWeylWordProd_append (l l' : List (Fin t.rank)) :
    t.geckWeylWordProd ht (l ++ l') =
      t.geckWeylWordProd ht l * t.geckWeylWordProd ht l' := by
  simp [geckWeylWordProd]

/-- Every Weyl-group element is spelled by a word in the Bourbaki nodes. -/
theorem geckWeylWordProd_surjective : Function.Surjective (t.geckWeylWordProd ht) := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  intro w
  obtain ⟨l, hl⟩ := TauCeti.exists_wordProd_eq
    (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) w
  refine ⟨l.map (t.simpleSupportEquivSimplyConnectedBase ht).symm, ?_⟩
  have hmap :
      (l.map (t.simpleSupportEquivSimplyConnectedBase ht).symm).map
          (t.simpleSupportEquivSimplyConnectedBase ht) = l := by
    simp
  rw [geckWeylWordProd, hmap]
  exact hl

/-! ## Characters of the word-level action -/

/-- A simple Geck reflection acts contravariantly on characters by the corresponding simple
reflection of the pinned root datum. -/
@[simp]
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
@[simp]
theorem torusCharacter_geckWeylWordTorusAction (l : List (Fin t.rank))
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) (mu : Fin t.rank → ℤ) :
    TauCeti.torusCharacter (t.geckWeylWordTorusAction ht l A s) mu =
      TauCeti.torusCharacter s ((t.geckWeylWordProd ht l)⁻¹ • mu) := by
  induction l generalizing mu with
  | nil => simp
  | cons i l ih =>
      rw [geckWeylWordTorusAction_cons, MonoidHom.comp_apply,
        t.torusCharacter_geckSimpleReflectionTorusPoint ht, ih,
        geckWeylWordProd_cons, mul_inv_rev, RootPairing.weylGroup.ofIdx_inv_eq, mul_smul]

/-- **Weyl words spelling the same abstract element induce the same action on the split torus.**
This holds over every commutative coefficient ring: the coordinate characters already separate
torus points. -/
theorem geckWeylWordTorusAction_eq_of_geckWeylWordProd_eq
    {l l' : List (Fin t.rank)} (h : t.geckWeylWordProd ht l = t.geckWeylWordProd ht l')
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

private noncomputable def geckWeylTorusEndomorphism
    (w : (t.simplyConnectedRootDatum ht).weylGroup)
    (A : Type v) [CommRing A] : (Fin t.rank → Aˣ) →* (Fin t.rank → Aˣ) :=
  t.geckWeylWordTorusAction ht
    (Function.surjInv (t.geckWeylWordProd_surjective ht) w) A

private theorem geckWeylTorusEndomorphism_eq_word
    {w : (t.simplyConnectedRootDatum ht).weylGroup} {l : List (Fin t.rank)}
    (hl : t.geckWeylWordProd ht l = w) (A : Type v) [CommRing A] :
    t.geckWeylTorusEndomorphism ht w A = t.geckWeylWordTorusAction ht l A := by
  apply t.geckWeylWordTorusAction_eq_of_geckWeylWordProd_eq ht
  rw [Function.surjInv_eq (t.geckWeylWordProd_surjective ht), hl]

private theorem geckWeylTorusEndomorphism_one (A : Type v) [CommRing A] :
    t.geckWeylTorusEndomorphism ht 1 A = MonoidHom.id _ := by
  rw [t.geckWeylTorusEndomorphism_eq_word ht (l := []) (by simp),
    geckWeylWordTorusAction_nil]

private theorem geckWeylTorusEndomorphism_mul
    (w w' : (t.simplyConnectedRootDatum ht).weylGroup)
    (A : Type v) [CommRing A] :
    t.geckWeylTorusEndomorphism ht (w * w') A =
      (t.geckWeylTorusEndomorphism ht w A).comp
        (t.geckWeylTorusEndomorphism ht w' A) := by
  obtain ⟨l, rfl⟩ := t.geckWeylWordProd_surjective ht w
  obtain ⟨l', rfl⟩ := t.geckWeylWordProd_surjective ht w'
  rw [t.geckWeylTorusEndomorphism_eq_word ht (l := l ++ l') (by simp),
    geckWeylWordTorusAction_append,
    t.geckWeylTorusEndomorphism_eq_word ht (l := l) rfl,
    t.geckWeylTorusEndomorphism_eq_word ht (l := l') rfl]

/-- **The Weyl-group action by automorphisms of the represented split torus.** Its value at a
Weyl-group element is characterized by `geckWeylTorusAction_eq_word`, so callers need not choose
a word. -/
noncomputable def geckWeylTorusAction (A : Type v) [CommRing A] :
    (t.simplyConnectedRootDatum ht).weylGroup →* MulAut (Fin t.rank → Aˣ) where
  toFun w := MonoidHom.toMulEquiv
    (t.geckWeylTorusEndomorphism ht w A)
    (t.geckWeylTorusEndomorphism ht w⁻¹ A)
    (by
      rw [← t.geckWeylTorusEndomorphism_mul ht]
      simpa using t.geckWeylTorusEndomorphism_one ht A)
    (by
      rw [← t.geckWeylTorusEndomorphism_mul ht]
      simpa using t.geckWeylTorusEndomorphism_one ht A)
  map_one' := by
    apply MulEquiv.ext
    intro s
    change t.geckWeylTorusEndomorphism ht 1 A s = s
    simpa using DFunLike.congr_fun (t.geckWeylTorusEndomorphism_one ht A) s
  map_mul' w w' := by
    apply MulEquiv.ext
    intro s
    change t.geckWeylTorusEndomorphism ht (w * w') A s =
      t.geckWeylTorusEndomorphism ht w A
        (t.geckWeylTorusEndomorphism ht w' A s)
    simpa using DFunLike.congr_fun (t.geckWeylTorusEndomorphism_mul ht w w' A) s

/-- The abstract Weyl action agrees with the word-level action of any word spelling the element. -/
theorem geckWeylTorusAction_eq_word {w : (t.simplyConnectedRootDatum ht).weylGroup}
    {l : List (Fin t.rank)} (hl : t.geckWeylWordProd ht l = w)
    (A : Type v) [CommRing A] :
    (t.geckWeylTorusAction ht A w).toMonoidHom = t.geckWeylWordTorusAction ht l A := by
  exact t.geckWeylTorusEndomorphism_eq_word ht hl A

/-- Pointwise form of `geckWeylTorusAction_eq_word`. -/
theorem geckWeylTorusAction_apply_eq_word {w : (t.simplyConnectedRootDatum ht).weylGroup}
    {l : List (Fin t.rank)} (hl : t.geckWeylWordProd ht l = w)
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    t.geckWeylTorusAction ht A w s = t.geckWeylWordTorusAction ht l A s := by
  exact DFunLike.congr_fun (t.geckWeylTorusAction_eq_word ht hl A) s

/-- The abstract action of a simple reflection is the pinned simple reflection on torus points. -/
@[simp]
theorem geckWeylTorusAction_ofIdx (i : Fin t.rank) (A : Type v) [CommRing A] :
    (t.geckWeylTorusAction ht A
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht)
          (t.simpleIndex ht i))).toMonoidHom =
      t.geckSimpleReflectionTorusPoint ht i A := by
  rw [t.geckWeylTorusAction_eq_word ht (l := [i]) (by simp),
    geckWeylWordTorusAction_cons, geckWeylWordTorusAction_nil]
  exact MonoidHom.comp_id _

/-- The abstract Weyl action is natural in the commutative ring of torus-point values. -/
@[simp]
theorem map_geckWeylTorusAction {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) (w : (t.simplyConnectedRootDatum ht).weylGroup)
    (s : Fin t.rank → Aˣ) (i : Fin t.rank) :
    Units.map (f : A →* B) (t.geckWeylTorusAction ht A w s i) =
      t.geckWeylTorusAction ht B w (fun j ↦ Units.map (f : A →* B) (s j)) i := by
  obtain ⟨l, rfl⟩ := t.geckWeylWordProd_surjective ht w
  rw [t.geckWeylTorusAction_apply_eq_word ht (l := l) rfl,
    t.geckWeylTorusAction_apply_eq_word ht (l := l) rfl]
  exact t.map_geckWeylWordTorusAction ht f l s i

/-- Characters transform contravariantly under the abstract Weyl action. -/
@[simp]
theorem torusCharacter_geckWeylTorusAction
    (w : (t.simplyConnectedRootDatum ht).weylGroup)
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) (mu : Fin t.rank → ℤ) :
    TauCeti.torusCharacter (t.geckWeylTorusAction ht A w s) mu =
      TauCeti.torusCharacter s (w⁻¹ • mu) := by
  obtain ⟨l, rfl⟩ := t.geckWeylWordProd_surjective ht w
  rw [t.geckWeylTorusAction_apply_eq_word ht (l := l) rfl]
  exact t.torusCharacter_geckWeylWordTorusAction ht l A s mu

end

end TauCeti.DynkinType
