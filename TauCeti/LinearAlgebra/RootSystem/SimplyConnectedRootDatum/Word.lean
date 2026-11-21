/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimpleReflections
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# Bourbaki-numbered Weyl words in the pinned simply connected root datum

For a valid Dynkin type `t`, the pinned root datum `t.simplyConnectedRootDatum ht` has simple
roots numbered by `Fin t.rank` in the Bourbaki order via `t.simpleIndex ht` and
`t.simpleSupportEquivSimplyConnectedBase ht`. This file defines
`TauCeti.DynkinType.geckWeylWordProd`, evaluating a word `l : List (Fin t.rank)` into
`(t.simplyConnectedRootDatum ht).weylGroup`, together with its basic word-homomorphism and
surjectivity lemmas.

Separating this root-datum word evaluator from the Geck torus action keeps the abstract
Bourbaki-numbered Coxeter API (`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coxeter`)
independent of the represented Geck carrier.

## Main definitions

* `TauCeti.DynkinType.geckWeylWordProd`: the abstract Weyl-group element spelled by a word in the
  Bourbaki nodes.

## Main results

* `TauCeti.DynkinType.geckWeylWordProd_nil`, `TauCeti.DynkinType.geckWeylWordProd_cons`, and
  `TauCeti.DynkinType.geckWeylWordProd_append`: evaluation on empty, cons, and concatenated words.
* `TauCeti.DynkinType.geckWeylWordProd_surjective`: every element of the Weyl group is spelled by
  a word in the Bourbaki nodes.
-/

public section

namespace TauCeti.DynkinType

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

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

end

end TauCeti.DynkinType
