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
`TauCeti.DynkinType.simplyConnectedWeylWordProd`, evaluating a word `l : List (Fin t.rank)` into
`(t.simplyConnectedRootDatum ht).weylGroup`, together with its basic word-homomorphism and
surjectivity lemmas.

Separating this root-datum word evaluator from the Geck torus action keeps the abstract
Bourbaki-numbered Coxeter API (`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coxeter`)
independent of the represented Geck carrier.

## Main definitions

* `TauCeti.DynkinType.simplyConnectedWeylWordProd`: the abstract Weyl-group element spelled by a
  word in the Bourbaki nodes.

## Main results

* `TauCeti.DynkinType.simplyConnectedWeylWordProd_nil`,
  `TauCeti.DynkinType.simplyConnectedWeylWordProd_cons`, and
  `TauCeti.DynkinType.simplyConnectedWeylWordProd_append`: evaluation on empty, cons, and
  concatenated words.
* `TauCeti.DynkinType.wordProd_map_simpleSupportEquiv`: the word product agrees with
  `TauCeti.wordProd` of the transported word.
* `TauCeti.DynkinType.simplyConnectedWeylWordProd_surjective`: every element of the Weyl group is
  spelled by a word in the Bourbaki nodes.
-/

public section

namespace TauCeti.DynkinType

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- **The abstract Weyl-group element spelled by a word in the Bourbaki nodes.** The node indices
are transported to the support of the pinned simply connected base before multiplying the simple
reflections. -/
def simplyConnectedWeylWordProd (l : List (Fin t.rank)) :
    (t.simplyConnectedRootDatum ht).weylGroup :=
  TauCeti.wordProd (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
    (l.map (t.simpleSupportEquivSimplyConnectedBase ht))

/-- The empty word spells the identity Weyl-group element. -/
@[simp]
theorem simplyConnectedWeylWordProd_nil : t.simplyConnectedWeylWordProd ht [] = 1 := by
  simp [simplyConnectedWeylWordProd]

/-- Prepending a node multiplies the corresponding simple reflection on the left. -/
@[simp]
theorem simplyConnectedWeylWordProd_cons (i : Fin t.rank) (l : List (Fin t.rank)) :
    t.simplyConnectedWeylWordProd ht (i :: l) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) *
        t.simplyConnectedWeylWordProd ht l := by
  simp [simplyConnectedWeylWordProd]

/-- Concatenation of node words spells the product of their Weyl-group elements. -/
@[simp]
theorem simplyConnectedWeylWordProd_append (l l' : List (Fin t.rank)) :
    t.simplyConnectedWeylWordProd ht (l ++ l') =
      t.simplyConnectedWeylWordProd ht l * t.simplyConnectedWeylWordProd ht l' := by
  simp [simplyConnectedWeylWordProd]

/-- The abstract Weyl-group element spelled by a node word is the product of the corresponding
pinned simple reflections. -/
theorem simplyConnectedWeylWordProd_eq_prod_map (l : List (Fin t.rank)) :
    t.simplyConnectedWeylWordProd ht l =
      (l.map fun i =>
        RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht)
          (t.simpleIndex ht i)).prod := by
  rw [simplyConnectedWeylWordProd, RootPairing.Base.wordProd_def, List.map_map]
  simp only [Function.comp_def, coe_simpleSupportEquivSimplyConnectedBase_apply]

/-- Multiplying the simple reflections indexed by a Bourbaki-node word transported along
`simpleSupportEquivSimplyConnectedBase` recovers `simplyConnectedWeylWordProd`. -/
@[simp]
theorem wordProd_map_simpleSupportEquiv (l : List (Fin t.rank)) :
    TauCeti.wordProd (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
        (l.map (t.simpleSupportEquivSimplyConnectedBase ht)) =
      t.simplyConnectedWeylWordProd ht l :=
  (rfl)

/-- Every Weyl-group element is spelled by a word in the Bourbaki nodes. -/
theorem simplyConnectedWeylWordProd_surjective :
    Function.Surjective (t.simplyConnectedWeylWordProd ht) := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  intro w
  obtain ⟨l, hl⟩ := TauCeti.exists_wordProd_eq
    (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) w
  refine ⟨l.map (t.simpleSupportEquivSimplyConnectedBase ht).symm, ?_⟩
  have hmap :
      (l.map (t.simpleSupportEquivSimplyConnectedBase ht).symm).map
          (t.simpleSupportEquivSimplyConnectedBase ht) = l := by
    simp
  rw [simplyConnectedWeylWordProd, hmap]
  exact hl

end

end TauCeti.DynkinType
