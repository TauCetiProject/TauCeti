/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.QuotientSpecialIsogeny
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.Weyl.SpecialMap

/-!
# The exceptional F₄ isogeny on Weyl-transported root subgroups

The special isogeny sends a pinned simple Weyl representative to the representative at
the reversed Bourbaki node. Consequently it sends any Weyl-transported root subgroup
to the subgroup with every node in its presentation reversed. The target root is the
length-exchanged root, and the parameter exponent is one on long source roots and two
on short source roots. The identities hold over all commutative 𝔽₂-algebras, including
nonreduced ones.

For the selected forty-eight root maps, the target parametrization is displayed by its
Weyl word. It is not identified here with the separately selected parametrization at
the target root: that would require independence of Weyl presentation. Nor is the carrier
identified with the pinned simply connected group scheme.

## Main results

* `specialIsogeny_weylRootSubgroupPoints`: the formula for every Weyl presentation.
* `specialIsogeny_rootSubgroupPointsAt`: the formula for every selected root map.
* `geckWeylRootIndex_map_rootSubgroupPresentation`: identification of its target root.

The construction uses the simple-root equations of `QuotientSpecialIsogeny` and the
closed root maps of `PrimeField.Root.Subgroup`.

## References

* R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, §11.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3--12.4.
-/

public section

namespace TauCeti.F4ShortRoot.PrimeField

open DynkinType

noncomputable section

variable (A : Type) [CommRing A] [Algebra (ZMod 2) A]

/-- The exceptional isogeny reverses the node of each pinned simple Weyl representative. -/
@[simp] theorem specialIsogeny_simpleWeylPoint (i : Fin 4) :
    specialIsogeny A (simpleWeylPoint i A) = simpleWeylPoint (lengthPermF4 i) A := by
  have hneg : (-1 : A) = 1 := by
    simpa only [map_neg, map_one] using
      congrArg (algebraMap (ZMod 2) A) (by decide : (-1 : ZMod 2) = 1)
  fin_cases i <;>
    simp [simpleWeylPoint_def, isogenyReverse, isogenyExponent, lengthPermF4_apply, hneg]

/-- The exceptional isogeny reverses each node in a pinned Weyl word. -/
@[simp] theorem specialIsogeny_weylWordPoint (l : List (Fin 4)) :
    specialIsogeny A (weylWordPoint l A) = weylWordPoint (l.map lengthPermF4) A := by
  induction l with
  | nil => simp
  | cons j l ih => simp [ih]

/-- On every Weyl-transported root subgroup, the special isogeny replaces each node of the
Weyl word, and its starting node, by `lengthPermF4`, preserving word order and using the
exponent prescribed at the starting simple root. -/
@[simp↓] theorem specialIsogeny_weylRootSubgroupPoints (l : List (Fin 4)) (i : Fin 4)
    (u : Multiplicative A) :
    specialIsogeny A (weylRootSubgroupPoints l i A u) =
      weylRootSubgroupPoints (l.map lengthPermF4) (lengthPermF4 i) A
        (Multiplicative.ofAdd (u.toAdd ^ isogenyExponent (.inl i))) := by
  simp only [weylRootSubgroupPoints_apply, map_mul, map_inv,
    specialIsogeny_weylWordPoint, specialIsogeny_rootSubgroupPoints,
    isogenyReverse, Sum.map_inl, lengthPermF4_apply, Fin.revPerm_apply]

/-- The Weyl presentation with each node mapped by `lengthPermF4` parametrizes the
length-exchanged root of a selected root. -/
theorem geckWeylRootIndex_map_rootSubgroupPresentation (k : Fin F4.numRoots) :
    F4.geckWeylRootIndex valid_F4 ((F4ShortRoot.rootSubgroupPresentation k).1.map lengthPermF4)
        (lengthPermF4 (F4ShortRoot.rootSubgroupPresentation k).2) =
      f4SpecialIsogenyIndex k := by
  rw [← f4SpecialIsogenyIndex_geckWeylRootIndex,
    F4ShortRoot.weylRootIndex_rootSubgroupPresentation]

/-- The exponent on a Weyl-transported root is the length of its length-exchanged root:
one for a long source root and two for a short source root. -/
private theorem isogenyExponent_eq_f4Length_f4SpecialIsogenyIndex_geckWeylRootIndex
    (l : List (Fin 4)) (i : Fin 4) :
    isogenyExponent (.inl i) =
      (f4Length (f4SpecialIsogenyIndex (F4.geckWeylRootIndex valid_F4 l i))).toNat := by
  calc
    _ = (F4.rootLength (lengthPermF4 i)).toNat := by
      fin_cases i <;> simp [isogenyExponent, rootLength_F4, lengthPermF4_apply]
    _ = (f4Length
        (F4.geckWeylRootIndex valid_F4 (l.map lengthPermF4) (lengthPermF4 i))).toNat :=
      congrArg Int.toNat (f4Length_geckWeylRootIndex (l.map lengthPermF4) (lengthPermF4 i)).symm
    _ = _ := congrArg (fun k => (f4Length k).toNat)
      (f4SpecialIsogenyIndex_geckWeylRootIndex l i).symm

/-- The special isogeny on each of the forty-eight selected root maps. The image is given
by its Weyl presentation with each node mapped by `lengthPermF4`, at `f4SpecialIsogenyIndex k`;
the parameter exponent is one on long source roots and two on short source roots. -/
@[simp↓] theorem specialIsogeny_rootSubgroupPointsAt (k : Fin F4.numRoots) (u : Multiplicative A) :
    specialIsogeny A (rootSubgroupPointsAt k A u) =
      weylRootSubgroupPoints ((F4ShortRoot.rootSubgroupPresentation k).1.map lengthPermF4)
        (lengthPermF4 (F4ShortRoot.rootSubgroupPresentation k).2) A
        (Multiplicative.ofAdd (u.toAdd ^ (f4Length (f4SpecialIsogenyIndex k)).toNat)) := by
  rw [rootSubgroupPointsAt_def, specialIsogeny_weylRootSubgroupPoints,
    isogenyExponent_eq_f4Length_f4SpecialIsogenyIndex_geckWeylRootIndex
      (F4ShortRoot.rootSubgroupPresentation k).1 (F4ShortRoot.rootSubgroupPresentation k).2,
    F4ShortRoot.weylRootIndex_rootSubgroupPresentation]

end

end TauCeti.F4ShortRoot.PrimeField
