/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.ClosedRootSubgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Action
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit

/-!
# Root subgroups of the Geck carrier at every root

The Geck carrier of a valid Dynkin type comes with root subgroups `x_{±i}` only at the numbered
simple roots `±α_i`. Every root of the pinned simply connected root datum is a Weyl-group image
`w α_i` of a simple root, and the Weyl words of the carrier supply representatives `n_w` of the
Weyl group. Conjugating the simple root subgroup at node `i` by the representative of a word `l`
spelling `w` therefore gives a copy of the additive group

```text
x_{l,i}(u) = n_l xᵢ(u) n_l⁻¹
```

inside the carrier, and the split weight torus rescales its parameter through the character
`w α_i`:

```text
s x_{l,i}(u) s⁻¹ = x_{l,i}((w α_i)(s) u).
```

That is the pinning equation of a root subgroup at the root `w α_i`, and every root arises this
way. The construction is indexed by the word and the node, like the Weyl representatives it is
built from. Two presentations `(l, i)` of the same root give root subgroups with the same image in
a Chevalley group, with parametrizations that agree up to the sign of the parameter; no
comparison between different presentations is made here.

## Main definitions

* `TauCeti.DynkinType.geckWeylRootIndex`: the root index `w α_i` attached to a word `l` spelling
  `w` and a node `i`.
* `TauCeti.DynkinType.geckWeylRootSubgroupPoints`: the root subgroup `x_{l,i}` in the points of the
  Geck carrier over a commutative ring.

## Main results

* `TauCeti.DynkinType.exists_geckWeylRootIndex_eq`: every root index is `w α_i` for some word and
  node, with `TauCeti.DynkinType.root_geckWeylRootIndex` identifying the root.
* `TauCeti.DynkinType.geckWeightTorusPoints_conj_geckWeylRootSubgroupPoints`: the weight torus
  rescales the parameter of `x_{l,i}` through the root at `geckWeylRootIndex l i`.
* `TauCeti.DynkinType.geckWeylRootSubgroupPoints_nil` and
  `TauCeti.DynkinType.geckWeylRootSubgroupPoints_singleton_self`: the empty word gives the raising
  subgroup at node `i`, and the word `[i]` gives the lowering subgroup at node `i` with negated
  parameter, at the root `-α_i` by `TauCeti.DynkinType.root_geckWeylRootIndex_singleton_self`.
* `TauCeti.DynkinType.geckWeylRootSubgroupPoints_injective` and
  `TauCeti.DynkinType.map_geckWeylRootSubgroupPoints`: each `x_{l,i}` is injective and natural in
  the value ring.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.3.
-/

public section

namespace TauCeti.DynkinType

universe v v'

noncomputable section

-- Matrices form a Lie ring through their commutator in the defining Geck representation.
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] TauCeti.moduleNNRat
-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

/-! ## The root attached to a word and a node -/

/-- **The root index attached to a Weyl word and a node**: the index of `w α_i`, for `w` the
Weyl-group element spelled by `l` and `α_i` the simple root at the Bourbaki node `i` of the pinned
simply connected root datum. -/
def geckWeylRootIndex (l : List (Fin t.rank)) (i : Fin t.rank) : Fin t.numRoots :=
  (t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht l) (t.simpleIndex ht i)

/-- The root at `geckWeylRootIndex l i` is the image of the simple root `α_i` under the Weyl-group
element spelled by `l`. -/
theorem root_geckWeylRootIndex (l : List (Fin t.rank)) (i : Fin t.rank) :
    (t.simplyConnectedRootDatum ht).root (t.geckWeylRootIndex ht l i) =
      t.geckWeylWordProd ht l • (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i) :=
  (RootPairing.weylGroup_apply_root _ _ _).symm

/-- The empty word attaches the simple root itself. -/
@[simp]
theorem geckWeylRootIndex_nil (i : Fin t.rank) :
    t.geckWeylRootIndex ht [] i = t.simpleIndex ht i := by
  simp [geckWeylRootIndex]

/-- Prepending a node reflects the attached root in the corresponding simple root. -/
theorem geckWeylRootIndex_cons (j : Fin t.rank) (l : List (Fin t.rank)) (i : Fin t.rank) :
    t.geckWeylRootIndex ht (j :: l) i =
      (t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht j)
        (t.geckWeylRootIndex ht l i) := by
  rw [geckWeylRootIndex, geckWeylWordProd_cons, RootPairing.weylGroupToPerm_ofIdx_mul_apply,
    geckWeylRootIndex]

/-- The one-letter word `[i]` attaches to the node `i` the negative of the simple root `α_i`. -/
@[simp]
theorem root_geckWeylRootIndex_singleton_self (i : Fin t.rank) :
    (t.simplyConnectedRootDatum ht).root (t.geckWeylRootIndex ht [i] i) =
      -(t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i) := by
  rw [root_geckWeylRootIndex, geckWeylWordProd_cons, geckWeylWordProd_nil, mul_one,
    RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_smul,
    RootPairing.reflection_apply_self]

/-- **Every root is attached to some word and node**: each root index of the pinned simply
connected root datum is `w α_i` for a Weyl word spelling `w` and a Bourbaki node `i`. -/
theorem exists_geckWeylRootIndex_eq (k : Fin t.numRoots) :
    ∃ (l : List (Fin t.rank)) (i : Fin t.rank), t.geckWeylRootIndex ht l i = k := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  obtain ⟨j, hj, w, hw⟩ := exists_mem_support_weylGroupToPerm_eq (t.simplyConnectedBase ht) k
  obtain ⟨l, rfl⟩ := t.geckWeylWordProd_surjective ht w
  refine ⟨l, (t.simpleSupportEquivSimplyConnectedBase ht).symm ⟨j, hj⟩, ?_⟩
  rw [geckWeylRootIndex, ← coe_simpleSupportEquivSimplyConnectedBase, Equiv.apply_symm_apply]
  exact hw

/-! ## The root subgroup attached to a word and a node -/

/-- **The root subgroup of the Geck carrier attached to a Weyl word and a node**: the conjugate
`x_{l,i}(u) = n_l xᵢ(u) n_l⁻¹` of the numbered raising subgroup at node `i` by the Weyl
representative of the word `l`. Its root is `geckWeylRootIndex l i`, by
`geckWeightTorusPoints_conj_geckWeylRootSubgroupPoints`. -/
def geckWeylRootSubgroupPoints (l : List (Fin t.rank)) (i : Fin t.rank) (A : Type v)
    [CommRing A] : Multiplicative A →* t.geckPoints ht A :=
  (MulAut.conj (t.geckWeylWordPoint ht l A)).toMonoidHom.comp
    (t.geckRootSubgroupPoints ht (.inl i) A)

/-- The root subgroup attached to a word is the conjugate of the numbered raising subgroup by the
word's Weyl representative. -/
@[simp]
theorem geckWeylRootSubgroupPoints_apply (l : List (Fin t.rank)) (i : Fin t.rank)
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    t.geckWeylRootSubgroupPoints ht l i A u =
      t.geckWeylWordPoint ht l A * t.geckRootSubgroupPoints ht (.inl i) A u *
        (t.geckWeylWordPoint ht l A)⁻¹ :=
  (rfl)

/-- The empty word gives the numbered raising subgroup at node `i`. -/
@[simp]
theorem geckWeylRootSubgroupPoints_nil (i : Fin t.rank) (A : Type v) [CommRing A] :
    t.geckWeylRootSubgroupPoints ht [] i A = t.geckRootSubgroupPoints ht (.inl i) A := by
  ext u
  simp

/-- Prepending a node conjugates by the corresponding simple Weyl representative. -/
theorem geckWeylRootSubgroupPoints_cons (j : Fin t.rank) (l : List (Fin t.rank))
    (i : Fin t.rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    t.geckWeylRootSubgroupPoints ht (j :: l) i A u =
      t.geckSimpleWeylPoint ht j A * t.geckWeylRootSubgroupPoints ht l i A u *
        (t.geckSimpleWeylPoint ht j A)⁻¹ := by
  simp only [geckWeylRootSubgroupPoints_apply, geckWeylWordPoint_cons]
  group

/-- **The word `[i]` gives the lowering subgroup at node `i`**, with negated parameter: the simple
Weyl representative at `i` conjugates `xᵢ(u)` to `x₋ᵢ(-u)`. -/
theorem geckWeylRootSubgroupPoints_singleton_self (i : Fin t.rank) (A : Type v) [CommRing A]
    (u : A) :
    t.geckWeylRootSubgroupPoints ht [i] i A (Multiplicative.ofAdd u) =
      t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd (-u)) := by
  rw [geckWeylRootSubgroupPoints_cons, geckWeylRootSubgroupPoints_nil,
    geckSimpleWeylPoint_conj_geckRootSubgroupPoints]

/-- Each root subgroup attached to a word is injective on parameters. -/
theorem geckWeylRootSubgroupPoints_injective (l : List (Fin t.rank)) (i : Fin t.rank)
    (A : Type v) [CommRing A] : Function.Injective (t.geckWeylRootSubgroupPoints ht l i A) :=
  (MulAut.conj (t.geckWeylWordPoint ht l A)).injective.comp
    (t.geckRootSubgroupPoints_injective ht (.inl i) A)

/-- **The root subgroup attached to a word is natural in the value ring**: a ring homomorphism
`f : A →+* B` carries `x_{l,i}(u)` over `A` to `x_{l,i}(f u)` over `B`. -/
theorem map_geckWeylRootSubgroupPoints {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) (l : List (Fin t.rank)) (i : Fin t.rank) (u : Multiplicative A) :
    (t.geckPointsPresentation ht A).map (t.geckPointsPresentation ht B) f
        (t.geckWeylRootSubgroupPoints ht l i A u) =
      t.geckWeylRootSubgroupPoints ht l i B
        (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  rw [geckWeylRootSubgroupPoints_apply, geckWeylRootSubgroupPoints_apply, map_mul, map_mul,
    map_inv, map_geckWeylWordPoint, map_geckRootSubgroupPoints]

/-! ## The pinning equation at every root -/

/-- **The pinning equation of the root subgroup attached to a word.** Conjugation by a weight-torus
point `s` rescales the parameter of `x_{l,i}` by `α(s)`, for `α` the root at
`geckWeylRootIndex l i`, that is `w α_i` with `w` the Weyl-group element spelled by `l`. -/
theorem geckWeightTorusPoints_conj_geckWeylRootSubgroupPoints (l : List (Fin t.rank))
    (i : Fin t.rank) (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) (u : Multiplicative A) :
    t.geckWeightTorusPoints ht A s * t.geckWeylRootSubgroupPoints ht l i A u *
        (t.geckWeightTorusPoints ht A s)⁻¹ =
      t.geckWeylRootSubgroupPoints ht l i A
        (Multiplicative.ofAdd
          ((torusCharacter s
              ((t.simplyConnectedRootDatum ht).root (t.geckWeylRootIndex ht l i)) : A) *
            Multiplicative.toAdd u)) := by
  set w := t.geckWeylWordProd ht l
  -- Write `s` as the word's action on `s' = w⁻¹ • s`, so that the torus point of `s` is the
  -- conjugate of the torus point of `s'` by the word's Weyl representative.
  set s' := t.geckWeylTorusAction ht A w⁻¹ s
  have hs : t.geckWeylWordTorusAction ht l A s' = s := by
    rw [← t.geckWeylTorusAction_apply_eq_word ht rfl, ← MulAut.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, MulAut.one_apply]
  have hT := t.geckWeylWordPoint_conj_geckWeightTorusPoints ht l A s'
  rw [hs] at hT
  have hchar :
      (torusCharacter s' ((t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i)) : A) =
        torusCharacter s ((t.simplyConnectedRootDatum ht).root (t.geckWeylRootIndex ht l i)) := by
    rw [torusCharacter_geckWeylTorusAction, inv_inv, root_geckWeylRootIndex]
  simp only [geckWeylRootSubgroupPoints_apply, ← hT, ← hchar,
    ← t.geckWeightTorusPoints_conj_geckRootSubgroupPoints_root_simpleIndex ht i A s' u]
  group

end

end TauCeti.DynkinType
