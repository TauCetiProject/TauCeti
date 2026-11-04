/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.RootSubgroup
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Gauss
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Gauss

/-!
# Opposite-root Gauss factorization in the Geck carrier

For a valid Dynkin type `t`, the numbered simple raising and lowering generators at each Bourbaki
node `i : Fin t.rank` form an `sl₂` pair in the defining matrix representation of Geck's Lie
algebra. Unlike minuscule or standard classical representations, Geck's representation is modeled on
the adjoint module, where root operators do not square to zero (root strings have length three for
simply laced or long roots and four in type `G₂`).

This file specializes the general Kostant opposite-root Gauss factorizations to the pinned Geck
lattice and its toral-closure group scheme, and then transports them by Weyl conjugation to every
root of `TauCeti.DynkinType.simplyConnectedRootDatum`. Over any commutative ring `A`:

* For any `a, b ∈ A` such that `u = 1 + a b` is a unit of `A`, the opposite simple-root elements at
  node `i` factor in both multiplication orders through the `i`-th coordinate of the represented
  split weight torus (which is the simple coroot `αᵢ^∨` by
  `TauCeti.DynkinType.coroot_simpleIndex`):
  ```text
  xᵢ(a) x₋ᵢ(b) = x₋ᵢ(b u⁻¹) t(Pi.mulSingle i u) xᵢ(a u⁻¹),
  x₋ᵢ(b) xᵢ(a) = xᵢ(a u⁻¹) t(Pi.mulSingle i u⁻¹) x₋ᵢ(b u⁻¹).
  ```
* For any Weyl word `l` and node `i`, the word presentations `(l, i)` and `(l ++ [i], i)` attach
  opposite roots `α` and `-α` at `r = geckWeylRootIndex l i`. Because `x_{[i],i}(b) = x₋ᵢ(-b)`,
  whenever `u = 1 - a b` is a unit of `A`, their root-subgroup elements factor through the coroot
  cocharacter `k ↦ u ^ (coroot r k)` of `r` (depending only on the root index `r`, not on the word
  `l` or node `i`).

## Main results

* `TauCeti.DynkinType.geckRootSubgroupParam_inl_mul_inr` and
  `TauCeti.DynkinType.geckRootSubgroupParam_inr_mul_inl`: opposite-simple-root Gauss factorizations
  on base-changed Geck lattice automorphisms.
* `TauCeti.DynkinType.geckRootSubgroupPoints_inl_mul_inr` and
  `TauCeti.DynkinType.geckRootSubgroupPoints_inr_mul_inl`: opposite-simple-root Gauss factorizations
  inside the matrix point group `TauCeti.DynkinType.geckPoints`.
* `TauCeti.DynkinType.geckWeylWordTorusAction_mulSingle` and
  `TauCeti.DynkinType.geckWeylTorusAction_mulSingle`: Weyl transport carries `Pi.mulSingle i u` to
  the coroot torus point `k ↦ u ^ (coroot (geckWeylRootIndex l i) k)`.
* `TauCeti.DynkinType.geckWeylRootSubgroupPoints_mul_append_singleton_self` and
  `TauCeti.DynkinType.geckWeylRootSubgroupPoints_append_singleton_self_mul`: opposite-root Gauss
  factorizations at every Weyl-word root pair `(l, i)` and `(l ++ [i], i)`.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3, Lemmas 19--20.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 12.1.
-/

public section

namespace TauCeti.DynkinType

universe v

noncomputable section

-- Matrices form a Lie ring through their commutator in the defining Geck representation.
attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] TauCeti.moduleNNRat

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

private theorem lie_lieBasis_h_rootGenerator_inr_neg (i q : Fin t.rank) :
    ⁅(t.lieBasis ht).h q, (t.lieBasis ht).rootGenerator (.inr i)⁆ =
      -((t.rootGeneratorWeight ht (.inl i) q : ℚ) • (t.lieBasis ht).rootGenerator (.inr i)) := by
  rw [t.lie_lieBasis_h_rootGenerator ht (.inr i) q, rootGeneratorWeight_inr,
    rootGeneratorWeight_inl, Int.cast_neg, neg_smul]

/-! ## Lattice-automorphism Gauss factorizations -/

/-- **Opposite-simple-root Gauss factorization on Geck lattice automorphisms (raising times
lowering).** Whenever `u = 1 + a b` is a unit of `A`, the product `xᵢ(a) x₋ᵢ(b)` at Bourbaki node
`i` factors through the `i`-th coordinate of `geckTorusPoints`. -/
theorem geckRootSubgroupParam_inl_mul_inr (i : Fin t.rank) (A : CommAlgCat.{v} ℤ)
    (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    t.geckRootSubgroupParam ht (.inl i) A (Multiplicative.ofAdd a) *
        t.geckRootSubgroupParam ht (.inr i) A (Multiplicative.ofAdd b) =
      t.geckRootSubgroupParam ht (.inr i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) *
        t.geckTorusPoints ht A (Pi.mulSingle i u) *
        t.geckRootSubgroupParam ht (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) := by
  have h :=
    UniversalEnvelopingAlgebra.kostantRootSubgroupParam_mul_kostantRootSubgroupParam_e_f
      (i := Sum.inl i) (j := Sum.inr i) (c := i) (α := t.rootGeneratorWeight ht (.inl i))
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
      (t.isNilpotent_geckRepresentation_rootGenerator ht (.inr i))
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
      (t.isCartanWeightVector_geckCoordinateBasisFin ht)
      (t.isSl2Triple_geckRepresentation ht i)
      (fun q => t.lie_lieBasis_h_rootGenerator ht (.inl i) q)
      (fun q => t.lie_lieBasis_h_rootGenerator_inr_neg ht i q)
      A a b u hu
  rwa [UniversalEnvelopingAlgebra.kostantCoordinateCocharacter_apply] at h

/-- **Opposite-simple-root Gauss factorization on Geck lattice automorphisms (lowering times
raising).** Whenever `u = 1 + a b` is a unit of `A`, the product `x₋ᵢ(b) xᵢ(a)` at Bourbaki node
`i` factors through the inverse of the `i`-th coordinate of `geckTorusPoints`. -/
theorem geckRootSubgroupParam_inr_mul_inl (i : Fin t.rank) (A : CommAlgCat.{v} ℤ)
    (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    t.geckRootSubgroupParam ht (.inr i) A (Multiplicative.ofAdd b) *
        t.geckRootSubgroupParam ht (.inl i) A (Multiplicative.ofAdd a) =
      t.geckRootSubgroupParam ht (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) *
        t.geckTorusPoints ht A (Pi.mulSingle i u⁻¹) *
        t.geckRootSubgroupParam ht (.inr i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) := by
  have hneg : (u : A) = 1 + (-a) * (-b) := by simpa only [neg_mul_neg] using hu
  have hinv := congrArg Inv.inv
    (t.geckRootSubgroupParam_inl_mul_inr ht i A (-a) (-b) u hneg)
  simpa only [mul_inv_rev, ← map_inv, ofAdd_neg, inv_inv, neg_mul, Pi.mulSingle_inv,
    mul_assoc] using hinv

/-! ## Point-group Gauss factorizations -/

/-- **Opposite-simple-root Gauss factorization in the Geck carrier point group (raising times
lowering).** Over every commutative ring `A` and whenever `u = 1 + a b` is a unit of `A`, the
product `xᵢ(a) x₋ᵢ(b)` in `t.geckPoints ht A` factors through the represented weight-torus point
`Pi.mulSingle i u`. -/
theorem geckRootSubgroupPoints_inl_mul_inr (i : Fin t.rank) (A : Type v) [CommRing A]
    (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd a) *
        t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd b) =
      t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) *
        t.geckWeightTorusPoints ht A (Pi.mulSingle i u) *
        t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) := by
  apply Subtype.ext
  have h :=
    UniversalEnvelopingAlgebra.kostantToralRootSubgroupPoints_mul_kostantToralRootSubgroupPoints_e_f
      (i := Sum.inl i) (j := Sum.inr i) (c := i) (α := t.rootGeneratorWeight ht (.inl i))
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
      (t.isCartanWeightVector_geckCoordinateBasisFin ht)
      (t.isSl2Triple_geckRepresentation ht i)
      (fun q => t.lie_lieBasis_h_rootGenerator ht (.inl i) q)
      (fun q => t.lie_lieBasis_h_rootGenerator_inr_neg ht i q)
      A a b u hu
  have hmatrix := congrArg Subtype.val h
  simpa only [Subgroup.coe_mul, coe_geckRootSubgroupPoints, coe_geckWeightTorusPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralWeightTorusPoints] using hmatrix

/-- **Opposite-simple-root Gauss factorization in the Geck carrier point group (lowering times
raising).** Over every commutative ring `A` and whenever `u = 1 + a b` is a unit of `A`, the
product `x₋ᵢ(b) xᵢ(a)` in `t.geckPoints ht A` factors through the represented weight-torus point
`Pi.mulSingle i u⁻¹`. -/
theorem geckRootSubgroupPoints_inr_mul_inl (i : Fin t.rank) (A : Type v) [CommRing A]
    (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd b) *
        t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd a) =
      t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) *
        t.geckWeightTorusPoints ht A (Pi.mulSingle i u⁻¹) *
        t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) := by
  have hneg : (u : A) = 1 + (-a) * (-b) := by simpa only [neg_mul_neg] using hu
  have hinv := congrArg Inv.inv
    (t.geckRootSubgroupPoints_inl_mul_inr ht i A (-a) (-b) u hneg)
  simpa only [mul_inv_rev, ← map_inv, ofAdd_neg, inv_inv, neg_mul, Pi.mulSingle_inv,
    mul_assoc] using hinv

/-! ## Opposite-root Gauss factorizations at every Weyl-word root -/

/-- Appending `[i]` to a Weyl word `l` negates the root attached at node `i`. -/
@[simp]
theorem root_geckWeylRootIndex_append_singleton_self (l : List (Fin t.rank)) (i : Fin t.rank) :
    (t.simplyConnectedRootDatum ht).root (t.geckWeylRootIndex ht (l ++ [i]) i) =
      -(t.simplyConnectedRootDatum ht).root (t.geckWeylRootIndex ht l i) := by
  rw [root_geckWeylRootIndex, geckWeylWordProd_append, mul_smul, ← root_geckWeylRootIndex,
    root_geckWeylRootIndex_singleton_self, smul_neg, ← root_geckWeylRootIndex]

/-- Appending `[i]` to a Weyl word `l` conjugates the lowering root subgroup at node `i` with
negated parameter. -/
theorem geckWeylRootSubgroupPoints_append_singleton_self (l : List (Fin t.rank))
    (i : Fin t.rank) (A : Type v) [CommRing A] (b : A) :
    t.geckWeylRootSubgroupPoints ht (l ++ [i]) i A (Multiplicative.ofAdd b) =
      t.geckWeylWordPoint ht l A *
        t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd (-b)) *
        (t.geckWeylWordPoint ht l A)⁻¹ := by
  calc
    t.geckWeylRootSubgroupPoints ht (l ++ [i]) i A (Multiplicative.ofAdd b)
      = t.geckWeylWordPoint ht l A *
          t.geckWeylRootSubgroupPoints ht [i] i A (Multiplicative.ofAdd b) *
          (t.geckWeylWordPoint ht l A)⁻¹ := by
        simp only [geckWeylRootSubgroupPoints_apply, geckWeylWordPoint_append]
        group
    _ = t.geckWeylWordPoint ht l A *
          t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd (-b)) *
          (t.geckWeylWordPoint ht l A)⁻¹ := by
        rw [geckWeylRootSubgroupPoints_singleton_self]

/-- **Weyl action on a simple-coroot torus point.** An abstract Weyl-group element `w` maps
`Pi.mulSingle i u` to the cocharacter torus point of the translated coroot
`weylGroupToPerm w (simpleIndex i)`. -/
theorem geckWeylTorusAction_mulSingle (w : (t.simplyConnectedRootDatum ht).weylGroup)
    (i : Fin t.rank) (A : Type v) [CommRing A] (u : Aˣ) :
    t.geckWeylTorusAction ht A w (Pi.mulSingle i u) =
      fun k ↦ u ^ ((t.simplyConnectedRootDatum ht).coroot
        ((t.simplyConnectedRootDatum ht).weylGroupToPerm w (t.simpleIndex ht i)) k) := by
  funext k
  let eₖ : Fin t.rank → ℤ := Pi.single k 1
  rw [← TauCeti.weightChar_single A k (t.geckWeylTorusAction ht A w (Pi.mulSingle i u)),
    TauCeti.weightChar_apply, t.torusCharacter_geckWeylTorusAction ht,
    TauCeti.torusCharacter_mulSingle]
  congr 1
  refine (t.coroot'_simpleIndex_apply ht i (w⁻¹ • eₖ)).symm.trans ?_
  have hw := w.1.coroot'_weightEquiv (t.simpleIndex ht i) (w⁻¹ • eₖ)
  have hsmul : w.1.weightEquiv (w⁻¹ • eₖ) = eₖ := smul_inv_smul w eₖ
  rw [← hw, hsmul]
  -- Unfold `coroot'` as `LinearMap.flip` of `toLinearMap` so the dot-product formula applies.
  change (t.simplyConnectedRootDatum ht).toLinearMap (Pi.single k 1)
    ((t.simplyConnectedRootDatum ht).coroot
      ((t.simplyConnectedRootDatum ht).weylGroupToPerm w (t.simpleIndex ht i))) = _
  rw [t.toLinearMap_simplyConnectedRootDatum ht, single_dotProduct, one_mul]

/-- `geckWeylRootIndex l i` is the image of `simpleIndex i` under the permutation action of the
Weyl-group element spelled by `l`. -/
theorem geckWeylRootIndex_eq_weylGroupToPerm (l : List (Fin t.rank)) (i : Fin t.rank) :
    t.geckWeylRootIndex ht l i =
      (t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht l)
        (t.simpleIndex ht i) := by
  induction l with
  | nil => simp
  | cons j l ih =>
      rw [geckWeylRootIndex_cons, ih, geckWeylWordProd_cons,
        RootPairing.weylGroupToPerm_ofIdx_mul_apply]

/-- **Weyl-word transport of a simple-coroot torus point.** Acting on `Pi.mulSingle i u` by a Weyl
word `l` yields the cocharacter torus point of the coroot at `geckWeylRootIndex l i`; in
particular, it depends on `(l, i)` only through the attached root index. -/
theorem geckWeylWordTorusAction_mulSingle (l : List (Fin t.rank)) (i : Fin t.rank)
    (A : Type v) [CommRing A] (u : Aˣ) :
    t.geckWeylWordTorusAction ht l A (Pi.mulSingle i u) =
      fun k ↦ u ^ ((t.simplyConnectedRootDatum ht).coroot (t.geckWeylRootIndex ht l i) k) := by
  rw [← t.geckWeylTorusAction_apply_eq_word ht rfl, geckWeylRootIndex_eq_weylGroupToPerm]
  exact t.geckWeylTorusAction_mulSingle ht (t.geckWeylWordProd ht l) i A u

/-- **Opposite-root Gauss factorization at any Weyl-word root pair (`(l, i)` times
`(l ++ [i], i)`).** Because `x_{[i],i}(b) = x₋ᵢ(-b)`, whenever `u = 1 - a b` is a unit of `A`, the
product `x_{l,i}(a) x_{l ++ [i],i}(b)` at the opposite roots `±α` (`α` at `geckWeylRootIndex l i`)
factors through the coroot torus point `k ↦ u ^ (coroot (geckWeylRootIndex l i) k)`. -/
theorem geckWeylRootSubgroupPoints_mul_append_singleton_self (l : List (Fin t.rank))
    (i : Fin t.rank) (A : Type v) [CommRing A] (a b : A) (u : Aˣ) (hu : (u : A) = 1 - a * b) :
    t.geckWeylRootSubgroupPoints ht l i A (Multiplicative.ofAdd a) *
        t.geckWeylRootSubgroupPoints ht (l ++ [i]) i A (Multiplicative.ofAdd b) =
      t.geckWeylRootSubgroupPoints ht (l ++ [i]) i A (Multiplicative.ofAdd (b * ↑u⁻¹)) *
        t.geckWeightTorusPoints ht A
          (fun k ↦ u ^ ((t.simplyConnectedRootDatum ht).coroot (t.geckWeylRootIndex ht l i) k)) *
        t.geckWeylRootSubgroupPoints ht l i A (Multiplicative.ofAdd (a * ↑u⁻¹)) := by
  have hu' : (u : A) = 1 + a * (-b) := by rw [mul_neg, ← sub_eq_add_neg]; exact hu
  have hsimple := t.geckRootSubgroupPoints_inl_mul_inr ht i A a (-b) u hu'
  rw [neg_mul] at hsimple
  calc
    t.geckWeylRootSubgroupPoints ht l i A (Multiplicative.ofAdd a) *
        t.geckWeylRootSubgroupPoints ht (l ++ [i]) i A (Multiplicative.ofAdd b)
      = t.geckWeylWordPoint ht l A *
          (t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd a) *
            t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd (-b))) *
          (t.geckWeylWordPoint ht l A)⁻¹ := by
        rw [geckWeylRootSubgroupPoints_append_singleton_self, geckWeylRootSubgroupPoints_apply]
        group
    _ = t.geckWeylWordPoint ht l A *
          (t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd (-(b * ↑u⁻¹))) *
            t.geckWeightTorusPoints ht A (Pi.mulSingle i u) *
            t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹))) *
          (t.geckWeylWordPoint ht l A)⁻¹ := by
        rw [hsimple]
    _ = (t.geckWeylWordPoint ht l A *
            t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd (-(b * ↑u⁻¹))) *
            (t.geckWeylWordPoint ht l A)⁻¹) *
          (t.geckWeylWordPoint ht l A *
            t.geckWeightTorusPoints ht A (Pi.mulSingle i u) *
            (t.geckWeylWordPoint ht l A)⁻¹) *
          (t.geckWeylWordPoint ht l A *
            t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) *
            (t.geckWeylWordPoint ht l A)⁻¹) := by
        group
    _ = t.geckWeylRootSubgroupPoints ht (l ++ [i]) i A (Multiplicative.ofAdd (b * ↑u⁻¹)) *
          t.geckWeightTorusPoints ht A
            (fun k ↦ u ^ ((t.simplyConnectedRootDatum ht).coroot (t.geckWeylRootIndex ht l i) k)) *
          t.geckWeylRootSubgroupPoints ht l i A (Multiplicative.ofAdd (a * ↑u⁻¹)) := by
        rw [← geckWeylRootSubgroupPoints_append_singleton_self,
          geckWeylWordPoint_conj_geckWeightTorusPoints, geckWeylWordTorusAction_mulSingle,
          ← geckWeylRootSubgroupPoints_apply]

/-- **Opposite-root Gauss factorization at any Weyl-word root pair (`(l ++ [i], i)` times
`(l, i)`).** Whenever `u = 1 - a b` is a unit of `A`, the product `x_{l ++ [i],i}(b) x_{l,i}(a)`
factors through the inverse coroot torus point
`k ↦ (u⁻¹) ^ (coroot (geckWeylRootIndex l i) k)`. -/
theorem geckWeylRootSubgroupPoints_append_singleton_self_mul (l : List (Fin t.rank))
    (i : Fin t.rank) (A : Type v) [CommRing A] (a b : A) (u : Aˣ) (hu : (u : A) = 1 - a * b) :
    t.geckWeylRootSubgroupPoints ht (l ++ [i]) i A (Multiplicative.ofAdd b) *
        t.geckWeylRootSubgroupPoints ht l i A (Multiplicative.ofAdd a) =
      t.geckWeylRootSubgroupPoints ht l i A (Multiplicative.ofAdd (a * ↑u⁻¹)) *
        t.geckWeightTorusPoints ht A
          (fun k ↦ u⁻¹ ^ ((t.simplyConnectedRootDatum ht).coroot (t.geckWeylRootIndex ht l i) k)) *
        t.geckWeylRootSubgroupPoints ht (l ++ [i]) i A (Multiplicative.ofAdd (b * ↑u⁻¹)) := by
  have hneg : (u : A) = 1 - (-a) * (-b) := by simpa only [neg_mul_neg] using hu
  have hinv := congrArg Inv.inv
    (t.geckWeylRootSubgroupPoints_mul_append_singleton_self ht l i A (-a) (-b) u hneg)
  simpa only [mul_inv_rev, ← map_inv, ofAdd_neg, inv_inv, neg_mul, Pi.inv_def, ← inv_zpow,
    mul_assoc] using hinv

end

end TauCeti.DynkinType
