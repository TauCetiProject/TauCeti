/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.RootSubgroup
import TauCeti.Algebra.Group.OneParameterGauss
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Gauss

/-!
# Opposite-root Gauss factorization at every Weyl-word root of the Geck carrier

For any valid Dynkin type `t`, Weyl word `l : List (Fin t.rank)`, and Bourbaki node `i`, the word
presentations `(l, i)` and `(l ++ [i], i)` attach opposite roots `α` and `-α` of
`TauCeti.DynkinType.simplyConnectedRootDatum` at `r = geckWeylRootIndex l i`
(`TauCeti.DynkinType.root_geckWeylRootIndex_append_singleton_self`). Conjugating the simple-root
Gauss factorizations of
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Gauss` by the Weyl-word
representative `geckWeylWordPoint` transports them to `(l, i)` and `(l ++ [i], i)`.

Because `x_{[i],i}(b) = x₋ᵢ(-b)` (`TauCeti.DynkinType.geckWeylRootSubgroupPoints_singleton_self`),
whenever `u = 1 - a b` is a unit of a commutative ring `A`, the opposite-root products in
`t.geckPoints ht A` factor in both multiplication orders through the coroot cocharacter
`k ↦ u ^ (coroot r k)` of `r` (depending only on the root index `r`, not on the word `l` or node
`i`):

```text
x_{l,i}(a) x_{l ++ [i],i}(b) = x_{l ++ [i],i}(b u⁻¹) t(k ↦ u ^ coroot r k) x_{l,i}(a u⁻¹),
x_{l ++ [i],i}(b) x_{l,i}(a) = x_{l,i}(a u⁻¹) t(k ↦ u⁻¹ ^ coroot r k) x_{l ++ [i],i}(b u⁻¹).
```

## Main results

* `TauCeti.DynkinType.geckWeylRootSubgroupPoints_mul_append_singleton_self`: opposite-root Gauss
  factorization for `x_{l,i}(a) x_{l ++ [i],i}(b)`.
* `TauCeti.DynkinType.geckWeylRootSubgroupPoints_append_singleton_self_mul`: opposite-root Gauss
  factorization for `x_{l ++ [i],i}(b) x_{l,i}(a)`.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3, Lemmas 19--20.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4, 7.2, and 12.1.
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
  simpa only [Pi.inv_def, inv_zpow] using
    map_ofAdd_mul_map_ofAdd_eq_of_map_ofAdd_neg_mul_map_ofAdd_neg_eq
      (t.geckWeylRootSubgroupPoints_mul_append_singleton_self ht l i A (-a) (-b) u
        (by rwa [neg_mul_neg]))

end

end TauCeti.DynkinType
