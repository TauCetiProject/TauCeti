/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Faithful
import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct

/-!
# Pointwise injectivity of Chevalley root subgroups

For every Chevalley datum `D` of every valid Dynkin type and over every commutative ring `A` —
including nonreduced rings with nilpotents and rings of characteristics two and three — every root
subgroup homomorphism `D.rootSubgroupPoints γ A` is injective.

This supplies pointwise parameter injectivity for Borel intersections, rank-one Bruhat cells, and
toral centralizers without assuming a full weight lattice. It is a statement on ring-valued points
and does not assert that `D.rootSubgroup γ` is a closed immersion of schemes.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.rootSubgroupPoints_injective`: `D.rootSubgroupPoints γ A` is
  injective over every commutative ring `A`.
* `TauCeti.DynkinType.ChevalleyDatum.rootSubgroupPoints_inj` and
  `TauCeti.DynkinType.ChevalleyDatum.rootSubgroupPoints_eq_one_iff`: `simp` characterizations of
  equality and triviality of root-subgroup points over any commutative ring.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 17–20.
* M. Demazure and A. Grothendieck, *SGA 3*, Exp. XXII, §4.1.
-/

public section

open Multiplicative

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Over every commutative ring, every root subgroup homomorphism of a Chevalley datum is
injective. No reducedness, characteristic, or full-weight hypothesis is required. -/
theorem rootSubgroupPoints_injective (γ : Fin t.numRoots) (A : Type v) [CommRing A] :
    Function.Injective (D.rootSubgroupPoints γ A) := by
  refine D.rootSubgroupPoints_injective_of_simple A (fun i a b hab => ?_) γ
  have h := (D.list_prod_map_rootSubgroupPoints_inj_of_posRoots A
    (l := [t.simpleIndex ht i]) (List.nodup_singleton _)
    (fun δ hδ => List.mem_singleton.mp hδ ▸ simpleIndex_mem_posRoots i)
    (u := fun _ => toAdd a) (v := fun _ => toAdd b)).mp
      (by simpa only [List.map_singleton, List.prod_singleton, ofAdd_toAdd] using hab)
  exact toAdd.injective (h (t.simpleIndex ht i) (List.mem_singleton_self _))

/-- Two parameters in the same root subgroup produce equal datum points if and only if they are
equal, over any commutative ring. -/
@[simp]
theorem rootSubgroupPoints_inj {γ : Fin t.numRoots} {A : Type v} [CommRing A]
    {u v : Multiplicative A} :
    D.rootSubgroupPoints γ A u = D.rootSubgroupPoints γ A v ↔ u = v :=
  (D.rootSubgroupPoints_injective γ A).eq_iff

/-- A root-subgroup point is the identity if and only if its multiplicative parameter is `1`, over
any commutative ring. -/
@[simp]
theorem rootSubgroupPoints_eq_one_iff {γ : Fin t.numRoots} {A : Type v} [CommRing A]
    {u : Multiplicative A} :
    D.rootSubgroupPoints γ A u = 1 ↔ u = 1 :=
  map_eq_one_iff _ (D.rootSubgroupPoints_injective γ A)

end TauCeti.DynkinType.ChevalleyDatum
