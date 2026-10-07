/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Transfer
public import TauCeti.Topology.Algebra.Group.TransversalWord

/-!
# Continuity of transfer

For an open finite-index subgroup `U ≤ G`, Mathlib's `MonoidHom.transfer` sends a continuous
homomorphism `U →* A` to a continuous homomorphism `G →* A`, where `A` is commutative.
The formula `transfer_eq_prod_lWord` computes this transfer using the same transversal words
as continuous cohomological corestriction. It is valid for every transversal, without topology;
continuity then follows from `continuous_lWord`.

Only separate continuity of multiplication on `G` and continuity of multiplication on `A`
are needed. Neither compactness of `G` nor discreteness of `A` is required.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
* Neukirch--Schmidt--Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.9).

The algebraic transfer is Mathlib's `MonoidHom.transfer`; the transversal computation uses
`MonoidHom.transfer_eq_prod_of_bijective`.
-/

public section

namespace TauCeti

variable {G A : Type*} [Group G] [CommGroup A] {U : Subgroup G} [U.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Transfer from an open finite-index subgroup preserves continuity. The commutative target
need not be discrete, and the ambient group need not be compact. -/
theorem continuous_transfer [TopologicalSpace G] [SeparatelyContinuousMul G]
    [TopologicalSpace A] [ContinuousMul A] (hU : IsOpen (U : Set G))
    {φ : U →* A} (hφ : Continuous φ) : Continuous (MonoidHom.transfer φ) := by
  rw [funext (transfer_eq_prod_lWord Quotient.out Quotient.out_eq φ)]
  exact continuous_finsetProd _ fun q _ =>
    hφ.comp ((continuous_lWord U Quotient.out hU q).subtype_mk _)

end TauCeti
