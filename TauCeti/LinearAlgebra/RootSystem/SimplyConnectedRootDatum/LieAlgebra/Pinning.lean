/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme

/-!
# The uniform exponential over the Chevalley pinning

For a valid Dynkin type, the Geck lattice construction provides, for each simple root,
a represented root subgroup: the uniform exponential `u ↦ exp(u • e_i)` of the `i`-th
simple raising generator `e_i`, as a matrix over any commutative ring. The definition
`TauCeti.DynkinType.pinnedExp` is a thin wrapper over the existing
`TauCeti.DynkinType.geckRootSubgroupMatrix` that converts the scalar `u : A` to a
`𝔾ₐ`-point through `Multiplicative.ofAdd` and `TauCeti.AdditiveGroup.gaPointsMulEquiv`.
No exponential matrix is re-implemented here: the definitional identification with the
root-subgroup construction is recorded in
`TauCeti.DynkinType.pinnedExp_eq_coe_geckRootSubgroupPoints`, and the laws of the
uniform exponential are the existing laws of the Geck root-subgroup construction,
reached through that identification.

This is the first step of the uniform pinned Chevalley–Demazure construction; further
properties of the pinning will be transferred from the root-subgroup API in follow-ups.

## Main results

* `TauCeti.DynkinType.pinnedExp`: the uniform exponential `u ↦ exp(u • e_i)` over any
  commutative ring.
* `TauCeti.DynkinType.pinnedExp_eq_coe_geckRootSubgroupPoints`: its identification with
  the coercion of the parametrized Geck root-subgroup point
  `TauCeti.DynkinType.geckRootSubgroupPoints`.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.

Roadmap: ReductiveGroups
-/

public section

namespace TauCeti.DynkinType

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- The uniform exponential `u ↦ exp(u • e_i)` of the `i`-th simple raising generator, as a
thin wrapper over `TauCeti.DynkinType.geckRootSubgroupMatrix`: the scalar `u : A` in any
commutative ring is converted to a `𝔾ₐ`-point through `Multiplicative.ofAdd` and
`TauCeti.AdditiveGroup.gaPointsMulEquiv`. -/
noncomputable def pinnedExp (A : Type*) [CommRing A]
    (i : Fin t.rank) (u : A) :
    Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A :=
  t.geckRootSubgroupMatrix ht (.inl i)
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (Multiplicative.ofAdd u))

/-- **Identification of the uniform exponential with the root-subgroup construction.**
`pinnedExp` is the coercion to the general linear group of the parametrized Geck
root-subgroup point `TauCeti.DynkinType.geckRootSubgroupPoints` at the corresponding
`𝔾ₐ`-parameter. -/
theorem pinnedExp_eq_coe_geckRootSubgroupPoints (A : Type*) [CommRing A]
    (i : Fin t.rank) (u : A) :
    t.pinnedExp ht A i u =
      (t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd u) :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) := by
  rw [t.coe_geckRootSubgroupPoints ht]
  rfl

end

end TauCeti.DynkinType
