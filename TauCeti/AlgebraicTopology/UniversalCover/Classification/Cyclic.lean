/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed
public import TauCeti.Topology.Homotopy.Monodromy.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Covers of a space with cyclic fundamental group are determined by their degree

A pointed connected cover of `(X, x)` is determined up to isomorphism by the subgroup of
`π₁(X, x)` it recovers (`IsCoveringMap.exists_homeomorph_comp_eq_of_range_eq`), and the index of
that subgroup is the number of sheets (`IsCoveringMap.card_fiber_eq_index`). In a cyclic group a
subgroup is determined by its index (`IsCyclic.subgroup_eq_iff_index_eq`). So when `π₁(X, x)` is
cyclic, two connected covers of `X` with the same number of sheets over `x` are isomorphic over
`X`, by an isomorphism carrying any chosen point of the first fibre to any chosen point of the
second.

The number of sheets is read with `Nat.card`, so an infinite fibre counts as `0`; the statement
holds in that case as well, since in an infinite cyclic group the trivial subgroup is the only one
of index `0`.

The main application is to the punctured disc, whose fundamental group is infinite cyclic: its
connected covers of finite degree `e ≠ 0` are all isomorphic to `z ↦ z ^ e`.

## Main declarations

* `IsCoveringMap.exists_homeomorph_comp_eq_of_card_fiber_eq`: over a base with cyclic `π₁(X, x)`,
  two pointed connected covers with fibres over `x` of the same cardinality are isomorphic as
  pointed covers.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 1.32 (the
  number of sheets is the index of the recovered subgroup) and Proposition 1.37 (pointed covers
  are classified by the recovered subgroup).
-/

public section

namespace TauCeti

variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
  {p : E → X} {q : F → X} {x : X}

/-- **Over a base with cyclic fundamental group, a pointed connected cover is determined by its
number of sheets.** If `π₁(X, x)` is cyclic and the fibres of `p` and `q` over `x` have the same
cardinality, then there is a homeomorphism `E ≃ₜ F` over `X` carrying the chosen point `e₀` of
the first fibre to the chosen point `f₀` of the second. -/
theorem _root_.IsCoveringMap.exists_homeomorph_comp_eq_of_card_fiber_eq
    [IsCyclic (FundamentalGroup X x)]
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace F] [LocallyPathConnectedSpace F]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (e₀ : p ⁻¹' {x}) (f₀ : q ⁻¹' {x})
    (hcard : Nat.card (p ⁻¹' {x}) = Nat.card (q ⁻¹' {x})) :
    ∃ h : E ≃ₜ F, h e₀ = f₀ ∧ q ∘ h = p :=
  hp.exists_homeomorph_comp_eq_of_range_eq hq e₀.2 f₀.2 <| by
    rw [IsCyclic.subgroup_eq_iff_index_eq, ← hp.card_fiber_eq_index e₀,
      ← hq.card_fiber_eq_index f₀, hcard]

end TauCeti
