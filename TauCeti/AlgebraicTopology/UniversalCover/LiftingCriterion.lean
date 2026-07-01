/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Subgroup-form lifting criterion for covering maps

This file records the lifting criterion in the subgroup form used by the universal-covers
roadmap. Mathlib already proves the fundamental result
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`: a map `f : A → X` lifts through
a covering map `p : E → X`, with prescribed basepoint lift `e₀`, when
`f_* π₁(A, a₀)` is contained in `p_* π₁(E, e₀)`.

The classification of covers often inserts an intermediate subgroup
`H ≤ π₁(X, f a₀)`: one first proves `f_* π₁(A, a₀) ≤ H`, and separately identifies `H` as a
subgroup of the image of `p_*`. The lemmas here package exactly that two-step shape, together
with the subsingleton-fundamental-group special case.

## Main declarations

* `TauCeti.IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le_subgroup`: lift when
  `f_* π₁(A, a₀) ≤ H ≤ p_* π₁(E, e₀)`.
* `existsUnique_continuousMap_lifts_of_subsingleton_fundamentalGroup`: lift when the source
  fundamental group is subsingleton.

## References

The proof is a thin wrapper around Mathlib's
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` (Junyan Xu,
`Mathlib/Topology/Homotopy/Lifting.lean`), and uses the trivial-source fundamental-group
range lemmas from `TauCeti.AlgebraicTopology.FundamentalGroup`.
-/

public section

namespace TauCeti

variable {A E X : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X}

namespace IsCoveringMap

/-- The lifting criterion for a covering map, with the subgroup inclusion factored through an
intermediate subgroup `H ≤ π₁(X, f a₀)`.

This is the form used when a cover is known to have recovered subgroup `H`: to lift `f`, it
suffices to show that `f_* π₁(A, a₀)` lies in `H`, and that `H` is contained in the image of
`p_* π₁(E, e₀)`. -/
theorem existsUnique_continuousMap_lifts_of_range_le_subgroup
    (hp : _root_.IsCoveringMap p) [PathConnectedSpace A] [LocallyPathConnectedSpace A]
    {f : C(A, X)} {a₀ : A} {e₀ : E} (he : p e₀ = f a₀)
    (H : Subgroup (_root_.FundamentalGroup X (f a₀)))
    (hfH : (_root_.FundamentalGroup.map f a₀).range ≤ H)
    (hHp : H ≤ (_root_.FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f :=
  hp.existsUnique_continuousMap_lifts_of_range_le he (hfH.trans hHp)

/-- The lifting criterion when the source fundamental group at `a₀` is subsingleton. In this
case the induced subgroup `f_* π₁(A, a₀)` is trivial. -/
theorem existsUnique_continuousMap_lifts_of_subsingleton_fundamentalGroup
    (hp : _root_.IsCoveringMap p) [PathConnectedSpace A] [LocallyPathConnectedSpace A]
    {f : C(A, X)} {a₀ : A} {e₀ : E}
    [Subsingleton (_root_.FundamentalGroup A a₀)] (he : p e₀ = f a₀) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f :=
  hp.existsUnique_continuousMap_lifts_of_range_le he <| by
    rw [FundamentalGroup.map_range_eq_bot_of_subsingleton f]
    exact bot_le

end IsCoveringMap

end TauCeti
