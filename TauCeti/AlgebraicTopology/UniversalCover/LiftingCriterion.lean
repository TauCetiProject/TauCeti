/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.Lifting

/-!
# The lifting criterion for covering maps

This file records the covering-space lifting criterion's subgroup condition in the form needed
by the universal covers roadmap. Mathlib already proves the theorem; Tau Ceti only packages the
precise subgroup condition.

For a covering map `p : E → X`, a continuous map `f : A → X`, a base point `a₀ : A`, and a
chosen lift `e₀ : E` of `f a₀`, the condition is the usual

`f_*(π₁(A, a₀)) ≤ p_*(π₁(E, e₀))`.

In Lean this is the subgroup inclusion

`(FundamentalGroup.map f a₀).range ≤
  (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range`.

Mathlib's theorem `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` then gives a
unique continuous lift `F : C(A, E)` with `F a₀ = e₀` and `p ∘ F = f`, under the standard
hypotheses that `A` is path connected and locally path connected.

## Main declarations

* `TauCeti.IsCoveringMap.LiftCondition`: the fundamental-group subgroup inclusion.
* `TauCeti.IsCoveringMap.liftCondition_iff_range_le`: `LiftCondition` unfolds to Mathlib's
  range-inclusion hypothesis.

## References

This is the Tau Ceti universal-covers roadmap, Stage 2, item 6 ("General lifting criterion,
already in Mathlib"). The proof reuses Junyan Xu's
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` from
`Mathlib/Topology/Homotopy/Lifting.lean`.
-/

public section

namespace TauCeti

namespace IsCoveringMap

variable {A E X : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X}

/-- The subgroup condition in the lifting criterion for a covering map.

For `hp : IsCoveringMap p`, a map `f : C(A, X)`, and a chosen lift `e₀` of `f a₀`, this says
that the image of `π₁(A, a₀)` under `f` is contained in the image of `π₁(E, e₀)` under `p`.
Under path-connectedness and local path-connectedness of `A`, this is exactly the hypothesis
needed to lift `f` uniquely through `p` with value `e₀` at `a₀`. -/
@[expose] def LiftCondition (hp : IsCoveringMap p) (f : C(A, X)) (a₀ : A) (e₀ : E)
    (he : p e₀ = f a₀) : Prop :=
  (FundamentalGroup.map f a₀).range ≤
    (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range

/-- The lifting condition is exactly the fundamental-group image inclusion appearing in
Mathlib's covering-space lifting criterion. -/
lemma liftCondition_iff_range_le (hp : IsCoveringMap p) (f : C(A, X)) (a₀ : A) (e₀ : E)
    (he : p e₀ = f a₀) :
    LiftCondition hp f a₀ e₀ he ↔
      (FundamentalGroup.map f a₀).range ≤
        (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range :=
  Iff.rfl

end IsCoveringMap

end TauCeti
