/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.Lifting

/-!
# The lifting criterion for covering maps

This file records the covering-space lifting criterion in the form needed by the universal
covers roadmap. Mathlib already proves the theorem; Tau Ceti only packages the precise
subgroup condition and gives local names for the general criterion and the simply-connected
special case.

For a covering map `p : E → X`, a continuous map `f : A → X`, a base point `a₀ : A`, and a
chosen lift `e₀ : E` of `f a₀`, the condition is the usual

`f_*(π₁(A, a₀)) ≤ p_*(π₁(E, e₀))`.

In Lean this is the subgroup inclusion

`(FundamentalGroup.map f a₀).range ≤
  (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range`.

The theorem then gives a unique continuous lift `F : C(A, E)` with `F a₀ = e₀` and
`p ∘ F = f`, under the standard hypotheses that `A` is path connected and locally path
connected. The simply-connected version drops the subgroup condition.

## Main declarations

* `TauCeti.IsCoveringMap.LiftCondition`: the fundamental-group subgroup inclusion.
* `TauCeti.IsCoveringMap.existsUnique_lift_of_liftCondition`: the general lifting
  criterion.

## References

This is the Tau Ceti universal-covers roadmap, Stage 2, item 6 ("General lifting criterion,
already in Mathlib"). The proof reuses Junyan Xu's
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` and
`IsCoveringMap.existsUnique_continuousMap_lifts` from
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

/-- The covering-space lifting criterion, stated using the named lifting condition.

If `A` is path connected and locally path connected, a continuous map `f : A → X` has a unique
lift through the covering map `p : E → X` taking `a₀` to the chosen point `e₀`, provided
`f_*(π₁(A, a₀)) ≤ p_*(π₁(E, e₀))`. -/
theorem existsUnique_lift_of_liftCondition (hp : IsCoveringMap p)
    [PathConnectedSpace A] [LocallyPathConnectedSpace A] {f : C(A, X)} {a₀ : A} {e₀ : E}
    (he : p e₀ = f a₀) (h : LiftCondition hp f a₀ e₀ he) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f :=
  hp.existsUnique_continuousMap_lifts_of_range_le he h

/-- Existence part of the covering-space lifting criterion. -/
theorem exists_lift_of_liftCondition (hp : IsCoveringMap p)
    [PathConnectedSpace A] [LocallyPathConnectedSpace A] {f : C(A, X)} {a₀ : A} {e₀ : E}
    (he : p e₀ = f a₀) (h : LiftCondition hp f a₀ e₀ he) :
    ∃ F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f :=
  (existsUnique_lift_of_liftCondition hp he h).exists

/-- Uniqueness part of the covering-space lifting criterion. -/
theorem lift_unique_of_liftCondition (hp : IsCoveringMap p)
    [PathConnectedSpace A] [LocallyPathConnectedSpace A] {f : C(A, X)} {a₀ : A} {e₀ : E}
    (he : p e₀ = f a₀) (h : LiftCondition hp f a₀ e₀ he) {F G : C(A, E)}
    (hF : F a₀ = e₀ ∧ p ∘ F = f) (hG : G a₀ = e₀ ∧ p ∘ G = f) :
    F = G :=
  (existsUnique_lift_of_liftCondition hp he h).unique hF hG

/-- Existence part of the simply-connected lifting criterion. -/
theorem exists_lift_of_simplyConnected (hp : IsCoveringMap p)
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A] (f : C(A, X)) (a₀ : A) (e₀ : E)
    (he : p e₀ = f a₀) :
    ∃ F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f :=
  (hp.existsUnique_continuousMap_lifts f a₀ e₀ he).exists

/-- Uniqueness part of the simply-connected lifting criterion. -/
theorem lift_unique_of_simplyConnected (hp : IsCoveringMap p)
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A] {f : C(A, X)} {a₀ : A} {e₀ : E}
    (he : p e₀ = f a₀) {F G : C(A, E)}
    (hF : F a₀ = e₀ ∧ p ∘ F = f) (hG : G a₀ = e₀ ∧ p ∘ G = f) :
    F = G :=
  (hp.existsUnique_continuousMap_lifts f a₀ e₀ he).unique hF hG

end IsCoveringMap

end TauCeti
