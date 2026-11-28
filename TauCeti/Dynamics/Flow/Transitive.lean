/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.Basic
public import TauCeti.Dynamics.Transitive

/-!
# Topologically transitive flows

A flow `ϕ` of `τ` on `X` is topologically transitive when its action `ϕ.toAddAction` is, in
Mathlib's `AddAction.IsTopologicallyTransitive τ X`: every nonempty open set `U` meets every
nonempty open set `V` after some time `t`, `(ϕ t '' U ∩ V).Nonempty`.

* A flow of an additive group with a dense orbit is transitive, in particular one with a dense
  forward orbit (`Flow.isTopologicallyTransitive_of_dense_forwardOrbit`). On a nonempty
  second-countable Baire space, for instance a nonempty compact metric space, a transitive flow of
  any additive monoid has a dense orbit (`Flow.IsTopologicallyTransitive.exists_dense_orbit`), so
  for groups transitivity is equivalent to the existence of a dense orbit
  (`Flow.isTopologicallyTransitive_iff_exists_dense_orbit`).
* If some time-`t` map is topologically transitive, as the `ℕ`-action of its iterates, so is the
  flow (`Flow.isTopologicallyTransitive_of_iterateMulAct`).

A dense orbit cannot be replaced by a dense forward orbit: the translation flow `x ↦ x + t` of
the compact metrizable space `EReal` without isolated points is transitive, but every forward
orbit lies in `[x, ⊤]`. The converse of the time-`t` statement also fails: the unit-speed flow of
the circle is transitive while its time-`1` map is the identity. Both are in
`TauCeti.Examples.Dynamics.Flow.Transitive`.

## Main definitions

* `Flow.IsTopologicallyTransitive ϕ`: the action `ϕ.toAddAction` is topologically transitive.
-/

public section

open Set Filter Topology

namespace Flow

variable {τ X : Type*} [TopologicalSpace τ] [TopologicalSpace X]

section AddMonoid

variable [AddMonoid τ] (ϕ : Flow τ X)

/-- A flow is *topologically transitive* when its action `ϕ.toAddAction` is: for nonempty open
sets `U` and `V` there is a time `t` with `ϕ t '' U ∩ V` nonempty. -/
def IsTopologicallyTransitive : Prop :=
  @AddAction.IsTopologicallyTransitive τ X _ _ ϕ.toAddAction

variable {ϕ}

theorem isTopologicallyTransitive_def :
    ϕ.IsTopologicallyTransitive ↔ @AddAction.IsTopologicallyTransitive τ X _ _ ϕ.toAddAction :=
  Iff.rfl

/-- A flow is topologically transitive exactly when for nonempty open sets `U` and `V` some
time-`t` image `ϕ t '' U` meets `V`. -/
theorem isTopologicallyTransitive_iff :
    ϕ.IsTopologicallyTransitive ↔ ∀ ⦃U V : Set X⦄, IsOpen U → U.Nonempty → IsOpen V →
      V.Nonempty → ∃ t : τ, (ϕ t '' U ∩ V).Nonempty := by
  let := ϕ.toAddAction
  rw [isTopologicallyTransitive_def, AddAction.isTopologicallyTransitive_iff]
  -- `t +ᵥ U` is `ϕ t '' U` by definition of `Flow.toAddAction`.
  rfl

/-- **Time-`t` maps.** If the time-`t` map of a flow is topologically transitive, as the
`ℕ`-action of its iterates, then so is the flow. -/
theorem isTopologicallyTransitive_of_iterateMulAct (t : τ)
    [h : MulAction.IsTopologicallyTransitive (IterateMulAct (ϕ t)) X] :
    ϕ.IsTopologicallyTransitive := by
  refine isTopologicallyTransitive_iff.2 fun U V hU hU₀ hV hV₀ ↦ ?_
  obtain ⟨⟨n⟩, hn⟩ := h.exists_smul_inter hU hU₀ hV hV₀
  refine ⟨n • t, ?_⟩
  rw [ϕ.map_nsmul]
  simpa only [← image_smul, IterateMulAct.mk_smul] using hn

/-- On a nonempty second-countable Baire space, a topologically transitive flow has a dense
orbit. -/
theorem IsTopologicallyTransitive.exists_dense_orbit [SecondCountableTopology X] [BaireSpace X]
    [Nonempty X] (h : ϕ.IsTopologicallyTransitive) : ∃ x, Dense (ϕ.orbit x) := by
  let := ϕ.toAddAction
  have := ϕ.continuousVAdd
  have : AddAction.IsTopologicallyTransitive τ X := h
  exact AddAction.exists_dense_orbit τ

end AddMonoid

section AddGroup

variable [AddGroup τ] {ϕ : Flow τ X}

/-- A flow with a dense orbit is topologically transitive. -/
theorem isTopologicallyTransitive_of_dense_orbit {x : X} (hx : Dense (ϕ.orbit x)) :
    ϕ.IsTopologicallyTransitive :=
  let := ϕ.toAddAction
  AddAction.isTopologicallyTransitive_of_dense_orbit hx

/-- A flow with a dense forward orbit is topologically transitive. -/
theorem isTopologicallyTransitive_of_dense_forwardOrbit [Preorder τ] [AddLeftMono τ] {x : X}
    (hx : Dense (ϕ.forwardOrbit x)) : ϕ.IsTopologicallyTransitive :=
  isTopologicallyTransitive_of_dense_orbit (hx.mono (ϕ.forwardOrbit_subset_orbit x))

/-- On a nonempty second-countable Baire space, for instance a nonempty compact metric space, a
flow is topologically transitive exactly when it has a dense orbit. -/
theorem isTopologicallyTransitive_iff_exists_dense_orbit [SecondCountableTopology X]
    [BaireSpace X] [Nonempty X] : ϕ.IsTopologicallyTransitive ↔ ∃ x, Dense (ϕ.orbit x) :=
  ⟨IsTopologicallyTransitive.exists_dense_orbit,
    fun ⟨_, hx⟩ ↦ isTopologicallyTransitive_of_dense_orbit hx⟩

end AddGroup

end Flow
