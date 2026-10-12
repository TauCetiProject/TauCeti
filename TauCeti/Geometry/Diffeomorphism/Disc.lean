/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.FixingSubgroup.Topology
public import TauCeti.Geometry.Manifold.Instances.ClosedBall
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Diffeomorphisms of the disc fixing its boundary, and Watanabe's theorem

The group `Diff(Dⁿ, ∂)` of smooth self-diffeomorphisms of the closed unit ball `Dⁿ ⊆ ℝⁿ` that fix
the boundary sphere pointwise carries the weak Whitney topology. The disc form of the Smale
conjecture in dimension `n` asserts that this space is contractible. It holds for `n = 2` (Smale)
and `n = 3` (Hatcher, whose proof of `Diff(S³) ≃ O(4)` establishes it in this form). In dimension
`4`, where it is the relative form of the conjecture `Diff(S⁴) ≃ O(5)`, Watanabe disproved it by
constructing rationally nontrivial elements of the homotopy groups of `Diff(D⁴, ∂)`; in
particular `π₁(Diff(D⁴, ∂))` has an element of infinite order.

This file states that theorem of Watanabe against the weak Whitney topology, and derives from it
that `Diff(D⁴, ∂)` is not contractible.

## Main definitions

* `TauCeti.DiscDiff n`: the group `Diff(Dⁿ, ∂)`.
* `TauCeti.WatanabeTheorem`: `π₁(Diff(D⁴, ∂))`, based at the identity, has an element of
  infinite order.

## Main results

* `TauCeti.DiscDiff.apply_eq`: an element of `Diff(Dⁿ, ∂)` fixes every unit vector.
* `TauCeti.watanabeTheorem_iff`: unfolds `WatanabeTheorem` to the existence of an element of
  infinite order in `π₁(Diff(D⁴, ∂))`.
* `TauCeti.WatanabeTheorem.not_contractibleSpace_discDiff_four`: Watanabe's theorem implies that
  `Diff(D⁴, ∂)` is not contractible, refuting the four-dimensional disc Smale conjecture.

## References

* T. Watanabe, *Some exotic nontrivial elements of the rational homotopy groups of `Diff(S⁴)`*,
  arXiv:1812.02448.
* A. Hatcher, *A proof of the Smale conjecture, `Diff(S³) ≃ O(4)`*, Ann. of Math. 117 (1983),
  553–607.
* R. Kirby, *Problems in Low-Dimensional Topology*, Problem 4.126.
-/

public section

open Metric
open scoped Manifold ContDiff Topology TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {n : ℕ} [NeZero n]

variable (n) in
/-- The group `Diff(Dⁿ, ∂)` of smooth self-diffeomorphisms of the closed unit ball of `ℝⁿ` that
fix its boundary pointwise. Under `open scoped TauCeti.DiffeomorphWeakWhitney` it carries the
subspace topology of the weak Whitney topology. -/
abbrev DiscDiff : Type :=
  RelativeDiff (𝓡∂ n) (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ∞
    ((𝓡∂ n).boundary (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))

/-- An element of `Diff(Dⁿ, ∂)` fixes every point of the unit sphere. -/
theorem DiscDiff.apply_eq (f : DiscDiff n) {x : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1}
    (hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1) :
    (f : Diff (𝓡∂ n) (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ∞) x = x :=
  have := Fact.mk (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
  RelativeDiff.apply_eq f (isBoundaryPoint_closedBall_iff.mpr hx)

/-- **Watanabe's theorem**: the fundamental group of `Diff(D⁴, ∂)`, with the weak Whitney topology
and based at the identity, has an element of infinite order. This fundamental group is abelian,
`Diff(D⁴, ∂)` being a topological group, so this says that `π₁(Diff(D⁴, ∂)) ⊗ ℚ ≠ 0`. -/
def WatanabeTheorem : Prop :=
  ∃ γ : π_ 1 (DiscDiff 4) 1, ¬ IsOfFinOrder γ

/-- Unfold Watanabe's theorem: `π₁(Diff(D⁴, ∂))`, based at the identity, has an element of
infinite order. -/
theorem watanabeTheorem_iff : WatanabeTheorem ↔ ∃ γ : π_ 1 (DiscDiff 4) 1, ¬ IsOfFinOrder γ :=
  (Iff.rfl)

/-- Watanabe's theorem refutes the four-dimensional disc Smale conjecture: `Diff(D⁴, ∂)` is not
contractible in the weak Whitney topology. -/
theorem WatanabeTheorem.not_contractibleSpace_discDiff_four (h : WatanabeTheorem) :
    ¬ ContractibleSpace (DiscDiff 4) := fun _ ↦ by
  obtain ⟨γ, hγ⟩ := h
  -- A contractible space is simply connected, so its first homotopy group is trivial.
  have : Subsingleton (π_ 1 (DiscDiff 4) 1) := HomotopyGroup.pi1EquivFundamentalGroup.subsingleton
  exact hγ (Subsingleton.elim 1 γ ▸ IsOfFinOrder.one)

end TauCeti
