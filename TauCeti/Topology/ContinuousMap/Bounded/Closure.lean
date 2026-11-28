/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import TauCeti.Topology.MetricSpace.Holder

/-!
# Bounded continuous functions on the closure of a set

A bounded continuous function on `closure s` is controlled by its values on `s`, which is dense in
`closure s`. So the uniform distance of two such functions is at most any bound on their pointwise
distances on `s` (`BoundedContinuousFunction.dist_le_of_forall_mem`).

Conversely, a function Hölder with a positive exponent on a bounded set `s` of a pseudometric
space, with values in a complete metric space, extends to a bounded continuous function on
`closure s` with the same Hölder constant and exponent
(`HolderOnWith.exists_holderWith_boundedContinuousFunction`). The extension is Mathlib's
`extendFrom s f` (`HolderOnWith.extendFrom_closure`), and the Hölder bound on the bounded set
`closure s` bounds it.
-/

public section

open Set
open scoped BoundedContinuousFunction NNReal

/-- Two bounded continuous functions on `closure s` whose values at each point of `s` are within
`c` of each other are within `c` of each other in the uniform distance. -/
theorem BoundedContinuousFunction.dist_le_of_forall_mem {X β : Type*} [TopologicalSpace X]
    [PseudoMetricSpace β] {s : Set X} (f g : closure s →ᵇ β) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x (hx : x ∈ s), dist (f ⟨x, subset_closure hx⟩) (g ⟨x, subset_closure hx⟩) ≤ c) :
    dist f g ≤ c := by
  refine (dist_le hc).2 fun x => ?_
  have hd : Dense (Subtype.val ⁻¹' s : Set (closure s)) := Subtype.dense_iff.2 <| by
    rw [Subtype.image_preimage_coe, inter_eq_right.2 subset_closure]
  have hC : IsClosed {y : closure s | dist (f y) (g y) ≤ c} :=
    isClosed_le (f.continuous.dist g.continuous) continuous_const
  have hsC : (Subtype.val ⁻¹' s : Set (closure s)) ⊆ {y | dist (f y) (g y) ≤ c} :=
    fun y hy => h y hy
  exact closure_minimal hsC hC (hd x)

/-- **Hölder functions on a bounded set extend to bounded continuous functions on its closure.**
A function `α`-Hölder with constant `C` on a bounded set `s`, `α > 0`, with values in a complete
metric space, agrees on `s` with a bounded continuous function on `closure s` that is `α`-Hölder
with constant `C`. -/
theorem HolderOnWith.exists_holderWith_boundedContinuousFunction {X Y : Type*}
    [PseudoMetricSpace X] [MetricSpace Y] [CompleteSpace Y] {C r : ℝ≥0} {f : X → Y} {s : Set X}
    (hf : HolderOnWith C r f s) (hr : 0 < r) (hs : Bornology.IsBounded s) :
    ∃ u : closure s →ᵇ Y, HolderWith C r u ∧ ∀ x (hx : x ∈ s), u ⟨x, subset_closure hx⟩ = f x := by
  obtain ⟨heq, hcl⟩ := hf.extendFrom_closure hr
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 (hcl.isBounded_image hs.closure)
  exact ⟨.mkOfBound ⟨_, (hcl.continuousOn hr).domRestrict⟩ D fun x y =>
    hD (mem_image_of_mem _ x.property) (mem_image_of_mem _ y.property), hcl.holderWith,
    fun x hx => heq hx⟩
