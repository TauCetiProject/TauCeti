/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Stable and unstable sets of a flow

For a real flow `φ`, the stable set of `x` consists of the points whose trajectories converge to
`x` as time tends to `+∞`; the unstable set uses time tending to `-∞`.  These are the underlying
sets which the stable-manifold theorem identifies locally as smooth manifolds near a hyperbolic
fixed point.

Both sets are invariant under the entire flow.  Moreover, either set can be nonempty only when
its limiting point is fixed by the flow.  Time reversal exchanges the two constructions.

## Main declarations

* `Flow.stableSet`: points converging to a given point in forward time.
* `Flow.unstableSet`: points converging to a given point in backward time.
* `Flow.isInvariant_stableSet` and `Flow.isInvariant_unstableSet`: invariance
  under time translation.
* `Flow.fixed_of_mem_stableSet` and `Flow.fixed_of_mem_unstableSet`: a limiting
  point of a trajectory is fixed.
* `Flow.stableSet_reverse` and `Flow.unstableSet_reverse`: time reversal exchanges
  stable and unstable sets.
* `Homeomorph.image_stableSet_eq` and `Homeomorph.image_unstableSet_eq`: a topological conjugacy
  transports stable and unstable sets.
* `Homeomorph.image_unstableSet_inter_stableSet_eq`: a conjugacy transports the set of
  connecting points between two endpoints.

## References

The stable and unstable set viewpoint follows M. Audin and M. Damian, *Morse Theory and Floer
Homology*, Springer Universitext (2014), Chapter 2, §2.1.d.  The conjugacy and coordinate-transport
perspective is used throughout D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic
Topology*, 2nd ed., AMS (2012), Chapters 2–4 and 10, with analytic background in Appendices A–C.
-/

public section

open Filter Set Topology

namespace Flow

variable {α : Type*} [TopologicalSpace α]

/-- The **stable set** of `x` under a real flow `φ`: the points whose trajectories converge to
`x` as time tends to `+∞`. -/
def stableSet (φ : _root_.Flow ℝ α) (x : α) : Set α :=
  {y | Tendsto (fun t ↦ φ t y) atTop (𝓝 x)}

/-- The **unstable set** of `x` under a real flow `φ`: the points whose trajectories converge to
`x` as time tends to `-∞`. -/
def unstableSet (φ : _root_.Flow ℝ α) (x : α) : Set α :=
  {y | Tendsto (fun t ↦ φ t y) atBot (𝓝 x)}

/-- Membership in a stable set means convergence of the trajectory in forward time. -/
@[simp]
theorem mem_stableSet {φ : _root_.Flow ℝ α} {x y : α} :
    y ∈ stableSet φ x ↔ Tendsto (fun t ↦ φ t y) atTop (𝓝 x) :=
  Iff.rfl

/-- Membership in an unstable set means convergence of the trajectory in backward time. -/
@[simp]
theorem mem_unstableSet {φ : _root_.Flow ℝ α} {x y : α} :
    y ∈ unstableSet φ x ↔ Tendsto (fun t ↦ φ t y) atBot (𝓝 x) :=
  Iff.rfl

/-- The stable set of a point is invariant under every time map of the flow. -/
theorem isInvariant_stableSet (φ : _root_.Flow ℝ α) (x : α) :
    IsInvariant φ (stableSet φ x) := by
  intro t y hy
  rw [mem_stableSet] at hy ⊢
  simpa only [Function.comp_def, ← φ.map_add, id_eq] using
    hy.comp (tendsto_atTop_add_const_right atTop t tendsto_id)

/-- The unstable set of a point is invariant under every time map of the flow. -/
theorem isInvariant_unstableSet (φ : _root_.Flow ℝ α) (x : α) :
    IsInvariant φ (unstableSet φ x) := by
  intro t y hy
  rw [mem_unstableSet] at hy ⊢
  simpa only [Function.comp_def, ← φ.map_add, id_eq] using
    hy.comp (tendsto_atBot_add_const_right atBot t tendsto_id)

/-- If some trajectory converges to `x` in forward time, then `x` is fixed by every time map of
the flow. -/
theorem fixed_of_mem_stableSet [T2Space α] {φ : _root_.Flow ℝ α} {x y : α}
    (hy : y ∈ stableSet φ x) (t : ℝ) :
    φ t x = x := by
  rw [mem_stableSet] at hy
  have hleft : Tendsto (fun u ↦ φ t (φ u y)) atTop (𝓝 (φ t x)) :=
    (φ.continuous_toFun t).continuousAt.tendsto.comp hy
  have hright : Tendsto (fun u ↦ φ t (φ u y)) atTop (𝓝 x) := by
    simpa only [Function.comp_def, ← φ.map_add, add_comm, id_eq] using
      hy.comp (tendsto_atTop_add_const_right atTop t tendsto_id)
  exact tendsto_nhds_unique hleft hright

/-- If some trajectory converges to `x` in backward time, then `x` is fixed by every time map of
the flow. -/
theorem fixed_of_mem_unstableSet [T2Space α] {φ : _root_.Flow ℝ α} {x y : α}
    (hy : y ∈ unstableSet φ x) (t : ℝ) :
    φ t x = x := by
  rw [mem_unstableSet] at hy
  have hleft : Tendsto (fun u ↦ φ t (φ u y)) atBot (𝓝 (φ t x)) :=
    (φ.continuous_toFun t).continuousAt.tendsto.comp hy
  have hright : Tendsto (fun u ↦ φ t (φ u y)) atBot (𝓝 x) := by
    simpa only [Function.comp_def, ← φ.map_add, add_comm, id_eq] using
      hy.comp (tendsto_atBot_add_const_right atBot t tendsto_id)
  exact tendsto_nhds_unique hleft hright

/-- A point belongs to its stable set exactly when it is fixed by the flow. -/
@[simp 1200]
theorem self_mem_stableSet_iff [T2Space α] {φ : _root_.Flow ℝ α} {x : α} :
    x ∈ stableSet φ x ↔ ∀ t, φ t x = x := by
  refine ⟨fun hx t ↦ fixed_of_mem_stableSet hx t, fun hx ↦ ?_⟩
  rw [mem_stableSet]
  simpa only [hx] using (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ x) atTop (𝓝 x))

/-- A point belongs to its unstable set exactly when it is fixed by the flow. -/
@[simp 1200]
theorem self_mem_unstableSet_iff [T2Space α] {φ : _root_.Flow ℝ α} {x : α} :
    x ∈ unstableSet φ x ↔ ∀ t, φ t x = x := by
  refine ⟨fun hx t ↦ fixed_of_mem_unstableSet hx t, fun hx ↦ ?_⟩
  rw [mem_unstableSet]
  simpa only [hx] using (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ x) atBot (𝓝 x))

/-- Time reversal is an involution. -/
@[simp]
theorem reverse_reverse {τ : Type*} [TopologicalSpace τ] [SubtractionCommMonoid τ]
    [ContinuousNeg τ] (φ : _root_.Flow τ α) : φ.reverse.reverse = φ :=
  _root_.Flow.ext fun t _ ↦ by simp only [_root_.Flow.reverse_apply, neg_neg]

/-- Time reversal exchanges stable and unstable sets. -/
@[simp]
theorem stableSet_reverse (φ : _root_.Flow ℝ α) (x : α) :
    stableSet φ.reverse x = unstableSet φ x := by
  ext y
  simp only [mem_stableSet, mem_unstableSet, _root_.Flow.reverse_apply]
  constructor
  · intro h
    simpa only [Function.comp_def, neg_neg] using h.comp tendsto_neg_atBot_atTop
  · intro h
    simpa only [Function.comp_def, neg_neg] using h.comp tendsto_neg_atTop_atBot

/-- Time reversal exchanges unstable and stable sets. -/
@[simp]
theorem unstableSet_reverse (φ : _root_.Flow ℝ α) (x : α) :
    unstableSet φ.reverse x = stableSet φ x := by
  rw [← stableSet_reverse φ.reverse x, reverse_reverse]

/-- Under the identity flow, the stable set of `x` is the singleton `{x}`. -/
@[simp]
theorem stableSet_id [T1Space α] (x : α) :
    stableSet (_root_.Flow.id ℝ α) x = {x} := by
  ext y
  simp [stableSet]

/-- Under the identity flow, the unstable set of `x` is the singleton `{x}`. -/
@[simp]
theorem unstableSet_id [T1Space α] (x : α) :
    unstableSet (_root_.Flow.id ℝ α) x = {x} := by
  ext y
  simp [unstableSet]

section Conjugacy

variable {β : Type*} [TopologicalSpace β]
  {φ : _root_.Flow ℝ α} {ψ : _root_.Flow ℝ β} (e : α ≃ₜ β)

theorem _root_.Homeomorph.map_flow_symm (hconj : ∀ t x, e (φ t x) = ψ t (e x)) (t : ℝ) (y : β) :
    e.symm (ψ t y) = φ t (e.symm y) := by
  apply e.injective
  rw [e.apply_symm_apply, hconj, e.apply_symm_apply]

private theorem tendsto_map_flow_iff (hconj : ∀ t x, e (φ t x) = ψ t (e x)) {l : Filter ℝ}
    {x y : α} :
    Tendsto (fun t ↦ ψ t (e y)) l (𝓝 (e x)) ↔ Tendsto (fun t ↦ φ t y) l (𝓝 x) := by
  constructor
  · intro hy
    have h := e.symm.continuous.continuousAt.tendsto.comp hy
    have h' : Tendsto (e.symm ∘ fun t ↦ ψ t (e y)) l (𝓝 x) := by
      simpa only [e.symm_apply_apply] using h
    refine Filter.Tendsto.congr' (f₂ := fun t ↦ φ t y) (Eventually.of_forall fun t ↦ by
      simp only [Function.comp_apply, e.map_flow_symm hconj, e.symm_apply_apply])
      h'
  · intro hy
    have h := e.continuous.continuousAt.tendsto.comp hy
    refine Filter.Tendsto.congr' (f₂ := fun t ↦ ψ t (e y)) (Eventually.of_forall fun t ↦ by
      simpa only [Function.comp_apply] using hconj t y) h

/-- A topological conjugacy carries membership in a stable set to membership in the
corresponding stable set. -/
theorem _root_.Homeomorph.mem_stableSet_map_iff
    (hconj : ∀ t x, e (φ t x) = ψ t (e x)) {x : α} {y : α} :
    e y ∈ stableSet ψ (e x) ↔ y ∈ stableSet φ x := by
  rw [mem_stableSet, mem_stableSet]
  exact tendsto_map_flow_iff e hconj

/-- A topological conjugacy carries a stable set to the corresponding stable set. -/
theorem _root_.Homeomorph.image_stableSet_eq
    (hconj : ∀ t x, e (φ t x) = ψ t (e x)) (x : α) :
    e '' stableSet φ x = stableSet ψ (e x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (e.mem_stableSet_map_iff hconj).2 hz
  · intro hy
    refine ⟨e.symm y, (e.mem_stableSet_map_iff hconj).1 ?_, e.apply_symm_apply y⟩
    simpa only [e.apply_symm_apply] using hy

/-- A topological conjugacy carries membership in an unstable set to membership in the
corresponding unstable set. -/
theorem _root_.Homeomorph.mem_unstableSet_map_iff
    (hconj : ∀ t x, e (φ t x) = ψ t (e x)) {x : α} {y : α} :
    e y ∈ unstableSet ψ (e x) ↔ y ∈ unstableSet φ x := by
  rw [mem_unstableSet, mem_unstableSet]
  exact tendsto_map_flow_iff e hconj

/-- A topological conjugacy carries an unstable set to the corresponding unstable set. -/
theorem _root_.Homeomorph.image_unstableSet_eq
    (hconj : ∀ t x, e (φ t x) = ψ t (e x)) (x : α) :
    e '' unstableSet φ x = unstableSet ψ (e x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (e.mem_unstableSet_map_iff hconj).2 hz
  · intro hy
    refine ⟨e.symm y, (e.mem_unstableSet_map_iff hconj).1 ?_, e.apply_symm_apply y⟩
    simpa only [e.apply_symm_apply] using hy

/-- A topological conjugacy transports the points whose trajectories connect two endpoints. -/
theorem _root_.Homeomorph.image_unstableSet_inter_stableSet_eq
    (hconj : ∀ t x, e (φ t x) = ψ t (e x)) (p q : α) :
    e '' (unstableSet φ p ∩ stableSet φ q) =
      unstableSet ψ (e p) ∩ stableSet ψ (e q) := by
  rw [Set.image_inter e.injective, e.image_unstableSet_eq hconj, e.image_stableSet_eq hconj]

end Conjugacy

end Flow
