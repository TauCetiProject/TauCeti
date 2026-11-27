/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import TauCeti.Analysis.AbsoluteValue.Inertia

/-!
# Closedness of the decomposition and inertia groups of an absolute value

Let a topological group `G` act continuously on a ring `L` that carries the discrete topology
(`[DiscreteTopology L] [ContinuousSMul G L]`), as `Gal(L/K)` does with its Krull topology. Then for
every absolute value `w` of `L` the decomposition group `MulAction.stabilizer G w` and the inertia
group `AbsoluteValue.inertia G w` are closed in `G`. Each defining condition, `w (σ • x) = w x` or
`w (σ • x - x) < 1` for one `x`, depends on `σ` only through `σ • x`, and `σ ↦ σ • x` is a
continuous map to a discrete space, so each condition cuts out a closed subset of `G`.

No compactness, normalisation or hypothesis relating `G` to a fixed field is needed, so this
applies to every absolute value of `L`, archimedean or not, and in particular to every place.

## Main results

* `AbsoluteValue.isClosed_stabilizer`: the decomposition group of `w` is closed.
* `AbsoluteValue.isClosed_inertia`: the inertia group of `w` is closed.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Ch. IV, §1.
-/

public section

namespace AbsoluteValue

variable {G L S : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace L] [DiscreteTopology L]

/-- For a continuous action on a discrete space, the set of `σ` such that `σ • x` satisfies a
given property is closed. -/
private theorem isClosed_setOf_smul [MulAction G L] [ContinuousSMul G L] (x : L) (p : L → Prop) :
    IsClosed {σ : G | p (σ • x)} :=
  (isClosed_discrete {y | p y}).preimage (continuous_id.smul continuous_const)

/-- **The decomposition group of an absolute value is closed.** If `G` acts continuously on a ring
`L` with the discrete topology, the stabilizer of every absolute value of `L` is closed. -/
theorem isClosed_stabilizer [Semiring L] [MulSemiringAction G L] [ContinuousSMul G L] [Semiring S]
    [PartialOrder S] (w : AbsoluteValue L S) :
    IsClosed (MulAction.stabilizer G w : Set G) := by
  have : (MulAction.stabilizer G w : Set G) = ⋂ x : L, {σ : G | w (σ • x) = w x} := by
    ext σ
    simpa using mem_stabilizer_iff_forall_apply_smul_eq (w := w) (σ := σ)
  rw [this]
  exact isClosed_iInter fun x ↦ isClosed_setOf_smul x (fun y ↦ w y = w x)

/-- **The inertia group of an absolute value is closed.** If `G` acts continuously on a ring `L`
with the discrete topology, the inertia group of every absolute value of `L` is closed. -/
theorem isClosed_inertia [Ring L] [MulSemiringAction G L] [ContinuousSMul G L] [CommRing S]
    [LinearOrder S] [IsStrictOrderedRing S] (w : AbsoluteValue L S) :
    IsClosed (w.inertia G : Set G) := by
  by_cases hw : IsNonarchimedean w
  · have : (w.inertia G : Set G) = (MulAction.stabilizer G w : Set G) ∩
        ⋂ x : L, ⋂ (_ : w x ≤ 1), {σ : G | w (σ • x - x) < 1} := by
      ext σ
      simp [mem_inertia_iff_of_isNonarchimedean hw]
    rw [this]
    exact (isClosed_stabilizer w).inter <| isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦
      isClosed_setOf_smul x (fun y ↦ w (y - x) < 1)
  · rw [inertia_eq_stabilizer hw]
    exact isClosed_stabilizer w

end AbsoluteValue
