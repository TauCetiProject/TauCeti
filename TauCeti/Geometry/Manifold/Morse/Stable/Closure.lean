/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Gluing.Broken
public import TauCeti.Geometry.Manifold.Morse.Stable.Breaking

/-!
# Closures of stable and unstable manifolds

Let `f` be a Morse function on a compact boundaryless manifold `M`, and `X` a pseudo-gradient
adapted to `f` satisfying the Morse–Smale condition. Write `p ⇝ q` when a trajectory of `X` runs
from `p` to `q`, that is, when `W^u(p) ∩ W^s(q)` is nonempty
(`TauCeti.IsAdaptedPseudoGradient.FlowsTo`), and `⇝*` for its reflexive and
transitive closure (`Relation.ReflTransGen hX.FlowsTo`): `p ⇝* q` when `q = p` or a finite chain of
trajectories, broken at critical points, runs from `p` to `q`. This file shows that the closure of
an unstable manifold is the union of the unstable manifolds of the critical points below it,

`closure W^u(p) = ⋃_{p ⇝* q} W^u(q)`

(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.closure_unstableSet`), and dually
`closure W^s(q) = ⋃_{p ⇝* q} W^s(p)`
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.closure_stableSet`).

The relation `⇝*` is a partial order, in which `f` strictly decreases
(`TauCeti.IsAdaptedPseudoGradient.apply_lt_apply_of_reflTransGen`) and, under the Morse–Smale
condition, so does the Morse index
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.manifoldMorseIndex_lt_of_reflTransGen`). Only
finitely many points lie below a given one
(`TauCeti.IsAdaptedPseudoGradient.finite_setOf_reflTransGen`), all of them critical except
possibly the point itself. These facts about chains are proved in
`TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice`. Consequently the closure of `W^u(p)` is a
finite union of unstable manifolds, and what it adds to `W^u(p)` lies in the unstable manifolds
of critical points of smaller index
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.closure_unstableSet_diff_subset`). Since `W^u(q)`
is a manifold of dimension `ind q`, this is the frontier condition for the decomposition of `M`
into the unstable manifolds: what the closure of each piece adds lies in pieces of lower
dimension. Dually, what the closure of `W^s(q)` adds lies in the stable manifolds of critical
points of larger index.

The two inclusions come from the two halves of the compactness and gluing theory of trajectories.

* **Breaking** gives `⊆`. A point `y` of the closure of `W^u(p)` lies on the unstable manifold of
  the critical point `a` to which it flows backwards. If `a ≠ p`, limits of trajectories from `p`
  through `y` break at `a`: the closure of `W^u(p)` also meets `W^s(a)` at a point `z ≠ a`
  (`exists_mem_closure_inter_stableSet_of_mem_closure_inter_unstableSet` in the namespace
  `TauCeti.IsAdaptedPseudoGradient`), which flows backwards to a critical point `b` with `b ⇝ a`
  and `f a < f b`. Induction on the number of critical points above `f a` gives `p ⇝* b`, so
  `p ⇝* a` (`TauCeti.IsAdaptedPseudoGradient.reflTransGen_of_mem_closure_unstableSet`, in
  `TauCeti.Geometry.Manifold.Morse.Stable.Breaking`). This inclusion needs no Morse–Smale
  condition (`TauCeti.IsAdaptedPseudoGradient.closure_unstableSet_subset`).
* **Gluing** gives `⊇`. If `p ⇝ q`, every point `y ≠ q` of `W^u(q)` flows forwards to a critical
  point `r ≠ q`, and the broken trajectory from `p` to `r` through `q` and `y` is a limit of
  unbroken trajectories from `p` to `r`
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.mem_closure_of_mem_unstableSet_inter_stableSet`),
  so `y` lies in the closure of `W^u(p)`; so does `q`, the forward limit of a trajectory from `p`.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `closure_unstableSet_subset`, `closure_stableSet_subset`: without the Morse–Smale condition, the
  closure of `W^u(p)` lies in the unstable manifolds below `p`, and that of `W^s(q)` in the stable
  manifolds above `q`.
* `IsMorseSmale.closure_unstableSet`, `IsMorseSmale.closure_stableSet`: the closures of unstable
  and stable manifolds.
* `IsMorseSmale.mem_closure_unstableSet_iff`, `IsMorseSmale.mem_closure_stableSet_iff`: a critical
  point lies in the closure of `W^u(p)` exactly when it lies below `p`, and in the closure of
  `W^s(q)` exactly when it lies above `q`.
* `IsMorseSmale.closure_unstableSet_diff_subset`, `IsMorseSmale.closure_stableSet_diff_subset`:
  the closure of `W^u(p)` adds only unstable manifolds of smaller index, and that of `W^s(q)` only
  stable manifolds of larger index.

## References

* F. Laudenbach, *On the Thom–Smale complex*, appendix to J.-M. Bismut and W. Zhang, *An extension
  of a theorem by Cheeger and Müller*, Astérisque **205** (1992) (the closure of an unstable
  manifold of a Morse–Smale gradient is the union of the unstable manifolds below it).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (breaking and gluing of trajectories).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M] {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {p q : M}

/-! ### Gluing: unstable manifolds below `p` lie in the closure of `W^u(p)` -/

/-- If a trajectory runs from `p` to `q`, then `W^u(q)` lies in the closure of `W^u(p)`. -/
private theorem IsMorseSmale.unstableSet_subset_closure_unstableSet_of_nonempty
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hpq : (hX.flow.unstableSet p ∩ hX.flow.stableSet q).Nonempty) :
    hX.flow.unstableSet q ⊆ closure (hX.flow.unstableSet p) := by
  rcases eq_or_ne p q with rfl | hpq'
  · exact subset_closure
  obtain ⟨a, ha⟩ := hpq
  intro y hy
  by_cases hyq : y = q
  · -- `q` is the forward limit of the trajectory through `a`, which stays in `W^u(p)`.
    subst hyq
    exact mem_closure_of_tendsto (Flow.mem_stableSet.1 ha.2)
      (Eventually.of_forall fun t ↦ Flow.isInvariant_unstableSet _ p t ha.1)
  -- Otherwise `y` flows forwards to some `r ≠ q`, and the trajectory from `p` to `r` broken at `q`
  -- through `a` and `y` is a limit of unbroken trajectories from `p` to `r`.
  obtain ⟨r, -, hr⟩ := hX.exists_tendsto_atTop hf y
  have hyr : y ∈ hX.flow.stableSet r := Flow.mem_stableSet.2 hr
  have hqr : q ≠ r := fun hqr ↦
    hyq (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hy, hqr ▸ hyr⟩)
  refine map_mem_closure continuous_snd
    (h.mem_closure_of_mem_unstableSet_inter_stableSet hf hpq' hqr ha ⟨hy, hyr⟩) fun w hw ↦ ?_
  obtain ⟨⟨hw₁, -⟩, -, -, t, ht⟩ := hw
  rw [← ht]
  exact Flow.isInvariant_unstableSet _ p t hw₁

/-- If a trajectory runs from `p` to `q`, then `W^s(p)` lies in the closure of `W^s(q)`. -/
private theorem IsMorseSmale.stableSet_subset_closure_stableSet_of_nonempty
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hpq : (hX.flow.unstableSet p ∩ hX.flow.stableSet q).Nonempty) :
    hX.flow.stableSet p ⊆ closure (hX.flow.stableSet q) := by
  rcases eq_or_ne p q with rfl | hpq'
  · exact subset_closure
  obtain ⟨a, ha⟩ := hpq
  intro y hy
  by_cases hyp : y = p
  · -- `p` is the backward limit of the trajectory through `a`, which stays in `W^s(q)`.
    subst hyp
    exact mem_closure_of_tendsto (Flow.mem_unstableSet.1 ha.1)
      (Eventually.of_forall fun t ↦ Flow.isInvariant_stableSet _ q t ha.2)
  -- Otherwise `y` flows backwards to some `x ≠ p`, and the trajectory from `x` to `q` broken at `p`
  -- through `y` and `a` is a limit of unbroken trajectories from `x` to `q`.
  obtain ⟨x, -, hx⟩ := hX.exists_tendsto_atBot hf y
  have hyx : y ∈ hX.flow.unstableSet x := Flow.mem_unstableSet.2 hx
  have hxp : x ≠ p := fun hxp ↦
    hyp (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hxp ▸ hyx, hy⟩)
  exact map_mem_closure continuous_fst
    (h.mem_closure_of_mem_unstableSet_inter_stableSet hf hxp hpq' ⟨hyx, hy⟩ ha)
    fun w hw ↦ hw.1.2

/-- **Unstable manifolds below `p` lie in the closure of `W^u(p)`.** Under the Morse–Smale
condition, if a chain of trajectories runs from `p` to `q`, then `W^u(q)` lies in the closure of
`W^u(p)`. -/
theorem IsMorseSmale.unstableSet_subset_closure_unstableSet (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f)
    (hpq : Relation.ReflTransGen hX.FlowsTo p q) :
    hX.flow.unstableSet q ⊆ closure (hX.flow.unstableSet p) := by
  induction hpq with
  | refl => exact subset_closure
  | tail _ hbc ih =>
    exact (h.unstableSet_subset_closure_unstableSet_of_nonempty hf (flowsTo_iff.1 hbc)).trans
      (closure_minimal ih isClosed_closure)

/-- **Stable manifolds above `q` lie in the closure of `W^s(q)`.** Under the Morse–Smale
condition, if a chain of trajectories runs from `p` to `q`, then `W^s(p)` lies in the closure of
`W^s(q)`. -/
theorem IsMorseSmale.stableSet_subset_closure_stableSet (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f)
    (hpq : Relation.ReflTransGen hX.FlowsTo p q) :
    hX.flow.stableSet p ⊆ closure (hX.flow.stableSet q) := by
  induction hpq with
  | refl => exact subset_closure
  | tail _ hbc ih =>
    exact ih.trans (closure_minimal
      (h.stableSet_subset_closure_stableSet_of_nonempty hf (flowsTo_iff.1 hbc)) isClosed_closure)

/-! ### The closures -/

/-- **The closure of `W^u(p)` lies in the unstable manifolds below `p`.** Every point of the
closure of `W^u(p)` lies on the unstable manifold `W^u(q)` of a point `q` reached from `p` by a
chain of trajectories. -/
theorem closure_unstableSet_subset (hX : IsAdaptedPseudoGradient f X) (hf : IsMorse 𝓘(ℝ, E) f)
    (p : M) :
    closure (hX.flow.unstableSet p) ⊆ ⋃ (q) (_ : Relation.ReflTransGen hX.FlowsTo p q),
        hX.flow.unstableSet q := fun y hy ↦ by
  obtain ⟨a, -, ha⟩ := hX.exists_tendsto_atBot hf y
  have hya : y ∈ hX.flow.unstableSet a := Flow.mem_unstableSet.2 ha
  exact mem_iUnion₂.2 ⟨a, reflTransGen_of_mem_closure_unstableSet hf hy hya, hya⟩

/-- **The closure of `W^s(q)` lies in the stable manifolds above `q`.** Every point of the closure
of `W^s(q)` lies on the stable manifold `W^s(p)` of a point `p` from which a chain of trajectories
runs to `q`. -/
theorem closure_stableSet_subset (hX : IsAdaptedPseudoGradient f X) (hf : IsMorse 𝓘(ℝ, E) f)
    (q : M) :
    closure (hX.flow.stableSet q) ⊆ ⋃ (p) (_ : Relation.ReflTransGen hX.FlowsTo p q),
        hX.flow.stableSet p := fun y hy ↦ by
  obtain ⟨b, -, hb⟩ := hX.exists_tendsto_atTop hf y
  have hyb : y ∈ hX.flow.stableSet b := Flow.mem_stableSet.2 hb
  exact mem_iUnion₂.2 ⟨b, reflTransGen_of_mem_closure_stableSet hf hy hyb, hyb⟩

/-- **The closure of an unstable manifold.** Under the Morse–Smale condition, the closure of
`W^u(p)` is the union of the unstable manifolds `W^u(q)` of the points `q` reached from `p` by
chains of trajectories. -/
theorem IsMorseSmale.closure_unstableSet (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (p : M) :
    closure (hX.flow.unstableSet p) = ⋃ (q) (_ : Relation.ReflTransGen hX.FlowsTo p q),
        hX.flow.unstableSet q :=
  (hX.closure_unstableSet_subset hf p).antisymm
    (iUnion₂_subset fun _ hq ↦ h.unstableSet_subset_closure_unstableSet hf hq)

/-- **The closure of a stable manifold.** Under the Morse–Smale condition, the closure of `W^s(q)`
is the union of the stable manifolds `W^s(p)` of the points `p` from which chains of trajectories
run to `q`. -/
theorem IsMorseSmale.closure_stableSet (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) (q : M) :
    closure (hX.flow.stableSet q) = ⋃ (p) (_ : Relation.ReflTransGen hX.FlowsTo p q),
        hX.flow.stableSet p :=
  (hX.closure_stableSet_subset hf q).antisymm
    (iUnion₂_subset fun _ hp ↦ h.stableSet_subset_closure_stableSet hf hp)

/-- **The critical points in the closure of `W^u(p)`** are the critical points below `p`: under the
Morse–Smale condition, a critical point `q` lies in the closure of `W^u(p)` exactly when a chain of
trajectories runs from `p` to `q`. -/
theorem IsMorseSmale.mem_closure_unstableSet_iff (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0) :
    q ∈ closure (hX.flow.unstableSet p) ↔ Relation.ReflTransGen hX.FlowsTo p q :=
  ⟨fun hq' ↦ reflTransGen_of_mem_closure_unstableSet hf hq'
      (hX.mem_unstableSet_inter_stableSet_self hq).1,
    fun hpq ↦ h.unstableSet_subset_closure_unstableSet hf hpq
      (hX.mem_unstableSet_inter_stableSet_self hq).1⟩

/-- **The critical points in the closure of `W^s(q)`** are the critical points above `q`: under the
Morse–Smale condition, a critical point `p` lies in the closure of `W^s(q)` exactly when a chain of
trajectories runs from `p` to `q`. -/
theorem IsMorseSmale.mem_closure_stableSet_iff (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) :
    p ∈ closure (hX.flow.stableSet q) ↔ Relation.ReflTransGen hX.FlowsTo p q :=
  ⟨fun hp' ↦ reflTransGen_of_mem_closure_stableSet hf hp'
      (hX.mem_unstableSet_inter_stableSet_self hp).2,
    fun hpq ↦ h.stableSet_subset_closure_stableSet hf hpq
      (hX.mem_unstableSet_inter_stableSet_self hp).2⟩

/-- **The closure of `W^u(p)` adds only unstable manifolds of smaller index.** Under the
Morse–Smale condition, the points of the closure of `W^u(p)` outside `W^u(p)` lie on the unstable
manifolds of critical points `q` below `p` with `ind q < ind p`, which have smaller dimension
than `W^u(p)`. -/
theorem IsMorseSmale.closure_unstableSet_diff_subset (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (p : M) :
    closure (hX.flow.unstableSet p) \ hX.flow.unstableSet p ⊆
      ⋃ (q) (_ : Relation.ReflTransGen hX.FlowsTo p q)
        (_ : manifoldMorseIndex 𝓘(ℝ, E) f q < manifoldMorseIndex 𝓘(ℝ, E) f p),
        hX.flow.unstableSet q := by
  rintro y ⟨hy, hyp⟩
  obtain ⟨a, -, ha⟩ := hX.exists_tendsto_atBot hf y
  have hya : y ∈ hX.flow.unstableSet a := Flow.mem_unstableSet.2 ha
  have hap : a ≠ p := fun hap ↦ hyp (hap ▸ hya)
  simp only [mem_iUnion]
  exact ⟨a, reflTransGen_of_mem_closure_unstableSet hf hy hya,
    h.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet hf hap ⟨y, hy, hya⟩, hya⟩

/-- **The closure of `W^s(q)` adds only stable manifolds of larger index.** Under the Morse–Smale
condition, the points of the closure of `W^s(q)` outside `W^s(q)` lie on the stable manifolds of
critical points `p` above `q` with `ind q < ind p`. -/
theorem IsMorseSmale.closure_stableSet_diff_subset (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (q : M) :
    closure (hX.flow.stableSet q) \ hX.flow.stableSet q ⊆
      ⋃ (p) (_ : Relation.ReflTransGen hX.FlowsTo p q)
        (_ : manifoldMorseIndex 𝓘(ℝ, E) f q < manifoldMorseIndex 𝓘(ℝ, E) f p),
        hX.flow.stableSet p := by
  rintro y ⟨hy, hyq⟩
  obtain ⟨b, -, hb⟩ := hX.exists_tendsto_atTop hf y
  have hyb : y ∈ hX.flow.stableSet b := Flow.mem_stableSet.2 hb
  have hbq : b ≠ q := fun hbq ↦ hyq (hbq ▸ hyb)
  simp only [mem_iUnion]
  exact ⟨b, reflTransGen_of_mem_closure_stableSet hf hy hyb,
    h.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet hf hbq ⟨y, hy, hyb⟩, hyb⟩

end IsAdaptedPseudoGradient

end TauCeti
