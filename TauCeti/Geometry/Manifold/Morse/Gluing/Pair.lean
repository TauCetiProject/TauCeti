/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Gluing.Broken
public import TauCeti.Geometry.Manifold.Morse.Stable.Pair

/-!
# Gluing the broken configurations of a Morse–Smale pair

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M`, and `X₀`, `X₁`
pseudo-gradients adapted to them, forming a Morse–Smale pair
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmalePair`). The intersections
`W^u_{X₀}(p) ∩ W^s_{X₁}(r)` are the moduli spaces behind continuation maps between Morse complexes.
A limit of points of such an intersection breaks at most at the source or at the target
(`IsMorseSmalePair.exists_mem_unstableSet_inter_stableSet_of_mem_closure`), into a configuration
of one of two kinds:

* **at the source**: a trajectory of `X₀` from `p` to a critical point `a` of `f₀`, followed by a
  point `y` of `W^u_{X₀}(a) ∩ W^s_{X₁}(r)`;
* **at the target**: a point `y` of `W^u_{X₀}(p) ∩ W^s_{X₁}(b)` for a critical point `b` of `f₁`,
  followed by a trajectory of `X₁` from `b` to `r`.

This file proves the converse, the gluing step: every such configuration with `y` off the
critical point where it breaks is a limit of points of `W^u_{X₀}(p) ∩ W^s_{X₁}(r)`, along orbits
following the broken trajectory. At the source, `W^s_{X₁}(r)` is a set flattened near `y` and
transverse there to `W^u_{X₀}(a)`, by the Morse–Smale condition of the pair, so the gluing of
`X₀` into a transverse set applies
(`IsMorseSmale.exists_mem_unstableSet_inter_flow_mem_of_isSliceChart`). At the target, reversing
both fields turns the configuration into one breaking at the source for the Morse–Smale pair
`(-X₁, -X₀)` (`IsMorseSmalePair.neg`).

When `ind p = ind r + 1`, the intersection is one-dimensional and these configurations are the
two kinds of ends that pair up in the proof that a continuation map is a chain map
(`IsMorseSmalePair.closure_unstableSet_inter_stableSet_subset`). Configurations breaking at a
point `y` equal to the critical point `a` (or `b`) itself are not treated here: the gluing above
reaches `y` along the orbit of `y`, which is constant at a critical point.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmalePair`:

* `exists_mem_unstableSet_inter_stableSet_flow_mem_of_source`,
  `mem_closure_unstableSet_inter_stableSet_of_source`: a configuration breaking at the source is
  a limit of points of `W^u_{X₀}(p) ∩ W^s_{X₁}(r)`, whose `X₀`-orbits pass near the trajectory of
  `X₀`.
* `exists_mem_unstableSet_inter_stableSet_flow_mem_of_target`,
  `mem_closure_unstableSet_inter_stableSet_of_target`: a configuration breaking at the target is
  a limit of points of `W^u_{X₀}(p) ∩ W^s_{X₁}(r)`, whose `X₁`-orbits pass near the trajectory of
  `X₁`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (the continuation map is a chain map, by counting the
  ends of the one-dimensional moduli spaces of continuation trajectories).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing of broken trajectories) and Chapter 6 (invariance of Morse homology by
  continuation).
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p r a b a₁ a₂ y : M}

namespace IsAdaptedPseudoGradient

namespace IsMorseSmalePair

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}

/-- **Gluing at the source.** Let `(X₀, X₁)` be a Morse–Smale pair with `X₀` Morse–Smale, `a₁` a
point of a trajectory of `X₀` from `p` to a critical point `a ≠ p`, and `y ≠ a` a point of
`W^u_{X₀}(a) ∩ W^s_{X₁}(r)`. For all neighbourhoods `N₁` of `a₁` and `N` of `y`, some point of
`W^u_{X₀}(p) ∩ W^s_{X₁}(r)` lies in `N` and its `X₀`-orbit passes through `N₁`. -/
theorem exists_mem_unstableSet_inter_stableSet_flow_mem_of_source
    (h : IsMorseSmalePair hX₀ hX₁) (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hpa : p ≠ a) (ha₁ : a₁ ∈ hX₀.flow.unstableSet p ∩ hX₀.flow.stableSet a)
    (hy : y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet r) (hya : y ≠ a) {N₁ N : Set M}
    (hN₁ : N₁ ∈ 𝓝 a₁) (hN : N ∈ 𝓝 y) :
    ∃ w ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r, w ∈ N ∧ ∃ s : ℝ, hX₀.flow s w ∈ N₁ := by
  -- `W^s_{X₁}(r)` is flattened near `y` and, by the pair condition, transverse to `W^u_{X₀}(a)`.
  obtain ⟨L, φ, -, hyφ, hφ, hS⟩ :=
    hX₁.exists_isSliceChart_stableSet (hX₁.mfderiv_eq_zero_of_mem_stableSet hy.2) hy.2
  exact h₀.exists_mem_unstableSet_inter_flow_mem_of_isSliceChart hf₀ hpa ha₁ hy.1 hya hφ hS hyφ
    hy.2 (by rw [sup_comm]; exact h.span_mtangentConeAt_sup_eq_top hy) hN₁ hN

/-- **Configurations breaking at the source are limits.** Let `(X₀, X₁)` be a Morse–Smale pair
with `X₀` Morse–Smale. If a trajectory of `X₀` runs from `p` to a critical point `a ≠ p`, then
every point `y ≠ a` of `W^u_{X₀}(a) ∩ W^s_{X₁}(r)` lies in the closure of
`W^u_{X₀}(p) ∩ W^s_{X₁}(r)`. -/
theorem mem_closure_unstableSet_inter_stableSet_of_source (h : IsMorseSmalePair hX₀ hX₁)
    (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hpa : p ≠ a)
    (ha₁ : a₁ ∈ hX₀.flow.unstableSet p ∩ hX₀.flow.stableSet a)
    (hy : y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet r) (hya : y ≠ a) :
    y ∈ closure (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r) := by
  refine mem_closure_iff_nhds.2 fun N hN ↦ ?_
  obtain ⟨w, hw, hwN, -⟩ :=
    h.exists_mem_unstableSet_inter_stableSet_flow_mem_of_source h₀ hf₀ hpa ha₁ hy hya
      Filter.univ_mem hN
  exact ⟨w, hwN, hw⟩

/-- **Gluing at the target.** Let `(X₀, X₁)` be a Morse–Smale pair with `X₁` Morse–Smale, `a₂` a
point of a trajectory of `X₁` from a critical point `b` to `r ≠ b`, and `y ≠ b` a point of
`W^u_{X₀}(p) ∩ W^s_{X₁}(b)`. For all neighbourhoods `N₂` of `a₂` and `N` of `y`, some point of
`W^u_{X₀}(p) ∩ W^s_{X₁}(r)` lies in `N` and its `X₁`-orbit passes through `N₂`. -/
theorem exists_mem_unstableSet_inter_stableSet_flow_mem_of_target
    (h : IsMorseSmalePair hX₀ hX₁) (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hbr : b ≠ r)
    (ha₂ : a₂ ∈ hX₁.flow.unstableSet b ∩ hX₁.flow.stableSet r)
    (hy : y ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet b) (hyb : y ≠ b) {N₂ N : Set M}
    (hN₂ : N₂ ∈ 𝓝 a₂) (hN : N ∈ 𝓝 y) :
    ∃ w ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r, w ∈ N ∧ ∃ s : ℝ, hX₁.flow s w ∈ N₂ := by
  -- Reversing both fields, the configuration breaks at the source for the pair `(-X₁, -X₀)`.
  have hrev := (h.neg hf₀ hf₁).exists_mem_unstableSet_inter_stableSet_flow_mem_of_source
    (h₁.neg hf₁) hf₁.neg hbr.symm (a₁ := a₂) (y := y) (r := p)
    (by rwa [hX₁.neg_flow hf₁, Flow.unstableSet_reverse, Flow.stableSet_reverse, inter_comm])
    (by rwa [hX₁.neg_flow hf₁, hX₀.neg_flow hf₀, Flow.unstableSet_reverse,
      Flow.stableSet_reverse, inter_comm]) hyb hN₂ hN
  rw [hX₁.neg_flow hf₁, hX₀.neg_flow hf₀, Flow.unstableSet_reverse, Flow.stableSet_reverse,
    inter_comm] at hrev
  obtain ⟨w, hw, hwN, s, hs⟩ := hrev
  exact ⟨w, hw, hwN, -s, by rwa [Flow.reverse_apply] at hs⟩

/-- **Configurations breaking at the target are limits.** Let `(X₀, X₁)` be a Morse–Smale pair
with `X₁` Morse–Smale. If a trajectory of `X₁` runs from a critical point `b` to `r ≠ b`, then
every point `y ≠ b` of `W^u_{X₀}(p) ∩ W^s_{X₁}(b)` lies in the closure of
`W^u_{X₀}(p) ∩ W^s_{X₁}(r)`. -/
theorem mem_closure_unstableSet_inter_stableSet_of_target (h : IsMorseSmalePair hX₀ hX₁)
    (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hbr : b ≠ r)
    (ha₂ : a₂ ∈ hX₁.flow.unstableSet b ∩ hX₁.flow.stableSet r)
    (hy : y ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet b) (hyb : y ≠ b) :
    y ∈ closure (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r) := by
  refine mem_closure_iff_nhds.2 fun N hN ↦ ?_
  obtain ⟨w, hw, hwN, -⟩ :=
    h.exists_mem_unstableSet_inter_stableSet_flow_mem_of_target h₁ hf₀ hf₁ hbr ha₂ hy hyb
      Filter.univ_mem hN
  exact ⟨w, hwN, hw⟩

end IsMorseSmalePair

end IsAdaptedPseudoGradient

end TauCeti
