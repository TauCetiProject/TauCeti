/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Gluing.Transverse
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

This file proves the converse, the gluing step: every such configuration is a limit of points of
`W^u_{X₀}(p) ∩ W^s_{X₁}(r)`, along orbits following the broken trajectory. This includes the
configurations in which `y` is the critical point `a` (or `b`) itself, which occur for instance
when `X₀ = X₁` and `a = r` (or `b = p`). At the source, `W^s_{X₁}(r)` is a
set flattened near `y` and transverse there to `W^u_{X₀}(a)`, by the Morse–Smale condition of the
pair, so the gluing of `X₀` into a transverse set applies
(`IsMorseSmale.exists_mem_unstableSet_inter_flow_mem_of_isSliceChart`), whether or not `y = a`.
At the target, reversing both fields turns the configuration into one breaking at the source for
the Morse–Smale pair `(-X₁, -X₀)` (`IsMorseSmalePair.neg`).

When `ind p = ind r + 1`, the intersection is one-dimensional and these configurations are the
two kinds of ends that pair up in the proof that a continuation map is a chain map
(`IsMorseSmalePair.closure_unstableSet_inter_stableSet_subset`). Each of them with `y` off the
critical point where it breaks is then an endpoint: recording a point `x` of the intersection by
`x` together with the point of its `X₀`-orbit on the level of a point `a₁` of the trajectory from
`p` to `a`, a configuration breaking at the source has a neighbourhood among these records
homeomorphic to a half-open interval `[0, δ)` (`IsMorseSmalePair.exists_homeomorph_Ico_of_source`,
the case of a stable manifold of `IsMorseSmale.exists_homeomorph_Ico_of_isSliceChart`), and
likewise at the target with the `X₁`-orbits (`IsMorseSmalePair.exists_homeomorph_Ico_of_target`).

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
* `exists_homeomorph_Ico_of_source`, `exists_homeomorph_Ico_of_target`: for `ind p = ind r + 1`,
  a configuration breaking at the source or at the target, with `y` off the critical point where
  it breaks (`y ≠ a`, respectively `y ≠ b`), is an endpoint of the compactified one-dimensional
  intersection.

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
point of a trajectory of `X₀` from `p` to a critical point `a ≠ p`, and `y` a point of
`W^u_{X₀}(a) ∩ W^s_{X₁}(r)`, possibly `a` itself. For all neighbourhoods `N₁` of `a₁` and `N` of
`y`, some point of `W^u_{X₀}(p) ∩ W^s_{X₁}(r)` lies in `N` and its `X₀`-orbit passes through
`N₁`. -/
theorem exists_mem_unstableSet_inter_stableSet_flow_mem_of_source
    (h : IsMorseSmalePair hX₀ hX₁) (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hpa : p ≠ a) (ha₁ : a₁ ∈ hX₀.flow.unstableSet p ∩ hX₀.flow.stableSet a)
    (hy : y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet r) {N₁ N : Set M}
    (hN₁ : N₁ ∈ 𝓝 a₁) (hN : N ∈ 𝓝 y) :
    ∃ w ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r, w ∈ N ∧ ∃ s : ℝ, hX₀.flow s w ∈ N₁ := by
  -- `W^s_{X₁}(r)` is flattened near `y` and, by the pair condition, transverse to `W^u_{X₀}(a)`.
  obtain ⟨L, φ, -, hyφ, hφ, hS⟩ :=
    hX₁.exists_isSliceChart_stableSet (hX₁.mfderiv_eq_zero_of_mem_stableSet hy.2) hy.2
  exact h₀.exists_mem_unstableSet_inter_flow_mem_of_isSliceChart hf₀ hpa ha₁ hy.1 hφ hS hyφ
    hy.2 (by rw [sup_comm]; exact h.span_mtangentConeAt_sup_eq_top hy) hN₁ hN

/-- **Configurations breaking at the source are limits.** Let `(X₀, X₁)` be a Morse–Smale pair
with `X₀` Morse–Smale. If a trajectory of `X₀` runs from `p` to a critical point `a ≠ p`, then
every point `y` of `W^u_{X₀}(a) ∩ W^s_{X₁}(r)`, `a` included, lies in the closure of
`W^u_{X₀}(p) ∩ W^s_{X₁}(r)`. -/
theorem mem_closure_unstableSet_inter_stableSet_of_source (h : IsMorseSmalePair hX₀ hX₁)
    (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hpa : p ≠ a)
    (ha₁ : a₁ ∈ hX₀.flow.unstableSet p ∩ hX₀.flow.stableSet a)
    (hy : y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet r) :
    y ∈ closure (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r) := by
  refine mem_closure_iff_nhds.2 fun N hN ↦ ?_
  obtain ⟨w, hw, hwN, -⟩ :=
    h.exists_mem_unstableSet_inter_stableSet_flow_mem_of_source h₀ hf₀ hpa ha₁ hy
      Filter.univ_mem hN
  exact ⟨w, hwN, hw⟩

/-- **Gluing at the target.** Let `(X₀, X₁)` be a Morse–Smale pair with `X₁` Morse–Smale, `a₂` a
point of a trajectory of `X₁` from a critical point `b` to `r ≠ b`, and `y` a point of
`W^u_{X₀}(p) ∩ W^s_{X₁}(b)`, possibly `b` itself. For all neighbourhoods `N₂` of `a₂` and `N` of
`y`, some point of `W^u_{X₀}(p) ∩ W^s_{X₁}(r)` lies in `N` and its `X₁`-orbit passes through
`N₂`. -/
theorem exists_mem_unstableSet_inter_stableSet_flow_mem_of_target
    (h : IsMorseSmalePair hX₀ hX₁) (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hbr : b ≠ r)
    (ha₂ : a₂ ∈ hX₁.flow.unstableSet b ∩ hX₁.flow.stableSet r)
    (hy : y ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet b) {N₂ N : Set M}
    (hN₂ : N₂ ∈ 𝓝 a₂) (hN : N ∈ 𝓝 y) :
    ∃ w ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r, w ∈ N ∧ ∃ s : ℝ, hX₁.flow s w ∈ N₂ := by
  -- Reversing both fields, the configuration breaks at the source for the pair `(-X₁, -X₀)`.
  have hrev := (h.neg hf₀ hf₁).exists_mem_unstableSet_inter_stableSet_flow_mem_of_source
    (h₁.neg hf₁) hf₁.neg hbr.symm (a₁ := a₂) (y := y) (r := p)
    (hX₁.unstableSet_inter_stableSet_eq_neg hX₁ hf₁ hf₁ b r ▸ ha₂)
    (hX₀.unstableSet_inter_stableSet_eq_neg hX₁ hf₀ hf₁ p b ▸ hy) hN₂ hN
  rw [← hX₀.unstableSet_inter_stableSet_eq_neg hX₁ hf₀ hf₁] at hrev
  obtain ⟨w, hw, hwN, s, hs⟩ := hrev
  exact ⟨w, hw, hwN, -s, by rwa [hX₁.neg_flow hf₁, Flow.reverse_apply] at hs⟩

/-- **Configurations breaking at the target are limits.** Let `(X₀, X₁)` be a Morse–Smale pair
with `X₁` Morse–Smale. If a trajectory of `X₁` runs from a critical point `b` to `r ≠ b`, then
every point `y` of `W^u_{X₀}(p) ∩ W^s_{X₁}(b)`, `b` included, lies in the closure of
`W^u_{X₀}(p) ∩ W^s_{X₁}(r)`. -/
theorem mem_closure_unstableSet_inter_stableSet_of_target (h : IsMorseSmalePair hX₀ hX₁)
    (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hbr : b ≠ r)
    (ha₂ : a₂ ∈ hX₁.flow.unstableSet b ∩ hX₁.flow.stableSet r)
    (hy : y ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet b) :
    y ∈ closure (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r) := by
  refine mem_closure_iff_nhds.2 fun N hN ↦ ?_
  obtain ⟨w, hw, hwN, -⟩ :=
    h.exists_mem_unstableSet_inter_stableSet_flow_mem_of_target h₁ hf₀ hf₁ hbr ha₂ hy
      Filter.univ_mem hN
  exact ⟨w, hwN, hw⟩

/-- **Half-open charts at the source.** Let `(X₀, X₁)` be a Morse–Smale pair with `X₀`
Morse–Smale, `a₁` a point of a trajectory of `X₀` from `p` to a critical point `a` with
`ind p = ind a + 1`, and `y ≠ a` a point of `W^u_{X₀}(a) ∩ W^s_{X₁}(r)`, where `ind a = ind r`.
Record a point `x` of the one-dimensional intersection `W^u_{X₀}(p) ∩ W^s_{X₁}(r)` by the pair
`(w, x)`, where `w` is the point of its `X₀`-orbit on the level of `a₁`, and the configuration
breaking at the source by `(a₁, y)`. Then `(a₁, y)` has a neighbourhood among these pairs
homeomorphic to a half-open interval `[0, δ)`, with `(a₁, y)` corresponding to `0`. -/
theorem exists_homeomorph_Ico_of_source (h : IsMorseSmalePair hX₀ hX₁) (h₀ : hX₀.IsMorseSmale)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hpa : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ a + 1)
    (har : manifoldMorseIndex 𝓘(ℝ, E) f₀ a = manifoldMorseIndex 𝓘(ℝ, E) f₁ r)
    (ha₁ : a₁ ∈ hX₀.flow.unstableSet p ∩ hX₀.flow.stableSet a)
    (hy : y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet r) (hya : y ≠ a) :
    ∃ (N : Set (M × M)) (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hδ⟩ : M × M) = (a₁, y) ∧
      N ⊆ insert (a₁, y) {w | w.2 ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r ∧
        f₀ w.1 = f₀ a₁ ∧ ∃ t, hX₀.flow t w.1 = w.2} ∧
      N ∈ 𝓝[insert (a₁, y) {w | w.2 ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r ∧
        f₀ w.1 = f₀ a₁ ∧ ∃ t, hX₀.flow t w.1 = w.2}] (a₁, y) := by
  -- `W^s_{X₁}(r)` is flattened near `y`, of dimension `n - ind a`, and transverse to `W^u_{X₀}(a)`.
  obtain ⟨L, φ, hL, hyφ, hφ, hS⟩ :=
    hX₁.exists_isSliceChart_stableSet (hX₁.mfderiv_eq_zero_of_mem_stableSet hy.2) hy.2
  exact h₀.exists_homeomorph_Ico_of_isSliceChart hf₀ hpa ha₁ hy.1 hya hφ hS hyφ hy.2
    (by rw [har]; exact hL) (by rw [sup_comm]; exact h.span_mtangentConeAt_sup_eq_top hy)

/-- **Half-open charts at the target.** Let `(X₀, X₁)` be a Morse–Smale pair with `X₁`
Morse–Smale, `a₂` a point of a trajectory of `X₁` from a critical point `b` to `r` with
`ind b = ind r + 1`, and `y ≠ b` a point of `W^u_{X₀}(p) ∩ W^s_{X₁}(b)`, where `ind p = ind b`.
Record a point `x` of the one-dimensional intersection `W^u_{X₀}(p) ∩ W^s_{X₁}(r)` by the pair
`(w, x)`, where `w` is the point of its `X₁`-orbit on the level of `a₂`, and the configuration
breaking at the target by `(a₂, y)`. Then `(a₂, y)` has a neighbourhood among these pairs
homeomorphic to a half-open interval `[0, δ)`, with `(a₂, y)` corresponding to `0`. -/
theorem exists_homeomorph_Ico_of_target (h : IsMorseSmalePair hX₀ hX₁) (h₁ : hX₁.IsMorseSmale)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (hbr : manifoldMorseIndex 𝓘(ℝ, E) f₁ b = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1)
    (hpb : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ b)
    (ha₂ : a₂ ∈ hX₁.flow.unstableSet b ∩ hX₁.flow.stableSet r)
    (hy : y ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet b) (hyb : y ≠ b) :
    ∃ (N : Set (M × M)) (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hδ⟩ : M × M) = (a₂, y) ∧
      N ⊆ insert (a₂, y) {w | w.2 ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r ∧
        f₁ w.1 = f₁ a₂ ∧ ∃ t, hX₁.flow t w.1 = w.2} ∧
      N ∈ 𝓝[insert (a₂, y) {w | w.2 ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r ∧
        f₁ w.1 = f₁ a₂ ∧ ∃ t, hX₁.flow t w.1 = w.2}] (a₂, y) := by
  -- Reversing both fields, the configuration breaks at the source for the pair `(-X₁, -X₀)`,
  -- with the Morse indices `n - ind` of `-f₁` and `-f₀`.
  have hb := hf₁.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (hX₁.mfderiv_eq_zero_of_mem_stableSet hy.2)
  have hr := hf₁.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (hX₁.mfderiv_eq_zero_of_mem_stableSet ha₂.2)
  have hp := hf₀.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (hX₀.mfderiv_eq_zero_of_mem_unstableSet hy.1)
  have hset : {w : M × M | w.2 ∈ (hX₁.neg hf₁).flow.unstableSet r ∩
      (hX₀.neg hf₀).flow.stableSet p ∧ (-f₁) w.1 = (-f₁) a₂ ∧
        ∃ t, (hX₁.neg hf₁).flow t w.1 = w.2} =
      {w | w.2 ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r ∧
        f₁ w.1 = f₁ a₂ ∧ ∃ t, hX₁.flow t w.1 = w.2} := by
    ext w
    rw [mem_ofPred_eq, mem_ofPred_eq, ← hX₀.unstableSet_inter_stableSet_eq_neg hX₁ hf₀ hf₁,
      hX₁.neg_flow hf₁, Pi.neg_apply, Pi.neg_apply, neg_inj]
    refine and_congr_right fun _ ↦ and_congr_right fun _ ↦
      ⟨fun ⟨t, ht⟩ ↦ ⟨-t, ?_⟩, fun ⟨t, ht⟩ ↦ ⟨-t, ?_⟩⟩
    · rwa [Flow.reverse_apply] at ht
    · rwa [Flow.reverse_apply, neg_neg]
  rw [← hset]
  exact (h.neg hf₀ hf₁).exists_homeomorph_Ico_of_source (h₁.neg hf₁) hf₁.neg
    (hb.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hr hbr)
    (by have := hb.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
        have := hp.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
        omega)
    (hX₁.unstableSet_inter_stableSet_eq_neg hX₁ hf₁ hf₁ b r ▸ ha₂)
    (hX₀.unstableSet_inter_stableSet_eq_neg hX₁ hf₀ hf₁ p b ▸ hy) hyb

end IsMorseSmalePair

end IsAdaptedPseudoGradient

end TauCeti
