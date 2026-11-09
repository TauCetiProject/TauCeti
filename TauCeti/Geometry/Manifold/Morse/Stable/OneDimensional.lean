/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Embedding
import TauCeti.Dynamics.Flow.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# One-dimensional stable and unstable manifolds consist of two trajectories

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, and `X` a
pseudo-gradient field adapted to `f`. At a critical point `x` of index `1`, the unstable manifold
`W^u(x)` is an embedded line through `x`. Its two half-lines are single trajectories of the flow, so
`W^u(x)` is `x` together with two disjoint orbits. Likewise, at a critical point of index `n - 1`,
the stable manifold `W^s(x)` is `x` together with two disjoint orbits.

This is the geometric input for the Morse complex in its lowest and highest degrees. When `X` also
satisfies the Morse–Smale condition, each of the two orbits ends at, respectively starts from, a
critical point of index `0`, respectively `n`. So the boundary of an index-one critical point
counts the two ends of its unstable manifold, and every critical point of index `n - 1` is reached
by exactly two trajectories from the critical points of index `n`. The decompositions themselves
hold for every adapted pseudo-gradient.

The proof reads the stable manifold through its parametrization by the stable subspace `L` of a
Morse chart (`TauCeti.IsAdaptedPseudoGradient.exists_stableParam`), which carries the scaling
`v ↦ e^{-s} v` of `L` to the time-`s` map of the flow. When `L` is a line spanned by `v`, the
points `c • v` with `c > 0` form the orbit of the image of `v`, and those with `c < 0` the orbit of
the image of `-v`. The unstable side is the stable side for `-X`, adapted to `-f`.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.exists_stableSet_eq_insert_union_orbit`: at a critical point of
  index `n - 1`, the stable manifold is the critical point together with two disjoint orbits.
* `TauCeti.IsAdaptedPseudoGradient.exists_unstableSet_eq_insert_union_orbit`: at a critical point
  of index `1`, the unstable manifold is the critical point together with two disjoint orbits.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1 (stable and unstable manifolds) and Chapter 4 (the Morse complex).
-/

public section

open Function Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {x : M}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- **A one-dimensional stable manifold consists of two trajectories.** If the critical point `x`
has Morse index `n - 1`, its stable manifold `W^s(x)` is `x` together with the orbits of two points
`y₁` and `y₂` different from `x`, and these two orbits are disjoint. -/
theorem exists_stableSet_eq_insert_union_orbit (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x + 1 = finrank ℝ E) :
    ∃ y₁ y₂ : M, y₁ ≠ x ∧ y₂ ≠ x ∧ Disjoint (hX.flow.orbit y₁) (hX.flow.orbit y₂) ∧
      hX.flow.stableSet x = insert x (hX.flow.orbit y₁ ∪ hX.flow.orbit y₂) := by
  obtain ⟨φ, δ, hemb, hrange, h0, -, hsmul⟩ := hX.exists_stableParam hf hx
  set ι := hX.stableParam φ δ
  have hinj : Injective ι := hemb.isEmbedding.injective
  -- The stable subspace of the chart is a line, spanned by some `v ≠ 0`.
  have hdim : finrank ℝ φ.stableSubspace = 1 := by
    have := φ.finrank_stableSubspace_add_manifoldMorseIndex
    omega
  obtain ⟨v, hv, hspan⟩ := finrank_eq_one_iff'.1 hdim
  -- Scaling by `c > 0` moves along the orbit, by the time `-log c`.
  have horbit (w : φ.stableSubspace) {c : ℝ} (hc : 0 < c) :
      ι (c • w) = hX.flow (-Real.log c) (ι w) := by
    rw [← hsmul, neg_neg, Real.exp_log hc]
  refine ⟨ι v, ι (-v), fun h ↦ hv (hinj (h.trans h0.symm)),
    fun h ↦ hv (neg_eq_zero.1 (hinj (h.trans h0.symm))), ?_, ?_⟩
  · -- A common point would give `e^{-t} • (-v) = e^{-s} • v` with positive scalars.
    refine Set.disjoint_left.2 fun z hz₁ hz₂ ↦ ?_
    obtain ⟨s, rfl⟩ := (hX.flow.mem_orbit_iff).1 hz₁
    obtain ⟨t, ht⟩ := (hX.flow.mem_orbit_iff).1 hz₂
    rw [← hsmul, ← hsmul] at ht
    have heq := hinj ht
    rw [smul_neg] at heq
    have hzero : (Real.exp (-s) + Real.exp (-t)) • v = 0 := by
      rw [add_smul, ← heq, neg_add_cancel]
    exact hv ((smul_eq_zero.1 hzero).resolve_left (by positivity))
  · ext z
    rw [← hrange]
    simp only [mem_range, mem_insert_iff, mem_union, Flow.mem_orbit_iff]
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨c, rfl⟩ := hspan w
      rcases lt_trichotomy c 0 with hc | rfl | hc
      · exact Or.inr (Or.inr ⟨_, (horbit (-v) (neg_pos.2 hc)).symm.trans (by rw [neg_smul_neg])⟩)
      · exact Or.inl (by rw [zero_smul, h0])
      · exact Or.inr (Or.inl ⟨_, (horbit v hc).symm⟩)
    · rintro (rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩)
      · exact ⟨0, h0⟩
      · exact ⟨_, hsmul v t⟩
      · exact ⟨_, hsmul (-v) t⟩

/-- **A one-dimensional unstable manifold consists of two trajectories.** If the critical point `x`
has Morse index `1`, its unstable manifold `W^u(x)` is `x` together with the orbits of two points
`y₁` and `y₂` different from `x`, and these two orbits are disjoint. -/
theorem exists_unstableSet_eq_insert_union_orbit (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = 1) :
    ∃ y₁ y₂ : M, y₁ ≠ x ∧ y₂ ≠ x ∧ Disjoint (hX.flow.orbit y₁) (hX.flow.orbit y₂) ∧
      hX.flow.unstableSet x = insert x (hX.flow.orbit y₁ ∪ hX.flow.orbit y₂) := by
  -- The unstable manifold of `X` is the stable manifold of `-X`, at a point of index `n - 1`.
  have hsum := (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx
    ).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  obtain ⟨y₁, y₂, h₁, h₂, hdisj, hW⟩ := (hX.neg hf).exists_stableSet_eq_insert_union_orbit
    (hf.neg.contMDiff.mdifferentiable (by simp)) (mfderiv_neg_eq_zero_iff.2 hx) (by omega)
  rw [← hX.unstableSet_eq_stableSet_neg hf, hX.neg_flow hf, Flow.orbit_reverse,
    Flow.orbit_reverse] at hW
  rw [hX.neg_flow hf, Flow.orbit_reverse, Flow.orbit_reverse] at hdisj
  exact ⟨y₁, y₂, h₁, h₂, hdisj, hW⟩

end IsAdaptedPseudoGradient

end TauCeti
