/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Embedding
import TauCeti.Geometry.Manifold.Morse.Stable.Frame
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
* `TauCeti.IsAdaptedPseudoGradient.unstableSet_inter_stableSet_eq_orbit`: at a critical point of
  index `n - 1`, the trajectories from `p` form a single orbit when one of the two trajectories
  into the critical point comes from `p` and the other does not.
* `TauCeti.IsAdaptedPseudoGradient.eventually_unstableSet_eq_insert_union_orbit`: at a critical
  point of index `1` at which `X` is linear in a Morse chart, the two orbits are those of the
  points `y_c` and `y_{-c}` of the chart with coordinates `c` and `-c` in the direction of negative
  weight, for every small `c ≠ 0`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1 (stable and unstable manifolds) and Chapter 4 (the Morse complex).
-/

public section

open Filter Function Module Set Topology
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
theorem exists_stableSet_eq_insert_union_orbit
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x + 1 = finrank ℝ E) :
    ∃ y₁ y₂ : M, y₁ ≠ x ∧ y₂ ≠ x ∧ Disjoint (hX.flow.orbit y₁) (hX.flow.orbit y₂) ∧
      hX.flow.stableSet x = insert x (hX.flow.orbit y₁ ∪ hX.flow.orbit y₂) := by
  obtain ⟨φ, δ, hemb, hrange, h0, -, hsmul⟩ := hX.exists_stableParam hx
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
    (mfderiv_neg_eq_zero_iff.2 hx) (by omega)
  rw [← hX.unstableSet_eq_stableSet_neg hf, hX.neg_flow hf, Flow.orbit_reverse,
    Flow.orbit_reverse] at hW
  rw [hX.neg_flow hf, Flow.orbit_reverse, Flow.orbit_reverse] at hdisj
  exact ⟨y₁, y₂, h₁, h₂, hdisj, hW⟩

/-- **A single trajectory into a critical point of index `n - 1`.** Let `x` be a critical point of
index `n - 1`, so that `W^s(x) - {x}` consists of two trajectories. If a point `y` of `W^s(x)`
lies in the unstable manifold of `p` and a point `z ≠ x` of `W^s(x)` does not, then the
trajectories from `p` to `x` form the single orbit of `y`: membership in `W^u(p)` is constant along
each of the two trajectories, and `z` lies on the other one. When `y = x`, the point `p` is `x`
and both sides are `{x}`. -/
theorem unstableSet_inter_stableSet_eq_orbit (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x + 1 = finrank ℝ E) {p y z : M}
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet x) (hz : z ∈ hX.flow.stableSet x)
    (hzx : z ≠ x) (hzp : z ∉ hX.flow.unstableSet p) :
    hX.flow.unstableSet p ∩ hX.flow.stableSet x = hX.flow.orbit y := by
  obtain ⟨y₁, y₂, -, -, -, hW⟩ := hX.exists_stableSet_eq_insert_union_orbit hx hind
  have horbit {a b : M} (ha : a ∈ hX.flow.orbit b) :
      a ∈ hX.flow.unstableSet p ↔ b ∈ hX.flow.unstableSet p := by
    obtain ⟨s, rfl⟩ := ha
    exact Flow.apply_mem_unstableSet_iff _ s
  have hside {a : M} (ha : a ∈ hX.flow.stableSet x) (hax : a ≠ x) :
      a ∈ hX.flow.orbit y₁ ∨ a ∈ hX.flow.orbit y₂ := by
    rw [hW] at ha
    exact (mem_insert_iff.1 ha).resolve_left hax
  -- Not both trajectories come from `p`, since the one through `z` does not.
  have hboth (h₁ : y₁ ∈ hX.flow.unstableSet p) (h₂ : y₂ ∈ hX.flow.unstableSet p) : False := by
    rcases hside hz hzx with h | h
    · exact hzp ((horbit h).2 h₁)
    · exact hzp ((horbit h).2 h₂)
  refine Subset.antisymm (fun w hw ↦ ?_) fun w ⟨s, hs⟩ ↦
    hs ▸ Flow.isInvariant_unstableSet_inter_stableSet _ p x s hy
  -- If `y = x`, then `p = x` and `w ∈ W^u(x) ∩ W^s(x)` is `x`.
  rcases eq_or_ne y x with rfl | hyx
  · obtain rfl := hX.eq_of_mem_unstableSet_of_mfderiv_eq_zero hx hy.1
    rw [hX.eq_of_mem_unstableSet_inter_stableSet hw]
    exact Flow.mem_orbit_self _ _
  -- Otherwise `x ∉ W^u(p)`, since `y ∈ W^u(x) ∩ W^s(x)` would be `x`.
  have hwx : w ≠ x := by
    rintro rfl
    obtain rfl := hX.eq_of_mem_unstableSet_of_mfderiv_eq_zero hx hw.1
    exact hyx (hX.eq_of_mem_unstableSet_inter_stableSet hy)
  obtain ⟨b, hwb, hyb⟩ : ∃ b, w ∈ hX.flow.orbit b ∧ y ∈ hX.flow.orbit b := by
    rcases hside hw.2 hwx with hw' | hw' <;> rcases hside hy.2 hyx with hy' | hy'
    · exact ⟨y₁, hw', hy'⟩
    · exact (hboth ((horbit hw').1 hw.1) ((horbit hy').1 hy.1)).elim
    · exact (hboth ((horbit hy').1 hy.1) ((horbit hw').1 hw.1)).elim
    · exact ⟨y₂, hw', hy'⟩
  rwa [(Flow.orbit_eq_iff _).2 hyb]

section UnstableAxis

variable {hX} {φ : MorseChart E f x} (hφ : ∀ y ∈ φ.toChart.source,
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
include hφ

/-- On the unstable axis, the points with opposite coordinates `c` and `-c ≠ 0` lie on different
orbits: the unstable frame of `c` is the velocity at the first point and its opposite at the
second, while the flow carries the frame and the velocity at the first point to positive multiples
of those at the second. -/
private theorem notMem_orbit_toChart_symm_negativeExtend_neg (hf : IsMorse 𝓘(ℝ, E) f)
    {c : {i // φ.weight i < 0} → ℝ} (hc : c ≠ 0)
    (h₁ : φ.negativeExtend c ∈ φ.toChart.target ∧
      φ.toChart.symm (φ.negativeExtend c) ∈ hX.flow.unstableSet x ∧
      hX.unstableFrame φ (φ.toChart.symm (φ.negativeExtend c)) c =
        X (φ.toChart.symm (φ.negativeExtend c)))
    (h₂ : φ.negativeExtend (-c) ∈ φ.toChart.target ∧
      φ.toChart.symm (φ.negativeExtend (-c)) ∈ hX.flow.unstableSet x ∧
      hX.unstableFrame φ (φ.toChart.symm (φ.negativeExtend (-c))) (-c) =
        X (φ.toChart.symm (φ.negativeExtend (-c)))) :
    φ.toChart.symm (φ.negativeExtend (-c)) ∉
      hX.flow.orbit (φ.toChart.symm (φ.negativeExtend c)) := by
  set y₁ := φ.toChart.symm (φ.negativeExtend c)
  set y₂ := φ.toChart.symm (φ.negativeExtend (-c))
  intro h
  obtain ⟨t, ht⟩ := (hX.flow.mem_orbit_iff).1 h
  obtain ⟨T, hT⟩ := (hX.eventually_mem_linearBackwardTimes hφ hf h₁.2.1).exists
  -- The frame at `y₂` on `c` is `e^{-t}` times the velocity, and also minus the velocity.
  have hflow := unstableFrame_flow hφ hT t c
  rw [h₁.2.2, hX.mfderiv_flow_apply_self, ht] at hflow
  have hneg : hX.unstableFrame φ y₂ c = -X y₂ := by
    rw [← h₂.2.2, map_neg, neg_neg]
  rw [hneg, eq_comm, ← sub_eq_zero, sub_neg_eq_add] at hflow
  have hsum : (Real.exp (-t) + 1) • X y₂ = 0 := by rwa [add_smul, one_smul]
  have hX0 : X y₂ = 0 := (smul_eq_zero.1 hsum).resolve_left (by positivity)
  -- So `y₂` is a rest point on the unstable manifold of `x`, hence `x` itself, which is not on
  -- the axis away from `0`.
  have hcrit := hX.eq_zero_iff.1 hX0
  exact φ.toChart_symm_negativeExtend_ne (neg_ne_zero.2 hc) h₂.1
    (hX.eq_of_mem_unstableSet_of_mfderiv_eq_zero hcrit h₂.2.1)

/-- **The two trajectories leaving a critical point of index one.** Let `X` be linear in the Morse
chart `φ` at a critical point `x` of index `1`. For every small `c ≠ 0` in the space of coordinates
of negative weight, which is a line, the points `y_c` and `y_{-c}` of the chart with coordinates
`c` and `-c` in the direction of negative weight and `0` elsewhere lie on different orbits, and the
unstable manifold of `x` is `x` together with these two orbits. -/
theorem eventually_unstableSet_eq_insert_union_orbit (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : manifoldMorseIndex 𝓘(ℝ, E) f x = 1) :
    ∀ᶠ c in 𝓝[≠] (0 : {i // φ.weight i < 0} → ℝ),
      φ.toChart.symm (φ.negativeExtend (-c)) ∉
          hX.flow.orbit (φ.toChart.symm (φ.negativeExtend c)) ∧
        hX.flow.unstableSet x = insert x (hX.flow.orbit (φ.toChart.symm (φ.negativeExtend c)) ∪
          hX.flow.orbit (φ.toChart.symm (φ.negativeExtend (-c)))) := by
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_mem_unstableSet_and_unstableFrame_eq_and_neg (hX := hX) hφ),
    self_mem_nhdsWithin] with c ⟨h₁, h₂⟩ hc
  set y₁ := φ.toChart.symm (φ.negativeExtend c)
  set y₂ := φ.toChart.symm (φ.negativeExtend (-c))
  have hc : c ≠ 0 := mem_compl_singleton_iff.1 hc
  have hsep := notMem_orbit_toChart_symm_negativeExtend_neg hφ hf hc h₁ h₂
  refine ⟨hsep, ?_⟩
  obtain ⟨u₁, u₂, -, -, -, hW⟩ := hX.exists_unstableSet_eq_insert_union_orbit hf
    (hX.mfderiv_eq_zero_of_mem_unstableSet h₁.2.1) hx
  have hy₁ : y₁ ≠ x := φ.toChart_symm_negativeExtend_ne hc h₁.1
  have hy₂ : y₂ ≠ x := φ.toChart_symm_negativeExtend_ne (neg_ne_zero.2 hc) h₂.1
  have hmem₁ := h₁.2.1
  have hmem₂ := h₂.2.1
  rw [hW] at hmem₁ hmem₂
  -- Neither point is `x`, and they lie on different orbits, so each of `u₁` and `u₂` shares its
  -- orbit with exactly one of them.
  rcases hmem₁ with h | h | h
  · exact absurd h hy₁
  · rcases hmem₂ with h' | h' | h'
    · exact absurd h' hy₂
    · exact (hsep (by rw [hX.flow.orbit_eq_iff.2 h]; exact h')).elim
    · rw [hW, hX.flow.orbit_eq_iff.2 h, hX.flow.orbit_eq_iff.2 h']
  · rcases hmem₂ with h' | h' | h'
    · exact absurd h' hy₂
    · rw [hW, hX.flow.orbit_eq_iff.2 h, hX.flow.orbit_eq_iff.2 h', union_comm]
    · exact (hsep (by rw [hX.flow.orbit_eq_iff.2 h]; exact h')).elim

end UnstableAxis

end IsAdaptedPseudoGradient

end TauCeti
