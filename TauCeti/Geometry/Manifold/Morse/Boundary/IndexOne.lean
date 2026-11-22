/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Integral
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedAugmentation
import TauCeti.Geometry.Manifold.Morse.Stable.OneDimensional

/-!
# The integral Morse boundary of a critical point of index one

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient adapted
to `f`, and `p` a critical point of index `1`. Its unstable manifold `W^u(p)` is a line through
`p`, so `W^u(p) - {p}` consists of two trajectories, one leaving `p` in each direction. Suppose
that `X` is linear in a Morse chart at `p`, and let `q` be a critical point of index `0`. The two
trajectories carry opposite signs for the integral Morse complex
(`TauCeti.IsAdaptedPseudoGradient.trajectorySign_eq_neg_of_notMem_orbit`, in
`TauCeti.Geometry.Manifold.Morse.Boundary.SignedAugmentation`), so this file shows that, if both
end at `q`, their contributions to the integral boundary cancel, and with a single minimum every
critical point of index `1` is an integral cycle. This is the cancellation behind the integral
Morse complexes of the sphere with two maxima, of the torus and of the real projective plane in
degree `1`.

The two trajectories are seen in a Morse chart `φ` at `p` in which `X` is linear. Its space `V` of
coordinates of negative weight is a line, oriented by the orientation of `W^u(p)` at `p`. For
small `c ∈ V`, the point `y_c` of the chart with coordinates `c` in the directions of negative
weight and `0` elsewhere lies on `W^u(p)`, and the unstable frame at `y_c` sends `c` to the
velocity `X y_c`
(`TauCeti.IsAdaptedPseudoGradient.eventually_mem_unstableSet_and_unstableFrame_eq`, in
`TauCeti.Geometry.Manifold.Morse.Stable.Frame`): in the chart
both vectors have coordinates `c` in the directions of negative weight, along which the linear
field is the identity. So at `y_c` the vector `c` points along the flow, while at `y_{-c}` it points
against it. For `c ≠ 0` the points `y_c` and `y_{-c}` therefore lie on different orbits, which are
the two trajectories leaving `p`
(`TauCeti.IsAdaptedPseudoGradient.eventually_unstableSet_eq_insert_union_orbit`, in
`TauCeti.Geometry.Manifold.Morse.Stable.OneDimensional`).

If both trajectories end at a critical point `q` of index `0`, the middle-level slice of the
trajectories from `p` to `q` consists of one point on each of them, with opposite signs. Hence the
signed count of the trajectories from `p` to `q` vanishes as soon as both trajectories leaving `p`
end at `q` (`TauCeti.IsAdaptedPseudoGradient.signedTrajectoryCount_eq_zero_of_mem_stableSet`).
Under the Morse–Smale condition every trajectory leaving `p` ends at a critical point of index `0`,
so when `f` has a single such point `m`, no integral boundary has a component along `m`, and the
integral boundary of every critical point of index `1` is zero (in the namespace
`TauCeti.IsAdaptedPseudoGradient`,
`IsMorseSmale.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero` in
`TauCeti.Geometry.Manifold.Morse.Boundary.SignedAugmentation`, and
`IsMorseSmale.signedMorseBoundary_single_eq_zero_of_unique_index_zero`). The mod-two counterpart
is `IsMorseSmale.morseBoundaryCoeff_eq_zero_of_unique_index_zero`, where the two trajectories
cancel because they are two.

The dual statement for a unique maximum does not hold over `ℤ`: on the real projective plane the
two trajectories from the maximum to the saddle carry the same sign. Whether they do depends on
the orientability of `M` along them, which the local argument here does not see.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `trajectorySign_eq_neg_of_mem_stableSet`: two different trajectories from a critical point of
  index `1` to the same critical point of index `0` carry opposite signs.
* `signedTrajectoryCount_eq_zero_of_mem_stableSet`: if both trajectories leaving a critical point
  of index `1` end at `q`, the signed count of the trajectories to `q` is zero.
* `IsMorseSmale.signedMorseBoundary_single_eq_zero_of_unique_index_zero`: with a unique critical
  point of index `0`, the integral boundary of every critical point of index `1` vanishes.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations, and the computation for the sphere with
  two maxima, where the two flow lines from the saddle to the minimum carry opposite signs).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients, and its computation for the real
  projective plane).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {p : M} {φ : MorseChart E f p}

/-- At a critical point `p` of index `1` at which `X` is linear in `φ`, some `c ≠ 0` gives points
`y_c` and `y_{-c}` of the unstable axis, different from `p` and on different orbits, at which the
unstable frames of `c` and `-c` are the velocity, and the unstable manifold of `p` is `p` together
with the orbits of these two points. -/
private theorem exists_axis_point
    (hφ : ∀ y ∈ φ.toChart.source,
      φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
        fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    (hf : IsMorse 𝓘(ℝ, E) f) (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1) :
    ∃ c : {i // φ.weight i < 0} → ℝ, c ≠ 0 ∧
      (φ.toChart.symm (φ.negativeExtend c) ∈ hX.flow.unstableSet p ∧
        hX.unstableFrame φ (φ.toChart.symm (φ.negativeExtend c)) c =
          X (φ.toChart.symm (φ.negativeExtend c))) ∧
      (φ.toChart.symm (φ.negativeExtend (-c)) ∈ hX.flow.unstableSet p ∧
        hX.unstableFrame φ (φ.toChart.symm (φ.negativeExtend (-c))) (-c) =
          X (φ.toChart.symm (φ.negativeExtend (-c)))) ∧
      φ.toChart.symm (φ.negativeExtend c) ≠ p ∧ φ.toChart.symm (φ.negativeExtend (-c)) ≠ p ∧
      φ.toChart.symm (φ.negativeExtend (-c)) ∉
        hX.flow.orbit (φ.toChart.symm (φ.negativeExtend c)) ∧
      hX.flow.unstableSet p = insert p (hX.flow.orbit (φ.toChart.symm (φ.negativeExtend c)) ∪
        hX.flow.orbit (φ.toChart.symm (φ.negativeExtend (-c)))) := by
  have : Nontrivial ({i // φ.weight i < 0} → ℝ) :=
    Module.nontrivial_of_finrank_eq_succ (by rw [φ.finrank_negativeWeight_fun, hp])
  obtain ⟨c, ⟨⟨hT₁, h₁⟩, hT₂, h₂⟩, hW, hc⟩ := ((eventually_nhdsWithin_of_eventually_nhds
    (eventually_mem_unstableSet_and_unstableFrame_eq_and_neg (hX := hX) hφ)).and
      ((eventually_unstableSet_eq_insert_union_orbit hφ hf hp).and self_mem_nhdsWithin)).exists
  have hc : c ≠ 0 := mem_compl_singleton_iff.1 hc
  exact ⟨c, hc, h₁, h₂, φ.toChart_symm_negativeExtend_ne hc hT₁,
    φ.toChart_symm_negativeExtend_ne (neg_ne_zero.2 hc) hT₂, hW⟩

/-- If the unstable manifold of `p` is `p` together with the orbits of two points `a` and `b` of
trajectories from `p` to `q`, then the middle-level slice of the trajectories from `p` to `q`
consists of one point on each of these orbits: for `-X` these are the trajectories from `q` to `p`,
read off the decomposition of the stable set of `p` by
`morseTrajectorySlice_eq_image_of_stableSet_subset`. -/
private theorem exists_morseTrajectorySlice_eq_pair (hf : IsMorse 𝓘(ℝ, E) f) {q a b : M}
    (hpq : p ≠ q) (ha : a ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hb : b ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hU : hX.flow.unstableSet p = insert p (hX.flow.orbit a ∪ hX.flow.orbit b)) :
    ∃ za ∈ hX.flow.orbit a, ∃ zb ∈ hX.flow.orbit b,
      hX.morseTrajectorySlice p q = {za, zb} := by
  set hXn := hX.neg hf
  have horbit (y : M) : hXn.flow.orbit y = hX.flow.orbit y := by
    rw [hX.neg_flow hf, Flow.orbit_reverse]
  have hneg {y : M} (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
      y ∈ hXn.flow.unstableSet q ∩ hXn.flow.stableSet p := by
    rwa [hX.neg_flow hf, Flow.unstableSet_reverse, Flow.stableSet_reverse, inter_comm]
  -- Each of the two trajectories crosses the middle level once.
  obtain ⟨τa, hτa, -⟩ :=
    hXn.existsUnique_flow_eq_midpoint_of_mem_unstableSet_inter_stableSet hpq.symm (hneg ha)
  obtain ⟨τb, hτb, -⟩ :=
    hXn.existsUnique_flow_eq_midpoint_of_mem_unstableSet_inter_stableSet hpq.symm (hneg hb)
  refine ⟨hXn.flow τa a, horbit a ▸ Flow.mem_orbit _ _ _, hXn.flow τb b,
    horbit b ▸ Flow.mem_orbit _ _ _, ?_⟩
  have hW : hXn.flow.stableSet p ⊆
      insert p (⋃ i : Bool, hXn.flow.orbit (bif i then a else b)) := by
    rw [← hX.unstableSet_eq_stableSet_neg hf, hU, union_eq_iUnion]
    refine insert_subset_insert (iUnion_mono fun i ↦ ?_)
    cases i <;> simp [horbit]
  rw [← hX.neg_morseTrajectorySlice hf, hXn.morseTrajectorySlice_eq_image_of_stableSet_subset
    (a := fun _ ↦ q) (τ := fun i ↦ bif i then τa else τb) hpq.symm hW
    (fun i ↦ by cases i <;> simp [hneg ha, hneg hb]) (fun i ↦ by cases i <;> simp [hτa, hτb])]
  -- Both orbits start at `q` for `-X`, so the image is the pair of crossings.
  ext z
  simp [or_comm]

section Sign

variable {q : M} {φq : MorseChart E f q}
  {op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))}
  {oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q))}
  {hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1}

variable (hφ : ∀ y ∈ φ.toChart.source,
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
include hφ

/-- Two different trajectories from a critical point `p` of index `1` to the same critical point
`q` of index `0` carry opposite signs, for every choice of the orientations at `p` and `q`: this is
`TauCeti.IsAdaptedPseudoGradient.trajectorySign_eq_neg_of_notMem_orbit` when `oq` is the positive
orientation of the zero space at `q`, and both signs change when `oq` is reversed. -/
theorem trajectorySign_eq_neg_of_mem_stableSet (hf : IsMorse 𝓘(ℝ, E) f)
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1) {y₁ y₂ : M}
    (hy₁ : y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hy₂ : y₂ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) (h : y₂ ∉ hX.flow.orbit y₁) :
    hX.trajectorySign φ φq op oq hpq y₂ = -hX.trajectorySign φ φq op oq hpq y₁ := by
  have hne : p ≠ q := ne_of_apply_ne (manifoldMorseIndex 𝓘(ℝ, E) f) (by omega)
  have key := trajectorySign_eq_neg_of_notMem_orbit (hX := hX) (φq₁ := φq) (φq₂ := φq) hf hφ op
    hp hpq hpq hy₁.1 hy₂.1
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hy₁)
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hy₂) h
  have hcard : Nat.card (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)) =
      Module.finrank ℝ ({i // φq.weight i < 0} → ℝ) := by
    rw [Nat.card_fin, φq.finrank_negativeWeight_fun]
  rcases oq.eq_or_eq_neg (Module.finBasisOfFinrankEq ℝ _ φq.finrank_negativeWeight_fun).orientation
    hcard with rfl | rfl
  · exact key
  · rw [trajectorySign_neg_right, trajectorySign_neg_right, key]

/-- **The trajectories leaving a critical point of index one cancel.** Let `X` be a
pseudo-gradient adapted to a Morse function `f`, linear in a Morse chart at a critical point `p` of
index `1`, and let `q` be a critical point of index `0`. If both trajectories leaving `p` end at
`q`, then the signed count of the trajectories from `p` to `q` is zero, for every choice of the
orientations at `p` and `q`. -/
theorem signedTrajectoryCount_eq_zero_of_mem_stableSet (hf : IsMorse 𝓘(ℝ, E) f)
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1)
    (hW : ∀ y ∈ hX.flow.unstableSet p, y ≠ p → y ∈ hX.flow.stableSet q) :
    hX.signedTrajectoryCount φ φq op oq hpq = 0 := by
  have hne : p ≠ q := ne_of_apply_ne (manifoldMorseIndex 𝓘(ℝ, E) f) (by omega)
  obtain ⟨c, -, h₁, h₂, hp₁, hp₂, hsep, hU⟩ := exists_axis_point (hX := hX) hφ hf hp
  set a := φ.toChart.symm (φ.negativeExtend c)
  set b := φ.toChart.symm (φ.negativeExtend (-c))
  have ha : a ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q := ⟨h₁.1, hW a h₁.1 hp₁⟩
  have hb : b ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q := ⟨h₂.1, hW b h₂.1 hp₂⟩
  -- The slice consists of one crossing on each of the two orbits, which carry opposite signs.
  obtain ⟨za, hza, zb, hzb, hslice⟩ := exists_morseTrajectorySlice_eq_pair hf hne ha hb hU
  have hmem {z : M} (hz : z ∈ hX.morseTrajectorySlice p q) :
      z ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    ⟨(hX.mem_morseTrajectorySlice.1 hz).1, (hX.mem_morseTrajectorySlice.1 hz).2.1⟩
  have hza' := hmem (hslice ▸ mem_insert za {zb})
  have hzb' := hmem (hslice ▸ mem_insert_of_mem za (mem_singleton zb))
  have hsep' : zb ∉ hX.flow.orbit za := by
    rwa [← hX.flow.orbit_eq_iff, hX.flow.orbit_eq_iff.2 hza, hX.flow.orbit_eq_iff.2 hzb,
      hX.flow.orbit_eq_iff]
  have hne' : za ≠ zb := fun h ↦ hsep' (h ▸ hX.flow.mem_orbit_self za)
  rw [signedTrajectoryCount_def, hslice, finsum_mem_pair hne',
    trajectorySign_eq_neg_of_mem_stableSet hφ hf hp hza' hzb' hsep', add_neg_cancel]

end Sign

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  (𝔬 : MorseOrientation f X)
include h hf

/-- **With a unique minimum, critical points of index one are integral cycles.** Under the
Morse–Smale condition, if `f` has at most one critical point of index `0`, then the integral Morse
boundary of every critical point of index `1` vanishes, with coefficients in any ring and whatever
the orientations. -/
theorem signedMorseBoundary_single_eq_zero_of_unique_index_zero {R : Type*} [Ring R]
    {p : criticalPoints 𝓘(ℝ, E) f} (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1)
    (hmin : {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x = 0}.Subsingleton)
    (a : R) : hX.signedMorseBoundary 𝔬 hf R (Finsupp.single p a) = 0 := by
  ext q
  rw [signedMorseBoundary_single_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f q = 0
  · have hqm (y : M) (hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0)
        (hy0 : manifoldMorseIndex 𝓘(ℝ, E) f y = 0) : y = q :=
      hmin ⟨hy, hy0⟩ ⟨mem_criticalPoints_iff_mfderiv_eq_zero.1 q.property, hq⟩
    rw [h.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero hf 𝔬 hqm p, Int.cast_zero,
      mul_zero]
  · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one (by omega), Int.cast_zero,
      mul_zero]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
