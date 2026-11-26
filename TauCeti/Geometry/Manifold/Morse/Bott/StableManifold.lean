/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Flow
public import TauCeti.Geometry.Manifold.Morse.Bott.Chart.StableSubspace
public import TauCeti.Geometry.Manifold.LinearSlice
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Stable and unstable manifolds of a critical submanifold of a Morse–Bott function

Let `X` be a pseudo-gradient field adapted to `f` in the Morse–Bott sense
(`TauCeti.IsBottAdaptedPseudoGradient`) on a compact boundaryless manifold `M` of dimension `n`.
Its critical points are not isolated, but every orbit converges to a single critical point
(`TauCeti.IsBottAdaptedPseudoGradient.exists_tendsto_atTop`). This file shows that the points
flowing into a piece `S` of the critical set form a smooth submanifold `W^s(S)` of `M`, and that
the endpoint map `W^s(S) → S`, sending a point to the limit of its orbit, is smooth.

The pieces `S` are sets of critical points on a single level `c` of `f` which contain every critical
point near each of their points: the critical points in some open subset of `M` on the level `c`.
For a Morse–Bott function these are, for instance, the connected components of the critical set and
their unions at one level. The stable set of `S` is `⋃ p ∈ S, W^s(p)`.

**The local picture.** In a Morse–Bott chart `φ` centred at a point of `S`, in which `X` is the
linear field `z ↦ (-wᵢ zᵢ)ᵢ`, a point near the centre lies in `W^s(S)` exactly when its coordinates
of negative weight vanish, that is, when it lies in the stable subspace of the chart
(`TauCeti.IsBottAdaptedPseudoGradient.exists_forall_mem_biUnion_stableSet_iff`). One direction is
the energy barrier of `TauCeti.Geometry.Manifold.Morse.Bott.Flow`: an orbit converging to a point of
`S` never goes below the level `c`, so it starts on the stable slice. Conversely, a point of the
stable slice converges along the linear flow to its projection onto the coordinates of weight `0`,
a critical point near the centre, which lies in `S`.

**Slice charts.** A point `y` of `W^s(p)`, `p ∈ S`, reaches the neighbourhood of `p` on which this
picture holds at some time `T`. The Morse–Bott chart at `p` composed with the time-`T` map of the
flow is then a slice chart at `y` flattening `W^s(S)` onto the stable subspace of the chart, of
dimension `n - λ`, where `λ` is the Morse index at `p`
(`TauCeti.IsBottAdaptedPseudoGradient.exists_isSliceChart_biUnion_stableSet`). When the Morse
index is constant on `S`, these charts make `W^s(S)` an embedded submanifold of dimension `n - λ`
(`TauCeti.IsBottAdaptedPseudoGradient.exists_isManifold_isSmoothEmbedding_biUnion_stableSet`).
Near `y` the endpoint map `TauCeti.IsBottAdaptedPseudoGradient.stableEndpoint` is the projection
of the chart onto the coordinates of weight `0`, composed with the time-`T` map, so it is smooth
(`TauCeti.IsBottAdaptedPseudoGradient.exists_contMDiffOn_eqOn_stableEndpoint`).

The unstable side follows by reversing time: `-X` is adapted to `-f`, its flow is the reversed flow,
and the Morse index of `-f` at a point of `S` is the dimension of the positive normal bundle. So
`W^u(S)` has dimension `n` minus the Morse index of `-f`, that is `λ + dim S`.

These are the stable and unstable manifolds of the critical submanifolds that enter the trajectory
spaces of a Morse–Bott function, with the endpoint maps to the critical submanifolds. For a Morse
function the critical points are isolated, and the statements for `S = {x}` are those of
`TauCeti.Geometry.Manifold.Morse.Stable.Manifold`.

## Main results

In the namespace `TauCeti.IsBottAdaptedPseudoGradient`:

* `exists_forall_mem_biUnion_stableSet_iff`: near a point of `S`, `W^s(S)` is the stable slice of
  a Morse–Bott chart.
* `exists_isSliceChart_biUnion_stableSet`, `exists_isSliceChart_biUnion_unstableSet`: slice charts
  for `W^s(S)` and `W^u(S)`, onto subspaces of dimensions `n - λ` and `n - λ⁻`, where `λ⁻` is the
  Morse index of `-f`.
* `exists_isManifold_isSmoothEmbedding_biUnion_stableSet`,
  `exists_isManifold_isSmoothEmbedding_biUnion_unstableSet`: when the indices are constant on `S`,
  `W^s(S)` and `W^u(S)` are embedded submanifolds.
* `exists_contMDiffOn_eqOn_stableEndpoint`, `exists_contMDiffOn_eqOn_unstableEndpoint`: the
  endpoint maps `stableEndpoint : W^s(S) → S` and `unstableEndpoint : W^u(S) → S` of
  `TauCeti.Geometry.Manifold.Morse.Bott.Flow` are smooth.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (Morse–Bott functions and their gradient flows).
* A. Banyaga and D. E. Hurtubise, *Lectures on Morse Homology*, Kluwer, 2004, Section 3.5
  (Morse–Bott functions).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsBottAdaptedPseudoGradient

/-- The cube of half the radius `r` in the coordinates of a Morse–Bott chart, as an open subset of
the chart source. -/
private theorem isOpen_halfCube (φ : MorseBottChart E f x) (r : ℝ) :
    IsOpen (φ.toChart.source ∩ φ.toChart ⁻¹' {v : E | ‖φ.coord v‖ < r / 2}) :=
  φ.toChart.continuousOn.isOpen_inter_preimage φ.toChart.open_source
    (isOpen_lt (continuous_norm.comp φ.continuous_coord) continuous_const)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  (hX : IsBottAdaptedPseudoGradient f X) {S : Set M} {c : ℝ}

/-- **The stable set of a piece of the critical set, in a Morse–Bott chart.** Let `S` be a set of
points on the level `c` of `f` containing every critical point near each of its points, and let `X`
be the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in a Morse–Bott chart `φ` centred at a point `x` of `S`. On a
small coordinate cube around `x`, a point lies in `⋃ p ∈ S, W^s(p)` exactly when it lies in the
stable subspace of the chart, where its coordinates of negative weight vanish. -/
theorem exists_forall_mem_biUnion_stableSet_iff (φ : MorseBottChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    (hc : ∀ p ∈ S, f p = c) (hSo : ∀ p ∈ S, ∀ᶠ q in 𝓝 p, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → q ∈ S)
    (hx : x ∈ S) :
    ∃ ε > 0, ∀ y ∈ φ.toChart.source, ‖φ.coord (φ.toChart y)‖ < ε →
      (y ∈ ⋃ p ∈ S, hX.flow.stableSet p ↔ φ.toChart y ∈ φ.stableSubspace) := by
  obtain ⟨r, hr, hrT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  -- The critical points with small coordinates lie in `S`.
  obtain ⟨δ, hδ, hδS⟩ := Metric.eventually_nhds_iff.1
    (φ.tendsto_toChart_symm_coord_symm_nhds_zero.eventually (hSo x hx))
  have hρ : 0 < r / (4 * (Module.finrank ℝ E + 1)) := by positivity
  refine ⟨min (r / (4 * (Module.finrank ℝ E + 1))) δ, lt_min hρ hδ, fun y hy hyε ↦ ?_⟩
  have hyr : ‖φ.coord (φ.toChart y)‖ < r / (4 * (Module.finrank ℝ E + 1)) :=
    hyε.trans_le (min_le_left _ _)
  have hyr2 : ‖φ.coord (φ.toChart y)‖ < r / 2 := hyr.trans_le <| by
    gcongr
    linarith [(Nat.cast_nonneg (Module.finrank ℝ E) : (0 : ℝ) ≤ Module.finrank ℝ E)]
  rw [φ.mem_stableSubspace, mem_iUnion₂]
  constructor
  · -- An orbit converging to a point of `S` never goes below the level `c = f x`, so it does not
    -- cross the energy barrier.
    rintro ⟨p, hp, hs⟩
    refine hX.forall_coord_eq_zero_of_forall_le_apply_flow φ hφ hrT hy hyr fun T ↦ ?_
    rw [hc x hx, ← hc p hp]
    exact Flow.le_of_mem_stableSet_of_antitone (Flow.isInvariant_stableSet _ _ T hs)
      (hX.mdifferentiable p).continuousAt (hX.antitone_flow _)
  · -- A point of the stable slice converges to its projection onto the critical set, which has
    -- small coordinates and therefore lies in `S`.
    intro hu
    set w : Fin (Module.finrank ℝ E) → ℝ := fun i ↦
      if φ.weight i = 0 then φ.coord (φ.toChart y) i else 0
    have hw : ‖w‖ < min (r / (4 * (Module.finrank ℝ E + 1))) δ :=
      (φ.norm_ite_weight_eq_zero_le _).trans_lt hyε
    have hwr : ‖w‖ < r := hw.trans_le ((min_le_left _ _).trans (by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg (Module.finrank ℝ E) : (0 : ℝ) ≤ Module.finrank ℝ E)]))
    have hcrit := φ.mfderiv_toChart_symm_coord_symm_eq_zero (hrT w hwr) fun i hi ↦ by
      simp [w, hi]
    refine ⟨_, hδS (by rw [dist_zero_right]; exact hw.trans_le (min_le_right _ _)) hcrit,
      Flow.mem_stableSet.2 (hX.tendsto_flow_of_forall_coord_eq_zero φ hφ hrT hy hyr2 hu)⟩

/-- A version of `exists_forall_mem_biUnion_stableSet_iff` on the cube of half a radius `r` of
coordinates inside the chart, as used for the slice charts and the endpoint maps. -/
private theorem exists_forall_mem_biUnion_stableSet_iff_half (φ : MorseBottChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    (hc : ∀ p ∈ S, f p = c) (hSo : ∀ p ∈ S, ∀ᶠ q in 𝓝 p, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → q ∈ S)
    (hx : x ∈ S) :
    ∃ r > 0, (∀ z, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target) ∧
      ∀ y ∈ φ.toChart.source, ‖φ.coord (φ.toChart y)‖ < r / 2 →
        (y ∈ ⋃ p ∈ S, hX.flow.stableSet p ↔ φ.toChart y ∈ φ.stableSubspace) := by
  obtain ⟨ε, hε, hloc⟩ := hX.exists_forall_mem_biUnion_stableSet_iff φ hφ hc hSo hx
  obtain ⟨r, hr, hrT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  refine ⟨min (2 * ε) r, lt_min (by positivity) hr,
    fun z hz ↦ hrT z (hz.trans_le (min_le_right _ _)), fun y hy hyr ↦ hloc y hy ?_⟩
  exact hyr.trans_le (by linarith [min_le_left (2 * ε) r])

/-- A point of the stable set of `p ∈ S` lies in the source of a slice chart for `W^s(S)` built
from a Morse–Bott chart at `p`, together with the data needed for its endpoint map. -/
private theorem exists_slice_data (hc : ∀ p ∈ S, f p = c)
    (hSo : ∀ p ∈ S, ∀ᶠ q in 𝓝 p, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → q ∈ S)
    {p y : M} (hp : p ∈ S) (hy : y ∈ hX.flow.stableSet p) :
    ∃ (φ : MorseBottChart E f p) (r T : ℝ),
      (∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
        fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)) ∧
      (∀ z, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target) ∧
      (∀ y ∈ φ.toChart.source, ‖φ.coord (φ.toChart y)‖ < r / 2 →
        (y ∈ ⋃ p ∈ S, hX.flow.stableSet p ↔ φ.toChart y ∈ φ.stableSubspace)) ∧
      hX.flow T y ∈ φ.toChart.source ∩ φ.toChart ⁻¹' {v : E | ‖φ.coord v‖ < r / 2} := by
  obtain ⟨φ, hφ⟩ := hX.exists_morseBottChart p (hX.mfderiv_eq_zero_of_mem_stableSet hy)
  obtain ⟨r, hr, hrT, hloc⟩ := hX.exists_forall_mem_biUnion_stableSet_iff_half φ hφ hc hSo hp
  have hpD : p ∈ φ.toChart.source ∩ φ.toChart ⁻¹' {v : E | ‖φ.coord v‖ < r / 2} :=
    ⟨φ.mem_source, by simpa using half_pos hr⟩
  obtain ⟨T, hT⟩ := ((Flow.mem_stableSet.1 hy).eventually
    ((isOpen_halfCube φ r).mem_nhds hpD)).exists
  exact ⟨φ, r, T, hφ, hrT, hloc, hT⟩

/-- **Slice charts for the stable manifold of a piece of the critical set.** Let `S` be a set of
points on the level `c` of `f` containing every critical point near each of its points. Every point
of the stable set `W^s(p)` of a point `p ∈ S` lies in the source of a chart of the maximal atlas
that flattens `⋃ p ∈ S, W^s(p)` onto a subspace of dimension `n - λ`, where `λ` is the Morse index
of `f` at `p`. -/
theorem exists_isSliceChart_biUnion_stableSet (hc : ∀ p ∈ S, f p = c)
    (hSo : ∀ p ∈ S, ∀ᶠ q in 𝓝 p, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → q ∈ S)
    {p y : M} (hp : p ∈ S) (hy : y ∈ hX.flow.stableSet p) :
    ∃ (L : Submodule ℝ E) (q : OpenPartialHomeomorph M E),
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f p = Module.finrank ℝ E ∧
        y ∈ q.source ∧ q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
        IsSliceChart q (L : Set E) (⋃ p ∈ S, hX.flow.stableSet p) := by
  obtain ⟨φ, r, T, -, -, hloc, hT⟩ := hX.exists_slice_data hc hSo hp hy
  obtain ⟨q, hyq, hq, hs⟩ := hX.exists_isSliceChart_of_flow_mem φ.mem_maximalAtlas
    (isOpen_halfCube φ r) inter_subset_left
    (hX.isSliceChart_flowDiffeomorph_trans_restr (L := φ.stableSubspace)
      (fun t y ↦ by simp only [mem_iUnion₂, Flow.apply_mem_stableSet_iff])
      (isOpen_halfCube φ r) (fun y hy ↦ hloc y hy.1 hy.2) T) hT
  exact ⟨φ.stableSubspace, q, φ.finrank_stableSubspace_add_manifoldMorseIndex, hyq, hq, hs⟩

/-- **The endpoint map of the stable manifold is smooth.** Let `S` be a set of points on the level
`c` of `f` containing every critical point near each of its points. Near every point `y` of the
stable set of a point of `S`, the forward endpoint map
`TauCeti.IsBottAdaptedPseudoGradient.stableEndpoint`, which sends `⋃ p ∈ S, W^s(p)` to `S`
(`TauCeti.IsBottAdaptedPseudoGradient.mem_biUnion_stableSet_iff`), agrees on
`⋃ p ∈ S, W^s(p)` with a map `g` that is smooth on a neighbourhood of `y` in `M`. -/
theorem exists_contMDiffOn_eqOn_stableEndpoint (hc : ∀ p ∈ S, f p = c)
    (hSo : ∀ p ∈ S, ∀ᶠ q in 𝓝 p, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → q ∈ S)
    {p y : M} (hp : p ∈ S) (hy : y ∈ hX.flow.stableSet p) :
    ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ g : M → M, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ g U ∧
      EqOn g hX.stableEndpoint (U ∩ ⋃ p ∈ S, hX.flow.stableSet p) := by
  obtain ⟨φ, r, T, hφ, hrT, hloc, hT⟩ := hX.exists_slice_data hc hSo hp hy
  have := φ.finiteDimensional
  set D := φ.toChart.source ∩ φ.toChart ⁻¹' {v : E | ‖φ.coord v‖ < r / 2}
  have hr : 0 < r := by
    have h : ‖φ.coord (φ.toChart (hX.flow T y))‖ < r / 2 := hT.2
    linarith [norm_nonneg (φ.coord (φ.toChart (hX.flow T y)))]
  -- The projection onto the coordinates of weight `0`, read in the chart.
  let P : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    ContinuousLinearMap.pi fun i ↦ if φ.weight i = 0 then ContinuousLinearMap.proj i else 0
  have hP (v : Fin (Module.finrank ℝ E) → ℝ) : P v = fun i ↦ if φ.weight i = 0 then v i else 0 := by
    funext i
    by_cases hi : φ.weight i = 0 <;> simp [P, hi]
  let ψ : E →L[ℝ] E := (φ.coordL.symm : _ →L[ℝ] E).comp (P.comp (φ.coordL : E →L[ℝ] _))
  have hψ (v : E) : ψ v = φ.coord.symm (fun i ↦ if φ.weight i = 0 then φ.coord v i else 0) := by
    simp [ψ, hP]
  -- The endpoint map is the projection, which is smooth on the cube `D`.
  have hπ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun y ↦ φ.toChart.symm (ψ (φ.toChart y))) D := by
    refine (contMDiffOn_symm_of_mem_maximalAtlas φ.mem_maximalAtlas).comp
      (ψ.contDiff.contMDiff.comp_contMDiffOn
        ((contMDiffOn_of_mem_maximalAtlas φ.mem_maximalAtlas).mono inter_subset_left))
      fun z hz ↦ ?_
    rw [mem_preimage, hψ]
    exact hrT _ (((φ.norm_ite_weight_eq_zero_le _).trans_lt hz.2).trans (half_lt_self hr))
  refine ⟨hX.flow T ⁻¹' D, (isOpen_halfCube φ r).preimage (hX.flow.continuous_toFun T), hT,
    fun z ↦ φ.toChart.symm (ψ (φ.toChart (hX.flow T z))), ?_, fun z ⟨hzD, hzS⟩ ↦ ?_⟩
  · exact hπ.comp (hX.contMDiff_flow_apply T).contMDiffOn fun z hz ↦ hz
  -- From time `T` on, the orbit of `z` converges along the linear flow to the projection.
  have hzS' : hX.flow T z ∈ ⋃ p ∈ S, hX.flow.stableSet p := by
    simpa only [mem_iUnion₂, Flow.apply_mem_stableSet_iff] using hzS
  have hu := (φ.mem_stableSubspace).1 ((hloc _ hzD.1 hzD.2).1 hzS')
  have hlim := hX.tendsto_flow_of_forall_coord_eq_zero φ hφ hrT hzD.1 hzD.2 hu
  rw [← hψ] at hlim
  have hlim' : Tendsto (fun t ↦ hX.flow t z) atTop
      (𝓝 (φ.toChart.symm (ψ (φ.toChart (hX.flow T z))))) :=
    (Flow.tendsto_atTop_iff_mem_stableSet_of_eqOn (b := T) fun s _ ↦ by
      dsimp only
      rw [← Flow.map_add, sub_add_cancel]).2 (Flow.mem_stableSet.2 hlim)
  exact (hX.stableEndpoint_eq_iff_mem_stableSet.2 (Flow.mem_stableSet.2 hlim')).symm

/-- **The stable manifold of a piece of the critical set.** Let `S` be a set of points on the level
`c` of `f` containing every critical point near each of its points, on which the Morse index of `f`
is `k`. Then `⋃ p ∈ S, W^s(p)` is an embedded submanifold of `M` of dimension `n - k`: it carries a
smooth manifold structure modelled on any subspace `L` of dimension `n - k`, with its subspace
topology, for which the inclusion into `M` is a smooth embedding. -/
theorem exists_isManifold_isSmoothEmbedding_biUnion_stableSet (hc : ∀ p ∈ S, f p = c)
    (hSo : ∀ p ∈ S, ∀ᶠ q in 𝓝 p, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → q ∈ S) {k : ℕ}
    (hk : ∀ p ∈ S, manifoldMorseIndex 𝓘(ℝ, E) f p = k) {L : Submodule ℝ E}
    (hL : Module.finrank ℝ L + k = Module.finrank ℝ E) :
    ∃ C : ChartedSpace L (⋃ p ∈ S, hX.flow.stableSet p), letI := C
      IsManifold 𝓘(ℝ, L) ∞ (⋃ p ∈ S, hX.flow.stableSet p) ∧
        Manifold.IsSmoothEmbedding 𝓘(ℝ, L) 𝓘(ℝ, E) ∞
          (Subtype.val : (⋃ p ∈ S, hX.flow.stableSet p) → M) := by
  refine exists_isSmoothEmbedding_of_finrankSubspaceCharts fun y hy ↦ ?_
  obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.1 hy
  obtain ⟨V, q, hV, hyq, hq, hs⟩ := hX.exists_isSliceChart_biUnion_stableSet hc hSo hp hyp
  exact ⟨q, V, hyq, fun z hz ↦ contMDiffAt_of_mem_maximalAtlas hq hz,
    fun z hz ↦ contMDiffAt_symm_of_mem_maximalAtlas hq hz, isSliceChart_iff.1 hs,
    by rw [hk p hp] at hV; omega⟩

/-! ### Unstable manifolds -/

/-- The unstable sets of the flow of `X` are the stable sets of the flow of `-X`. -/
private theorem biUnion_stableSet_neg :
    ⋃ p ∈ S, hX.neg.flow.stableSet p = ⋃ p ∈ S, hX.flow.unstableSet p := by
  simp only [hX.neg_flow, Flow.stableSet_reverse]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- The hypotheses on `S` for `f` give the same hypotheses for `-f`. -/
private theorem neg_hyps (hc : ∀ p ∈ S, f p = c)
    (hSo : ∀ p ∈ S, ∀ᶠ q in 𝓝 p, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → q ∈ S) :
    (∀ p ∈ S, (-f) p = -c) ∧
      ∀ p ∈ S, ∀ᶠ q in 𝓝 p, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (-f) q = 0 → q ∈ S :=
  ⟨fun p hp ↦ by simp [hc p hp], fun p hp ↦ (hSo p hp).mono fun q hq h ↦
    hq (mfderiv_neg_eq_zero_iff.1 h)⟩

/-- **Slice charts for the unstable manifold of a piece of the critical set.** Let `S` be a set of
points on the level `c` of `f` containing every critical point near each of its points. Every point
of the unstable set `W^u(p)` of a point `p ∈ S` lies in the source of a chart of the maximal atlas
that flattens `⋃ p ∈ S, W^u(p)` onto a subspace of dimension `n - λ⁻`, where `λ⁻` is the Morse
index of `-f` at `p`. These are the slice charts of the stable manifold for `-X`, adapted to
`-f`. -/
theorem exists_isSliceChart_biUnion_unstableSet (hc : ∀ p ∈ S, f p = c)
    (hSo : ∀ p ∈ S, ∀ᶠ q in 𝓝 p, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → q ∈ S)
    {p y : M} (hp : p ∈ S) (hy : y ∈ hX.flow.unstableSet p) :
    ∃ (L : Submodule ℝ E) (q : OpenPartialHomeomorph M E),
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) (-f) p = Module.finrank ℝ E ∧
        y ∈ q.source ∧ q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
        IsSliceChart q (L : Set E) (⋃ p ∈ S, hX.flow.unstableSet p) := by
  rw [← hX.biUnion_stableSet_neg]
  rw [← Flow.stableSet_reverse, ← hX.neg_flow] at hy
  obtain ⟨hc', hSo'⟩ := neg_hyps hc hSo
  exact hX.neg.exists_isSliceChart_biUnion_stableSet hc' hSo' hp hy

/-- **The endpoint map of the unstable manifold is smooth.** Let `S` be a set of points on the
level `c` of `f` containing every critical point near each of its points. Near every point `y` of
the unstable set of a point of `S`, the backward endpoint map
`TauCeti.IsBottAdaptedPseudoGradient.unstableEndpoint`, which sends `⋃ p ∈ S, W^u(p)` to `S`
(`TauCeti.IsBottAdaptedPseudoGradient.mem_biUnion_unstableSet_iff`), agrees on
`⋃ p ∈ S, W^u(p)` with a map `g` that is smooth on a neighbourhood of `y` in `M`. -/
theorem exists_contMDiffOn_eqOn_unstableEndpoint (hc : ∀ p ∈ S, f p = c)
    (hSo : ∀ p ∈ S, ∀ᶠ q in 𝓝 p, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → q ∈ S)
    {p y : M} (hp : p ∈ S) (hy : y ∈ hX.flow.unstableSet p) :
    ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ g : M → M, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ g U ∧
      EqOn g hX.unstableEndpoint (U ∩ ⋃ p ∈ S, hX.flow.unstableSet p) := by
  rw [← Flow.stableSet_reverse, ← hX.neg_flow] at hy
  obtain ⟨hc', hSo'⟩ := neg_hyps hc hSo
  rw [← hX.biUnion_stableSet_neg, ← hX.neg_stableEndpoint]
  exact hX.neg.exists_contMDiffOn_eqOn_stableEndpoint hc' hSo' hp hy

/-- **The unstable manifold of a piece of the critical set.** Let `S` be a set of points on the
level `c` of `f` containing every critical point near each of its points, on which the Morse index
of `-f` is `k`. Then `⋃ p ∈ S, W^u(p)` is an embedded submanifold of `M` of dimension `n - k`: it
carries a smooth manifold structure modelled on any subspace `L` of dimension `n - k`, with its
subspace topology, for which the inclusion into `M` is a smooth embedding. -/
theorem exists_isManifold_isSmoothEmbedding_biUnion_unstableSet (hc : ∀ p ∈ S, f p = c)
    (hSo : ∀ p ∈ S, ∀ᶠ q in 𝓝 p, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → q ∈ S) {k : ℕ}
    (hk : ∀ p ∈ S, manifoldMorseIndex 𝓘(ℝ, E) (-f) p = k) {L : Submodule ℝ E}
    (hL : Module.finrank ℝ L + k = Module.finrank ℝ E) :
    ∃ C : ChartedSpace L (⋃ p ∈ S, hX.flow.unstableSet p), letI := C
      IsManifold 𝓘(ℝ, L) ∞ (⋃ p ∈ S, hX.flow.unstableSet p) ∧
        Manifold.IsSmoothEmbedding 𝓘(ℝ, L) 𝓘(ℝ, E) ∞
          (Subtype.val : (⋃ p ∈ S, hX.flow.unstableSet p) → M) := by
  obtain ⟨hc', hSo'⟩ := neg_hyps hc hSo
  rw [← hX.biUnion_stableSet_neg]
  exact hX.neg.exists_isManifold_isSmoothEmbedding_biUnion_stableSet hc' hSo' hk hL

end IsBottAdaptedPseudoGradient

end TauCeti
