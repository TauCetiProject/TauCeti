/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.LocalModels
import all TauCeti.Geometry.Manifold.Boundary.OneDimensional

/-!
# Compact one-manifolds oriented by local coordinates

An orientation of a one-dimensional space is given here topologically, by local coordinates
(`TauCeti.IsOrientingCoordinates`): functions `φ x`, continuous and injective near `x`, any two of
which induce the same order near every point where both are defined. Unlike the orientations of
the interior by charts in `TauCeti.Geometry.Manifold.Boundary.OneDimensional`, these coordinates
are also defined at the boundary points. At a boundary point `x` the orientation points out of `M`
when `x` is a local maximum of `φ x`, and into `M` when it is a local minimum; exactly one of the
two holds, and which one can be read in any orienting coordinate defined at `x`. The oriented
count says that these two kinds of boundary points of a compact Hausdorff one-manifold are equally
many. No smoothness is assumed. It is the topological counterpart of
`TauCeti.ncard_setOf_signBasis_eq_one_eq_ncard_setOf_signBasis_eq_neg_one`, which needs a smooth
structure. It is a topological input to the proof that the integral Morse boundary squares to
zero, where the broken trajectories at the two ends of an arc of index-two trajectories carry
opposite signs.

## Strategy

The proof reuses the cut set of the parity proof in
`TauCeti.Geometry.Manifold.Boundary.OneDimensional`: finitely many interior points `P` cut `M`
into arcs, each lying in a single chart. Call an end of an arc a *tail* when the orientation leaves
its point into the arc. Along an arc the coordinates `φ z` all increase, or all decrease, with the
chart coordinate, so of its two ends exactly one is a tail. Of the two sides of a point of `P`
exactly one is a tail as well. Counting tails with `1` and the other ends with `-1`, every arc and
every point of `P` therefore contribute `0`, and so do the boundary points, which are tails exactly
when they are incoming.

## Main results

* `TauCeti.IsOrientingCoordinates.isLocalMax_iff_not_isLocalMin`: at a boundary point an
  orientation points either out or in.
* `TauCeti.IsOrientingCoordinates.isLocalMax_iff_of_mem` and
  `TauCeti.IsOrientingCoordinates.isLocalMin_iff_of_mem`: whether it points out or in can be read
  in any orienting coordinate defined at the boundary point.
* `TauCeti.ModelWithCorners.ncard_setOf_isLocalMax_eq_ncard_setOf_isLocalMin`: a compact oriented
  one-dimensional manifold has as many outgoing as incoming boundary points.
* `TauCeti.ncard_setOf_isLocalMax_eq_ncard_setOf_isLocalMin_of_forall_exists_homeomorph_Ico`: the
  same for a compact Hausdorff space given by local models.

## References

* J. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 (the boundary points of a compact oriented one-manifold have signs adding up to zero) and
  Appendix (the classification of one-manifolds).
-/

public section

noncomputable section

open Function Set Topology

open scoped Manifold

open TauCeti.EuclideanHalfSpace

namespace TauCeti

section Direction

variable {M : Type*} [TopologicalSpace M] {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}

/-- A function `ψ` *increases along the chart `e` at `y`* when it exceeds `ψ y` at the points read
by `e` with coordinate slightly above that of `y`. -/
private def IncreasesAt (e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)) (ψ : M → ℝ) (y : M) :
    Prop :=
  ∀ᶠ s in 𝓝[>] (e y).val 0, ψ y < ψ (e.symm (normalRay s))

/-- The points of a chart domain with coordinate within `η` of that of `y` form a neighbourhood of
`y`. -/
private theorem coord_mem_nhds {y : M} (hy : y ∈ e.source) {η : ℝ} (hη : 0 < η) :
    e.source ∩ (fun z ↦ (e z).val 0) ⁻¹' {s | |s - (e y).val 0| < η} ∈ 𝓝 y :=
  (continuousOn_coord.isOpen_inter_preimage e.open_source
    (isOpen_lt (by fun_prop) continuous_const)).mem_nhds ⟨hy, by simpa using hη⟩

/-- Reading the coordinates slightly above that of `y` back through the chart tends to `y`. -/
private theorem tendsto_symm_normalRay {y : M} (hy : y ∈ e.source) :
    Filter.Tendsto (fun s ↦ e.symm (normalRay s)) (𝓝[>] (e y).val 0) (𝓝 y) := by
  obtain ⟨ε, hε, -, h⟩ := exists_coord_nhds e.open_source subset_rfl hy
  have hc : ContinuousAt (fun s ↦ e.symm (normalRay s)) ((e y).val 0) :=
    (continuousOn_symm_normalRay (S := Icc ((e y).val 0 - ε) ((e y).val 0 + ε)) fun s hs ↦
      (h s ((abs_sub_comm _ _).trans_le (mem_Icc_iff_abs_le.2 hs))).1).continuousAt
      (Icc_mem_nhds (by linarith) (by linarith))
  simpa only [symm_normalRay_coord hy] using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- **Continuous injective functions are monotone in a coordinate.** If `ψ` is continuous and
injective on an open neighbourhood `V` of a point `y` of a chart domain, then on a coordinate
interval around `y`, read through the chart, `ψ` is strictly monotone if it increases along the
chart at `y`, and strictly antitone otherwise. -/
private theorem exists_strictMonoOn_of_increasesAt {V : Set M} (hV : IsOpen V) {ψ : M → ℝ}
    (hψc : ContinuousOn ψ V) (hψi : InjOn ψ V) {y : M} (hyV : y ∈ V) (hye : y ∈ e.source) :
    ∃ η > 0, (∀ s, |s - (e y).val 0| ≤ η → normalRay s ∈ e.target ∧ e.symm (normalRay s) ∈ V) ∧
      (IncreasesAt e ψ y → StrictMonoOn (fun s ↦ ψ (e.symm (normalRay s)))
        (Icc (max ((e y).val 0 - η) 0) ((e y).val 0 + η))) ∧
      (¬IncreasesAt e ψ y → StrictAntiOn (fun s ↦ ψ (e.symm (normalRay s)))
        (Icc (max ((e y).val 0 - η) 0) ((e y).val 0 + η))) := by
  obtain ⟨η, hη, -, h⟩ :=
    exists_coord_nhds (hV.inter e.open_source) inter_subset_right ⟨hyV, hye⟩
  set t := (e y).val 0
  have ht : 0 ≤ t := (e y).property
  set I := Icc (max (t - η) 0) (t + η)
  have hI : ∀ s ∈ I, |s - t| ≤ η ∧ 0 ≤ s := fun s hs ↦
    ⟨abs_sub_le_iff.2 ⟨by linarith [hs.2], by linarith [le_max_left (t - η) 0, hs.1]⟩,
      (le_max_right _ _).trans hs.1⟩
  have hcont : ContinuousOn (fun s ↦ ψ (e.symm (normalRay s))) I :=
    hψc.comp (continuousOn_symm_normalRay fun s hs ↦ (h s (hI s hs).1).1)
      fun s hs ↦ (h s (hI s hs).1).2.1
  have hinj : InjOn (fun s ↦ ψ (e.symm (normalRay s))) I := fun s hs s' hs' hss' ↦ by
    rw [← coord_symm_normalRay (hI s hs).2 (h s (hI s hs).1).1,
      ← coord_symm_normalRay (hI s' hs').2 (h s' (hI s' hs').1).1,
      hψi (h s (hI s hs).1).2.1 (h s' (hI s' hs').1).2.1 hss']
  have htI : t ∈ I := ⟨max_le (by linarith) ht, by linarith⟩
  have hyt : e.symm (normalRay t) = y := symm_normalRay_coord hye
  have hev : ∀ᶠ s in 𝓝[>] t, s ∈ I ∧ t < s := by
    filter_upwards [Ioo_mem_nhdsGT (by linarith : t < t + η)] with s hs
    exact ⟨⟨(max_le (by linarith) ht).trans hs.1.le, hs.2.le⟩, hs.1⟩
  refine ⟨η, hη, fun s hs ↦ ⟨(h s hs).1, (h s hs).2.1⟩, fun hinc ↦ ?_, fun hinc ↦ ?_⟩ <;>
    rcases hcont.strictMonoOn_of_injOn_Icc' (htI.1.trans htI.2) hinj with hm | ha
  · exact hm
  · obtain ⟨s, ⟨hsI, hts⟩, hlt⟩ := (hev.and hinc).exists
    have := ha htI hsI hts
    simp only [hyt] at this
    exact absurd hlt (lt_asymm this)
  · refine absurd ?_ hinc
    filter_upwards [hev] with s hs
    simpa only [hyt] using hm htI hs.1 hs.2
  · exact ha

/-- A function strictly monotone on `S` when `P` holds, and strictly antitone otherwise, increases
from `s` to `s' > s` in `S` exactly when `P` holds, and decreases exactly when it does not. -/
private theorem lt_iff_of_strictMonoOn_of_strictAntiOn {f : ℝ → ℝ} {S : Set ℝ} {P : Prop}
    (hmono : P → StrictMonoOn f S) (hanti : ¬P → StrictAntiOn f S) {s s' : ℝ} (hs : s ∈ S)
    (hs' : s' ∈ S) (hss' : s < s') : (f s < f s' ↔ P) ∧ (f s' < f s ↔ ¬P) := by
  by_cases hP : P
  · have := hmono hP hs hs' hss'
    exact ⟨iff_of_true this hP, iff_of_false (lt_asymm this) (not_not.2 hP)⟩
  · have := hanti hP hs hs' hss'
    exact ⟨iff_of_false (lt_asymm this) hP, iff_of_true this hP⟩

/-- **Sides of a point and the direction of a coordinate.** Let `ψ` be continuous and injective on
an open neighbourhood of a point `p` of a chart domain, and let `S` accumulate at `p`, with all its
points in the chart domain, read above `p` if `a` holds and below `p` otherwise. Then `ψ` exceeds
`ψ p` on `S` near `p` exactly when `ψ` increases along the chart at `p` if and only if `a`. -/
private theorem eventually_lt_iff_increasesAt {V : Set M} (hV : IsOpen V) {ψ : M → ℝ}
    (hψc : ContinuousOn ψ V) (hψi : InjOn ψ V) {p : M} (hpV : p ∈ V) (hpe : p ∈ e.source)
    {S : Set M} (hpS : p ∈ closure S) {a : Prop}
    (hS : ∀ w ∈ S, w ∈ e.source ∧
      ((e p).val 0 < (e w).val 0 ∧ a ∨ (e w).val 0 < (e p).val 0 ∧ ¬a)) :
    (∀ᶠ w in 𝓝 p, w ∈ S → ψ p < ψ w) ↔ (IncreasesAt e ψ p ↔ a) := by
  obtain ⟨η, hη, -, hmono, hanti⟩ := exists_strictMonoOn_of_increasesAt hV hψc hψi hpV hpe
  set t := (e p).val 0
  have htI : t ∈ Icc (max (t - η) 0) (t + η) := ⟨max_le (by linarith) (e p).property, by linarith⟩
  -- On `S` near `p`, comparing values of `ψ` with `ψ p` compares coordinates with that of `p`.
  have hcmp : ∀ w ∈ S, |(e w).val 0 - t| < η → (ψ p < ψ w ↔ (IncreasesAt e ψ p ↔ a)) := by
    intro w hwS hwη
    obtain ⟨hwe, hw⟩ := hS w hwS
    have hwI : (e w).val 0 ∈ Icc (max (t - η) 0) (t + η) :=
      ⟨max_le (by linarith [(abs_lt.1 hwη).1]) (e w).property, by linarith [(abs_lt.1 hwη).2]⟩
    have hp : ψ p = ψ (e.symm (normalRay t)) := by rw [symm_normalRay_coord hpe]
    have hw' : ψ w = ψ (e.symm (normalRay ((e w).val 0))) := by rw [symm_normalRay_coord hwe]
    rw [hp, hw']
    rcases hw with ⟨hlt, ha⟩ | ⟨hlt, ha⟩
    · rw [(lt_iff_of_strictMonoOn_of_strictAntiOn hmono hanti htI hwI hlt).1, iff_true_intro ha,
        iff_true]
    · rw [(lt_iff_of_strictMonoOn_of_strictAntiOn hmono hanti hwI htI hlt).2, iff_false_intro ha,
        iff_false]
  constructor
  · intro h
    by_contra hne
    obtain ⟨w, hwS, hlt, -, hwη⟩ := ((mem_closure_iff_frequently.1 hpS).and_eventually
      (h.and (coord_mem_nhds hpe hη))).exists
    exact hne ((hcmp w hwS hwη).1 (hlt hwS))
  · intro h
    filter_upwards [coord_mem_nhds hpe hη] with w hw hwS
    exact (hcmp w hwS hw.2).2 h

/-- If, in a chart, a set `S` accumulating at `p` is read above `p` and a set `T` accumulating at
`p` below `p`, then a function continuous and injective near `p` exceeds its value at `p` near
`p` on exactly one of `S` and `T`. -/
private theorem eventually_lt_iff_not_eventually_lt {V : Set M} (hV : IsOpen V) {ψ : M → ℝ}
    (hψc : ContinuousOn ψ V) (hψi : InjOn ψ V) {p : M} (hpV : p ∈ V) (hpe : p ∈ e.source)
    {S T : Set M} (hpS : p ∈ closure S) (hpT : p ∈ closure T)
    (hS : ∀ w ∈ S, w ∈ e.source ∧ (e p).val 0 < (e w).val 0)
    (hT : ∀ w ∈ T, w ∈ e.source ∧ (e w).val 0 < (e p).val 0) :
    (∀ᶠ w in 𝓝 p, w ∈ S → ψ p < ψ w) ↔ ¬∀ᶠ w in 𝓝 p, w ∈ T → ψ p < ψ w := by
  rw [eventually_lt_iff_increasesAt hV hψc hψi hpV hpe hpS (a := True)
      fun w hw ↦ ⟨(hS w hw).1, .inl ⟨(hS w hw).2, trivial⟩⟩,
    eventually_lt_iff_increasesAt hV hψc hψi hpV hpe hpT (a := False)
      fun w hw ↦ ⟨(hT w hw).1, .inr ⟨(hT w hw).2, not_false⟩⟩]
  simp

end Direction

section Sides

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]

/-- A function continuous and injective near a point `p` exceeds its value at `p` near `p` on
exactly one of the two sides of `p`: the side `true` is read above `p` in the chart at `p`, and
the side `false` below it. -/
private theorem IsSides.opposite {P : Set M} {p : M} {J : Bool → Set M} {N : Set M}
    {q : Bool → M} (hs : IsSides P p J N q) {ψ : M → ℝ} {V : Set M} (hV : IsOpen V)
    (hpV : p ∈ V) (hψc : ContinuousOn ψ V) (hψi : InjOn ψ V) :
    (∀ᶠ w in 𝓝 p, w ∈ J true → ψ p < ψ w) ↔ ¬∀ᶠ w in 𝓝 p, w ∈ J false → ψ p < ψ w := by
  obtain ⟨η, hη, hηt, htarget, hJ⟩ := hs.param
  set e := chartAt (EuclideanHalfSpace 1) p
  set t := (e p).val 0
  -- A point of a side is read at its parameter.
  have hside (b : Bool) : ∀ w ∈ J b,
      w ∈ e.source ∧ (e w).val 0 ∈ cond b (Ioc t (t + η)) (Ico (t - η) t) := by
    intro w hw
    rw [hJ b] at hw
    obtain ⟨s, hs', rfl⟩ := hw
    have hsI : s ∈ Icc (t - η) (t + η) := (cond_Ioc_Ico_facts hη b).1 hs'
    refine ⟨e.map_target (htarget s hsI), ?_⟩
    rwa [coord_symm_normalRay (by linarith [hsI.1]) (htarget s hsI)]
  exact eventually_lt_iff_not_eventually_lt hV hψc hψi hpV (mem_chart_source _ p)
    (hs.mem_closure true) (hs.mem_closure false)
    (fun w hw ↦ ⟨(hside true w hw).1, (hside true w hw).2.1⟩)
    fun w hw ↦ ⟨(hside false w hw).1, (hside false w hw).2.2⟩

end Sides

section Orientation

/-- **Orientations of a one-dimensional space by local coordinates.** The functions `φ x : X → ℝ`,
each continuous and injective on an open neighbourhood `U x` of `x`, *orient* `X` when any two of
them induce the same order near every point at which both are defined: near a point `z` of
`U x ∩ U y`, a point `w` lies above `z` for `φ x` exactly when it lies above `z` for `φ y`. On a
one-dimensional manifold this is an orientation, for which the local coordinates `φ x` are
positively oriented. It needs no smooth structure, so it applies to spaces such as compactified
spaces of trajectories, which are described by local homeomorphisms only. Local orientations
through local homology are `TauCeti.IsLocalOrientation`; the description by coordinates used here
is specific to dimension one. -/
structure IsOrientingCoordinates {X : Type*} [TopologicalSpace X] (U : X → Set X)
    (φ : X → X → ℝ) : Prop where
  /-- The domain of each coordinate is open. -/
  isOpen (x : X) : IsOpen (U x)
  /-- The domain of the coordinate at `x` contains `x`. -/
  mem (x : X) : x ∈ U x
  /-- Each coordinate is continuous on its domain. -/
  continuousOn (x : X) : ContinuousOn (φ x) (U x)
  /-- Each coordinate is injective on its domain. -/
  injOn (x : X) : InjOn (φ x) (U x)
  /-- Any two coordinates induce the same order near each point of their common domain. -/
  coherent (x y : X) : ∀ z ∈ U x ∩ U y, ∀ᶠ w in 𝓝 z, (φ x z < φ x w ↔ φ y z < φ y w)

variable {M : Type*} [TopologicalSpace M] {U : M → Set M} {φ : M → M → ℝ}
  {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}

/-- Two orienting coordinates defined at a point `z` of a chart domain increase along the chart at
`z` together. -/
private theorem IsOrientingCoordinates.increasesAt_iff_increasesAt
    (hφ : IsOrientingCoordinates U φ) {x y z : M} (hz : z ∈ U x ∩ U y) (hze : z ∈ e.source) :
    IncreasesAt e (φ x) z ↔ IncreasesAt e (φ y) z :=
  Filter.eventually_congr ((tendsto_symm_normalRay hze).eventually (hφ.coherent x y z hz))

/-- Along a chart, whether the orienting coordinate `φ z` increases at `z` is locally constant in
the coordinate of `z`. -/
private theorem IsOrientingCoordinates.exists_increasesAt_iff (hφ : IsOrientingCoordinates U φ)
    {y : M} (hye : y ∈ e.source) :
    ∃ η > 0, ∀ z ∈ e.source, |(e z).val 0 - (e y).val 0| < η →
      (IncreasesAt e (φ z) z ↔ IncreasesAt e (φ y) y) := by
  obtain ⟨η, hη, hball, hmono, hanti⟩ := exists_strictMonoOn_of_increasesAt (hφ.isOpen y)
    (hφ.continuousOn y) (hφ.injOn y) (hφ.mem y) hye
  refine ⟨η, hη, fun z hze hzy ↦ ?_⟩
  set t := (e y).val 0
  set t' := (e z).val 0
  have hzt : e.symm (normalRay t') = z := symm_normalRay_coord hze
  have hzU : z ∈ U y := hzt ▸ (hball t' hzy.le).2
  obtain ⟨η', hη', -, hmono', hanti'⟩ := exists_strictMonoOn_of_increasesAt (hφ.isOpen z)
    (hφ.continuousOn z) (hφ.injOn z) (hφ.mem z) hze
  set δ := min η' (η - |t' - t|)
  have hδ : 0 < δ := lt_min hη' (by linarith)
  -- A coordinate `s` just above `t'` at which the coordinates `φ y` and `φ z` are compared.
  obtain ⟨s, ⟨hts, hsδ⟩, hcoh⟩ :=
    ((show ∀ᶠ s in 𝓝[>] t', s ∈ Ioo t' (t' + δ) from Ioo_mem_nhdsGT (by linarith)).and
      ((tendsto_symm_normalRay hze).eventually (hφ.coherent y z z ⟨hzU, hφ.mem z⟩))).exists
  have hδη' := min_le_left η' (η - |t' - t|)
  have hδη := min_le_right η' (η - |t' - t|)
  have ht' : 0 ≤ t' := (e z).property
  have hI : ∀ r, t' ≤ r → r ≤ s → r ∈ Icc (max (t - η) 0) (t + η) := fun r h₁ h₂ ↦
    ⟨max_le (by linarith [neg_abs_le (t' - t)]) (by linarith),
      by linarith [le_abs_self (t' - t)]⟩
  have hI' : ∀ r, t' ≤ r → r ≤ s → r ∈ Icc (max (t' - η') 0) (t' + η') := fun r h₁ h₂ ↦
    ⟨max_le (by linarith) (by linarith), by linarith⟩
  have h₁ := (lt_iff_of_strictMonoOn_of_strictAntiOn hmono hanti (hI t' le_rfl hts.le)
    (hI s hts.le le_rfl) hts).1
  have h₂ := (lt_iff_of_strictMonoOn_of_strictAntiOn hmono' hanti' (hI' t' le_rfl hts.le)
    (hI' s hts.le le_rfl) hts).1
  simp only [hzt] at h₁ h₂
  exact h₂.symm.trans (hcoh.symm.trans h₁)

/-- Along a chart, whether the orienting coordinate `φ z` increases at `z` is the same at all
points `z` of a preconnected subset of the chart domain. -/
private theorem IsOrientingCoordinates.increasesAt_iff_of_isPreconnected
    (hφ : IsOrientingCoordinates U φ) {K : Set M} (hK : IsPreconnected K) (hKe : K ⊆ e.source)
    {z z' : M} (hz : z ∈ K) (hz' : z' ∈ K) :
    IncreasesAt e (φ z) z ↔ IncreasesAt e (φ z') z' := by
  classical
  have hcont : ContinuousOn (fun w ↦ decide (IncreasesAt e (φ w) w)) K := fun w hw ↦ by
    obtain ⟨η, hη, h⟩ := hφ.exists_increasesAt_iff (hKe hw)
    refine ((continuousAt_const : ContinuousAt (fun _ ↦ decide (IncreasesAt e (φ w) w)) w).congr
      ?_).continuousWithinAt
    filter_upwards [coord_mem_nhds (hKe hw) hη] with v hv
    simp only [h v hv.1 hv.2]
  simpa using hK.constant hcont hz hz'

/-- At a point of coordinate `0`, a function continuous and injective nearby has a local minimum
exactly when it increases along the chart, and a local maximum exactly when it does not. -/
private theorem isLocalMin_iff_increasesAt {V : Set M} (hV : IsOpen V) {ψ : M → ℝ}
    (hψc : ContinuousOn ψ V) (hψi : InjOn ψ V) {y : M} (hyV : y ∈ V) (hye : y ∈ e.source)
    (hy0 : (e y).val 0 = 0) :
    (IsLocalMin ψ y ↔ IncreasesAt e ψ y) ∧ (IsLocalMax ψ y ↔ ¬IncreasesAt e ψ y) := by
  obtain ⟨η, hη, -, hmono, hanti⟩ := exists_strictMonoOn_of_increasesAt hV hψc hψi hyV hye
  simp only [hy0, zero_sub, zero_add, max_eq_right (neg_nonpos.2 hη.le)] at hmono hanti
  have h0 : (0 : ℝ) ∈ Icc 0 η := ⟨le_rfl, hη.le⟩
  have hy : ψ y = ψ (e.symm (normalRay 0)) := by rw [← hy0, symm_normalRay_coord hye]
  -- Near `y`, every point is read at a coordinate in `[0, η]`.
  have hW : ∀ᶠ w in 𝓝 y, (e w).val 0 ∈ Icc 0 η ∧ ψ w = ψ (e.symm (normalRay ((e w).val 0))) := by
    filter_upwards [coord_mem_nhds hye hη] with w hw
    have hwη : |(e w).val 0 - (e y).val 0| < η := hw.2
    rw [hy0, sub_zero, abs_of_nonneg (e w).property] at hwη
    exact ⟨⟨(e w).property, hwη.le⟩, by rw [symm_normalRay_coord hw.1]⟩
  -- Just above the coordinate `0`, the normal ray stays near `y` and in `(0, η]`.
  have hR : ∀ᶠ s in 𝓝[>] (e y).val 0, s ∈ Icc 0 η ∧ 0 < s := by
    rw [hy0]
    filter_upwards [Ioo_mem_nhdsGT hη] with s hs
    exact ⟨⟨hs.1.le, hs.2.le⟩, hs.1⟩
  have hγ := tendsto_symm_normalRay hye
  by_cases hinc : IncreasesAt e ψ y
  · have hmin : IsLocalMin ψ y := by
      filter_upwards [hW] with w hw
      rw [hy, hw.2]
      exact ((hmono hinc).le_iff_le h0 hw.1).2 hw.1.1
    refine ⟨iff_of_true hmin hinc, iff_of_false (fun hmax ↦ ?_) (not_not.2 hinc)⟩
    obtain ⟨s, hs, hle⟩ := (hinc.and (hγ.eventually hmax)).exists
    exact (lt_irrefl _) (hs.trans_le hle)
  · have hmax : IsLocalMax ψ y := by
      filter_upwards [hW] with w hw
      rw [hy, hw.2]
      exact ((hanti hinc).le_iff_ge hw.1 h0).2 hw.1.1
    refine ⟨iff_of_false (fun hmin ↦ ?_) hinc, iff_of_true hmax hinc⟩
    obtain ⟨s, ⟨hsI, hs⟩, hle⟩ := (hR.and (hγ.eventually hmin)).exists
    have : ψ (e.symm (normalRay s)) < ψ (e.symm (normalRay 0)) := hanti hinc h0 hsI hs
    rw [← hy] at this
    exact (lt_irrefl _) (this.trans_le hle)

end Orientation

section OrientedParity

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  {U : M → Set M} {φ : M → M → ℝ}

/-- An end of an arc is a *tail* when the orientation leaves its point into the arc: for a side
`J p c` of a point `p` of `P`, when `φ p` exceeds its value at `p` on that side near `p`; for a
boundary point `y`, when `y` is a local minimum of `φ y`. -/
private def CutData.IsTail (D : CutData M) (φ : M → M → ℝ) : M × Bool ⊕ M → Prop
  | .inl (p, c) => ∀ᶠ w in 𝓝 p, w ∈ D.J p c → φ p p < φ p w
  | .inr y => IsLocalMin (φ y) y

/-- **Tails of an arc.** Let `z₀` be a point of an arc `K`, read in the chart `e`. An end of `K` is
a tail exactly when the orientation increases along `e` at `z₀` if and only if the end lies at the
lower end of the interval of coordinates of `K`. -/
private theorem CutData.isTail_iff [T2Space M] (D : CutData M) (hB : ((𝓡∂ 1).boundary M).Finite)
    (hφ : IsOrientingCoordinates U φ) {ω₀ : M × Bool ⊕ M}
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)} {α β : ℝ}
    (h : IsArcIn e α β (D.arcOf ω₀)) {z₀ : M} (hz₀ : z₀ ∈ D.arcOf ω₀) {ω : M × Bool ⊕ M}
    (hω : ω ∈ (D.ends hB.toFinset).filter (fun ω ↦ D.arcOf ω = D.arcOf ω₀)) :
    D.IsTail φ ω ↔ (IncreasesAt e (φ z₀) z₀ ↔
      (e (Sum.elim Prod.fst id ω)).val 0 = sInf ((fun z ↦ (e z).val 0) '' D.arcOf ω₀)) := by
  set K := D.arcOf ω₀
  set I := (fun z ↦ (e z).val 0) '' K with hI
  have hKe : K ⊆ e.source := fun z hz ↦ (h.mem z hz).1
  rcases ω with ⟨p, c⟩ | y <;> rw [Finset.mem_filter] at hω
  · have hp : p ∈ D.P := by simpa [CutData.ends] using hω.1
    obtain ⟨hJ, hpe, hpI, hpend⟩ := D.inl_end h
      (subset_compl_iff_disjoint_right.1 (connectedComponentIn_subset _ _)) hp hω.2
    -- The arc lies above `p` in the chart if `p` is its lower end, and below `p` otherwise.
    have hS : ∀ w ∈ D.J p c, w ∈ e.source ∧ ((e p).val 0 < (e w).val 0 ∧ (e p).val 0 = sInf I ∨
        (e w).val 0 < (e p).val 0 ∧ ¬(e p).val 0 = sInf I) := by
      intro w hw
      have hwI : (e w).val 0 ∈ I := mem_image_of_mem _ (hJ hw)
      have hne : (e w).val 0 ≠ (e p).val 0 := fun h' ↦ hpI (h' ▸ hwI)
      refine ⟨hKe (hJ hw), ?_⟩
      rcases hpend with h' | h'
      · exact Or.inl ⟨lt_of_le_of_ne (h' ▸ csInf_le h.bddBelow hwI) hne.symm, h'⟩
      · exact Or.inr ⟨lt_of_le_of_ne (h' ▸ le_csSup h.bddAbove hwI) hne,
          fun h'' ↦ h.sInf_lt_sSup.ne (h''.symm.trans h')⟩
    have hpcl : p ∈ closure (D.J p c) := (D.sides p hp).mem_closure c
    -- The direction at `p` is the direction along the arc.
    obtain ⟨η, hη, hloc⟩ := hφ.exists_increasesAt_iff hpe
    obtain ⟨z, ⟨hze, hzη⟩, hzK⟩ :=
      mem_closure_iff_nhds.1 (closure_mono hJ hpcl) _ (coord_mem_nhds hpe hη)
    rw [CutData.IsTail, eventually_lt_iff_increasesAt (hφ.isOpen p) (hφ.continuousOn p)
      (hφ.injOn p) (hφ.mem p) hpe hpcl hS, ← hloc z hze hzη,
      hφ.increasesAt_iff_of_isPreconnected h.isPreconnected hKe hzK hz₀, Sum.elim_inl]
  · have hy : y ∈ (𝓡∂ 1).boundary M := by simpa [CutData.ends] using hω.1
    obtain ⟨hyK, -, hyI⟩ := D.inr_end h hy hω.2
    rw [← hI] at hyI
    have hye := hKe hyK
    rw [CutData.IsTail, (isLocalMin_iff_increasesAt (hφ.isOpen y) (hφ.continuousOn y)
      (hφ.injOn y) (hφ.mem y) hye
      ((ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff hye).1 hy)).1,
      hφ.increasesAt_iff_of_isPreconnected h.isPreconnected hKe hyK hz₀, Sum.elim_inr, id_eq,
      hyI, eq_self_iff_true, iff_true]

/-- Two signs `±1`, positive exactly when the corresponding one of two exclusive and exhaustive
propositions holds, add up to `0`. -/
private theorem ite_add_ite_eq_zero {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ ¬Q) :
    ((if P then 1 else -1 : ℤ) + if Q then 1 else -1) = 0 := by
  by_cases hQ : Q <;> simp [hQ, h]

open scoped Classical in
/-- **Every arc has one tail and one head.** For the orientation given by the coordinates `φ`,
exactly one of the two ends of an arc is a tail: counting tails with `1` and the other ends with
`-1`, the ends of an arc add up to `0`. -/
private theorem CutData.sum_filter_arcOf_isTail [T2Space M] (D : CutData M)
    (hB : ((𝓡∂ 1).boundary M).Finite) (hφ : IsOrientingCoordinates U φ) {ω₀ : M × Bool ⊕ M}
    (hω₀ : ω₀ ∈ D.ends hB.toFinset) :
    ∑ ω ∈ (D.ends hB.toFinset).filter (fun ω ↦ D.arcOf ω = D.arcOf ω₀),
      (if D.IsTail φ ω then (1 : ℤ) else -1) = 0 := by
  obtain ⟨e, α, β, h⟩ := D.arc _ (D.base_notMem (fun y hy ↦ hB.mem_toFinset.1 hy) hω₀)
  obtain ⟨hinj, himage⟩ := D.injOn_and_image_filter_arcOf hB h
  obtain ⟨z₀, hz₀⟩ := h.nonempty
  set I := (fun z ↦ (e z).val 0) '' D.arcOf ω₀
  set v : M × Bool ⊕ M → ℝ := fun ω ↦ (e (Sum.elim Prod.fst id ω)).val 0
  set F := (D.ends hB.toFinset).filter (fun ω ↦ D.arcOf ω = D.arcOf ω₀)
  -- The arc has two ends, one at each end of its interval of coordinates.
  have hcard : F.card = 2 := D.card_filter_arcOf_eq_two hB hω₀
  obtain ⟨a, b, hab, hF⟩ := Finset.card_eq_two.1 hcard
  have ha : a ∈ F := by rw [hF]; exact Finset.mem_insert_self a {b}
  have hb : b ∈ F := by rw [hF]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have hva : v a = sInf I ∨ v a = sSup I := by
    simpa [himage] using Finset.mem_image_of_mem v ha
  have hvb : v b = sInf I ∨ v b = sSup I := by
    simpa [himage] using Finset.mem_image_of_mem v hb
  have hvab : v a ≠ v b := fun h' ↦ hab (hinj (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) h')
  have hne := h.sInf_lt_sSup.ne
  have hxor : v a = sInf I ↔ ¬v b = sInf I := by
    rcases hva with hva | hva <;> rcases hvb with hvb | hvb
    · exact absurd (hva.trans hvb.symm) hvab
    · exact iff_of_true hva fun h' ↦ hne (h'.symm.trans hvb)
    · exact iff_of_false (fun h' ↦ hne (h'.symm.trans hva)) (not_not.2 hvb)
    · exact absurd (hva.trans hvb.symm) hvab
  -- Exactly one of the two ends is a tail.
  have htail : D.IsTail φ a ↔ ¬D.IsTail φ b := by
    simp only [v] at hxor
    rw [D.isTail_iff hB hφ h hz₀ ha, D.isTail_iff hB hφ h hz₀ hb, hxor]
    tauto
  rw [hF, Finset.sum_pair hab]
  exact ite_add_ite_eq_zero htail

end OrientedParity

section Main

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]

/-- **At a boundary point, an orientation points either out or in.** At a boundary point `x` of a
one-dimensional manifold oriented by coordinates `φ`, the coordinate `φ x` has a local maximum,
where the orientation points out of `M`, exactly when it has no local minimum, where the
orientation points into `M`. -/
theorem IsOrientingCoordinates.isLocalMax_iff_not_isLocalMin {U : M → Set M} {φ : M → M → ℝ}
    (hφ : IsOrientingCoordinates U φ) {x : M} (hx : x ∈ (𝓡∂ 1).boundary M) :
    IsLocalMax (φ x) x ↔ ¬IsLocalMin (φ x) x := by
  have hxe := mem_chart_source (EuclideanHalfSpace 1) x
  obtain ⟨hmin, hmax⟩ := isLocalMin_iff_increasesAt (hφ.isOpen x) (hφ.continuousOn x)
    (hφ.injOn x) (hφ.mem x) hxe
    ((ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff hxe).1 hx)
  rw [hmax, hmin]

/-- **Whether an orientation points out does not depend on the coordinate.** At a boundary point
`x` of a one-dimensional manifold oriented by coordinates `φ`, every coordinate `φ y` defined at `x`
has a local maximum there exactly when `φ x` does. -/
theorem IsOrientingCoordinates.isLocalMax_iff_of_mem {U : M → Set M} {φ : M → M → ℝ}
    (hφ : IsOrientingCoordinates U φ) {x y : M} (hx : x ∈ (𝓡∂ 1).boundary M) (hxy : x ∈ U y) :
    IsLocalMax (φ x) x ↔ IsLocalMax (φ y) x := by
  have hxe := mem_chart_source (EuclideanHalfSpace 1) x
  have hx0 := (ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff hxe).1 hx
  rw [(isLocalMin_iff_increasesAt (hφ.isOpen x) (hφ.continuousOn x) (hφ.injOn x) (hφ.mem x) hxe
      hx0).2, (isLocalMin_iff_increasesAt (hφ.isOpen y) (hφ.continuousOn y) (hφ.injOn y) hxy hxe
      hx0).2, hφ.increasesAt_iff_increasesAt ⟨hφ.mem x, hxy⟩ hxe]

/-- **Whether an orientation points in does not depend on the coordinate.** At a boundary point
`x` of a one-dimensional manifold oriented by coordinates `φ`, every coordinate `φ y` defined at `x`
has a local minimum there exactly when `φ x` does. -/
theorem IsOrientingCoordinates.isLocalMin_iff_of_mem {U : M → Set M} {φ : M → M → ℝ}
    (hφ : IsOrientingCoordinates U φ) {x y : M} (hx : x ∈ (𝓡∂ 1).boundary M) (hxy : x ∈ U y) :
    IsLocalMin (φ x) x ↔ IsLocalMin (φ y) x := by
  have hxe := mem_chart_source (EuclideanHalfSpace 1) x
  have hx0 := (ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff hxe).1 hx
  rw [(isLocalMin_iff_increasesAt (hφ.isOpen x) (hφ.continuousOn x) (hφ.injOn x) (hφ.mem x) hxe
      hx0).1, (isLocalMin_iff_increasesAt (hφ.isOpen y) (hφ.continuousOn y) (hφ.injOn y) hxy hxe
      hx0).1, hφ.increasesAt_iff_increasesAt ⟨hφ.mem x, hxy⟩ hxe]

/-- **A compact oriented one-dimensional manifold has as many outgoing as incoming boundary
points.** Let `M` be a compact Hausdorff topological manifold modelled on the half-line
`EuclideanHalfSpace 1`, oriented by local coordinates `φ`. The boundary points at which the
orientation points out of `M`, the local maxima of `φ x`, are as many as those at which it points
into `M`, the local minima of `φ x`. Every boundary point is of exactly one of these two kinds
(`TauCeti.IsOrientingCoordinates.isLocalMax_iff_not_isLocalMin`), so this refines
`TauCeti.ModelWithCorners.even_ncard_boundary_euclideanHalfSpace_one`. No smoothness of the atlas
or of the coordinates is assumed. -/
theorem ModelWithCorners.ncard_setOf_isLocalMax_eq_ncard_setOf_isLocalMin [CompactSpace M]
    [T2Space M] {U : M → Set M} {φ : M → M → ℝ} (hφ : IsOrientingCoordinates U φ) :
    {x ∈ (𝓡∂ 1).boundary M | IsLocalMax (φ x) x}.ncard =
      {x ∈ (𝓡∂ 1).boundary M | IsLocalMin (φ x) x}.ncard := by
  classical
  obtain ⟨D⟩ := nonempty_cutData (M := M)
  have hB := ModelWithCorners.finite_boundary_euclideanHalfSpace_one (M := M)
  set g : M × Bool ⊕ M → ℤ := fun ω ↦ if D.IsTail φ ω then 1 else -1
  -- Grouped by arcs, the signs of the ends add up to zero.
  have hsum : ∑ ω ∈ D.ends hB.toFinset, g ω = 0 := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun ω hω ↦ Finset.mem_image_of_mem D.arcOf hω)]
    refine Finset.sum_eq_zero fun K hK ↦ ?_
    obtain ⟨ω₀, hω₀, rfl⟩ := Finset.mem_image.1 hK
    simp only [g]
    exact D.sum_filter_arcOf_isTail hB hφ hω₀
  -- The two sides of each point of `P` have opposite signs.
  have hP : ∑ pc ∈ D.finite.toFinset ×ˢ (Finset.univ : Finset Bool), g (.inl pc) = 0 := by
    rw [Finset.sum_product]
    refine Finset.sum_eq_zero fun p hp ↦ ?_
    have hopp : D.IsTail φ (.inl (p, true)) ↔ ¬D.IsTail φ (.inl (p, false)) := by
      simp only [CutData.IsTail]
      exact (D.sides p (D.finite.mem_toFinset.1 hp)).opposite (hφ.isOpen p) (hφ.mem p)
        (hφ.continuousOn p) (hφ.injOn p)
    simp only [g, Fintype.sum_bool]
    exact ite_add_ite_eq_zero hopp
  -- So on the boundary the local minima, of sign `1`, cancel the other points, of sign `-1`.
  rw [CutData.ends, Finset.sum_disjSum, hP, zero_add] at hsum
  have hcount : (hB.toFinset.filter fun x ↦ IsLocalMin (φ x) x).card =
      (hB.toFinset.filter fun x ↦ ¬IsLocalMin (φ x) x).card := by
    simp only [g] at hsum
    have h' : ∑ y ∈ hB.toFinset, (if IsLocalMin (φ y) y then (1 : ℤ) else -1) = 0 :=
      (Finset.sum_congr rfl fun y _ ↦ if_congr (by rw [CutData.IsTail]) rfl rfl).trans hsum
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const] at h'
    simp only [nsmul_eq_mul, mul_one, mul_neg] at h'
    omega
  have hconv (q : M → Prop) :
      {x ∈ (𝓡∂ 1).boundary M | q x}.ncard = (hB.toFinset.filter q).card := by
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    simp only [Set.Finite.mem_toFinset]
  rw [hconv, hconv, hcount,
    Finset.filter_congr fun x hx ↦ hφ.isLocalMax_iff_not_isLocalMin (hB.mem_toFinset.1 hx)]

end Main

section LocalModels

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {B : Set X}

/-- **At an endpoint, an orientation points either out or in.** For a space `X` described by local
models as in `TauCeti.exists_chartedSpace_euclideanHalfSpace_one_boundary_eq` and oriented by
local coordinates `φ`, at each point `x ∈ B` the coordinate `φ x` has a local maximum exactly
when it has no local minimum. -/
theorem IsOrientingCoordinates.isLocalMax_iff_not_isLocalMin_of_forall_exists_homeomorph_Ico
    (hF : Module.finrank ℝ F = 1)
    (hB : ∀ x ∈ B, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x)
    (hX : ∀ x ∉ B, ∃ N ∈ 𝓝 x, ∃ V : Set F, IsOpen V ∧ Nonempty (V ≃ₜ N)) {U : X → Set X}
    {φ : X → X → ℝ} (hφ : IsOrientingCoordinates U φ) {x : X} (hx : x ∈ B) :
    IsLocalMax (φ x) x ↔ ¬IsLocalMin (φ x) x := by
  obtain ⟨C, hC⟩ := exists_chartedSpace_euclideanHalfSpace_one_boundary_eq hF hB hX
  exact hφ.isLocalMax_iff_not_isLocalMin (hC ▸ hx)

/-- **At an endpoint, whether an orientation points out does not depend on the coordinate.** For a
space `X` described by local models as in
`TauCeti.exists_chartedSpace_euclideanHalfSpace_one_boundary_eq` and oriented by local coordinates
`φ`, at each point `x ∈ B` every coordinate `φ y` defined at `x` has a local maximum there exactly
when `φ x` does. -/
theorem
    IsOrientingCoordinates.isLocalMax_iff_of_mem_of_forall_exists_homeomorph_Ico
    (hF : Module.finrank ℝ F = 1)
    (hB : ∀ x ∈ B, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x)
    (hX : ∀ x ∉ B, ∃ N ∈ 𝓝 x, ∃ V : Set F, IsOpen V ∧ Nonempty (V ≃ₜ N)) {U : X → Set X}
    {φ : X → X → ℝ} (hφ : IsOrientingCoordinates U φ) {x y : X} (hx : x ∈ B) (hxy : x ∈ U y) :
    IsLocalMax (φ x) x ↔ IsLocalMax (φ y) x := by
  obtain ⟨C, hC⟩ := exists_chartedSpace_euclideanHalfSpace_one_boundary_eq hF hB hX
  exact hφ.isLocalMax_iff_of_mem (hC ▸ hx) hxy

/-- **At an endpoint, whether an orientation points in does not depend on the coordinate.** For a
space `X` described by local models as in
`TauCeti.exists_chartedSpace_euclideanHalfSpace_one_boundary_eq` and oriented by local coordinates
`φ`, at each point `x ∈ B` every coordinate `φ y` defined at `x` has a local minimum there exactly
when `φ x` does. -/
theorem
    IsOrientingCoordinates.isLocalMin_iff_of_mem_of_forall_exists_homeomorph_Ico
    (hF : Module.finrank ℝ F = 1)
    (hB : ∀ x ∈ B, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x)
    (hX : ∀ x ∉ B, ∃ N ∈ 𝓝 x, ∃ V : Set F, IsOpen V ∧ Nonempty (V ≃ₜ N)) {U : X → Set X}
    {φ : X → X → ℝ} (hφ : IsOrientingCoordinates U φ) {x y : X} (hx : x ∈ B) (hxy : x ∈ U y) :
    IsLocalMin (φ x) x ↔ IsLocalMin (φ y) x := by
  obtain ⟨C, hC⟩ := exists_chartedSpace_euclideanHalfSpace_one_boundary_eq hF hB hX
  exact hφ.isLocalMin_iff_of_mem (hC ▸ hx) hxy

/-- **A compact oriented space locally modelled on the half-line has as many outgoing as incoming
endpoints.** Let `X` be compact and Hausdorff, and let `B` be a set of points of `X` such that

* each `x ∈ B` has a neighbourhood `N` with a homeomorphism `[0, ε) ≃ₜ N` sending `0` to `x`, and
* each `x ∉ B` has a neighbourhood homeomorphic to an open subset of a one-dimensional real
  normed space `F`.

If local coordinates `φ` orient `X`, then the points of `B` at which `φ x` has a local maximum,
where the orientation points out of `X`, are as many as those at which it has a local minimum,
where it points into `X`. This is
`TauCeti.ModelWithCorners.ncard_setOf_isLocalMax_eq_ncard_setOf_isLocalMin` for a space described
by local homeomorphisms rather than by an atlas, and the oriented refinement of
`TauCeti.even_ncard_of_forall_exists_homeomorph_Ico`. For an oriented compactified space of
index-two trajectories, `B` is the set of broken trajectories. -/
theorem ncard_setOf_isLocalMax_eq_ncard_setOf_isLocalMin_of_forall_exists_homeomorph_Ico
    [CompactSpace X] [T2Space X] (hF : Module.finrank ℝ F = 1)
    (hB : ∀ x ∈ B, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x)
    (hX : ∀ x ∉ B, ∃ N ∈ 𝓝 x, ∃ V : Set F, IsOpen V ∧ Nonempty (V ≃ₜ N)) {U : X → Set X}
    {φ : X → X → ℝ} (hφ : IsOrientingCoordinates U φ) :
    {x ∈ B | IsLocalMax (φ x) x}.ncard = {x ∈ B | IsLocalMin (φ x) x}.ncard := by
  obtain ⟨C, hC⟩ := exists_chartedSpace_euclideanHalfSpace_one_boundary_eq hF hB hX
  subst hC
  exact ModelWithCorners.ncard_setOf_isLocalMax_eq_ncard_setOf_isLocalMin hφ

end LocalModels

end TauCeti
