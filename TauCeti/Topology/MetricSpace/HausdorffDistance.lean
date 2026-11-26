/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Order.Compact

/-!
# Distances to sets

For a nonempty set in a pseudometric space, the extended distance `Metric.infEDist x S` equals
`ENNReal.ofReal t` for some `t ≥ 0` exactly when the real distance `Metric.infDist x S` equals `t`
(`Metric.infEDist_eq_ofReal_iff`). For any two sets `S` and `T` in a pseudometric space, the real
infimum `sInf ((fun z ↦ infDist z T) '' S)` agrees with `(⨅ z ∈ S, ⨅ ζ ∈ T, edist z ζ).toReal`
(`Metric.sInf_image_infDist_eq_toReal_biInf`), including when `S` or `T` is empty.
In a seminormed group, `Metric.infDist x s` is the infimum of the norms `‖x - y‖` over `y ∈ s`
(`Metric.infDist_eq_iInf_norm_sub`).

Hausdorff convergence to zero passes along chains of sets: if `A i` approaches `B i` and `B i`
approaches `Z` in the Hausdorff extended distance, then `A i` approaches `Z`
(`Metric.tendsto_hausdorffEDist_of_tendsto_of_tendsto`). If sets `A i` approach a closed set `Z`,
every limit of points `y i ∈ A i` lies in `Z` (`Metric.mem_of_tendsto_hausdorffEDist`).

A `K`-Lipschitz map with `K ≠ 0` multiplies the extended distance from a point to a set, and the
Hausdorff extended distance between two sets, by at most `K`
(`LipschitzWith.infEDist_image_le`, `LipschitzWith.hausdorffEDist_image_le`). This is what makes
the union-of-images operator of an iterated function system a contraction.

A continuous map from a nonempty compact space into a pseudometric space has a nearest point to
every point: some value of the map minimises the distance to it
(`Continuous.exists_isMinOn_dist`).

Membership in an open set at the zeros of a map `d` is uniform on a compact set: if `A x` lies in
an open set `O` wherever `d x = 0` on a compact `K`, with `d` and `A` continuous on `K`, then every
point close to `A x` at a point `x ∈ K` where `d x` is small lies in `O`
(`IsCompact.exists_pos_forall_mem_of_norm_le`). The proof bounds `‖d x‖ + infDist (A x) Oᶜ` below
on `K`.

For an isometry `ι : Z → E` and a dense set `D ⊆ Z`, every point `y : E` has a point `z ∈ D`
whose distance to each `s : Z` is at most `2 * dist (ι s) y` plus any prescribed positive slack
(`Isometry.exists_mem_dist_le_two_mul_dist_add`). This brings an approximation made in the ambient
space `E` back to `D`.
-/

public section

open Filter Set Topology
open scoped ENNReal NNReal

namespace Metric

/-- For a nonempty set in a pseudometric space, the extended distance to it equals a nonnegative
real number exactly when the real distance does. -/
theorem infEDist_eq_ofReal_iff {X : Type*} [PseudoMetricSpace X] {x : X} {S : Set X}
    {t : ℝ} (hS : S.Nonempty) (ht : 0 ≤ t) :
    infEDist x S = ENNReal.ofReal t ↔ infDist x S = t := by
  constructor
  · intro h
    rw [infDist, h, ENNReal.toReal_ofReal ht]
  · intro h
    rw [← h, infDist, ENNReal.ofReal_toReal (infEDist_ne_top hS)]

/-- For any subsets `S` and `T` of a pseudometric space, the infimum over `z ∈ S` of the ordinary
distance `infDist z T` equals `(⨅ z ∈ S, ⨅ ζ ∈ T, edist z ζ).toReal` (evaluating to `0` on both
sides when `S` or `T` is empty). -/
theorem sInf_image_infDist_eq_toReal_biInf {X : Type*} [PseudoMetricSpace X] (S T : Set X) :
    sInf ((fun z ↦ infDist z T) '' S) = (⨅ z ∈ S, ⨅ ζ ∈ T, edist z ζ).toReal := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp [hS.image_const]
  · simp_rw [sInf_image', infDist, iInf_subtype',
      ← ENNReal.toReal_iInf (fun _ : S ↦ infEDist_ne_top hT), infEDist, iInf_subtype']

/-- `Metric.infDist x s` as an infimum of norms: the norm form of `Metric.infDist_eq_iInf`. -/
theorem infDist_eq_iInf_norm_sub {E : Type*} [SeminormedAddCommGroup E] {s : Set E} {x : E} :
    infDist x s = ⨅ y : s, ‖x - y‖ := by
  simp [infDist_eq_iInf, dist_eq_norm]

variable {X ι : Type*} [PseudoEMetricSpace X] {l : Filter ι}

/-- If sets `A i` approach `B i` and `B i` approach `Z` in the Hausdorff extended distance, then
`A i` approach `Z`. -/
theorem tendsto_hausdorffEDist_of_tendsto_of_tendsto {A B : ι → Set X} {Z : Set X}
    (hAB : Tendsto (fun i ↦ hausdorffEDist (A i) (B i)) l (𝓝 0))
    (hBZ : Tendsto (fun i ↦ hausdorffEDist (B i) Z) l (𝓝 0)) :
    Tendsto (fun i ↦ hausdorffEDist (A i) Z) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hAB.add hBZ)
    (fun _ ↦ zero_le) fun _ ↦ hausdorffEDist_triangle

/-- If sets `A i` approach a closed set `Z` in the Hausdorff extended distance, then every limit
of points `y i ∈ A i` lies in `Z`. -/
theorem mem_of_tendsto_hausdorffEDist [l.NeBot] {A : ι → Set X} {Z : Set X} (hZ : IsClosed Z)
    (hA : Tendsto (fun i ↦ hausdorffEDist (A i) Z) l (𝓝 0)) {y : ι → X}
    (hy : ∀ᶠ i in l, y i ∈ A i) {y₀ : X} (hy₀ : Tendsto y l (𝓝 y₀)) : y₀ ∈ Z := by
  -- `infEDist y₀ Z ≤ edist y₀ (y i) + hausdorffEDist (A i) Z`, and both terms tend to zero.
  have hlim : Tendsto (fun i ↦ edist y₀ (y i) + hausdorffEDist (A i) Z) l (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := y₀)).edist hy₀).add hA
  rw [mem_iff_infEDist_zero_of_closed hZ, ← nonpos_iff_eq_zero]
  refine ge_of_tendsto hlim ?_
  filter_upwards [hy] with i hi
  exact infEDist_le_edist_add_infEDist.trans
    (add_le_add le_rfl (infEDist_le_hausdorffEDist_of_mem hi))

end Metric

namespace LipschitzWith

open Metric

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {K : ℝ≥0} {f : X → Y}

/-- A `K`-Lipschitz map with `K ≠ 0` multiplies the extended distance from a point to a set by at
most `K`. (For `K = 0` and the empty set the right side would be `0 * ∞ = 0`.) -/
theorem infEDist_image_le (hf : LipschitzWith K f) (hK : K ≠ 0) (x : X) (s : Set X) :
    infEDist (f x) (f '' s) ≤ K * infEDist x s := by
  have hK' : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK
  simp only [infEDist, iInf_image]
  rw [ENNReal.mul_iInf_of_ne hK' ENNReal.coe_ne_top]
  refine iInf_mono fun y ↦ ?_
  rw [ENNReal.mul_iInf_of_ne hK' ENNReal.coe_ne_top]
  exact iInf_mono fun _ ↦ hf x y

/-- A `K`-Lipschitz map with `K ≠ 0` multiplies the Hausdorff extended distance between two sets
by at most `K`. -/
theorem hausdorffEDist_image_le (hf : LipschitzWith K f) (hK : K ≠ 0) (s t : Set X) :
    hausdorffEDist (f '' s) (f '' t) ≤ K * hausdorffEDist s t := by
  refine hausdorffEDist_le_of_infEDist ?_ ?_ <;> rintro _ ⟨x, hx, rfl⟩
  · exact (hf.infEDist_image_le hK x t).trans
      (mul_le_mul_right (infEDist_le_hausdorffEDist_of_mem hx) _)
  · rw [hausdorffEDist_comm]
    exact (hf.infEDist_image_le hK x s).trans
      (mul_le_mul_right (infEDist_le_hausdorffEDist_of_mem hx) _)

end LipschitzWith

/-- A continuous map `g` from a nonempty compact space into a pseudometric space has a nearest point
to every `y`: some value `g x` minimises the distance from `y` to the values of `g`. -/
theorem Continuous.exists_isMinOn_dist {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] [PseudoMetricSpace Y] {g : X → Y} (hg : Continuous g) (y : Y) :
    ∃ x, IsMinOn (fun z => dist y (g z)) univ x := by
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    ((continuous_const (y := y)).dist hg).continuousOn
  exact ⟨x, hx⟩

open Metric in
/-- **Membership in an open set near the zeros of a map is uniform on a compact set.**

Let `d` and `A` be continuous on a compact set `K`, where `A` takes values in a pseudometric space,
and let `A x` lie in an open set `O` at every zero `x ∈ K` of `d`. Then there is `δ > 0` such that,
at every point `x ∈ K` with `‖d x‖ ≤ δ`, every point within `δ` of `A x` lies in `O`. -/
theorem IsCompact.exists_pos_forall_mem_of_norm_le {X F Y : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [PseudoMetricSpace Y] {K : Set X} (hK : IsCompact K) {d : X → F}
    {A : X → Y} (hd : ContinuousOn d K) (hA : ContinuousOn A K) {O : Set Y} (hO : IsOpen O)
    (h : ∀ x ∈ K, d x = 0 → A x ∈ O) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y, ‖d x‖ ≤ δ → dist y (A x) ≤ δ → y ∈ O := by
  -- The complement `S` of `O` is closed; if it is empty there is nothing to prove.
  set S : Set Y := Oᶜ
  have hS : IsClosed S := hO.isClosed_compl
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · exact ⟨1, one_pos, fun x _ y _ _ ↦ by simp [compl_empty_iff.1 hSe]⟩
  -- `φ x` is positive on `K`: at a zero of `d` the point `A x` lies outside `S`.
  set φ : X → ℝ := fun x ↦ ‖d x‖ + infDist (A x) S
  have hφ : ContinuousOn φ K := hd.norm.add ((continuous_infDist_pt S).comp_continuousOn hA)
  have hpos (x : X) (hx : x ∈ K) : 0 < φ x := by
    by_cases h₀ : d x = 0
    · have hx' := (hS.notMem_iff_infDist_pos hSne).1 fun hxS ↦ hxS (h x hx h₀)
      simpa [φ, h₀] using hx'
    · exact add_pos_of_pos_of_nonneg (norm_pos_iff.2 h₀) infDist_nonneg
  -- By compactness, `φ` has a positive lower bound `m` on `K`.
  obtain ⟨m, hm, hmK⟩ := hK.exists_forall_le' hφ hpos
  -- If `‖d x‖ ≤ m / 3`, then `A x` is at distance at least `2m / 3` from `S`, so a point of `S`
  -- cannot lie within `m / 3` of it.
  refine ⟨m / 3, by positivity, fun x hx y hdx hy ↦ ?_⟩
  by_contra hyS
  have hinf : infDist (A x) S ≤ dist y (A x) :=
    (infDist_le_dist_of_mem (hyS : y ∈ S)).trans_eq (dist_comm _ _)
  linarith [hmK x hx]

/-- For an isometry `ι : Z → E` of a nonempty space, a dense set `D ⊆ Z`, every `y : E` and every
`r > 0`, there is `z ∈ D` with `dist s z ≤ 2 * dist (ι s) y + r` for every `s : Z`. -/
theorem Isometry.exists_mem_dist_le_two_mul_dist_add {Z E : Type*} [PseudoMetricSpace Z]
    [PseudoMetricSpace E] [Nonempty Z] {ι : Z → E} (hι : Isometry ι) {D : Set Z} (hD : Dense D)
    (y : E) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ D, ∀ s, dist s z ≤ 2 * dist (ι s) y + r := by
  obtain ⟨_, ⟨s₀, rfl⟩, hs₀⟩ := (Metric.infDist_lt_iff (range_nonempty ι)).1
    (lt_add_of_pos_right (Metric.infDist y (range ι)) (half_pos hr))
  obtain ⟨z, hzD, hz⟩ := hD.exists_dist_lt s₀ (half_pos hr)
  refine ⟨z, hzD, fun s ↦ ?_⟩
  have h₁ := dist_triangle s s₀ z
  have h₂ := hι.dist_eq s s₀
  have h₃ := dist_triangle (ι s) y (ι s₀)
  have h₄ : Metric.infDist y (range ι) ≤ dist (ι s) y := by
    rw [dist_comm]
    exact Metric.infDist_le_dist_of_mem (mem_range_self s)
  linarith
