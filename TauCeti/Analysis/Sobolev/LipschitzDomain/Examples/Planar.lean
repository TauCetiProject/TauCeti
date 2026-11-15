/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.Normed.Lp.ProdLp.Rotation
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import TauCeti.Analysis.SpecialFunctions.Sqrt

/-!
# Planar examples and non-examples of Lipschitz domains

The open unit square `(0, 1)²` is a Lipschitz domain with constant `1`. Along the open edges a
translated and rotated chart `TauCeti.prodRecentredRotation` has the flat graph `0`; at a corner
a rotation by an odd multiple of `π / 4` turns the quarter-plane into the region above
`γ s = |s|`, which is `1`-Lipschitz.

Two standard planar sets fail the predicate. In a chart centred at a frontier point the domain
contains a whole cone above the centre and misses a whole cone below it, because the graph is
Lipschitz and passes through the centre (`Set.IsLipschitzChart.symm_mem_of_mul_norm_lt_fst` and
`Set.IsLipschitzChart.symm_notMem_of_fst_lt_neg_mul_norm`). The slit disc
`B(0, 1) ∖ [0, 1) × {0}` misses no open set near a slit point, so no chart is centred there. The
cusp `{(s, t) | √|s| < t}` contains no cone at the origin, so no chart, with any Lipschitz
constant, is centred there.

## Main declarations

* `TauCeti.openUnitSquare`, `TauCeti.slitUnitDisc`, `TauCeti.sqrtAbsCusp`: the three planar sets,
  with membership lemmas `TauCeti.mem_openUnitSquare`, `TauCeti.mem_slitUnitDisc` and
  `TauCeti.mem_sqrtAbsCusp`.
* `TauCeti.isLipschitzChartWith_openUnitSquare_zero`: the corner chart of the square at the
  origin, with graph `|s|` after the rotation by `π / 4`.
* `TauCeti.isLipschitzDomainWith_openUnitSquare`: the open unit square is a Lipschitz domain
  with constant `1`.
* `TauCeti.not_exists_isLipschitzChart_slitUnitDisc`,
  `TauCeti.not_isLipschitzDomain_slitUnitDisc`: no chart of the slit disc is centred at a slit
  point.
* `TauCeti.not_exists_isLipschitzChart_sqrtAbsCusp`, `TauCeti.not_isLipschitzDomain_sqrtAbsCusp`:
  no chart of the cusp is centred at the origin.

## References

* P. Grisvard, *Elliptic Problems in Nonsmooth Domains*, Definition 1.2.1.1.
-/

public section

noncomputable section

open Metric Set Topology
open scoped NNReal

namespace TauCeti

/-! ### The open unit square -/

/-- The open unit square `(0, 1)²` in the Euclidean plane. -/
def openUnitSquare : Set (WithLp 2 (ℝ × ℝ)) :=
  {x | x.fst ∈ Ioo 0 1 ∧ x.snd ∈ Ioo 0 1}

/-- Membership in the open unit square. -/
@[simp]
theorem mem_openUnitSquare {x : WithLp 2 (ℝ × ℝ)} :
    x ∈ openUnitSquare ↔ x.fst ∈ Ioo 0 1 ∧ x.snd ∈ Ioo 0 1 :=
  Iff.rfl

/-- The open unit square is open. -/
theorem isOpen_openUnitSquare : IsOpen openUnitSquare :=
  (isOpen_Ioo.preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst).inter
    (isOpen_Ioo.preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ).snd)

/-- The frontier of the open unit square lies in the closed square. -/
theorem mem_Icc_of_mem_frontier_openUnitSquare {x : WithLp 2 (ℝ × ℝ)}
    (hx : x ∈ frontier openUnitSquare) : x.fst ∈ Icc 0 1 ∧ x.snd ∈ Icc 0 1 := by
  refine closure_minimal (s := openUnitSquare)
    (t := {y : WithLp 2 (ℝ × ℝ) | y.fst ∈ Icc 0 1 ∧ y.snd ∈ Icc 0 1})
    (fun y hy => ⟨Ioo_subset_Icc_self hy.1, Ioo_subset_Icc_self hy.2⟩) ?_
    (frontier_subset_closure hx)
  exact (isClosed_Icc.preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst).inter
    (isClosed_Icc.preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ).snd)

/-- A rotation chart of the open unit square, from the description of the square in chart
coordinates. -/
theorem isLipschitzChartWith_openUnitSquare_of_forall_mem_iff (c : WithLp 2 (ℝ × ℝ)) {α β : ℝ}
    (hαβ : α ^ 2 + β ^ 2 = 1) {φ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hφ0 : φ 0 = 0)
    (hφ : LipschitzWith 1 φ)
    (hmem : ∀ u v : ℝ, |u| < a → |v| < b →
      ((c.fst + (α * u - β * v) ∈ Ioo 0 1 ∧ c.snd + (β * u + α * v) ∈ Ioo 0 1) ↔ φ v < u)) :
    openUnitSquare.IsLipschitzChartWith 1 (prodRecentredRotation α β hαβ c) φ a b := by
  refine (Set.isLipschitzChartWith_iff ..).2 ⟨ha, hb, hφ0, hφ, fun z hz => ?_⟩
  rw [mem_normalCylinder, Real.norm_eq_abs] at hz
  simpa using hmem z.fst z.snd (abs_lt.2 ⟨hz.1, hz.2.1⟩) hz.2.2

/-- The arithmetic of a corner chart: with `k = (√2)⁻¹`, the rotated quarter-plane
`k (u - v) > 0, k (u + v) > 0` near the origin is the region `|v| < u`. -/
private theorem corner_iff {u v : ℝ} (hu : |u| < 1 / 2) (hv : |v| < 1 / 2) :
    ((√2)⁻¹ * (u - v) ∈ Ioo (0 : ℝ) 1 ∧ (√2)⁻¹ * (u + v) ∈ Ioo (0 : ℝ) 1) ↔ |v| < u := by
  have hk1 : 1 / 2 < (√2)⁻¹ := by
    rw [one_div]
    exact inv_strictAnti₀ (by positivity) ((Real.sqrt_lt' two_pos).2 (by norm_num))
  have hk2 : (√2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two
  set k : ℝ := (√2)⁻¹
  rw [abs_lt] at hu hv ⊢
  simp only [mem_Ioo]
  constructor
  · rintro ⟨⟨h1, -⟩, h2, -⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩

/-- The rotation by `π / 4` centred at the corner `0` is a chart of the open unit square with
graph `|s|` and constant `1`. -/
theorem isLipschitzChartWith_openUnitSquare_zero :
    openUnitSquare.IsLipschitzChartWith 1
      (prodRecentredRotation (√2)⁻¹ (√2)⁻¹ Real.inv_sqrt_two_sq_add_inv_sqrt_two_sq 0)
      (fun s => |s|) (1 / 2) (1 / 2) := by
  refine isLipschitzChartWith_openUnitSquare_of_forall_mem_iff 0 _ (by norm_num) (by norm_num)
    abs_zero (lipschitzWith_one_norm (E := ℝ)) fun u v hu hv => ?_
  refine Iff.trans ?_ (corner_iff hu hv)
  simp only [WithLp.zero_fst, WithLp.zero_snd, zero_add, mul_sub, mul_add]

/-- The edge charts of the open unit square: at a point `c` of an open edge, the translated
rotation by a multiple of `π / 2` taking the first coordinate to the inward normal is a chart with
flat graph. -/
private theorem exists_isLipschitzChartWith_openUnitSquare_edge {c : WithLp 2 (ℝ × ℝ)}
    (hc : c.fst ∈ Ioo 0 1 ∧ (c.snd = 0 ∨ c.snd = 1) ∨ c.snd ∈ Ioo 0 1 ∧ (c.fst = 0 ∨ c.fst = 1)) :
    ∃ (α β : ℝ) (hαβ : α ^ 2 + β ^ 2 = 1) (b : ℝ),
      openUnitSquare.IsLipschitzChartWith 1 (prodRecentredRotation α β hαβ c) (fun _ => 0) 1 b := by
  have hlip0 : LipschitzWith 1 (fun _ : ℝ => (0 : ℝ)) := (LipschitzWith.const 0).weaken zero_le_one
  -- The bottom, top, left and right edges.
  rcases hc with ⟨⟨h0, h1⟩, he | he⟩ | ⟨⟨h0, h1⟩, he | he⟩ <;>
    [refine ⟨0, 1, by norm_num, min c.fst (1 - c.fst), ?_⟩;
      refine ⟨0, -1, by norm_num, min c.fst (1 - c.fst), ?_⟩;
      refine ⟨1, 0, by norm_num, min c.snd (1 - c.snd), ?_⟩;
      refine ⟨-1, 0, by norm_num, min c.snd (1 - c.snd), ?_⟩] <;>
  · refine isLipschitzChartWith_openUnitSquare_of_forall_mem_iff c _ one_pos
      (lt_min h0 (by linarith)) rfl hlip0 fun u v hu hv => ?_
    obtain ⟨hv1, hv2⟩ := lt_min_iff.1 hv
    rw [abs_lt] at hu hv1 hv2
    simp only [he, mem_Ioo]
    constructor
    · rintro ⟨⟨h2, h3⟩, h4, h5⟩; linarith
    · intro H; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- The corner charts of the open unit square: at a corner `c`, the translated rotation by an odd
multiple of `π / 4` taking the first coordinate to the inward diagonal is a chart with graph
`|s|`. -/
private theorem exists_isLipschitzChartWith_openUnitSquare_corner {c : WithLp 2 (ℝ × ℝ)}
    (hs : c.fst = 0 ∨ c.fst = 1) (ht : c.snd = 0 ∨ c.snd = 1) :
    ∃ (α β : ℝ) (hαβ : α ^ 2 + β ^ 2 = 1), openUnitSquare.IsLipschitzChartWith 1
      (prodRecentredRotation α β hαβ c) (fun s => |s|) (1 / 2) (1 / 2) := by
  have hk0 := Real.inv_sqrt_two_sq_add_inv_sqrt_two_sq
  have hk : (-(√2)⁻¹ : ℝ) ^ 2 + ((√2)⁻¹ : ℝ) ^ 2 = 1 := by rw [neg_sq]; exact hk0
  have hk' : ((√2)⁻¹ : ℝ) ^ 2 + (-(√2)⁻¹ : ℝ) ^ 2 = 1 := by rw [neg_sq]; exact hk0
  have hk'' : (-(√2)⁻¹ : ℝ) ^ 2 + (-(√2)⁻¹ : ℝ) ^ 2 = 1 := by rw [neg_sq]; exact hk0
  rcases hs with hs | hs <;> rcases ht with ht | ht <;>
    [refine ⟨_, _, hk0, ?_⟩; refine ⟨_, _, hk', ?_⟩; refine ⟨_, _, hk, ?_⟩;
      refine ⟨_, _, hk'', ?_⟩] <;>
  · refine isLipschitzChartWith_openUnitSquare_of_forall_mem_iff c _ (by norm_num) (by norm_num)
      abs_zero (lipschitzWith_one_norm (E := ℝ)) fun u v hu hv => ?_
    refine Iff.trans ?_ (corner_iff hu hv)
    simp only [hs, ht, mem_Ioo]
    constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- **The open unit square is a Lipschitz domain** with constant `1`. Along the open edges the
charts are rotations by multiples of `π / 2` with flat graph, and at the corners rotations by
odd multiples of `π / 4` with graph `|s|`. -/
theorem isLipschitzDomainWith_openUnitSquare :
    openUnitSquare.IsLipschitzDomainWith (E := ℝ) 1 := by
  refine (Set.isLipschitzDomainWith_iff ..).2 ⟨isOpen_openUnitSquare, fun x hx => ?_⟩
  obtain ⟨⟨hs0, hs1⟩, ht0, ht1⟩ := mem_Icc_of_mem_frontier_openUnitSquare hx
  have hxΩ : x ∉ openUnitSquare := isOpen_openUnitSquare.interior_eq ▸ hx.2
  suffices ∃ (α β : ℝ) (hαβ : α ^ 2 + β ^ 2 = 1) (φ : ℝ → ℝ) (a b : ℝ),
      openUnitSquare.IsLipschitzChartWith 1 (prodRecentredRotation α β hαβ x) φ a b by
    obtain ⟨α, β, hαβ, φ, a, b, hc⟩ := this
    exact (Set.isLipschitzDomainAtWith_iff ..).2
      ⟨_, φ, a, b, prodRecentredRotation_apply_self α β hαβ x, hc⟩
  have h01 : ∀ {w : ℝ}, 0 ≤ w → w ≤ 1 → w ∉ Ioo 0 1 → w = 0 ∨ w = 1 := by
    intro w hw0 hw1 hw
    by_contra! H
    exact hw ⟨lt_of_le_of_ne hw0 (Ne.symm H.1), lt_of_le_of_ne hw1 H.2⟩
  by_cases hs : x.fst ∈ Ioo 0 1
  · obtain ⟨α, β, hαβ, b, hc⟩ := exists_isLipschitzChartWith_openUnitSquare_edge
      (Or.inl ⟨hs, h01 ht0 ht1 fun ht => hxΩ ⟨hs, ht⟩⟩)
    exact ⟨α, β, hαβ, _, _, _, hc⟩
  by_cases ht : x.snd ∈ Ioo 0 1
  · obtain ⟨α, β, hαβ, b, hc⟩ :=
      exists_isLipschitzChartWith_openUnitSquare_edge (Or.inr ⟨ht, h01 hs0 hs1 hs⟩)
    exact ⟨α, β, hαβ, _, _, _, hc⟩
  obtain ⟨α, β, hαβ, hc⟩ :=
    exists_isLipschitzChartWith_openUnitSquare_corner (h01 hs0 hs1 hs) (h01 ht0 ht1 ht)
  exact ⟨α, β, hαβ, _, _, _, hc⟩

/-! ### Cones of a planar chart -/

/-- A point within `η` of `(t₀, 0)` in chart coordinates, where `t₀ ≠ 0`, `|t₀| ≤ h / 2`,
`|t₀| ≤ r` and `(K + 1) η ≤ |t₀| / 2`, lies in the cylinder `normalCylinder h r`; it lies strictly
above the cone `K ‖s‖ < t` if `0 < t₀`, and strictly below the cone `t < -(K ‖s‖)` if `t₀ < 0`. -/
private theorem mem_normalCylinder_and_cone_of_dist_le {K : ℝ≥0} {h r t₀ η : ℝ}
    {z : WithLp 2 (ℝ × ℝ)} (ht₀ : t₀ ≠ 0) (hh : |t₀| ≤ h / 2) (hr : |t₀| ≤ r)
    (hη : (K + 1) * η ≤ |t₀| / 2) (hz : dist z (WithLp.toLp 2 (t₀, 0)) ≤ η) :
    z ∈ normalCylinder h r ∧ (0 < t₀ → K * ‖z.snd‖ < z.fst) ∧
      (t₀ < 0 → z.fst < -(K * ‖z.snd‖)) := by
  have h1 := (WithLp.dist_fst_le z _).trans hz
  have h2 := (WithLp.dist_snd_le z _).trans hz
  rw [Real.dist_eq] at h1 h2
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, sub_zero] at h1 h2
  have hK : (K : ℝ) * |z.snd| ≤ K * η := mul_le_mul_of_nonneg_left h2 K.coe_nonneg
  have hKη : 0 ≤ (K : ℝ) * η := mul_nonneg K.coe_nonneg ((abs_nonneg _).trans h2)
  rw [abs_le] at h1 h2
  simp only [mem_normalCylinder, Real.norm_eq_abs, abs_lt]
  rcases ht₀.lt_or_gt with h0 | h0 <;>
    [rw [abs_of_neg h0] at hh hr hη; rw [abs_of_pos h0] at hh hr hη] <;>
  exact ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, fun _ => by linarith,
    fun _ => by linarith⟩

/-! ### The slit disc -/

/-- The slit disc `B(0, 1) ∖ [0, 1) × {0}` in the Euclidean plane. -/
def slitUnitDisc : Set (WithLp 2 (ℝ × ℝ)) :=
  ball 0 1 \ {x | x.fst ∈ Ico 0 1 ∧ x.snd = 0}

/-- Membership in the slit disc: a point of the open unit disc off the slit `[0, 1) × {0}`. -/
@[simp]
theorem mem_slitUnitDisc {x : WithLp 2 (ℝ × ℝ)} :
    x ∈ slitUnitDisc ↔ ‖x‖ < 1 ∧ (x.fst ∈ Ico 0 1 → x.snd ≠ 0) := by
  simp [slitUnitDisc]

/-- Every slit point lies on the frontier of the slit disc. -/
theorem mem_frontier_slitUnitDisc {p : WithLp 2 (ℝ × ℝ)} (hp : p.fst ∈ Ico 0 1)
    (hp' : p.snd = 0) : p ∈ frontier slitUnitDisc := by
  refine ⟨Metric.mem_closure_iff.2 fun ε hε => ?_,
    fun hint => (interior_subset hint).2 ⟨hp, hp'⟩⟩
  set t := min (ε / 2) ((1 - p.fst) / 2)
  have ht : 0 < t := lt_min (by linarith) (by linarith [hp.2])
  have ht1 : t ≤ ε / 2 := min_le_left _ _
  have ht2 : t ≤ (1 - p.fst) / 2 := min_le_right _ _
  have hnt : ‖WithLp.toLp 2 ((0 : ℝ), t)‖ = t := by
    rw [WithLp.norm_toLp_snd, Real.norm_of_nonneg ht.le]
  refine ⟨p + WithLp.toLp 2 (0, t), ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball_zero_iff]
    calc ‖p + WithLp.toLp 2 ((0 : ℝ), t)‖ ≤ ‖p‖ + ‖WithLp.toLp 2 ((0 : ℝ), t)‖ := norm_add_le _ _
      _ = p.fst + t := by
        rw [WithLp.prod_norm_eq_norm_fst_of_snd_eq_zero hp', hnt, Real.norm_of_nonneg hp.1]
      _ < 1 := by linarith [hp.2]
  · rintro ⟨-, h⟩
    simp only [WithLp.add_snd, hp', WithLp.toLp_snd, zero_add] at h
    exact ht.ne' h
  · rw [dist_self_add_right, hnt]
    linarith

/-- A point of the open unit disc outside the slit disc lies on the axis `t = 0`. -/
private theorem snd_eq_zero_of_notMem_slitUnitDisc {x : WithLp 2 (ℝ × ℝ)} (hx : ‖x‖ < 1)
    (hx' : x ∉ slitUnitDisc) : x.snd = 0 := by
  by_contra H
  exact hx' ⟨mem_ball_zero_iff.2 hx, fun hs => H hs.2⟩

/-- **The slit disc is not a Lipschitz domain at a slit point.** No Lipschitz chart, with any
constant and any cylinder, is centred at a point `p` of the slit `[0, 1) × {0}`: such a chart
would place a whole open set below its graph, outside the slit disc but inside the disc, while
the slit near `p` contains no open set. -/
theorem not_exists_isLipschitzChart_slitUnitDisc {p : WithLp 2 (ℝ × ℝ)} (hp : p.fst ∈ Ico 0 1)
    (hp' : p.snd = 0) :
    ¬ ∃ (e : WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ)) (γ : ℝ → ℝ) (K : ℝ≥0) (h r : ℝ),
      slitUnitDisc.IsLipschitzChart e γ K h r ∧ e p = 0 := by
  rintro ⟨e, γ, K, h, r, hc, hep⟩
  have hγ := hc.apply_zero_of_mem_frontier (mem_frontier_slitUnitDisc hp hp') hep
  have hh := hc.height_pos
  have hr := hc.radius_pos
  set ε := min (min (h / 2) r) ((1 - p.fst) / 2)
  have hε : 0 < ε := lt_min (lt_min (by linarith) hr) (by linarith [hp.2])
  have hεh : ε ≤ h / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hεr : ε ≤ r := (min_le_left _ _).trans (min_le_right _ _)
  have hεp : ε ≤ (1 - p.fst) / 2 := min_le_right _ _
  set η := ε / (2 * (K + 1))
  have hη : 0 < η := by positivity
  have hKη : (K + 1) * η = ε / 2 := by simp only [η]; field_simp
  have hηε : η ≤ ε / 2 := by linarith [mul_nonneg K.coe_nonneg hη.le]
  set z₁ : WithLp 2 (ℝ × ℝ) := WithLp.toLp 2 (-ε, 0)
  set w₁ := e.symm z₁
  set w₂ := w₁ + WithLp.toLp 2 (0, η)
  have hnη : ‖WithLp.toLp 2 ((0 : ℝ), η)‖ = η := by
    rw [WithLp.norm_toLp_snd, Real.norm_of_nonneg hη.le]
  -- Points within `η` of `z₁` in chart coordinates lie below the graph, outside the slit disc.
  have hbelow : ∀ w, dist (e w) z₁ ≤ η → w ∉ slitUnitDisc := fun w hw => by
    have hε' : |-ε| = ε := by rw [abs_neg, abs_of_pos hε]
    obtain ⟨hz, -, hlt⟩ := mem_normalCylinder_and_cone_of_dist_le (h := h) (r := r)
      (neg_ne_zero.2 hε.ne') (by rwa [hε']) (by rwa [hε']) (by rw [hε', hKη]) hw
    simpa using hc.symm_notMem_of_fst_lt_neg_mul_norm hγ hz (hlt (neg_neg_of_pos hε))
  have hw₁ : w₁ ∉ slitUnitDisc := hbelow w₁ (by simp [w₁, hη.le])
  have hw₂ : w₂ ∉ slitUnitDisc := hbelow w₂ (by
    rw [← e.apply_symm_apply z₁, e.dist_map, dist_comm, dist_self_add_right, hnη])
  -- Both points lie in the disc, hence on the slit, but their second coordinates differ.
  have hdp : dist w₁ p = ε := by
    rw [← e.dist_map, AffineIsometryEquiv.apply_symm_apply, hep, dist_zero_right]
    simp [z₁, abs_of_pos hε]
  have hnp : ‖p‖ = p.fst := by
    rw [WithLp.prod_norm_eq_norm_fst_of_snd_eq_zero hp', Real.norm_of_nonneg hp.1]
  have hb₁ : ‖w₁‖ ≤ p.fst + ε := by
    rw [← dist_zero_right, ← hnp, ← dist_zero_right p, ← hdp, add_comm]
    exact dist_triangle _ _ _
  have hb₂ : ‖w₂‖ ≤ p.fst + ε + η := (norm_add_le _ _).trans (by rw [hnη]; linarith)
  have hs₁ := snd_eq_zero_of_notMem_slitUnitDisc (by linarith [hp.2]) hw₁
  have hs₂ := snd_eq_zero_of_notMem_slitUnitDisc (by linarith [hp.2]) hw₂
  simp only [w₂, WithLp.add_snd, hs₁, WithLp.toLp_snd, zero_add] at hs₂
  exact hη.ne' hs₂

/-- The slit disc has no centred Lipschitz chart at a slit point, for any constant `L`. -/
theorem not_isLipschitzDomainAtWith_slitUnitDisc {p : WithLp 2 (ℝ × ℝ)} (hp : p.fst ∈ Ico 0 1)
    (hp' : p.snd = 0) (L : ℝ≥0) : ¬ slitUnitDisc.IsLipschitzDomainAtWith (E := ℝ) L p := by
  rw [Set.isLipschitzDomainAtWith_iff]
  rintro ⟨e, φ, a, b, he, hc⟩
  exact not_exists_isLipschitzChart_slitUnitDisc hp hp' ⟨e, φ, L, a, b, hc.toIsLipschitzChart, he⟩

/-- The slit disc is not a Lipschitz domain. -/
theorem not_isLipschitzDomain_slitUnitDisc : ¬ slitUnitDisc.IsLipschitzDomain ℝ := fun H => by
  have h0 : (0 : WithLp 2 (ℝ × ℝ)).fst ∈ Ico 0 1 := by simp
  obtain ⟨e, γ, K, h, r, hc, hmem⟩ := Set.isLipschitzDomain_iff_exists_mem_normalCylinder.1 H 0
    (mem_frontier_slitUnitDisc h0 (by simp))
  obtain ⟨e', γ', h', r', hc', he'⟩ := hc.exists_isLipschitzChart_eq_zero hmem
  exact not_exists_isLipschitzChart_slitUnitDisc h0 (by simp) ⟨e', γ', K, h', r', hc', he'⟩

/-- The slit disc is not a Lipschitz domain with any constant `L`. -/
theorem not_isLipschitzDomainWith_slitUnitDisc (L : ℝ≥0) :
    ¬ slitUnitDisc.IsLipschitzDomainWith (E := ℝ) L := fun H =>
  not_isLipschitzDomain_slitUnitDisc H.isLipschitzDomain

/-! ### The square-root cusp -/

/-- The cusp `{(s, t) | √|s| < t}` in the Euclidean plane. -/
def sqrtAbsCusp : Set (WithLp 2 (ℝ × ℝ)) :=
  {x | √|x.fst| < x.snd}

/-- Membership in the cusp. -/
@[simp]
theorem mem_sqrtAbsCusp {x : WithLp 2 (ℝ × ℝ)} : x ∈ sqrtAbsCusp ↔ √|x.fst| < x.snd :=
  Iff.rfl

/-- The vertex of the cusp lies on its frontier. -/
theorem zero_mem_frontier_sqrtAbsCusp : (0 : WithLp 2 (ℝ × ℝ)) ∈ frontier sqrtAbsCusp := by
  refine ⟨Metric.mem_closure_iff.2 fun ε hε => ⟨WithLp.toLp 2 (0, ε / 2), ?_, ?_⟩,
    fun hint => ?_⟩
  · simpa using half_pos hε
  · rw [dist_zero_left, WithLp.norm_toLp_snd, Real.norm_of_nonneg (by linarith)]
    linarith
  · have := interior_subset hint
    simp at this

/-- **The cusp is not Lipschitz at its vertex.** No Lipschitz chart, with any constant `K` and
any cylinder, is centred at the origin: such a chart would put a cone of positive aperture,
with vertex at the origin, inside the cusp, while near the origin the cusp is thinner than any
cone because `√|s|` has no finite Lipschitz constant at `0`. -/
theorem not_exists_isLipschitzChart_sqrtAbsCusp :
    ¬ ∃ (e : WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ)) (γ : ℝ → ℝ) (K : ℝ≥0) (h r : ℝ),
      sqrtAbsCusp.IsLipschitzChart e γ K h r ∧ e 0 = 0 := by
  rintro ⟨e, γ, K, h, r, hc, he0⟩
  have hγ := hc.apply_zero_of_mem_frontier zero_mem_frontier_sqrtAbsCusp he0
  have hh := hc.height_pos
  have hr := hc.radius_pos
  set c : ℝ := 1 / (2 * (K + 1))
  have hc0 : 0 < c := by positivity
  have hKc : (K + 1) * c = 1 / 2 := by simp only [c]; field_simp
  set ε := min (min c (h / 2)) r
  have hε : 0 < ε := lt_min (lt_min hc0 (by linarith)) hr
  have hεc : ε ≤ c := (min_le_left _ _).trans (min_le_left _ _)
  have hεh : ε ≤ h / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hεr : ε ≤ r := min_le_right _ _
  set δ := ε * c
  have hδ : 0 < δ := by positivity
  have hKδ : (K + 1) * δ = ε / 2 := by simp only [δ]; linear_combination ε * hKc
  have hεδ : ε ^ 2 ≤ δ := by simp only [δ, sq]; exact mul_le_mul_of_nonneg_left hεc hε.le
  set z₀ : WithLp 2 (ℝ × ℝ) := WithLp.toLp 2 (ε, 0)
  set p := e.symm z₀
  -- Move horizontally away from the axis `s = 0`, by `δ`.
  obtain ⟨σ, hσ, hσp⟩ : ∃ σ : ℝ, |σ| = δ ∧ δ ≤ |p.fst + σ| := by
    by_cases hp : 0 ≤ p.fst
    · exact ⟨δ, abs_of_pos hδ, by rw [abs_of_nonneg (by linarith)]; linarith⟩
    · refine ⟨-δ, by rw [abs_neg, abs_of_pos hδ], ?_⟩
      rw [abs_of_neg (by linarith)]
      linarith
  set q := p + WithLp.toLp 2 (σ, 0)
  have hd : dist (e q) z₀ = δ := by
    rw [← e.apply_symm_apply z₀, e.dist_map, dist_comm, dist_self_add_right,
      WithLp.norm_toLp_fst, Real.norm_eq_abs, hσ]
  -- The point `q` lies above the cone of the chart, hence in the cusp.
  have hq : q ∈ sqrtAbsCusp := by
    have hε' : |ε| = ε := abs_of_pos hε
    obtain ⟨hz, hlt, -⟩ := mem_normalCylinder_and_cone_of_dist_le (h := h) (r := r) hε.ne'
      (by rwa [hε']) (by rwa [hε']) (by rw [hε', hKδ]) hd.le
    simpa using hc.symm_mem_of_mul_norm_lt_fst hγ hz (hlt hε)
  -- But `q` is too far from the axis for its height.
  have hnp : ‖p‖ = ε := by
    rw [← dist_zero_right, ← e.dist_map, AffineIsometryEquiv.apply_symm_apply, he0,
      dist_zero_right, WithLp.norm_toLp_fst, Real.norm_of_nonneg hε.le]
  have hqs : q.snd ≤ ε := by
    simp only [q, WithLp.add_snd, WithLp.toLp_snd, add_zero]
    exact (le_abs_self _).trans ((WithLp.norm_snd_le ℝ p).trans hnp.le)
  have hq' : |q.fst| < ε ^ 2 :=
    (Real.sqrt_lt' hε).1 (lt_of_lt_of_le hq hqs)
  simp only [q, WithLp.add_fst, WithLp.toLp_fst] at hq'
  linarith

/-- The cusp has no centred Lipschitz chart at its vertex, for any constant `L`. -/
theorem not_isLipschitzDomainAtWith_sqrtAbsCusp (L : ℝ≥0) :
    ¬ sqrtAbsCusp.IsLipschitzDomainAtWith (E := ℝ) L 0 := by
  rw [Set.isLipschitzDomainAtWith_iff]
  rintro ⟨e, φ, a, b, he, hc⟩
  exact not_exists_isLipschitzChart_sqrtAbsCusp ⟨e, φ, L, a, b, hc.toIsLipschitzChart, he⟩

/-- The cusp is not a Lipschitz domain. -/
theorem not_isLipschitzDomain_sqrtAbsCusp : ¬ sqrtAbsCusp.IsLipschitzDomain ℝ := fun H => by
  obtain ⟨e, γ, K, h, r, hc, hmem⟩ := Set.isLipschitzDomain_iff_exists_mem_normalCylinder.1 H 0
    zero_mem_frontier_sqrtAbsCusp
  obtain ⟨e', γ', h', r', hc', he'⟩ := hc.exists_isLipschitzChart_eq_zero hmem
  exact not_exists_isLipschitzChart_sqrtAbsCusp ⟨e', γ', K, h', r', hc', he'⟩

/-- The cusp is not a Lipschitz domain with any constant `L`. -/
theorem not_isLipschitzDomainWith_sqrtAbsCusp (L : ℝ≥0) :
    ¬ sqrtAbsCusp.IsLipschitzDomainWith (E := ℝ) L := fun H =>
  not_isLipschitzDomain_sqrtAbsCusp H.isLipschitzDomain

end TauCeti
