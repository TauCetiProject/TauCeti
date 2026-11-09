/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# Planar examples and non-examples of Lipschitz domains

The open unit square `(0, 1)²` is a Lipschitz domain with constant `1`. Along the open edges a
translated and rotated chart has the flat graph `0`; at a corner the rotation by `π / 4` turns
the quarter-plane into the region above `γ s = |s|`, which is `1`-Lipschitz.

Two standard planar sets fail the predicate. In a chart centred at a frontier point the domain
contains a whole cone above the centre and misses a whole cone below it, because the graph is
Lipschitz and passes through the centre. The slit disc `B(0, 1) ∖ [0, 1) × {0}` misses no open
set near a slit point, so no chart is centred there. The cusp `{(s, t) | √|s| < t}` contains no
cone at the origin, so no chart, with any Lipschitz constant, is centred there.

## Main declarations

* `Set.IsLipschitzChart.symm_mem_of_mul_norm_lt_fst`,
  `Set.IsLipschitzChart.symm_notMem_of_fst_lt_neg_mul_norm`: a chart whose graph passes through
  the centre contains the upward cone and misses the downward cone of its cylinder.
* `TauCeti.prodL2Rotation`: the rotation `(s, t) ↦ (α s + β t, α t - β s)` of the Euclidean plane.
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

namespace Set.IsLipschitzChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Set F} {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ}

/-- The graph of a Lipschitz chart centred at a frontier point passes through the origin. -/
theorem apply_zero_of_mem_frontier (hc : IsLipschitzChart Ω e γ K h r) {x : F}
    (hx : x ∈ frontier Ω) (hex : e x = 0) : γ 0 = 0 := by
  have := hc.fst_apply_eq_of_mem_frontier hx
    (hex ▸ TauCeti.zero_mem_normalCylinder hc.height_pos hc.radius_pos)
  simpa [hex] using this.symm

/-- **Upward cone.** If the graph of a Lipschitz chart passes through the origin, every point of
the cylinder above the cone `K * ‖y‖ < t` corresponds to a point of `Ω`. -/
theorem symm_mem_of_mul_norm_lt_fst (hc : IsLipschitzChart Ω e γ K h r) (hγ : γ 0 = 0)
    {z : WithLp 2 (ℝ × E)} (hz : z ∈ TauCeti.normalCylinder h r) (hlt : K * ‖z.snd‖ < z.fst) :
    e.symm z ∈ Ω := by
  rw [hc.mem_iff (by simpa using hz), AffineIsometryEquiv.apply_symm_apply]
  have := hc.lipschitzWith.dist_le_mul z.snd 0
  rw [hγ, Real.dist_eq, sub_zero, dist_zero_right] at this
  linarith [le_abs_self (γ z.snd)]

/-- **Downward cone.** If the graph of a Lipschitz chart passes through the origin, no point of
the cylinder below the cone `t < -(K * ‖y‖)` corresponds to a point of `Ω`. -/
theorem symm_notMem_of_fst_lt_neg_mul_norm (hc : IsLipschitzChart Ω e γ K h r) (hγ : γ 0 = 0)
    {z : WithLp 2 (ℝ × E)} (hz : z ∈ TauCeti.normalCylinder h r)
    (hlt : z.fst < -(K * ‖z.snd‖)) : e.symm z ∉ Ω := by
  rw [hc.mem_iff (by simpa using hz), AffineIsometryEquiv.apply_symm_apply, not_lt]
  have := hc.lipschitzWith.dist_le_mul z.snd 0
  rw [hγ, Real.dist_eq, sub_zero, dist_zero_right] at this
  linarith [neg_abs_le (γ z.snd)]

end Set.IsLipschitzChart

namespace TauCeti

/-! ### Rotations of the Euclidean plane -/

/-- Two points of the Euclidean plane with the same coordinates are equal. -/
private theorem prodL2_ext {x y : WithLp 2 (ℝ × ℝ)} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) :
    x = y :=
  (WithLp.ext_iff 2).2 (Prod.ext h1 h2)

/-- The rotation `(s, t) ↦ (α s + β t, α t - β s)` of the Euclidean plane `WithLp 2 (ℝ × ℝ)`,
for `α ^ 2 + β ^ 2 = 1`. -/
def prodL2Rotation (α β : ℝ) (hαβ : α ^ 2 + β ^ 2 = 1) :
    WithLp 2 (ℝ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × ℝ) where
  toFun x := WithLp.toLp 2 (α * x.fst + β * x.snd, α * x.snd - β * x.fst)
  invFun z := WithLp.toLp 2 (α * z.fst - β * z.snd, β * z.fst + α * z.snd)
  map_add' x y := by apply prodL2_ext <;> simp <;> ring
  map_smul' c x := by apply prodL2_ext <;> simp <;> ring
  left_inv x := by
    apply prodL2_ext
    · simp only [WithLp.toLp_fst, WithLp.toLp_snd]
      linear_combination x.fst * hαβ
    · simp only [WithLp.toLp_fst, WithLp.toLp_snd]
      linear_combination x.snd * hαβ
  right_inv z := by
    apply prodL2_ext
    · simp only [WithLp.toLp_fst, WithLp.toLp_snd]
      linear_combination z.fst * hαβ
    · simp only [WithLp.toLp_fst, WithLp.toLp_snd]
      linear_combination z.snd * hαβ
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2,
      WithLp.prod_norm_sq_eq_of_L2]
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, WithLp.toLp_fst,
      WithLp.toLp_snd, Real.norm_eq_abs, sq_abs]
    linear_combination (x.fst ^ 2 + x.snd ^ 2) * hαβ

/-- The rigid coordinates `x ↦ R (x - c)` of the plane, centred at `c`, for the rotation
`R = prodL2Rotation α β hαβ`. -/
def prodL2RotationChart (c : WithLp 2 (ℝ × ℝ)) (α β : ℝ) (hαβ : α ^ 2 + β ^ 2 = 1) :
    WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ) :=
  (AffineIsometryEquiv.vaddConst ℝ c).symm.trans (prodL2Rotation α β hαβ).toAffineIsometryEquiv

/-- The rotation chart sends its centre to the origin. -/
@[simp]
theorem prodL2RotationChart_apply_self (c : WithLp 2 (ℝ × ℝ)) (α β : ℝ)
    (hαβ : α ^ 2 + β ^ 2 = 1) : prodL2RotationChart c α β hαβ c = 0 := by
  simp [prodL2RotationChart]

/-- The first coordinate of the inverse of a rotation chart. -/
@[simp]
theorem prodL2RotationChart_symm_fst (c : WithLp 2 (ℝ × ℝ)) (α β : ℝ)
    (hαβ : α ^ 2 + β ^ 2 = 1) (z : WithLp 2 (ℝ × ℝ)) :
    ((prodL2RotationChart c α β hαβ).symm z).fst = c.fst + (α * z.fst - β * z.snd) := by
  simp [prodL2RotationChart, prodL2Rotation, add_comm]
  rfl

/-- The second coordinate of the inverse of a rotation chart. -/
@[simp]
theorem prodL2RotationChart_symm_snd (c : WithLp 2 (ℝ × ℝ)) (α β : ℝ)
    (hαβ : α ^ 2 + β ^ 2 = 1) (z : WithLp 2 (ℝ × ℝ)) :
    ((prodL2RotationChart c α β hαβ).symm z).snd = c.snd + (β * z.fst + α * z.snd) := by
  simp [prodL2RotationChart, prodL2Rotation, add_comm]
  rfl

/-! ### The open unit square -/

/-- The open unit square `(0, 1)²` in the Euclidean plane. -/
def openUnitSquare : Set (WithLp 2 (ℝ × ℝ)) :=
  {x | x.fst ∈ Ioo 0 1 ∧ x.snd ∈ Ioo 0 1}

/-- The open unit square is open. -/
theorem isOpen_openUnitSquare : IsOpen openUnitSquare :=
  (isOpen_Ioo.preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst).inter
    (isOpen_Ioo.preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ).snd)

/-- The frontier of the open unit square lies in the closed square and outside the open one. -/
theorem mem_Icc_of_mem_frontier_openUnitSquare {x : WithLp 2 (ℝ × ℝ)}
    (hx : x ∈ frontier openUnitSquare) :
    (x.fst ∈ Icc 0 1 ∧ x.snd ∈ Icc 0 1) ∧ x ∉ openUnitSquare := by
  rw [isOpen_openUnitSquare.frontier_eq] at hx
  refine ⟨closure_minimal (s := openUnitSquare)
    (t := {y : WithLp 2 (ℝ × ℝ) | y.fst ∈ Icc 0 1 ∧ y.snd ∈ Icc 0 1})
    (fun y hy => ⟨Ioo_subset_Icc_self hy.1, Ioo_subset_Icc_self hy.2⟩) ?_ hx.1, hx.2⟩
  exact (isClosed_Icc.preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst).inter
    (isClosed_Icc.preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ).snd)

/-- A rotation chart of the open unit square, from the description of the square in chart
coordinates. -/
theorem isLipschitzChartWith_openUnitSquare_of (c : WithLp 2 (ℝ × ℝ)) {α β : ℝ}
    (hαβ : α ^ 2 + β ^ 2 = 1) {φ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hφ0 : φ 0 = 0)
    (hφ : LipschitzWith 1 φ)
    (hmem : ∀ u v : ℝ, |u| < a → |v| < b →
      ((c.fst + (α * u - β * v) ∈ Ioo 0 1 ∧ c.snd + (β * u + α * v) ∈ Ioo 0 1) ↔ φ v < u)) :
    openUnitSquare.IsLipschitzChartWith 1 (prodL2RotationChart c α β hαβ) φ a b := by
  refine (Set.isLipschitzChartWith_iff ..).2 ⟨ha, hb, hφ0, hφ, fun z hz => ?_⟩
  rw [mem_normalCylinder, Real.norm_eq_abs] at hz
  simpa [openUnitSquare] using hmem z.fst z.snd (abs_lt.2 ⟨hz.1, hz.2.1⟩) hz.2.2

/-- The square of `(√2)⁻¹` is `1 / 2`. -/
private theorem inv_sqrt_two_sq : ((√2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div]

/-- `(√2)⁻¹` lies in `(1 / 2, 1)`. -/
private theorem inv_sqrt_two_mem : ((√2)⁻¹ : ℝ) ∈ Ioo (1 / 2) 1 := by
  have h1 : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2 : √2 < (2 : ℝ) := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨?_, inv_lt_one_of_one_lt₀ h1⟩
  rw [one_div]
  exact inv_strictAnti₀ (by linarith) h2

/-- The arithmetic of a corner chart: with `k = (√2)⁻¹`, the rotated quarter-plane
`k (u - v) > 0, k (u + v) > 0` near the origin is the region `|v| < u`. -/
private theorem corner_iff {u v : ℝ} (hu : |u| < 1 / 2) (hv : |v| < 1 / 2) :
    ((√2)⁻¹ * (u - v) ∈ Ioo (0 : ℝ) 1 ∧ (√2)⁻¹ * (u + v) ∈ Ioo (0 : ℝ) 1) ↔ |v| < u := by
  obtain ⟨hk1, hk2⟩ := inv_sqrt_two_mem
  set k : ℝ := (√2)⁻¹
  rw [abs_lt] at hu hv ⊢
  have hk : 0 < k := by linarith
  simp only [mem_Ioo]
  constructor
  · rintro ⟨⟨h1, -⟩, h2, -⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩

/-- The vector `((√2)⁻¹, (√2)⁻¹)` has unit length. -/
theorem inv_sqrt_two_sq_add_inv_sqrt_two_sq : ((√2)⁻¹ : ℝ) ^ 2 + ((√2)⁻¹ : ℝ) ^ 2 = 1 := by
  rw [inv_sqrt_two_sq]; norm_num

/-- The rotation by `π / 4` centred at the corner `0` is a chart of the open unit square with
graph `|s|` and constant `1`. -/
theorem isLipschitzChartWith_openUnitSquare_zero :
    openUnitSquare.IsLipschitzChartWith 1
      (prodL2RotationChart 0 (√2)⁻¹ (√2)⁻¹ inv_sqrt_two_sq_add_inv_sqrt_two_sq)
      (fun s => |s|) (1 / 2) (1 / 2) := by
  refine isLipschitzChartWith_openUnitSquare_of 0 _ (by norm_num) (by norm_num) abs_zero
    (lipschitzWith_one_norm (E := ℝ)) fun u v hu hv => ?_
  refine Iff.trans ?_ (corner_iff hu hv)
  simp only [WithLp.zero_fst, WithLp.zero_snd, zero_add, mul_sub, mul_add]

/-- **The open unit square is a Lipschitz domain** with constant `1`. Along the open edges the
charts are rotations by multiples of `π / 2` with flat graph, and at the corners rotations by
odd multiples of `π / 4` with graph `|s|`. -/
theorem isLipschitzDomainWith_openUnitSquare :
    openUnitSquare.IsLipschitzDomainWith (E := ℝ) 1 := by
  refine (Set.isLipschitzDomainWith_iff ..).2 ⟨isOpen_openUnitSquare, fun x hx => ?_⟩
  obtain ⟨⟨⟨hs0, hs1⟩, ht0, ht1⟩, hxΩ⟩ := mem_Icc_of_mem_frontier_openUnitSquare hx
  have hlip0 : LipschitzWith 1 (fun _ : ℝ => (0 : ℝ)) := (LipschitzWith.const 0).weaken zero_le_one
  obtain ⟨hk1, hk2⟩ := inv_sqrt_two_mem
  have hk0 := inv_sqrt_two_sq_add_inv_sqrt_two_sq
  have hk : (-(√2)⁻¹ : ℝ) ^ 2 + ((√2)⁻¹ : ℝ) ^ 2 = 1 := by rw [neg_sq]; exact hk0
  have hk' : ((√2)⁻¹ : ℝ) ^ 2 + (-(√2)⁻¹ : ℝ) ^ 2 = 1 := by rw [neg_sq]; exact hk0
  have hk'' : (-(√2)⁻¹ : ℝ) ^ 2 + (-(√2)⁻¹ : ℝ) ^ 2 = 1 := by rw [neg_sq]; exact hk0
  suffices ∃ (α β : ℝ) (hαβ : α ^ 2 + β ^ 2 = 1) (φ : ℝ → ℝ) (a b : ℝ),
      openUnitSquare.IsLipschitzChartWith 1 (prodL2RotationChart x α β hαβ) φ a b by
    obtain ⟨α, β, hαβ, φ, a, b, hc⟩ := this
    exact (Set.isLipschitzDomainAtWith_iff ..).2
      ⟨_, φ, a, b, prodL2RotationChart_apply_self x α β hαβ, hc⟩
  have h01 : ∀ {w : ℝ}, 0 ≤ w → w ≤ 1 → w ∉ Ioo 0 1 → w = 0 ∨ w = 1 := by
    intro w hw0 hw1 hw
    by_contra! H
    exact hw ⟨lt_of_le_of_ne hw0 (Ne.symm H.1), lt_of_le_of_ne hw1 H.2⟩
  by_cases hs : x.fst ∈ Ioo 0 1
  · obtain ⟨hs0', hs1'⟩ := hs
    have hb : 0 < min x.fst (1 - x.fst) := lt_min hs0' (by linarith)
    rcases h01 ht0 ht1 fun ht => hxΩ ⟨⟨hs0', hs1'⟩, ht⟩ with ht | ht
    · -- The bottom edge: the chart `(s, t) ↦ (t, x.fst - s)`.
      refine ⟨0, 1, by norm_num, fun _ => 0, 1, _, isLipschitzChartWith_openUnitSquare_of x _
        one_pos hb rfl hlip0 fun u v hu hv => ?_⟩
      obtain ⟨hv1, hv2⟩ := lt_min_iff.1 hv
      rw [abs_lt] at hu hv1 hv2
      simp only [ht, mem_Ioo]
      constructor
      · intro H; linarith [H.2.1]
      · intro H; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · -- The top edge: the chart `(s, t) ↦ (1 - t, s - x.fst)`.
      refine ⟨0, -1, by norm_num, fun _ => 0, 1, _, isLipschitzChartWith_openUnitSquare_of x _
        one_pos hb rfl hlip0 fun u v hu hv => ?_⟩
      obtain ⟨hv1, hv2⟩ := lt_min_iff.1 hv
      rw [abs_lt] at hu hv1 hv2
      simp only [ht, mem_Ioo]
      constructor
      · intro H; linarith [H.2.2]
      · intro H; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hs' := h01 hs0 hs1 hs
  by_cases ht : x.snd ∈ Ioo 0 1
  · obtain ⟨ht0', ht1'⟩ := ht
    have hb : 0 < min x.snd (1 - x.snd) := lt_min ht0' (by linarith)
    rcases hs' with hs' | hs'
    · -- The left edge: the chart `(s, t) ↦ (s, t - x.snd)`.
      refine ⟨1, 0, by norm_num, fun _ => 0, 1, _, isLipschitzChartWith_openUnitSquare_of x _
        one_pos hb rfl hlip0 fun u v hu hv => ?_⟩
      obtain ⟨hv1, hv2⟩ := lt_min_iff.1 hv
      rw [abs_lt] at hu hv1 hv2
      simp only [hs', mem_Ioo]
      constructor
      · intro H; linarith [H.1.1]
      · intro H; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · -- The right edge: the chart `(s, t) ↦ (1 - s, x.snd - t)`.
      refine ⟨-1, 0, by norm_num, fun _ => 0, 1, _, isLipschitzChartWith_openUnitSquare_of x _
        one_pos hb rfl hlip0 fun u v hu hv => ?_⟩
      obtain ⟨hv1, hv2⟩ := lt_min_iff.1 hv
      rw [abs_lt] at hu hv1 hv2
      simp only [hs', mem_Ioo]
      constructor
      · intro H; linarith [H.1.2]
      · intro H; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  -- The four corners: rotations by odd multiples of `π / 4`.
  have ht' := h01 ht0 ht1 ht
  rcases hs' with hs' | hs' <;> rcases ht' with ht' | ht' <;>
    [refine ⟨_, _, hk0, ?_⟩; refine ⟨_, _, hk', ?_⟩; refine ⟨_, _, hk, ?_⟩;
      refine ⟨_, _, hk'', ?_⟩] <;>
  · refine ⟨fun s => |s|, 1 / 2, 1 / 2, isLipschitzChartWith_openUnitSquare_of x _
      (by norm_num) (by norm_num) abs_zero (lipschitzWith_one_norm (E := ℝ)) fun u v hu hv => ?_⟩
    refine Iff.trans ?_ (corner_iff hu hv)
    simp only [hs', ht', mem_Ioo]
    constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-! ### The slit disc -/

/-- The slit disc `B(0, 1) ∖ [0, 1) × {0}` in the Euclidean plane. -/
def slitUnitDisc : Set (WithLp 2 (ℝ × ℝ)) :=
  ball 0 1 \ {x | x.fst ∈ Ico 0 1 ∧ x.snd = 0}

/-- A point of the horizontal axis has norm the absolute value of its first coordinate. -/
private theorem norm_eq_abs_fst_of_snd_eq_zero {p : WithLp 2 (ℝ × ℝ)} (hp : p.snd = 0) :
    ‖p‖ = |p.fst| := by
  rw [WithLp.prod_norm_eq_of_L2, hp]
  simp [Real.sqrt_sq_eq_abs]

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
      _ = p.fst + t := by rw [norm_eq_abs_fst_of_snd_eq_zero hp', hnt, abs_of_nonneg hp.1]
      _ < 1 := by linarith [hp.2]
  · rintro ⟨-, h⟩
    simp only [WithLp.add_snd, hp', WithLp.toLp_snd, zero_add] at h
    exact ht.ne' h
  · rw [dist_self_add_right, hnt]
    linarith

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
  have hK : (0 : ℝ) < K + 1 := by positivity
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
  -- Both points lie below the graph of the chart, hence outside the slit disc.
  have hw₁ : w₁ ∉ slitUnitDisc := by
    refine hc.symm_notMem_of_fst_lt_neg_mul_norm hγ ?_ ?_
    · simp only [mem_normalCylinder, z₁, WithLp.toLp_fst, WithLp.toLp_snd, norm_zero]
      exact ⟨by linarith, by linarith, hr⟩
    · simp only [z₁, WithLp.toLp_fst, WithLp.toLp_snd, norm_zero, mul_zero, neg_zero]
      linarith
  have hd : dist (e w₂) z₁ = η := by
    rw [show z₁ = e w₁ by simp [w₁], e.dist_map, dist_comm, dist_self_add_right, hnη]
  have h1 := WithLp.dist_fst_le (e w₂) z₁
  have h2 := WithLp.dist_snd_le (e w₂) z₁
  rw [hd, Real.dist_eq] at h1 h2
  simp only [z₁, WithLp.toLp_fst, WithLp.toLp_snd, sub_neg_eq_add, sub_zero] at h1 h2
  rw [abs_le] at h1 h2
  have hw₂ : w₂ ∉ slitUnitDisc := by
    have := hc.symm_notMem_of_fst_lt_neg_mul_norm hγ (z := e w₂) ?_ ?_
    · simpa using this
    · rw [mem_normalCylinder, Real.norm_eq_abs, abs_lt]
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rw [Real.norm_eq_abs]
      have : (K : ℝ) * |(e w₂).snd| ≤ K * η :=
        mul_le_mul_of_nonneg_left (abs_le.2 h2) K.coe_nonneg
      nlinarith
  -- Both points lie in the disc, hence on the slit, but their second coordinates differ.
  have hdp : dist w₁ p = ε := by
    rw [← e.dist_map, AffineIsometryEquiv.apply_symm_apply, hep, dist_zero_right]
    simp [z₁, abs_of_pos hε]
  have hnp : ‖p‖ = p.fst := by rw [norm_eq_abs_fst_of_snd_eq_zero hp', abs_of_nonneg hp.1]
  have hb₁ : ‖w₁‖ ≤ p.fst + ε := by
    rw [← dist_zero_right, ← hnp, ← dist_zero_right p, ← hdp, add_comm]
    exact dist_triangle _ _ _
  have hb₂ : ‖w₂‖ ≤ p.fst + ε + η := (norm_add_le _ _).trans (by rw [hnη]; linarith)
  have hs₁ : w₁.snd = 0 := by
    by_contra H
    exact hw₁ ⟨mem_ball_zero_iff.2 (by linarith [hp.2]), fun hs => H hs.2⟩
  have hs₂ : w₂.snd = 0 := by
    by_contra H
    exact hw₂ ⟨mem_ball_zero_iff.2 (by linarith [hp.2]), fun hs => H hs.2⟩
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

/-- The vertex of the cusp lies on its frontier. -/
theorem zero_mem_frontier_sqrtAbsCusp : (0 : WithLp 2 (ℝ × ℝ)) ∈ frontier sqrtAbsCusp := by
  refine ⟨Metric.mem_closure_iff.2 fun ε hε => ⟨WithLp.toLp 2 (0, ε / 2), ?_, ?_⟩,
    fun hint => ?_⟩
  · change √|(0 : ℝ)| < ε / 2
    simpa using half_pos hε
  · rw [dist_zero_left, WithLp.norm_toLp_snd, Real.norm_of_nonneg (by linarith)]
    linarith
  · have := interior_subset hint
    simp [sqrtAbsCusp] at this

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
  have hK : (0 : ℝ) < K + 1 := by positivity
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
  have hδε : δ ≤ ε / 2 := by linarith [mul_nonneg K.coe_nonneg hδ.le]
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
    rw [show z₀ = e p by simp [p], e.dist_map, dist_comm, dist_self_add_right,
      WithLp.norm_toLp_fst, Real.norm_eq_abs, hσ]
  have h1 := WithLp.dist_fst_le (e q) z₀
  have h2 := WithLp.dist_snd_le (e q) z₀
  rw [hd, Real.dist_eq] at h1 h2
  simp only [z₀, WithLp.toLp_fst, WithLp.toLp_snd, sub_zero] at h1 h2
  rw [abs_le] at h1 h2
  -- The point `q` lies above the cone of the chart, hence in the cusp.
  have hq : q ∈ sqrtAbsCusp := by
    have := hc.symm_mem_of_mul_norm_lt_fst hγ (z := e q) ?_ ?_
    · simpa using this
    · rw [mem_normalCylinder, Real.norm_eq_abs, abs_lt]
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rw [Real.norm_eq_abs]
      have : (K : ℝ) * |(e q).snd| ≤ K * δ :=
        mul_le_mul_of_nonneg_left (abs_le.2 h2) K.coe_nonneg
      nlinarith
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
