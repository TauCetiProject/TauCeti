/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Polygon.DeltaMove
public import TauCeti.Geometry.Polygon.Subdivision
public import TauCeti.Topology.Homotopy.Isotopy.Push
import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!
# Δ-moves are realized by ambient isotopies

A Δ-move (`Polygon.IsDeltaMove`) replaces an edge `u = [a, b]` of a polygonal knot by the other
two sides `[a, c]` and `[c, b]` of a triangle `D` that meets the knot only in `u`. By Burde and
Zieschang (Proposition 1.10) such a move is realized by an ambient isotopy: an isotopy of the
ambient space through homeomorphisms carries the knot onto the moved one. This file proves this
for simple polygons in any real normed affine space, respecting the traversals of the polygons
(`Polygon.IsDeltaMove.exists_ambientIsotopy_boundaryParam`). Consequently combinatorially
equivalent polygonal knots are ambient isotopic
(`TauCeti.SimplePolygon.CombinatoriallyEquivalent.exists_ambientIsotopy_image_boundary`). The
converse, that ambient isotopic polygonal knots in `ℝ³` are combinatorially equivalent, is not
proved here.

The ambient isotopy is a push (`TauCeti.AmbientIsotopy.push`) moving the midpoint `m` of `u` to
`c`. In coordinates centred at `m`, write `α = a - m` and `γ = c - m`, and let `f`, `g` be
continuous linear functionals reading off the coefficients of `α` and `γ`. The push is weighted
by the sublinear function

`μ_ε w = |f w| + max ((1 - ε) * g w) (-g w / ε) + ‖w - f w • α - g w • γ‖ / ε`.

It takes the value `|s|` at `s • α` and the value `1 - ε < 1` at `γ`. So the push carries
`[a, m]` affinely onto `[a, c]` and `[m, b]` onto `[c, b]`. As `ε → 0` the sublevel sets
`{μ_ε ≤ 1}` shrink to the triangle `D - m`, and for small `ε` every other edge of the polygon
lies where `μ_ε ≥ 1`, so the push fixes it. For the edges away from `u` this follows by
compactness. The two edges adjacent to `u` leave `D` at `a` and at `b`, so `μ_ε` increases along
them for small `ε`.

## Main results

* `Polygon.IsDeltaMove.exists_ambientIsotopy_boundaryParam`: a Δ-move on a simple polygon is
  realized by an ambient isotopy carrying the traversal of the polygon onto the traversal of the
  moved polygon, after an increasing change of time.
* `Polygon.IsDeltaMove.exists_ambientIsotopy_image_boundary`: the same, for the boundaries as
  sets.
* `TauCeti.SimplePolygon.CombinatoriallyEquivalent.exists_ambientIsotopy_image_boundary`:
  combinatorially equivalent simple polygons are ambient isotopic.

## References

* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1 §B, Definitions 1.6 and 1.7 and Proposition 1.10.
-/

open Set Function Filter Topology AffineMap

/-! ### A sublinear function adapted to a triangle -/

namespace Polygon

section Frame

/-- Coordinates adapted to a triangle with vertices `α`, `-α` and `γ` in `V`: continuous linear
functionals `f`, `g` reading off the coefficients of `α` and `γ`. -/
private structure Frame (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  α : V
  γ : V
  f : StrongDual ℝ V
  g : StrongDual ℝ V
  f_α : f α = 1
  f_γ : f γ = 0
  g_α : g α = 0
  g_γ : g γ = 1

namespace Frame

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : Frame V)

/-- The component of `w` off the plane spanned by `α` and `γ`. -/
private noncomputable def proj (w : V) : V :=
  w - F.f w • F.α - F.g w • F.γ

private theorem proj_add (w w' : V) : F.proj (w + w') = F.proj w + F.proj w' := by
  simp only [proj, map_add, add_smul]
  abel

private theorem proj_smul (r : ℝ) (w : V) : F.proj (r • w) = r • F.proj w := by
  simp only [proj, map_smul, smul_eq_mul, smul_sub, mul_smul]

private theorem proj_smul_α (s : ℝ) : F.proj (s • F.α) = 0 := by
  simp [proj, F.f_α, F.g_α]

private theorem proj_γ : F.proj F.γ = 0 := by
  simp [proj, F.f_γ, F.g_γ]

private theorem continuous_proj : Continuous F.proj := by
  unfold proj
  fun_prop

/-- The sublinear function whose sublevel set `{gauge ε ≤ 1}` is a thickening of the triangle
`{a α + b γ | 0 ≤ b, |a| + b ≤ 1}` with vertices `α`, `-α`, `γ`, which shrinks to the triangle
as `ε → 0`: it contains `γ` in its interior and has `±α` on its boundary. -/
private noncomputable def gauge (ε : ℝ) (w : V) : ℝ :=
  |F.f w| + max ((1 - ε) * F.g w) (-F.g w / ε) + ‖F.proj w‖ / ε

/-- The closed triangle with vertices `α`, `-α` and `γ`. -/
private def Mem (w : V) : Prop :=
  F.proj w = 0 ∧ 0 ≤ F.g w ∧ |F.f w| + F.g w ≤ 1

variable {F} {ε : ℝ}

private theorem continuous_gauge (ε : ℝ) : Continuous (F.gauge ε) := by
  have := F.continuous_proj
  unfold gauge
  fun_prop

private theorem max_nonneg (hε : 0 < ε) (hε₁ : ε ≤ 1) (x : ℝ) :
    0 ≤ max ((1 - ε) * x) (-x / ε) := by
  rcases le_total 0 x with hx | hx
  · exact le_max_of_le_left (mul_nonneg (by linarith) hx)
  · exact le_max_of_le_right (div_nonneg (by linarith) hε.le)

private theorem gauge_nonneg (hε : 0 < ε) (hε₁ : ε ≤ 1) (w : V) : 0 ≤ F.gauge ε w :=
  add_nonneg (add_nonneg (abs_nonneg _) (max_nonneg hε hε₁ _)) (div_nonneg (norm_nonneg _) hε.le)

private theorem gauge_add_le (hε : 0 < ε) (w w' : V) :
    F.gauge ε (w + w') ≤ F.gauge ε w + F.gauge ε w' := by
  have h₁ : |F.f (w + w')| ≤ |F.f w| + |F.f w'| := by
    rw [map_add]
    exact abs_add_le _ _
  have h₂ : max ((1 - ε) * F.g (w + w')) (-F.g (w + w') / ε) ≤
      max ((1 - ε) * F.g w) (-F.g w / ε) + max ((1 - ε) * F.g w') (-F.g w' / ε) := by
    rw [map_add, mul_add, neg_add, add_div]
    exact max_add_add_le_max_add_max
  have h₃ : ‖F.proj (w + w')‖ / ε ≤ ‖F.proj w‖ / ε + ‖F.proj w'‖ / ε := by
    rw [← add_div, proj_add]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) hε.le
  unfold gauge
  linarith

private theorem gauge_smul {r : ℝ} (hr : 0 ≤ r) (w : V) :
    F.gauge ε (r • w) = r * F.gauge ε w := by
  simp only [gauge, map_smul, smul_eq_mul, proj_smul, norm_smul, Real.norm_of_nonneg hr,
    abs_mul, abs_of_nonneg hr]
  rw [show (1 - ε) * (r * F.g w) = r * ((1 - ε) * F.g w) by ring,
    show -(r * F.g w) / ε = r * (-F.g w / ε) by ring, ← mul_max_of_nonneg _ _ hr]
  ring

private theorem gauge_smul_α (s : ℝ) : F.gauge ε (s • F.α) = |s| := by
  simp [gauge, F.f_α, F.g_α, proj_smul_α]

private theorem gauge_γ (hε : 0 < ε) (hε₁ : ε ≤ 1) : F.gauge ε F.γ = 1 - ε := by
  have : -1 / ε ≤ 1 - ε := by
    rw [neg_div]
    linarith [div_pos one_pos hε]
  simp [gauge, F.f_γ, F.g_γ, proj_γ, this]

/-- The gauges increase as `ε` decreases. -/
private theorem gauge_anti {ε' : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε') (hε' : ε' ≤ 1) (w : V) :
    F.gauge ε' w ≤ F.gauge ε w := by
  have hε'₀ : 0 < ε' := hε.trans_le hεε'
  have h₁ : ‖F.proj w‖ / ε' ≤ ‖F.proj w‖ / ε :=
    div_le_div_of_nonneg_left (norm_nonneg _) hε hεε'
  have h₂ : max ((1 - ε') * F.g w) (-F.g w / ε') ≤ max ((1 - ε) * F.g w) (-F.g w / ε) := by
    rcases le_total 0 (F.g w) with hg | hg
    · have h₃ : -F.g w / ε' ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε'₀.le
      have h₄ : 0 ≤ (1 - ε) * F.g w := mul_nonneg (by linarith) hg
      exact max_le (le_max_of_le_left (by nlinarith)) (le_max_of_le_left (h₃.trans h₄))
    · have h₃ : 0 ≤ -F.g w / ε := div_nonneg (by linarith) hε.le
      have h₄ : (1 - ε') * F.g w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hg
      exact max_le (le_max_of_le_right (h₄.trans h₃))
        (le_max_of_le_right (div_le_div_of_nonneg_left (by linarith) hε hεε'))
  unfold gauge
  linarith

/-- A point with `gauge ε w ≤ 1` for all `ε ∈ (0, 1)` lies in the triangle. -/
private theorem mem_of_forall_gauge_le_one {w : V} (h : ∀ ε ∈ Ioo (0 : ℝ) 1, F.gauge ε w ≤ 1) :
    F.Mem w := by
  have hmax := fun ε (hε : ε ∈ Ioo (0 : ℝ) 1) => max_nonneg hε.1 hε.2.le (F.g w)
  have hpr := fun ε (hε : ε ∈ Ioo (0 : ℝ) 1) => div_nonneg (norm_nonneg (F.proj w)) hε.1.le
  have hfa := abs_nonneg (F.f w)
  -- The off-plane component vanishes.
  have hp : F.proj w = 0 := by
    by_contra hp
    have hN := norm_pos_iff.2 hp
    set ε := min (‖F.proj w‖ / 2) (1 / 2) with hε
    have hε₀ : 0 < ε := lt_min (by positivity) (by norm_num)
    have hε₁ : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have h₁ := h ε ⟨hε₀, hε₁⟩
    have h₂ : 2 ≤ ‖F.proj w‖ / ε := by
      rw [le_div_iff₀ hε₀]
      linarith [min_le_left (‖F.proj w‖ / 2) (1 / 2)]
    unfold gauge at h₁
    linarith [hmax ε ⟨hε₀, hε₁⟩]
  -- The `γ`-coordinate is nonnegative.
  have hg : 0 ≤ F.g w := by
    by_contra hg
    push Not at hg
    set ε := min (-F.g w / 2) (1 / 2) with hε
    have hε₀ : 0 < ε := lt_min (by linarith) (by norm_num)
    have hε₁ : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have h₁ := h ε ⟨hε₀, hε₁⟩
    have h₂ : 2 ≤ -F.g w / ε := by
      rw [le_div_iff₀ hε₀]
      linarith [min_le_left (-F.g w / 2) (1 / 2)]
    unfold gauge at h₁
    linarith [le_max_right ((1 - ε) * F.g w) (-F.g w / ε), hpr ε ⟨hε₀, hε₁⟩]
  -- The two coordinates satisfy the triangle inequality `|a| + b ≤ 1` in the limit `ε → 0`.
  refine ⟨hp, hg, ?_⟩
  by_contra hfg
  push Not at hfg
  set δ := |F.f w| + F.g w - 1 with hδ
  have hδ₀ : 0 < δ := by linarith
  set ε := min (1 / 2) (δ / (2 * (F.g w + 1))) with hε
  have hε₀ : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε₁ : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have h₁ := h ε ⟨hε₀, hε₁⟩
  have h₂ : ε * F.g w < δ := by
    have : ε * (F.g w + 1) ≤ δ / 2 := by
      calc ε * (F.g w + 1) ≤ δ / (2 * (F.g w + 1)) * (F.g w + 1) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
        _ = δ / 2 := by field_simp
    nlinarith
  unfold gauge at h₁
  linarith [le_max_left ((1 - ε) * F.g w) (-F.g w / ε), hpr ε ⟨hε₀, hε₁⟩]

private theorem proj_α : F.proj F.α = 0 := by
  simpa using F.proj_smul_α 1

private theorem gauge_α : F.gauge ε F.α = 1 := by
  simpa using F.gauge_smul_α (ε := ε) 1

/-- Near `α`, the gauge grows linearly along the ray from `α` in the direction `w`. -/
private theorem gauge_add_smul {w : V} (ε : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (h1 : 0 ≤ 1 + τ * F.f w) :
    F.gauge ε (F.α + τ • w) =
      1 + τ * (F.f w + max ((1 - ε) * F.g w) (-F.g w / ε) + ‖F.proj w‖ / ε) := by
  simp only [gauge, map_add, map_smul, smul_eq_mul, F.f_α, F.g_α, proj_add, proj_smul,
    proj_α, zero_add, norm_smul, Real.norm_of_nonneg hτ, abs_of_nonneg h1]
  rw [show (1 - ε) * (τ * F.g w) = τ * ((1 - ε) * F.g w) by ring,
    show -(τ * F.g w) / ε = τ * (-F.g w / ε) by ring, ← mul_max_of_nonneg _ _ hτ]
  ring

/-- Along a direction `w` leaving the triangle at the vertex `α`, the rate of growth of the gauge
at `α` is eventually nonnegative as `ε → 0`. -/
private theorem eventually_rate_nonneg {w : V}
    (hw : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ¬F.Mem (F.α + τ • w)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ F.f w + max ((1 - ε) * F.g w) (-F.g w / ε) + ‖F.proj w‖ / ε := by
  have hinv : Tendsto (fun ε : ℝ => ε⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have hε1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  by_cases hp : F.proj w = 0
  · rcases lt_or_ge (F.g w) 0 with hg | hg
    · -- Leaving the plane of the triangle below the edge `[-α, α]`.
      have ht : Tendsto (fun ε : ℝ => -F.g w * ε⁻¹) (𝓝[>] 0) atTop :=
        hinv.const_mul_atTop (by linarith)
      filter_upwards [ht.eventually_ge_atTop (-F.f w)] with ε hε
      have : -F.g w / ε = -F.g w * ε⁻¹ := div_eq_mul_inv _ _
      simp only [hp, norm_zero, zero_div, add_zero]
      linarith [le_max_right ((1 - ε) * F.g w) (-F.g w / ε)]
    · rcases lt_or_ge 0 (F.f w + F.g w) with hfg | hfg
      · -- Leaving the triangle across its side `[α, γ]`.
        have ht : Tendsto (fun ε : ℝ => F.f w + (1 - ε) * F.g w) (𝓝[>] 0)
            (𝓝 (F.f w + F.g w)) := by
          have : Tendsto (fun ε : ℝ => F.f w + (1 - ε) * F.g w) (𝓝 0)
              (𝓝 (F.f w + (1 - 0) * F.g w)) :=
            ((continuous_const.add ((continuous_const.sub continuous_id).mul
              continuous_const)).tendsto 0)
          simpa using this.mono_left nhdsWithin_le_nhds
        filter_upwards [ht.eventually_const_lt hfg] with ε hε
        simp only [hp, norm_zero, zero_div, add_zero]
        linarith [le_max_left ((1 - ε) * F.g w) (-F.g w / ε)]
      · -- Otherwise the ray from `α` starts inside the triangle.
        exfalso
        have h1 : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 ≤ 1 + τ * F.f w := by
          have : Tendsto (fun τ : ℝ => 1 + τ * F.f w) (𝓝 0) (𝓝 (1 + 0 * F.f w)) :=
            (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
          exact (this.mono_left nhdsWithin_le_nhds).eventually_const_le
            (by norm_num : (0 : ℝ) < 1 + 0 * F.f w)
        have hmem : ∀ᶠ τ in 𝓝[>] (0 : ℝ), F.Mem (F.α + τ • w) := by
          filter_upwards [self_mem_nhdsWithin, h1] with τ hτ h1
          refine ⟨by simp [proj_add, proj_smul, proj_α, hp], ?_, ?_⟩
          · simpa [F.g_α] using mul_nonneg (le_of_lt hτ) hg
          · simp only [map_add, map_smul, smul_eq_mul, F.f_α, F.g_α, zero_add,
              abs_of_nonneg h1]
            nlinarith [le_of_lt (show (0 : ℝ) < τ from hτ)]
        obtain ⟨τ, h₁, h₂⟩ := (hw.and hmem).exists
        exact h₁ h₂
  · -- Leaving the plane of the triangle.
    have ht : Tendsto (fun ε : ℝ => ‖F.proj w‖ * ε⁻¹) (𝓝[>] 0) atTop :=
      hinv.const_mul_atTop (norm_pos_iff.2 hp)
    filter_upwards [ht.eventually_ge_atTop (|F.f w| + |F.g w|), hε1] with ε hε hε'
    have h₁ : -|F.g w| ≤ (1 - ε) * F.g w := by
      rcases le_total 0 (F.g w) with hg | hg
      · nlinarith [abs_nonneg (F.g w), hε'.2]
      · rw [abs_of_nonpos hg]
        nlinarith [hε'.1]
    have : ‖F.proj w‖ / ε = ‖F.proj w‖ * ε⁻¹ := div_eq_mul_inv _ _
    linarith [le_max_left ((1 - ε) * F.g w) (-F.g w / ε), neg_abs_le (F.f w)]

/-- Along a direction `w` leaving the triangle at the vertex `α`, the gauges are eventually at
least `1` on the whole ray from `α`: the triangle meets the ray from `α` only at `α`, and the
sublevel sets of the gauges shrink to the triangle. -/
private theorem eventually_one_le_gauge_add_smul {w : V}
    (hw : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ¬F.Mem (F.α + τ • w)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ τ : ℝ, 0 ≤ τ → 1 ≤ F.gauge ε (F.α + τ • w) := by
  filter_upwards [F.eventually_rate_nonneg hw, Ioo_mem_nhdsGT one_pos] with ε hdε hε τ hτ
  -- Up to the parameter `τ₀`, the gauge is `1 + τ * d` with `d ≥ 0`; beyond it, convexity takes
  -- over.
  set τ₀ : ℝ := 1 / (|F.f w| + 1) with hτ₀
  have hτ₀pos : 0 < τ₀ := by positivity
  have hτ₀f : ∀ τ', 0 ≤ τ' → τ' ≤ τ₀ → 0 ≤ 1 + τ' * F.f w := by
    intro τ' h0 h1
    have : τ' * |F.f w| ≤ τ₀ * |F.f w| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    have : τ₀ * |F.f w| < 1 := by
      rw [hτ₀, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
      linarith
    nlinarith [neg_abs_le (F.f w), abs_nonneg (F.f w)]
  rcases le_or_gt τ τ₀ with hττ₀ | hττ₀
  · rw [F.gauge_add_smul ε hτ (hτ₀f τ hτ hττ₀)]
    nlinarith
  · have hτpos : 0 < τ := hτ₀pos.trans hττ₀
    have hconv : F.α + τ₀ • w = (1 - τ₀ / τ) • F.α + (τ₀ / τ) • (F.α + τ • w) := by
      rw [smul_add, smul_smul, div_mul_cancel₀ _ hτpos.ne', sub_smul, one_smul]
      abel
    have hle := F.gauge_add_le hε.1 ((1 - τ₀ / τ) • F.α) ((τ₀ / τ) • (F.α + τ • w))
    rw [← hconv, F.gauge_smul (sub_nonneg.2 ((div_le_one hτpos).2 hττ₀.le)),
      F.gauge_smul (div_nonneg hτ₀pos.le hτpos.le), gauge_α,
      F.gauge_add_smul ε hτ₀pos.le (hτ₀f τ₀ hτ₀pos.le le_rfl)] at hle
    have hq : 0 < τ₀ / τ := div_pos hτ₀pos hτpos
    nlinarith

/-- The same frame with `α` and its coordinate negated: it describes the same triangle, with the
vertices `α` and `-α` exchanged. -/
private def neg : Frame V where
  α := -F.α
  γ := F.γ
  f := -F.f
  g := F.g
  f_α := by simp [F.f_α]
  f_γ := by simp [F.f_γ]
  g_α := by simp [F.g_α]
  g_γ := F.g_γ

private theorem neg_α : F.neg.α = -F.α := (rfl)

private theorem gauge_neg : F.neg.gauge ε = F.gauge ε := by
  funext w
  simp [gauge, proj, neg]

private theorem mem_neg {w : V} : F.neg.Mem w ↔ F.Mem w := by
  simp [Mem, proj, neg]

/-- The gauges are eventually at least `1` on a compact set disjoint from the triangle. -/
private theorem eventually_forall_one_le_gauge {K : Set V} (hK : IsCompact K)
    (h : ∀ w ∈ K, ¬F.Mem w) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ w ∈ K, 1 ≤ F.gauge ε w := by
  have : Nonempty (Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  let t : Ioo (0 : ℝ) 1 → Set V := fun ε => {w | F.gauge ε w ≤ 1}
  have htc : ∀ ε, IsClosed (t ε) := fun ε => isClosed_le (continuous_gauge _) continuous_const
  have hst : Disjoint K (⋂ ε, t ε) := by
    refine Set.disjoint_left.2 fun w hwK hw => h w hwK (mem_of_forall_gauge_le_one fun ε hε => ?_)
    exact mem_iInter.1 hw ⟨ε, hε⟩
  have hdt : Directed (· ⊇ ·) t := by
    intro ε₁ ε₂
    refine ⟨⟨min ε₁ ε₂, lt_min ε₁.2.1 ε₂.2.1, (min_le_left _ _).trans_lt ε₁.2.2⟩,
      fun w hw => ?_, fun w hw => ?_⟩
    · exact (gauge_anti (lt_min ε₁.2.1 ε₂.2.1) (min_le_left _ _) ε₁.2.2.le w).trans hw
    · exact (gauge_anti (lt_min ε₁.2.1 ε₂.2.1) (min_le_right _ _) ε₂.2.2.le w).trans hw
  obtain ⟨ε₀, hε₀⟩ := hK.elim_directed_family_closed t htc hst hdt
  filter_upwards [Ioc_mem_nhdsGT ε₀.2.1] with ε hε w hw
  by_contra hlt
  push Not at hlt
  exact Set.disjoint_left.1 hε₀ hw
    ((gauge_anti hε.1 hε.2 ε₀.2.2.le w).trans hlt.le)

end Frame

end Frame

/-! ### The frame of a Δ-move -/

section DeltaMoveFrame

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {n : ℕ} {poly : Polygon P n} {i : Fin n} {c : P}

/-- Two linearly independent vectors of a real normed space have continuous coordinate
functionals. -/
private theorem exists_frame_of_linearIndependent {α γ : V}
    (hli : LinearIndependent ℝ ![α, γ]) :
    ∃ F : Frame V, F.α = α ∧ F.γ = γ := by
  have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range ![α, γ])) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  let b := Module.Basis.span hli
  let φ : Submodule.span ℝ (Set.range ![α, γ]) →L[ℝ] (Fin 2 → ℝ) :=
    LinearMap.toContinuousLinearMap b.equivFun.toLinearMap
  obtain ⟨L, hL⟩ := φ.exist_extension_of_finiteDimensional_range
  have hL' : ∀ k : Fin 2, L (![α, γ] k) = Pi.single k 1 := by
    intro k
    have h₁ : (⟨![α, γ] k, Submodule.subset_span (Set.mem_range_self k)⟩ :
        Submodule.span ℝ (Set.range ![α, γ])) = b k :=
      (Module.Basis.span_apply hli k).symm
    have h₂ := congrArg (fun T => T ⟨![α, γ] k, Submodule.subset_span (Set.mem_range_self k)⟩) hL
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Submodule.subtypeL_apply] at h₂
    rw [← h₂, h₁]
    simp [φ, Finsupp.single_eq_pi_single]
  refine ⟨⟨α, γ, (ContinuousLinearMap.proj 0).comp L, (ContinuousLinearMap.proj 1).comp L,
    ?_, ?_, ?_, ?_⟩, rfl, rfl⟩ <;>
  simp [show L α = Pi.single 0 1 from hL' 0, show L γ = Pi.single 1 1 from hL' 1]

/-- The vectors from the midpoint `m` of the replaced edge to its start and to the new vertex of a
Δ-move are linearly independent. -/
private theorem IsDeltaMove.linearIndependent_vsub_midpoint (h : poly.IsDeltaMove ℝ i c) :
    LinearIndependent ℝ ![poly i -ᵥ midpoint ℝ (poly i) (poly (finRotate n i)),
      c -ᵥ midpoint ℝ (poly i) (poly (finRotate n i))] := by
  set a := poly i
  set b := poly (finRotate n i)
  set m := midpoint ℝ a b
  rw [LinearIndependent.pair_iff]
  intro s t hst
  -- Read `s • (a - m) + t • (c - m) = 0` as a vanishing weighted difference of `a`, `b`, `c`.
  have hw : ∑ k, ![(s - t) / 2, (-s - t) / 2, t] k = 0 := by
    simp [Fin.sum_univ_three]
    ring
  have hv : Finset.univ.weightedVSub ![a, b, c] ![(s - t) / 2, (-s - t) / 2, t] = (0 : V) := by
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw m,
      Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
    have hb : b -ᵥ m = -(a -ᵥ m) := by
      rw [right_vsub_midpoint, left_vsub_midpoint, ← neg_vsub_eq_vsub_rev a b, smul_neg]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, hb]
    rw [← hst]
    module
  have h0 := h.affineIndependent Finset.univ _ hw hv
  have ht : t = 0 := by simpa using h0 2 (Finset.mem_univ _)
  have hs : (s - t) / 2 = 0 := by simpa using h0 0 (Finset.mem_univ _)
  exact ⟨by linarith, ht⟩

/-- The frame of a Δ-move, centred at the midpoint of the replaced edge. -/
private theorem IsDeltaMove.exists_frame (h : poly.IsDeltaMove ℝ i c) :
    ∃ F : Frame V, F.α = poly i -ᵥ midpoint ℝ (poly i) (poly (finRotate n i)) ∧
      F.γ = c -ᵥ midpoint ℝ (poly i) (poly (finRotate n i)) :=
  exists_frame_of_linearIndependent h.linearIndependent_vsub_midpoint

/-- The point `w +ᵥ m`, for `w` in the triangle of a frame of a Δ-move centred at the midpoint `m`
of the replaced edge, lies in the triangle of the Δ-move. -/
private theorem IsDeltaMove.vadd_mem_closedInterior (h : poly.IsDeltaMove ℝ i c) {F : Frame V}
    (hα : F.α = poly i -ᵥ midpoint ℝ (poly i) (poly (finRotate n i)))
    (hγ : F.γ = c -ᵥ midpoint ℝ (poly i) (poly (finRotate n i))) {w : V} (hw : F.Mem w) :
    w +ᵥ midpoint ℝ (poly i) (poly (finRotate n i)) ∈ h.triangle.closedInterior := by
  set m := midpoint ℝ (poly i) (poly (finRotate n i))
  obtain ⟨hp, hg, hfg⟩ := hw
  have hwe : w = F.f w • F.α + F.g w • F.γ := by
    unfold Frame.proj at hp
    rw [sub_sub, sub_eq_zero] at hp
    exact hp
  have hb : poly (finRotate n i) -ᵥ m = -F.α := by
    rw [hα, right_vsub_midpoint, left_vsub_midpoint, ← neg_vsub_eq_vsub_rev (poly i), smul_neg]
  have hsum : ∑ k, ![(1 + F.f w - F.g w) / 2, (1 - F.f w - F.g w) / 2, F.g w] k = 1 := by
    simp [Fin.sum_univ_three]
    ring
  have hfa := abs_le.1 (le_refl |F.f w|)
  refine ⟨_, hsum, fun k => ?_, ?_⟩
  · fin_cases k <;> simp <;> constructor <;> linarith [hfa.1, hfa.2, abs_nonneg (F.f w)]
  · rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ hsum m,
      Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three, IsDeltaMove.triangle_points]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, hb, ← hα, ← hγ]
    congr 1
    conv_rhs => rw [hwe]
    module

/-- Along a segment `[v, v']` leaving the triangle at the vertex `v` of a frame `G`, the gauges
of `G` are eventually at least `1`, when the segment meets the triangle only at `v` and at another
vertex `u`. -/
private theorem Frame.eventually_one_le_gauge_affineSegment (G : Frame V) {m v v' u : P}
    {D : Set P} (hG : ∀ w, G.Mem w → w +ᵥ m ∈ D) (hv : G.α = v -ᵥ m) (hvv' : v ≠ v')
    (hvu : v ≠ u) (hD : ∀ x ∈ affineSegment ℝ v v', x ∈ D → x = v ∨ x = u) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ affineSegment ℝ v v', 1 ≤ G.gauge ε (x -ᵥ m) := by
  have hpt : ∀ τ : ℝ, lineMap v v' τ -ᵥ m = G.α + τ • (v' -ᵥ v) := by
    intro τ
    rw [hv, lineMap_apply, vadd_vsub_assoc]
    abel
  have key := G.eventually_one_le_gauge_add_smul (w := v' -ᵥ v) <| by
    have h₁ : ∀ᶠ τ in 𝓝[>] (0 : ℝ), lineMap v v' τ ≠ u := by
      have : Tendsto (fun τ : ℝ => lineMap v v' τ) (𝓝 0) (𝓝 (lineMap v v' (0 : ℝ))) :=
        (AffineMap.lineMap_continuous (p := v) (q := v')).tendsto 0
      rw [lineMap_apply_zero] at this
      exact (this.mono_left nhdsWithin_le_nhds).eventually_ne hvu
    filter_upwards [h₁, Ioo_mem_nhdsGT one_pos] with τ hτu hτ hmem
    have hx : lineMap v v' τ ∈ affineSegment ℝ v v' := ⟨τ, ⟨hτ.1.le, hτ.2.le⟩, rfl⟩
    have hxD : lineMap v v' τ ∈ D := by
      have := hG _ hmem
      rwa [← hpt, vsub_vadd] at this
    rcases hD _ hx hxD with h | h
    · rcases AffineMap.lineMap_eq_left_iff.1 h with h | h
      · exact hvv' h
      · exact hτ.1.ne' h
    · exact hτu h
  filter_upwards [key] with ε hε x hx
  obtain ⟨τ, hτ, rfl⟩ := hx
  rw [hpt]
  exact hε τ hτ.1

/-- On a compact set disjoint from the image of the triangle of a frame `G`, the gauges of `G` are
eventually at least `1`. -/
private theorem Frame.eventually_one_le_gauge_of_disjoint (G : Frame V) {m : P} {D K : Set P}
    (hG : ∀ w, G.Mem w → w +ᵥ m ∈ D) (hK : IsCompact K) (hKD : Disjoint K D) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ K, 1 ≤ G.gauge ε (x -ᵥ m) := by
  have := G.eventually_forall_one_le_gauge
    (hK.image (continuous_id.vsub continuous_const) : IsCompact ((· -ᵥ m) '' K)) <| by
      rintro _ ⟨x, hx, rfl⟩ hmem
      have := hG _ hmem
      rw [vsub_vadd] at this
      exact Set.disjoint_left.1 hKD hx this
  filter_upwards [this] with ε hε x hx
  exact hε _ ⟨x, hx, rfl⟩

/-- On every edge of a simple polygon other than the one replaced by a Δ-move, the gauges of the
frame of the move are eventually at least `1`. -/
private theorem IsDeltaMove.eventually_one_le_gauge_edgeSet (hp : poly.IsSimple ℝ)
    (h : poly.IsDeltaMove ℝ i c) {F : Frame V}
    (hα : F.α = poly i -ᵥ midpoint ℝ (poly i) (poly (finRotate n i)))
    (hγ : F.γ = c -ᵥ midpoint ℝ (poly i) (poly (finRotate n i))) {k : Fin n} (hk : k ≠ i) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ poly.edgeSet ℝ k,
      1 ≤ F.gauge ε (x -ᵥ midpoint ℝ (poly i) (poly (finRotate n i))) := by
  set m := midpoint ℝ (poly i) (poly (finRotate n i))
  have hG : ∀ w, F.Mem w → w +ᵥ m ∈ h.triangle.closedInterior :=
    fun w hw => h.vadd_mem_closedInterior hα hγ hw
  have hD : ∀ x ∈ poly.edgeSet ℝ k, x ∈ h.triangle.closedInterior →
      x = poly i ∨ x = poly (finRotate n i) := fun x hx hxD =>
    h.edgeSet_inter_closedInterior_subset hk ⟨hx, hxD⟩
  have hab : poly i ≠ poly (finRotate n i) := hp.hasNondegenerateEdges i
  by_cases hk₁ : finRotate n k = i
  · -- The edge ending at the start of the replaced edge.
    have hseg : poly.edgeSet ℝ k = affineSegment ℝ (poly i) (poly k) := by
      rw [Polygon.edgeSet, hk₁, affineSegment_comm]
    have hne : poly i ≠ poly k := by
      rw [← hk₁]
      exact (hp.hasNondegenerateEdges k).symm
    rw [hseg]
    exact F.eventually_one_le_gauge_affineSegment hG hα hne hab fun x hx hxD =>
      hD x (hseg ▸ hx) hxD
  by_cases hk₂ : k = finRotate n i
  · -- The edge starting at the end of the replaced edge, read in the negated frame.
    have hseg : poly.edgeSet ℝ k =
        affineSegment ℝ (poly (finRotate n i)) (poly (finRotate n k)) := by
      rw [Polygon.edgeSet, hk₂]
    have hneg : F.neg.α = poly (finRotate n i) -ᵥ m := by
      rw [Frame.neg_α, hα, right_vsub_midpoint, left_vsub_midpoint,
        ← neg_vsub_eq_vsub_rev (poly i), smul_neg]
    have hne : poly (finRotate n i) ≠ poly (finRotate n k) := by
      rw [← hk₂]
      exact hp.hasNondegenerateEdges k
    rw [hseg]
    have := F.neg.eventually_one_le_gauge_affineSegment (fun w hw => hG w (F.mem_neg.1 hw)) hneg
      hne hab.symm fun x hx hxD => (hD x (hseg ▸ hx) hxD).symm
    simpa only [Frame.gauge_neg] using this
  · -- An edge disjoint from the replaced edge misses the triangle.
    have hdisj : Disjoint (poly.edgeSet ℝ k) h.triangle.closedInterior := by
      refine Set.disjoint_left.2 fun x hx hxD => ?_
      rcases hD x hx hxD with rfl | rfl
      · rcases hp.eq_vertex_of_mem_edgeSet hk hx (poly.apply_mem_edgeSet_self ℝ i) with
          ⟨h₁, -⟩ | ⟨h₁, -⟩
        · exact hk₁ h₁.symm
        · exact hk₂ h₁
      · rcases hp.eq_vertex_of_mem_edgeSet hk hx (poly.apply_finRotate_mem_edgeSet ℝ i) with
          ⟨h₁, -⟩ | ⟨h₁, -⟩
        · exact hk₁ h₁.symm
        · exact hk₂ h₁
    have hK : IsCompact (poly.edgeSet ℝ k) := by
      rw [edgeSet_eq_image_edgePath]
      exact isCompact_Icc.image (AffineMap.lineMap_continuous)
    exact F.eventually_one_le_gauge_of_disjoint hG hK hdisj

/-- **The push of a Δ-move.** For a Δ-move on a simple polygon, there is an ambient isotopy whose
final map carries each edge of the polygon subdivided at the midpoint `m` of the replaced edge onto
the corresponding edge of the moved polygon, parameter by parameter. It is the push from `m` to
the new vertex `c` weighted by the gauge of a thickening of the triangle of the move: it fixes the
other edges and drags the two halves of the replaced edge onto the two new edges. -/
private theorem IsDeltaMove.exists_ambientIsotopy_edgePath (hp : poly.IsSimple ℝ)
    (h : poly.IsDeltaMove ℝ i c) :
    ∃ Φ : TauCeti.AmbientIsotopy P, ∀ (j : Fin (n + 1)), ∀ s ∈ Icc (0 : ℝ) 1,
      Φ.final ((poly.insertVertex i (midpoint ℝ (poly i) (poly (finRotate n i)))).edgePath ℝ j s) =
        (poly.insertVertex i c).edgePath ℝ j s := by
  set a := poly i
  set b := poly (finRotate n i)
  set m := midpoint ℝ a b
  obtain ⟨F, hα, hγ⟩ := h.exists_frame
  -- Choose `ε` so that the gauge is at least `1` on all the other edges.
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ k, k ≠ i → ∀ x ∈ poly.edgeSet ℝ k,
      1 ≤ F.gauge ε (x -ᵥ m) := by
    rw [Filter.eventually_all]
    intro k
    by_cases hk : k = i
    · exact Eventually.of_forall fun _ h => absurd hk h
    · filter_upwards [h.eventually_one_le_gauge_edgeSet hp hα hγ hk] with ε hε _ x hx
      exact hε x hx
  obtain ⟨ε, hεk, hε⟩ := (hall.and (Ioo_mem_nhdsGT one_pos)).exists
  have hv : ∀ (w : V) (r : ℝ), 0 < r → F.gauge ε (w + r • F.γ) < F.gauge ε w + r := by
    intro w r hr
    have := F.gauge_add_le hε.1 w (r • F.γ)
    rw [F.gauge_smul hr.le, F.gauge_γ hε.1 hε.2.le] at this
    nlinarith [hε.1]
  have hb : b -ᵥ m = -F.α := by
    rw [hα, right_vsub_midpoint, left_vsub_midpoint, ← neg_vsub_eq_vsub_rev a, smul_neg]
  refine ⟨TauCeti.AmbientIsotopy.push (F.gauge ε) m F.γ (F.continuous_gauge ε)
    (F.gauge_nonneg hε.1 hε.2.le) hv, fun j s hs => ?_⟩
  rw [TauCeti.AmbientIsotopy.push_final_apply]
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i.succ j
  · -- The second half `[m, b]` of the replaced edge goes onto the second new edge `[c, b]`.
    rw [edgePath_insertVertex_succ_self, edgePath_insertVertex_succ_self]
    have hx : lineMap m b s -ᵥ m = (-s) • F.α := by
      rw [lineMap_vsub_left, hb, smul_neg, neg_smul]
    rw [hx, F.gauge_smul_α, abs_neg, abs_of_nonneg hs.1, max_eq_left (by linarith [hs.2])]
    refine (vsub_left_cancel_iff (p := m)).1 ?_
    rw [vadd_vsub_assoc, hx, lineMap_apply, vadd_vsub_assoc, ← vsub_sub_vsub_cancel_right b c m, hb,
      ← hγ]
    module
  · by_cases hk : k = i
    · -- The first half `[a, m]` of the replaced edge goes onto the first new edge `[a, c]`.
      subst hk
      rw [Fin.succAbove_succ_self, edgePath_insertVertex_castSucc_self,
        edgePath_insertVertex_castSucc_self]
      have hx : lineMap a m s -ᵥ m = (1 - s) • F.α := by
        rw [lineMap_vsub_right, hα]
      rw [hx, F.gauge_smul_α, abs_of_nonneg (by linarith [hs.2]), sub_sub_cancel,
        max_eq_left hs.1]
      refine (vsub_left_cancel_iff (p := m)).1 ?_
      rw [vadd_vsub_assoc, hx, lineMap_apply, vadd_vsub_assoc, ← vsub_sub_vsub_cancel_right c a m,
        ← hα, ← hγ]
      module
    · -- The other edges are fixed.
      rw [edgePath_insertVertex_succAbove _ _ _ hk, edgePath_insertVertex_succAbove _ _ _ hk]
      have : 1 ≤ F.gauge ε (poly.edgePath ℝ k s -ᵥ m) := hεk k hk _ ⟨s, hs, rfl⟩
      rw [max_eq_right (by linarith), zero_smul, zero_vadd]

end DeltaMoveFrame

end Polygon

public section

namespace Polygon

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {n : ℕ} {poly : Polygon P n} {i : Fin n} {c : P}

/-- **A Δ-move is realized by an ambient isotopy.** For a Δ-move on a simple polygon, there is an
ambient isotopy of the ambient space whose final homeomorphism respects the traversals: the
boundary parametrization of the polygon, followed by the final homeomorphism, is the boundary
parametrization of the moved polygon after an increasing change of time `φ`, which maps one
period `[0, n)` into `[0, n + 1)`. The final homeomorphism maps the boundary of the polygon onto
the boundary of the moved polygon (`Polygon.IsDeltaMove.exists_ambientIsotopy_image_boundary`). -/
theorem IsDeltaMove.exists_ambientIsotopy_boundaryParam [NeZero n] (hp : poly.IsSimple ℝ)
    (h : poly.IsDeltaMove ℝ i c) :
    ∃ Φ : TauCeti.AmbientIsotopy P, ∃ φ : ℝ → ℝ, StrictMono φ ∧ ∀ t ∈ Ico (0 : ℝ) n,
      φ t ∈ Ico (0 : ℝ) (n + 1 : ℕ) ∧
        Φ.final (poly.boundaryParam t) = (poly.insertVertex i c).boundaryParam (φ t) := by
  obtain ⟨Φ, hΦ⟩ := h.exists_ambientIsotopy_edgePath hp
  have hmid : poly.edgePath ℝ i 2⁻¹ = midpoint ℝ (poly i) (poly (finRotate n i)) := by
    rw [midpoint, invOf_eq_inv, Polygon.edgePath]
  obtain ⟨φ, hφ, hφt⟩ :=
    poly.exists_strictMono_boundaryParam_insertVertex_edgePath i (s := 2⁻¹)
      ⟨by norm_num, by norm_num⟩
  refine ⟨Φ, φ, hφ, fun t ht => ⟨(hφt t ht).1, ?_⟩⟩
  rw [← (hφt t ht).2.1, hmid, boundaryParam_eq_edgePath_edgeIndexAt,
    boundaryParam_eq_edgePath_edgeIndexAt]
  exact hΦ _ _ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

/-- **A Δ-move is realized by an ambient isotopy**, on the level of sets: for a Δ-move on a simple
polygon, there is an ambient isotopy of the ambient space whose final homeomorphism carries the
boundary of the polygon onto the boundary of the moved polygon. -/
theorem IsDeltaMove.exists_ambientIsotopy_image_boundary (hp : poly.IsSimple ℝ)
    (h : poly.IsDeltaMove ℝ i c) :
    ∃ Φ : TauCeti.AmbientIsotopy P,
      Φ.final '' poly.boundary ℝ = (poly.insertVertex i c).boundary ℝ := by
  obtain ⟨Φ, hΦ⟩ := h.exists_ambientIsotopy_edgePath hp
  refine ⟨Φ, ?_⟩
  have hmid : midpoint ℝ (poly i) (poly (finRotate n i)) = poly.edgePath ℝ i 2⁻¹ := by
    rw [midpoint, invOf_eq_inv, Polygon.edgePath]
  have hbdry : poly.boundary ℝ =
      (poly.insertVertex i (midpoint ℝ (poly i) (poly (finRotate n i)))).boundary ℝ := by
    rw [hmid, boundary_insertVertex_edgePath poly i ⟨by norm_num, by norm_num⟩]
  have hcomp : ⇑Φ.final ∘
      (poly.insertVertex i (midpoint ℝ (poly i) (poly (finRotate n i)))).boundaryParam =
        (poly.insertVertex i c).boundaryParam := by
    funext t
    rw [Function.comp_apply, boundaryParam_eq_edgePath_edgeIndexAt,
      boundaryParam_eq_edgePath_edgeIndexAt]
    exact hΦ _ _ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  rw [hbdry, ← range_boundaryParam, ← Set.range_comp, hcomp, range_boundaryParam]

end Polygon

namespace TauCeti

namespace SimplePolygon

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Combinatorially equivalent polygonal knots are ambient isotopic** (Burde–Zieschang,
Proposition 1.10, one direction): if two simple polygons are related by a sequence of Δ-moves,
their inverses and relabellings, some ambient isotopy of the ambient space carries the boundary of
the first onto the boundary of the second. -/
theorem CombinatoriallyEquivalent.exists_ambientIsotopy_image_boundary {p q : SimplePolygon ℝ P}
    (h : CombinatoriallyEquivalent p q) :
    ∃ Φ : AmbientIsotopy P, Φ.final '' p.toPolygon.boundary ℝ = q.toPolygon.boundary ℝ := by
  refine CombinatoriallyEquivalent.induction
    (motive := fun p q => ∃ Φ : AmbientIsotopy P,
      Φ.final '' p.toPolygon.boundary ℝ = q.toPolygon.boundary ℝ) (fun {p _} hpq => ?_)
    (fun p => ⟨AmbientIsotopy.refl P, by simp⟩) (fun _ ih => ?_) (fun _ _ ih₁ ih₂ => ?_) h
  · cases hpq with
    | rotate => exact ⟨AmbientIsotopy.refl P, by simp⟩
    | deltaMove i c h => exact h.exists_ambientIsotopy_image_boundary p.isSimple
    | subdivide i c hc hq =>
      have hb : (p.toPolygon.insertVertex i c).boundary ℝ = p.toPolygon.boundary ℝ := by
        obtain ⟨s, hs, rfl⟩ := hc
        exact Polygon.boundary_insertVertex_edgePath p.toPolygon i hs
      exact ⟨AmbientIsotopy.refl P, by simp [hb]⟩
  · obtain ⟨Φ, hΦ⟩ := ih
    refine ⟨Φ.symm, ?_⟩
    rw [← hΦ, Set.image_image]
    simp [AmbientIsotopy.symm_final_final]
  · obtain ⟨Φ, hΦ⟩ := ih₁
    obtain ⟨Ψ, hΨ⟩ := ih₂
    refine ⟨Φ.trans Ψ, ?_⟩
    rw [← hΨ, ← hΦ, Set.image_image]
    simp

end SimplePolygon

end TauCeti
