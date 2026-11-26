/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.LocalToGlobal
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.IntermediateValue

/-!
# Convexity charts of an indefinite quadratic form

Let `V` and `W` be real normed spaces and let `Q (a, b) = ‖b‖² - ‖a‖²` on `V × W`. This is the
local model of a Morse–Bott function near a critical point: by the Morse–Bott lemma, a function
`f` reads `f (i s) - ‖a‖² + ‖b‖²` in suitable coordinates `(x, a, b)` near a point of a
nondegenerate critical submanifold, the coordinates `a` spanning the negative directions of the
Hessian and `b` the positive ones.

This file shows that when neither `V` nor `W` has dimension one, `Q` is a *convex map* near the
origin in the sense of the local-to-global principle (`TauCeti.IsConvexChart`): on the ball
`R = {‖a‖² + ‖b‖² < r}`,

* every fibre `R ∩ {Q = v}` is preconnected
  (`TauCeti.isPreconnected_setOf_norm_sq_sub_norm_sq_eq`). For `v > 0` it is the image of
  `{a | v + 2 ‖a‖² < r} × S(W)` under `(a, u) ↦ (a, √(v + ‖a‖²) u)`, and the unit sphere `S(W)` is
  preconnected because `W` does not have dimension one; for `v = 0` it is a cone, star-shaped about
  the origin; and `v < 0` is the case `v > 0` with the factors exchanged;
* `Q` is open onto its range at every point (`TauCeti.image_norm_sq_sub_norm_sq_mem_nhdsWithin`),
  with no hypothesis on the dimensions. Near a point `(a, b)` with `a ≠ 0` shrinking `a` raises `Q`
  and enlarging it lowers `Q`, and similarly for `b`, so by the intermediate value theorem `Q` takes
  every nearby value on each side, except on a side where the range of `Q` stops: at the origin,
  `Q ≤ 0` when `W = 0` and `Q ≥ 0` when `V = 0`.

Hence for every preconnected open set `B` of a third space `P`, the product `B × R` is a convexity
chart of `(x, a, b) ↦ c + Q (a, b)` (`TauCeti.isConvexChart_prod_setOf_norm_sq_add_norm_sq_lt`),
and a map reading as this model in a chart has convexity charts at the points of the zero section
(`TauCeti.exists_isConvexChart_of_eqOn_norm_sq_sub_norm_sq`).

The hypothesis on the dimensions cannot be dropped: for `V = 0` and `W = ℝ` the fibre
`{b² = v}` of a positive value is the two points `±√v`. This is why the levels of a Morse–Bott
function are connected only in the absence of critical points of index or coindex one, as for the
components of a moment map.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15,
  § 2 (the levels of a Morse–Bott function without index or coindex one are connected).
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513, § 3.
-/

public section

open Filter Function Metric Set Topology

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-! ### The fibres -/

/-- A set closed under scaling by every `t ∈ [0, 1]` is preconnected: it is empty, or it contains
the origin and is star-shaped about it. -/
private theorem isPreconnected_of_forall_smul_mem {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} (hs : ∀ x ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ s) :
    IsPreconnected s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact isPreconnected_empty
  have h0 : (0 : E) ∈ s := by simpa using hs x hx 0 ⟨le_rfl, zero_le_one⟩
  exact (StarConvex.isPathConnected (starConvex_zero_iff.2 fun y hy t ht₀ ht₁ ↦
    hs y hy t ⟨ht₀, ht₁⟩) h0).isConnected.isPreconnected

/-- The fibres of `‖b‖² - ‖a‖²` of positive value in the ball `‖a‖² + ‖b‖² < r` are preconnected
when `W` does not have dimension one. -/
private theorem isPreconnected_setOf_norm_sq_sub_norm_sq_eq_of_pos (hW : Module.rank ℝ W ≠ 1)
    (r : ℝ) {v : ℝ} (hv : 0 < v) :
    IsPreconnected {y : V × W | ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 < r ∧ ‖y.2‖ ^ 2 - ‖y.1‖ ^ 2 = v} := by
  -- The fibre is the image of `D × S(W)` under `(a, u) ↦ (a, √(v + ‖a‖²) u)`.
  set D := {a : V | v + 2 * ‖a‖ ^ 2 < r}
  have himage : (fun p : V × W ↦ (p.1, √(v + ‖p.1‖ ^ 2) • p.2)) '' (D ×ˢ sphere (0 : W) 1) =
      {y : V × W | ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 < r ∧ ‖y.2‖ ^ 2 - ‖y.1‖ ^ 2 = v} := by
    ext ⟨a, b⟩
    simp only [mem_image, mem_prod, mem_sphere_zero_iff_norm, Prod.exists, Prod.mk.injEq,
      mem_ofPred_eq, D]
    constructor
    · rintro ⟨a, u, ⟨ha, hu⟩, rfl, rfl⟩
      have hsq : √(v + ‖a‖ ^ 2) ^ 2 = v + ‖a‖ ^ 2 := Real.sq_sqrt (by positivity)
      rw [norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs, hsq]
      constructor <;> linarith
    · rintro ⟨hr, hv'⟩
      have hb : 0 < ‖b‖ := by
        by_contra h
        rw [le_antisymm (not_lt.1 h) (norm_nonneg b)] at hv'
        nlinarith [sq_nonneg ‖a‖]
      have hsq : √(v + ‖a‖ ^ 2) = ‖b‖ := by
        rw [← hv', sub_add_cancel, Real.sqrt_sq hb.le]
      refine ⟨a, ‖b‖⁻¹ • b, ⟨by linarith, ?_⟩, rfl, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hb.ne']
      · rw [hsq, smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
  rw [← himage]
  -- `D` is closed under scaling by `t ∈ [0, 1]`.
  have hD : IsPreconnected D := isPreconnected_of_forall_smul_mem fun a ha t ht ↦ by
    simp only [D, mem_ofPred_eq, norm_smul, Real.norm_of_nonneg ht.1, mul_pow] at ha ⊢
    linarith [mul_le_of_le_one_left (sq_nonneg ‖a‖) (pow_le_one₀ (n := 2) ht.1 ht.2)]
  -- The unit sphere of `W` is preconnected, being empty in dimension zero.
  have hS : IsPreconnected (sphere (0 : W) 1) := by
    rcases hW.lt_or_gt with h | h
    · have : Subsingleton W := rank_zero_iff.1 (Cardinal.lt_one_iff.1 h)
      convert isPreconnected_empty
      refine eq_empty_of_forall_notMem fun u hu ↦ ?_
      rw [mem_sphere_zero_iff_norm, Subsingleton.elim u 0, norm_zero] at hu
      exact zero_ne_one hu
    · exact isPreconnected_sphere h 0 1
  exact (hD.prod hS).image _ (by fun_prop)

/-- **The fibres of an indefinite quadratic form are preconnected.** If neither `V` nor `W` has
dimension one, then for all `r` and `v` the points `(a, b)` of the ball `‖a‖² + ‖b‖² < r` with
`‖b‖² - ‖a‖² = v` form a preconnected set. -/
theorem isPreconnected_setOf_norm_sq_sub_norm_sq_eq (hV : Module.rank ℝ V ≠ 1)
    (hW : Module.rank ℝ W ≠ 1) (r v : ℝ) :
    IsPreconnected {y : V × W | ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 < r ∧ ‖y.2‖ ^ 2 - ‖y.1‖ ^ 2 = v} := by
  rcases lt_trichotomy v 0 with hv | rfl | hv
  · -- Exchanging the factors turns the fibre of `v` into the fibre of `-v`.
    have h := (isPreconnected_setOf_norm_sq_sub_norm_sq_eq_of_pos (V := W) hV r
      (neg_pos.2 hv)).image Prod.swap continuous_swap.continuousOn
    convert h using 1
    ext ⟨a, b⟩
    simp only [mem_ofPred_eq, image_swap_eq_preimage_swap, mem_preimage, Prod.fst_swap,
      Prod.snd_swap]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  · -- The fibre of `0` is closed under scaling by `t ∈ [0, 1]`.
    refine isPreconnected_of_forall_smul_mem fun y hy t ht ↦ ?_
    simp only [mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, norm_smul, Real.norm_of_nonneg ht.1,
      mul_pow] at hy ⊢
    have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.1 ht.2
    constructor
    · linarith [mul_le_of_le_one_left (sq_nonneg ‖y.1‖) ht2,
        mul_le_of_le_one_left (sq_nonneg ‖y.2‖) ht2]
    · rw [← mul_sub, hy.2, mul_zero]
  · exact isPreconnected_setOf_norm_sq_sub_norm_sq_eq_of_pos hW r hv

/-! ### Openness onto the range -/

/-- Above its value at `y`, the function `‖b‖² - ‖a‖²` maps every neighbourhood of `y` onto a set
containing an interval `[q y, b]` with `b > q y`, unless `y = 0` and `W = 0`, when its range lies
below `q y = 0`. -/
private theorem exists_Icc_subset_image_norm_sq_sub_norm_sq_or (y : V × W) {N : Set (V × W)}
    (hN : N ∈ 𝓝 y) :
    (∃ b > ‖y.2‖ ^ 2 - ‖y.1‖ ^ 2,
        Icc (‖y.2‖ ^ 2 - ‖y.1‖ ^ 2) b ⊆ (fun z : V × W ↦ ‖z.2‖ ^ 2 - ‖z.1‖ ^ 2) '' N) ∨
      range (fun z : V × W ↦ ‖z.2‖ ^ 2 - ‖z.1‖ ^ 2) ⊆ Iic (‖y.2‖ ^ 2 - ‖y.1‖ ^ 2) := by
  set q := fun z : V × W ↦ ‖z.2‖ ^ 2 - ‖z.1‖ ^ 2
  have hq : Continuous q := by fun_prop
  -- If a curve through `y` raises `q` at all small positive times, then by the intermediate value
  -- theorem `q '' N` contains an interval `[q y, b]` with `b > q y`.
  have hcurve {g : ℝ → V × W} (hg : Continuous g) (hg0 : g 0 = y)
      (hlt : ∀ t ∈ Ioc (0 : ℝ) 1, q y < q (g t)) : ∃ b > q y, Icc (q y) b ⊆ q '' N := by
    obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhds_iff.1 (hg.continuousAt.preimage_mem_nhds (hg0 ▸ hN))
    set t₀ := min (δ / 2) 1
    have ht₀ : 0 < t₀ := lt_min (half_pos hδ) one_pos
    refine ⟨q (g t₀), hlt t₀ ⟨ht₀, min_le_right _ _⟩, fun w hw ↦ ?_⟩
    obtain ⟨t, ⟨ht0, htt₀⟩, rfl⟩ := intermediate_value_Icc ht₀.le (hq.comp hg).continuousOn
      (by rwa [comp_apply, hg0])
    refine ⟨g t, hδN ?_, rfl⟩
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht0]
    exact htt₀.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδ))
  by_cases h1 : y.1 = 0
  · by_cases h2 : y.2 ≠ 0 ∨ ∃ w : W, w ≠ 0
    · -- Move `b` away from the origin along `w`: `y.2` itself, or any `w ≠ 0` if `y.2 = 0`.
      obtain ⟨w, hw⟩ : ∃ w : W, ∀ t ∈ Ioc (0 : ℝ) 1, ‖y.2‖ < ‖y.2 + t • w‖ := by
        by_cases hy : y.2 = 0
        · obtain ⟨w, hw⟩ := h2.resolve_left (not_not.2 hy)
          refine ⟨w, fun t ht ↦ ?_⟩
          rw [hy, zero_add, norm_zero, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
          exact mul_pos ht.1 (norm_pos_iff.2 hw)
        · refine ⟨y.2, fun t ht ↦ ?_⟩
          have h1t : y.2 + t • y.2 = (1 + t) • y.2 := by rw [add_smul, one_smul]
          rw [h1t, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [ht.1])]
          nlinarith [ht.1, norm_pos_iff.2 hy]
      refine Or.inl (hcurve (g := fun t ↦ (y.1, y.2 + t • w)) (by fun_prop) (by simp)
        fun t ht ↦ ?_)
      have := hw t ht
      simp only [q]
      nlinarith [norm_nonneg y.2]
    · -- Otherwise `y = 0` and `W = 0`, so `‖b‖² - ‖a‖² = -‖a‖² ≤ 0`.
      push Not at h2
      refine Or.inr ?_
      rintro _ ⟨z, rfl⟩
      simp only [q, mem_Iic, h1, h2.1, h2.2 z.2, norm_zero]
      nlinarith [sq_nonneg ‖z.1‖]
  · -- Shrink `a` towards the origin.
    refine Or.inl (hcurve (g := fun t ↦ ((1 - t) • y.1, y.2)) (by fun_prop) (by simp)
      fun t ht ↦ ?_)
    have ha := norm_pos_iff.2 h1
    simp only [q, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 ht.2), mul_pow]
    have : (1 - t) ^ 2 < 1 := by nlinarith [ht.1, ht.2]
    nlinarith [mul_lt_mul_of_pos_right this (pow_pos ha 2)]

/-- **An indefinite quadratic form is open onto its range.** The function `‖b‖² - ‖a‖²` on `V × W`
maps every neighbourhood of a point `y` onto a neighbourhood of its value at `y` within its range.
-/
theorem image_norm_sq_sub_norm_sq_mem_nhdsWithin (y : V × W) {N : Set (V × W)} (hN : N ∈ 𝓝 y) :
    (fun z : V × W ↦ ‖z.2‖ ^ 2 - ‖z.1‖ ^ 2) '' N ∈
      𝓝[range fun z : V × W ↦ ‖z.2‖ ^ 2 - ‖z.1‖ ^ 2] (‖y.2‖ ^ 2 - ‖y.1‖ ^ 2) := by
  set q := fun z : V × W ↦ ‖z.2‖ ^ 2 - ‖z.1‖ ^ 2 with hq
  have hup := exists_Icc_subset_image_norm_sq_sub_norm_sq_or y hN
  -- Below the value at `y`: exchange the factors, which negates the function.
  have hswap (z : V × W) : ‖z.swap.2‖ ^ 2 - ‖z.swap.1‖ ^ 2 = -q z := by
    simp only [hq, Prod.fst_swap, Prod.snd_swap]
    ring
  have hdown : (∃ b < q y, Icc b (q y) ⊆ q '' N) ∨ range q ⊆ Ici (q y) := by
    rcases exists_Icc_subset_image_norm_sq_sub_norm_sq_or y.swap
        (continuous_swap.continuousAt.preimage_mem_nhds (by rwa [Prod.swap_swap])) with
      ⟨b, hb, hbN⟩ | hle
    · have hy := hswap y
      refine Or.inl ⟨-b, by linarith, fun w hw ↦ ?_⟩
      obtain ⟨z, hzN, hz⟩ := hbN (a := -w) ⟨by linarith [hw.2], by linarith [hw.1]⟩
      refine ⟨z.swap, hzN, ?_⟩
      simp only [hq, Prod.fst_swap, Prod.snd_swap] at hz ⊢
      linarith
    · refine Or.inr ?_
      rintro _ ⟨z, rfl⟩
      have := hle ⟨z.swap, rfl⟩
      simp only [mem_Iic, hswap] at this
      exact neg_le_neg_iff.1 this
  -- Split the range at `q y`; on a side where it stops at `q y`, its trace is at most `{q y}`.
  have hrange : range q = range q ∩ Iic (q y) ∪ range q ∩ Ici (q y) := by
    rw [← inter_union_distrib_left, Iic_union_Ici, inter_univ]
  have hpt {t : Set ℝ} (ht : t ⊆ {q y}) : q '' N ∈ 𝓝[t] (q y) :=
    nhdsWithin_mono _ ht (by
      rw [nhdsWithin_singleton]
      exact mem_pure.2 (mem_image_of_mem _ (mem_of_mem_nhds hN)))
  rw [hrange, nhdsWithin_union]
  refine ⟨?_, ?_⟩
  · rcases hdown with ⟨b, hb, hbN⟩ | hle
    · exact nhdsWithin_mono _ inter_subset_right (mem_of_superset (Icc_mem_nhdsLE hb) hbN)
    · exact hpt fun _ ⟨hz, hzy⟩ ↦ le_antisymm hzy (hle hz)
  · rcases hup with ⟨b, hb, hbN⟩ | hle
    · exact nhdsWithin_mono _ inter_subset_right (mem_of_superset (Icc_mem_nhdsGE hb) hbN)
    · exact hpt fun _ ⟨hz, hzy⟩ ↦ le_antisymm (hle hz) hzy

/-! ### Convexity charts -/

/-- **Convexity charts of an indefinite quadratic form.** If neither `V` nor `W` has dimension one,
then for every preconnected open set `B` of a topological space `P` and all `c` and `r`, the product
of `B` with the ball `‖a‖² + ‖b‖² < r` is a convexity chart of `(x, a, b) ↦ c + ‖b‖² - ‖a‖²`. -/
theorem isConvexChart_prod_setOf_norm_sq_add_norm_sq_lt {P : Type*} [TopologicalSpace P]
    (hV : Module.rank ℝ V ≠ 1) (hW : Module.rank ℝ W ≠ 1) (c r : ℝ) {B : Set P} (hBo : IsOpen B)
    (hB : IsPreconnected B) :
    IsConvexChart (fun z : P × (V × W) ↦ c + (‖z.2.2‖ ^ 2 - ‖z.2.1‖ ^ 2))
      (B ×ˢ {y : V × W | ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 < r}) := by
  set R := {y : V × W | ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 < r}
  have hf : Continuous fun z : P × (V × W) ↦ c + (‖z.2.2‖ ^ 2 - ‖z.2.1‖ ^ 2) := by fun_prop
  -- The ball is closed under scaling by `t ∈ [0, 1]`.
  have hR : IsPreconnected R := isPreconnected_of_forall_smul_mem fun y hy t ht ↦ by
    simp only [R, mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, norm_smul, Real.norm_of_nonneg ht.1,
      mul_pow] at hy ⊢
    have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.1 ht.2
    linarith [mul_le_of_le_one_left (sq_nonneg ‖y.1‖) ht2,
      mul_le_of_le_one_left (sq_nonneg ‖y.2‖) ht2]
  refine ⟨hBo.prod (isOpen_lt (by fun_prop) continuous_const), ?_, fun U _ hUo z hz ↦ ?_,
    fun v ↦ ?_⟩
  · -- The image of the preconnected chart is an interval.
    exact (isPreconnected_iff_ordConnected.1 ((hB.prod hR).image _ hf.continuousOn)).convex
  · -- Through `z`, the slice of `U` over `z.1` is a neighbourhood of `z.2` mapped into `f '' U`.
    have hN : (fun y ↦ (z.1, y)) ⁻¹' U ∈ 𝓝 z.2 :=
      (Continuous.prodMk_right z.1).continuousAt.preimage_mem_nhds (hUo.mem_nhds hz)
    have h := image_mem_map (m := Homeomorph.addLeft c)
      (image_norm_sq_sub_norm_sq_mem_nhdsWithin z.2 hN)
    rw [(Homeomorph.addLeft c).isEmbedding.map_nhdsWithin_eq] at h
    refine mem_of_superset (nhdsWithin_mono _ ?_ h) ?_
    · rintro _ ⟨w, -, rfl⟩
      exact ⟨_, ⟨w.2, rfl⟩, rfl⟩
    · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨(z.1, y), hy, rfl⟩
  · -- The fibre of `v` is the product of `B` with the fibre of `v - c` in the ball.
    convert hB.prod (isPreconnected_setOf_norm_sq_sub_norm_sq_eq hV hW r (v - c)) using 1
    ext ⟨x, y⟩
    simp only [R, mem_inter_iff, mem_prod, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hx, hy⟩, hv⟩
      exact ⟨hx, hy, by linarith⟩
    · rintro ⟨hx, hy, hv⟩
      exact ⟨⟨hx, hy⟩, by linarith⟩

/-- **Convexity charts of a map reading as an indefinite quadratic form.** If neither `V` nor `W`
has dimension one, and in a chart `e : X → P × (V × W)` a real function `f` reads
`(x, a, b) ↦ c + ‖b‖² - ‖a‖²`, then every point of the source of `e` sent to the zero section
`P × {0}` lies in a convexity chart of `f`. -/
theorem exists_isConvexChart_of_eqOn_norm_sq_sub_norm_sq {X P : Type*} [TopologicalSpace X]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (hV : Module.rank ℝ V ≠ 1)
    (hW : Module.rank ℝ W ≠ 1) {f : X → ℝ} {c : ℝ} {e : OpenPartialHomeomorph X (P × (V × W))}
    (hf : EqOn f ((fun z ↦ c + (‖z.2.2‖ ^ 2 - ‖z.2.1‖ ^ 2)) ∘ e) e.source) {x : X}
    (hx : x ∈ e.source) (hx0 : (e x).2 = 0) : ∃ U, x ∈ U ∧ IsConvexChart f U := by
  -- A product of a ball in `P` and a ball `‖a‖² + ‖b‖² < ε²` inside the target of `e`.
  have hex : e x = ((e x).1, 0) := Prod.ext rfl hx0
  obtain ⟨u, hu, w, hw, huw⟩ := mem_nhds_prod_iff.1
    (hex ▸ e.open_target.mem_nhds (e.map_source hx))
  obtain ⟨δ, hδ, hδu⟩ := Metric.mem_nhds_iff.1 hu
  obtain ⟨ε, hε, hεw⟩ := Metric.mem_nhds_iff.1 hw
  have hRw : {y : V × W | ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 < ε ^ 2} ⊆ w := fun y hy ↦ by
    refine hεw ?_
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
    constructor <;> refine lt_of_pow_lt_pow_left₀ 2 hε.le ?_ <;>
      nlinarith [hy.out, sq_nonneg ‖y.1‖, sq_nonneg ‖y.2‖]
  refine ⟨e.source ∩ e ⁻¹' (ball (e x).1 δ ×ˢ {y : V × W | ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 < ε ^ 2}),
    ⟨hx, ?_⟩, (isConvexChart_prod_setOf_norm_sq_add_norm_sq_lt hV hW c (ε ^ 2)
    isOpen_ball (convex_ball (e x).1 δ).isPreconnected).source_inter_preimage
      ((prod_mono hδu hRw).trans huw) hf⟩
  rw [mem_preimage, hex]
  exact ⟨mem_ball_self hδ, by simpa using pow_pos hε 2⟩

end TauCeti
