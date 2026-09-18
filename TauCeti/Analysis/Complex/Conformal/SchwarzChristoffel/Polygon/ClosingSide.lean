/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.GlobalTurning
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.ShortTurn
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.UnboundedEdge
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Separation of Schwarz--Christoffel sides from the closing side

With the total exponent `-2`, the two unbounded pieces of the Schwarz--Christoffel boundary both
run in the positive real direction (`schwarzChristoffelBoundary_lt_vertexAtInfinity` and
`schwarzChristoffelVertexAtInfinity_lt_boundary`): the last finite vertex, the vertex at infinity
and the first finite vertex lie on one horizontal line in this order.

Under the classical convex-polygon hypotheses (strictly ordered prevertices and exponents in
`(-1, 0)`), every other finite vertex lies strictly above that line.  The bounded side vectors have
arguments strictly increasing in `(-2π, 0)`, so the heights of the vertices first increase and then
decrease; since the first and last vertices have equal heights, all intermediate heights are
larger.

Consequently a bounded side meets the closing line at most in an endpoint shared with the closing
side, and nonadjacent bounded and closing polygon sides are disjoint.  Together with the separation
of nonadjacent bounded sides, this is the input for global simplicity of the Schwarz--Christoffel
polygon.

## Main results

* `TauCeti.im_schwarzChristoffelVertex_zero_lt` -- every finite vertex other than the first and
  the last lies strictly above the closing line.
* `TauCeti.disjoint_schwarzChristoffelPolygon_edgeSet_last_prevertex` and
  `TauCeti.disjoint_schwarzChristoffelPolygon_edgeSet_last` -- bounded sides are disjoint from the
  nonadjacent closing sides.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane
open scoped ComplexOrder

namespace TauCeti

variable {n : ℕ}

/-- The closing side runs from the last finite vertex through the vertex at infinity to the first
finite vertex, horizontally and in the positive real direction. -/
theorem schwarzChristoffelVertex_last_lt_vertexAtInfinity_lt_vertex_zero
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a) (he : ∀ k, -1 < e k)
    (hsum : ∑ k, e k = -2) :
    schwarzChristoffelVertex a e z₀ (Fin.last n) < schwarzChristoffelVertexAtInfinity a e z₀ ∧
      schwarzChristoffelVertexAtInfinity a e z₀ < schwarzChristoffelVertex a e z₀ 0 := by
  have hfinite (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using he k
  have hr := schwarzChristoffelBoundary_lt_vertexAtInfinity a e z₀ (hfinite (Fin.last n))
    (fun l _ ↦ ha.monotone l.le_last) (by rw [hsum]; norm_num)
  have hl := schwarzChristoffelVertexAtInfinity_lt_boundary a e z₀
    (hfinite 0) (fun l _ ↦ ha.monotone l.zero_le) hsum
  rw [schwarzChristoffelBoundary_apply_prevertex a e z₀ _ (hfinite _)] at hr hl
  exact ⟨hr, hl⟩

/-- **The vertex at infinity lies on the closing line.** Its imaginary part equals that of the
first finite vertex. -/
@[simp]
theorem im_schwarzChristoffelVertexAtInfinity_eq_im_zero
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) :
    (schwarzChristoffelVertexAtInfinity a e z₀).im =
      (schwarzChristoffelVertex a e z₀ 0).im := by
  exact (Complex.lt_def.mp
    (schwarzChristoffelVertex_last_lt_vertexAtInfinity_lt_vertex_zero a e z₀ ha
      (fun k ↦ (he k).1) hsum).2).2

/-- **The first and last finite vertices lie on the same closing line.** Their imaginary parts
agree. -/
@[simp]
theorem im_schwarzChristoffelVertex_last_eq_im_zero
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) :
    (schwarzChristoffelVertex a e z₀ (Fin.last n)).im =
      (schwarzChristoffelVertex a e z₀ 0).im := by
  obtain ⟨hr, hl⟩ :=
    schwarzChristoffelVertex_last_lt_vertexAtInfinity_lt_vertex_zero a e z₀ ha
      (fun k ↦ (he k).1) hsum
  exact (Complex.lt_def.mp hr).2.trans (Complex.lt_def.mp hl).2

/-- The height increment along a bounded side is its positive length times the sine of its edge
angle. -/
private lemma exists_im_schwarzChristoffelVertex_succ_sub (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : StrictMono a) (hfinite : ∀ k, -1 < ∑ l with a l = a k, e l)
    (i : Fin n) :
    ∃ d : ℝ, 0 < d ∧ (schwarzChristoffelVertex a e z₀ i.succ).im -
        (schwarzChristoffelVertex a e z₀ i.castSucc).im =
      d * Real.sin (schwarzChristoffelEdgeAngle a e (a i.castSucc)) := by
  refine ⟨‖schwarzChristoffelVertex a e z₀ i.succ - schwarzChristoffelVertex a e z₀ i.castSucc‖,
    norm_pos_iff.mpr (sub_ne_zero.mpr ?_), ?_⟩
  · refine (schwarzChristoffelVertex_ne a e z₀ (ha i.castSucc_lt_succ) ?_ (hfinite _)
      (hfinite _)).symm
    intro k _ hk
    have hik := Fin.lt_def.mp ((ha.lt_iff_lt).mp hk.1)
    have hki := Fin.lt_def.mp ((ha.lt_iff_lt).mp hk.2)
    simp only [Fin.val_castSucc, Fin.val_succ] at hik hki
    omega
  · rw [← Complex.sub_im]
    conv_lhs => rw [schwarzChristoffelVertex_succ_sub_eq_norm_mul a e z₀ ha i
      (hfinite _) (hfinite _)]
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Complex.exp_ofReal_mul_I_im]

/-- **The finite vertices lie above the closing line.**  For strictly ordered prevertices with
exponents in `(-1, 0)` summing to `-2`, every finite Schwarz--Christoffel vertex other than the
first and the last lies strictly above the horizontal line through the first vertex, which also
contains the last vertex and the vertex at infinity. -/
theorem im_schwarzChristoffelVertex_zero_lt (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane)
    (ha : StrictMono a) (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2)
    {k : Fin (n + 1)} (hk₀ : k ≠ 0) (hkn : k ≠ Fin.last n) :
    (schwarzChristoffelVertex a e z₀ 0).im < (schwarzChristoffelVertex a e z₀ k).im := by
  have hfinite (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using (he k).1
  set θ : Fin (n + 1) → ℝ := fun l ↦ schwarzChristoffelEdgeAngle a e (a l)
  have hθmono : StrictMono θ :=
    schwarzChristoffelEdgeAngle_comp_strictMono a e ha fun l ↦ (he l).2
  have hθlow (l : Fin (n + 1)) : -2 * Real.pi < θ l :=
    (schwarzChristoffelEdgeAngle_mem_Ioc a e (fun l ↦ (he l).2) hsum l).1
  have hθlast : θ (Fin.last n) = 0 :=
    schwarzChristoffelEdgeAngle_eq_zero_of_last_le a e ha.monotone le_rfl
  -- The first and last vertices have equal heights.
  have hends : (schwarzChristoffelVertex a e z₀ (Fin.last n)).im =
      (schwarzChristoffelVertex a e z₀ 0).im :=
    im_schwarzChristoffelVertex_last_eq_im_zero a e z₀ ha he hsum
  -- Telescope the heights along the natural-number indices.
  let W : ℕ → ℝ := fun m ↦ if hm : m < n + 1 then (schwarzChristoffelVertex a e z₀ ⟨m, hm⟩).im
    else 0
  have hW (l : Fin (n + 1)) : W l = (schwarzChristoffelVertex a e z₀ l).im := by
    simp only [W, l.isLt, ↓reduceDIte, Fin.eta]
  have hstep (l : ℕ) (hl : l < n) : ∃ d : ℝ, 0 < d ∧
      W (l + 1) - W l = d * Real.sin (θ ⟨l, by omega⟩) := by
    obtain ⟨d, hd, h⟩ := exists_im_schwarzChristoffelVertex_succ_sub a e z₀ ha hfinite ⟨l, hl⟩
    refine ⟨d, hd, ?_⟩
    have h1 := hW ⟨l + 1, by omega⟩
    have h0 := hW ⟨l, by omega⟩
    rw [Fin.val_mk] at h1 h0
    rw [h1, h0]
    simpa only [Fin.succ_mk, Fin.castSucc_mk] using h
  have hkval : 0 < k.val := Fin.pos_iff_ne_zero.mpr hk₀
  have hkn' : k.val < n := by
    simpa only [Fin.lt_def, Fin.val_last] using Fin.lt_last_iff_ne_last.mpr hkn
  rw [← hW, ← hW]
  simp only [Fin.val_zero]
  by_cases hθk : θ k ≤ -Real.pi
  · -- Every earlier side points upward.
    have htel := Finset.sum_Ico_sub W (Nat.zero_le k.val)
    rw [← sub_pos, ← htel]
    refine Finset.sum_pos (fun l hl ↦ ?_) (Finset.nonempty_Ico.mpr hkval)
    rw [Finset.mem_Ico] at hl
    obtain ⟨d, hd, h⟩ := hstep l (hl.2.trans hkn')
    rw [h]
    have hlt : θ ⟨l, by omega⟩ < θ k := hθmono (Fin.mk_lt_mk.mpr hl.2)
    refine mul_pos hd ?_
    rw [← Real.sin_add_two_pi]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθlow ⟨l, by omega⟩]) (by linarith)
  · -- Every later side points downward, and the total height change is zero.
    have htel := Finset.sum_Ico_sub W hkn'.le
    have hWn : W n = W 0 := by
      have h1 := hW (Fin.last n)
      have h0 := hW 0
      rw [Fin.val_last] at h1
      rw [Fin.val_zero] at h0
      rw [h1, h0, hends]
    have hneg : ∑ l ∈ Finset.Ico k.val n, (W (l + 1) - W l) < 0 := by
      refine Finset.sum_neg (fun l hl ↦ ?_) (Finset.nonempty_Ico.mpr hkn')
      rw [Finset.mem_Ico] at hl
      obtain ⟨d, hd, h⟩ := hstep l hl.2
      rw [h]
      have hle : θ k ≤ θ ⟨l, by omega⟩ := hθmono.monotone (Fin.mk_le_mk.mpr hl.1)
      have hlt : θ ⟨l, by omega⟩ < θ (Fin.last n) :=
        hθmono (Fin.mk_lt_mk.mpr (by simpa using hl.2))
      rw [hθlast] at hlt
      exact mul_neg_of_pos_of_neg hd
        (Real.sin_neg_of_neg_of_neg_pi_lt hlt (by linarith))
    rw [htel, hWn] at hneg
    linarith

/-- **Every finite Schwarz--Christoffel vertex lies on or above the closing line.** The line is
identified by the imaginary part of the first finite vertex. -/
@[grind .]
theorem im_schwarzChristoffelVertex_zero_le (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane)
    (ha : StrictMono a) (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2)
    (k : Fin (n + 1)) :
    (schwarzChristoffelVertex a e z₀ 0).im ≤ (schwarzChristoffelVertex a e z₀ k).im := by
  rcases eq_or_ne k 0 with rfl | hk₀
  · exact le_rfl
  rcases eq_or_ne k (Fin.last n) with rfl | hkn
  · exact (im_schwarzChristoffelVertex_last_eq_im_zero a e z₀ ha he hsum).ge
  · exact (im_schwarzChristoffelVertex_zero_lt a e z₀ ha he hsum hk₀ hkn).le

/-- A point of a bounded side lying no higher than the closing line is the endpoint `V k` of that
side, provided the other endpoint `V k'` is neither the first nor the last vertex. -/
private lemma eq_of_mem_segment_schwarzChristoffelVertex_of_im_le (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : StrictMono a) (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0)
    (hsum : ∑ k, e k = -2) (k : Fin (n + 1)) {k' : Fin (n + 1)} (hk₀ : k' ≠ 0)
    (hkn : k' ≠ Fin.last n) {z : ℂ}
    (hz : z ∈ segment ℝ (schwarzChristoffelVertex a e z₀ k) (schwarzChristoffelVertex a e z₀ k'))
    (hzh : z.im ≤ (schwarzChristoffelVertex a e z₀ 0).im) :
    z = schwarzChristoffelVertex a e z₀ k := by
  have hk := im_schwarzChristoffelVertex_zero_le a e z₀ ha he hsum k
  have hk' := im_schwarzChristoffelVertex_zero_lt a e z₀ ha he hsum hk₀ hkn
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at hzh
  -- Both endpoints are at least as high as the line and the second is strictly higher, so a
  -- convex combination reaching the line puts no weight on the second endpoint.
  have hsh : s * (schwarzChristoffelVertex a e z₀ 0).im +
      t * (schwarzChristoffelVertex a e z₀ 0).im = (schwarzChristoffelVertex a e z₀ 0).im := by
    rw [← add_mul, hst, one_mul]
  have ht0 : t = 0 := le_antisymm (not_lt.mp fun htpos ↦ by
    linarith [mul_le_mul_of_nonneg_left hk hs, mul_lt_mul_of_pos_left hk' htpos]) ht
  obtain rfl : s = 1 := by linarith
  simp [ht0]

/-- **A bounded side misses the nonadjacent right-hand closing side.**  Under the classical
convex-polygon hypotheses, the bounded side from vertex `i` to vertex `i + 1`, where `i + 1` is not
the last finite vertex, is disjoint from the polygon side joining the last finite vertex to the
vertex at infinity. -/
theorem disjoint_schwarzChristoffelPolygon_edgeSet_last_prevertex (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : StrictMono a) (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0)
    (hsum : ∑ k, e k = -2) (i : Fin n) (hi : i.val + 1 < n) :
    Disjoint ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc)
      ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last n).castSucc) := by
  obtain ⟨hr, hl⟩ := schwarzChristoffelVertex_last_lt_vertexAtInfinity_lt_vertex_zero a e z₀ ha
      (fun k ↦ (he k).1) hsum
  rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc,
    schwarzChristoffelPolygon_edgeSet_last_prevertex, Set.disjoint_left]
  intro z hzi hzc
  -- The closing side is horizontal at the height of the first vertex and ends left of it.
  obtain ⟨hz₁, hz₂⟩ := segment_subset_Icc hr.le hzc
  have hzim : z.im = (schwarzChristoffelVertex a e z₀ 0).im :=
    ((Complex.le_def.mp hz₁).2.symm.trans (Complex.lt_def.mp hr).2).trans
      (Complex.lt_def.mp hl).2
  have hsucc : i.succ ≠ Fin.last n := by
    rw [Ne, Fin.ext_iff, Fin.val_succ, Fin.val_last]
    omega
  have hzeq := eq_of_mem_segment_schwarzChristoffelVertex_of_im_le a e z₀ ha he hsum _
    (Fin.succ_ne_zero i) hsucc hzi hzim.le
  rcases eq_or_ne i.castSucc 0 with h0 | h0
  · rw [hzeq, h0] at hz₂
    exact (Complex.le_def.mp hz₂).1.not_gt (Complex.lt_def.mp hl).1
  · have hlt := im_schwarzChristoffelVertex_zero_lt a e z₀ ha he hsum h0
      (Fin.castSucc_lt_last i).ne
    rw [← hzeq, hzim] at hlt
    exact hlt.false

/-- **A bounded side misses the nonadjacent left-hand closing side.**  Under the classical
convex-polygon hypotheses, the bounded side from vertex `i` to vertex `i + 1`, where `i` is not the
first finite vertex, is disjoint from the polygon side joining the vertex at infinity to the first
finite vertex. -/
theorem disjoint_schwarzChristoffelPolygon_edgeSet_last (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : StrictMono a) (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0)
    (hsum : ∑ k, e k = -2) (i : Fin n) (hi : 0 < i.val) :
    Disjoint ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc)
      ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 1))) := by
  obtain ⟨hr, hl⟩ := schwarzChristoffelVertex_last_lt_vertexAtInfinity_lt_vertex_zero a e z₀ ha
      (fun k ↦ (he k).1) hsum
  rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc,
    schwarzChristoffelPolygon_edgeSet_last, Set.disjoint_left]
  intro z hzi hzc
  -- The closing side is horizontal at the height of the first vertex and starts right of the
  -- last vertex.
  obtain ⟨hz₁, -⟩ := segment_subset_Icc hl.le hzc
  have hzim : z.im = (schwarzChristoffelVertex a e z₀ 0).im :=
    (Complex.le_def.mp hz₁).2.symm.trans (Complex.lt_def.mp hl).2
  have hcast : i.castSucc ≠ 0 := by
    rw [Ne, Fin.ext_iff, Fin.val_castSucc, Fin.val_zero]
    omega
  have hzeq := eq_of_mem_segment_schwarzChristoffelVertex_of_im_le a e z₀ ha he hsum _
    hcast (Fin.castSucc_lt_last i).ne (by rwa [segment_symm] at hzi) hzim.le
  rcases eq_or_ne i.succ (Fin.last n) with hn | hn
  · rw [hzeq, hn] at hz₁
    exact (Complex.le_def.mp hz₁).1.not_gt (Complex.lt_def.mp hr).1
  · have hlt := im_schwarzChristoffelVertex_zero_lt a e z₀ ha he hsum (Fin.succ_ne_zero i) hn
    rw [← hzeq, hzim] at hlt
    exact hlt.false

/-- The bounded Schwarz--Christoffel boundary arc lies strictly above the closing line,
except at its first and last prevertices. -/
theorem im_schwarzChristoffelBoundary_first_lt (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : StrictMono a) (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0)
    (hsum : ∑ k, e k = -2) {x : ℝ} (hx : x ∈ Ioo (a 0) (a (Fin.last n))) :
    (schwarzChristoffelBoundary a e z₀ (a 0)).im <
      (schwarzChristoffelBoundary a e z₀ x).im := by
  have hfinite (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using (he k).1
  have hn : 2 ≤ n := by
    by_contra! hn
    interval_cases n
    · have hsum' : e 0 = -2 := by simpa using hsum
      linarith [(he 0).1]
    · have hsum' : e 0 + e 1 = -2 := by simpa [Fin.sum_univ_succ] using hsum
      linarith [(he 0).1, (he 1).1]
  have hx' : x ∈ ⋃ j ∈ Ico 0 (Fin.last n), Ioc (a j) (a (Order.succ j)) := by
    rw [ha.monotone.biUnion_Ico_Ioc_map_succ]
    exact ⟨hx.1, hx.2.le⟩
  simp only [mem_iUnion, mem_Ico] at hx'
  obtain ⟨j, ⟨-, hj⟩, hxj⟩ := hx'
  obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj.ne
  have hxi : x ∈ Icc (a i.castSucc) (a i.succ) :=
    Ioc_subset_Icc_self (by simpa only [Fin.orderSucc_castSucc] using hxj)
  have hfree : ∀ k, e k ≠ 0 → a k ∉ Ioo (a i.castSucc) (a i.succ) := by
    intro k _ hk
    have h₁ := ha.lt_iff_lt.mp hk.1
    have h₂ := ha.lt_iff_lt.mp hk.2
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h₁ h₂
    omega
  have hmem : schwarzChristoffelBoundary a e z₀ x ∈
      segment ℝ (schwarzChristoffelVertex a e z₀ i.castSucc)
        (schwarzChristoffelVertex a e z₀ i.succ) := by
    rw [← schwarzChristoffelBoundary_image_Icc_prevertex a e z₀
      (ha.monotone i.castSucc_le_succ) hfree (hfinite _) (hfinite _)]
    exact ⟨x, hxi, rfl⟩
  rw [schwarzChristoffelBoundary_apply_prevertex a e z₀ 0 (hfinite 0)]
  by_contra! hle
  have hinj := schwarzChristoffelBoundary_injOn_Icc a e z₀ hfree (hfinite _) (hfinite _)
  by_cases hi : i.castSucc = 0
  · have hisucc : i.succ ≠ Fin.last n := by
      simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_zero] at hi
      rw [Ne, Fin.ext_iff, Fin.val_succ, Fin.val_last]
      omega
    have heq := eq_of_mem_segment_schwarzChristoffelVertex_of_im_le a e z₀ ha he hsum _
      (Fin.succ_ne_zero i) hisucc hmem hle
    rw [← schwarzChristoffelBoundary_apply_prevertex a e z₀ _ (hfinite _)] at heq
    have hxeq := hinj hxi ⟨le_rfl, (ha i.castSucc_lt_succ).le⟩ heq
    rw [hi] at hxeq
    exact hx.1.ne' hxeq
  · have heq := eq_of_mem_segment_schwarzChristoffelVertex_of_im_le a e z₀ ha he hsum _
      hi (Fin.castSucc_lt_last i).ne (by rwa [segment_symm] at hmem) hle
    by_cases hiend : i.succ = Fin.last n
    · rw [← schwarzChristoffelBoundary_apply_prevertex a e z₀ _ (hfinite _)] at heq
      have hxeq := hinj hxi ⟨(ha i.castSucc_lt_succ).le, le_rfl⟩ heq
      rw [hiend] at hxeq
      exact hx.2.ne hxeq
    · have hlt := im_schwarzChristoffelVertex_zero_lt a e z₀ ha he hsum
        (Fin.succ_ne_zero i) hiend
      rw [← heq] at hlt
      exact hle.not_gt hlt

end TauCeti
