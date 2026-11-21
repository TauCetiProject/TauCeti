/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Elliptic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Open-interval parametrization of polygon edges and half-edges

Let `σ` pair the sides of a convex hyperbolic `n`-gon `P`, whose vertices may lie either in `ℍ` or
on `∂ℍ = OnePoint ℝ`. Mapping the geodesic parameter through `Real.arctan` yields a bounded angle
interval `(α, β) ⊆ (-(π / 2), π / 2)` for bounded segments, rays, and bi-infinite geodesics alike.
Composing the affine map `(-1, 1) → (α, β)` with `Real.tan` and `geodesicLine (P.sideGeodesic i)`
produces `σ.edgeArc i : ℝ → ℍ`, carrying the open side when `σ.pair i ≠ i` and the open half-side
up to `σ.selfPairedSideFixedPoint` when `σ.pair i = i`.

## Main definitions and results

* `ConvexPolygon.SidePairing.edgeArc`: the open `1`-cell arc `ℝ → ℍ` on `Ioo (-1 : ℝ) 1`.
* `ConvexPolygon.SidePairing.continuousOn_edgeArc`, `ConvexPolygon.SidePairing.injOn_edgeArc`:
  continuity and injectivity on `Ioo (-1) 1`.
* `ConvexPolygon.SidePairing.mem_image_edgeArc_or_selfPaired_of_mem_side`: coverage of `P.side j`
  away from finite vertices.
* `ConvexPolygon.SidePairing.tendsto_edgeArc_neg_one_of_eq_inl`,
  `ConvexPolygon.SidePairing.tendsto_edgeArc_neg_one_atImInfty_of_eq_inr`,
  `ConvexPolygon.SidePairing.tendsto_edgeArc_one_of_pair_eq`,
  `ConvexPolygon.SidePairing.tendsto_edgeArc_one_of_eq_inl`, and
  `ConvexPolygon.SidePairing.tendsto_edgeArc_one_atImInfty_of_eq_inr`: endpoint limits at `±1`.
-/

public section

noncomputable section

open Metric MulAction Set Topology UpperHalfPlane
open scoped MatrixGroups OnePoint Real

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

/-! ### Geodesic parameters of endpoints and self-paired midpoints -/

open scoped Classical in
private def startParam (P : ConvexPolygon n) (i : Fin n) : ℝ :=
  if h : ∃ v, P.vertex i = .inl v then
    Classical.choose ((h.choose_spec ▸ P.isGeodesicFromTo_sideGeodesic i).left_mem_range)
  else 0

private theorem geodesicLine_startParam {i : Fin n} {v : ℍ} (hv : P.vertex i = .inl v) :
    geodesicLine (P.sideGeodesic i) (startParam P i) = v := by
  have hex : ∃ v', P.vertex i = .inl v' := ⟨v, hv⟩
  rw [startParam, dite_eq_left hex]
  exact (Classical.choose_spec
    ((hex.choose_spec ▸ P.isGeodesicFromTo_sideGeodesic i).left_mem_range)).trans
    (Sum.inl.inj (hex.choose_spec.symm.trans hv))

open scoped Classical in
private def endParam (P : ConvexPolygon n) (i : Fin n) : ℝ :=
  if h : ∃ w, P.vertex (i + 1) = .inl w then
    Classical.choose ((h.choose_spec ▸ P.isGeodesicFromTo_sideGeodesic i).right_mem_range)
  else 0

private theorem geodesicLine_endParam {i : Fin n} {w : ℍ} (hw : P.vertex (i + 1) = .inl w) :
    geodesicLine (P.sideGeodesic i) (endParam P i) = w := by
  have hex : ∃ w', P.vertex (i + 1) = .inl w' := ⟨w, hw⟩
  rw [endParam, dite_eq_left hex]
  exact (Classical.choose_spec
    ((hex.choose_spec ▸ P.isGeodesicFromTo_sideGeodesic i).right_mem_range)).trans
    (Sum.inl.inj (hex.choose_spec.symm.trans hw))

private theorem startParam_lt_endParam {i : Fin n} {v w : ℍ}
    (hv : P.vertex i = .inl v) (hw : P.vertex (i + 1) = .inl w) :
    startParam P i < endParam P i := by
  have hg := P.isGeodesicFromTo_sideGeodesic i; rw [hv, hw] at hg
  obtain ⟨s, t, hst, hs, ht⟩ := isGeodesicFromTo_inl_inl.1 hg
  rwa [geodesicLine_injective _ ((geodesicLine_startParam hv).trans hs.symm),
    geodesicLine_injective _ ((geodesicLine_endParam hw).trans ht.symm)]

private def midParam {i : Fin n} (hi : σ.pair i = i) : ℝ :=
  Classical.choose (P.side_subset_range_sideGeodesic i (σ.selfPairedSideFixedPoint_spec ⟨i, hi⟩).1)

private theorem geodesicLine_midParam {i : Fin n} (hi : σ.pair i = i) :
    geodesicLine (P.sideGeodesic i) (σ.midParam hi) = σ.selfPairedSideFixedPoint ⟨i, hi⟩ :=
  Classical.choose_spec
    (P.side_subset_range_sideGeodesic i (σ.selfPairedSideFixedPoint_spec ⟨i, hi⟩).1)

private theorem map_smul_geodesicLine_of_pair_eq {i : Fin n} (hi : σ.pair i = i) (t : ℝ) :
    σ.map i • geodesicLine (P.sideGeodesic i) t =
      geodesicLine (P.sideGeodesic i) (2 * σ.midParam hi - t) := by
  have hg := (P.isGeodesicFromTo_sideGeodesic i).smul (σ.map i)
  rw [σ.map_smul_vertex, σ.map_smul_vertex_add_one, hi] at hg
  obtain ⟨r, hr⟩ := (isGeodesicFromTo_mul_pslS_iff.mpr
    (P.isGeodesicFromTo_sideGeodesic i)).exists_eq_mul_dilation hg
  have hact (u : ℝ) : σ.map i • geodesicLine (P.sideGeodesic i) u =
      geodesicLine (P.sideGeodesic i) (-(r + u)) := by
    rw [smul_geodesicLine, hr, geodesicLine_mul_dilation, geodesicLine_mul_pslS]
  have hfix : σ.map i • geodesicLine (P.sideGeodesic i) (-r / 2) =
      geodesicLine (P.sideGeodesic i) (-r / 2) := by rw [hact]; congr 1; ring
  have hm : σ.midParam hi = -r / 2 := geodesicLine_injective _
    ((σ.geodesicLine_midParam hi).trans (σ.selfPairedSideFixedPoint_eq ⟨i, hi⟩ hfix))
  rw [hact, hm]; congr 1; ring

private theorem midParam_eq_avg {i : Fin n} (hi : σ.pair i = i) {v : ℍ}
    (hv : P.vertex i = .inl v) :
    ∃ w : ℍ, P.vertex (i + 1) = .inl w ∧ σ.midParam hi = (startParam P i + endParam P i) / 2 := by
  have hw : P.vertex (i + 1) = .inl (σ.map i • v) := by
    simpa [hi, hv] using (σ.map_smul_vertex i).symm
  refine ⟨σ.map i • v, hw, ?_⟩
  have h1 : geodesicLine (P.sideGeodesic i) (2 * σ.midParam hi - startParam P i) =
      geodesicLine (P.sideGeodesic i) (endParam P i) := by
    rw [← σ.map_smul_geodesicLine_of_pair_eq hi, geodesicLine_startParam hv,
      geodesicLine_endParam hw]
  linarith [geodesicLine_injective _ h1]

/-! ### Uniform angle intervals via `Real.arctan` -/

private def startAngle (P : ConvexPolygon n) (i : Fin n) : ℝ :=
  if (P.vertex i).isLeft then Real.arctan (startParam P i) else -(π / 2)

private def sideEndAngle (P : ConvexPolygon n) (i : Fin n) : ℝ :=
  if (P.vertex (i + 1)).isLeft then Real.arctan (endParam P i) else π / 2

private def edgeEndAngle (i : Fin n) : ℝ :=
  if hi : σ.pair i = i then Real.arctan (σ.midParam hi) else sideEndAngle P i

private theorem startAngle_of_eq_inl {i : Fin n} {v : ℍ} (hv : P.vertex i = .inl v) :
    startAngle P i = Real.arctan (startParam P i) := by
  simp [startAngle, hv]

private theorem startAngle_of_eq_inr {i : Fin n} {ξ : OnePoint ℝ} (hξ : P.vertex i = .inr ξ) :
    startAngle P i = -(π / 2) := by
  simp [startAngle, hξ]

private theorem edgeEndAngle_of_pair_eq {i : Fin n} (hi : σ.pair i = i) :
    σ.edgeEndAngle i = Real.arctan (σ.midParam hi) := by
  simp [edgeEndAngle, hi]

private theorem edgeEndAngle_of_eq_inl {i : Fin n} {w : ℍ} (hi : σ.pair i ≠ i)
    (hw : P.vertex (i + 1) = .inl w) :
    σ.edgeEndAngle i = Real.arctan (endParam P i) := by
  simp [edgeEndAngle, sideEndAngle, hi, hw]

private theorem edgeEndAngle_of_eq_inr {i : Fin n} {η : OnePoint ℝ} (hi : σ.pair i ≠ i)
    (hη : P.vertex (i + 1) = .inr η) :
    σ.edgeEndAngle i = π / 2 := by
  simp [edgeEndAngle, sideEndAngle, hi, hη]

private theorem neg_pi_div_two_le_startAngle (i : Fin n) : -(π / 2) ≤ startAngle P i := by
  unfold startAngle; split_ifs; exacts [(Real.neg_pi_div_two_lt_arctan _).le, le_rfl]

private theorem edgeEndAngle_le_pi_div_two (i : Fin n) : σ.edgeEndAngle i ≤ π / 2 := by
  unfold edgeEndAngle sideEndAngle; split_ifs
  exacts [(Real.arctan_lt_pi_div_two _).le, (Real.arctan_lt_pi_div_two _).le, le_rfl]

private theorem startAngle_lt_edgeEndAngle (i : Fin n) :
    startAngle P i < σ.edgeEndAngle i := by
  unfold startAngle edgeEndAngle sideEndAngle
  split_ifs with hp hi hq
  · obtain ⟨v, hv⟩ := Sum.isLeft_iff.1 hp; obtain ⟨w, hw, hm⟩ := σ.midParam_eq_avg hi hv
    exact Real.arctan_strictMono (by linarith [startParam_lt_endParam hv hw])
  · obtain ⟨v, hv⟩ := Sum.isLeft_iff.1 hp; obtain ⟨w, hw⟩ := Sum.isLeft_iff.1 hq
    exact Real.arctan_strictMono (startParam_lt_endParam hv hw)
  · exact Real.arctan_lt_pi_div_two _
  · exact Real.neg_pi_div_two_lt_arctan _
  · exact Real.neg_pi_div_two_lt_arctan _
  · linarith [Real.pi_pos]

private theorem edgeEndAngle_le_sideEndAngle (i : Fin n) :
    σ.edgeEndAngle i ≤ sideEndAngle P i := by
  unfold edgeEndAngle sideEndAngle
  split_ifs with hi hq
  · obtain ⟨w, hw⟩ := Sum.isLeft_iff.1 hq
    have hv : P.vertex i = .inl (σ.map i • w) := by
      simpa [hi, hw] using (σ.map_smul_vertex_add_one i).symm
    obtain ⟨w', hw', hm⟩ := σ.midParam_eq_avg hi hv
    exact Real.arctan_mono (by linarith [startParam_lt_endParam hv hw'])
  · exact (Real.arctan_lt_pi_div_two _).le
  · exact le_rfl
  · exact le_rfl

private theorem mem_side_and_ne_endpoints_iff {i : Fin n} {z : ℍ} :
    (z ∈ P.side i ∧ P.vertex i ≠ .inl z ∧ P.vertex (i + 1) ≠ .inl z) ↔
      ∃ t : ℝ, Real.arctan t ∈ Ioo (startAngle P i) (sideEndAngle P i) ∧
        geodesicLine (P.sideGeodesic i) t = z := by
  have hg := P.isGeodesicFromTo_sideGeodesic i
  unfold startAngle sideEndAngle
  rcases hp : P.vertex i with v | ξ <;> rcases hq : P.vertex (i + 1) with w | η
  · rw [P.side_def, hp, hq, extGeodesicSegment_inl_inl, ← geodesicLine_startParam hp,
      ← geodesicLine_endParam hq, geodesicSegment_geodesicLine,
      uIcc_of_le (startParam_lt_endParam hp hq).le]
    simp only [Sum.isLeft_inl, ↓reduceIte, mem_Ioo, Real.arctan_lt_arctan_iff, mem_image, mem_Icc,
      ne_eq, Sum.inl.injEq]
    constructor
    · rintro ⟨⟨t, ⟨h₁, h₂⟩, rfl⟩, hn₁, hn₂⟩
      exact ⟨t, ⟨h₁.lt_of_ne fun h ↦ hn₁ (congrArg _ h),
        h₂.lt_of_ne fun h ↦ hn₂ (congrArg _ h.symm)⟩, rfl⟩
    · rintro ⟨t, ⟨h₁, h₂⟩, rfl⟩
      exact ⟨⟨t, ⟨h₁.le, h₂.le⟩, rfl⟩, fun h ↦ h₁.ne (geodesicLine_injective _ h),
        fun h ↦ h₂.ne' (geodesicLine_injective _ h)⟩
  · rw [hp, hq] at hg; obtain ⟨_, hinf⟩ := isGeodesicFromTo_inl_inr.1 hg
    rw [P.side_def, hp, hq, ← geodesicLine_startParam hp, ← hinf, ← geodesicLine_image_Ici]
    simp only [Sum.isLeft_inl, Sum.isLeft_inr, ↓reduceIte, Bool.false_eq_true, mem_Ioo,
      Real.arctan_lt_arctan_iff, Real.arctan_lt_pi_div_two, and_true, mem_image, mem_Ici, ne_eq,
      Sum.inl.injEq, reduceCtorEq, not_false_eq_true]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hn⟩; exact ⟨t, ht.lt_of_ne fun h ↦ hn (congrArg _ h), rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht.le, rfl⟩, fun h ↦ ht.ne (geodesicLine_injective _ h)⟩
  · rw [hp, hq] at hg; obtain ⟨h0, _⟩ := isGeodesicFromTo_inr_inl.1 hg
    rw [P.side_def, hp, hq, ← h0, ← geodesicLine_endParam hq, ← geodesicLine_image_Iic]
    simp only [Sum.isLeft_inr, Sum.isLeft_inl, Bool.false_eq_true, ↓reduceIte, mem_Ioo,
      Real.neg_pi_div_two_lt_arctan, Real.arctan_lt_arctan_iff, true_and, mem_image, mem_Iic, ne_eq,
      Sum.inl.injEq, reduceCtorEq, not_false_eq_true]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hn⟩; exact ⟨t, ht.lt_of_ne fun h ↦ hn (congrArg _ h.symm), rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht.le, rfl⟩, fun h ↦ ht.ne' (geodesicLine_injective _ h)⟩
  · rw [hp, hq] at hg; obtain ⟨h0, hinf⟩ := isGeodesicFromTo_inr_inr.1 hg
    rw [P.side_def, hp, hq, ← h0, ← hinf, ← range_geodesicLine_eq_extGeodesicSegment]
    simp [Real.neg_pi_div_two_lt_arctan, Real.arctan_lt_pi_div_two]

/-! ### The public `edgeArc` API -/

private def edgeAngle (i : Fin n) (u : ℝ) : ℝ :=
  (startAngle P i + σ.edgeEndAngle i) / 2 + (σ.edgeEndAngle i - startAngle P i) / 2 * u

private theorem edgeAngle_neg_one (i : Fin n) : σ.edgeAngle i (-1) = startAngle P i := by
  unfold edgeAngle; ring

private theorem edgeAngle_one (i : Fin n) : σ.edgeAngle i 1 = σ.edgeEndAngle i := by
  unfold edgeAngle; ring

/-- The open `1`-cell arc carried by side `i` of `(P, σ)`, parametrized on `Ioo (-1 : ℝ) 1` along
`P.sideGeodesic i`. When `σ.pair i ≠ i`, its image on `Ioo (-1) 1` is `P.side i` minus any finite
endpoints; when `σ.pair i = i`, its image is the open half-side between `P.vertex i` and
`σ.selfPairedSideFixedPoint ⟨i, hi⟩`. -/
def edgeArc (i : Fin n) (u : ℝ) : ℍ :=
  geodesicLine (P.sideGeodesic i) (Real.tan (σ.edgeAngle i u))

private theorem edgeAngle_mem_Ioo (i : Fin n) {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    σ.edgeAngle i u ∈ Ioo (startAngle P i) (σ.edgeEndAngle i) := by
  have hlt := σ.startAngle_lt_edgeEndAngle i
  exact ⟨by unfold edgeAngle; nlinarith [hu.1], by unfold edgeAngle; nlinarith [hu.2]⟩

private theorem edgeAngle_mem_tan_domain (i : Fin n) {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    σ.edgeAngle i u ∈ Ioo (-(π / 2)) (π / 2) :=
  Ioo_subset_Ioo (neg_pi_div_two_le_startAngle i) (σ.edgeEndAngle_le_pi_div_two i)
    (σ.edgeAngle_mem_Ioo i hu)

private theorem geodesicLine_mem_image_edgeArc {i : Fin n} {t : ℝ}
    (ht : Real.arctan t ∈ Ioo (startAngle P i) (σ.edgeEndAngle i)) :
    geodesicLine (P.sideGeodesic i) t ∈ σ.edgeArc i '' Ioo (-1) 1 := by
  have hpos : 0 < σ.edgeEndAngle i - startAngle P i := sub_pos.2 (σ.startAngle_lt_edgeEndAngle i)
  set u := (2 * Real.arctan t - (startAngle P i + σ.edgeEndAngle i)) /
    (σ.edgeEndAngle i - startAngle P i)
  refine ⟨u, ⟨(lt_div_iff₀ hpos).2 (by linarith [ht.1]), (div_lt_iff₀ hpos).2 (by linarith [ht.2])⟩,
    ?_⟩
  have hang : σ.edgeAngle i u = Real.arctan t := by
    have hne : σ.edgeEndAngle i - startAngle P i ≠ 0 := hpos.ne'
    simp only [edgeAngle, u]; field_simp; ring
  rw [edgeArc, hang, Real.tan_arctan]

private theorem continuous_edgeAngle (i : Fin n) : Continuous (σ.edgeAngle i) := by
  unfold edgeAngle; fun_prop

/-- `σ.edgeArc i` is continuous on `Ioo (-1) 1`. -/
theorem continuousOn_edgeArc (i : Fin n) : ContinuousOn (σ.edgeArc i) (Ioo (-1) 1) :=
  (isometry_geodesicLine _).continuous.comp_continuousOn <|
    Real.continuousOn_tan_Ioo.comp (σ.continuous_edgeAngle i).continuousOn
      fun _ hu ↦ σ.edgeAngle_mem_tan_domain i hu

/-- `σ.edgeArc i` is injective on `Ioo (-1) 1`. -/
theorem injOn_edgeArc (i : Fin n) : InjOn (σ.edgeArc i) (Ioo (-1) 1) := by
  have hinj : Function.Injective (σ.edgeAngle i) := fun u v h ↦ by
    unfold edgeAngle at h
    exact mul_left_cancel₀ (half_pos (sub_pos.2 (σ.startAngle_lt_edgeEndAngle i))).ne' (by linarith)
  exact (geodesicLine_injective _).comp_injOn
    (Real.strictMonoOn_tan.injOn.comp hinj.injOn fun _ hu ↦ σ.edgeAngle_mem_tan_domain i hu)

private theorem edgeArc_props (i : Fin n) {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    σ.edgeArc i u ∈ P.side i ∧
      (∀ k, P.vertex k ≠ .inl (σ.edgeArc i u)) ∧
      ∀ hi : σ.pair i = i, Real.tan (σ.edgeAngle i u) < σ.midParam hi := by
  have hθ := σ.edgeAngle_mem_Ioo i hu
  have hdom := σ.edgeAngle_mem_tan_domain i hu
  have htan : Real.arctan (Real.tan (σ.edgeAngle i u)) = σ.edgeAngle i u :=
    Real.arctan_tan hdom.1 hdom.2
  obtain ⟨hside, hne₁, hne₂⟩ := mem_side_and_ne_endpoints_iff.2 ⟨Real.tan (σ.edgeAngle i u),
    by rw [htan]; exact Ioo_subset_Ioo_right (σ.edgeEndAngle_le_sideEndAngle i) hθ, rfl⟩
  refine ⟨hside, fun k hk ↦ ?_, fun hi ↦ Real.arctan_lt_arctan_iff.1 ?_⟩
  · rcases P.eq_or_eq_add_one_of_vertex_eq_inl_of_mem_side hk hside with rfl | rfl
    exacts [hne₁ hk, hne₂ hk]
  · rw [htan]; simpa [edgeEndAngle, hi] using hθ.2

/-- Every point of `σ.edgeArc i` on `Ioo (-1) 1` lies on `P.side i`. -/
theorem edgeArc_mem_side (i : Fin n) {u : ℝ} (hu : u ∈ Ioo (-1) 1) : σ.edgeArc i u ∈ P.side i :=
  (σ.edgeArc_props i hu).1

/-- No point of `σ.edgeArc i` on `Ioo (-1) 1` is a finite vertex of `P`. -/
theorem vertex_ne_inl_edgeArc (i : Fin n) {u : ℝ} (hu : u ∈ Ioo (-1) 1) (k : Fin n) :
    P.vertex k ≠ .inl (σ.edgeArc i u) :=
  (σ.edgeArc_props i hu).2.1 k

/-- No point of `σ.edgeArc i` on `Ioo (-1) 1` equals the fixed point of a self-paired side. -/
theorem edgeArc_ne_selfPairedSideFixedPoint (i : Fin n) {u : ℝ} (hu : u ∈ Ioo (-1) 1)
    (j : {k : Fin n // σ.pair k = k}) :
    σ.edgeArc i u ≠ σ.selfPairedSideFixedPoint j := by
  intro h
  obtain ⟨hside, -, hmid⟩ := σ.edgeArc_props i hu
  obtain ⟨hs_j, hp_j, hq_j, -⟩ := σ.selfPairedSideFixedPoint_spec j
  obtain rfl := P.eq_of_mem_side_of_mem_side hs_j hp_j hq_j (h ▸ hside)
  rw [edgeArc, ← σ.geodesicLine_midParam j.property] at h
  exact (hmid j.property).ne (geodesicLine_injective _ h)

/-- No side-paired image `σ.map i • σ.edgeArc i u` (`u ∈ Ioo (-1) 1`) equals the fixed point of a
self-paired side. -/
theorem map_smul_edgeArc_ne_selfPairedSideFixedPoint (i : Fin n) {u : ℝ} (hu : u ∈ Ioo (-1) 1)
    (j : {k : Fin n // σ.pair k = k}) :
    σ.map i • σ.edgeArc i u ≠ σ.selfPairedSideFixedPoint j := by
  intro h
  obtain ⟨hside, -, hmid⟩ := σ.edgeArc_props i hu
  obtain ⟨hs_j, hp_j, hq_j, -⟩ := σ.selfPairedSideFixedPoint_spec j
  have hj_eq : j.val = σ.pair i :=
    P.eq_of_mem_side_of_mem_side hs_j hp_j hq_j (h ▸ σ.map_smul_mem_side hside)
  have hij : j.val = i := by have h1 := congrArg σ.pair hj_eq; rwa [j.property, σ.pair_pair] at h1
  have hii : σ.pair i = i := hj_eq.symm.trans hij
  have hj : j = ⟨i, hii⟩ := Subtype.ext hij
  rw [hj, ← σ.geodesicLine_midParam hii, edgeArc,
    σ.map_smul_geodesicLine_of_pair_eq hii] at h
  linarith [geodesicLine_injective _ h, hmid hii]

/-- The image of `Ioo (-1) 1` under `σ.edgeArc i` is disjoint from its image under `σ.map i`. -/
theorem map_smul_edgeArc_ne_edgeArc (i : Fin n) {u v : ℝ}
    (hu : u ∈ Ioo (-1) 1) (hv : v ∈ Ioo (-1) 1) :
    σ.map i • σ.edgeArc i u ≠ σ.edgeArc i v := by
  intro h
  obtain ⟨hsu, -, hmidu⟩ := σ.edgeArc_props i hu
  obtain ⟨hsv, hnev, hmidv⟩ := σ.edgeArc_props i hv
  have hi : σ.pair i = i :=
    (P.eq_of_mem_side_of_mem_side hsv (hnev i) (hnev (i + 1))
      (h ▸ σ.map_smul_mem_side hsu)).symm
  rw [edgeArc, edgeArc, σ.map_smul_geodesicLine_of_pair_eq hi] at h
  linarith [geodesicLine_injective _ h, hmidu hi, hmidv hi]

/-- Every point of `P.side j` away from its finite endpoints lies on `σ.edgeArc j '' Ioo (-1) 1`,
equals `σ.selfPairedSideFixedPoint ⟨j, hj⟩`, or is sent into `σ.edgeArc j '' Ioo (-1) 1` by
`σ.map j`. -/
theorem mem_image_edgeArc_or_selfPaired_of_mem_side {j : Fin n} {z : ℍ}
    (hz : z ∈ P.side j) (hzp : P.vertex j ≠ .inl z) (hzq : P.vertex (j + 1) ≠ .inl z) :
    z ∈ σ.edgeArc j '' Ioo (-1) 1 ∨
      ∃ hj : σ.pair j = j, z = σ.selfPairedSideFixedPoint ⟨j, hj⟩ ∨
        σ.map j • z ∈ σ.edgeArc j '' Ioo (-1) 1 := by
  obtain ⟨t, ht, rfl⟩ := mem_side_and_ne_endpoints_iff.1 ⟨hz, hzp, hzq⟩
  by_cases hj : σ.pair j = j
  · rcases lt_trichotomy t (σ.midParam hj) with hlt | rfl | hgt
    · exact Or.inl (σ.geodesicLine_mem_image_edgeArc
        ⟨ht.1, by simpa [edgeEndAngle, hj] using Real.arctan_strictMono hlt⟩)
    · exact Or.inr ⟨hj, Or.inl (σ.geodesicLine_midParam hj)⟩
    · refine Or.inr ⟨hj, Or.inr (σ.map_smul_geodesicLine_of_pair_eq hj t ▸
        σ.geodesicLine_mem_image_edgeArc ⟨?_, ?_⟩)⟩
      · unfold startAngle
        split_ifs with hp
        · obtain ⟨v, hv⟩ := Sum.isLeft_iff.1 hp
          obtain ⟨w, hw, hm⟩ := σ.midParam_eq_avg hj hv
          have ht2 : t < endParam P j := by
            simpa [sideEndAngle, hw, Real.arctan_lt_arctan_iff] using ht.2
          exact Real.arctan_strictMono (by linarith)
        · exact Real.neg_pi_div_two_lt_arctan _
      · simpa [edgeEndAngle, hj] using
          Real.arctan_strictMono (by linarith : 2 * σ.midParam hj - t < σ.midParam hj)
  · exact Or.inl (σ.geodesicLine_mem_image_edgeArc (by simpa [edgeEndAngle, hj] using ht))

/-! ### Endpoint limits -/

private theorem tendsto_edgeAngle_neg_one (i : Fin n) :
    Filter.Tendsto (σ.edgeAngle i) (𝓝[Ioo (-1) 1] (-1)) (𝓝[>] (startAngle P i)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((σ.edgeAngle_neg_one i ▸ (σ.continuous_edgeAngle i).tendsto (-1)).mono_left nhdsWithin_le_nhds)
    (Filter.mem_of_superset self_mem_nhdsWithin fun _ hu ↦ (σ.edgeAngle_mem_Ioo i hu).1)

private theorem tendsto_edgeAngle_one (i : Fin n) :
    Filter.Tendsto (σ.edgeAngle i) (𝓝[Ioo (-1) 1] 1) (𝓝[<] (σ.edgeEndAngle i)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((σ.edgeAngle_one i ▸ (σ.continuous_edgeAngle i).tendsto 1).mono_left nhdsWithin_le_nhds)
    (Filter.mem_of_superset self_mem_nhdsWithin fun _ hu ↦ (σ.edgeAngle_mem_Ioo i hu).2)

private theorem tendsto_edgeArc_of_tendsto_arctan {i : Fin n} {c t : ℝ}
    (h : Filter.Tendsto (σ.edgeAngle i) (𝓝[Ioo (-1) 1] c) (𝓝 (Real.arctan t))) :
    Filter.Tendsto (σ.edgeArc i) (𝓝[Ioo (-1) 1] c) (𝓝 (geodesicLine (P.sideGeodesic i) t)) := by
  have htan : Filter.Tendsto Real.tan (𝓝 (Real.arctan t)) (𝓝 t) := by
    simpa [Real.tan_arctan] using (Real.continuousOn_tan_Ioo.continuousAt
      (Ioo_mem_nhds (Real.neg_pi_div_two_lt_arctan t) (Real.arctan_lt_pi_div_two t))).tendsto
  exact ((isometry_geodesicLine _).continuous.tendsto t).comp (htan.comp h)

/-- At a finite starting vertex `P.vertex i = .inl v`, `σ.edgeArc i u → v` as `u → -1` within
`Ioo (-1) 1`. -/
theorem tendsto_edgeArc_neg_one_of_eq_inl {i : Fin n} {v : ℍ} (hv : P.vertex i = .inl v) :
    Filter.Tendsto (σ.edgeArc i) (𝓝[Ioo (-1) 1] (-1)) (𝓝 v) :=
  geodesicLine_startParam hv ▸ σ.tendsto_edgeArc_of_tendsto_arctan
    ((startAngle_of_eq_inl hv ▸ σ.tendsto_edgeAngle_neg_one i).mono_right nhdsWithin_le_nhds)

/-- At an ideal starting vertex `P.vertex i = .inr ξ` sent to `∞` by `g : PSL(2, ℝ)`, the horodisc
height `(g • σ.edgeArc i u).im` tends to `∞` as `u → -1` within `Ioo (-1) 1`. -/
theorem tendsto_edgeArc_neg_one_atImInfty_of_eq_inr {i : Fin n} {ξ : OnePoint ℝ} {g : PSL(2, ℝ)}
    (hξ : P.vertex i = .inr ξ) (hg : g • ξ = ∞) :
    Filter.Tendsto (σ.edgeArc i) (𝓝[Ioo (-1) 1] (-1))
      (Filter.comap (fun z : ℍ ↦ (g • z).im) Filter.atTop) := by
  have hside := P.isGeodesicFromTo_sideGeodesic i; rw [hξ] at hside
  have hg0 : (g * P.sideGeodesic i) • ((0 : ℝ) : OnePoint ℝ) = ∞ := by
    rw [mul_smul, hside.smul_zero_eq, hg]
  have him : Filter.Tendsto (geodesicLine (P.sideGeodesic i)) Filter.atBot
      (Filter.comap (fun z : ℍ ↦ (g • z).im) Filter.atTop) :=
    Filter.tendsto_comap_iff.2 <|
      (Filter.tendsto_comap_iff.1 (tendsto_geodesicLine_atBot_atImInfty hg0)).congr
        fun t ↦ by rw [Function.comp_apply, Function.comp_apply, smul_geodesicLine]
  exact him.comp <| Real.tendsto_tan_neg_pi_div_two.comp
    (startAngle_of_eq_inr hξ ▸ σ.tendsto_edgeAngle_neg_one i)

/-- On a self-paired side `i`, `σ.edgeArc i u → σ.selfPairedSideFixedPoint ⟨i, hi⟩` as `u → 1`
within `Ioo (-1) 1`. -/
theorem tendsto_edgeArc_one_of_pair_eq {i : Fin n} (hi : σ.pair i = i) :
    Filter.Tendsto (σ.edgeArc i) (𝓝[Ioo (-1) 1] 1)
      (𝓝 (σ.selfPairedSideFixedPoint ⟨i, hi⟩)) :=
  σ.geodesicLine_midParam hi ▸ σ.tendsto_edgeArc_of_tendsto_arctan
    ((σ.edgeEndAngle_of_pair_eq hi ▸ σ.tendsto_edgeAngle_one i).mono_right nhdsWithin_le_nhds)

/-- On a non-self-paired side `i` with finite end vertex `P.vertex (i + 1) = .inl w`,
`σ.edgeArc i u → w` as `u → 1` within `Ioo (-1) 1`. -/
theorem tendsto_edgeArc_one_of_eq_inl {i : Fin n} {w : ℍ} (hi : σ.pair i ≠ i)
    (hw : P.vertex (i + 1) = .inl w) :
    Filter.Tendsto (σ.edgeArc i) (𝓝[Ioo (-1) 1] 1) (𝓝 w) :=
  geodesicLine_endParam hw ▸ σ.tendsto_edgeArc_of_tendsto_arctan
    ((σ.edgeEndAngle_of_eq_inl hi hw ▸ σ.tendsto_edgeAngle_one i).mono_right nhdsWithin_le_nhds)

/-- On a non-self-paired side `i` with ideal end vertex `P.vertex (i + 1) = .inr η` sent to `∞`
by `g : PSL(2, ℝ)`, `(g • σ.edgeArc i u).im → ∞` as `u → 1` within `Ioo (-1) 1`. -/
theorem tendsto_edgeArc_one_atImInfty_of_eq_inr {i : Fin n} {η : OnePoint ℝ} {g : PSL(2, ℝ)}
    (hi : σ.pair i ≠ i) (hη : P.vertex (i + 1) = .inr η) (hg : g • η = ∞) :
    Filter.Tendsto (σ.edgeArc i) (𝓝[Ioo (-1) 1] 1)
      (Filter.comap (fun z : ℍ ↦ (g • z).im) Filter.atTop) := by
  have hside := P.isGeodesicFromTo_sideGeodesic i; rw [hη] at hside
  have hginf : (g * P.sideGeodesic i) • (∞ : OnePoint ℝ) = ∞ := by
    rw [mul_smul, hside.smul_infty_eq, hg]
  have him : Filter.Tendsto (geodesicLine (P.sideGeodesic i)) Filter.atTop
      (Filter.comap (fun z : ℍ ↦ (g • z).im) Filter.atTop) :=
    Filter.tendsto_comap_iff.2 <|
      (Filter.tendsto_comap_iff.1 (tendsto_geodesicLine_atTop_atImInfty hginf)).congr
        fun t ↦ by rw [Function.comp_apply, Function.comp_apply, smul_geodesicLine]
  exact him.comp <| Real.tendsto_tan_pi_div_two.comp
    (σ.edgeEndAngle_of_eq_inr hi hη ▸ σ.tendsto_edgeAngle_one i)

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

end
