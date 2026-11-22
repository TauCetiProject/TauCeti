/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Betweenness
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Uniqueness
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.InjectivityRadius.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Metric balls and unique minimizing geodesics below the injectivity radius

When a Riemannian manifold `M` carries its Riemannian distance (`IsRiemannianManifold`), Gauss's
lemma identifies the exponential image of every normal tangent ball `B(0, r)` with the open metric
`r`-ball around `p`. This file records the resulting metric-ball characterization of `inj(p)`,
radial distance identities, and existence and uniqueness of minimizing geodesics below `inj(p)` and
`inj(M)` in `EMetricSpace`, complete `MetricSpace`, and intrinsic `riemannianEDist` forms.

## Main results

* `TauCeti.Manifold.injectivityRadiusAt_eq_sSup_eball`,
  `TauCeti.Manifold.injectivityRadiusAt_eq_sSup_ball`: supremum characterizations onto metric balls.
* `TauCeti.Manifold.edist_riemannianExp_eq_enorm_of_enorm_lt_injectivityRadiusAt`,
  `TauCeti.Manifold.dist_riemannianExp_eq_norm_of_enorm_lt_injectivityRadiusAt`,
  `TauCeti.Manifold.image_riemannianExp_eball_injectivityRadiusAt`: radial distances and
  `exp_p '' Metric.eball 0 (inj(p)) = Metric.eball p (inj(p))`.
* `TauCeti.Manifold.existsUnique_riemannianExp_eq_of_edist_lt_injectivityRadiusAt`,
  `TauCeti.Manifold.exists_isGeodesicCurveOn_Icc_and_unique_of_edist_lt_injectivityRadiusAt`,
  `TauCeti.Manifold.exists_isGeodesicCurveOn_Icc_and_unique_of_edist_lt_injectivityRadius`,
  `TauCeti.Manifold.exists_isGeodesicSegment_and_unique_of_ofReal_dist_lt_injectivityRadiusAt`,
  `TauCeti.Manifold.exists_isGeodesicCurveOn_Icc_and_unique_of_riemannianEDist_lt_injectivityRadius`
  : existence and uniqueness of minimizing geodesics below `inj(p)` and `inj(M)`.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed., World Scientific (2007),
  Definition 4.1.23, p. 151.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapters 6
  and 10.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser (1992), Chapter 3, §3 and Chapter 13, §2.
-/

public section

open Bundle Function Manifold Metric Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

section EMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-! ### Metric-ball supremum characterization -/

/-- **Metric-ball supremum formula for `injectivityRadiusAt`.** The injectivity radius at `p` is the
supremum over `r ≥ 0` of the radii for which `exp_p` restricts to a smooth partial diffeomorphism
from the open tangent `r`-ball onto the open extended-metric `r`-ball around `p`. -/
theorem injectivityRadiusAt_eq_sSup_eball (p : M) :
    injectivityRadiusAt I M p =
      sSup (ENNReal.ofReal '' {r : ℝ | 0 ≤ r ∧
        ∃ e : PartialDiffeomorph 𝓘(ℝ, TangentSpace I p) I (TangentSpace I p) M ∞,
          e.source = Metric.ball 0 r ∧ e.target = Metric.eball p (ENNReal.ofReal r) ∧
            EqOn e (riemannianExp I M p) (Metric.ball 0 r)}) := by
  refine le_antisymm ?_ (sSup_le ?_)
  · rw [injectivityRadiusAt_def]
    refine iSup₂_le fun r h ↦ le_sSup ⟨r, ⟨(by simpa only [Metric.mem_ball, dist_self] using
      h.zero_mem : (0 : ℝ) < r).le, (isNormalDomain_ball_iff_exists_partialDiffeomorph_eball
        (by simpa only [Metric.mem_ball, dist_self] using h.zero_mem)).1 h⟩, rfl⟩
  · rintro _ ⟨r, ⟨hr, he⟩, rfl⟩
    rcases hr.eq_or_lt with rfl | hr <;> [simp;
      exact ((isNormalDomain_ball_iff_exists_partialDiffeomorph_eball hr).2
        he).ofReal_le_injectivityRadiusAt]

/-! ### Radial distance and geodesic ball of radius `inj(p)` -/

/-- **Radial distance identity below `inj(p)`.** For every tangent vector `v` at `p` with
`‖v‖ₑ < injectivityRadiusAt I M p`, the Riemannian distance from `p` to `exp_p v` is `‖v‖ₑ`. -/
theorem edist_riemannianExp_eq_enorm_of_enorm_lt_injectivityRadiusAt {p : M}
    {v : TangentSpace I p} (hv : ‖v‖ₑ < injectivityRadiusAt I M p) :
    edist p (riemannianExp I M p v) = ‖v‖ₑ :=
  let ⟨_, _, hvr, _, hball⟩ := exists_isNormalDomain_ball_of_enorm_lt_injectivityRadiusAt hv
  hball.edist_riemannianExp_eq_of_mem_ball subset_rfl hvr

/-- **Radial geodesic segments below `inj(p)` are minimizing.** -/
theorem pathELength_riemannianExp_smul_eq_edist_of_enorm_lt_injectivityRadiusAt {p : M}
    {v : TangentSpace I p} (hv : ‖v‖ₑ < injectivityRadiusAt I M p) :
    pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1 =
      edist p (riemannianExp I M p v) :=
  let ⟨_, _, hvr, _, hball⟩ := exists_isNormalDomain_ball_of_enorm_lt_injectivityRadiusAt hv
  hball.pathELength_riemannianExp_smul_eq_edist_of_mem_ball subset_rfl hvr

/-- **The exponential image of the `inj(p)`-ball is the metric `inj(p)`-ball.** No completeness or
connectedness hypothesis is needed: when `inj(p) = ⊤`, `Metric.eball p ⊤` consists of the points at
finite Riemannian distance from `p`. -/
theorem image_riemannianExp_eball_injectivityRadiusAt (p : M) :
    riemannianExp I M p '' Metric.eball 0 (injectivityRadiusAt I M p) =
      Metric.eball p (injectivityRadiusAt I M p) := by
  ext q; constructor
  · rintro ⟨v, hv, rfl⟩; simp only [Metric.mem_eball, edist_zero_right] at hv ⊢
    rwa [edist_comm, edist_riemannianExp_eq_enorm_of_enorm_lt_injectivityRadiusAt hv]
  · intro hq; rw [Metric.mem_eball, edist_comm] at hq
    obtain ⟨r, -, hqr, hr⟩ := ENNReal.lt_iff_exists_real_btwn.1 hq
    have hr₀ : 0 < r := ENNReal.ofReal_pos.1 (zero_le.trans_lt hqr)
    obtain ⟨v, hv, rfl⟩ : q ∈ riemannianExp I M p '' Metric.ball 0 r := by
      rwa [(isNormalDomain_ball_of_lt_injectivityRadiusAt hr₀ hr).image_riemannianExp_ball
        subset_rfl, Metric.mem_eball']
    exact ⟨v, by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
      exact ((ENNReal.ofReal_lt_ofReal_iff hr₀).2 (mem_ball_zero_iff.1 hv)).trans hr, rfl⟩

/-! ### Existence and uniqueness of minimizing geodesics below `inj(p)` and `inj(M)` -/

/-- Every point `q` at extended distance strictly less than `inj(p)` from `p` has a unique preimage
under `exp_p` in `Metric.eball 0 (inj(p))`. -/
theorem existsUnique_riemannianExp_eq_of_edist_lt_injectivityRadiusAt {p q : M}
    (hq : edist p q < injectivityRadiusAt I M p) :
    ∃! v : TangentSpace I p, ‖v‖ₑ < injectivityRadiusAt I M p ∧ riemannianExp I M p v = q := by
  obtain ⟨v, hv, rfl⟩ : q ∈ riemannianExp I M p '' Metric.eball 0 (injectivityRadiusAt I M p) := by
    rwa [image_riemannianExp_eball_injectivityRadiusAt, Metric.mem_eball, edist_comm]
  simp only [Metric.mem_eball, edist_zero_right] at hv
  exact ⟨v, ⟨hv, rfl⟩, fun w ⟨hw, hwq⟩ ↦ injOn_riemannianExp_eball_injectivityRadiusAt p
    (by simpa only [Metric.mem_eball, edist_zero_right] using hw)
    (by simpa only [Metric.mem_eball, edist_zero_right] using hv) hwq⟩

/-- **Uniqueness of minimizing geodesics to `exp_p v` below `inj(p)`.** If
`‖v‖ₑ < injectivityRadiusAt I M p`, then any geodesic `γ` on `[0, 1]` from `p` to `exp_p v` of
length at most `edist p (exp_p v)` agrees with the radial geodesic `t ↦ exp_p (t • v)` on `[0, 1]`.
The competitor need not be assumed to remain in a normal neighbourhood: the escape estimate confines
it automatically. -/
theorem eqOn_riemannianExp_smul_of_isGeodesicCurveOn_of_enorm_lt_injectivityRadiusAt {p : M}
    {v : TangentSpace I p} {γ : ℝ → M} (hv : ‖v‖ₑ < injectivityRadiusAt I M p)
    (hγ : IsGeodesicCurveOn I γ (Icc 0 1)) (hγ0 : γ 0 = p)
    (hγ1 : γ 1 = riemannianExp I M p v)
    (hlen : pathELength I γ 0 1 ≤ edist p (riemannianExp I M p v)) :
    EqOn γ (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) := by
  obtain ⟨R, -, hvR, -, hball⟩ := exists_isNormalDomain_ball_of_enorm_lt_injectivityRadiusAt hv
  have hnorm : ‖v‖ < R := mem_ball_zero_iff.1 hvR
  have hrad_len := hball.pathELength_riemannianExp_smul_eq_edist_of_mem_ball subset_rfl hvR
  -- Separate `‖v‖` from `R` by `(‖v‖ + R) / 2` so the escape estimate forces `γ` into `B(0, R)`.
  have hmaps : MapsTo γ (Icc 0 1) (riemannianExp I M p '' Metric.ball 0 R) := by_contra fun hnot ↦
    lt_irrefl _ ((hball.pathELength_riemannianExp_smul_lt_of_not_mapsTo
      (Metric.closedBall_subset_ball (by linarith : (‖v‖ + R) / 2 < R))
      (mem_ball_zero_iff.2 (by linarith : ‖v‖ < (‖v‖ + R) / 2))
      (hγ.contMDiffOn.of_le (by norm_num)) hγ0 hnot).trans_le (hlen.trans_eq hrad_len.symm))
  exact hball.eqOn_riemannianExp_smul_of_geodesic_pathELength_le hvR hγ hmaps hγ0 hγ1
    (hlen.trans_eq hrad_len.symm)

/-- **Unique minimizing geodesic below `inj(p)`.** Whenever `edist p q < injectivityRadiusAt I M p`,
there is a tangent vector `v` with `‖v‖ₑ = edist p q` and `exp_p v = q` such that
`t ↦ exp_p (t • v)` is a geodesic on `[0, 1]` from `p` to `q` of length `edist p q` (the constant
geodesic at `p` when `p = q`), and every geodesic on `[0, 1]` from `p` to `q` of length at most
`edist p q` agrees with `t ↦ exp_p (t • v)` on `[0, 1]`. -/
theorem exists_isGeodesicCurveOn_Icc_and_unique_of_edist_lt_injectivityRadiusAt {p q : M}
    (hq : edist p q < injectivityRadiusAt I M p) :
    ∃ v : TangentSpace I p, ‖v‖ₑ = edist p q ∧ riemannianExp I M p v = q ∧
      IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) ∧
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1 = edist p q ∧
      ∀ γ : ℝ → M, IsGeodesicCurveOn I γ (Icc 0 1) → γ 0 = p → γ 1 = q →
        pathELength I γ 0 1 ≤ edist p q →
        EqOn γ (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) := by
  obtain ⟨v, ⟨hv, rfl⟩, -⟩ := existsUnique_riemannianExp_eq_of_edist_lt_injectivityRadiusAt hq
  exact ⟨v, (edist_riemannianExp_eq_enorm_of_enorm_lt_injectivityRadiusAt hv).symm, rfl,
    isGeodesicCurveOn_riemannianExp_smul_Icc zero_lt_one zero_mem_geodesicInterval
      (mem_expDomain_iff.1 (mem_expDomain_of_enorm_lt_injectivityRadiusAt hv)),
    pathELength_riemannianExp_smul_eq_edist_of_enorm_lt_injectivityRadiusAt hv, fun _ ↦
      eqOn_riemannianExp_smul_of_isGeodesicCurveOn_of_enorm_lt_injectivityRadiusAt hv⟩

/-- **Unique minimizing geodesic below the global injectivity radius `inj(M)`.** Whenever
`edist p q < injectivityRadius I M`, `p` and `q` are joined by a unique minimizing geodesic on
`[0, 1]`, given by `t ↦ exp_p (t • v)` (including the constant geodesic when `p = q`). -/
theorem exists_isGeodesicCurveOn_Icc_and_unique_of_edist_lt_injectivityRadius {p q : M}
    (hq : edist p q < injectivityRadius I M) :
    ∃ v : TangentSpace I p, ‖v‖ₑ = edist p q ∧ riemannianExp I M p v = q ∧
      IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) ∧
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1 = edist p q ∧
      ∀ γ : ℝ → M, IsGeodesicCurveOn I γ (Icc 0 1) → γ 0 = p → γ 1 = q →
        pathELength I γ 0 1 ≤ edist p q →
        EqOn γ (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) :=
  exists_isGeodesicCurveOn_Icc_and_unique_of_edist_lt_injectivityRadiusAt
    (hq.trans_le (injectivityRadius_le p))

end EMetric

section Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- Ordinary-metric counterpart of `injectivityRadiusAt_eq_sSup_eball`: `inj(p)` is the supremum
over `r ≥ 0` of the radii for which `exp_p` restricts to a smooth partial diffeomorphism from the
tangent open `r`-ball `Metric.ball 0 r` onto the metric `r`-ball `Metric.ball p r`. -/
theorem injectivityRadiusAt_eq_sSup_ball (p : M) :
    injectivityRadiusAt I M p =
      sSup (ENNReal.ofReal '' {r : ℝ | 0 ≤ r ∧
        ∃ e : PartialDiffeomorph 𝓘(ℝ, TangentSpace I p) I (TangentSpace I p) M ∞,
          e.source = Metric.ball 0 r ∧ e.target = Metric.ball p r ∧
            EqOn e (riemannianExp I M p) (Metric.ball 0 r)}) := by
  simp only [injectivityRadiusAt_eq_sSup_eball, Metric.eball_ofReal]

/-- Ordinary-metric radial distance identity below `inj(p)`. -/
theorem dist_riemannianExp_eq_norm_of_enorm_lt_injectivityRadiusAt {p : M}
    {v : TangentSpace I p} (hv : ‖v‖ₑ < injectivityRadiusAt I M p) :
    dist p (riemannianExp I M p v) = ‖v‖ := by
  rw [dist_edist, edist_riemannianExp_eq_enorm_of_enorm_lt_injectivityRadiusAt hv, toReal_eNorm]

/-- When `‖v‖ₑ < injectivityRadiusAt I M p`, the maximal geodesic from `(p, v)` is a metric geodesic
segment (`IsGeodesicSegment`) on `[0, 1]`. -/
theorem isGeodesicSegment_maximalGeodesic_of_enorm_lt_injectivityRadiusAt {p : M}
    {v : TangentSpace I p} (hv : ‖v‖ₑ < injectivityRadiusAt I M p) :
    IsGeodesicSegment (maximalGeodesic I M p v) p (riemannianExp I M p v) :=
  isGeodesicSegment_maximalGeodesic
    (dist_riemannianExp_eq_norm_of_enorm_lt_injectivityRadiusAt hv).symm.le

/-- **Unique metric geodesic segment below `inj(p)` on a complete Riemannian manifold.** Whenever
`ENNReal.ofReal (dist p q) < injectivityRadiusAt I M p`, there is a tangent vector `v` with
`‖v‖ = dist p q` and `exp_p v = q` such that `t ↦ exp_p (t • v)` is a metric geodesic segment from
`p` to `q` (the constant curve when `p = q`), and every metric geodesic segment from `p` to `q`
agrees with `t ↦ exp_p (t • v)` on `[0, 1]`. -/
theorem exists_isGeodesicSegment_and_unique_of_ofReal_dist_lt_injectivityRadiusAt
    [CompleteSpace M] {p q : M}
    (hq : ENNReal.ofReal (dist p q) < injectivityRadiusAt I M p) :
    ∃ v : TangentSpace I p, ‖v‖ = dist p q ∧ riemannianExp I M p v = q ∧
      IsGeodesicSegment (fun t : ℝ ↦ riemannianExp I M p (t • v)) p q ∧
      ∀ γ : ℝ → M, IsGeodesicSegment γ p q →
        EqOn γ (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) := by
  obtain ⟨v, ⟨hv, rfl⟩, -⟩ :=
    existsUnique_riemannianExp_eq_of_edist_lt_injectivityRadiusAt (p := p) (q := q)
      (by rwa [edist_dist])
  obtain ⟨_, -, hvr, -, hball⟩ := exists_isNormalDomain_ball_of_enorm_lt_injectivityRadiusAt hv
  exact ⟨v, (dist_riemannianExp_eq_norm_of_enorm_lt_injectivityRadiusAt hv).symm, rfl,
    (funext (riemannianExp_smul p v)).symm ▸
      isGeodesicSegment_maximalGeodesic_of_enorm_lt_injectivityRadiusAt hv,
    fun _ hγ ↦ hball.eqOn_riemannianExp_smul_of_isGeodesicSegment subset_rfl hvr hγ⟩

/-- **Unique metric geodesic segment below `inj(M)` on a complete Riemannian manifold.** -/
theorem exists_isGeodesicSegment_and_unique_of_ofReal_dist_lt_injectivityRadius
    [CompleteSpace M] {p q : M}
    (hq : ENNReal.ofReal (dist p q) < injectivityRadius I M) :
    ∃ v : TangentSpace I p, ‖v‖ = dist p q ∧ riemannianExp I M p v = q ∧
      IsGeodesicSegment (fun t : ℝ ↦ riemannianExp I M p (t • v)) p q ∧
      ∀ γ : ℝ → M, IsGeodesicSegment γ p q →
        EqOn γ (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) :=
  exists_isGeodesicSegment_and_unique_of_ofReal_dist_lt_injectivityRadiusAt
    (hq.trans_le (injectivityRadius_le p))

end Metric

section TopologicalSpace

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### Intrinsic `riemannianEDist` versions without `[IsRiemannianManifold I M]` -/

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- Transfers a `riemannianEDist` statement to the `EMetricSpace.ofRiemannianMetric` instance. -/
private theorem with_ofRiemannianMetric {P : (M → M → ℝ≥0∞) → Prop}
    (h : ∀ [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)],
      @P (@edist M (EMetricSpace.ofRiemannianMetric I M).toEDist)) :
    P (riemannianEDist I) := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have h1 := h
  rwa [show (edist : M → M → ℝ≥0∞) = riemannianEDist I from
    funext₂ (IsRiemannianManifold.out (I := I))] at h1

/-- **Intrinsic radial distance below `inj(p)`.** Requires no `IsRiemannianManifold` instance on
`M`. -/
theorem riemannianEDist_riemannianExp_eq_enorm_of_enorm_lt_injectivityRadiusAt {p : M}
    {v : TangentSpace I p} (hv : ‖v‖ₑ < injectivityRadiusAt I M p) :
    riemannianEDist I p (riemannianExp I M p v) = ‖v‖ₑ :=
  with_ofRiemannianMetric (P := fun d ↦ d p (riemannianExp I M p v) = ‖v‖ₑ) <| by
    intro _
    let : EMetricSpace M := .ofRiemannianMetric I M
    exact edist_riemannianExp_eq_enorm_of_enorm_lt_injectivityRadiusAt hv

/-- Every point `q` with `riemannianEDist I p q < injectivityRadiusAt I M p` has a unique preimage
under `exp_p` of extended norm strictly less than `inj(p)`. -/
theorem existsUnique_riemannianExp_eq_of_riemannianEDist_lt_injectivityRadiusAt {p q : M}
    (hq : riemannianEDist I p q < injectivityRadiusAt I M p) :
    ∃! v : TangentSpace I p, ‖v‖ₑ < injectivityRadiusAt I M p ∧ riemannianExp I M p v = q :=
  with_ofRiemannianMetric
    (P := fun d ↦ d p q < injectivityRadiusAt I M p →
      ∃! v : TangentSpace I p, ‖v‖ₑ < injectivityRadiusAt I M p ∧ riemannianExp I M p v = q)
    (by
      intro _
      let : EMetricSpace M := .ofRiemannianMetric I M
      exact existsUnique_riemannianExp_eq_of_edist_lt_injectivityRadiusAt) hq

/-- **Unique minimizing geodesic below `inj(p)` (`riemannianEDist` form).** Applicable even when `M`
carries a non-intrinsic ambient metric (such as the chordal metric on an embedded sphere). -/
theorem exists_isGeodesicCurveOn_Icc_and_unique_of_riemannianEDist_lt_injectivityRadiusAt {p q : M}
    (hq : riemannianEDist I p q < injectivityRadiusAt I M p) :
    ∃ v : TangentSpace I p, ‖v‖ₑ = riemannianEDist I p q ∧ riemannianExp I M p v = q ∧
      IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) ∧
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1 = riemannianEDist I p q ∧
      ∀ γ : ℝ → M, IsGeodesicCurveOn I γ (Icc 0 1) → γ 0 = p → γ 1 = q →
        pathELength I γ 0 1 ≤ riemannianEDist I p q →
        EqOn γ (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) :=
  with_ofRiemannianMetric
    (P := fun d ↦ d p q < injectivityRadiusAt I M p →
      ∃ v : TangentSpace I p, ‖v‖ₑ = d p q ∧ riemannianExp I M p v = q ∧
        IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) ∧
        pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1 = d p q ∧
        ∀ γ : ℝ → M, IsGeodesicCurveOn I γ (Icc 0 1) → γ 0 = p → γ 1 = q →
          pathELength I γ 0 1 ≤ d p q →
          EqOn γ (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1))
    (by
      intro _
      let : EMetricSpace M := .ofRiemannianMetric I M
      exact exists_isGeodesicCurveOn_Icc_and_unique_of_edist_lt_injectivityRadiusAt) hq

/-- **Unique minimizing geodesic below `inj(M)` (`riemannianEDist` form).** -/
theorem exists_isGeodesicCurveOn_Icc_and_unique_of_riemannianEDist_lt_injectivityRadius {p q : M}
    (hq : riemannianEDist I p q < injectivityRadius I M) :
    ∃ v : TangentSpace I p, ‖v‖ₑ = riemannianEDist I p q ∧ riemannianExp I M p v = q ∧
      IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) ∧
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1 = riemannianEDist I p q ∧
      ∀ γ : ℝ → M, IsGeodesicCurveOn I γ (Icc 0 1) → γ 0 = p → γ 1 = q →
        pathELength I γ 0 1 ≤ riemannianEDist I p q →
        EqOn γ (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 1) :=
  exists_isGeodesicCurveOn_Icc_and_unique_of_riemannianEDist_lt_injectivityRadiusAt
    (hq.trans_le (injectivityRadius_le p))

end TopologicalSpace

end TauCeti.Manifold

end
