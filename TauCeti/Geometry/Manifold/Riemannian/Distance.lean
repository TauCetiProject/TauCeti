/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import TauCeti.Geometry.Manifold.ContMDiff.Defs
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Comparison and finiteness of the Riemannian distance, and the induced metric space

`Manifold.riemannianEDist I x y` is the infimum of the lengths of `C¹` paths from `x` to `y`, an
*extended* distance: it is `∞` as soon as no such path exists. This file identifies exactly when it
is finite, and uses that to promote the extended metric space structure
`EMetricSpace.ofRiemannianMetric` of a preconnected Riemannian manifold to an ordinary metric space
structure, which is what statements about `dist`, `ProperSpace` and `CompleteSpace` need.

The key point is that `{y | riemannianEDist I x y < ∞}` is clopen: it is open because nearby points
are at small Riemannian distance (`eventually_riemannianEDist_lt`), and its complement is open for
the same reason. Hence it contains the connected component of `x`. Conversely a `C¹` path is in
particular continuous, so a point at finite Riemannian distance from `x` lies in the connected
component of `x`. Together these give
`riemannianEDist_lt_top_iff_mem_connectedComponent`, of which finiteness on a preconnected manifold
is the special case that matters downstream.

## Main results

* `TauCeti.Manifold.riemannianEDist_le_mul`: a `C¹` map with differential uniformly bounded by
  a positive constant increases Riemannian extended distances by at most that factor.
* `TauCeti.Manifold.ofReal_mul_eNorm_sub_le_pathELength_comp`: conversely, a map from a normed
  space whose differential stretches vectors by at least `c` along a `C¹` curve sends it to a curve
  of length at least `c` times the displacement of the curve.
* `TauCeti.IsRiemannianManifold.lipschitzWith_of_norm_mfderiv_le`: the corresponding global
  Lipschitz estimate when both ambient extended distances are Riemannian.
* `TauCeti.Manifold.riemannianEDist_lt_top_iff_mem_connectedComponent`: the Riemannian distance from
  `x` to `y` is finite if and only if `y` lies in the connected component of `x`.
* `TauCeti.Manifold.riemannianEDist_ne_top`: on a preconnected manifold the Riemannian distance is
  never `∞`.
* `TauCeti.PseudoMetricSpace.ofRiemannianMetric` and `TauCeti.MetricSpace.ofRiemannianMetric`: the
  (pseudo)metric space structures of a preconnected Riemannian manifold, refining
  `PseudoEMetricSpace.ofRiemannianMetric` and `EMetricSpace.ofRiemannianMetric`; both satisfy
  `IsRiemannianManifold I M`, and `PseudoMetricSpace.ofRiemannianMetric_eq`,
  `MetricSpace.ofRiemannianMetric_eq`, and `MetricSpace.completeSpace_ofRiemannianMetric` compare
  them with an existing ambient `(Pseudo)MetricSpace` satisfying `IsRiemannianManifold I M`.
* `TauCeti.IsRiemannianManifold.edist_le_pathELength` and
  `TauCeti.IsRiemannianManifold.dist_le_toReal_pathELength`: the ambient (extended) distance of a
  Riemannian manifold, read through `IsRiemannianManifold.out`, is bounded by the length of any
  `C¹` path.
* `TauCeti.IsRiemannianManifold.edist_le_of_norm_mfderiv_le`: the mean-value inequality for a
  `C¹` map from a normed space into a Riemannian manifold along a segment.
* `TauCeti.IsRiemannianManifold.lipschitzOnWith_of_norm_curveVelocity_le`: a `C¹` curve whose speed
  is bounded by `K` on an interval is `K`-Lipschitz there.
* `TauCeti.IsRiemannianManifold.exists_lipschitzOnWith_of_contMDiffAt`: a map from a
  real normed space into a manifold with continuous Riemannian metric is Lipschitz
  on a ball around each point where it is `C¹`.
* `TauCeti.IsRiemannianManifold.exists_lipschitzOnWith_extChartAt_symm_of_isCompact`: on a
  boundaryless manifold, the inverse of an extended chart is Lipschitz, for the ambient distance,
  on each compact subset of the chart target.
* `TauCeti.Manifold.le_riemannianEDist_of_forall_le_pathELength`: the extended distance is bounded
  below by any bound valid for the lengths of *all* `C¹` curves joining two points, since it is the
  infimum of those lengths.
* `TauCeti.Manifold.riemannianEDist_le_of_tendsto_of_forall_pathELength_le` and
  `TauCeti.Manifold.tendsto_of_mapClusterPt_of_forall_pathELength_le`: a convergent `C¹` curve is
  within its tail length of its limit, and a curve whose tail lengths tend to zero converges to each
  of its cluster points.

The path-containment lemma `TauCeti.Manifold.mem_ball_of_pathELength_lt` is adapted from
Giada Franz’s verified `ForTauCeti` formalization.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7 §2, Def. 2.4.
* `Mathlib/Geometry/Manifold/Riemannian/Basic.lean` (S. Gouëzel):
  `PseudoEMetricSpace.ofRiemannianMetric`, `EMetricSpace.ofRiemannianMetric`, and their
  `IsRiemannianManifold` instances, which the (pseudo)metric constructions here adapt.
-/

public section

open Bundle Manifold Set
open scoped ENNReal Manifold NNReal Topology

noncomputable section

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

namespace Manifold

section Finiteness

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- Two points at finite Riemannian distance are joined by a path: a `C¹` path witnessing any
strict upper bound on the distance is in particular continuous. -/
theorem joined_of_riemannianEDist_lt_top {x y : M} (h : riemannianEDist I x y < ⊤) :
    Joined x y := by
  obtain ⟨γ, hγ0, hγ1, hγ, -⟩ := exists_lt_of_riemannianEDist_lt h
  exact (JoinedIn.ofLine (F := univ) hγ.continuousOn hγ0 hγ1 (subset_univ _)).joined

/-- The Riemannian extended distance is bounded below by any bound that is valid for the lengths
of *all* `C¹` curves joining the two points: it is the infimum of those lengths. -/
theorem le_riemannianEDist_of_forall_le_pathELength {x y : M} {c : ℝ≥0∞}
    (h : ∀ γ : ℝ → M, γ 0 = x → γ 1 = y → CMDiff[Icc 0 1] 1 γ →
      c ≤ pathELength I γ 0 1) :
    c ≤ riemannianEDist I x y := by
  by_contra hle
  rw [not_le] at hle
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hle
  obtain ⟨γ, h0, h1, hγ, hl⟩ := exists_lt_of_riemannianEDist_lt hr1
  exact absurd ((h γ h0 h1 hγ).trans hl.le) (not_le.2 hr2)

section Comparison

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- A `C¹` map whose differential is bounded by a positive constant increases Riemannian
extended distances by at most that factor. Positivity allows infinitely distant components. -/
theorem riemannianEDist_le_mul {f : M → N} (hf : ContMDiff I J 1 f) {C : ℝ≥0}
    (hC0 : C ≠ 0) (hC : ∀ x (v : TangentSpace I x), ‖mfderiv I J f x v‖ ≤ C * ‖v‖)
    (x y : M) : riemannianEDist J (f x) (f y) ≤ C * riemannianEDist I x y := by
  rw [← ENNReal.div_le_iff' (ENNReal.coe_ne_zero.2 hC0) ENNReal.coe_ne_top]
  refine le_riemannianEDist_of_forall_le_pathELength fun γ h0 h1 hγ ↦ ?_
  rw [ENNReal.div_le_iff' (ENNReal.coe_ne_zero.2 hC0) ENNReal.coe_ne_top]
  refine (riemannianEDist_le_pathELength (hf.comp_contMDiffOn hγ)
    (congrArg f h0) (congrArg f h1) zero_le_one).trans ?_
  rw [pathELength_eq_lintegral_mfderiv_Ioo, pathELength_eq_lintegral_mfderiv_Ioo,
    ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine MeasureTheory.setLIntegral_mono' measurableSet_Ioo fun t ht ↦ ?_
  have hdiff := (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  rw [mfderiv_comp t ((hf _).mdifferentiableAt one_ne_zero) hdiff, ContinuousLinearMap.comp_apply,
    ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (hC _ _)

/-- A map from a normed space whose differential stretches every vector by at least the factor
`c` at the points of a `C¹` curve `y` maps it to a curve whose Riemannian length is at least `c`
times the displacement of `y`. -/
theorem ofReal_mul_eNorm_sub_le_pathELength_comp {φ : F → M} {y : ℝ → F} {a b c : ℝ}
    (hab : a ≤ b) (hy : ContDiffOn ℝ 1 y (Icc a b))
    (hφ : ∀ s ∈ Icc a b, MDifferentiableAt 𝓘(ℝ, F) I φ (y s))
    (hc : ∀ s ∈ Icc a b, ∀ v : F, c * ‖v‖ ≤ ‖mfderiv 𝓘(ℝ, F) I φ (y s) v‖) :
    ENNReal.ofReal c * ‖y b - y a‖ₑ ≤ pathELength I (φ ∘ y) a b := by
  rcases hab.eq_or_lt with rfl | hab'
  · simp
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  refine (mul_le_mul_right (eNorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hy hab)
    _).trans ?_
  rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine MeasureTheory.setLIntegral_mono' measurableSet_Icc fun s hs ↦ ?_
  -- The velocity of `φ ∘ y` is the image of the velocity of `y` under the differential of `φ`.
  have hv : mfderivWithin 𝓘(ℝ, ℝ) I (φ ∘ y) (Icc a b) s 1 =
      curveVelocityWithin I (φ ∘ y) (Icc a b) s :=
    curveVelocityWithin_apply.symm
  rw [hv, curveVelocityWithin_map (hφ s hs) (uniqueDiffOn_Icc hab' s hs)
      (hy.differentiableOn one_ne_zero s hs).mdifferentiableWithinAt,
    curveVelocityWithin_eq_derivWithin, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul' (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hc s hs _)

end Comparison

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I) in
/-- Open Riemannian balls are open: any point close enough to a point `y` at Riemannian distance
less than `r` from `x` is again at distance less than `r` from `x`, by the triangle inequality. In
particular, with `r = ⊤`, the set of points at finite Riemannian distance from `x` is open. -/
theorem isOpen_setOfPred_riemannianEDist_lt (x : M) (r : ℝ≥0∞) :
    IsOpen {y | riemannianEDist I x y < r} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨δ, hδ, hδr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hy
  filter_upwards [eventually_riemannianEDist_lt I y (ENNReal.coe_pos.2 hδ)] with z hz
  exact (riemannianEDist_triangle (y := y)).trans_lt
    ((ENNReal.add_lt_add_left (ne_top_of_lt hy) hz).trans hδr)

variable (I) in
/-- The set of points at finite Riemannian distance from `x` is closed: if `y` is at infinite
Riemannian distance from `x`, then so is any point close enough to `y`, again by the triangle
inequality. -/
theorem isClosed_setOfPred_riemannianEDist_lt_top (x : M) :
    IsClosed {y | riemannianEDist I x y < ⊤} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  filter_upwards [eventually_riemannianEDist_lt I y zero_lt_one] with z hz hz'
  refine hy ((riemannianEDist_triangle (y := z)).trans_lt (ENNReal.add_lt_top.2 ⟨hz', ?_⟩))
  rw [riemannianEDist_comm]
  exact hz.trans_le le_top

variable (I) in
/-- The set of points at finite Riemannian distance from `x` is clopen. -/
theorem isClopen_setOfPred_riemannianEDist_lt_top (x : M) :
    IsClopen {y | riemannianEDist I x y < ⊤} :=
  ⟨isClosed_setOfPred_riemannianEDist_lt_top I x, isOpen_setOfPred_riemannianEDist_lt I x ⊤⟩

variable (I) in
/-- Two points of a preconnected set are at finite Riemannian distance. -/
theorem riemannianEDist_lt_top_of_isPreconnected {s : Set M} (hs : IsPreconnected s) {x y : M}
    (hx : x ∈ s) (hy : y ∈ s) : riemannianEDist I x y < ⊤ :=
  hs.subset_isClopen (isClopen_setOfPred_riemannianEDist_lt_top I x)
    ⟨x, hx, by simp [riemannianEDist_self]⟩ hy

variable (I) in
/-- The Riemannian distance from `x` to `y` is finite exactly when `y` lies in the connected
component of `x`. -/
theorem riemannianEDist_lt_top_iff_mem_connectedComponent {x y : M} :
    riemannianEDist I x y < ⊤ ↔ y ∈ connectedComponent x :=
  ⟨fun h ↦ pathComponent_subset_component x (joined_of_riemannianEDist_lt_top h),
    riemannianEDist_lt_top_of_isPreconnected I isPreconnected_connectedComponent
      mem_connectedComponent⟩

variable (I) in
/-- On a preconnected manifold, the Riemannian distance between any two points is finite. -/
theorem riemannianEDist_lt_top [PreconnectedSpace M] (x y : M) : riemannianEDist I x y < ⊤ :=
  riemannianEDist_lt_top_of_isPreconnected I isPreconnected_univ (mem_univ x) (mem_univ y)

variable (I) in
/-- On a preconnected manifold, the Riemannian distance between any two points is finite. This is
the hypothesis needed to turn `EMetricSpace.ofRiemannianMetric` into a genuine metric space. -/
@[aesop (rule_sets := [finiteness]) safe apply, simp]
theorem riemannianEDist_ne_top [PreconnectedSpace M] (x y : M) : riemannianEDist I x y ≠ ⊤ :=
  (riemannianEDist_lt_top I x y).ne

end Finiteness

section TailLength

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {p : M}

open Filter

/-- **The distance from a point of a convergent curve to its limit is at most the length of the
rest of the curve.** If `γ` is `C¹` on `[t, ∞)` and converges to `p`, and every piece of `γ`
starting at time `t` has Riemannian length at most `L`, then `γ t` is at Riemannian distance at
most `L` from `p`. -/
theorem riemannianEDist_le_of_tendsto_of_forall_pathELength_le {t : ℝ} {L : ℝ≥0∞}
    (hγ : CMDiff[Ici t] 1 γ) (hp : Tendsto γ atTop (𝓝 p))
    (hL : ∀ s, pathELength I γ t s ≤ L) : riemannianEDist I (γ t) p ≤ L := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  -- Compare with a later point `γ s` which is `ε`-close to `p`.
  obtain ⟨s, hs, hts⟩ := ((hp.eventually (eventually_riemannianEDist_lt I p
    (c := ε) (by exact_mod_cast hε))).and (eventually_ge_atTop t)).exists
  calc riemannianEDist I (γ t) p
      ≤ riemannianEDist I (γ t) (γ s) + riemannianEDist I (γ s) p := riemannianEDist_triangle
    _ ≤ pathELength I γ t s + ε := by
        gcongr
        · exact riemannianEDist_le_pathELength (hγ.mono Icc_subset_Ici_self) rfl rfl hts
        · rw [riemannianEDist_comm]
          exact hs.le
    _ ≤ L + ε := by gcongr; exact hL s

/-- **A curve whose tail lengths tend to zero converges to each of its cluster points.** If `γ`
is `C¹` on `[a, ∞)`, the Riemannian lengths of its pieces starting at time `t` tend to zero as
`t → ∞`, and `p` is a cluster point of `γ t` as `t → ∞`, then `γ` converges to `p`. In particular
a curve of finite length on `[a, ∞)` in a compact manifold converges. -/
theorem tendsto_of_mapClusterPt_of_forall_pathELength_le [RegularSpace M] {a : ℝ}
    (hγ : CMDiff[Ici a] 1 γ) (hp : MapClusterPt p atTop γ)
    (hlen : ∀ ε > 0, ∀ᶠ t in atTop, ∀ s, pathELength I γ t s ≤ ε) :
    Tendsto γ atTop (𝓝 p) := by
  intro U hU
  -- Points at Riemannian distance less than `c` from `p` lie in `U`.
  obtain ⟨c, hc, hcU⟩ := setOfPred_riemannianEDist_lt_subset_nhds I hU
  have hc2 : (0 : ℝ≥0∞) < (c : ℝ≥0∞) / 2 :=
    ENNReal.half_pos (by exact_mod_cast hc.ne')
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((hlen _ hc2).and (eventually_ge_atTop a))
  -- Some time `u ≥ T` brings `γ` within `c / 2` of `p`; afterwards `γ` moves by at most `c / 2`.
  obtain ⟨u, hu, huT⟩ := ((hp.frequently (eventually_riemannianEDist_lt I p hc2)).and_eventually
    (eventually_ge_atTop T)).exists
  refine mem_map.2 (mem_atTop_sets.2 ⟨T, fun t ht ↦ hcU ?_⟩)
  have hut : riemannianEDist I (γ u) (γ t) ≤ c / 2 := by
    rcases le_total u t with h | h
    · exact (riemannianEDist_le_pathELength (hγ.mono fun r hr ↦ (hT u huT).2.trans hr.1) rfl rfl
        h).trans ((hT u huT).1 t)
    · rw [riemannianEDist_comm]
      exact (riemannianEDist_le_pathELength (hγ.mono fun r hr ↦ (hT t ht).2.trans hr.1) rfl rfl
        h).trans ((hT t ht).1 u)
  calc riemannianEDist I p (γ t)
      ≤ riemannianEDist I p (γ u) + riemannianEDist I (γ u) (γ t) := riemannianEDist_triangle
    _ < c / 2 + c / 2 :=
        ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top (by finiteness) hut) hu hut
    _ = c := ENNReal.add_halves _

end TailLength

end Manifold

namespace IsRiemannianManifold

section PseudoEMetric

variable {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

/-- In a Riemannian manifold, the ambient extended distance between the endpoints of a `C¹` path
is at most the length of that path. This is `Manifold.riemannianEDist_le_pathELength` read through
`IsRiemannianManifold.out`. -/
theorem edist_le_pathELength {γ : ℝ → M} {a b : ℝ} (hγ : CMDiff[Icc a b] 1 γ) (hab : a ≤ b) :
    edist (γ a) (γ b) ≤ pathELength I γ a b := by
  rw [IsRiemannianManifold.out (I := I) (γ a) (γ b)]
  exact riemannianEDist_le_pathELength hγ rfl rfl hab

/-- **The mean-value inequality for maps into a Riemannian manifold.** Let `f` be a map from a real
normed space to a Riemannian manifold which is `C¹` at every point of the segment from `a` to `b`.
If its differential along that segment sends `b - a` to vectors of norm at most `C`, then `f a` and
`f b` are at extended distance at most `C`. -/
theorem edist_le_of_norm_mfderiv_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → M} {a b : F} {C : ℝ}
    (hf : ∀ z ∈ segment ℝ a b, ContMDiffAt 𝓘(ℝ, F) I 1 f z)
    (hC : ∀ z ∈ segment ℝ a b, ‖mfderiv 𝓘(ℝ, F) I f z (b - a)‖ ≤ C) :
    edist (f a) (f b) ≤ ENNReal.ofReal C := by
  let c : ℝ → F := fun τ ↦ a + τ • (b - a)
  have hcseg : MapsTo c (Icc 0 1) (segment ℝ a b) := fun τ hτ ↦ by
    rw [segment_eq_image']
    exact ⟨τ, hτ, rfl⟩
  have hcderiv : ∀ τ, HasDerivAt c (b - a) τ := fun τ ↦
    (((hasDerivAt_id' τ).smul_const (b - a)).const_add a).congr_deriv (one_smul ℝ _)
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 c := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  have hsmooth : CMDiff[Icc 0 1] 1 (f ∘ c) := fun τ hτ ↦
    (hf _ (hcseg hτ)).comp_contMDiffWithinAt τ hc.contMDiffAt.contMDiffWithinAt
  have hlen := edist_le_pathELength hsmooth zero_le_one
  have h0 : c 0 = a := by simp [c]
  have h1 : c 1 = b := by simp [c]
  simp only [Function.comp_apply, h0, h1] at hlen
  calc
    edist (f a) (f b) ≤ pathELength I (f ∘ c) 0 1 := hlen
    _ = ∫⁻ τ in Ioo 0 1, ‖mfderiv 𝓘(ℝ, ℝ) I (f ∘ c) τ (1 : ℝ)‖ₑ :=
      pathELength_eq_lintegral_mfderiv_Ioo
    _ ≤ ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal C := by
      refine MeasureTheory.setLIntegral_mono' measurableSet_Ioo fun τ hτ ↦ ?_
      have hτ' : c τ ∈ segment ℝ a b := hcseg (Ioo_subset_Icc_self hτ)
      rw [← Manifold.curveVelocity_apply,
        ((hf _ hτ').mdifferentiableAt one_ne_zero).curveVelocity_comp_mfderiv (hcderiv τ),
        ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hC _ hτ')
    _ = ENNReal.ofReal C := by simp

/-- A curve that is `C¹` at every point of an interval `s` and whose Riemannian speed is at most
`K` on `s` is `K`-Lipschitz on `s` for the ambient extended distance. -/
theorem lipschitzOnWith_of_norm_curveVelocity_le {γ : ℝ → M} {s : Set ℝ} {K : ℝ≥0}
    (hs : OrdConnected s) (hγ : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ) I 1 γ t)
    (hK : ∀ t ∈ s, ‖Manifold.curveVelocity I γ t‖ ≤ K) :
    LipschitzOnWith K γ s := by
  intro u hu v hv
  have hsub : segment ℝ u v ⊆ s := by
    rw [segment_eq_uIcc]
    exact hs.uIcc_subset hu hv
  calc edist (γ u) (γ v) ≤ ENNReal.ofReal (K * dist u v) := by
        refine edist_le_of_norm_mfderiv_le (fun z hz ↦ hγ z (hsub hz)) fun z hz ↦ ?_
        -- `L` is the differential retyped with source `ℝ` instead of `TangentSpace 𝓘(ℝ) z`, which
        -- unfolds to `ℝ`; this lets real scalars act on its arguments.
        let L : ℝ →L[ℝ] TangentSpace I (γ z) := mfderiv 𝓘(ℝ) I γ z
        have hL : L (v - u) = (v - u) • Manifold.curveVelocity I γ z := by
          have h := L.map_smul (v - u) (1 : ℝ)
          rw [smul_eq_mul, mul_one] at h
          rwa [Manifold.curveVelocity_apply]
        -- Restate the goal through the `let`-bound `L`, so that `hL` can rewrite it.
        change ‖L (v - u)‖ ≤ K * dist u v
        rw [hL, norm_smul, Real.norm_eq_abs, ← Real.dist_eq, dist_comm, mul_comm]
        exact mul_le_mul_of_nonneg_right (hK z (hsub hz)) dist_nonneg
    _ = K * edist u v := by
        rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal, edist_dist]

/-- A `C¹` map between Riemannian manifolds with differential bounded by a positive constant
is Lipschitz with that constant. -/
theorem lipschitzWith_of_norm_mfderiv_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    {N : Type*} [PseudoEMetricSpace N] [ChartedSpace K N]
    [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]
    {f : M → N} (hf : ContMDiff I J 1 f) {C : ℝ≥0} (hC0 : C ≠ 0)
    (hC : ∀ x (v : TangentSpace I x), ‖mfderiv I J f x v‖ ≤ C * ‖v‖) :
    LipschitzWith C f := by
  intro x y
  rw [IsRiemannianManifold.out (I := J), IsRiemannianManifold.out (I := I)]
  exact Manifold.riemannianEDist_le_mul hf hC0 hC x y

section LocalLipschitz

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A map from a real normed space into a manifold with a continuous Riemannian
metric is Lipschitz, for the ambient extended distance, on a ball around each point at which it is
`C¹`. -/
theorem exists_lipschitzOnWith_of_contMDiffAt {f : F → M} {x : F}
    (hf : ContMDiffAt 𝓘(ℝ, F) I 1 f x) :
    ∃ r > 0, ∃ C : ℝ≥0, LipschitzOnWith C f (Metric.ball x r) := by
  set U := {y | ContMDiffAt 𝓘(ℝ, F) I 1 f y}
  have hU : IsOpen U := TauCeti.isOpen_setOfPred_contMDiffAt (by simp)
  have hUx : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hf
  have hcont := ContMDiffOn.continuousOn_norm_mfderiv_apply
    (fun y (hy : y ∈ U) ↦ hy.contMDiffWithinAt) le_rfl hU
  -- `L y` is the differential retyped with source `F` instead of `TangentSpace 𝓘(ℝ, F) y`, which
  -- unfolds to `F`; this gives it an operator norm.
  let L (y : F) : F →L[ℝ] TangentSpace I (f y) := mfderiv 𝓘(ℝ, F) I f y
  have hL0 : ‖L x 0‖ < 1 := by
    rw [map_zero, norm_zero]
    exact one_pos
  -- Joint continuity at `(x, 0)` gives `‖L y w‖ < 1` for `y` near `x` and `‖w‖ < δ`.
  have hsmall : ∀ᶠ p : F × F in 𝓝 x ×ˢ 𝓝 0, ‖L p.1 p.2‖ < 1 := by
    rw [← nhds_prod_eq]
    exact (hcont.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hf, mem_univ 0⟩)).eventually
      (gt_mem_nhds hL0)
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := Filter.eventually_prod_iff.1 hsmall
  obtain ⟨δ, hδ, hδQ⟩ := Metric.eventually_nhds_iff_ball.1 hQ
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, (C : ℝ) = 2 / δ := ⟨⟨2 / δ, by positivity⟩, rfl⟩
  -- Rescaling vectors of norm in `[δ / 2, δ)` bounds the operator norm by `2 / δ`.
  have hbound : ∀ᶠ y in 𝓝 x, ‖L y‖ ≤ C :=
    hP.mono fun y hy ↦ ContinuousLinearMap.opNorm_le_of_shell (c := (2 : ℝ)) hδ C.coe_nonneg
      (by norm_num) fun w hw₁ hw₂ ↦ by
        rw [Real.norm_ofNat] at hw₁
        refine (hPQ hy (hδQ w (mem_ball_zero_iff.2 hw₂))).le.trans ?_
        calc (1 : ℝ) = 2 / δ * (δ / 2) := by field_simp
          _ ≤ C * ‖w‖ := by rw [hC]; gcongr
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hUx.and hbound)
  refine ⟨r, hr, C, fun a ha b hb ↦ ?_⟩
  have hseg := (convex_ball x r).segment_subset ha hb
  calc edist (f a) (f b) ≤ ENNReal.ofReal (C * ‖b - a‖) :=
        edist_le_of_norm_mfderiv_le (fun z hz ↦ (hball _ (hseg hz)).1) fun z hz ↦
          (L z).le_of_opNorm_le (hball _ (hseg hz)).2 _
    _ = C * edist a b := by
        rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, edist_dist, dist_eq_norm,
          norm_sub_rev]

end LocalLipschitz

end PseudoEMetric

section PseudoMetric

variable {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

variable (I) in
/-- In a Riemannian manifold whose ambient distance is an ordinary one, that distance is the real
part of the Riemannian extended distance. -/
theorem dist_eq_toReal_riemannianEDist (x y : M) : dist x y = (riemannianEDist I x y).toReal := by
  rw [dist_edist, IsRiemannianManifold.out (I := I) x y]

variable (I) in
/-- In a Riemannian manifold whose ambient distance is an ordinary one, the distance is bounded
above by the length of any `C¹` path of finite length between the two points. -/
theorem dist_le_toReal_pathELength {γ : ℝ → M} {a b : ℝ} {x y : M} (hγ : CMDiff[Icc a b] 1 γ)
    (ha : γ a = x) (hb : γ b = y) (hab : a ≤ b) (h : pathELength I γ a b ≠ ⊤) :
    dist x y ≤ (pathELength I γ a b).toReal := by
  subst ha hb
  rw [dist_edist]
  exact ENNReal.toReal_mono h (edist_le_pathELength hγ hab)

variable (I) in
/-- In a Riemannian manifold whose ambient distance is an ordinary one, any bound `r` on the
distance from `x` to `y` is witnessed by a `C¹` path on `[0, 1]` of length `< ENNReal.ofReal r`. -/
theorem exists_pathELength_lt_of_dist_lt {x y : M} {r : ℝ} (hr : dist x y < r) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ CMDiff[Icc 0 1] 1 γ ∧
      pathELength I γ 0 1 < ENNReal.ofReal r := by
  apply exists_lt_of_riemannianEDist_lt
  rw [← IsRiemannianManifold.out (I := I) x y, edist_dist]
  exact (ENNReal.ofReal_lt_ofReal_iff (dist_nonneg.trans_lt hr)).2 hr

section LocalLipschitz

variable [I.Boundaryless] [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **The inverse chart is Lipschitz on compact sets.** On a boundaryless manifold with a
continuous Riemannian metric, the inverse of the extended chart at `x` is Lipschitz, from the norm
distance of the model space to the ambient distance, on every compact subset of the chart
target. -/
theorem exists_lipschitzOnWith_extChartAt_symm_of_isCompact (x : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I x).target) :
    ∃ C : ℝ≥0, LipschitzOnWith C (extChartAt I x).symm K := by
  refine LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK fun z hz ↦ ?_
  have hsmooth : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I x).symm z :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (hKt hz))
  obtain ⟨r, hr, C, hC⟩ := exists_lipschitzOnWith_of_contMDiffAt hsmooth
  exact ⟨C, Metric.ball z r, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hr), hC⟩

end LocalLipschitz

end PseudoMetric

end IsRiemannianManifold

namespace Manifold

section BallContainment

variable {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

/-- A `C¹` path starting at `p` whose length is less than `s` stays in the open ball `B(p, s)`. -/
theorem mem_ball_of_pathELength_lt {γ : ℝ → M} {p : M} {s : ℝ} (hγ : CMDiff[Icc 0 1] 1 γ)
    (hγ0 : γ 0 = p) (hlen : pathELength I γ 0 1 < ENNReal.ofReal s) {t : ℝ} (ht : t ∈ Icc 0 1) :
    γ t ∈ Metric.ball p s := by
  have hle : pathELength I γ 0 t ≤ pathELength I γ 0 1 := pathELength_mono le_rfl ht.2
  have hlt : pathELength I γ 0 t < ENNReal.ofReal s := hle.trans_lt hlen
  have hd := TauCeti.IsRiemannianManifold.dist_le_toReal_pathELength (I := I)
    (hγ.mono (Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1 hlt.ne_top
  rw [Metric.mem_ball, dist_comm]
  refine hd.trans_lt ?_
  have hs : 0 < s := by
    by_contra h
    simp [ENNReal.ofReal_eq_zero.2 (not_lt.1 h)] at hlt
  exact (ENNReal.toReal_lt_toReal hlt.ne_top ENNReal.ofReal_ne_top).2 hlt |>.trans_eq
    (ENNReal.toReal_ofReal hs.le)

end BallContainment

end Manifold

section OfRiemannianMetric

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- The pseudometric space structure associated to a Riemannian metric on a preconnected manifold,
obtained from `PseudoEMetricSpace.ofRiemannianMetric` now that the extended distance is known to be
finite. As for the extended version, the topology is defeq to the original one.

This should only be used when constructing data in specific situations. To develop the theory, one
should rather assume that there is an already existing pseudometric space structure, satisfying
additionally the predicate `IsRiemannianManifold I M`. -/
@[reducible] def PseudoMetricSpace.ofRiemannianMetric [RegularSpace M] [PreconnectedSpace M] :
    PseudoMetricSpace M :=
  letI : PseudoEMetricSpace M := .ofRiemannianMetric I M
  PseudoEMetricSpace.toPseudoMetricSpace (fun x y ↦ Manifold.riemannianEDist_ne_top I x y)

/-- The distance of `PseudoMetricSpace.ofRiemannianMetric` is the infimum of the lengths of `C¹`
paths, i.e. the resulting pseudometric space satisfies the `IsRiemannianManifold I M` predicate. -/
instance [RegularSpace M] [PreconnectedSpace M] :
    letI : PseudoMetricSpace M := PseudoMetricSpace.ofRiemannianMetric I M
    IsRiemannianManifold I M := by
  let : PseudoMetricSpace M := PseudoMetricSpace.ofRiemannianMetric I M
  -- `PseudoEMetricSpace.toPseudoMetricSpace` is set up so that the extended distance is preserved
  -- definitionally (its `edist` field is literally `edist`), and the extended distance of
  -- `PseudoEMetricSpace.ofRiemannianMetric` is `riemannianEDist I` by construction. So the
  -- predicate holds by `rfl`, exactly as for the extended structure it refines.
  exact ⟨fun _ _ ↦ rfl⟩

variable (I M) in
/-- The metric space structure associated to a Riemannian metric on a preconnected manifold,
obtained from `EMetricSpace.ofRiemannianMetric` now that the extended distance is known to be
finite. As for the extended version, the topology is defeq to the original one.

This should only be used when constructing data in specific situations. To develop the theory, one
should rather assume that there is an already existing metric space structure, satisfying
additionally the predicate `IsRiemannianManifold I M`. -/
-- The body is exposed because the characteristic property of the construction, that the topology
-- it induces is the manifold topology, is a definitional equality: a consumer installing this
-- structure on a manifold must unfold it to keep the charted-space instances of that topology.
@[expose, reducible] def MetricSpace.ofRiemannianMetric [T3Space M] [PreconnectedSpace M] :
    MetricSpace M :=
  letI : EMetricSpace M := .ofRiemannianMetric I M
  EMetricSpace.toMetricSpace (fun x y ↦ Manifold.riemannianEDist_ne_top I x y)

/-- The distance of `MetricSpace.ofRiemannianMetric` is the infimum of the lengths of `C¹` paths,
i.e. the resulting metric space satisfies the `IsRiemannianManifold I M` predicate. -/
instance [T3Space M] [PreconnectedSpace M] :
    letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
    IsRiemannianManifold I M := by
  let : MetricSpace M := MetricSpace.ofRiemannianMetric I M
  -- As above: `EMetricSpace.toMetricSpace` preserves the extended distance definitionally, and the
  -- extended distance of `EMetricSpace.ofRiemannianMetric` is `riemannianEDist I` by construction.
  exact ⟨fun _ _ ↦ rfl⟩

end OfRiemannianMetric

section OfRiemannianMetricEq

variable (I) in
/-- When the ambient pseudometric space on a preconnected Riemannian manifold already has distance
given by `riemannianEDist`, `PseudoMetricSpace.ofRiemannianMetric` recovers that ambient
`PseudoMetricSpace` structure. -/
theorem PseudoMetricSpace.ofRiemannianMetric_eq (M : Type*) [hM : PseudoMetricSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [PreconnectedSpace M]
    [IsRiemannianManifold I M] :
    PseudoMetricSpace.ofRiemannianMetric I M = hM := by
  ext x y
  exact (IsRiemannianManifold.dist_eq_toReal_riemannianEDist I x y).symm

variable (I) in
/-- When the ambient metric space on a preconnected Riemannian manifold already has distance given
by `riemannianEDist`, `MetricSpace.ofRiemannianMetric` recovers that ambient `MetricSpace`
structure. -/
theorem MetricSpace.ofRiemannianMetric_eq (M : Type*) [hM : MetricSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [PreconnectedSpace M]
    [IsRiemannianManifold I M] :
    MetricSpace.ofRiemannianMetric I M = hM := by
  ext x y
  exact (IsRiemannianManifold.dist_eq_toReal_riemannianEDist I x y).symm

variable (I) in
/-- When a complete metric space on a preconnected Riemannian manifold has distance given by
`riemannianEDist`, the metric space `MetricSpace.ofRiemannianMetric I M` is also complete. -/
theorem MetricSpace.completeSpace_ofRiemannianMetric (M : Type*) [MetricSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [PreconnectedSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M] :
    @CompleteSpace M (MetricSpace.ofRiemannianMetric I M).toUniformSpace := by
  rw [MetricSpace.ofRiemannianMetric_eq I M]
  infer_instance

end OfRiemannianMetricEq

end TauCeti
