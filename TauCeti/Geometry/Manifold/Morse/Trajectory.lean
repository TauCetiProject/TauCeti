/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.ExponentialConvergence
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Distance

/-!
# Convergence of prescribed forward gradient trajectories

The maximal negative-gradient flow estimates also apply to any prescribed integral curve on
`[0, ∞)`. A compact trap with finitely many critical points forces convergence to a critical point
in that trap. In particular this applies to Morse functions, without compactness of the ambient
manifold, and to proper bounded-below Morse functions without a separately supplied trap.

If a forward curve converges to a nondegenerate critical point, its Riemannian extended distance
`Manifold.riemannianEDist I` to that point is bounded by `C * exp (-c * t)` for every `t ≥ 0`. This
is the intrinsic distance of the metric on the tangent bundle, so no metric space structure on `M`
is assumed; it induces the topology of `M` (`PseudoEMetricSpace.ofRiemannianMetric`), so it is
continuous along the curve. The existing eventual estimate
`TauCeti.exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient` supplies the tail
bound, and `TauCeti.exists_tendsto_maximalIntegralCurve_neg_mgradient` supplies compact-trap
convergence. Continuity on the initial compact time interval absorbs that interval into `C`.
No adapted metric or positivity of the Hessian is required, so a trajectory may converge to a
saddle. For Morse functions, convergence alone supplies the nondegenerate critical point:
`IsMIntegralCurveOn.mem_criticalPoints_of_tendsto_neg_mgradient` proves criticality of the limit,
and `TauCeti.IsMorse.exists_riemannianEDist_le_mul_exp_of_tendsto_neg_mgradient` gives the distance
bound.

The comparison with the maximal curve moves the time origin to time `1`, which lies in the
interior of the prescribed curve's domain. It therefore does not require a two-sided derivative
of the prescribed curve at its initial endpoint.

The trajectories split into equilibria and the rest. Uniqueness of integral curves also holds from
the endpoint `0` (`IsMIntegralCurveOn.apply_eq_of_eq_zero`), so a forward curve that meets a
critical point at some time `t₀ ≥ 0` is constant on `[0, ∞)`
(`IsMIntegralCurveOn.apply_eq_of_mem_criticalPoints_neg_mgradient`). Its energy and its tail length
(`IsMIntegralCurveOn.pathELength_eq_zero_of_mem_criticalPoints_neg_mgradient`) vanish, and the
exponential distance bound holds with the constant `0`. Any other forward curve meets no critical
point, so `f` strictly decreases along it (`IsMIntegralCurveOn.strictAntiOn_comp_neg_mgradient`).
If such a curve converges to `p`, then at every time `t ≥ 0` its energy `f (γ t) - f p` and its
Riemannian distance to `p` are both positive
(`IsMIntegralCurveOn.forall_eq_or_forall_pos_of_tendsto_neg_mgradient`). An estimate by a power
of the energy may therefore divide by the energy only off the equilibria.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.1.6 and Chapter 2.
-/

public section

open Bundle Filter Function Set Topology TauCeti TauCeti.Manifold
open scoped ContDiff Manifold

section Topological

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 2 M] [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {γ : ℝ → M} {K : Set M} {p : M}

/-- A prescribed forward negative-gradient curve trapped in a compact set containing only
finitely many critical points converges to a critical point in that set. -/
theorem IsMIntegralCurveOn.exists_tendsto_neg_mgradient
    (hγ : IsMIntegralCurveOn γ (-mgradient I f) (Ici 0)) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hK : IsCompact K) (hmem : MapsTo γ (Ici 0) K)
    (hfin : (criticalPoints I f ∩ K).Finite) :
    ∃ p ∈ criticalPoints I f ∩ K, Tendsto γ atTop (𝓝 p) := by
  have hmaps := hγ.mapsTo_maximalIntegralCurve_Ici (contMDiff_neg_mgradient_one hf)
    (by norm_num : (0 : ℝ) < 1) hmem
  obtain ⟨p, hp, hlim⟩ := exists_tendsto_maximalIntegralCurve_neg_mgradient hK
    (hmaps.mono_left inter_subset_right) hf hfin
  exact ⟨p, hp, (hγ.tendsto_maximalIntegralCurve_iff
    (contMDiff_neg_mgradient_one hf) (by norm_num : (0 : ℝ) < 1)).1 hlim⟩

/-- The limit of a convergent prescribed forward negative-gradient curve is critical. No
compact trap is required as an input: the forward image together with its limit is compact. -/
theorem IsMIntegralCurveOn.mem_criticalPoints_of_tendsto_neg_mgradient
    (hγ : IsMIntegralCurveOn γ (-mgradient I f) (Ici 0)) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hconv : Tendsto γ atTop (𝓝 p)) : p ∈ criticalPoints I f := by
  let : Inhabited (Ici (0 : ℝ)) := ⟨0, le_rfl⟩
  have hlim : Tendsto (fun t : Ici (0 : ℝ) ↦ γ t) (cocompact (Ici (0 : ℝ))) (𝓝 p) := by
    rw [cocompact_eq_atTop]
    exact tendsto_comp_val_Ici_atTop.mpr hconv
  have hK : IsCompact (insert p (γ '' Ici 0)) := by
    simpa only [image_eq_range] using
      hlim.isCompact_insert_range_of_cocompact hγ.continuousOn.domRestrict
  have hmaps := hγ.mapsTo_maximalIntegralCurve_Ici (contMDiff_neg_mgradient_one hf)
    (by norm_num : (0 : ℝ) < 1) (fun t ht ↦ mem_insert_of_mem p (mem_image_of_mem γ ht))
  exact mem_criticalPoints_of_mapClusterPt_maximalIntegralCurve_neg_mgradient hK
    (hmaps.mono_left inter_subset_right) hf
    ((hγ.tendsto_maximalIntegralCurve_iff
      (contMDiff_neg_mgradient_one hf) (by norm_num : (0 : ℝ) < 1)).2 hconv).mapClusterPt

namespace TauCeti

/-- A forward trajectory of a Morse function trapped in a compact set converges to a critical
point belonging to that set, for an arbitrary `C¹` metric. -/
theorem IsMorse.exists_tendsto_of_isMIntegralCurveOn_neg_mgradient
    (hf : IsMorse I f) (hγ : IsMIntegralCurveOn γ (-mgradient I f) (Ici 0))
    (hK : IsCompact K) (hmem : MapsTo γ (Ici 0) K) :
    ∃ p ∈ criticalPoints I f ∩ K, Tendsto γ atTop (𝓝 p) :=
  hγ.exists_tendsto_neg_mgradient (hf.contMDiff.of_le (by norm_num)) hK hmem
    (hf.finite_criticalPoints_inter hK)

/-- Every prescribed forward trajectory of a proper bounded-below Morse function converges to a
critical point. Neither compactness of the manifold nor completeness of the metric is needed. -/
theorem IsMorse.exists_tendsto_of_isMIntegralCurveOn_neg_mgradient_of_isProperMap
    (hf : IsMorse I f) (hγ : IsMIntegralCurveOn γ (-mgradient I f) (Ici 0))
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) :
    ∃ p ∈ criticalPoints I f, Tendsto γ atTop (𝓝 p) := by
  have hf2 : ContMDiff I 𝓘(ℝ) 2 f := hf.contMDiff.of_le (by norm_num)
  obtain ⟨p, hp, hlim⟩ := hf.exists_tendsto_maximalIntegralCurve_neg_mgradient hp hbdd (γ 1)
  exact ⟨p, hp, (hγ.tendsto_maximalIntegralCurve_iff
    (contMDiff_neg_mgradient_one hf2) (by norm_num : (0 : ℝ) < 1)).1 hlim⟩

end TauCeti

end Topological

section Distance

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 2 M] [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {γ : ℝ → M} {p : M}

/-- Transfer the eventual maximal-flow estimate to a prescribed forward curve. -/
private theorem eventually_riemannianEDist_neg_mgradient
    (hγ : IsMIntegralCurveOn γ (-mgradient I f) (Ici 0)) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hp : IsManifoldNondegenerateCriticalPoint I f p) (hconv : Tendsto γ atTop (𝓝 p)) :
    ∃ c > 0, ∃ C > 0, ∀ᶠ t in atTop,
      Manifold.riemannianEDist I (γ t) p ≤ ENNReal.ofReal (C * Real.exp (-(c * t))) := by
  have heq := hγ.eqOn_maximalIntegralCurve_Ici
    (contMDiff_neg_mgradient_one hf) (b := 1) (by norm_num)
  have hlim := (hγ.tendsto_maximalIntegralCurve_iff
    (contMDiff_neg_mgradient_one hf) (by norm_num : (0 : ℝ) < 1)).2 hconv
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  obtain ⟨c, hc, C, hC, hbound⟩ :=
    exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient hp.mem_criticalPoints
      hp.exists_mul_abs_sub_le_norm_mgradient_sq hlim hf
  refine ⟨c, hc, C * Real.exp c, by positivity, ?_⟩
  filter_upwards [(tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id).eventually hbound,
    eventually_ge_atTop (1 : ℝ)] with t ht ht1
  simp only [id_eq] at ht
  have hpoint : maximalIntegralCurve (-mgradient I f) (γ 1) (t - 1) = γ t := by
    simpa only [comp_apply, sub_add_cancel] using
      heq (x := t - 1) (by simp only [mem_Ioi]; linarith)
  rwa [← sub_eq_add_neg, hpoint, exp_neg_mul_sub, mul_one, ← mul_assoc] at ht

/-- A prescribed forward negative-gradient curve converging to a nondegenerate critical point
satisfies an exponential bound on its Riemannian extended distance to that point, for every
nonnegative time and not only eventually. No metric space structure on `M` is assumed. The limit
may be a saddle. -/
theorem IsMIntegralCurveOn.exists_riemannianEDist_le_mul_exp_of_tendsto_neg_mgradient
    (hγ : IsMIntegralCurveOn γ (-mgradient I f) (Ici 0)) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hp : IsManifoldNondegenerateCriticalPoint I f p) (hconv : Tendsto γ atTop (𝓝 p)) :
    ∃ C > 0, ∃ c > 0, ∀ t ≥ 0,
      Manifold.riemannianEDist I (γ t) p ≤ ENNReal.ofReal (C * Real.exp (-(c * t))) := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  -- The Riemannian distance is the distance of a pseudo-emetric structure whose topology is that
  -- of `M` by construction, so it is continuous.
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  -- The whole trajectory and its limit lie in one connected set. Distances to the limit are
  -- finite even when the extended distance takes infinite values between components.
  have hconn := (isPreconnected_Ici.image γ hγ.continuousOn).closure
  have hpcl : p ∈ closure (γ '' Ici 0) :=
    mem_closure_of_tendsto hconv (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht using mem_image_of_mem γ ht)
  have hfin (t : ℝ) (ht : 0 ≤ t) : Manifold.riemannianEDist I (γ t) p ≠ ⊤ :=
    (riemannianEDist_lt_top_of_isPreconnected I hconn
      (subset_closure (mem_image_of_mem γ ht)) hpcl).ne
  have hcont : ContinuousOn (fun t ↦ (Manifold.riemannianEDist I (γ t) p).toReal) (Ici 0) := by
    simp_rw [← IsRiemannianManifold.out (I := I)]
    exact ENNReal.continuousOn_toReal.comp
      (continuous_edist.comp_continuousOn (hγ.continuousOn.prodMk continuousOn_const))
      fun t ht ↦ by rw [IsRiemannianManifold.out (I := I)]; exact hfin t ht
  obtain ⟨c, hc, C, _, hbound⟩ := eventually_riemannianEDist_neg_mgradient hγ hf hp hconv
  have hbound' : ∀ᶠ t in atTop,
      (Manifold.riemannianEDist I (γ t) p).toReal ≤ C * Real.exp (-(c * t)) := by
    filter_upwards [hbound] with t ht
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) ht
  obtain ⟨B, hB, hBbound⟩ := hcont.exists_forall_le_mul_exp_Ici_of_eventually_le hbound'
  exact ⟨B, hB, c, hc, fun t ht ↦ (ENNReal.le_ofReal_iff_toReal_le (hfin t ht)
    (by positivity)).2 (hBbound t ht)⟩

namespace TauCeti

/-- A convergent prescribed forward trajectory of a Morse function satisfies an exponential bound
on its Riemannian extended distance to the limit, for every nonnegative time. No compact trap,
criticality hypothesis on the limit or metric space structure on `M` needs to be supplied. -/
theorem IsMorse.exists_riemannianEDist_le_mul_exp_of_tendsto_neg_mgradient
    (hf : IsMorse I f) (hγ : IsMIntegralCurveOn γ (-mgradient I f) (Ici 0))
    (hconv : Tendsto γ atTop (𝓝 p)) :
    ∃ C > 0, ∃ c > 0, ∀ t ≥ 0,
      Manifold.riemannianEDist I (γ t) p ≤ ENNReal.ofReal (C * Real.exp (-(c * t))) := by
  have hf2 : ContMDiff I 𝓘(ℝ) 2 f := hf.contMDiff.of_le (by norm_num)
  exact hγ.exists_riemannianEDist_le_mul_exp_of_tendsto_neg_mgradient hf2
    (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (hγ.mem_criticalPoints_of_tendsto_neg_mgradient hf2 hconv)) hconv

end TauCeti

end Distance

section Equilibrium

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {γ : ℝ → M} {p : M}

/-- **A forward trajectory through a critical point is the equilibrium there.** If a prescribed
forward negative-gradient curve meets a critical point of `f` at some time `t₀ ≥ 0`, it is constant
on `[0, ∞)`. Uniqueness of integral curves holds from the endpoint `0` as well, so the curve agrees
with the constant curve at that point. -/
theorem IsMIntegralCurveOn.apply_eq_of_mem_criticalPoints_neg_mgradient
    (hγ : IsMIntegralCurveOn γ (-mgradient I f) (Ici 0)) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    {t₀ t : ℝ} (ht₀ : 0 ≤ t₀) (hcrit : γ t₀ ∈ criticalPoints I f) (ht : 0 ≤ t) : γ t = γ t₀ :=
  hγ.apply_eq_of_eq_zero isPreconnected_Ici ht₀ (contMDiff_neg_mgradient_one hf).contMDiffAt
    (by rwa [Pi.neg_apply, neg_eq_zero, mgradient_eq_zero_iff, ← mem_criticalPoints]) ht

/-- **Off the equilibria, `f` strictly decreases.** Along a prescribed forward negative-gradient
curve that does not start at a critical point, `f` strictly decreases on `[0, ∞)`: the curve meets
no critical point, so `f` has the negative derivative `-‖grad f‖²` along it. -/
theorem IsMIntegralCurveOn.strictAntiOn_comp_neg_mgradient
    (hγ : IsMIntegralCurveOn γ (-mgradient I f) (Ici 0)) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (h0 : γ 0 ∉ criticalPoints I f) : StrictAntiOn (f ∘ γ) (Ici 0) := by
  refine hγ.strictAntiOn_comp (convex_Ici 0) (fun t _ ↦ hf.mdifferentiable (by norm_num) _)
    fun t ht ↦ ?_
  have hcrit : γ t ∉ criticalPoints I f := fun h ↦ h0 <| by
    rwa [hγ.apply_eq_of_mem_criticalPoints_neg_mgradient hf (interior_subset ht) h le_rfl]
  rw [mem_criticalPoints, ← mgradient_eq_zero_iff] at hcrit
  rw [Pi.neg_apply, mvfderiv_apply_neg_mgradient, neg_lt_zero]
  positivity

/-- **The equilibrium has length zero.** A prescribed forward negative-gradient curve starting at a
critical point has Riemannian length `0` from any time `t ≥ 0` to any time `s`, so its tail length
vanishes. -/
theorem IsMIntegralCurveOn.pathELength_eq_zero_of_mem_criticalPoints_neg_mgradient
    (hγ : IsMIntegralCurveOn γ (-mgradient I f) (Ici 0)) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (h0 : γ 0 ∈ criticalPoints I f) {t s : ℝ} (ht : 0 ≤ t) :
    Manifold.pathELength I γ t s = 0 := by
  rw [Manifold.pathELength_congr (γ' := fun _ ↦ γ 0) fun u hu ↦
    hγ.apply_eq_of_mem_criticalPoints_neg_mgradient hf le_rfl h0 (ht.trans hu.1)]
  simp [Manifold.pathELength_eq_lintegral_mfderiv_Icc, mfderiv_const]

/-- **Equilibrium or positive energy.** Let a prescribed forward negative-gradient curve converge
to `p`. Either it is the equilibrium at `p`, constant on `[0, ∞)`, or at every time `t ≥ 0` both
its energy `f (γ t) - f p` and its Riemannian distance to `p` are positive. At the equilibrium the
energy, the tail length
(`IsMIntegralCurveOn.pathELength_eq_zero_of_mem_criticalPoints_neg_mgradient`) and the distance
to `p` all vanish, so the exponential bound on the distance holds with the constant `0`. -/
theorem IsMIntegralCurveOn.forall_eq_or_forall_pos_of_tendsto_neg_mgradient
    (hγ : IsMIntegralCurveOn γ (-mgradient I f) (Ici 0)) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hconv : Tendsto γ atTop (𝓝 p)) :
    (∀ t ≥ 0, γ t = p) ∨
      ∀ t ≥ 0, 0 < f (γ t) - f p ∧ 0 < Manifold.riemannianEDist I (γ t) p := by
  by_cases h0 : γ 0 ∈ criticalPoints I f
  · -- The curve is constant, so its limit `p` is its value.
    have hconst (t : ℝ) (ht : 0 ≤ t) : γ t = γ 0 :=
      hγ.apply_eq_of_mem_criticalPoints_neg_mgradient hf le_rfl h0 ht
    have hp : γ 0 = p := tendsto_nhds_unique (tendsto_const_nhds.congr' <| by
      filter_upwards [eventually_ge_atTop 0] with t ht using (hconst t ht).symm) hconv
    exact .inl fun t ht ↦ (hconst t ht).trans hp
  · -- `f` strictly decreases along the curve towards `f p`, so it stays above `f p`.
    have hanti := hγ.strictAntiOn_comp_neg_mgradient hf h0
    have hlim : Tendsto (f ∘ γ) atTop (𝓝 (f p)) := (hf.continuous.tendsto p).comp hconv
    refine .inr fun t ht ↦ ?_
    have ht1 : (0 : ℝ) ≤ t + 1 := by linarith
    have hle : f p ≤ f (γ (t + 1)) := le_of_tendsto hlim <| by
      filter_upwards [eventually_ge_atTop (t + 1)] with s hs
      exact hanti.antitoneOn ht1 (ht1.trans hs) hs
    have hlt : f (γ (t + 1)) < f (γ t) := hanti ht ht1 (by linarith)
    have hE : 0 < f (γ t) - f p := by linarith
    refine ⟨hE, ?_⟩
    -- The Riemannian distance is positive between the distinct points `γ t` and `p`.
    have : IsManifold I 1 M := IsManifold.of_le one_le_two
    have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
    have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
    exact Manifold.riemannianEDist_pos.2 fun h ↦ by rw [h, sub_self] at hE; exact hE.false

end Equilibrium
