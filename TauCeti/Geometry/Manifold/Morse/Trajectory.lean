/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.ExponentialConvergence
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.Geometry.Manifold.IntegralCurve.Forward
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Distance

/-!
# Convergence of prescribed forward gradient trajectories

The maximal negative-gradient flow estimates also apply to any prescribed integral curve on
`[0, ∞)`. A compact trap with finitely many critical points forces convergence to a critical point
in that trap. In particular this applies to Morse functions, without compactness of the ambient
manifold, and to proper bounded-below Morse functions without a separately supplied trap.

If a forward curve converges to a nondegenerate critical point, its Riemannian extended distance
to that point is bounded by `C * exp (-c * t)` for every `t ≥ 0`. The existing eventual estimate
`TauCeti.exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient` supplies the tail
bound, and `TauCeti.exists_tendsto_maximalIntegralCurve_neg_mgradient` supplies compact-trap
convergence. Continuity on the initial compact time interval absorbs that interval into `C`.
No adapted metric or positivity of the Hessian is required, so a trajectory may converge to a
saddle.

The comparison with the maximal curve moves the time origin to time `1`, which lies in the
interior of the prescribed curve's domain. It therefore does not require a two-sided derivative
of the prescribed curve at its initial endpoint.

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
  have hshift : IsMIntegralCurveOn (γ ∘ (· + 1)) (-mgradient I f) (Ioi (-1)) :=
    (hγ.comp_add 1).mono fun t ht ↦ by simp only [mem_ofPred_eq, mem_Ici, mem_Ioi] at *; linarith
  have heq := hshift.eqOn_maximalIntegralCurve_Ioi (x := γ 1)
    (contMDiff_neg_mgradient_one hf) (by norm_num) (by simp)
  have hmaps : MapsTo (maximalIntegralCurve (-mgradient I f) (γ 1))
      (maximalIntegralCurveInterval (-mgradient I f) (γ 1) ∩ Ici 0) K := by
    intro t ht
    rw [heq (x := t) (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) ht.2)]
    exact hmem (by simpa only [comp_apply, mem_Ici] using add_nonneg ht.2 zero_le_one)
  obtain ⟨p, hp, hlim⟩ := exists_tendsto_maximalIntegralCurve_neg_mgradient hK hmaps hf hfin
  refine ⟨p, hp, ?_⟩
  have hlim' := hlim.comp (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
  apply hlim'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  simpa only [comp_apply, id_eq, neg_add_cancel_right] using
    heq (x := t + -1) (by simp only [mem_Ioi]; linarith)

namespace TauCeti

/-- A forward trajectory of a Morse function trapped in a compact set converges to a critical
point belonging to that set, for an arbitrary `C¹` metric. -/
theorem IsMorse.exists_tendsto_of_isMIntegralCurveOn_neg_mgradient [I.Boundaryless]
    (hf : IsMorse I f) (hγ : IsMIntegralCurveOn γ (-mgradient I f) (Ici 0))
    (hK : IsCompact K) (hmem : MapsTo γ (Ici 0) K) :
    ∃ p ∈ criticalPoints I f ∩ K, Tendsto γ atTop (𝓝 p) :=
  hγ.exists_tendsto_neg_mgradient (hf.contMDiff.of_le (by norm_num)) hK hmem
    (hf.finite_criticalPoints_inter hK)

/-- Every prescribed forward trajectory of a proper bounded-below Morse function converges to a
critical point. Neither compactness of the manifold nor completeness of the metric is needed. -/
theorem IsMorse.exists_tendsto_of_isMIntegralCurveOn_neg_mgradient_of_isProperMap [I.Boundaryless]
    (hf : IsMorse I f) (hγ : IsMIntegralCurveOn γ (-mgradient I f) (Ici 0))
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) :
    ∃ p ∈ criticalPoints I f, Tendsto γ atTop (𝓝 p) := by
  have hf2 : ContMDiff I 𝓘(ℝ) 2 f := hf.contMDiff.of_le (by norm_num)
  have hshift : IsMIntegralCurveOn (γ ∘ (· + 1)) (-mgradient I f) (Ioi (-1)) :=
    (hγ.comp_add 1).mono fun t ht ↦ by simp only [mem_ofPred_eq, mem_Ici, mem_Ioi] at *; linarith
  have heq := hshift.eqOn_maximalIntegralCurve_Ioi (x := γ 1)
    (contMDiff_neg_mgradient_one hf2) (by norm_num) (by simp)
  obtain ⟨p, hp, hlim⟩ := hf.exists_tendsto_maximalIntegralCurve_neg_mgradient hp hbdd (γ 1)
  refine ⟨p, hp, ?_⟩
  apply (hlim.comp (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  simpa only [comp_apply, id_eq, neg_add_cancel_right] using
    heq (x := t + -1) (by simp only [mem_Ioi]; linarith)

end TauCeti

end Topological

section Distance

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [PseudoEMetricSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 2 M] [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {f : M → ℝ} {γ : ℝ → M} {p : M}

/-- Transfer the eventual maximal-flow estimate to a prescribed forward curve. -/
private theorem eventually_edist_neg_mgradient
    (hγ : IsMIntegralCurveOn γ (-mgradient I f) (Ici 0)) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hp : IsManifoldNondegenerateCriticalPoint I f p) (hconv : Tendsto γ atTop (𝓝 p)) :
    ∃ c > 0, ∃ C > 0, ∀ᶠ t in atTop, edist (γ t) p ≤ ENNReal.ofReal (C * Real.exp (-(c * t))) := by
  have hshift : IsMIntegralCurveOn (γ ∘ (· + 1)) (-mgradient I f) (Ioi (-1)) :=
    (hγ.comp_add 1).mono fun t ht ↦ by simp only [mem_ofPred_eq, mem_Ici, mem_Ioi] at *; linarith
  have heq := hshift.eqOn_maximalIntegralCurve_Ioi (x := γ 1)
    (contMDiff_neg_mgradient_one hf) (by norm_num) (by simp)
  have hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) (γ 1) :=
    fun t ht ↦ hshift.Ioi_subset_maximalIntegralCurveInterval (by norm_num) (by simp)
      (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) ht)
  have hlim : Tendsto (maximalIntegralCurve (-mgradient I f) (γ 1)) atTop (𝓝 p) := by
    apply (hconv.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (heq (x := t) (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) ht)).symm
  obtain ⟨c, hc, C, hC, hbound⟩ :=
    exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient hp hx hlim hf
  refine ⟨c, hc, C * Real.exp c, by positivity, ?_⟩
  filter_upwards [(tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id).eventually hbound,
    eventually_ge_atTop (1 : ℝ)] with t ht ht1
  simp only [id_eq] at ht
  rw [heq (x := t + -1) (by simp only [mem_Ioi]; linarith), comp_apply,
    neg_add_cancel_right, ← IsRiemannianManifold.out (I := I)] at ht
  rw [← sub_eq_add_neg, exp_neg_mul_sub, mul_one] at ht
  simpa only [mul_assoc] using ht

/-- A prescribed forward negative-gradient curve converging to a nondegenerate critical point
satisfies an exponential distance bound for every nonnegative time, not only eventually. The
extended distance is the Riemannian path distance. The limit may be a saddle. -/
theorem IsMIntegralCurveOn.exists_edist_le_exp_of_tendsto_neg_mgradient
    (hγ : IsMIntegralCurveOn γ (-mgradient I f) (Ici 0)) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hp : IsManifoldNondegenerateCriticalPoint I f p) (hconv : Tendsto γ atTop (𝓝 p)) :
    ∃ C > 0, ∃ c > 0, ∀ t ≥ 0, edist (γ t) p ≤ ENNReal.ofReal (C * Real.exp (-(c * t))) := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  -- The whole trajectory and its limit lie in one connected set. Distances to the limit are
  -- finite even when the ambient extended metric takes infinite values between components.
  have hconn := (isPreconnected_Ici.image γ hγ.continuousOn).closure
  have hpcl : p ∈ closure (γ '' Ici 0) :=
    mem_closure_of_tendsto hconv (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht using mem_image_of_mem γ ht)
  have hfin (t : ℝ) (ht : 0 ≤ t) : edist (γ t) p ≠ ⊤ := by
    rw [IsRiemannianManifold.out (I := I)]
    exact (riemannianEDist_lt_top_of_isPreconnected I hconn
      (subset_closure (mem_image_of_mem γ ht)) hpcl).ne
  have hcont : ContinuousOn (fun t ↦ (edist (γ t) p).toReal) (Ici 0) :=
    ENNReal.continuousOn_toReal.comp
      (continuous_edist.comp_continuousOn (hγ.continuousOn.prodMk continuousOn_const))
      (fun t ht ↦ hfin t ht)
  obtain ⟨c, hc, C, _, hbound⟩ := eventually_edist_neg_mgradient hγ hf hp hconv
  have hbound' : ∀ᶠ t in atTop, (edist (γ t) p).toReal ≤ C * Real.exp (-(c * t)) := by
    filter_upwards [hbound] with t ht
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) ht
  obtain ⟨B, hB, hBbound⟩ := hcont.exists_forall_le_mul_exp_Ici_of_eventually_le hbound'
  exact ⟨B, hB, c, hc, fun t ht ↦ (ENNReal.le_ofReal_iff_toReal_le (hfin t ht)
    (by positivity)).2 (hBbound t ht)⟩

end Distance
