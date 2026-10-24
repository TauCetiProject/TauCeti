/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import TauCeti.Geometry.Manifold.Morse.GradientFlow
-- Private: the normed-space Łojasiewicz inequality, Grönwall's inequality, the continuity of a
-- `C¹` metric and the comparison of length with energy are used only inside proofs; no
-- declaration below exposes their APIs.
import TauCeti.Analysis.Calculus.Morse.Basic
import TauCeti.Analysis.ODE.Gronwall
import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Exponential convergence of a negative gradient trajectory on a manifold

Let `f` be a function on a manifold `M` carrying a continuous Riemannian metric, and let `p` be a
nondegenerate critical point of `f`. Near `p` the **Morse form of Łojasiewicz's gradient
inequality** holds with the optimal exponent `1/2`:

`lam * |f y - f p| ≤ ‖grad f y‖ ^ 2`

(`TauCeti.IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq`). It is
transported from the normed-space inequality
`TauCeti.IsNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_fderiv_sq` for the coordinate
expression of `f` in the preferred chart at `p`: near `p` the differential of that expression is
bounded by a multiple of the Riemannian length of the gradient
(`TauCeti.Manifold.eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient`). The metric
need not be adapted to the chart, nor smooth.

Now let `γ` be the maximal integral curve of `-grad f` through `x`, defined for all positive time
and converging to `p`. The energy `f (γ t) - f p` is nonnegative
(`TauCeti.le_comp_maximalIntegralCurve_neg_mgradient`), since `f` decreases along `γ` and tends to
`f p`. Its derivative is `-‖grad f (γ t)‖ ^ 2`, which the inequality above bounds by `-lam` times
the energy once `γ` stays near `p`, so by Grönwall's inequality the energy decays like
`exp (-lam * t)` (`TauCeti.exists_sub_le_mul_exp_maximalIntegralCurve_neg_mgradient`). This is the
manifold counterpart, for an arbitrary `C¹` metric, of the vector-space theorem
`TauCeti.IsIntegralCurveOn.exists_sub_le_mul_exp_atTop`.

Energy decay alone does not bound the distance from `γ t` to `p`, since the Hessian at a saddle
has null directions. The distance is recovered from the Riemannian length of `γ`. The length over
`[a, b]` is at most `sqrt (2 * (b - a) * E)`, where `E` is the path energy `½ ∫ ‖γ'‖²` of `γ` on
`[a, b]` (`ContMDiffOn.pathELength_le_ofReal_sqrt_energy`), and along a negative gradient
trajectory `2 * E = f (γ a) - f (γ b)` (`TauCeti.energy_maximalIntegralCurve_neg_mgradient`).
Over each unit of time the square root of `f (γ t) - f p` shrinks by the factor `exp (-lam / 2)`,
so summing a geometric series bounds the tail length of `γ` after time `t`, and with it the
Riemannian distance from `γ t` to `p`, by a multiple of `sqrt (f (γ t) - f p)`. Hence that distance
decays exponentially
(`TauCeti.exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`), as in
`TauCeti.IsIntegralCurveOn.exists_norm_sub_le_mul_exp_atTop`. The distance is
`Manifold.riemannianEDist`, the infimum of lengths of `C¹` paths; on a Riemannian manifold in the
sense of `IsRiemannianManifold` it is the ambient extended distance.

## Main results

* `TauCeti.IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq`: the
  Łojasiewicz inequality with exponent `1/2` near a nondegenerate critical point, for the
  Riemannian gradient.
* `TauCeti.le_comp_maximalIntegralCurve_neg_mgradient`: the energy along a forward negative
  gradient trajectory is bounded below by its value at the limit point.
* `TauCeti.exists_sub_le_mul_exp_maximalIntegralCurve_neg_mgradient`: along a forward negative
  gradient trajectory converging to a nondegenerate critical point the energy decays exponentially.
* `TauCeti.exists_pathELength_le_mul_sqrt_maximalIntegralCurve_neg_mgradient` and
  `TauCeti.exists_riemannianEDist_le_mul_sqrt_maximalIntegralCurve_neg_mgradient`: the tail length
  of a trajectory converging to a nondegenerate critical point, and its Riemannian distance to the
  limit, are bounded by a multiple of the square root of the energy.
* `TauCeti.exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`: such a
  trajectory converges to its limit exponentially fast in the Riemannian distance.

## References

* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, Éditions du CNRS, Paris, 1963, 87--89.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open Bundle Filter MeasureTheory Set Topology TauCeti.Manifold
open scoped ContDiff ENNReal Manifold

namespace TauCeti

section Lojasiewicz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {p : M}

/-- **The Morse form of Łojasiewicz's gradient inequality on a Riemannian manifold.** Near a
nondegenerate critical point `p` of `f`, the absolute energy difference `|f y - f p|` is bounded by
a multiple of the squared Riemannian length of the gradient of `f` at `y`, for any continuous
Riemannian metric. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq
    (hp : IsManifoldNondegenerateCriticalPoint I f p) :
    ∃ lam > 0, ∀ᶠ y in 𝓝 p, lam * |f y - f p| ≤ ‖mgradient I f y‖ ^ 2 := by
  obtain ⟨lam, hlam, hloj⟩ :=
    ((isManifoldNondegenerateCriticalPoint_iff I).1 hp).exists_mul_abs_sub_le_norm_fderiv_sq
  obtain ⟨C, hC, hbd⟩ :=
    eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient (I := I) f p
  refine ⟨lam / C ^ 2, by positivity, ?_⟩
  filter_upwards [(continuousAt_extChartAt (I := I) p).eventually hloj, hbd,
    extChartAt_source_mem_nhds (I := I) p] with y hy hyb hys
  simp only [Function.comp_apply, (extChartAt I p).left_inv hys,
    (extChartAt I p).left_inv (mem_extChartAt_source p)] at hy
  calc lam / C ^ 2 * |f y - f p| = lam * |f y - f p| / C ^ 2 := by ring
    _ ≤ ‖fderiv ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p y)‖ ^ 2 / C ^ 2 := by gcongr
    _ ≤ (C * ‖mgradient I f y‖) ^ 2 / C ^ 2 := by gcongr
    _ = ‖mgradient I f y‖ ^ 2 := by field_simp

end Lojasiewicz

section Decay

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x p : M}

/-- **The energy along a convergent trajectory is nonnegative.** If the maximal integral curve of
`-grad f` through `x` exists for all positive time and converges to `p`, then `f p ≤ f (γ t)` for
every `t ≥ 0`: the function `f` decreases along the curve and tends to `f p`. -/
theorem le_comp_maximalIntegralCurve_neg_mgradient (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hconv : Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p)) {t : ℝ}
    (ht : 0 ≤ t) :
    f p ≤ f (maximalIntegralCurve (-mgradient I f) x t) := by
  refine le_of_tendsto ((hf.continuous.tendsto p).comp hconv) ?_
  filter_upwards [eventually_ge_atTop t] with s hs
  exact antitoneOn_comp_maximalIntegralCurve_neg_mgradient hf (hx ht) (hx (ht.trans hs)) hs

/-- **The energy along a trajectory converging to a nondegenerate critical point decays
exponentially.** If the maximal integral curve `γ` of `-grad f` through `x` exists for all positive
time and converges to a nondegenerate critical point `p`, then `f (γ t) - f p ≤ C * exp (-μ * t)`
for some `μ, C > 0` and all large `t`. -/
theorem exists_sub_le_mul_exp_maximalIntegralCurve_neg_mgradient (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hp : IsManifoldNondegenerateCriticalPoint I f p)
    (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hconv : Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p)) :
    ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop,
      f (maximalIntegralCurve (-mgradient I f) x t) - f p ≤ C * Real.exp (-(μ * t)) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  set γ := maximalIntegralCurve (-mgradient I f) x
  obtain ⟨lam, hlam, hloj⟩ := hp.exists_mul_abs_sub_le_norm_mgradient_sq
  -- After some time `T ≥ 0` the trajectory stays where the Łojasiewicz inequality holds.
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((hconv.eventually hloj).and (eventually_ge_atTop 0))
  let g : ℝ → ℝ := fun s ↦ f (γ s) - f p
  have hg : ∀ s ∈ Ici T, HasDerivAt g (-‖mgradient I f (γ s)‖ ^ 2) s := fun s hs ↦
    (hasDerivAt_comp_maximalIntegralCurve_neg_mgradient hf
      (hx ((hT T le_rfl).2.trans hs))).sub_const _
  have hloj' : ∀ s ∈ Ici T, lam * |g s| ≤ ‖mgradient I f (γ s)‖ ^ 2 := fun s hs ↦ (hT s hs).1
  -- On `[T, ∞)` the energy `g` satisfies `g' = -‖grad f‖² ≤ -lam * g`, so it decays exponentially.
  exact ⟨lam, hlam, exists_le_mul_exp_atTop_of_hasDerivAt_le_neg_mul (lam := lam) hg fun s hs ↦
    by linarith [hloj' s hs, mul_le_mul_of_nonneg_left (le_abs_self (g s)) hlam.le]⟩

/-! ### Length of a trajectory and distance to its limit -/

variable (hp : IsManifoldNondegenerateCriticalPoint I f p)
  (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
  (hconv : Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p))
include hp hx hconv

/-- **The tail length of a trajectory converging to a nondegenerate critical point is controlled
by the square root of its energy.** If the maximal integral curve `γ` of `-grad f` through `x`
exists for all positive time and converges to a nondegenerate critical point `p`, then for some
`K > 0` and all large `t`, every piece of `γ` starting at time `t` has Riemannian length at most
`K * sqrt (f (γ t) - f p)`. -/
theorem exists_pathELength_le_mul_sqrt_maximalIntegralCurve_neg_mgradient
    (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    ∃ K > 0, ∀ᶠ t in atTop, ∀ s,
      Manifold.pathELength I (maximalIntegralCurve (-mgradient I f) x) t s ≤
        ENNReal.ofReal (K * √(f (maximalIntegralCurve (-mgradient I f) x t) - f p)) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  set γ := maximalIntegralCurve (-mgradient I f) x
  set e : ℝ → ℝ := fun s ↦ f (γ s) - f p
  obtain ⟨lam, hlam, hloj⟩ := hp.exists_mul_abs_sub_le_norm_mgradient_sq
  -- After some time `T ≥ 0` the trajectory stays where the Łojasiewicz inequality holds.
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((hconv.eventually hloj).and (eventually_ge_atTop 0))
  have he : ∀ s ∈ Ici T, HasDerivAt e (-‖mgradient I f (γ s)‖ ^ 2) s := fun s hs ↦
    (hasDerivAt_comp_maximalIntegralCurve_neg_mgradient hf
      (hx ((hT T le_rfl).2.trans hs))).sub_const _
  have he0 : ∀ s ∈ Ici T, 0 ≤ e s := fun s hs ↦
    sub_nonneg.2 (le_comp_maximalIntegralCurve_neg_mgradient hf hx hconv
      ((hT T le_rfl).2.trans hs))
  -- In unit time the square root of the energy decreases by the factor `r = exp (-lam / 2)`.
  set r := Real.exp (-lam / 2)
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hdecay : ∀ t ∈ Ici T, √(e (t + 1)) ≤ r * √(e t) := by
    intro t ht
    have h := le_mul_exp_of_hasDerivAt_le_neg_mul (lam := lam) (fun s hs ↦ he s (le_trans ht hs))
      (fun s hs ↦ by
        simp only [e]
        linarith [(hT s (le_trans ht hs)).1,
          mul_le_mul_of_nonneg_left (le_abs_self (f (γ s) - f p)) hlam.le])
      (le_add_of_nonneg_right zero_le_one)
    rw [add_sub_cancel_left, mul_one] at h
    calc √(e (t + 1)) ≤ √(e t * Real.exp (-lam)) := Real.sqrt_le_sqrt h
      _ = r * √(e t) := by rw [Real.sqrt_mul (he0 t ht), ← Real.exp_half, mul_comm]
  -- A unit-time piece of `γ` has length at most `sqrt (2 * E)`, where its path energy `E` is half
  -- the drop of `f` over that time, so the length is at most `sqrt (e t)`.
  have hstep : ∀ t ∈ Ici T, Manifold.pathELength I γ t (t + 1) ≤ ENNReal.ofReal √(e t) := by
    intro t ht
    have htt : t ≤ t + 1 := le_add_of_nonneg_right zero_le_one
    have hsub : Icc t (t + 1) ⊆ maximalIntegralCurveInterval (-mgradient I f) x :=
      fun s hs ↦ hx ((hT T le_rfl).2.trans (ht.trans hs.1))
    refine ((contMDiffOn_maximalIntegralCurve_neg_mgradient hf).pathELength_le_ofReal_sqrt_energy
      isOpen_maximalIntegralCurveInterval.uniqueMDiffOn htt hsub).trans ?_
    rw [energy_maximalIntegralCurve_neg_mgradient hf (by rwa [uIcc_of_le htt]),
      add_sub_cancel_left]
    have := he0 (t + 1) (ht.trans htt)
    gcongr
    simp only [e] at this ⊢
    linarith
  -- Summing the geometric series: `K = 1 / (1 - r)` satisfies `1 + K * r = K`.
  set K := 1 / (1 - r)
  have hK : 0 < K := one_div_pos.2 (sub_pos.2 hr1)
  have hKr : 1 + K * r = K := by
    have : 1 - r ≠ 0 := (sub_pos.2 hr1).ne'
    simp only [K]
    field_simp
    ring
  have hlen : ∀ n : ℕ, ∀ t ∈ Ici T,
      Manifold.pathELength I γ t (t + n) ≤ ENNReal.ofReal (K * √(e t)) := by
    intro n
    induction n with
    | zero => intro t _; simp
    | succ n ih =>
      intro t ht
      have ht1 : t + 1 ∈ Ici T := le_add_of_le_of_nonneg ht zero_le_one
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [← Manifold.pathELength_add (b := t + 1) (by linarith) (by push_cast; linarith)]
      calc Manifold.pathELength I γ t (t + 1) + Manifold.pathELength I γ (t + 1) (t + ↑(n + 1))
          ≤ ENNReal.ofReal √(e t) + ENNReal.ofReal (K * √(e (t + 1))) := by
            gcongr
            · exact hstep t ht
            · simpa [add_assoc, add_comm (1 : ℝ)] using ih (t + 1) ht1
        _ ≤ ENNReal.ofReal √(e t) + ENNReal.ofReal (K * (r * √(e t))) := by
            gcongr
            exact hdecay t ht
        _ = ENNReal.ofReal (K * √(e t)) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            linear_combination √(e t) * hKr
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop T] with t ht s
  exact (Manifold.pathELength_mono le_rfl (by linarith [Nat.le_ceil (s - t)])).trans
    (hlen ⌈s - t⌉₊ t ht)

/-- **The Riemannian distance from a trajectory to its nondegenerate limit is controlled by the
square root of its energy.** If the maximal integral curve `γ` of `-grad f` through `x` exists for
all positive time and converges to a nondegenerate critical point `p`, then for some `K > 0` and
all large `t`, the Riemannian distance from `γ t` to `p` is at most `K * sqrt (f (γ t) - f p)`. -/
theorem exists_riemannianEDist_le_mul_sqrt_maximalIntegralCurve_neg_mgradient
    (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    ∃ K > 0, ∀ᶠ t in atTop,
      Manifold.riemannianEDist I (maximalIntegralCurve (-mgradient I f) x t) p ≤
        ENNReal.ofReal (K * √(f (maximalIntegralCurve (-mgradient I f) x t) - f p)) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  set γ := maximalIntegralCurve (-mgradient I f) x
  obtain ⟨K, hK, hlen⟩ := exists_pathELength_le_mul_sqrt_maximalIntegralCurve_neg_mgradient
    hp hx hconv hf
  refine ⟨K, hK, ?_⟩
  filter_upwards [hlen, eventually_ge_atTop 0] with t ht ht0
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  -- Compare with a later point `γ s` which is `ε`-close to `p`.
  obtain ⟨s, hs, hts⟩ := ((hconv.eventually (eventually_riemannianEDist_lt I p
    (c := ε) (by exact_mod_cast hε))).and (eventually_ge_atTop t)).exists
  calc Manifold.riemannianEDist I (γ t) p
      ≤ Manifold.riemannianEDist I (γ t) (γ s) + Manifold.riemannianEDist I (γ s) p :=
        Manifold.riemannianEDist_triangle
    _ ≤ Manifold.pathELength I γ t s + ε := by
        gcongr
        · exact Manifold.riemannianEDist_le_pathELength
            ((contMDiffOn_maximalIntegralCurve_neg_mgradient hf).mono
              fun u hu ↦ hx (ht0.trans hu.1)) rfl rfl hts
        · rw [Manifold.riemannianEDist_comm]
          exact hs.le
    _ ≤ ENNReal.ofReal (K * √(f (γ t) - f p)) + ε := by gcongr; exact ht s

/-- **A trajectory converging to a nondegenerate critical point converges exponentially fast in
the Riemannian distance.** If the maximal integral curve `γ` of `-grad f` through `x` exists for
all positive time and converges to a nondegenerate critical point `p`, then the Riemannian
distance from `γ t` to `p` is at most `C * exp (-μ * t)` for some `μ, C > 0` and all large `t`.
This is the manifold counterpart, for an arbitrary `C¹` metric, of the vector-space theorem
`TauCeti.IsIntegralCurveOn.exists_norm_sub_le_mul_exp_atTop`. -/
theorem exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient
    (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop,
      Manifold.riemannianEDist I (maximalIntegralCurve (-mgradient I f) x t) p ≤
        ENNReal.ofReal (C * Real.exp (-(μ * t))) := by
  obtain ⟨K, hK, hdist⟩ := exists_riemannianEDist_le_mul_sqrt_maximalIntegralCurve_neg_mgradient
    hp hx hconv hf
  obtain ⟨μ, hμ, C, hC, henergy⟩ :=
    exists_sub_le_mul_exp_maximalIntegralCurve_neg_mgradient hf hp hx hconv
  refine ⟨μ / 2, by positivity, K * √C, by positivity, ?_⟩
  filter_upwards [hdist, henergy] with t ht hte
  refine ht.trans (ENNReal.ofReal_le_ofReal ?_)
  calc K * √(f (maximalIntegralCurve (-mgradient I f) x t) - f p)
      ≤ K * √(C * Real.exp (-(μ * t))) := by gcongr
    _ = K * √C * Real.exp (-(μ / 2 * t)) := by
        rw [Real.sqrt_mul hC.le, ← Real.exp_half, mul_assoc]
        ring_nf

end Decay

end TauCeti
