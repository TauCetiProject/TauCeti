/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Probability.ConditionalProbability
public import TauCeti.MeasureTheory.OptimalTransport.DynamicPlan
public import TauCeti.MeasureTheory.OptimalTransport.MetricMeasure.Basic
public import TauCeti.MeasureTheory.OptimalTransport.MetricMeasure.DistortionCoefficient
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The measure-contraction property `MCP(K, N)`

Let `M` be a metric-measure space (`TauCeti.MetricMeasureSpace`): a complete separable metric
space `X` with its Borel structure and a reference measure `m` finite on bounded sets. For a
curvature bound `K : ℝ` and a dimension bound `N : ℝ`, `M` has the *measure-contraction property*
`MCP(K, N)` of Ohta and Sturm when the reference measure contracts towards every point of its
support at least as fast as in the model space of curvature `K / (N - 1)` and dimension `N`.
In the form of Cavalletti–Mondino used here: for every `o` in the support of `m` and every
measurable `A` with `0 < m(A) < ∞`, the normalised restriction `m[|A] = m(A)⁻¹ m|_A` is joined to
the Dirac mass `δ_o` by a dynamic plan `η` concentrated on geodesics such that, for every time
`t ∈ [0, 1]`,

`(e_t)_# (τ_{K,N}^{(1-t)}(d(γ₀, γ₁))^N η(dγ)) ≤ m(A)⁻¹ m`,

where `e_t` evaluates a path at time `t` and `τ_{K,N}` is the distortion coefficient
`TauCeti.distortionTau`. In words: the mass of `A`, transported along geodesics to `o` and
weighted by the distortion coefficient, never piles up above the reference measure. Since the
target is a Dirac mass, the only coupling of `m[|A]` and `δ_o` is their product, so every
dynamic plan concentrated on geodesics with these two time marginals is an optimal one; no
separate optimality requirement is needed. Ohta states the condition with the time reversed,
starting from `δ_o` at time `0`; the two forms agree after reversing the paths.

The coefficient `τ_{K,N}^{(s)}(θ)` is infinite for `K > 0` and `θ` beyond the Bonnet–Myers
distance `π √((N - 1) / K)`, at every time `s`, following Sturm. With this convention the
condition at time `t = 0` already forces the **Bonnet–Myers diameter bound**: under `MCP(K, N)`
with `K > 0` and `N > 0`, any two points of the support of `m` are at distance at most
`π √((N - 1) / K)` (`TauCeti.MetricMeasureSpace.MeasureContraction.dist_le`).

On a finite-dimensional real normed space `E` of dimension `n ≥ 1` with an additive Haar measure,
the plan moving `m[|A]` along straight segments to `o` shows that `MCP(K, N)` holds for every
`K ≤ 0` and `N ≥ n`; conversely the time marginals of any plan from the unit ball to `0` are
carried by smaller balls, so `MCP(0, N)` forces `N ≥ n`. Thus Haar measure on `E` satisfies
`MCP(0, N)` exactly when `N ≥ n`
(`TauCeti.MetricMeasureSpace.measureContraction_zero_iff_finrank_le`), and `MCP(K, N)` for no
`K > 0` and `N > 0`, its support being unbounded.

## Main definitions

* `TauCeti.MetricMeasureSpace.MeasureContraction M K N`: the measure-contraction property
  `MCP(K, N)` of the metric-measure space `M`.

## Main statements

* `TauCeti.MetricMeasureSpace.MeasureContraction.mono`: for `N ≥ 0`, `MCP(K, N)` implies
  `MCP(K', N)` whenever `K' ≤ K`.
* `TauCeti.MetricMeasureSpace.MeasureContraction.dist_le`,
  `TauCeti.MetricMeasureSpace.MeasureContraction.diam_support_le`: the Bonnet–Myers diameter
  bound `diam (supp m) ≤ π √((N - 1) / K)` under `MCP(K, N)` with `K > 0` and `N > 0`.
* `TauCeti.MetricMeasureSpace.measureContraction_of_nonpos_of_finrank_le`: Haar measure on a real
  vector space of dimension `n ≥ 1` satisfies `MCP(K, N)` for `K ≤ 0` and `N ≥ n`.
* `TauCeti.MetricMeasureSpace.finrank_le_of_measureContraction_zero`,
  `TauCeti.MetricMeasureSpace.measureContraction_zero_iff_finrank_le`: Haar measure on a real
  vector space of dimension `n` satisfies `MCP(0, N)` only for `N ≥ n`, and, for `n ≥ 1`, exactly
  then.
* `TauCeti.MetricMeasureSpace.not_measureContraction_of_pos`: Haar measure on a nontrivial real
  vector space satisfies `MCP(K, N)` for no `K > 0` and `N > 0`.

## References

* S. Ohta, *On the measure contraction property of metric measure spaces*, Comment. Math. Helv.
  82 (2007), 805–828, Definition 2.1.
* K.-T. Sturm, *On the geometry of metric measure spaces. II*, Acta Math. 196 (2006), 133–177,
  §5.
* F. Cavalletti and A. Mondino, *Optimal maps in essentially non-branching spaces*, Commun.
  Contemp. Math. 19 (2017), 1750007, Definition 2.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Module
open scoped ENNReal unitInterval Real

namespace TauCeti

namespace MetricMeasureSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [BorelSpace X] {M : MetricMeasureSpace X} {K K' N : ℝ}

/-- The **measure-contraction property** `MCP(K, N)` of Ohta and Sturm, in the form of
Cavalletti–Mondino: for every point `o` of the support of the reference measure `m` and every
measurable `A` with `0 < m(A) < ∞`, some dynamic plan `η` concentrated on geodesics has law
`m[|A] = m(A)⁻¹ m|_A` at time `0` and law `δ_o` at time `1`, and for every time `t` the law at
time `t` of `η` weighted by `τ_{K,N}^{(1-t)}(d(γ₀, γ₁))^N` is at most `m(A)⁻¹ m`.

Such a plan is automatically optimal, since `m[|A]` and `δ_o` have only one coupling. -/
def MeasureContraction (M : MetricMeasureSpace X) (K N : ℝ) : Prop :=
  ∀ o ∈ M.support, ∀ A : Set X, MeasurableSet A → 0 < M.reference A → M.reference A < ∞ →
    ∃ η : Measure C(I, X), (∀ᵐ γ ∂η, γ ∈ geodesicPaths X) ∧
      η.timeMarginal 0 = M.reference[|A] ∧ η.timeMarginal 1 = Measure.dirac o ∧
      ∀ t : I, (η.withDensity fun γ ↦
        distortionTau K N (1 - t) (dist (γ 0) (γ 1)) ^ N).timeMarginal t ≤
          (M.reference A)⁻¹ • M.reference

/-- The measure-contraction property `MCP(K, N)`, unfolded. -/
theorem measureContraction_iff : M.MeasureContraction K N ↔
    ∀ o ∈ M.support, ∀ A : Set X, MeasurableSet A → 0 < M.reference A → M.reference A < ∞ →
      ∃ η : Measure C(I, X), (∀ᵐ γ ∂η, γ ∈ geodesicPaths X) ∧
        η.timeMarginal 0 = M.reference[|A] ∧ η.timeMarginal 1 = Measure.dirac o ∧
        ∀ t : I, (η.withDensity fun γ ↦
          distortionTau K N (1 - t) (dist (γ 0) (γ 1)) ^ N).timeMarginal t ≤
            (M.reference A)⁻¹ • M.reference :=
  Iff.rfl

/-- `MCP(K, N)` implies `MCP(K', N)` for every `K' ≤ K`, when `N ≥ 0`: the distortion coefficient
increases with the curvature bound. -/
theorem MeasureContraction.mono (h : M.MeasureContraction K N) (hK : K' ≤ K) (hN : 0 ≤ N) :
    M.MeasureContraction K' N := by
  intro o ho A hA hpos hfin
  obtain ⟨η, hgeo, h₀, h₁, hle⟩ := h o ho A hA hpos hfin
  refine ⟨η, hgeo, h₀, h₁, fun t ↦
    (Measure.timeMarginal_mono (withDensity_mono (ae_of_all _ fun γ ↦ ?_)) t).trans (hle t)⟩
  exact ENNReal.rpow_le_rpow (distortionTau_left_monotone (sub_nonneg.2 (unitInterval.le_one t))
    (sub_le_self _ (unitInterval.nonneg t)) hK) hN

/-- **The Bonnet–Myers diameter bound under `MCP(K, N)`.** If `M` satisfies `MCP(K, N)` with
`K > 0` and `N > 0`, any two points of the support of the reference measure are at distance at
most `π √((N - 1) / K)`. -/
theorem MeasureContraction.dist_le (h : M.MeasureContraction K N) (hK : 0 < K) (hN : 0 < N)
    {x y : X} (hx : x ∈ M.support) (hy : y ∈ M.support) : dist x y ≤ π * √((N - 1) / K) := by
  by_contra! hlt
  -- Transport a small ball about `y` to `x`: all its points are beyond the Bonnet–Myers distance.
  set r := (dist x y - π * √((N - 1) / K)) / 2 with hr_def
  have hr : 0 < r := by linarith
  have hA : MeasurableSet (ball y r) := measurableSet_ball
  have hpos : 0 < M.reference (ball y r) := (M.mem_support_iff y).1 hy _ (ball_mem_nhds y hr)
  have hfin : M.reference (ball y r) < ∞ := M.finite_bounded _ isBounded_ball
  obtain ⟨η, -, h₀, h₁, hle⟩ := h x hx _ hA hpos hfin
  -- The distortion weight is infinite on almost every path starting in the ball.
  have hτ : ∀ᵐ γ ∂η, γ 0 ∈ ball y r →
      distortionTau K N (1 - ((0 : I) : ℝ)) (dist (γ 0) (γ 1)) ^ N = ⊤ := by
    filter_upwards [Measure.ae_eq_of_timeMarginal_eq_dirac h₁] with γ hγ₁ hγ₀
    rw [mem_ball] at hγ₀
    rw [hγ₁, distortionTau_eq_top_of_lt hK, ENNReal.top_rpow_of_pos hN]
    linarith [dist_triangle x (γ 0) y, dist_comm x (γ 0)]
  have hηS : η {γ : C(I, X) | γ 0 ∈ ball y r} = 1 := by
    rw [← Measure.timeMarginal_apply η 0 hA, h₀, cond_apply_self hpos.ne' hfin.ne]
  -- At time `0`, the weighted law gives infinite mass to the ball, which has mass `1` on the right.
  have hball := Measure.le_iff'.1 (hle 0) (ball y r)
  rw [Measure.timeMarginal_withDensity_apply_of_ae_eq hA hτ, hηS, mul_one, Measure.smul_apply,
    smul_eq_mul, ENNReal.inv_mul_cancel hpos.ne' hfin.ne] at hball
  exact ENNReal.one_ne_top (top_le_iff.1 hball)

/-- **The Bonnet–Myers diameter bound under `MCP(K, N)`**, for `K > 0` and `N > 0`: the support of
the reference measure has diameter at most `π √((N - 1) / K)`. -/
theorem MeasureContraction.diam_support_le (h : M.MeasureContraction K N) (hK : 0 < K)
    (hN : 0 < N) : diam M.support ≤ π * √((N - 1) / K) :=
  diam_le_of_forall_dist_le (by positivity) fun _ hx _ hy ↦ h.dist_le hK hN hx hy

/-- Under `MCP(K, N)` with `K > 0` and `N > 0`, the support of the reference measure is bounded. -/
theorem MeasureContraction.isBounded_support (h : M.MeasureContraction K N) (hK : 0 < K)
    (hN : 0 < N) : Bornology.IsBounded M.support :=
  isBounded_iff.2 ⟨_, fun _ hx _ hy ↦ h.dist_le hK hN hx hy⟩

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {M : MetricMeasureSpace E}
  [M.reference.IsAddHaarMeasure]

/-- For a ratio `0 < s ≤ 1` and `N ≥ n`, the image of `m[|A]` under the homothety of ratio `s`
towards `o`, weighted by `s^N`, is at most `m(A)⁻¹ m`: the homothety multiplies volumes by `sⁿ`. -/
private theorem rpow_smul_map_cond_homothety_le {s : ℝ} (hs₀ : 0 < s) (hs₁ : s ≤ 1)
    (hN : (finrank ℝ E : ℝ) ≤ N) (o : E) (A : Set E) :
    ENNReal.ofReal s ^ N • M.reference[|A].map (AffineMap.homothety o s) ≤
      (M.reference A)⁻¹ • M.reference := by
  have hmeas : Measurable (AffineMap.homothety o s) :=
    (AffineMap.homothety_continuous o s).measurable
  -- The weight `s^N` compensates the volume factor `s^(-n)` since `N ≥ n`.
  have hc : ENNReal.ofReal s ^ N * ENNReal.ofReal |(s ^ finrank ℝ E)⁻¹| ≤ 1 := by
    rw [abs_of_pos (by positivity), ENNReal.ofReal_rpow_of_pos hs₀,
      ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_one, ← Real.rpow_natCast,
      ← Real.rpow_neg hs₀.le, ← Real.rpow_add hs₀]
    exact Real.rpow_le_one hs₀.le hs₁ (by linarith)
  refine Measure.le_iff'.2 fun S ↦ ?_
  calc (ENNReal.ofReal s ^ N • M.reference[|A].map (AffineMap.homothety o s)) S
      = ENNReal.ofReal s ^ N * ((M.reference A)⁻¹ *
          (M.reference.restrict A).map (AffineMap.homothety o s) S) := by
        rw [ProbabilityTheory.cond, Measure.map_smul _ hmeas.aemeasurable, Measure.smul_apply,
          Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    _ ≤ ENNReal.ofReal s ^ N * ((M.reference A)⁻¹ *
          M.reference.map (AffineMap.homothety o s) S) := by
        gcongr
        exact Measure.restrict_le_self
    _ = (M.reference A)⁻¹ *
          ((ENNReal.ofReal s ^ N * ENNReal.ofReal |(s ^ finrank ℝ E)⁻¹|) * M.reference S) := by
        rw [Measure.map_addHaar_homothety _ _ hs₀.ne', Measure.smul_apply, smul_eq_mul]
        ring
    _ ≤ (M.reference A)⁻¹ * (1 * M.reference S) := by gcongr
    _ = ((M.reference A)⁻¹ • M.reference) S := by
        rw [one_mul, Measure.smul_apply, smul_eq_mul]

/-- **Haar measure satisfies `MCP(K, N)` for `K ≤ 0` and `N ≥ n`.** On a real vector space of
finite dimension `n ≥ 1`, an additive Haar reference measure satisfies `MCP(K, N)` for every
`K ≤ 0` and `N ≥ n`. The plan moves `m[|A]` along straight segments to `o`; its law at time `t`
is the image of `m[|A]` under the homothety of ratio `1 - t` towards `o`. -/
theorem measureContraction_of_nonpos_of_finrank_le [Nontrivial E] (hK : K ≤ 0)
    (hN : (finrank ℝ E : ℝ) ≤ N) : M.MeasureContraction K N := by
  have hN₀ : 0 < N := (Nat.cast_pos.2 finrank_pos).trans_le hN
  intro o _ A hA hpos hfin
  have hseg : Measurable fun y : E ↦ segmentPath (y, o) :=
    (segmentPath.continuous.comp (continuous_id.prodMk continuous_const)).measurable
  have hprob : IsProbabilityMeasure M.reference[|A] :=
    cond_isProbabilityMeasure_of_finite hpos.ne' hfin.ne
  -- The law at time `t` of the segment plan is the image of `m[|A]` under the homothety.
  have hmarg (t : I) : (M.reference[|A].map fun y ↦ segmentPath (y, o)).timeMarginal t =
      M.reference[|A].map (AffineMap.homothety o (1 - (t : ℝ))) := by
    rw [Measure.timeMarginal_map _ hseg]
    congr 1
    ext y
    rw [segmentPath_apply, AffineMap.homothety_eq_lineMap, AffineMap.lineMap_apply_one_sub]
  refine ⟨M.reference[|A].map fun y ↦ segmentPath (y, o), ?_, ?_, ?_, fun t ↦ ?_⟩
  · exact (ae_map_iff hseg.aemeasurable isClosed_geodesicPaths.measurableSet).2
      (ae_of_all _ fun y ↦ segmentPath_mem_geodesicPaths (y, o))
  · simp [hmarg]
  · rw [hmarg]
    simp only [Icc.coe_one, sub_self, AffineMap.homothety_zero, AffineMap.coe_const]
    exact (Measure.map_const _ o).trans (by simp)
  -- The weight is at most its flat value `(1 - t)^N`.
  have hweight : (M.reference[|A].map fun y ↦ segmentPath (y, o)).withDensity
      (fun γ ↦ distortionTau K N (1 - t) (dist (γ 0) (γ 1)) ^ N) ≤
      ENNReal.ofReal (1 - t) ^ N • M.reference[|A].map fun y ↦ segmentPath (y, o) := by
    rw [← withDensity_const]
    exact withDensity_mono (ae_of_all _ fun γ ↦ ENNReal.rpow_le_rpow (distortionTau_le_ofReal
      (sub_nonneg.2 (unitInterval.le_one t)) (sub_le_self _ (unitInterval.nonneg t)) hK) hN₀.le)
  refine (Measure.timeMarginal_mono hweight t).trans ?_
  rw [Measure.timeMarginal_smul, hmarg]
  rcases (unitInterval.le_one t).lt_or_eq with ht | ht
  · exact rpow_smul_map_cond_homothety_le (sub_pos.2 ht) (sub_le_self _ (unitInterval.nonneg t))
      hN o A
  · simp only [ht, sub_self, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hN₀, zero_smul]
    exact Measure.zero_le _

/-- **`MCP(0, N)` forces `N ≥ n` for Haar measure.** If an additive Haar reference measure on a
real vector space of finite dimension `n` satisfies `MCP(0, N)`, then `N ≥ n`. At time `1 / 2`,
any plan from the closed unit ball to `0` has its law carried by the ball of radius `1 / 2`, of
relative volume `2^(-n)`, while the weight is `2^(-N)`. -/
theorem finrank_le_of_measureContraction_zero (h : M.MeasureContraction 0 N) :
    (finrank ℝ E : ℝ) ≤ N := by
  have hA : MeasurableSet (closedBall (0 : E) 1) := measurableSet_closedBall
  have hpos : 0 < M.reference (closedBall (0 : E) 1) :=
    measure_closedBall_pos M.reference 0 one_pos
  have hfin : M.reference (closedBall (0 : E) 1) < ∞ := M.finite_bounded _ isBounded_closedBall
  have h0 : (0 : E) ∈ M.support := by
    rw [support_def, Measure.support_eq_univ]
    exact mem_univ 0
  obtain ⟨η, hgeo, h₀, h₁, hle⟩ := h 0 h0 _ hA hpos hfin
  have hprob : IsProbabilityMeasure M.reference[|closedBall (0 : E) 1] :=
    cond_isProbabilityMeasure_of_finite hpos.ne' hfin.ne
  have hη : η univ = 1 := by
    have := Measure.timeMarginal_apply η 0 MeasurableSet.univ
    rw [h₀, measure_univ] at this
    simpa using this.symm
  let _ : IsProbabilityMeasure η := ⟨hη⟩
  set t : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have hS : MeasurableSet {γ : C(I, E) | γ t ∈ closedBall (0 : E) (1 / 2)} :=
    ContinuousMap.measurable_eval t measurableSet_closedBall
  -- Almost every path is in the ball of radius `1 / 2` at time `1 / 2`.
  have hηS : η {γ : C(I, E) | γ t ∈ closedBall (0 : E) (1 / 2)} = 1 := by
    rw [← hη, ← ae_iff_measure_eq hS.nullMeasurableSet]
    have h0 : ∀ᵐ γ ∂η, γ 0 ∈ closedBall (0 : E) 1 :=
      (Measure.ae_timeMarginal_iff (p := (· ∈ closedBall (0 : E) 1)) hA).1
        (h₀ ▸ ae_cond_mem hA)
    filter_upwards [hgeo, h0, Measure.ae_eq_of_timeMarginal_eq_dirac h₁] with γ hγ hγ₀ hγ₁
    have ht : |(t : ℝ) - ((1 : I) : ℝ)| = 1 / 2 := by norm_num [t]
    rw [mem_closedBall, ← hγ₁, mem_geodesicPaths_iff.1 hγ t 1, hγ₁, ht]
    rw [mem_closedBall] at hγ₀
    linarith
  have hball := Measure.le_iff'.1 (hle t) (closedBall 0 (1 / 2))
  simp only [distortionTau_zero_left] at hball
  rw [Measure.timeMarginal_withDensity_apply_of_ae_eq measurableSet_closedBall
      (ae_of_all _ fun _ _ ↦ rfl), hηS, mul_one, Measure.smul_apply, smul_eq_mul,
    Measure.addHaar_closedBall' _ _ (r := 1 / 2) (by norm_num), mul_left_comm,
    ENNReal.inv_mul_cancel hpos.ne' hfin.ne, mul_one] at hball
  rw [show 1 - ((t : ℝ)) = 1 / 2 by norm_num [t], ENNReal.ofReal_rpow_of_pos (by norm_num),
    ENNReal.ofReal_le_ofReal_iff (by positivity), ← Real.rpow_natCast] at hball
  exact (Real.rpow_le_rpow_left_iff_of_base_lt_one (by norm_num) (by norm_num)).1 hball

/-- **Haar measure satisfies `MCP(0, N)` exactly when `N ≥ n`.** On a real vector space of finite
dimension `n ≥ 1`, an additive Haar reference measure satisfies `MCP(0, N)` if and only if
`N ≥ n`. -/
theorem measureContraction_zero_iff_finrank_le [Nontrivial E] :
    M.MeasureContraction 0 N ↔ (finrank ℝ E : ℝ) ≤ N :=
  ⟨finrank_le_of_measureContraction_zero, measureContraction_of_nonpos_of_finrank_le le_rfl⟩

/-- Haar measure on a nontrivial real vector space of finite dimension satisfies `MCP(K, N)` for
no `K > 0` and `N > 0`: its support is the whole unbounded space, against the Bonnet–Myers
bound. -/
theorem not_measureContraction_of_pos [Nontrivial E] (hK : 0 < K) (hN : 0 < N) :
    ¬M.MeasureContraction K N := fun h ↦
  NormedSpace.unbounded_univ ℝ E (by
    simpa only [support_def, Measure.support_eq_univ] using h.isBounded_support hK hN)

end Euclidean

end MetricMeasureSpace

end TauCeti
