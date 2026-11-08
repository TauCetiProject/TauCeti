/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Pseudodifferential.OutputSupport
import TauCeti.Analysis.Pseudodifferential.Sobolev
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Composition of pseudodifferential operators

Let `a` be a symbol of order `m` with values in `W →L[ℂ] U`, and `b` a symbol of order `m'` with
values in `V →L[ℂ] W` that vanishes for positions outside a compact set
(`TauCeti.Symbol.HasCompactSpatialSupport`). The composition `Op(a) ∘ Op(b)` of their left
(Kohn–Nirenberg) quantizations is again the quantization of a symbol, of order `m + m'`: the
composition symbol

`(a # b)(x, ξ) = ∫ 𝐞 ⟪θ, x⟫ a(x, ξ + 2πθ) b̂(θ, ξ) dθ`,

where `b̂(θ, ξ)` is the Fourier transform of the position slice `y ↦ b(y, ξ)` and
`𝐞 t = exp(2πit)`. With the angular frequency `η = 2πθ` this is the classical exact formula
`(a # b)(x, ξ) = (2π)⁻ⁿ ∫ exp(i ⟪x, η⟫) a(x, ξ + η) b̂(η / 2π, ξ) dη`. It is the starting point,
not developed here, of the asymptotic expansion `a # b ∼ ∑_α (1/i)^|α|/α! ∂_ξ^α a ∂_x^α b`.

## Main declarations

* `TauCeti.Symbol.sharp`: the composition symbol `a # b`, a symbol of order `m + m'`, with
  coefficient `TauCeti.Symbol.coefficient_sharp`.
* `TauCeti.Symbol.quantizeSchwartzValue_sharp`: `Op(a # b) u = Op(a) (Op(b) u)` for Schwartz
  functions `u`, where `Op(b) u` is a test function.
* `TauCeti.Symbol.coefficient_eq_sharp_of_forall_quantizeSchwartzValue_eq`: `a # b` is the only
  symbol whose quantization is `Op(a) ∘ Op(b)`.
* `TauCeti.Symbol.spatialDeriv_sharp`, `TauCeti.Symbol.coefficient_frequencyDeriv_sharp`: the
  Leibniz rules `∂ (a # b) = ∂a # b + a # ∂b` for position and frequency derivatives.
* `TauCeti.Symbol.HasCompactSpatialSupport.sharp`: if `a` also has compact spatial support, then
  so does `a # b`.
* `TauCeti.Symbol.coefficient_const_id_sharp`: the constant symbol `1` is a left identity,
  `1 # b = b`.

## The proof

As `b` has compact spatial support, `b̂(θ, ξ)` decays faster than every power of `θ`, with growth
`⟨ξ⟩ ^ m'`, `⟨ξ⟩ = (1 + ‖ξ‖²) ^ (1 / 2)`. With Peetre's inequality
`⟨ξ + 2πθ⟩ ^ m ≤ 2 ^ (|m| / 2) ⟨ξ⟩ ^ m ⟨2πθ⟩ ^ |m|` the integrand of `a # b` is at most
`C ⟨ξ⟩ ^ (m + m') (1 + ‖θ‖) ^ (-n - 1)`. Differentiating under the integral sign gives the Leibniz
rules, a position derivative of `b` being the factor `2πi θ_j` on `b̂`, so the derivatives of
`a # b` are again composition symbols, and smoothness and the symbol estimates follow by induction.
For the composition formula, `𝓕 (Op(b) u) ζ = ∫ b̂(ζ - η, 2πη) (𝓕 u η) dη`
(`TauCeti.Symbol.HasCompactSpatialSupport.fourier_quantizeSchwartzValue`) is inserted into `Op(a)`
and the two frequency integrals are exchanged, after the shear `(η, θ) ↦ (η, η + θ)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1,
  Theorem 18.1.8.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (2.5)–(2.7).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped SchwartzMap RealInnerProductSpace ContDiff LineDeriv

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### The Fourier transform in the position of a function of two variables

The results of this section are stated for an abstract complex normed target `G` rather than for
`V →L[ℂ] W`: for the latter, the instance searches for the measurability and the norms of
`CoordinateSpace n →L[ℝ] G`-valued functions time out. -/

section FourierSlice

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  {f : CoordinateSpace n × CoordinateSpace n → G}
  {K : Set (CoordinateSpace n)}

/-- The Fourier transform `f̂(θ, ξ)` of the position slices `y ↦ f(y, ξ)` of a continuous function
vanishing for positions outside a compact set is jointly continuous in `(θ, ξ)`. -/
private theorem continuous_fourier_slice (hf : Continuous f) (hK : IsCompact K)
    (hfK : ∀ y ∉ K, ∀ η, f (y, η) = 0) :
    Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ 𝓕 (fun y ↦ f (y, q.2)) q.1 := by
  simp only [Real.fourier_eq]
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall q₀.2 1)).exists_bound_of_continuousOn
    hf.continuousOn
  have hnhds : ∀ᶠ q : CoordinateSpace n × CoordinateSpace n in nhds q₀,
      q.2 ∈ Metric.closedBall q₀.2 1 :=
    (continuous_snd.tendsto q₀).eventually (Metric.closedBall_mem_nhds _ one_pos)
  refine continuousAt_of_dominated (bound := K.indicator fun _ ↦ C)
    (Filter.Eventually.of_forall fun q ↦ ((Real.continuous_fourierChar.comp
      (by fun_prop)).smul (hf.comp (by fun_prop))).aestronglyMeasurable)
    ?_ ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (ae_of_all _ fun y ↦ ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (hf.comp (by fun_prop))).continuousAt)
  filter_upwards [hnhds] with q hq
  refine ae_of_all _ fun y ↦ ?_
  rw [Circle.norm_smul]
  by_cases hy : y ∈ K
  · rw [Set.indicator_of_mem hy]
    exact hC _ (Set.mk_mem_prod hy hq)
  · rw [Set.indicator_of_notMem hy, hfK y hy, norm_zero]

/-- **Differentiation of `f̂(θ, ξ)` in the frequency.** For a `C¹` function `f` vanishing for
positions outside a compact set, the Fourier transform of the position slices is differentiable in
the frequency, with partial derivatives the Fourier transforms of the partial derivatives:
`∂_{ξ_j} f̂(θ, ξ) = (∂_{ξ_j} f)^(θ, ξ)`. -/
private theorem hasFDerivAt_fourier_slice (hf : ContDiff ℝ 1 f) (hK : IsCompact K)
    (hfK : ∀ y ∉ K, ∀ η, f (y, η) = 0) (θ ξ : CoordinateSpace n) :
    HasFDerivAt (fun η ↦ 𝓕 (fun y ↦ f (y, η)) θ)
      (∑ j, (EuclideanSpace.proj j : CoordinateSpace n →L[ℝ] ℝ).smulRight
        (𝓕 (fun y ↦ coordinateDeriv [j] (fun η ↦ f (y, η)) ξ) θ)) ξ := by
  -- The phase factor, as a real-linear map, so that no complex scalars act on derivatives.
  set e : CoordinateSpace n → G →L[ℝ] G := fun y ↦
    ContinuousLinearMap.lsmul ℝ ℂ (𝐞 (-⟪y, θ⟫) : ℂ) with he_def
  have he : Continuous e := (ContinuousLinearMap.lsmul ℝ ℂ).continuous.comp
    (continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop)))
  have he_norm (y : CoordinateSpace n) : ‖e y‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_lsmul_apply_le _).trans (by simp)
  -- The partial derivative of `f` in the frequency is jointly continuous.
  have hD : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      fderiv ℝ (fun η ↦ f (q.1, η)) q.2 :=
    (ContDiff.fderiv (f := fun (q : CoordinateSpace n × CoordinateSpace n) η ↦ f (q.1, η))
      (hf.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)) contDiff_snd
      (n := 0) (by simp)).continuous
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall ξ 1)).exists_bound_of_continuousOn
    hD.continuousOn
  have hdiff (y η : CoordinateSpace n) : HasFDerivAt (fun η ↦ e y (f (y, η)))
      ((e y).comp (fderiv ℝ (fun η ↦ f (y, η)) η)) η :=
    (e y).hasFDerivAt.comp η
      ((hf.comp (contDiff_prodMk_right y)).differentiable one_ne_zero η).hasFDerivAt
  have hcont (η : CoordinateSpace n) : Continuous fun y ↦ e y (f (y, η)) :=
    he.clm_apply (hf.continuous.comp (continuous_id.prodMk continuous_const))
  have hcont' : Continuous fun y ↦ (e y).comp (fderiv ℝ (fun η ↦ f (y, η)) ξ) :=
    he.clm_comp (hD.comp (continuous_id.prodMk continuous_const))
  have hsupp (η : CoordinateSpace n) : HasCompactSupport fun y ↦ e y (f (y, η)) :=
    HasCompactSupport.intro hK fun y hy ↦ by simp [hfK y hy]
  have hzero (y : CoordinateSpace n) (hy : y ∉ K) (η : CoordinateSpace n) :
      fderiv ℝ (fun η ↦ f (y, η)) η = 0 := by
    have h0 : (fun η ↦ f (y, η)) = 0 := funext fun η ↦ hfK y hy η
    simp [h0]
  have hsupp' : HasCompactSupport fun y ↦ (e y).comp (fderiv ℝ (fun η ↦ f (y, η)) ξ) :=
    HasCompactSupport.intro hK fun y hy ↦ by simp [hzero y hy]
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun η y ↦ e y (f (y, η)))
    (F' := fun η y ↦ (e y).comp (fderiv ℝ (fun η ↦ f (y, η)) η))
    (bound := K.indicator fun _ ↦ C) (Metric.ball_mem_nhds ξ one_pos)
    (Filter.Eventually.of_forall fun η ↦ (hcont η).aestronglyMeasurable)
    ((hcont ξ).integrable_of_hasCompactSupport (hsupp ξ)) hcont'.aestronglyMeasurable
    (ae_of_all _ fun y η hη ↦ ?_)
    ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (ae_of_all _ fun y η _ ↦ hdiff y η)
  · have hF : (fun η ↦ 𝓕 (fun y ↦ f (y, η)) θ) = fun η ↦ ∫ y, e y (f (y, η)) := by
      funext η
      simp only [Real.fourier_eq, Circle.smul_def, he_def, ContinuousLinearMap.lsmul_apply]
    rw [hF]
    convert key using 1
    refine ContinuousLinearMap.ext fun h ↦ ?_
    have hint := hcont'.integrable_of_hasCompactSupport (μ := volume) hsupp'
    rw [ContinuousLinearMap.integral_apply hint]
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr h]
    simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply, map_sum,
      map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
      ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    rw [integral_finsetSum (f := fun j y ↦
      h j • e y (fderiv ℝ (fun η ↦ f (y, η)) ξ (EuclideanSpace.single j 1))) _
      fun j _ ↦ (hint.apply_continuousLinearMap _).smul (h j)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_smul]
    congr 1
    simp only [Real.fourier_eq, Circle.smul_def, coordinateDeriv_cons, coordinateDeriv_nil, he_def,
      ContinuousLinearMap.lsmul_apply]
  · refine ((e y).opNorm_comp_le _).trans ?_
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      exact (mul_le_of_le_one_left (norm_nonneg _) (he_norm y)).trans
        (hC _ (Set.mk_mem_prod hy (Metric.ball_subset_closedBall hη)))
    · simp [hzero y hy, Set.indicator_of_notMem hy]

end FourierSlice

/-! ### The Fourier transform of a symbol in the position -/

section SymbolFourier

variable {b : Symbol n V W m'}

/-- The Fourier transform of the position derivative `∂_{x_j} b` is `2πi θ_j b̂(θ, ξ)`. -/
private theorem HasCompactSpatialSupport.fourier_spatialDeriv (hb : b.HasCompactSpatialSupport)
    (j : Fin n) (ξ θ : CoordinateSpace n) :
    𝓕 (fun y ↦ (Symbol.spatialDeriv j b).coefficient (y, ξ)) θ =
      (2 * π * Complex.I * θ j) • 𝓕 (fun y ↦ b.coefficient (y, ξ)) θ := by
  set f := (hb.hasCompactSupport_slice ξ).toSchwartzMap (b.contDiff_coefficient_slice ξ)
  have hf : (fun y ↦ b.coefficient (y, ξ)) = ⇑f :=
    (funext (HasCompactSupport.toSchwartzMap_toFun _ _)).symm
  have hdf : (fun y ↦ (Symbol.spatialDeriv j b).coefficient (y, ξ)) =
      ⇑(∂_{EuclideanSpace.single j (1 : ℝ)} f : 𝓢(CoordinateSpace n, V →L[ℂ] W)) := by
    funext y
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, ← hf, ← fderiv_coefficient_single]
  have hg : (fun x : CoordinateSpace n ↦ ⟪x, EuclideanSpace.single j (1 : ℝ)⟫).HasTemperateGrowth :=
    ((innerSL ℝ).flip _).hasTemperateGrowth
  rw [hdf, hf, ← SchwartzMap.fourier_coe, ← SchwartzMap.fourier_coe,
    SchwartzMap.fourier_lineDerivOp_eq, smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
    EuclideanSpace.inner_single_right, smul_comm, ← Complex.coe_smul, smul_smul]
  simp [mul_comm]

end SymbolFourier


/-! ### Estimates -/

section Estimates

/-- The derivative of a symbol of order `m` in both variables is bounded by `C ⟨ζ⟩ ^ m`, locally
uniformly in the position. -/
private theorem exists_bound_fderiv_coefficient_prod (a : Symbol n W U m)
    (K : Set (CoordinateSpace n)) (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ζ, ‖fderiv ℝ a.coefficient (x, ζ)‖ ≤ C * (1 + ‖ζ‖ ^ 2) ^ (m / 2) := by
  choose C hC0 hC using fun j ↦ (spatialDeriv j a).exists_bound_coefficient K hK
  choose D hD0 hD using fun j ↦ (frequencyDeriv j a).exists_bound_coefficient K hK
  have hC0' : 0 ≤ ∑ j, C j := Finset.sum_nonneg fun j _ ↦ hC0 j
  have hD0' : 0 ≤ ∑ j, D j := Finset.sum_nonneg fun j _ ↦ hD0 j
  refine ⟨∑ j, C j + ∑ j, D j, add_nonneg hC0' hD0', fun x hx ζ ↦ ?_⟩
  have hdiff := (a.contDiff_coefficient.differentiable (by simp)) (x, ζ)
  refine (fderiv ℝ a.coefficient (x, ζ)).norm_le_sum_norm_apply_prod_single.trans ?_
  rw [add_mul, Finset.sum_mul, Finset.sum_mul]
  refine add_le_add (Finset.sum_le_sum fun j _ ↦ ?_) (Finset.sum_le_sum fun j _ ↦ ?_)
  · rw [hdiff.fderiv_apply_single_zero, ← coefficient_spatialDeriv]
    exact hC j x hx ζ
  · rw [hdiff.fderiv_apply_zero_single, ← coefficient_frequencyDeriv]
    exact (hD j x hx ζ).trans
      (mul_le_mul_of_nonneg_left (rpow_weight_le_rpow_weight ζ (by linarith)) (hD0 j))

variable {b : Symbol n V W m'}

/-- **The basic estimate.** For a symbol `b` with compact spatial support, Peetre's inequality and
the rapid decay of `b̂` in `θ` give, for every real `s` and every `k`,
`⟨ξ + 2πθ⟩ ^ s ‖b̂(θ, ξ)‖ ≤ C ⟨ξ⟩ ^ (s + m') (1 + ‖θ‖) ^ (-k)`. -/
private theorem HasCompactSpatialSupport.exists_rpow_mul_norm_fourier_le
    (hb : b.HasCompactSpatialSupport) (s : ℝ) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ ξ θ : CoordinateSpace n,
      (1 + ‖ξ + (2 * π) • θ‖ ^ 2) ^ (s / 2) * ‖𝓕 (fun y ↦ b.coefficient (y, ξ)) θ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((s + m') / 2) * (1 + ‖θ‖) ^ (-(k : ℝ)) := by
  obtain ⟨Cb, hCb0, hCb⟩ := hb.exists_one_add_norm_pow_mul_norm_fourier_le (⌈|s|⌉₊ + k)
  refine ⟨2 ^ (|s| / 2) * (2 * π) ^ |s| * Cb, by positivity, fun ξ θ ↦ ?_⟩
  have hw : 0 < 1 + ‖θ‖ := by positivity
  have hscale : (1 + ‖(2 * π) • θ‖ ^ 2) ^ (|s| / 2) ≤ (2 * π) ^ |s| * (1 + ‖θ‖) ^ ⌈|s|⌉₊ := by
    refine (one_add_norm_sq_rpow_le_of_norm_eq_mul (c := 2 * π) (x := (2 * π) • θ) (y := θ)
      (by linarith [Real.two_le_pi]) |s|
      (by rw [norm_smul, Real.norm_of_nonneg (by positivity)])).trans ?_
    rw [abs_abs]
    gcongr
    exact one_add_norm_sq_rpow_le_one_add_norm_pow θ (abs_nonneg s) (Nat.le_ceil _)
  have hsplit : (1 + ‖θ‖) ^ ⌈|s|⌉₊ = (1 + ‖θ‖) ^ (-(k : ℝ)) * (1 + ‖θ‖) ^ (⌈|s|⌉₊ + k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hw]
    congr 1
    push_cast
    ring
  calc (1 + ‖ξ + (2 * π) • θ‖ ^ 2) ^ (s / 2) * ‖𝓕 (fun y ↦ b.coefficient (y, ξ)) θ‖
      ≤ 2 ^ (|s| / 2) * (1 + ‖ξ‖ ^ 2) ^ (s / 2) * ((2 * π) ^ |s| * (1 + ‖θ‖) ^ ⌈|s|⌉₊) *
          ‖𝓕 (fun y ↦ b.coefficient (y, ξ)) θ‖ := by
        gcongr
        exact (one_add_norm_add_sq_rpow_le_mul s ξ ((2 * π) • θ)).trans (by gcongr)
    _ = 2 ^ (|s| / 2) * (2 * π) ^ |s| * (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖θ‖) ^ (-(k : ℝ)) *
          ((1 + ‖θ‖) ^ (⌈|s|⌉₊ + k) * ‖𝓕 (fun y ↦ b.coefficient (y, ξ)) θ‖) := by
        rw [hsplit]
        ring
    _ ≤ 2 ^ (|s| / 2) * (2 * π) ^ |s| * (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖θ‖) ^ (-(k : ℝ)) *
          (Cb * (1 + ‖ξ‖ ^ 2) ^ (m' / 2)) :=
        mul_le_mul_of_nonneg_left (hCb θ ξ) (by positivity)
    _ = _ := by
        rw [add_div, Real.rpow_add (by positivity)]
        ring

/-- The basic estimate for frequencies in a bounded set, for `b̂` together with its frequency
derivatives. -/
private theorem HasCompactSpatialSupport.exists_rpow_mul_norm_fourier_le_of_norm_le
    (hb : b.HasCompactSpatialSupport) (s : ℝ) (k : ℕ) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ ξ θ : CoordinateSpace n, ‖ξ‖ ≤ R →
      (1 + ‖ξ + (2 * π) • θ‖ ^ 2) ^ (s / 2) * (‖𝓕 (fun y ↦ b.coefficient (y, ξ)) θ‖ +
        ∑ j, ‖𝓕 (fun y ↦ (Symbol.frequencyDeriv j b).coefficient (y, ξ)) θ‖) ≤
        C * (1 + ‖θ‖) ^ (-(k : ℝ)) := by
  obtain ⟨C₀, hC₀, h₀⟩ := hb.exists_rpow_mul_norm_fourier_le s k
  choose C hC hC' using fun j ↦ (hb.frequencyDeriv j).exists_rpow_mul_norm_fourier_le s k
  set M₀ := (1 + R ^ 2) ^ (|s + m'| / 2)
  set M := (1 + R ^ 2) ^ (|s + (m' - 1)| / 2)
  refine ⟨C₀ * M₀ + ∑ j, C j * M, add_nonneg (mul_nonneg hC₀ (by positivity))
    (Finset.sum_nonneg fun j _ ↦ mul_nonneg (hC j) (by positivity)), fun ξ θ hξ ↦ ?_⟩
  have hw := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖θ‖) (-(k : ℝ))
  rw [mul_add, Finset.mul_sum, add_mul, Finset.sum_mul]
  refine add_le_add ((h₀ ξ θ).trans ?_) (Finset.sum_le_sum fun j _ ↦ (hC' j ξ θ).trans ?_)
  · gcongr
    exact one_add_norm_sq_rpow_le_of_norm_le hξ _
  · gcongr
    · exact hC j
    · exact one_add_norm_sq_rpow_le_of_norm_le hξ _

end Estimates

/-! ### Differentiation under the composition integral -/

section PhaseIntegral

variable {G₁ G₂ G₃ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁] [NormedAddCommGroup G₂]
  [NormedSpace ℝ G₂] [NormedAddCommGroup G₃] [NormedSpace ℝ G₃] [NormedSpace ℂ G₃]
  [IsScalarTower ℝ ℂ G₃]
  (B : G₁ →L[ℝ] G₂ →L[ℝ] G₃) {A : CoordinateSpace n × CoordinateSpace n → G₁}
  {Bh : CoordinateSpace n → CoordinateSpace n → G₂}
  {DBh : CoordinateSpace n → CoordinateSpace n → CoordinateSpace n →L[ℝ] G₂}

/-- The derivative in `p = (x, ξ)` of the integrand
`𝐞 ⟪θ, x⟫ • B (A (x, ξ + 2πθ)) (Bh θ ξ)` of the composition integral, written with real-linear
maps only. -/
private def phaseIntegrandFDeriv (A : CoordinateSpace n × CoordinateSpace n → G₁)
    (Bh : CoordinateSpace n → CoordinateSpace n → G₂)
    (DBh : CoordinateSpace n → CoordinateSpace n → CoordinateSpace n →L[ℝ] G₂)
    (θ : CoordinateSpace n) (p : CoordinateSpace n × CoordinateSpace n) :
    CoordinateSpace n × CoordinateSpace n →L[ℝ] G₃ :=
  (ContinuousLinearMap.lsmul ℝ ℂ (𝐞 ⟪θ, p.1⟫ : ℂ)).comp
      ((B.flip (Bh θ p.2)).comp (fderiv ℝ A (p.1, p.2 + (2 * π) • θ)) +
        (B (A (p.1, p.2 + (2 * π) • θ))).comp
          ((DBh θ p.2).comp (ContinuousLinearMap.snd ℝ _ _))) +
    ((innerSL ℝ θ).comp (ContinuousLinearMap.fst ℝ _ _)).smulRight
      ((2 * π * Complex.I * 𝐞 ⟪θ, p.1⟫) • B (A (p.1, p.2 + (2 * π) • θ)) (Bh θ p.2))

private theorem phaseIntegrandFDeriv_apply (θ : CoordinateSpace n)
    (p h : CoordinateSpace n × CoordinateSpace n) :
    phaseIntegrandFDeriv B A Bh DBh θ p h =
      (𝐞 ⟪θ, p.1⟫ : ℂ) • (B (fderiv ℝ A (p.1, p.2 + (2 * π) • θ) h) (Bh θ p.2) +
        B (A (p.1, p.2 + (2 * π) • θ)) (DBh θ p.2 h.2)) +
      (2 * π * Complex.I * ⟪θ, h.1⟫ * 𝐞 ⟪θ, p.1⟫) • B (A (p.1, p.2 + (2 * π) • θ)) (Bh θ p.2) := by
  simp only [phaseIntegrandFDeriv, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, ← smul_assoc, Complex.real_smul]
  congr 2
  ring

/-- The integrand of the composition integral has the derivative `phaseIntegrandFDeriv`. -/
private theorem hasFDerivAt_phaseIntegrand (hA : ContDiff ℝ 1 A)
    (hBh : ∀ θ ξ, HasFDerivAt (Bh θ) (DBh θ ξ) ξ) (θ : CoordinateSpace n)
    (p : CoordinateSpace n × CoordinateSpace n) :
    HasFDerivAt (fun p : CoordinateSpace n × CoordinateSpace n ↦
        (𝐞 ⟪θ, p.1⟫ : ℂ) • B (A (p.1, p.2 + (2 * π) • θ)) (Bh θ p.2))
      (phaseIntegrandFDeriv B A Bh DBh θ p) p := by
  have hshift : HasFDerivAt (fun p : CoordinateSpace n × CoordinateSpace n ↦
      (p.1, p.2 + (2 * π) • θ)) (ContinuousLinearMap.id ℝ _) p := by
    convert (hasFDerivAt_id p).add_const ((0 : CoordinateSpace n), (2 * π) • θ) using 1
    funext q
    ext <;> simp
  have hAq := ((hA.differentiable one_ne_zero _).hasFDerivAt).comp p hshift
  have hBq := (hBh θ p.2).comp p hasFDerivAt_snd
  have hv := B.hasFDerivAt_of_bilinear hAq hBq
  have hc : HasFDerivAt (fun p : CoordinateSpace n × CoordinateSpace n ↦ (𝐞 ⟪θ, p.1⟫ : ℂ))
      ((ContinuousLinearMap.toSpanSingleton ℝ (2 * π * Complex.I * 𝐞 ⟪θ, p.1⟫)).comp
        ((innerSL ℝ θ).comp (ContinuousLinearMap.fst ℝ _ _))) p := by
    have := (Real.hasDerivAt_fourierChar ⟪θ, p.1⟫).hasFDerivAt.comp p
      ((innerSL ℝ θ).comp (ContinuousLinearMap.fst ℝ _ _)).hasFDerivAt
    exact this
  have hF := (ContinuousLinearMap.lsmul ℝ ℂ).hasFDerivAt_of_bilinear hc hv
  simp only [ContinuousLinearMap.lsmul_apply] at hF
  refine hF.congr_fderiv (ContinuousLinearMap.ext fun h ↦ ?_)
  rw [phaseIntegrandFDeriv_apply]
  simp only [add_apply, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lsmul_apply, map_add, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.id_apply, Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply, smul_add, ← Complex.coe_smul]
  congr 1
  · exact add_comm _ _
  · rw [smul_eq_mul]
    ring_nf

/-- **Differentiation under the composition integral.** If the integrand
`𝐞 ⟪θ, x⟫ • B (A (x, ξ + 2πθ)) (Bh θ ξ)` and its derivative are dominated, for `(x, ξ)` near `p₀`,
by an integrable function `g` of `θ`, then the integral is differentiable at `p₀`, with derivative
the integral of the derivatives. -/
private theorem hasFDerivAt_integral_phaseIntegrand (hA : ContDiff ℝ 1 A)
    (hBh : ∀ θ ξ, HasFDerivAt (Bh θ) (DBh θ ξ) ξ)
    (hBc : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ Bh q.1 q.2)
    (hDc : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ DBh q.1 q.2)
    {p₀ : CoordinateSpace n × CoordinateSpace n} {g : CoordinateSpace n → ℝ} (hg : Integrable g)
    (hbound : ∀ θ, ∀ p ∈ Metric.ball p₀ 1, (1 + ‖θ‖) * ((‖A (p.1, p.2 + (2 * π) • θ)‖ +
        ‖fderiv ℝ A (p.1, p.2 + (2 * π) • θ)‖) *
          (‖Bh θ p.2‖ + ∑ j, ‖DBh θ p.2 (EuclideanSpace.single j 1)‖)) ≤ g θ) :
    ∃ D : CoordinateSpace n × CoordinateSpace n →L[ℝ] G₃,
      HasFDerivAt (fun p : CoordinateSpace n × CoordinateSpace n ↦
          ∫ θ, (𝐞 ⟪θ, p.1⟫ : ℂ) • B (A (p.1, p.2 + (2 * π) • θ)) (Bh θ p.2)) D p₀ ∧
      ∀ h, D h = ∫ θ, ((𝐞 ⟪θ, p₀.1⟫ : ℂ) • (B (fderiv ℝ A (p₀.1, p₀.2 + (2 * π) • θ) h)
          (Bh θ p₀.2) + B (A (p₀.1, p₀.2 + (2 * π) • θ)) (DBh θ p₀.2 h.2)) +
        (2 * π * Complex.I * ⟪θ, h.1⟫ * 𝐞 ⟪θ, p₀.1⟫) •
          B (A (p₀.1, p₀.2 + (2 * π) • θ)) (Bh θ p₀.2)) := by
  have he (x : CoordinateSpace n) : Continuous fun θ : CoordinateSpace n ↦ (𝐞 ⟪θ, x⟫ : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hAθ (p : CoordinateSpace n × CoordinateSpace n) :
      Continuous fun θ : CoordinateSpace n ↦ A (p.1, p.2 + (2 * π) • θ) :=
    hA.continuous.comp (by fun_prop)
  have hfAθ (p : CoordinateSpace n × CoordinateSpace n) :
      Continuous fun θ : CoordinateSpace n ↦ fderiv ℝ A (p.1, p.2 + (2 * π) • θ) :=
    (hA.continuous_fderiv one_ne_zero).comp (by fun_prop)
  have hBθ (ξ : CoordinateSpace n) : Continuous fun θ ↦ Bh θ ξ :=
    hBc.comp (continuous_id.prodMk continuous_const)
  have hDθ (ξ : CoordinateSpace n) : Continuous fun θ ↦ DBh θ ξ :=
    hDc.comp (continuous_id.prodMk continuous_const)
  have hcont (p : CoordinateSpace n × CoordinateSpace n) : Continuous fun θ : CoordinateSpace n ↦
      (𝐞 ⟪θ, p.1⟫ : ℂ) • B (A (p.1, p.2 + (2 * π) • θ)) (Bh θ p.2) :=
    (he p.1).smul ((B.continuous.comp (hAθ p)).clm_apply (hBθ p.2))
  have hcont' : Continuous fun θ ↦ phaseIntegrandFDeriv B A Bh DBh θ p₀ := by
    refine continuous_clm_apply.2 fun h ↦ ?_
    simp only [phaseIntegrandFDeriv_apply]
    refine ((he p₀.1).smul ((((B.continuous.comp ((hfAθ p₀).clm_apply continuous_const)).clm_apply
      (hBθ p₀.2))).add ((B.continuous.comp (hAθ p₀)).clm_apply
        ((hDθ p₀.2).clm_apply continuous_const)))).add ?_
    have hi : Continuous fun θ : CoordinateSpace n ↦ (⟪θ, h.1⟫ : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)
    exact ((continuous_const.mul hi).mul (he p₀.1)).smul
      ((B.continuous.comp (hAθ p₀)).clm_apply (hBθ p₀.2))
  -- The pointwise bounds.
  have hB0 : 0 ≤ ‖B‖ := norm_nonneg B
  have hnorm (θ : CoordinateSpace n) (p : CoordinateSpace n × CoordinateSpace n) :
      ‖(𝐞 ⟪θ, p.1⟫ : ℂ) • B (A (p.1, p.2 + (2 * π) • θ)) (Bh θ p.2)‖ ≤
        ‖B‖ * ((1 + ‖θ‖) * ((‖A (p.1, p.2 + (2 * π) • θ)‖ +
          ‖fderiv ℝ A (p.1, p.2 + (2 * π) • θ)‖) *
            (‖Bh θ p.2‖ + ∑ j, ‖DBh θ p.2 (EuclideanSpace.single j 1)‖))) := by
    rw [norm_smul, Circle.norm_coe, one_mul]
    refine (B.le_opNorm₂ _ _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hB0
    have h1 : 1 ≤ 1 + ‖θ‖ := le_add_of_nonneg_right (norm_nonneg θ)
    have h2 := norm_nonneg (fderiv ℝ A (p.1, p.2 + (2 * π) • θ))
    have h3 : 0 ≤ ∑ j, ‖DBh θ p.2 (EuclideanSpace.single j 1)‖ := by positivity
    have h4 := norm_nonneg (A (p.1, p.2 + (2 * π) • θ))
    have h5 := norm_nonneg (Bh θ p.2)
    nlinarith [mul_nonneg h4 h5, mul_nonneg (add_nonneg h4 h2) (add_nonneg h5 h3)]
  have hnorm' (θ : CoordinateSpace n) (p : CoordinateSpace n × CoordinateSpace n) :
      ‖phaseIntegrandFDeriv B A Bh DBh θ p‖ ≤
        (1 + 2 * π) * ‖B‖ * ((1 + ‖θ‖) * ((‖A (p.1, p.2 + (2 * π) • θ)‖ +
          ‖fderiv ℝ A (p.1, p.2 + (2 * π) • θ)‖) *
            (‖Bh θ p.2‖ + ∑ j, ‖DBh θ p.2 (EuclideanSpace.single j 1)‖))) := by
    have hDB : ‖DBh θ p.2‖ ≤ ∑ j, ‖DBh θ p.2 (EuclideanSpace.single j 1)‖ :=
      (DBh θ p.2).norm_le_sum_norm_apply_single
    set a := ‖A (p.1, p.2 + (2 * π) • θ)‖
    set a' := ‖fderiv ℝ A (p.1, p.2 + (2 * π) • θ)‖
    set β := ‖Bh θ p.2‖
    set β' := ∑ j, ‖DBh θ p.2 (EuclideanSpace.single j 1)‖
    have ha := norm_nonneg (A (p.1, p.2 + (2 * π) • θ))
    have ha' := norm_nonneg (fderiv ℝ A (p.1, p.2 + (2 * π) • θ))
    have hβ := norm_nonneg (Bh θ p.2)
    have hβ' : 0 ≤ β' := by positivity
    have hθ := norm_nonneg θ
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
    rw [phaseIntegrandFDeriv_apply]
    have hh2 : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
    have hi : ‖(2 * π * Complex.I * ⟪θ, h.1⟫ * 𝐞 ⟪θ, p.1⟫ : ℂ)‖ ≤ 2 * π * (‖θ‖ * ‖h‖) := by
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg pi_pos.le,
        Complex.norm_I, mul_one, Circle.norm_coe, Real.norm_eq_abs]
      gcongr
      exact (abs_real_inner_le_norm θ h.1).trans (by gcongr; exact norm_fst_le h)
    have t1 : ‖B (fderiv ℝ A (p.1, p.2 + (2 * π) • θ) h) (Bh θ p.2)‖ ≤ ‖B‖ * (a' * ‖h‖) * β :=
      (B.le_opNorm₂ _ _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)
    have t2 : ‖B (A (p.1, p.2 + (2 * π) • θ)) (DBh θ p.2 h.2)‖ ≤ ‖B‖ * a * (β' * ‖h‖) :=
      (B.le_opNorm₂ _ _).trans
        (by gcongr; exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr))
    have t3 : ‖B (A (p.1, p.2 + (2 * π) • θ)) (Bh θ p.2)‖ ≤ ‖B‖ * a * β := B.le_opNorm₂ _ _
    calc _ ≤ ‖(𝐞 ⟪θ, p.1⟫ : ℂ) • (B (fderiv ℝ A (p.1, p.2 + (2 * π) • θ) h) (Bh θ p.2) +
            B (A (p.1, p.2 + (2 * π) • θ)) (DBh θ p.2 h.2))‖ +
          ‖(2 * π * Complex.I * ⟪θ, h.1⟫ * 𝐞 ⟪θ, p.1⟫ : ℂ)‖ *
            ‖B (A (p.1, p.2 + (2 * π) • θ)) (Bh θ p.2)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul (2 * π * Complex.I * ⟪θ, h.1⟫ * 𝐞 ⟪θ, p.1⟫ : ℂ)]
      _ ≤ (‖B‖ * (a' * ‖h‖) * β + ‖B‖ * a * (β' * ‖h‖)) +
          2 * π * (‖θ‖ * ‖h‖) * (‖B‖ * a * β) := by
          rw [norm_smul, Circle.norm_coe, one_mul]
          gcongr
          exact (norm_add_le _ _).trans (add_le_add t1 t2)
      _ = ‖B‖ * ((a' * β + a * β') + 2 * π * (‖θ‖ * (a * β))) * ‖h‖ := by ring
      _ ≤ ‖B‖ * ((1 + 2 * π) * ((1 + ‖θ‖) * ((a + a') * (β + β')))) * ‖h‖ := by
          gcongr
          nlinarith [mul_nonneg ha hβ, mul_nonneg ha' hβ, mul_nonneg ha hβ', mul_nonneg ha' hβ',
            mul_nonneg hθ (mul_nonneg ha hβ), mul_nonneg hθ (mul_nonneg ha' hβ),
            mul_nonneg hθ (mul_nonneg ha hβ'), mul_nonneg hθ (mul_nonneg ha' hβ'), pi_pos]
      _ = _ := by ring
  have hp₀ : p₀ ∈ Metric.ball p₀ 1 := Metric.mem_ball_self one_pos
  have hint' : Integrable (fun θ ↦ phaseIntegrandFDeriv B A Bh DBh θ p₀) :=
    (hg.const_mul ((1 + 2 * π) * ‖B‖)).mono' hcont'.aestronglyMeasurable
      (ae_of_all _ fun θ ↦ (hnorm' θ p₀).trans (by gcongr; exact hbound θ p₀ hp₀))
  refine ⟨_, hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds p₀ one_pos)
    (Filter.Eventually.of_forall fun p ↦ (hcont p).aestronglyMeasurable)
    ((hg.const_mul ‖B‖).mono' (hcont p₀).aestronglyMeasurable
      (ae_of_all _ fun θ ↦ (hnorm θ p₀).trans (by gcongr; exact hbound θ p₀ hp₀)))
    hcont'.aestronglyMeasurable
    (ae_of_all _ fun θ p hp ↦ (hnorm' θ p).trans (by gcongr; exact hbound θ p hp))
    (hg.const_mul ((1 + 2 * π) * ‖B‖))
    (ae_of_all _ fun θ p _ ↦ hasFDerivAt_phaseIntegrand B hA hBh θ p), fun h ↦ ?_⟩
  rw [ContinuousLinearMap.integral_apply hint']
  simp only [phaseIntegrandFDeriv_apply]

end PhaseIntegral


/-! ### The coefficient of the composition symbol -/

section SharpCoeff

variable {b : Symbol n V W m'}

/-- The Fourier transform `b̂(θ, ξ)` of the position slice `y ↦ b(y, ξ)` at `θ`. -/
private def fourierSlice (b : Symbol n V W m') (θ ξ : CoordinateSpace n) : V →L[ℂ] W :=
  𝓕 (fun y ↦ b.coefficient (y, ξ)) θ

/-- The frequency derivative of `b̂(θ, ξ)`, assembled from the Fourier transforms of the frequency
derivatives of `b`. -/
private def fourierSliceDeriv (b : Symbol n V W m') (θ ξ : CoordinateSpace n) :
    CoordinateSpace n →L[ℝ] (V →L[ℂ] W) :=
  ∑ j, (EuclideanSpace.proj j : CoordinateSpace n →L[ℝ] ℝ).smulRight
    (fourierSlice (Symbol.frequencyDeriv j b) θ ξ)

/-- The coefficient `(a # b)(x, ξ) = ∫ 𝐞 ⟪θ, x⟫ a(x, ξ + 2πθ) b̂(θ, ξ) dθ` of the composition
symbol. -/
private def sharpCoeff (a : Symbol n W U m) (b : Symbol n V W m')
    (p : CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] U :=
  ∫ θ, (𝐞 ⟪θ, p.1⟫ : ℂ) • (a.coefficient (p.1, p.2 + (2 * π) • θ)).comp (fourierSlice b θ p.2)

private theorem HasCompactSpatialSupport.continuous_fourierSlice (hb : b.HasCompactSpatialSupport) :
    Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ fourierSlice b q.1 q.2 := by
  obtain ⟨K, hK, hKb⟩ := hasCompactSpatialSupport_iff.mp hb
  exact continuous_fourier_slice b.contDiff_coefficient.continuous hK hKb

private theorem HasCompactSpatialSupport.continuous_fourierSliceDeriv
    (hb : b.HasCompactSpatialSupport) :
    Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ fourierSliceDeriv b q.1 q.2 := by
  refine continuous_clm_apply.2 fun h ↦ ?_
  simp only [fourierSliceDeriv, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.proj_apply]
  exact continuous_finsetSum _ fun j _ ↦
    (hb.frequencyDeriv j).continuous_fourierSlice.const_smul (h j)

private theorem HasCompactSpatialSupport.hasFDerivAt_fourierSlice (hb : b.HasCompactSpatialSupport)
    (θ ξ : CoordinateSpace n) :
    HasFDerivAt (fourierSlice b θ) (fourierSliceDeriv b θ ξ) ξ := by
  obtain ⟨K, hK, hKb⟩ := hasCompactSpatialSupport_iff.mp hb
  have h := hasFDerivAt_fourier_slice (b.contDiff_coefficient.of_le (by simp)) hK hKb θ ξ
  simp only [← coefficient_frequencyDeriv] at h
  exact h

private theorem continuous_sharpIntegrand (a : Symbol n W U m) (hb : b.HasCompactSpatialSupport)
    (p : CoordinateSpace n × CoordinateSpace n) :
    Continuous fun θ ↦ (𝐞 ⟪θ, p.1⟫ : ℂ) •
      (a.coefficient (p.1, p.2 + (2 * π) • θ)).comp (fourierSlice b θ p.2) := by
  have he : Continuous fun θ : CoordinateSpace n ↦ (𝐞 ⟪θ, p.1⟫ : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_id.inner continuous_const))
  have hq : Continuous fun θ : CoordinateSpace n ↦ (p.1, p.2 + (2 * π) • θ) :=
    continuous_const.prodMk (continuous_const.add (continuous_const_smul _))
  have ha : Continuous fun θ ↦ a.coefficient (p.1, p.2 + (2 * π) • θ) :=
    a.contDiff_coefficient.continuous.comp hq
  have hbc : Continuous fun θ ↦ fourierSlice b θ p.2 :=
    hb.continuous_fourierSlice.comp₂ continuous_id continuous_const
  exact he.smul (ha.clm_comp hbc)

/-- The integrand of `a # b` decays faster than every power of `θ`, with the weight
`⟨ξ⟩ ^ (m + m')` of a symbol of order `m + m'`. -/
private theorem exists_norm_sharpIntegrand_le (a : Symbol n W U m)
    (hb : b.HasCompactSpatialSupport) (K : Set (CoordinateSpace n)) (hK : IsCompact K) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ θ : CoordinateSpace n,
      ‖(𝐞 ⟪θ, x⟫ : ℂ) • (a.coefficient (x, ξ + (2 * π) • θ)).comp (fourierSlice b θ ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m + m') / 2) * (1 + ‖θ‖) ^ (-(k : ℝ)) := by
  obtain ⟨Ca, hCa0, hCa⟩ := a.exists_bound_coefficient K hK
  obtain ⟨C, hC0, hC⟩ := hb.exists_rpow_mul_norm_fourier_le m k
  refine ⟨Ca * C, mul_nonneg hCa0 hC0, fun x hx ξ θ ↦ ?_⟩
  rw [norm_smul, Circle.norm_coe, one_mul]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc ‖a.coefficient (x, ξ + (2 * π) • θ)‖ * ‖fourierSlice b θ ξ‖
      ≤ Ca * ((1 + ‖ξ + (2 * π) • θ‖ ^ 2) ^ (m / 2) * ‖fourierSlice b θ ξ‖) := by
        rw [← mul_assoc]
        gcongr
        exact hCa x hx _
    _ ≤ Ca * (C * (1 + ‖ξ‖ ^ 2) ^ ((m + m') / 2) * (1 + ‖θ‖) ^ (-(k : ℝ))) :=
        mul_le_mul_of_nonneg_left (hC ξ θ) hCa0
    _ = _ := by ring

private theorem integrable_one_add_norm_rpow_neg_succ :
    Integrable fun θ : CoordinateSpace n ↦ (1 + ‖θ‖) ^ (-((n + 1 : ℕ) : ℝ)) :=
  integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; push_cast; linarith)

private theorem integrable_sharpIntegrand (a : Symbol n W U m) (hb : b.HasCompactSpatialSupport)
    (p : CoordinateSpace n × CoordinateSpace n) :
    Integrable fun θ ↦ (𝐞 ⟪θ, p.1⟫ : ℂ) •
      (a.coefficient (p.1, p.2 + (2 * π) • θ)).comp (fourierSlice b θ p.2) := by
  obtain ⟨C, -, hC⟩ := exists_norm_sharpIntegrand_le a hb {p.1} isCompact_singleton (n + 1)
  exact (integrable_one_add_norm_rpow_neg_succ.const_mul _).mono'
    (continuous_sharpIntegrand a hb p).aestronglyMeasurable
    (ae_of_all _ fun θ ↦ hC p.1 rfl p.2 θ)

/-- The coefficient of `a # b` has the growth `⟨ξ⟩ ^ (m + m')` of a symbol of order `m + m'`,
locally uniformly in the position. -/
private theorem exists_norm_sharpCoeff_le (a : Symbol n W U m) (hb : b.HasCompactSpatialSupport)
    (K : Set (CoordinateSpace n)) (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖sharpCoeff a b (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m + m') / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_sharpIntegrand_le a hb K hK (n + 1)
  refine ⟨C * ∫ θ : CoordinateSpace n, (1 + ‖θ‖) ^ (-((n + 1 : ℕ) : ℝ)),
    mul_nonneg hC0 (integral_nonneg fun _ ↦ by positivity), fun x hx ξ ↦ ?_⟩
  refine (norm_integral_le_of_norm_le (integrable_one_add_norm_rpow_neg_succ.const_mul _)
    (ae_of_all _ fun θ ↦ hC x hx ξ θ)).trans_eq ?_
  rw [integral_const_mul]
  ring

private theorem fourierSliceDeriv_apply_single (θ ξ : CoordinateSpace n) (j : Fin n) :
    fourierSliceDeriv b θ ξ (EuclideanSpace.single j 1) =
      fourierSlice (Symbol.frequencyDeriv j b) θ ξ := by
  simp [fourierSliceDeriv, PiLp.single_apply]

/-- **Differentiation of `a # b`.** The coefficient of the composition symbol is differentiable,
with derivative the integral of the derivative of the integrand. -/
private theorem hasFDerivAt_sharpCoeff (a : Symbol n W U m) (hb : b.HasCompactSpatialSupport)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    ∃ D : CoordinateSpace n × CoordinateSpace n →L[ℝ] (V →L[ℂ] U),
      HasFDerivAt (sharpCoeff a b) D p₀ ∧
      ∀ h, D h = ∫ θ, ((𝐞 ⟪θ, p₀.1⟫ : ℂ) •
          ((fderiv ℝ a.coefficient (p₀.1, p₀.2 + (2 * π) • θ) h).comp (fourierSlice b θ p₀.2) +
            (a.coefficient (p₀.1, p₀.2 + (2 * π) • θ)).comp (fourierSliceDeriv b θ p₀.2 h.2)) +
        (2 * π * Complex.I * ⟪θ, h.1⟫ * 𝐞 ⟪θ, p₀.1⟫) •
          (a.coefficient (p₀.1, p₀.2 + (2 * π) • θ)).comp (fourierSlice b θ p₀.2)) := by
  obtain ⟨Ca, hCa0, hCa⟩ :=
    a.exists_bound_coefficient (Metric.closedBall p₀.1 1) (isCompact_closedBall _ _)
  obtain ⟨Cf, hCf0, hCf⟩ :=
    exists_bound_fderiv_coefficient_prod a (Metric.closedBall p₀.1 1) (isCompact_closedBall _ _)
  obtain ⟨C, hC0, hC⟩ := hb.exists_rpow_mul_norm_fourier_le_of_norm_le m (n + 2) (‖p₀.2‖ + 1)
  have key := hasFDerivAt_integral_phaseIntegrand
    ((ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ) (A := a.coefficient)
    (Bh := fourierSlice b) (DBh := fourierSliceDeriv b) (a.contDiff_coefficient.of_le (by simp))
    hb.hasFDerivAt_fourierSlice hb.continuous_fourierSlice hb.continuous_fourierSliceDeriv
    (p₀ := p₀) (g := fun θ ↦ (Ca + Cf) * C * (1 + ‖θ‖) ^ (-((n + 1 : ℕ) : ℝ)))
    (integrable_one_add_norm_rpow_neg_succ.const_mul _) (fun θ p hp ↦ ?_)
  · simp only [ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
      ContinuousLinearMap.compL_apply] at key
    exact key
  · have hdist : dist p p₀ < 1 := hp
    have hx : p.1 ∈ Metric.closedBall p₀.1 1 :=
      Metric.mem_closedBall.2 ((le_max_left _ _).trans hdist.le)
    have hξ : ‖p.2‖ ≤ ‖p₀.2‖ + 1 := by
      have := (norm_le_insert' p.2 p₀.2)
      have h2 : ‖p.2 - p₀.2‖ ≤ 1 := by
        rw [← dist_eq_norm]
        exact (le_max_right _ _).trans hdist.le
      linarith
    have hw : (1 + ‖θ‖) * (1 + ‖θ‖) ^ (-((n + 2 : ℕ) : ℝ)) =
        (1 + ‖θ‖) ^ (-((n + 1 : ℕ) : ℝ)) := by
      rw [mul_comm, ← Real.rpow_add_one (by positivity)]
      congr 1
      push_cast
      ring
    simp only [fourierSliceDeriv_apply_single]
    have hA : ‖a.coefficient (p.1, p.2 + (2 * π) • θ)‖ +
        ‖fderiv ℝ a.coefficient (p.1, p.2 + (2 * π) • θ)‖ ≤
          (Ca + Cf) * (1 + ‖p.2 + (2 * π) • θ‖ ^ 2) ^ (m / 2) := by
      rw [add_mul]
      exact add_le_add (hCa _ hx _) (hCf _ hx _)
    have hB := hC p.2 θ hξ
    simp only [fourierSlice] at hB ⊢
    calc (1 + ‖θ‖) * ((‖a.coefficient (p.1, p.2 + (2 * π) • θ)‖ +
          ‖fderiv ℝ a.coefficient (p.1, p.2 + (2 * π) • θ)‖) *
          (‖𝓕 (fun y ↦ b.coefficient (y, p.2)) θ‖ +
            ∑ j, ‖𝓕 (fun y ↦ (Symbol.frequencyDeriv j b).coefficient (y, p.2)) θ‖))
        ≤ (1 + ‖θ‖) * ((Ca + Cf) * ((1 + ‖p.2 + (2 * π) • θ‖ ^ 2) ^ (m / 2) *
          (‖𝓕 (fun y ↦ b.coefficient (y, p.2)) θ‖ +
            ∑ j, ‖𝓕 (fun y ↦ (Symbol.frequencyDeriv j b).coefficient (y, p.2)) θ‖))) := by
          rw [← mul_assoc (Ca + Cf)]
          gcongr
      _ ≤ (1 + ‖θ‖) * ((Ca + Cf) * (C * (1 + ‖θ‖) ^ (-((n + 2 : ℕ) : ℝ)))) := by
          gcongr
      _ = (Ca + Cf) * C * (1 + ‖θ‖) ^ (-((n + 1 : ℕ) : ℝ)) := by
          rw [← hw]
          ring

private theorem differentiable_sharpCoeff (a : Symbol n W U m) (hb : b.HasCompactSpatialSupport) :
    Differentiable ℝ (sharpCoeff a b) := fun p ↦ by
  obtain ⟨D, hD, -⟩ := hasFDerivAt_sharpCoeff a hb p
  exact hD.differentiableAt

/-- **Leibniz rule in the position.** `∂_{x_j} (a # b) = (∂_{x_j} a) # b + a # (∂_{x_j} b)`. -/
private theorem fderiv_sharpCoeff_apply_inl (a : Symbol n W U m) (hb : b.HasCompactSpatialSupport)
    (p : CoordinateSpace n × CoordinateSpace n) (j : Fin n) :
    fderiv ℝ (sharpCoeff a b) p (EuclideanSpace.single j 1, 0) =
      sharpCoeff (Symbol.spatialDeriv j a) b p + sharpCoeff a (Symbol.spatialDeriv j b) p := by
  obtain ⟨D, hD, hDapp⟩ := hasFDerivAt_sharpCoeff a hb p
  rw [hD.fderiv, hDapp, sharpCoeff, sharpCoeff, ← integral_add
    (integrable_sharpIntegrand _ hb p) (integrable_sharpIntegrand a (hb.spatialDeriv j) p)]
  refine integral_congr_ae (ae_of_all _ fun θ ↦ ?_)
  have hdiff := (a.contDiff_coefficient.differentiable (by simp)) (p.1, p.2 + (2 * π) • θ)
  have hfd := hdiff.fderiv_apply_single_zero j
  dsimp only at hfd
  simp only [hfd, ← coefficient_spatialDeriv, map_zero, ContinuousLinearMap.comp_zero, add_zero,
    fourierSlice, hb.fourier_spatialDeriv j p.2 θ, ContinuousLinearMap.comp_smul,
    EuclideanSpace.inner_single_right, one_mul, conj_trivial]
  module

/-- **Leibniz rule in the frequency.** `∂_{ξ_j} (a # b) = (∂_{ξ_j} a) # b + a # (∂_{ξ_j} b)`. -/
private theorem fderiv_sharpCoeff_apply_inr (a : Symbol n W U m) (hb : b.HasCompactSpatialSupport)
    (p : CoordinateSpace n × CoordinateSpace n) (j : Fin n) :
    fderiv ℝ (sharpCoeff a b) p (0, EuclideanSpace.single j 1) =
      sharpCoeff (Symbol.frequencyDeriv j a) b p + sharpCoeff a (Symbol.frequencyDeriv j b) p := by
  obtain ⟨D, hD, hDapp⟩ := hasFDerivAt_sharpCoeff a hb p
  rw [hD.fderiv, hDapp, sharpCoeff, sharpCoeff, ← integral_add
    (integrable_sharpIntegrand _ hb p) (integrable_sharpIntegrand a (hb.frequencyDeriv j) p)]
  refine integral_congr_ae (ae_of_all _ fun θ ↦ ?_)
  have hdiff := (a.contDiff_coefficient.differentiable (by simp)) (p.1, p.2 + (2 * π) • θ)
  have hfd := hdiff.fderiv_apply_zero_single j
  dsimp only at hfd
  simp only [hfd, ← coefficient_frequencyDeriv, fourierSliceDeriv_apply_single, inner_zero_right,
    Complex.ofReal_zero, mul_zero, zero_mul, zero_smul, add_zero, smul_add]

private theorem coordinateDeriv_fst_sharpCoeff (a : Symbol n W U m)
    (hb : b.HasCompactSpatialSupport) (j : Fin n) (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun y ↦ sharpCoeff a b (y, ξ)) x =
      sharpCoeff (Symbol.spatialDeriv j a) b (x, ξ) +
        sharpCoeff a (Symbol.spatialDeriv j b) (x, ξ) := by
  have h := (differentiable_sharpCoeff a hb (x, ξ)).fderiv_apply_single_zero j
  dsimp only at h
  rw [← h, fderiv_sharpCoeff_apply_inl a hb]

private theorem coordinateDeriv_snd_sharpCoeff (a : Symbol n W U m)
    (hb : b.HasCompactSpatialSupport) (j : Fin n) (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun η ↦ sharpCoeff a b (x, η)) ξ =
      sharpCoeff (Symbol.frequencyDeriv j a) b (x, ξ) +
        sharpCoeff a (Symbol.frequencyDeriv j b) (x, ξ) := by
  have h := (differentiable_sharpCoeff a hb (x, ξ)).fderiv_apply_zero_single j
  dsimp only at h
  rw [← h, fderiv_sharpCoeff_apply_inr a hb]

/-- The coefficient of `a # b` is smooth: its partial derivatives are again coefficients of
compositions of symbols, by the Leibniz rules. -/
private theorem contDiff_sharpCoeff_nat (k : ℕ) :
    ∀ {m m' : ℝ} (a : Symbol n W U m) {b : Symbol n V W m'}, b.HasCompactSpatialSupport →
      ContDiff ℝ k (sharpCoeff a b) := by
  induction k with
  | zero => exact fun a _ hb ↦ contDiff_zero.2 (differentiable_sharpCoeff a hb).continuous
  | succ k ih =>
    intro m m' a b hb
    rw [Nat.cast_succ]
    refine contDiff_succ_of_contDiff_fderiv_apply_single (differentiable_sharpCoeff a hb)
      (fun j ↦ ?_) (fun j ↦ ?_)
    · simp_rw [fderiv_sharpCoeff_apply_inl a hb]
      exact (ih _ hb).add (ih a (hb.spatialDeriv j))
    · simp_rw [fderiv_sharpCoeff_apply_inr a hb]
      exact (ih _ hb).add (ih a (hb.frequencyDeriv j))

private theorem contDiff_sharpCoeff (a : Symbol n W U m) (hb : b.HasCompactSpatialSupport) :
    ContDiff ℝ ∞ (sharpCoeff a b) :=
  contDiff_infty.2 fun k ↦ contDiff_sharpCoeff_nat k a hb

/-- The symbol estimates of order `m + m'` for the coefficient of `a # b`, by induction on the
words `α` and `β`: each derivative falls on `a` or on `b` by the Leibniz rules. -/
private theorem exists_bound_mixedDeriv_sharpCoeff (β : List (Fin n)) :
    ∀ (α : List (Fin n)) {m m' : ℝ} (a : Symbol n W U m) {b : Symbol n V W m'},
      b.HasCompactSpatialSupport → ∀ K : Set (CoordinateSpace n), IsCompact K →
        ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖mixedDeriv α β (sharpCoeff a b) x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m + m' - β.length) / 2) := by
  induction β using List.reverseRecOn with
  | nil =>
    intro α
    induction α using List.reverseRecOn with
    | nil =>
      intro m m' a b hb K hK
      obtain ⟨C, hC0, hC⟩ := exists_norm_sharpCoeff_le a hb K hK
      exact ⟨C, hC0, fun x hx ξ ↦ by simpa using hC x hx ξ⟩
    | append_singleton α j ih =>
      intro m m' a b hb K hK
      obtain ⟨C₁, h₁0, h₁⟩ := ih (Symbol.spatialDeriv j a) hb K hK
      obtain ⟨C₂, h₂0, h₂⟩ := ih a (hb.spatialDeriv j) K hK
      refine ⟨C₁ + C₂, add_nonneg h₁0 h₂0, fun x hx ξ ↦ ?_⟩
      have hfun : (fun p : CoordinateSpace n × CoordinateSpace n ↦
          coordinateDeriv [j] (fun y ↦ sharpCoeff a b (y, p.2)) p.1) =
            sharpCoeff (Symbol.spatialDeriv j a) b + sharpCoeff a (Symbol.spatialDeriv j b) :=
        funext fun p ↦ coordinateDeriv_fst_sharpCoeff a hb j p.1 p.2
      rw [← mixedDeriv_coordinateDeriv_fst (contDiff_sharpCoeff a hb), hfun,
        mixedDeriv_add (contDiff_sharpCoeff _ hb) (contDiff_sharpCoeff a (hb.spatialDeriv j)),
        add_mul]
      exact (norm_add_le _ _).trans (add_le_add (h₁ x hx ξ) (h₂ x hx ξ))
  | append_singleton β j ih =>
    intro α m m' a b hb K hK
    obtain ⟨C₁, h₁0, h₁⟩ := ih α (Symbol.frequencyDeriv j a) hb K hK
    obtain ⟨C₂, h₂0, h₂⟩ := ih α a (hb.frequencyDeriv j) K hK
    refine ⟨C₁ + C₂, add_nonneg h₁0 h₂0, fun x hx ξ ↦ ?_⟩
    have hfun : (fun p : CoordinateSpace n × CoordinateSpace n ↦
        coordinateDeriv [j] (fun η ↦ sharpCoeff a b (p.1, η)) p.2) =
          sharpCoeff (Symbol.frequencyDeriv j a) b + sharpCoeff a (Symbol.frequencyDeriv j b) :=
      funext fun p ↦ coordinateDeriv_snd_sharpCoeff a hb j p.1 p.2
    have e₁ : (m - 1 + m' - β.length) / 2 = (m + m' - (β ++ [j]).length) / 2 := by
      simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      ring
    have e₂ : (m + (m' - 1) - β.length) / 2 = (m + m' - (β ++ [j]).length) / 2 := by
      simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      ring
    rw [← mixedDeriv_coordinateDeriv_snd, hfun,
      mixedDeriv_add (contDiff_sharpCoeff _ hb) (contDiff_sharpCoeff a (hb.frequencyDeriv j)),
      add_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · simpa only [e₁] using h₁ x hx ξ
    · simpa only [e₂] using h₂ x hx ξ

end SharpCoeff

/-! ### The composition symbol and the composition theorem -/

section Sharp

/-- **The composition symbol** `a # b` of a symbol `a` of order `m` and a symbol `b` of order `m'`
with compact spatial support. It is the symbol of order `m + m'` with coefficient
`(a # b)(x, ξ) = ∫ 𝐞 ⟪θ, x⟫ a(x, ξ + 2πθ) b̂(θ, ξ) dθ`
(`TauCeti.Symbol.coefficient_sharp`), where `b̂(θ, ξ)` is the Fourier transform of the position
slice `y ↦ b(y, ξ)`, and its quantization is the composition of the quantizations of `a` and `b`
(`TauCeti.Symbol.quantizeSchwartzValue_sharp`). -/
def sharp (a : Symbol n W U m) {b : Symbol n V W m'}
    (hb : b.HasCompactSpatialSupport) : Symbol n V U (m + m') where
  coefficient := sharpCoeff a b
  contDiff_coefficient := contDiff_sharpCoeff a hb
  exists_bound K hK α β := exists_bound_mixedDeriv_sharpCoeff β α a hb K hK


private theorem coefficient_sharp_eq (a : Symbol n W U m) {b : Symbol n V W m'}
    (hb : b.HasCompactSpatialSupport) : (a.sharp hb).coefficient = sharpCoeff a b := (rfl)

/-- The coefficient of the composition symbol:
`(a # b)(x, ξ) = ∫ 𝐞 ⟪θ, x⟫ a(x, ξ + 2πθ) b̂(θ, ξ) dθ`. -/
theorem coefficient_sharp (a : Symbol n W U m) {b : Symbol n V W m'}
    (hb : b.HasCompactSpatialSupport)
    (x ξ : CoordinateSpace n) :
    (a.sharp hb).coefficient (x, ξ) = ∫ θ, (𝐞 ⟪θ, x⟫ : ℂ) •
      (a.coefficient (x, ξ + (2 * π) • θ)).comp (𝓕 (fun y ↦ b.coefficient (y, ξ)) θ) := (rfl)

/-- **Leibniz rule in the position.** `∂_{x_j} (a # b) = (∂_{x_j} a) # b + a # (∂_{x_j} b)`. -/
theorem spatialDeriv_sharp (a : Symbol n W U m) {b : Symbol n V W m'}
    (hb : b.HasCompactSpatialSupport) (j : Fin n) :
    spatialDeriv j (a.sharp hb) = (spatialDeriv j a).sharp hb + a.sharp (hb.spatialDeriv j) := by
  ext1
  funext p
  rw [coefficient_add, Pi.add_apply, coefficient_spatialDeriv, coefficient_sharp_eq,
    coefficient_sharp_eq, coefficient_sharp_eq]
  exact coordinateDeriv_fst_sharpCoeff a hb j p.1 p.2

/-- **Leibniz rule in the frequency.** `∂_{ξ_j} (a # b) = (∂_{ξ_j} a) # b + a # (∂_{ξ_j} b)`, the
three symbols having orders `m + m' - 1`, `m - 1 + m'` and `m + (m' - 1)`. -/
theorem coefficient_frequencyDeriv_sharp (a : Symbol n W U m) {b : Symbol n V W m'}
    (hb : b.HasCompactSpatialSupport)
    (j : Fin n) (p : CoordinateSpace n × CoordinateSpace n) :
    (frequencyDeriv j (a.sharp hb)).coefficient p =
      ((frequencyDeriv j a).sharp hb).coefficient p +
        (a.sharp (hb.frequencyDeriv j)).coefficient p := by
  rw [coefficient_frequencyDeriv, coefficient_sharp_eq, coefficient_sharp_eq,
    coefficient_sharp_eq]
  exact coordinateDeriv_snd_sharpCoeff a hb j p.1 p.2

/-- If the left factor also has compact spatial support, then so does `a # b`. -/
theorem HasCompactSpatialSupport.sharp {a : Symbol n W U m} (ha : a.HasCompactSpatialSupport)
    {b : Symbol n V W m'} (hb : b.HasCompactSpatialSupport) :
    (a.sharp hb).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  exact hasCompactSpatialSupport_iff.2 ⟨K, hK, fun x hx ξ ↦ by simp [coefficient_sharp, hKa x hx]⟩

/-- **Composition of quantizations.** For a symbol `a` and a symbol `b` with compact spatial
support, `Op(b) u` is a test function for every Schwartz function `u`, and
`Op(a # b) u = Op(a) (Op(b) u)`. -/
theorem quantizeSchwartzValue_sharp [CompleteSpace W] (a : Symbol n W U m) {b : Symbol n V W m'}
    (hb : b.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.sharp hb).coefficient u x =
      quantizeSchwartzValue a.coefficient
        ((hb.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
          (b.contDiff_quantizeSchwartzValue u)) x := by
  -- Without completeness of `U` both sides are integrals defined to be zero.
  by_cases hU : CompleteSpace U
  swap
  · rw [quantizeSchwartzValue_def, quantizeSchwartzValue_def, integral_of_not_completeSpace hU,
      integral_of_not_completeSpace hU]
  set w := (hb.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
    (b.contDiff_quantizeSchwartzValue u)
  have hw : (w : CoordinateSpace n → W) = quantizeSchwartzValue b.coefficient u :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  -- The double integrand, in the frequencies `ζ` of `u` and `η` of `Op(b) u`.
  set H : CoordinateSpace n × CoordinateSpace n → U := fun z ↦
    𝐞 ⟪z.2, x⟫ • a.coefficient (x, (2 * π) • z.2)
      (fourierSlice b (z.2 - z.1) ((2 * π) • z.1) (𝓕 u z.1)) with hH
  have hHc : Continuous H := by
    have h₀ : Continuous fun z : CoordinateSpace n × CoordinateSpace n ↦ 𝐞 ⟪z.2, x⟫ :=
      Real.continuous_fourierChar.comp (continuous_snd.inner continuous_const)
    have h₁ : Continuous fun z : CoordinateSpace n × CoordinateSpace n ↦
        a.coefficient (x, (2 * π) • z.2) :=
      a.contDiff_coefficient.continuous.comp
        (continuous_const.prodMk ((continuous_const_smul (2 * π)).comp continuous_snd))
    have h₂ : Continuous fun z : CoordinateSpace n × CoordinateSpace n ↦
        fourierSlice b (z.2 - z.1) ((2 * π) • z.1) :=
      hb.continuous_fourierSlice.comp₂ (continuous_snd.sub continuous_fst)
        ((continuous_const_smul (2 * π)).comp continuous_fst)
    have h₃ : Continuous fun z : CoordinateSpace n × CoordinateSpace n ↦ 𝓕 u z.1 :=
      (𝓕 u).continuous.comp continuous_fst
    exact h₀.smul (h₁.clm_apply (h₂.clm_apply h₃))
  -- After the shear `(ζ, θ) ↦ (ζ, ζ + θ)` the integrand is dominated by a product.
  obtain ⟨C, hC0, hC⟩ := exists_norm_sharpIntegrand_le a hb {x} isCompact_singleton (n + 1)
  have hshear : Integrable (H ∘ fun z ↦ (z.1, z.1 + z.2)) (volume.prod volume) := by
    refine ((((𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) (m + m')).const_mul
      C).mul_prod integrable_one_add_norm_rpow_neg_succ).mono'
      (hHc.comp (continuous_fst.prodMk (continuous_fst.add continuous_snd))).aestronglyMeasurable
      (ae_of_all _ fun z ↦ ?_)
    have h := hC x rfl ((2 * π) • z.1) z.2
    rw [norm_smul, Circle.norm_coe, one_mul] at h
    simp only [Function.comp_apply, hH, add_sub_cancel_left, smul_add, Circle.norm_smul]
    calc ‖a.coefficient (x, (2 * π) • z.1 + (2 * π) • z.2)
          (fourierSlice b z.2 ((2 * π) • z.1) (𝓕 u z.1))‖
        ≤ ‖(a.coefficient (x, (2 * π) • z.1 + (2 * π) • z.2)).comp
            (fourierSlice b z.2 ((2 * π) • z.1))‖ * ‖𝓕 u z.1‖ :=
          ContinuousLinearMap.le_opNorm (((a.coefficient _)).comp _) _
      _ ≤ C * (1 + ‖(2 * π) • z.1‖ ^ 2) ^ ((m + m') / 2) *
            (1 + ‖z.2‖) ^ (-((n + 1 : ℕ) : ℝ)) * ‖𝓕 u z.1‖ := by gcongr
      _ = C * ((1 + ‖(2 * π) • z.1‖ ^ 2) ^ ((m + m') / 2) * ‖𝓕 u z.1‖) *
            (1 + ‖z.2‖) ^ (-((n + 1 : ℕ) : ℝ)) := by ring
  have hHi : Integrable H (volume.prod volume) :=
    ((measurePreserving_prod_add volume volume).integrable_comp hHc.aestronglyMeasurable).1 hshear
  calc quantizeSchwartzValue (a.sharp hb).coefficient u x
      = ∫ ζ, ∫ θ, H (ζ, ζ + θ) := by
        rw [quantizeSchwartzValue_def]
        refine integral_congr_ae (ae_of_all _ fun ζ ↦ ?_)
        rw [coefficient_sharp_eq]
        unfold sharpCoeff
        dsimp only
        rw [ContinuousLinearMap.integral_apply (integrable_sharpIntegrand a hb (x, (2 * π) • ζ)),
          Circle.smul_def, ← integral_smul]
        refine integral_congr_ae (ae_of_all _ fun θ ↦ ?_)
        simp only [hH, add_sub_cancel_left, smul_add, inner_add_left, AddChar.map_add_eq_mul,
          Circle.coe_mul, Circle.smul_def, smul_apply,
          ContinuousLinearMap.comp_apply, smul_smul, mul_comm]
    _ = ∫ ζ, ∫ η, H (ζ, η) :=
        integral_congr_ae (ae_of_all _ fun ζ ↦ integral_add_left_eq_self (fun η ↦ H (ζ, η)) ζ)
    _ = ∫ η, ∫ ζ, H (ζ, η) := integral_integral_swap (f := fun ζ η ↦ H (ζ, η)) hHi
    _ = quantizeSchwartzValue a.coefficient w x := by
        rw [quantizeSchwartzValue_def]
        refine integral_congr_ae (ae_of_all _ fun η ↦ ?_)
        obtain ⟨Cb, -, hCb⟩ := hb.exists_one_add_norm_pow_mul_norm_fourier_le 0
        have hint : Integrable fun ζ ↦ fourierSlice b (η - ζ) ((2 * π) • ζ) (𝓕 u ζ) := by
          refine (((𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) m').const_mul
            Cb).mono' ((hb.continuous_fourierSlice.comp₂ (continuous_const.sub continuous_id)
              (continuous_const_smul _)).clm_apply (𝓕 u).continuous).aestronglyMeasurable
              (ae_of_all _ fun ζ ↦ ?_)
          refine ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
          have h := hCb (η - ζ) ((2 * π) • ζ)
          rw [pow_zero, one_mul] at h
          rw [← mul_assoc]
          gcongr
          exact h
        simp only [hH, Circle.smul_def]
        rw [integral_smul, (a.coefficient (x, (2 * π) • η)).integral_comp_comm hint,
          SchwartzMap.fourier_coe w, hw, hb.fourier_quantizeSchwartzValue u η]
        unfold fourierSlice
        rfl

/-- **Uniqueness of the composition symbol.** A symbol `c`, of any order, whose quantization is
`Op(a) ∘ Op(b)` on compactly supported Schwartz functions has the coefficient of `a # b`. -/
theorem coefficient_eq_sharp_of_forall_quantizeSchwartzValue_eq [CompleteSpace V] [CompleteSpace W]
    [CompleteSpace U] {m'' : ℝ}
    {a : Symbol n W U m} {b : Symbol n V W m'} (hb : b.HasCompactSpatialSupport)
    {c : Symbol n V U m''}
    (h : ∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport u → ∀ x,
      quantizeSchwartzValue c.coefficient u x = quantizeSchwartzValue a.coefficient
        ((hb.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
          (b.contDiff_quantizeSchwartzValue u)) x) :
    c.coefficient = (a.sharp hb).coefficient :=
  coefficient_eq_of_forall_quantizeSchwartzValue_eq fun u hu ↦ funext fun x ↦
    (h u hu x).trans (quantizeSchwartzValue_sharp a hb u x).symm

/-- The constant symbol `1` is a left identity for the composition: `1 # b = b`. On the level of
coefficients this is the Fourier inversion formula `∫ 𝐞 ⟪θ, x⟫ b̂(θ, ξ) dθ = b(x, ξ)`. -/
theorem coefficient_const_id_sharp [CompleteSpace V] [CompleteSpace W] {b : Symbol n V W m'}
    (hb : b.HasCompactSpatialSupport) :
    ((const (ContinuousLinearMap.id ℂ W)).sharp hb).coefficient = b.coefficient := by
  have hid : (const (ContinuousLinearMap.id ℂ W) : Symbol n W W 0).coefficient =
      fun _ ↦ ContinuousLinearMap.id ℂ W := funext (coefficient_const _)
  refine (coefficient_eq_sharp_of_forall_quantizeSchwartzValue_eq hb fun u _ x ↦ ?_).symm
  rw [hid, quantizeSchwartzValue_id, HasCompactSupport.toSchwartzMap_toFun]

end Sharp

end Symbol

end TauCeti
