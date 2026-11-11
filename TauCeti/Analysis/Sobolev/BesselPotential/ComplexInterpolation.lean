/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Cpow
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic.Module
import TauCeti.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion

/-!
# Interpolation of operators on the Hilbert scale of Bessel-potential spaces

Let `E` be a finite-dimensional real inner product space and `H^s = H^{s,2}` Mathlib's
Bessel-potential spaces of functions on `E` with values in a complex Hilbert space. This file
proves that the scale `(H^s)_{s ∈ ℝ}` interpolates operators: if a linear map `T` of Schwartz
spaces is bounded `H^{s₀} → H^{t₀}` with norm at most `M₀` and `H^{s₁} → H^{t₁}` with norm at most
`M₁`, then for `0 ≤ θ ≤ 1` it is bounded `H^{s_θ} → H^{t_θ}` with norm at most
`M₀ ^ (1 - θ) M₁ ^ θ`, where `s_θ = (1 - θ) s₀ + θ s₁` and `t_θ = (1 - θ) t₀ + θ t₁`.

The proof is Stein's argument with an analytic family of weights. The tool is the Bessel potential
of complex order (`SchwartzMap.besselPotentialCLM`), the Fourier multiplier `J^z` with symbol the
complex power `⟨ξ⟩ ^ z` of the Japanese bracket (`TauCeti.japaneseBracketCpow`). For real `z = s` it
is the Bessel potential of order `s`, and the `H^r` norm of `J^z u` is the `H^{r + re z}` norm of
`u` (`SchwartzMap.norm_toBesselPotentialSpaceCLM_besselPotentialCLM`), so imaginary orders act
isometrically on every `H^r`. Its dependence on `z` is holomorphic in every `H^r`
(`SchwartzMap.hasDerivAt_toBesselPotentialSpaceCLM_besselPotentialCLM`).

Given Schwartz functions `u` and `v`, the function

`G z = ∫ ⟪J^{d(conj z)} v, T (J^{c(z)} u)⟫`, `c(z) = s_θ - s_z`, `d(z) = t_z - t_θ`,

is entire, bounded on the strip `0 ≤ re z ≤ 1`, and on the two boundary lines the duality of
`H^{-t_j}` and `H^{t_j}` under the `L²` pairing (`SchwartzMap.norm_integral_inner_le`) bounds it by
`M_j ‖u‖_{H^{s_θ}} ‖v‖_{H^{-t_θ}}`. Hadamard's three-lines theorem then bounds `G θ = ∫ ⟪v, T u⟫`,
and the choice `v = J^{2 t_θ} (T u)` turns this into the norm bound
(`SchwartzMap.norm_toBesselPotentialSpaceCLM_le_rpow_mul_rpow_mul_norm`). Since Schwartz functions
are dense, `T` then extends to a bounded operator `H^{s_θ} → H^{t_θ}`
(`SchwartzMap.exists_toBesselPotentialSpaceCLM_comp_eq_of_interpolation`).

## Main declarations

* `SchwartzMap.besselPotentialCLM z`: the Bessel potential `J^z` of complex order on Schwartz
  space, with `SchwartzMap.fourier_besselPotentialCLM_apply`,
  `SchwartzMap.besselPotentialCLM_besselPotentialCLM_apply` and the comparison
  `SchwartzMap.toTemperedDistribution_besselPotentialCLM_ofReal` with Mathlib's
  `TemperedDistribution.besselPotential` at real orders.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM_besselPotentialCLM`:
  `‖J^z u‖_{H^r} = ‖u‖_{H^{r + re z}}`.
* `SchwartzMap.hasDerivAt_toBesselPotentialSpaceCLM_besselPotentialCLM`: `z ↦ J^z u` is holomorphic
  with values in `H^r`.
* `SchwartzMap.inner_toLp_toBesselPotentialSpaceCLM_neg`, `SchwartzMap.norm_integral_inner_le`:
  the `L²` pairing of `H^{-r}` and `H^r`, and `|∫ ⟪a, b⟫| ≤ ‖a‖_{H^{-r}} ‖b‖_{H^r}`.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM_le_rpow_mul_rpow_mul_norm`: the interpolation
  inequality.
* `SchwartzMap.exists_toBesselPotentialSpaceCLM_comp_eq_of_interpolation`: the interpolated
  operator `H^{s_θ} → H^{t_θ}`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Springer, 1976, §§4.1, 6.4.
* E. M. Stein, *Interpolation of linear operators*, Trans. Amer. Math. Soc. 83 (1956), 482–492.
-/

public section

noncomputable section

open MeasureTheory FourierTransform Complex Complex.HadamardThreeLines
open scoped ENNReal SchwartzMap BesselPotentialSpace InnerProductSpace ComplexConjugate

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The **Bessel potential of complex order** `z` on Schwartz functions: the Fourier multiplier
`J^z u = 𝓕⁻ (⟨ξ⟩ ^ z 𝓕 u)` whose symbol is the complex power `⟨ξ⟩ ^ z` of the Japanese bracket
`⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`. For real `z = s` it is the Bessel potential of order `s`
(`SchwartzMap.besselPotentialCLM_ofReal`), and the orders add under composition
(`SchwartzMap.besselPotentialCLM_besselPotentialCLM_apply`). -/
def besselPotentialCLM (z : ℂ) : 𝓢(E, F) →L[ℂ] 𝓢(E, F) :=
  fourierMultiplierCLM F (TauCeti.japaneseBracketCpow z)

/-- At a real order `s` the Bessel potential is the Fourier multiplier with symbol
`(1 + ‖ξ‖ ^ 2) ^ (s / 2)`, the one defining the inclusion of Schwartz functions into `H^{s,p}`. -/
theorem besselPotentialCLM_ofReal (s : ℝ) :
    besselPotentialCLM (E := E) (F := F) (s : ℂ) =
      fourierMultiplierCLM F (fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) := by
  rw [besselPotentialCLM]
  congr 1
  funext ξ
  exact TauCeti.japaneseBracketCpow_ofReal s ξ

variable [CompleteSpace F]

/-- The Fourier transform of `J^z u` is `⟨ξ⟩ ^ z 𝓕 u`. -/
@[simp]
theorem fourier_besselPotentialCLM_apply (z : ℂ) (u : 𝓢(E, F)) (ξ : E) :
    𝓕 (besselPotentialCLM z u) ξ = TauCeti.japaneseBracketCpow z ξ • 𝓕 u ξ := by
  rw [besselPotentialCLM, fourierMultiplierCLM_apply, fourier_fourierInv_eq,
    smulLeftCLM_apply_apply (TauCeti.hasTemperateGrowth_japaneseBracketCpow z)]

@[simp]
theorem besselPotentialCLM_zero :
    besselPotentialCLM (E := E) (F := F) 0 = ContinuousLinearMap.id ℂ _ := by
  have h : TauCeti.japaneseBracketCpow (0 : ℂ) = fun _ : E ↦ (1 : ℂ) :=
    funext TauCeti.japaneseBracketCpow_zero
  rw [besselPotentialCLM, h, fourierMultiplierCLM_const, one_smul]

/-- The orders of Bessel potentials add: `J^w (J^z u) = J^(z + w) u`. -/
@[simp]
theorem besselPotentialCLM_besselPotentialCLM_apply (z w : ℂ) (u : 𝓢(E, F)) :
    besselPotentialCLM w (besselPotentialCLM z u) = besselPotentialCLM (z + w) u := by
  simp only [besselPotentialCLM]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply
    (TauCeti.hasTemperateGrowth_japaneseBracketCpow w)
    (TauCeti.hasTemperateGrowth_japaneseBracketCpow z)]
  congr 2
  funext ξ
  rw [Pi.mul_apply, TauCeti.japaneseBracketCpow_add, mul_comm]

/-- At a real order `s`, the Bessel potential of a Schwartz function is Mathlib's Bessel potential
`TemperedDistribution.besselPotential E F s` of the corresponding tempered distribution. -/
theorem toTemperedDistribution_besselPotentialCLM_ofReal (s : ℝ) (u : 𝓢(E, F)) :
    (besselPotentialCLM (s : ℂ) u : 𝓢'(E, F)) =
      TemperedDistribution.besselPotential E F s (u : 𝓢'(E, F)) := by
  rw [besselPotentialCLM_ofReal, TemperedDistribution.besselPotential,
    TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]

/-- The `Lᵖ` part of a Schwartz function in `H^{r,p}` is its Bessel potential of order `r`. -/
theorem toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM (r : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : 𝓢(E, F)) :
    (toBesselPotentialSpaceCLM r p u).toLp = (besselPotentialCLM (r : ℂ) u).toLp p := by
  rw [toLp_toBesselPotentialSpaceCLM, besselPotentialCLM_ofReal]

end Normed

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The Bessel potentials shift the order of the `H^r` norms.** The `H^r` norm of `J^z u` is the
`H^{r + re z}` norm of `u`; in particular imaginary orders act isometrically on every `H^r`. -/
theorem norm_toBesselPotentialSpaceCLM_besselPotentialCLM (r : ℝ) (z : ℂ) (u : 𝓢(E, H)) :
    ‖toBesselPotentialSpaceCLM r 2 (besselPotentialCLM z u)‖ =
      ‖toBesselPotentialSpaceCLM (r + z.re) 2 u‖ := by
  rw [norm_toBesselPotentialSpaceCLM, norm_toBesselPotentialSpaceCLM]
  congr 1
  refine eLpNorm_congr_norm_ae (memLp_one_add_norm_sq_rpow_smul_fourier _ _ 2).aestronglyMeasurable
    (memLp_one_add_norm_sq_rpow_smul_fourier _ _ 2).aestronglyMeasurable (.of_forall fun ξ ↦ ?_)
  have h1 : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [fourier_besselPotentialCLM_apply, norm_smul, norm_smul, norm_smul, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    TauCeti.norm_japaneseBracketCpow, ← mul_assoc, ← Real.rpow_add h1]
  ring_nf

/-- **The `L²` pairing of `H^{-r}` and `H^r`.** For Schwartz functions `a` and `b`, the `L²` inner
product of the `L²` parts of `a ∈ H^{-r}` and `b ∈ H^r` is `∫ ⟪a, b⟫`, for every real `r`. -/
theorem inner_toLp_toBesselPotentialSpaceCLM_neg (r : ℝ) (a b : 𝓢(E, H)) :
    ⟪(toBesselPotentialSpaceCLM (-r) 2 a).toLp, (toBesselPotentialSpaceCLM r 2 b).toLp⟫_ℂ =
      ∫ x, ⟪a x, b x⟫_ℂ := by
  rw [toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM,
    toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM, inner_toL2_toL2_eq _ _ volume,
    ← integral_inner_fourier_fourier, ← integral_inner_fourier_fourier a b]
  congr 1
  funext ξ
  have h1 : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [fourier_besselPotentialCLM_apply, fourier_besselPotentialCLM_apply, inner_smul_left,
    inner_smul_right, ← mul_assoc, TauCeti.japaneseBracketCpow_ofReal,
    TauCeti.japaneseBracketCpow_ofReal, Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← Real.rpow_add h1, neg_div, neg_add_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]

/-- **Duality of `H^{-r}` and `H^r` under the `L²` pairing**:
`|∫ ⟪a, b⟫| ≤ ‖a‖_{H^{-r}} ‖b‖_{H^r}` for Schwartz functions `a` and `b`. -/
theorem norm_integral_inner_le (r : ℝ) (a b : 𝓢(E, H)) :
    ‖∫ x, ⟪a x, b x⟫_ℂ‖ ≤
      ‖toBesselPotentialSpaceCLM (-r) 2 a‖ * ‖toBesselPotentialSpaceCLM r 2 b‖ := by
  rw [← inner_toLp_toBesselPotentialSpaceCLM_neg r, ← BesselPotentialSpace.norm_toLp_eq,
    ← BesselPotentialSpace.norm_toLp_eq (toBesselPotentialSpaceCLM r 2 b)]
  exact norm_inner_le_norm _ _

/-- **The Bessel potentials depend holomorphically on the order.** For a Schwartz function `u`
and every real `r`, the map `z ↦ J^z u` into `H^r` is complex differentiable, with derivative
`J^z (log ⟨D⟩ u)`, where `log ⟨D⟩` is the Fourier multiplier with symbol
`log ⟨ξ⟩ = log (1 + ‖ξ‖ ^ 2) / 2`. -/
theorem hasDerivAt_toBesselPotentialSpaceCLM_besselPotentialCLM (r : ℝ) (u : 𝓢(E, H)) (z : ℂ) :
    HasDerivAt (fun w ↦ toBesselPotentialSpaceCLM r 2 (besselPotentialCLM w u))
      (toBesselPotentialSpaceCLM r 2 (besselPotentialCLM z
        (fourierMultiplierCLM H (fun ξ : E ↦ ((Real.log (1 + ‖ξ‖ ^ 2) / 2 : ℝ) : ℂ)) u))) z := by
  set ℓ : E → ℂ := fun ξ ↦ ((Real.log (1 + ‖ξ‖ ^ 2) / 2 : ℝ) : ℂ) with hℓ_def
  have hℓ : ℓ.HasTemperateGrowth := by
    have : ℓ = fun ξ : E ↦ (((1 / 2 : ℝ) * Real.log (1 + ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
      funext ξ
      simp only [hℓ_def]
      ring_nf
    rw [this]
    fun_prop
  set R := r + z.re + 3
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine (Asymptotics.IsBigO.of_bound ‖toBesselPotentialSpaceCLM R 2 u‖ ?_).trans_isLittleO
    (Asymptotics.isLittleO_pow_id one_lt_two)
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) zero_lt_one] with h hh
  rw [Metric.mem_closedBall, dist_zero_right] at hh
  rw [← map_smul, ← map_sub, ← map_sub, norm_toBesselPotentialSpaceCLM,
    norm_toBesselPotentialSpaceCLM, norm_pow, mul_comm]
  -- The Fourier transform of the remainder is the remainder of the symbol times `𝓕 u`.
  have hrem (ξ : E) : 𝓕 (besselPotentialCLM (z + h) u - besselPotentialCLM z u -
      h • besselPotentialCLM z (fourierMultiplierCLM H ℓ u)) ξ =
      (TauCeti.japaneseBracketCpow (z + h) ξ - TauCeti.japaneseBracketCpow z ξ -
        h * (TauCeti.japaneseBracketCpow z ξ * ℓ ξ)) • 𝓕 u ξ := by
    simp only [sub_eq_add_neg, FourierAdd.fourier_add, FourierTransform.fourier_neg,
      FourierSMul.fourier_smul, add_apply, neg_apply, smul_apply, fourier_besselPotentialCLM_apply]
    rw [fourierMultiplierCLM_apply, fourier_fourierInv_eq, smulLeftCLM_apply_apply hℓ]
    module
  set w := besselPotentialCLM (z + h) u - besselPotentialCLM z u -
    h • besselPotentialCLM z (fourierMultiplierCLM H ℓ u)
  have hbound : eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) • 𝓕 w ξ) 2 volume ≤
      ENNReal.ofReal (‖h‖ ^ 2) *
        eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (R / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (memLp_one_add_norm_sq_rpow_smul_fourier r w 2).aestronglyMeasurable (.of_forall fun ξ ↦ ?_) 2
    have h1 : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
    rw [hrem, norm_smul, norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hr := TauCeti.norm_japaneseBracketCpow_add_sub_sub_le z hh ξ
    calc (1 + ‖ξ‖ ^ 2) ^ (r / 2) * (‖TauCeti.japaneseBracketCpow (z + h) ξ -
          TauCeti.japaneseBracketCpow z ξ - h * (TauCeti.japaneseBracketCpow z ξ * ℓ ξ)‖ *
            ‖𝓕 u ξ‖)
        ≤ (1 + ‖ξ‖ ^ 2) ^ (r / 2) * ((‖h‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ ((z.re + 3) / 2)) *
            ‖𝓕 u ξ‖) := by gcongr
      _ = ‖h‖ ^ 2 * ((1 + ‖ξ‖ ^ 2) ^ (R / 2) * ‖𝓕 u ξ‖) := by
        rw [show R / 2 = r / 2 + (z.re + 3) / 2 by ring, Real.rpow_add h1]
        ring
  have hfin := (memLp_one_add_norm_sq_rpow_smul_fourier R u 2).eLpNorm_ne_top
  calc (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) • 𝓕 w ξ) 2 volume).toReal
      ≤ (ENNReal.ofReal (‖h‖ ^ 2) *
          eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (R / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hbound
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

end Hilbert

section Interpolation

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- A linear map `T` of Schwartz spaces that is bounded `H^s → H^t` sends a family whose image in
`H^s` is complex differentiable to a family whose image in `H^t` is complex differentiable. -/
private theorem hasDerivAt_toBesselPotentialSpaceCLM_apply {T : 𝓢(E, V) →ₗ[ℂ] 𝓢(E, W)}
    {s t M : ℝ}
    (hT : ∀ u, ‖toBesselPotentialSpaceCLM t 2 (T u)‖ ≤ M * ‖toBesselPotentialSpaceCLM s 2 u‖)
    {f : ℂ → 𝓢(E, V)} {f' : 𝓢(E, V)} {z : ℂ}
    (hf : HasDerivAt (fun w ↦ toBesselPotentialSpaceCLM s 2 (f w))
      (toBesselPotentialSpaceCLM s 2 f') z) :
    HasDerivAt (fun w ↦ toBesselPotentialSpaceCLM t 2 (T (f w)))
      (toBesselPotentialSpaceCLM t 2 (T f')) z := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hf ⊢
  refine (Asymptotics.IsBigO.of_bound M (.of_forall fun h ↦ ?_)).trans_isLittleO hf
  simpa only [map_sub, map_smul] using hT (f (z + h) - f z - h • f')

/-- **Interpolation on the Hilbert scale of Bessel-potential spaces.** Let `T` be a linear map of
Schwartz spaces with `‖T u‖_{H^{t₀}} ≤ M₀ ‖u‖_{H^{s₀}}` and `‖T u‖_{H^{t₁}} ≤ M₁ ‖u‖_{H^{s₁}}`.
Then for `0 ≤ θ ≤ 1`,
`‖T u‖_{H^{t_θ}} ≤ M₀ ^ (1 - θ) M₁ ^ θ ‖u‖_{H^{s_θ}}`, where `s_θ = (1 - θ) s₀ + θ s₁` and
`t_θ = (1 - θ) t₀ + θ t₁`. -/
theorem norm_toBesselPotentialSpaceCLM_le_rpow_mul_rpow_mul_norm {T : 𝓢(E, V) →ₗ[ℂ] 𝓢(E, W)}
    {s₀ s₁ t₀ t₁ M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ u, ‖toBesselPotentialSpaceCLM t₀ 2 (T u)‖ ≤ M₀ * ‖toBesselPotentialSpaceCLM s₀ 2 u‖)
    (h₁ : ∀ u, ‖toBesselPotentialSpaceCLM t₁ 2 (T u)‖ ≤ M₁ * ‖toBesselPotentialSpaceCLM s₁ 2 u‖)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (u : 𝓢(E, V)) :
    ‖toBesselPotentialSpaceCLM ((1 - θ) * t₀ + θ * t₁) 2 (T u)‖ ≤
      M₀ ^ (1 - θ) * M₁ ^ θ * ‖toBesselPotentialSpaceCLM ((1 - θ) * s₀ + θ * s₁) 2 u‖ := by
  set sθ := (1 - θ) * s₀ + θ * s₁ with hsθ
  set tθ := (1 - θ) * t₀ + θ * t₁ with htθ
  -- The test function `v = J^{2 tθ} (T u)` realizes the `H^{tθ}` norm of `T u` in the pairing.
  set v : 𝓢(E, W) := besselPotentialCLM ((2 * tθ : ℝ) : ℂ) (T u) with hv
  -- The analytic families of orders, `c z = sθ - s_z` for `u` and `d z = t_z - tθ` for `v`.
  set c : ℂ → ℂ := fun z ↦ ((sθ - s₀ : ℝ) : ℂ) + z * ((s₀ - s₁ : ℝ) : ℂ) with hc
  set d : ℂ → ℂ := fun z ↦ ((t₀ - tθ : ℝ) : ℂ) + z * ((t₁ - t₀ : ℝ) : ℂ) with hd
  set Φ : ℂ → Lp W 2 (volume : Measure E) :=
    fun z ↦ (toBesselPotentialSpaceCLM t₀ 2 (T (besselPotentialCLM (c z) u))).toLp with hΦ
  set Ψ : ℂ → Lp W 2 (volume : Measure E) :=
    fun z ↦ (toBesselPotentialSpaceCLM (-t₀) 2 (besselPotentialCLM (d z) v)).toLp with hΨ
  set G : ℂ → ℂ := fun z ↦ ⟪Ψ (conj z), Φ z⟫_ℂ with hG_def
  -- `G z` is the `L²` pairing of `J^{d (conj z)} v` and `T (J^{c z} u)`, in any dual weights.
  have hG (z : ℂ) (r : ℝ) : G z =
      ⟪(toBesselPotentialSpaceCLM (-r) 2 (besselPotentialCLM (d (conj z)) v)).toLp,
        (toBesselPotentialSpaceCLM r 2 (T (besselPotentialCLM (c z) u))).toLp⟫_ℂ := by
    simp only [hG_def, hΦ, hΨ]
    rw [inner_toLp_toBesselPotentialSpaceCLM_neg, inner_toLp_toBesselPotentialSpaceCLM_neg]
  have hre_c (z : ℂ) : (c z).re = sθ - s₀ + z.re * (s₀ - s₁) := by simp [hc]
  have hre_d (z : ℂ) : (d (conj z)).re = t₀ - tθ + z.re * (t₁ - t₀) := by simp [hd]
  -- The basic estimate of `G z`, from the duality of `H^{-r}` and `H^r` and a bound `H^s → H^r`.
  have hbound (z : ℂ) {r s M : ℝ}
      (hT : ∀ u, ‖toBesselPotentialSpaceCLM r 2 (T u)‖ ≤ M * ‖toBesselPotentialSpaceCLM s 2 u‖) :
      ‖G z‖ ≤ ‖toBesselPotentialSpaceCLM (-r + (t₀ - tθ + z.re * (t₁ - t₀))) 2 v‖ *
        (M * ‖toBesselPotentialSpaceCLM (s + (sθ - s₀ + z.re * (s₀ - s₁))) 2 u‖) := by
    rw [hG z r]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [BesselPotentialSpace.norm_toLp_eq, BesselPotentialSpace.norm_toLp_eq,
      norm_toBesselPotentialSpaceCLM_besselPotentialCLM, hre_d]
    gcongr
    rw [← hre_c, ← norm_toBesselPotentialSpaceCLM_besselPotentialCLM]
    exact hT _
  -- `G` is entire.
  have hdiff : Differentiable ℂ G := by
    intro z
    have h1 := (hasDerivAt_toBesselPotentialSpaceCLM_besselPotentialCLM s₀ u (c z)).scomp z
      (((hasDerivAt_id z).mul_const ((s₀ - s₁ : ℝ) : ℂ)).const_add ((sθ - s₀ : ℝ) : ℂ))
    rw [← map_smul] at h1
    have h2 := (hasDerivAt_toBesselPotentialSpaceCLM_besselPotentialCLM (-t₀) v
      (d (conj z))).scomp (conj z)
      (((hasDerivAt_id (conj z)).mul_const ((t₁ - t₀ : ℝ) : ℂ)).const_add ((t₀ - tθ : ℝ) : ℂ))
    set eΦ := (BesselPotentialSpace.toLpₗᵢ E W t₀ 2).toContinuousLinearEquiv
    set eΨ := (BesselPotentialSpace.toLpₗᵢ E W (-t₀) 2).toContinuousLinearEquiv
    obtain ⟨Φ', hΦd⟩ : ∃ Φ', HasDerivAt Φ Φ' z :=
      ⟨_, (eΦ.hasFDerivAt.comp_hasDerivAt z (hasDerivAt_toBesselPotentialSpaceCLM_apply h₀ h1))
        |>.congr_of_eventuallyEq (.of_forall fun w ↦ by simp [hΦ, eΦ])⟩
    obtain ⟨Ψ', hΨd⟩ : ∃ Ψ', HasDerivAt Ψ Ψ' (conj z) :=
      ⟨_, (eΨ.hasFDerivAt.comp_hasDerivAt (conj z) h2).congr_of_eventuallyEq
        (.of_forall fun w ↦ by simp [hΨ, eΨ])⟩
    exact (hΨd.inner_comp_conj hΦd).differentiableAt
  -- At `θ` both orders vanish and `G θ = ‖T u‖²_{H^{tθ}}`.
  have hcθ : c θ = 0 := by
    simp only [hc, hsθ]
    push_cast
    ring
  have hdθ : d (conj (θ : ℂ)) = 0 := by
    simp only [hd, Complex.conj_ofReal, htθ]
    push_cast
    ring
  have hvL : (toBesselPotentialSpaceCLM (-tθ) 2 v).toLp =
      (toBesselPotentialSpaceCLM tθ 2 (T u)).toLp := by
    rw [toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM,
      toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM, hv,
      besselPotentialCLM_besselPotentialCLM_apply]
    congr 3
    push_cast
    ring
  set N := ‖toBesselPotentialSpaceCLM tθ 2 (T u)‖ with hN
  have hGθ : G θ = ((N ^ 2 : ℝ) : ℂ) := by
    rw [hG θ tθ, hcθ, hdθ, besselPotentialCLM_zero, besselPotentialCLM_zero,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply, hvL, inner_self_eq_norm_sq_to_K,
      BesselPotentialSpace.norm_toLp_eq]
    push_cast
    rfl
  have hvN : ‖toBesselPotentialSpaceCLM (-tθ) 2 v‖ = N := by
    rw [hv, norm_toBesselPotentialSpaceCLM_besselPotentialCLM, Complex.ofReal_re,
      show -tθ + 2 * tθ = tθ by ring]
  -- Boundary bounds on the two lines and a bound on the closed strip.
  set X := ‖toBesselPotentialSpaceCLM sθ 2 u‖ with hX
  have ha : ∀ z ∈ Complex.re ⁻¹' {0}, ‖G z‖ ≤ N * (M₀ * X) := fun z hz ↦ by
    have hz' : z.re = 0 := hz
    have h := hbound z h₀
    rw [show -t₀ + (t₀ - tθ + z.re * (t₁ - t₀)) = -tθ by rw [hz']; ring,
      show s₀ + (sθ - s₀ + z.re * (s₀ - s₁)) = sθ by rw [hz']; ring, hvN] at h
    exact h
  have hb : ∀ z ∈ Complex.re ⁻¹' {1}, ‖G z‖ ≤ N * (M₁ * X) := fun z hz ↦ by
    have hz' : z.re = 1 := hz
    have h := hbound z h₁
    rw [show -t₁ + (t₀ - tθ + z.re * (t₁ - t₀)) = -tθ by rw [hz']; ring,
      show s₁ + (sθ - s₀ + z.re * (s₀ - s₁)) = sθ by rw [hz']; ring, hvN] at h
    exact h
  have hB : BddAbove ((norm ∘ G) '' verticalClosedStrip 0 1) := by
    refine ⟨‖toBesselPotentialSpaceCLM (-tθ + |t₁ - t₀|) 2 v‖ *
      (M₀ * ‖toBesselPotentialSpaceCLM (sθ + |s₀ - s₁|) 2 u‖), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hz0, hz1⟩ : 0 ≤ z.re ∧ z.re ≤ 1 := hz
    refine (hbound z h₀).trans ?_
    have hle_v : -t₀ + (t₀ - tθ + z.re * (t₁ - t₀)) ≤ -tθ + |t₁ - t₀| := by
      nlinarith [le_abs_self (t₁ - t₀), neg_abs_le (t₁ - t₀)]
    have hle_u : s₀ + (sθ - s₀ + z.re * (s₀ - s₁)) ≤ sθ + |s₀ - s₁| := by
      nlinarith [le_abs_self (s₀ - s₁), neg_abs_le (s₀ - s₁)]
    rw [← BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM hle_v,
      ← BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM hle_u]
    gcongr
    · exact BesselPotentialSpace.norm_inclusion_apply_le _ _
    · exact BesselPotentialSpace.norm_inclusion_apply_le _ _
  -- Hadamard's three-lines theorem at `θ` gives `N ^ 2 ≤ N (M₀ X) ^ (1 - θ) (M₁ X) ^ θ`.
  have hX0 : 0 ≤ X := norm_nonneg _
  have mul_rpow_mul_mul_rpow {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
      (c * a) ^ (1 - θ) * (c * b) ^ θ = c * (a ^ (1 - θ) * b ^ θ) := by
    rw [Real.mul_rpow hc ha, Real.mul_rpow hc hb, mul_mul_mul_comm,
      ← Real.rpow_add' hc (by norm_num : 1 - θ + θ ≠ 0), sub_add_cancel, Real.rpow_one]
  have h3 := norm_le_interp_of_mem_verticalClosedStrip₀₁' G (z := θ)
    (by simpa [verticalClosedStrip] using hθ) hdiff.diffContOnCl hB ha hb
  rw [hGθ, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    mul_rpow_mul_mul_rpow (mul_nonneg hM₀ hX0) (mul_nonneg hM₁ hX0) (norm_nonneg _),
    mul_comm M₀ X, mul_comm M₁ X, mul_rpow_mul_mul_rpow hM₀ hM₁ hX0, pow_two] at h3
  -- Divide by `N`.
  rcases (norm_nonneg _ : 0 ≤ N).eq_or_lt with hN0 | hN0
  · rw [show N = 0 from hN0.symm]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hM₀ _) (Real.rpow_nonneg hM₁ _)) hX0
  · rw [mul_comm _ X]
    exact le_of_mul_le_mul_left h3 hN0

/-- **Interpolated operators on the Hilbert scale.** Under the hypotheses of
`SchwartzMap.norm_toBesselPotentialSpaceCLM_le_rpow_mul_rpow_mul_norm`, the linear map `T` of
Schwartz spaces extends to a bounded operator `H^{s_θ} → H^{t_θ}` of norm at most
`M₀ ^ (1 - θ) M₁ ^ θ`. -/
theorem exists_extension_norm_le_rpow_mul_rpow {T : 𝓢(E, V) →ₗ[ℂ] 𝓢(E, W)}
    {s₀ s₁ t₀ t₁ M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ u, ‖toBesselPotentialSpaceCLM t₀ 2 (T u)‖ ≤ M₀ * ‖toBesselPotentialSpaceCLM s₀ 2 u‖)
    (h₁ : ∀ u, ‖toBesselPotentialSpaceCLM t₁ 2 (T u)‖ ≤ M₁ * ‖toBesselPotentialSpaceCLM s₁ 2 u‖)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ S : H^{(1 - θ) * s₀ + θ * s₁}(E, V) →L[ℂ] H^{(1 - θ) * t₀ + θ * t₁}(E, W),
      (∀ u, S (toBesselPotentialSpaceCLM _ 2 u) = toBesselPotentialSpaceCLM _ 2 (T u)) ∧
        ‖S‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
  have hbd := norm_toBesselPotentialSpaceCLM_le_rpow_mul_rpow_mul_norm hM₀ hM₁ h₀ h₁ hθ
  have hdense := denseRange_toBesselPotentialSpaceCLM (E := E) (F := V)
    ((1 - θ) * s₀ + θ * s₁) (p := 2) ENNReal.ofNat_ne_top
  refine ⟨((toBesselPotentialSpaceCLM ((1 - θ) * t₀ + θ * t₁) 2).toLinearMap ∘ₗ T).extendOfNorm
    (toBesselPotentialSpaceCLM _ 2).toLinearMap, fun u ↦ ?_, ?_⟩
  · exact LinearMap.extendOfNorm_eq hdense ⟨_, hbd⟩ u
  · exact LinearMap.opNorm_extendOfNorm_le hdense
      (mul_nonneg (Real.rpow_nonneg hM₀ _) (Real.rpow_nonneg hM₁ _)) hbd

end Interpolation

end SchwartzMap
