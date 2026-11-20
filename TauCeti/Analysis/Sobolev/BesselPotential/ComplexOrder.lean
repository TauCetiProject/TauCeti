/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Cpow
import Mathlib.Tactic.Module
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Fourier.MihlinHormander

/-!
# Bessel potentials of complex order on Schwartz space

Let `E` be a finite-dimensional real inner product space. The Bessel potential of complex order
`z` (`SchwartzMap.besselPotentialCLM z`) is the Fourier multiplier `J^z` on Schwartz functions
whose symbol is the complex power `⟨ξ⟩ ^ z` of the Japanese bracket
(`TauCeti.japaneseBracketCpow`). For real `z = s` it is the Bessel potential of order `s`, and the
orders add under composition.

For Schwartz functions with values in a complex Hilbert space, the `H^r` norm of `J^z u` is the
`H^{r + re z}` norm of `u`, so imaginary orders act isometrically on every `H^r`, and `z ↦ J^z u` is
holomorphic with values in every `H^r = H^{r,2}`. These are the analytic families of weights used in
Stein's interpolation argument.

For `1 < p < ∞` and `p ≠ 2` the imaginary orders are no longer isometries of `Lᵖ`, but they are
bounded with norm growing polynomially in the order: the symbol `⟨ξ⟩ ^ (i τ)` satisfies Mihlin's
condition of order `N = ⌊dim E / 2⌋ + 1` with constant `O((1 + |τ|) ^ N)`
(`TauCeti.exists_norm_iteratedFDeriv_japaneseBracketCpow_le_div_pow`), so the Mihlin–Hörmander
multiplier theorem gives `‖J^(i τ) u‖_p ≤ C (1 + |τ|) ^ N ‖u‖_p`. Composing with the real orders,
`J^z` maps `H^{r + re z, p}` to `H^{r,p}` with norm `O((1 + |im z|) ^ N)`. Such polynomial growth on
vertical lines is admissible in Stein's interpolation theorem, which is how the Bessel-potential
spaces with `p ≠ 2` are interpolated (Bergh–Löfström, §6.4, proof of Theorem 6.4.5 (7)).

## Main declarations

* `SchwartzMap.besselPotentialCLM z`: the Bessel potential `J^z` of complex order on Schwartz
  space, with `SchwartzMap.fourier_besselPotentialCLM_apply`,
  `SchwartzMap.besselPotentialCLM_besselPotentialCLM_apply` and the comparison
  `SchwartzMap.toTemperedDistributionCLM_besselPotentialCLM_ofReal` with Mathlib's
  `TemperedDistribution.besselPotential` at real orders.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM_besselPotentialCLM`:
  `‖J^z u‖_{H^r} = ‖u‖_{H^{r + re z}}`.
* `SchwartzMap.hasDerivAt_toBesselPotentialSpaceCLM_besselPotentialCLM`: `z ↦ J^z u` is holomorphic
  with values in `H^r`.
* `SchwartzMap.exists_eLpNorm_besselPotentialCLM_le`: for `1 < p < ∞` and `re z ≤ 0`,
  `‖J^z u‖_p ≤ C (1 + ‖z‖) ^ N ‖u‖_p`.
* `SchwartzMap.exists_norm_toBesselPotentialSpaceCLM_besselPotentialCLM_le`: for `1 < p < ∞`,
  `‖J^z u‖_{H^{r,p}} ≤ C (1 + |im z|) ^ N ‖u‖_{H^{r + re z, p}}`.

## References

* J. Bergh, J. Löfström, *Interpolation Spaces: An Introduction*, Springer, 1976, §6.1 (the
  Mihlin multiplier theorem) and §6.4 (the Bessel-potential spaces and their complex
  interpolation).
-/

public section

noncomputable section

open MeasureTheory FourierTransform Complex
open scoped ENNReal SchwartzMap BesselPotentialSpace

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

theorem besselPotentialCLM_def (z : ℂ) :
    besselPotentialCLM (E := E) (F := F) z =
      fourierMultiplierCLM F (TauCeti.japaneseBracketCpow z) :=
  (rfl)

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

/-- The orders of Bessel potentials add: `J^w ∘ J^z = J^(z + w)`. -/
theorem besselPotentialCLM_compL_besselPotentialCLM (z w : ℂ) :
    besselPotentialCLM (E := E) (F := F) w ∘L besselPotentialCLM z =
      besselPotentialCLM (z + w) := by
  ext1 u
  exact besselPotentialCLM_besselPotentialCLM_apply z w u

/-- At a real order `s`, the Bessel potential of a Schwartz function is Mathlib's Bessel potential
`TemperedDistribution.besselPotential E F s` of the corresponding tempered distribution. -/
theorem toTemperedDistributionCLM_besselPotentialCLM_ofReal (s : ℝ) (u : 𝓢(E, F)) :
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
@[simp]
theorem norm_toBesselPotentialSpaceCLM_besselPotentialCLM (r : ℝ) (z : ℂ) (u : 𝓢(E, H)) :
    ‖toBesselPotentialSpaceCLM r 2 (besselPotentialCLM z u)‖ =
      ‖toBesselPotentialSpaceCLM (r + z.re) 2 u‖ := by
  rw [norm_toBesselPotentialSpaceCLM, norm_toBesselPotentialSpaceCLM]
  congr 1
  refine eLpNorm_congr_norm_ae (memLp_one_add_norm_sq_rpow_smul_fourier _ _ 2).aestronglyMeasurable
    (memLp_one_add_norm_sq_rpow_smul_fourier _ _ 2).aestronglyMeasurable (.of_forall fun ξ ↦ ?_)
  have h1 : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  simp only [fourier_besselPotentialCLM_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos h1 _), TauCeti.norm_japaneseBracketCpow]
  rw [← mul_assoc, ← Real.rpow_add h1]
  ring_nf

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
    simp only [hrem, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos h1 _)]
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

section Lp

open scoped NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {p : ℝ≥0∞}

/-- **Bessel potentials of order with nonpositive real part on `Lᵖ`.** For `1 < p < ∞` there is a
constant `C` such that, for every complex order `z` with `re z ≤ 0` and every Schwartz function
`u`, `‖J^z u‖_p ≤ C (1 + ‖z‖) ^ N ‖u‖_p`, where `N = ⌊dim E / 2⌋ + 1`. The symbol `⟨ξ⟩ ^ z`
satisfies Mihlin's condition of order `N` with a constant `O((1 + ‖z‖) ^ N)`, so this is the
Mihlin–Hörmander multiplier theorem. For imaginary orders `z = i τ` it bounds `J^(i τ)` on `Lᵖ`
with polynomial growth in `τ`; for `p = 2` these operators are isometries. -/
theorem exists_eLpNorm_besselPotentialCLM_le (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ z : ℂ, z.re ≤ 0 → ∀ u : 𝓢(E, H),
      eLpNorm (besselPotentialCLM z u) p volume ≤
        C * (1 + ‖z‖ₑ) ^ (Module.finrank ℝ E / 2 + 1) * eLpNorm u p volume := by
  set N := Module.finrank ℝ E / 2 + 1
  have hpow (z : ℂ) : (1 : ℝ≥0∞) ≤ (1 + ‖z‖ₑ) ^ N := one_le_pow₀ le_self_add
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- On the zero space the symbol is the constant `⟨0⟩ ^ z = 1`.
    refine ⟨1, fun z _ u ↦ ?_⟩
    have hsymb : TauCeti.japaneseBracketCpow z = fun _ : E ↦ (1 : ℂ) := funext fun ξ ↦ by
      rw [Subsingleton.elim ξ 0, TauCeti.japaneseBracketCpow_zero_right]
    rw [besselPotentialCLM_def, hsymb, fourierMultiplierCLM_const, one_smul,
      ContinuousLinearMap.id_apply, ENNReal.coe_one, one_mul]
    exact le_mul_of_one_le_left (by positivity) (hpow z)
  have hN : Module.finrank ℝ E < 2 * N := by omega
  obtain ⟨C, hC⟩ :=
    exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le (F := H) hN hp hp_top
  choose D hD using fun k ↦
    TauCeti.exists_norm_iteratedFDeriv_japaneseBracketCpow_le_div_pow (H := E) k
  set D' : ℝ≥0 := ∑ k ∈ Finset.range (N + 1), ‖D k‖₊
  refine ⟨C * D', fun z hz u ↦ ?_⟩
  -- Mihlin's condition of order `N` with constant `D' (1 + ‖z‖) ^ N`.
  have hmihlin : ∀ k ≤ N, ∀ ξ : E, ξ ≠ 0 →
      ‖iteratedFDeriv ℝ k (TauCeti.japaneseBracketCpow z) ξ‖ ≤
        ((D' * (1 + ‖z‖₊) ^ N : ℝ≥0) : ℝ) / ‖ξ‖ ^ k := fun k hk ξ hξ ↦ by
    have hDk : D k ≤ D' := by
      refine (Real.le_norm_self _).trans ?_
      exact_mod_cast Finset.single_le_sum (f := fun k ↦ ‖D k‖₊) (fun i _ ↦ by positivity)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
    have hz1 : (1 : ℝ) ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg z)
    push_cast
    exact (hD k z hz ξ hξ).trans (div_le_div_of_nonneg_right
      (mul_le_mul hDk (pow_le_pow_right₀ hz1 hk) (by positivity) D'.coe_nonneg) (by positivity))
  refine (hC (TauCeti.hasTemperateGrowth_japaneseBracketCpow z) hmihlin u).trans_eq ?_
  push_cast [eNorm_eq_nnNorm]
  ring

/-- **Bessel potentials of complex order on `H^{r,p}`.** For `1 < p < ∞` there is a constant `C`
such that, for every real `r`, every complex order `z` and every Schwartz function `u`,

`‖J^z u‖_{H^{r,p}} ≤ C (1 + |im z|) ^ N ‖u‖_{H^{r + re z, p}}`,  `N = ⌊dim E / 2⌋ + 1`.

So `J^z` maps `H^{r + re z, p}` to `H^{r,p}`, with norm growing at most polynomially in `im z`.
For `p = 2` it is an isometry (`SchwartzMap.norm_toBesselPotentialSpaceCLM_besselPotentialCLM`).
These are the bounds on the analytic family `z ↦ J^z` that Stein's interpolation theorem needs to
interpolate between Bessel-potential spaces with `p ≠ 2`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_besselPotentialCLM_le [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ ∞) :
    ∃ C : ℝ, ∀ (r : ℝ) (z : ℂ) (u : 𝓢(E, H)),
      ‖toBesselPotentialSpaceCLM r p (besselPotentialCLM z u)‖ ≤
        C * (1 + |z.im|) ^ (Module.finrank ℝ E / 2 + 1) *
          ‖toBesselPotentialSpaceCLM (r + z.re) p u‖ := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_besselPotentialCLM_le (E := E) (H := H) hp hp_top
  refine ⟨C, fun r z u ↦ ?_⟩
  -- `J^r J^z u = J^(i im z) (J^(r + re z) u)`, and `J^(i im z)` is bounded on `Lᵖ`.
  have horder : besselPotentialCLM (r : ℂ) (besselPotentialCLM z u) =
      besselPotentialCLM ((z.im : ℂ) * I) (besselPotentialCLM ((r + z.re : ℝ) : ℂ) u) := by
    rw [besselPotentialCLM_besselPotentialCLM_apply, besselPotentialCLM_besselPotentialCLM_apply]
    congr 2
    apply Complex.ext <;> simp [add_comm]
  have hIm : ‖((z.im : ℂ) * I)‖ₑ = ‖z.im‖ₑ := by
    have h : ‖((z.im : ℂ) * I)‖ = ‖z.im‖ := by simp
    rw [← ofReal_norm, h, ofReal_norm]
  have h := hC ((z.im : ℂ) * I) (by simp) (besselPotentialCLM ((r + z.re : ℝ) : ℂ) u)
  rw [hIm] at h
  rw [← BesselPotentialSpace.norm_toLp_eq, ← BesselPotentialSpace.norm_toLp_eq,
    toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM,
    toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM, norm_toLp, norm_toLp, horder]
  have hfin : (C : ℝ≥0∞) * (1 + ‖z.im‖ₑ) ^ (Module.finrank ℝ E / 2 + 1) ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top (by simp))
  calc (eLpNorm (besselPotentialCLM ((z.im : ℂ) * I)
        (besselPotentialCLM ((r + z.re : ℝ) : ℂ) u)) p volume).toReal
      ≤ ((C : ℝ≥0∞) * (1 + ‖z.im‖ₑ) ^ (Module.finrank ℝ E / 2 + 1) *
          eLpNorm (besselPotentialCLM ((r + z.re : ℝ) : ℂ) u) p volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hfin
          ((besselPotentialCLM ((r + z.re : ℝ) : ℂ) u).memLp p volume).eLpNorm_ne_top) h
    _ = C * (1 + |z.im|) ^ (Module.finrank ℝ E / 2 + 1) *
          (eLpNorm (besselPotentialCLM ((r + z.re : ℝ) : ℂ) u) p volume).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_add ENNReal.one_ne_top (by simp)]
        simp

end Lp

end SchwartzMap
