/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Real
import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.Series

/-!
# The sine and cosine of real `H^s` functions near zero

Let `E` be a finite-dimensional real inner product space of dimension `n` and `s > n / 2`, so that
`H^s(E)` is an algebra and every real element `F` of `H^s(E)` has a continuous representative `f`
(`BesselPotentialSpace.continuousRep`). By the action of power series on `H^s`
(`TemperedDistribution.exists_hasSum_mul_pow`), the real functions `sin f - f` and `cos f - 1` lie
in `H^s` again. This file packages them as maps of the real subspace
`BesselPotentialSpace.realSubmodule E h` to itself,

`BesselPotentialSpace.sinSubSelf h hs F = sin f - f`,
`BesselPotentialSpace.cosSubOne h hs F = cos f - 1`

(`BesselPotentialSpace.coeFn_inclusionLp_sinSubSelf`,
`BesselPotentialSpace.coeFn_inclusionLp_cosSubOne`), and shows that both vanish to second order at
zero: they vanish at `0` and have strict derivative `0` there
(`BesselPotentialSpace.hasStrictFDerivAt_sinSubSelf_zero`,
`BesselPotentialSpace.hasStrictFDerivAt_cosSubOne_zero`). So `F ↦ sin f` and `F ↦ cos f - 1` are
strictly differentiable at `0` with derivatives the identity and `0`, which is what an implicit
function argument for an equation involving a phase `exp (i f)` needs at `f = 0`.

Both come from `exp (i f) - 1 - i f = ∑_{n ≥ 1} (i f) ^ (n + 1) / (n + 1)!`. The Lipschitz
estimate for power series on `H^s`
(`TemperedDistribution.exists_norm_toBesselPotentialSpace_sub_le_of_hasSum_mul_pow`) bounds the
differences of this series on the ball of radius `R` by `∑_{n ≥ 1} (C R) ^ n / n! ≤ C R exp (C R)`
times the distance, and this factor tends to `0` with `R`.

## Main declarations

* `BesselPotentialSpace.sinSubSelf`, `BesselPotentialSpace.cosSubOne`: `sin f - f` and
  `cos f - 1` as maps of the real elements of `H^s(E)`.
* `BesselPotentialSpace.hasStrictFDerivAt_sinSubSelf_zero`,
  `BesselPotentialSpace.hasStrictFDerivAt_cosSubOne_zero`: their strict derivatives at `0` vanish.

## References

* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, Section 3.
-/

public section

noncomputable section

open MeasureTheory Module Filter Asymptotics TemperedDistribution
open scoped Nat Topology BesselPotentialSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace BesselPotentialSpace

variable {s : ℝ} {h : 0 ≤ s}

/-! ### The series of `exp (i z) - 1 - i z` -/

/-- The coefficients of `exp (i z) - 1 - i z = ∑ₙ aₙ z ^ (n + 1)`. -/
private def expIRemainderCoeff (n : ℕ) : ℂ :=
  Function.update (fun n : ℕ ↦ (((n + 1)! : ℂ))⁻¹ * Complex.I ^ (n + 1)) 0 0 n

private theorem hasSum_expIRemainderCoeff (z : ℂ) :
    HasSum (fun n ↦ expIRemainderCoeff n * z ^ (n + 1))
      (Complex.exp (Complex.I * z) - 1 - Complex.I * z) := by
  have h := (Complex.hasSum_exp_sub_one (Complex.I * z)).update 0 0
  convert h using 1
  · funext n
    rcases n with _ | n
    · simp [expIRemainderCoeff]
    · simp only [expIRemainderCoeff, ne_eq, Nat.add_one_ne_zero, not_false_eq_true,
        Function.update_of_ne, mul_pow]
      ring
  · simp only [zero_add, Nat.factorial_one, Nat.cast_one, inv_one, pow_one, one_mul]
    ring

private theorem norm_expIRemainderCoeff_le (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖expIRemainderCoeff n‖ * t ^ n ≤ t ^ n / n ! := by
  rcases n with _ | n
  · simp [expIRemainderCoeff]
  · simp only [expIRemainderCoeff, ne_eq, Nat.add_one_ne_zero, not_false_eq_true,
      Function.update_of_ne, norm_mul, norm_inv, Complex.norm_natCast, norm_pow, Complex.norm_I,
      one_pow, mul_one]
    rw [div_eq_inv_mul]
    gcongr
    exact Nat.le_succ _

/-- The Lipschitz factor of the series: its term of index `n + 1` is at most `t tⁿ / n!`, so the
whole factor is at most `t exp t`. -/
private theorem norm_expIRemainderCoeff_succ_mul_le (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖expIRemainderCoeff (n + 1)‖ * ((n + 1 : ℕ) + 1) * t ^ (n + 1) ≤ t * (t ^ n / n !) := by
  simp only [expIRemainderCoeff, ne_eq, Nat.add_one_ne_zero, not_false_eq_true,
    Function.update_of_ne, norm_mul, norm_inv, Complex.norm_natCast, norm_pow, Complex.norm_I,
    one_pow, mul_one]
  have hf : ((n + 1 + 1)! : ℝ) = (n + 1 + 1) * (n + 1)! := by
    push_cast [Nat.factorial_succ]
    ring
  have hle : (n ! : ℝ) ≤ (n + 1)! := by exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  rw [hf, pow_succ]
  push_cast
  calc _ = ((n + 1)! : ℝ)⁻¹ * (t ^ n * t) := by field_simp
    _ ≤ (n ! : ℝ)⁻¹ * (t ^ n * t) := by gcongr
    _ = t * (t ^ n / n !) := by ring

/-! ### The remainder `exp (i F) - 1 - i F` on `H^s` -/

private theorem exists_expIRemainder (hs : finrank ℝ E < 2 * s) (F : H^{s}(E)) :
    ∃ v : H^{s}(E), ∀ᵐ z ∂volume,
      HasSum (fun n ↦ expIRemainderCoeff n * inclusionLp h F z ^ (n + 1)) (inclusionLp h v z) := by
  obtain ⟨C, hC0, hC⟩ := exists_hasSum_mul_pow hs
  set R := C * ‖(memSobolev_inclusionLp h F).toBesselPotentialSpace‖
  have hsum : Summable fun n ↦ ‖expIRemainderCoeff n‖ * R ^ n :=
    (Real.summable_pow_div_factorial R).of_nonneg_of_le (fun n ↦ by positivity)
      fun n ↦ norm_expIRemainderCoeff_le n R (by positivity)
  obtain ⟨v, hv, hvs, -⟩ := hC (memSobolev_inclusionLp h F) hsum
  refine ⟨hvs.toBesselPotentialSpace, ?_⟩
  rw [← toLp_inclusion h hvs.toBesselPotentialSpace,
    toLp_inclusion_toBesselPotentialSpace h hvs rfl]
  exact hv

/-- The element `exp (i F) - 1 - i F` of `H^s(E)`, `s > n / 2`. -/
private def expIRemainder (hs : finrank ℝ E < 2 * s) (h : 0 ≤ s) (F : H^{s}(E)) : H^{s}(E) :=
  (exists_expIRemainder (h := h) hs F).choose

private theorem hasSum_expIRemainder (hs : finrank ℝ E < 2 * s) (F : H^{s}(E)) :
    ∀ᵐ z ∂volume, HasSum (fun n ↦ expIRemainderCoeff n * inclusionLp h F z ^ (n + 1))
      (inclusionLp h (expIRemainder hs h F) z) :=
  (exists_expIRemainder (h := h) hs F).choose_spec

private theorem coeFn_inclusionLp_expIRemainder (hs : finrank ℝ E < 2 * s) (F : H^{s}(E)) :
    ⇑(inclusionLp h (expIRemainder hs h F)) =ᵐ[volume]
      fun z ↦ Complex.exp (Complex.I * inclusionLp h F z) - 1 - Complex.I * inclusionLp h F z := by
  filter_upwards [hasSum_expIRemainder (h := h) hs F] with z hz
  exact hz.unique (hasSum_expIRemainderCoeff _)

private theorem expIRemainder_zero (hs : finrank ℝ E < 2 * s) : expIRemainder hs h 0 = 0 := by
  refine ext_of_ae_eq_inclusionLp h ?_
  filter_upwards [coeFn_inclusionLp_expIRemainder (h := h) hs 0,
    Lp.coeFn_zero ℂ 2 (volume : Measure E)] with z hz h0
  rw [hz, map_zero, h0]
  simp

/-- **The remainder `exp (i F) - 1 - i F` is locally Lipschitz with a small constant.** There is
`C ≥ 0` such that on the ball of radius `R` of `H^s(E)` the remainder has Lipschitz constant at
most `C R exp (C R)`. -/
private theorem exists_norm_expIRemainder_sub_le (hs : finrank ℝ E < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ {F G : H^{s}(E)} {R : ℝ}, ‖F‖ ≤ R → ‖G‖ ≤ R →
      ‖expIRemainder hs h F - expIRemainder hs h G‖ ≤
        C * R * Real.exp (C * R) * ‖F - G‖ := by
  obtain ⟨C, hC, hlip⟩ := exists_norm_toBesselPotentialSpace_sub_le_of_hasSum_mul_pow hs
  refine ⟨C, hC, fun {F G R} hFR hGR ↦ ?_⟩
  have hR : 0 ≤ R := (norm_nonneg F).trans hFR
  have hCR : 0 ≤ C * R := mul_nonneg hC hR
  have hexpsum := (Real.summable_pow_div_factorial (C * R)).mul_left (C * R)
  have hmaj : Summable fun n ↦ ‖expIRemainderCoeff n‖ * (n + 1) * (C * R) ^ n :=
    (summable_nat_add_iff 1).1 <| hexpsum.of_nonneg_of_le (fun n ↦ by positivity)
      fun n ↦ by exact_mod_cast norm_expIRemainderCoeff_succ_mul_le n _ hCR
  have key := hlip (memSobolev_inclusionLp h F) (memSobolev_inclusionLp h G) (R := R)
    (by rwa [toBesselPotentialSpace_memSobolev_inclusionLp])
    (by rwa [toBesselPotentialSpace_memSobolev_inclusionLp]) hmaj
    (memSobolev_inclusionLp h (expIRemainder hs h F))
    (memSobolev_inclusionLp h (expIRemainder hs h G))
    (hasSum_expIRemainder hs F) (hasSum_expIRemainder hs G)
  simp only [toBesselPotentialSpace_memSobolev_inclusionLp] at key
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hexp : Real.exp (C * R) = ∑' n, (C * R) ^ n / n ! := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp, ← tsum_mul_left, hmaj.tsum_eq_zero_add]
  simp only [expIRemainderCoeff, Function.update_self, norm_zero, zero_mul, zero_add]
  exact ((summable_nat_add_iff 1).2 hmaj).tsum_le_tsum
    (fun n ↦ by exact_mod_cast norm_expIRemainderCoeff_succ_mul_le n _ hCR) hexpsum

/-- **The remainder `exp (i F) - 1 - i F` has strict derivative `0` at `0`.** -/
private theorem hasStrictFDerivAt_expIRemainder_zero (hs : finrank ℝ E < 2 * s) :
    HasStrictFDerivAt (𝕜 := ℝ) (expIRemainder hs h) (0 : H^{s}(E) →L[ℝ] H^{s}(E)) 0 := by
  obtain ⟨C, -, hlip⟩ := exists_norm_expIRemainder_sub_le (h := h) hs
  rw [hasStrictFDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  -- On a small ball the Lipschitz constant `C R exp (C R)` is at most `c`.
  obtain ⟨δ, hδ, hδc⟩ : ∃ δ > 0, C * δ * Real.exp (C * δ) ≤ c := by
    have ht : Tendsto (fun δ : ℝ ↦ C * δ * Real.exp (C * δ)) (𝓝 0) (𝓝 0) := by
      have : Continuous fun δ : ℝ ↦ C * δ * Real.exp (C * δ) := by fun_prop
      simpa using this.tendsto 0
    obtain ⟨δ, hδ, hδ'⟩ := Metric.tendsto_nhds_nhds.1 ht c hc
    refine ⟨δ / 2, half_pos hδ, ?_⟩
    have := hδ' (x := δ / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]; linarith)
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  filter_upwards [Metric.closedBall_mem_nhds (0 : H^{s}(E) × H^{s}(E)) hδ] with p hp
  rw [mem_closedBall_zero_iff] at hp
  have h₁ : ‖p.1‖ ≤ δ := (norm_fst_le p).trans hp
  have h₂ : ‖p.2‖ ≤ δ := (norm_snd_le p).trans hp
  rw [show (0 : H^{s}(E) →L[ℝ] H^{s}(E)) (p.1 - p.2) = 0 from rfl, sub_zero]
  exact (hlip h₁ h₂).trans (mul_le_mul_of_nonneg_right hδc (norm_nonneg _))

/-! ### The sine and the cosine -/

variable (h) in
/-- **`sin f - f` for a real element of `H^s`**, `s > n / 2`: the real element of `H^s(E)` whose
function is `sin f - f`, where `f` is the continuous representative of `F`
(`coeFn_inclusionLp_sinSubSelf`). -/
def sinSubSelf (hs : finrank ℝ E < 2 * s) (F : realSubmodule E h) : realSubmodule E h :=
  realPartCLM E h (-Complex.I • expIRemainder hs h F)

variable (h) in
/-- **`cos f - 1` for a real element of `H^s`**, `s > n / 2`: the real element of `H^s(E)` whose
function is `cos f - 1`, where `f` is the continuous representative of `F`
(`coeFn_inclusionLp_cosSubOne`). -/
def cosSubOne (hs : finrank ℝ E < 2 * s) (F : realSubmodule E h) : realSubmodule E h :=
  realPartCLM E h (expIRemainder hs h F)

/-- The function of `sinSubSelf hs F` is `sin f - f`, for the continuous representative `f` of
`F`. -/
theorem coeFn_inclusionLp_sinSubSelf (hs : finrank ℝ E < 2 * s) (F : realSubmodule E h) :
    ⇑(inclusionLp h (sinSubSelf h hs F : H^{s}(E))) =ᵐ[volume]
      fun z ↦ ((Real.sin (continuousRep F z) - continuousRep F z : ℝ) : ℂ) := by
  filter_upwards [coeFn_inclusionLp_realPartCLM (h := h) (-Complex.I • expIRemainder hs h F),
    coeFn_inclusionLp_smul_ae_eq h (-Complex.I) (coeFn_inclusionLp_expIRemainder (h := h) hs F),
    coeFn_inclusionLp_ae_eq_continuousRep hs F] with z h₁ h₂ h₃
  rw [sinSubSelf, h₁, h₂, h₃]
  simp only [smul_eq_mul, mul_comm Complex.I (continuousRep F z : ℂ)]
  rw [Complex.exp_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.mul_re]

/-- The function of `cosSubOne hs F` is `cos f - 1`, for the continuous representative `f` of
`F`. -/
theorem coeFn_inclusionLp_cosSubOne (hs : finrank ℝ E < 2 * s) (F : realSubmodule E h) :
    ⇑(inclusionLp h (cosSubOne h hs F : H^{s}(E))) =ᵐ[volume]
      fun z ↦ ((Real.cos (continuousRep F z) - 1 : ℝ) : ℂ) := by
  filter_upwards [coeFn_inclusionLp_realPartCLM (h := h) (expIRemainder hs h F),
    coeFn_inclusionLp_expIRemainder (h := h) hs F,
    coeFn_inclusionLp_ae_eq_continuousRep hs F] with z h₁ h₂ h₃
  rw [cosSubOne, h₁, h₂, h₃]
  simp only [mul_comm Complex.I (continuousRep F z : ℂ)]
  rw [Complex.exp_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.mul_re]

@[simp]
theorem sinSubSelf_zero (hs : finrank ℝ E < 2 * s) : sinSubSelf h hs 0 = 0 := by
  simp [sinSubSelf, expIRemainder_zero]

@[simp]
theorem cosSubOne_zero (hs : finrank ℝ E < 2 * s) : cosSubOne h hs 0 = 0 := by
  simp [cosSubOne, expIRemainder_zero]

/-- The remainder `exp (i F) - 1 - i F` on the real elements has strict derivative `0` at `0`. -/
private theorem hasStrictFDerivAt_expIRemainder_coe_zero (hs : finrank ℝ E < 2 * s) :
    HasStrictFDerivAt (fun F : realSubmodule E h ↦ expIRemainder hs h F)
      (0 : realSubmodule E h →L[ℝ] H^{s}(E)) 0 := by
  simpa using (hasStrictFDerivAt_expIRemainder_zero (h := h) hs).comp (0 : realSubmodule E h)
    (realSubmodule E h).subtypeL.hasStrictFDerivAt

/-- **`sin f - f` vanishes to second order at `0`**: its strict derivative at `0` is `0`. -/
theorem hasStrictFDerivAt_sinSubSelf_zero (hs : finrank ℝ E < 2 * s) :
    HasStrictFDerivAt (sinSubSelf h hs)
      (0 : realSubmodule E h →L[ℝ] realSubmodule E h) 0 := by
  have hS := ((realPartCLM E h).comp ((-Complex.I : ℂ) • ContinuousLinearMap.id ℝ H^{s}(E))
    ).hasStrictFDerivAt.comp (0 : realSubmodule E h) (hasStrictFDerivAt_expIRemainder_coe_zero hs)
  rw [ContinuousLinearMap.comp_zero] at hS
  exact hS

/-- **`cos f - 1` vanishes to second order at `0`**: its strict derivative at `0` is `0`. -/
theorem hasStrictFDerivAt_cosSubOne_zero (hs : finrank ℝ E < 2 * s) :
    HasStrictFDerivAt (cosSubOne h hs)
      (0 : realSubmodule E h →L[ℝ] realSubmodule E h) 0 := by
  have hC := (realPartCLM E h).hasStrictFDerivAt.comp (0 : realSubmodule E h)
    (hasStrictFDerivAt_expIRemainder_coe_zero hs)
  rw [ContinuousLinearMap.comp_zero] at hC
  exact hC

end BesselPotentialSpace
