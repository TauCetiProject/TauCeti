/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.Analysis.ODE.Gronwall.Integrable
import TauCeti.Analysis.ODE.SecondOrder.Linear

/-!
# Equations with a large parameter: the case of no transition points

Let `Δ` be an open interval of `ℝ`, let `ψ` be continuous on `Δ`, and consider the equation

  `W'' = (u² + ψ(ξ)) W`

for a large parameter `u > 0`. This is the form to which the Liouville transformation
(`TauCeti.deriv_deriv_liouvilleTransform_of_normalized`) brings `w'' = (u² f + g) w` when `f`
has no zeros in the interval. Substituting `W = e^{uξ} ∑ Aₛ(ξ) u⁻ˢ` formally gives `A₀ = 1` and

  `A_{s+1}' = -A_s''/2 + ψ A_s/2`,

each `A_{s+1}` being determined up to an additive constant. For every `α ∈ Δ` and every `n`, if
`A₀, …, A_{n-1}` are `C²` and `A_n` is a primitive as above, the equation has a solution

  `W(ξ) = e^{uξ} (∑_{s<n} Aₛ(ξ) u⁻ˢ + ε(ξ))`

with, for `ξ ≥ α` in `Δ`, the error bounds

  `‖ε(ξ)‖, ‖ε'(ξ)‖ / u ≤ 2 exp((∫_α^ξ ‖ψ‖) / u) (∫_α^ξ ‖A_n'‖) / uⁿ`

(`TauCeti.exists_caseI_solution_norm_le`). Since `A₁' = ψ/2`, the integral `∫_α^ξ ‖ψ‖` is
twice the variation of `A₁`, and these are the bounds of DLMF 2.8.11–2.8.12 for real `ξ`.
Reflecting `ξ ↦ -ξ` gives the solution `e^{-uξ} (∑_{s<n} (-1)ˢ Aₛ(ξ) u⁻ˢ + ε(ξ))` with the same
bounds for `ξ ≤ α`, the integrals being taken over `[ξ, α]`
(`TauCeti.exists_caseI_solution_left_norm_le`).

When `ψ` and `A_n'` are integrable on `[α, b₂)`, where `b₂` is the right end of `Δ`, the first
solution has the expansion

  `e^{-uξ} W(ξ) - ∑_{s<n} Aₛ(ξ) u⁻ˢ = O(u⁻ⁿ)`,
  `e^{-uξ} W'(ξ) - ∑_{s<n} (u Aₛ(ξ) + Aₛ'(ξ)) u⁻ˢ = O(u^{1-n})`

as `u → ∞`, uniformly for `ξ ∈ [α, b₂)` (`TauCeti.exists_caseI_solution`); symmetrically for the
second solution on `(b₁, α]` (`TauCeti.exists_caseI_solution_left`). Uniformity is expressed
along the product filter `𝓟 U ×ˢ atTop`, whose first component is `ξ` and second `u`.

## Proof

Writing `W = e^{uξ} (S + ε)` with `S = ∑_{s<n} Aₛ u⁻ˢ`, the recursion telescopes to
`S'' + 2u S' - ψ S = -2u A_n'/uⁿ`, so that the error satisfies

  `ε'' + 2u ε' = ψ ε + J`,  `J = 2u A_n'/uⁿ`,

and the solution `W` is chosen with `ε(α) = ε'(α) = 0`. Integrating `(e^{2uξ} ε')' = e^{2uξ} G`
and `(ε' + 2u ε)' = G`, where `G = ψ ε + J`, gives

  `ε'(ξ) = ∫_α^ξ e^{-2u(ξ-v)} G(v) dv`,  `2u ε(ξ) = ∫_α^ξ (1 - e^{-2u(ξ-v)}) G(v) dv`,

and Grönwall's inequality (`TauCeti.le_mul_exp_integral_of_le_add_integral_mul`) bounds `ε`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 10, §3.
* NIST Digital Library of Mathematical Functions, §2.8(ii), equations (2.8.10)–(2.8.13),
  <https://dlmf.nist.gov/2.8.ii>.
-/

public section

open Set Filter Finset MeasureTheory Asymptotics
open scoped Topology

namespace TauCeti

section Error

variable {I : Set ℝ} {u α : ℝ} {ε ε₁ : ℝ → ℂ}

/-- The derivative of the complex-valued exponential `y ↦ e^{cy}`. -/
private lemma hasDerivAt_ofReal_exp_mul (c x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (Real.exp (c * y) : ℂ)) (Real.exp (c * x) * c) x := by
  simpa using ((hasDerivAt_id x).const_mul c).exp.ofReal_comp

/-- `e^{-t} e^t = 1` in `ℂ`. -/
private lemma ofReal_exp_neg_mul_ofReal_exp (t : ℝ) : (Real.exp (-t) : ℂ) * Real.exp t = 1 := by
  rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]

/-- `∫_α^y ‖f‖ ≤ ∫_α^x ‖f‖` for `y ∈ [α, x]`. -/
private lemma integral_norm_le_of_mem_Icc {f : ℝ → ℂ} {x y : ℝ} (hf : ContinuousOn f (Icc α x))
    (hy : y ∈ Icc α x) : ∫ v in α..y, ‖f v‖ ≤ ∫ v in α..x, ‖f v‖ :=
  intervalIntegral.integral_mono_interval le_rfl hy.1 hy.2 (ae_of_all _ fun _ ↦ norm_nonneg _)
    (hf.norm.intervalIntegrable_of_Icc (hy.1.trans hy.2))

/-- The error `ε` of the equation `ε'' + 2u ε' = G` with `ε(α) = ε'(α) = 0`, written through
its integrating factors. -/
private lemma caseI_error_eq (hIc : I.OrdConnected) (hα : α ∈ I) {G : ℝ → ℂ}
    (hG : ContinuousOn G I) (hε : ∀ x ∈ I, HasDerivAt ε (ε₁ x) x)
    (hε₁ : ∀ x ∈ I, HasDerivAt ε₁ (G x - 2 * u * ε₁ x) x) (h0 : ε α = 0) (h1 : ε₁ α = 0)
    {x : ℝ} (hx : x ∈ I) :
    ε₁ x = ∫ v in α..x, (Real.exp (2 * u * (v - x)) : ℂ) * G v ∧
      2 * u * ε x = ∫ v in α..x, ((1 - Real.exp (2 * u * (v - x)) : ℝ) : ℂ) * G v := by
  have hsub : uIcc α x ⊆ I := hIc.uIcc_subset hα hx
  have hexp (c : ℝ) : Continuous fun v : ℝ ↦ (Real.exp (2 * u * (v - c)) : ℂ) := by fun_prop
  have hGi : IntervalIntegrable G volume α x := (hG.mono hsub).intervalIntegrable
  have hEi : IntervalIntegrable (fun v ↦ (Real.exp (2 * u * (v - x)) : ℂ) * G v) volume α x :=
    ((hexp x).continuousOn.mul (hG.mono hsub)).intervalIntegrable
  -- `(e^{2u(v - x)} ε₁)' = e^{2u(v - x)} G` and `(ε₁ + 2u ε)' = G`.
  have hF : ∫ v in α..x, (Real.exp (2 * u * (v - x)) : ℂ) * G v = ε₁ x := by
    have hd (v : ℝ) (hv : v ∈ uIcc α x) : HasDerivAt
        (fun t ↦ (Real.exp (2 * u * (t - x)) : ℂ) * ε₁ t)
        ((Real.exp (2 * u * (v - x)) : ℂ) * G v) v := by
      convert (hasDerivAt_ofReal_exp_mul (2 * u) (v - x)).comp_sub_const v x |>.mul
        (hε₁ v (hsub hv)) using 1
      push_cast
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hEi]
    simp [h1]
  have hH : ∫ v in α..x, G v = ε₁ x + 2 * u * ε x := by
    have hd (v : ℝ) (hv : v ∈ uIcc α x) :
        HasDerivAt (fun t ↦ ε₁ t + 2 * u * ε t) (G v) v := by
      convert (hε₁ v (hsub hv)).add ((hε v (hsub hv)).const_mul (2 * (u : ℂ))) using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hGi]
    simp [h0, h1]
  refine ⟨hF.symm, ?_⟩
  simp_rw [Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul]
  rw [intervalIntegral.integral_sub hGi hEi, hH, hF]
  ring

/-- If `ε'' + 2u ε' = ψ ε + J` on `I` with `ε(α) = ε'(α) = 0`, then for `x ≥ α` in `I` both
`‖ε' x‖` and `2u ‖ε x‖` are at most `∫_α^x (‖ψ‖ ‖ε‖ + ‖J‖)`, since the weights
`e^{2u(v - x)}` and `1 - e^{2u(v - x)}` of `caseI_error_eq` lie in `[0, 1]`. -/
private lemma norm_caseI_error_le_integral (hIc : I.OrdConnected) (hα : α ∈ I) (hu : 0 < u)
    {ψ J : ℝ → ℂ} (hψ : ContinuousOn ψ I) (hJ : ContinuousOn J I)
    (hε : ∀ x ∈ I, HasDerivAt ε (ε₁ x) x)
    (hε₁ : ∀ x ∈ I, HasDerivAt ε₁ (ψ x * ε x + J x - 2 * u * ε₁ x) x) (h0 : ε α = 0)
    (h1 : ε₁ α = 0) {x : ℝ} (hx : x ∈ I) (hαx : α ≤ x) :
    ‖ε₁ x‖ ≤ ∫ v in α..x, ‖ψ v‖ * ‖ε v‖ + ‖J v‖ ∧
      2 * u * ‖ε x‖ ≤ ∫ v in α..x, ‖ψ v‖ * ‖ε v‖ + ‖J v‖ := by
  have hsub : Icc α x ⊆ I := hIc.out hα hx
  have hεc : ContinuousOn ε I := fun y hy ↦ (hε y hy).continuousAt.continuousWithinAt
  have hGc : ContinuousOn (fun v ↦ ψ v * ε v + J v) I := (hψ.mul hεc).add hJ
  obtain ⟨h₁, h₂⟩ := caseI_error_eq (G := fun v ↦ ψ v * ε v + J v) hIc hα hGc hε
    (by simpa using hε₁) h0 h1 hx
  have hw {w : ℝ → ℝ} (hwc : Continuous w) (hw : ∀ v ∈ Icc α x, 0 ≤ w v ∧ w v ≤ 1) :
      ‖∫ v in α..x, (w v : ℂ) * (ψ v * ε v + J v)‖ ≤
        ∫ v in α..x, ‖ψ v‖ * ‖ε v‖ + ‖J v‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hαx).trans
      (intervalIntegral.integral_mono_on hαx ?_ ?_ fun v hv ↦ ?_)
    · exact (((Complex.continuous_ofReal.comp hwc).continuousOn.mul (hGc.mono hsub)).norm)
        |>.intervalIntegrable_of_Icc hαx
    · exact ((hψ.norm.mul hεc.norm).add hJ.norm).mono hsub |>.intervalIntegrable_of_Icc hαx
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw v hv).1]
      calc w v * ‖ψ v * ε v + J v‖ ≤ 1 * ‖ψ v * ε v + J v‖ :=
            mul_le_mul_of_nonneg_right (hw v hv).2 (norm_nonneg _)
        _ ≤ ‖ψ v‖ * ‖ε v‖ + ‖J v‖ := by rw [one_mul, ← norm_mul]; exact norm_add_le _ _
  have he (v : ℝ) (hv : v ∈ Icc α x) : Real.exp (2 * u * (v - x)) ≤ 1 :=
    Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [hv.2]))
  refine ⟨?_, ?_⟩
  · rw [h₁]
    exact hw (w := fun v ↦ Real.exp (2 * u * (v - x))) (by fun_prop)
      fun v hv ↦ ⟨(Real.exp_pos _).le, he v hv⟩
  · have h2u : ‖(2 * u : ℂ)‖ = 2 * u := by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [← h2u, ← norm_mul, h₂]
    exact hw (w := fun v ↦ 1 - Real.exp (2 * u * (v - x))) (by fun_prop)
      fun v hv ↦ ⟨sub_nonneg.2 (he v hv), by linarith [Real.exp_pos (2 * u * (v - x))]⟩

/-- **Error bound.** If `ε'' + 2u ε' = ψ ε + J` on `I` with `ε(α) = ε'(α) = 0`, then for
`x ≥ α` in `I`, `‖ε x‖ ≤ (∫_α^x ‖J‖) / (2u) · exp((∫_α^x ‖ψ‖) / (2u))`. -/
private lemma norm_caseI_error_le (hIc : I.OrdConnected) (hα : α ∈ I) (hu : 0 < u)
    {ψ J : ℝ → ℂ} (hψ : ContinuousOn ψ I) (hJ : ContinuousOn J I)
    (hε : ∀ x ∈ I, HasDerivAt ε (ε₁ x) x)
    (hε₁ : ∀ x ∈ I, HasDerivAt ε₁ (ψ x * ε x + J x - 2 * u * ε₁ x) x) (h0 : ε α = 0)
    (h1 : ε₁ α = 0) {x : ℝ} (hx : x ∈ I) (hαx : α ≤ x) :
    ‖ε x‖ ≤ (∫ v in α..x, ‖J v‖) / (2 * u) * Real.exp ((∫ v in α..x, ‖ψ v‖) / (2 * u)) := by
  have hsub : Icc α x ⊆ I := hIc.out hα hx
  have hεc : ContinuousOn ε I := fun y hy ↦ (hε y hy).continuousAt.continuousWithinAt
  have hu2 : 0 < 2 * u := by positivity
  -- At every `y ∈ [α, x]`, `‖ε y‖ ≤ (∫_α^x ‖J‖) / (2u) + ∫_α^y (‖ψ‖ / (2u)) ‖ε‖`.
  have hrec (y : ℝ) (hy : y ∈ Icc α x) : ‖ε y‖ ≤ (∫ v in α..x, ‖J v‖) / (2 * u) +
      ∫ v in α..y, ‖ψ v‖ / (2 * u) * ‖ε v‖ := by
    have hsy : Icc α y ⊆ I := hIc.out hα (hsub hy)
    have hle := (norm_caseI_error_le_integral hIc hα hu hψ hJ hε hε₁ h0 h1 (hsub hy) hy.1).2
    rw [intervalIntegral.integral_add (f := fun v ↦ ‖ψ v‖ * ‖ε v‖)
      ((hψ.norm.mul hεc.norm).mono hsy |>.intervalIntegrable_of_Icc hy.1)
      ((hJ.norm.mono hsy).intervalIntegrable_of_Icc hy.1)] at hle
    have hJy := integral_norm_le_of_mem_Icc (hJ.mono hsub) hy
    have hdiv : ∫ v in α..y, ‖ψ v‖ / (2 * u) * ‖ε v‖ =
        (∫ v in α..y, ‖ψ v‖ * ‖ε v‖) / (2 * u) := by
      rw [← intervalIntegral.integral_div]; congr 1; ext v; ring
    rw [hdiv, ← add_div, le_div_iff₀ hu2]
    linarith
  have hβ : ContinuousOn (fun v ↦ ‖ψ v‖ / (2 * u)) I := hψ.norm.div_const _
  have key := le_mul_exp_integral_of_le_add_integral_mul (u := fun v ↦ ‖ε v‖)
    (β := fun v ↦ ‖ψ v‖ / (2 * u)) (hβ.mono hsub |>.integrableOn_Icc)
    (ae_of_all _ fun _ ↦ by positivity) ((hβ.mul hεc.norm).mono hsub |>.integrableOn_Icc)
    (ae_restrict_of_forall_mem measurableSet_Icc hrec) ⟨hαx, le_rfl⟩ (hrec x ⟨hαx, le_rfl⟩)
  rwa [intervalIntegral.integral_div] at key

/-- **Derivative bound.** If `ε'' + 2u ε' = ψ ε + J` on `I` with `ε(α) = ε'(α) = 0` and
`‖ε‖ ≤ M` on `[α, x]`, then `‖ε' x‖ ≤ (∫_α^x ‖ψ‖) M + ∫_α^x ‖J‖`. -/
private lemma norm_caseI_error_deriv_le (hIc : I.OrdConnected) (hα : α ∈ I) (hu : 0 < u)
    {ψ J : ℝ → ℂ} (hψ : ContinuousOn ψ I) (hJ : ContinuousOn J I)
    (hε : ∀ x ∈ I, HasDerivAt ε (ε₁ x) x)
    (hε₁ : ∀ x ∈ I, HasDerivAt ε₁ (ψ x * ε x + J x - 2 * u * ε₁ x) x) (h0 : ε α = 0)
    (h1 : ε₁ α = 0) {x M : ℝ} (hx : x ∈ I) (hαx : α ≤ x) (hM : ∀ y ∈ Icc α x, ‖ε y‖ ≤ M) :
    ‖ε₁ x‖ ≤ (∫ v in α..x, ‖ψ v‖) * M + ∫ v in α..x, ‖J v‖ := by
  have hsub : Icc α x ⊆ I := hIc.out hα hx
  have hεc : ContinuousOn ε I := fun y hy ↦ (hε y hy).continuousAt.continuousWithinAt
  refine (norm_caseI_error_le_integral hIc hα hu hψ hJ hε hε₁ h0 h1 hx hαx).1.trans <|
    (intervalIntegral.integral_mono_on (g := fun v ↦ M * ‖ψ v‖ + ‖J v‖) hαx ?_ ?_
      fun v hv ↦ ?_).trans_eq ?_
  · exact ((hψ.norm.mul hεc.norm).add hJ.norm).mono hsub |>.intervalIntegrable_of_Icc hαx
  · exact (continuousOn_const.mul (hψ.norm.mono hsub)).add (hJ.norm.mono hsub)
      |>.intervalIntegrable_of_Icc hαx
  · rw [mul_comm M]; gcongr; exact hM v hv
  · rw [intervalIntegral.integral_add (intervalIntegrable_const.mul_continuousOn
      (hψ.norm.mono (uIcc_of_le hαx ▸ hsub))) ((hJ.norm.mono hsub).intervalIntegrable_of_Icc hαx),
      intervalIntegral.integral_const_mul, mul_comm M]

/-- **Error bounds in the form of DLMF 2.8.12.** If `ε'' + 2u ε' = ψ ε + J` on `I` with
`ε(α) = ε'(α) = 0`, then for `x ≥ α` in `I`, with `K = (∫_α^x ‖J‖) / (2u)`,
`‖ε x‖ ≤ 2 exp((∫_α^x ‖ψ‖) / u) K` and `‖ε' x‖ ≤ 2u exp((∫_α^x ‖ψ‖) / u) K`. -/
private lemma norm_caseI_error_le_and (hIc : I.OrdConnected) (hα : α ∈ I) (hu : 0 < u)
    {ψ J : ℝ → ℂ} (hψ : ContinuousOn ψ I) (hJ : ContinuousOn J I)
    (hε : ∀ x ∈ I, HasDerivAt ε (ε₁ x) x)
    (hε₁ : ∀ x ∈ I, HasDerivAt ε₁ (ψ x * ε x + J x - 2 * u * ε₁ x) x) (h0 : ε α = 0)
    (h1 : ε₁ α = 0) {x : ℝ} (hx : x ∈ I) (hαx : α ≤ x) :
    ‖ε x‖ ≤ 2 * Real.exp ((∫ v in α..x, ‖ψ v‖) / u) * ((∫ v in α..x, ‖J v‖) / (2 * u)) ∧
      ‖ε₁ x‖ ≤ 2 * u * Real.exp ((∫ v in α..x, ‖ψ v‖) / u) *
        ((∫ v in α..x, ‖J v‖) / (2 * u)) := by
  have hsub : Icc α x ⊆ I := hIc.out hα hx
  have hu2 : 0 < 2 * u := by positivity
  set P := ∫ v in α..x, ‖ψ v‖
  set K := (∫ v in α..x, ‖J v‖) / (2 * u)
  have hP : 0 ≤ P := intervalIntegral.integral_nonneg hαx fun _ _ ↦ norm_nonneg _
  have hK : 0 ≤ K := div_nonneg (intervalIntegral.integral_nonneg hαx fun _ _ ↦ norm_nonneg _)
    hu2.le
  -- The bound `K(y) exp(P(y) / (2u))` at `y ∈ [α, x]` is at most its value at `x`.
  have hM (y : ℝ) (hy : y ∈ Icc α x) : ‖ε y‖ ≤ K * Real.exp (P / (2 * u)) := by
    refine (norm_caseI_error_le hIc hα hu hψ hJ hε hε₁ h0 h1 (hsub hy) hy.1).trans ?_
    exact mul_le_mul (div_le_div_of_nonneg_right (integral_norm_le_of_mem_Icc (hJ.mono hsub) hy)
      hu2.le) (Real.exp_le_exp.2 (div_le_div_of_nonneg_right
        (integral_norm_le_of_mem_Icc (hψ.mono hsub) hy) hu2.le)) (Real.exp_pos _).le hK
  -- With `y = P / (2u) ≥ 0`, both bounds follow from `e^y ≤ 2 e^{2y}` and
  -- `y e^y + 1 ≤ e^{2y}`, the latter from `e^y ≥ 1 + y`.
  set y := P / (2 * u)
  have hy : 0 ≤ y := div_nonneg hP hu2.le
  have hPy : P / u = 2 * y := by simp only [y]; field_simp
  have hPu : P = 2 * u * y := by simp only [y]; field_simp
  have hJK : ∫ v in α..x, ‖J v‖ = 2 * u * K := by simp only [K]; field_simp
  have hey := Real.add_one_le_exp y
  have hey0 := Real.exp_pos y
  have hexp : Real.exp (2 * y) = Real.exp y * Real.exp y := by rw [two_mul, Real.exp_add]
  have hd : ‖ε₁ x‖ ≤ 2 * u * y * (K * Real.exp y) + 2 * u * K := by
    have h := norm_caseI_error_deriv_le hIc hα hu hψ hJ hε hε₁ h0 h1 hx hαx hM
    rw [hJK] at h
    rw [← hPu]
    exact h
  rw [hPy, hexp]
  refine ⟨(hM x ⟨hαx, le_rfl⟩).trans (by nlinarith [mul_nonneg hK hey0.le]), hd.trans ?_⟩
  have : y * Real.exp y + 1 ≤ Real.exp y * Real.exp y := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 * u * K)]

end Error

section CaseI

variable {Δ : Set ℝ} {ψ : ℝ → ℂ} {A : ℕ → ℝ → ℂ} {n : ℕ} {α : ℝ}

/-- Since `A₀ = 1` on the open set `Δ`, `A₀' = 0` there. -/
private lemma deriv_caseI_zero (hΔ : IsOpen Δ) (hA0 : ∀ x ∈ Δ, A 0 x = 1) {x : ℝ} (hx : x ∈ Δ) :
    deriv (A 0) x = 0 := by
  rw [Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (1 : ℂ))
    (eventually_of_mem (hΔ.mem_nhds hx) hA0), deriv_const]

/-- The recursion `A_{s+1}' = -A_s''/2 + ψ A_s/2` with `A₀ = 1` telescopes: the formal sum
`S = ∑_{s<n} Aₛ u⁻ˢ` satisfies `S'' + 2u S' - ψ S = -2u A_n' / uⁿ`. -/
private lemma caseI_sum_residual (hΔ : IsOpen Δ) (hA0 : ∀ x ∈ Δ, A 0 x = 1)
    (hrec : ∀ s < n, ∀ x ∈ Δ,
      HasDerivAt (A (s + 1)) (-iteratedDeriv 2 (A s) x / 2 + ψ x * A s x / 2) x)
    {u : ℝ} (hu : 0 < u) {x : ℝ} (hx : x ∈ Δ) :
    ∑ s ∈ range n, (iteratedDeriv 2 (A s) x + 2 * u * deriv (A s) x - ψ x * A s x) / (u : ℂ) ^ s =
      -(2 * u * deriv (A n) x / (u : ℂ) ^ n) := by
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
  set f : ℕ → ℂ := fun s ↦ 2 * u * deriv (A s) x / (u : ℂ) ^ s
  have hterm (s : ℕ) (hs : s ∈ range n) :
      (iteratedDeriv 2 (A s) x + 2 * u * deriv (A s) x - ψ x * A s x) / (u : ℂ) ^ s =
        f s - f (s + 1) := by
    have h := (hrec s (mem_range.1 hs) x hx).deriv
    simp only [f, h, pow_succ]
    field_simp
    ring
  rw [sum_congr rfl hterm, sum_range_sub']
  simp [f, deriv_caseI_zero hΔ hA0 hx]

/-- `deriv (A n)` is continuous on `Δ`. -/
private lemma continuousOn_deriv_caseI (hΔ : IsOpen Δ) (hψ : ContinuousOn ψ Δ)
    (hA0 : ∀ x ∈ Δ, A 0 x = 1) (hA : ∀ s < n, ContDiffOn ℝ 2 (A s) Δ)
    (hrec : ∀ s < n, ∀ x ∈ Δ,
      HasDerivAt (A (s + 1)) (-iteratedDeriv 2 (A s) x / 2 + ψ x * A s x / 2) x) :
    ContinuousOn (deriv (A n)) Δ := by
  cases n with
  | zero =>
    exact continuousOn_const (c := (0 : ℂ)) |>.congr fun x hx ↦ deriv_caseI_zero hΔ hA0 hx
  | succ m =>
    have h2 : ContinuousOn (iteratedDeriv 2 (A m)) Δ := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      exact (((hA m m.lt_succ_self).deriv_of_isOpen hΔ (m := 1) (by norm_num)).deriv_of_isOpen
        hΔ (m := 0) (by norm_num)).continuousOn
    refine ((h2.neg.div_const 2).add ((hψ.mul (hA m m.lt_succ_self).continuousOn).div_const
      2)).congr fun x hx ↦ ?_
    exact (hrec m m.lt_succ_self x hx).deriv

/-- The truncated formal solution `S = ∑_{s<n} Aₛ u⁻ˢ` has derivatives `S' = ∑_{s<n} Aₛ' u⁻ˢ`
and `S'' = ∑_{s<n} Aₛ'' u⁻ˢ` on `Δ`, with `S'' + 2u S' - ψ S = -2u A_n' / uⁿ`. -/
private lemma caseI_formalSum (hΔ : IsOpen Δ) (hA0 : ∀ x ∈ Δ, A 0 x = 1)
    (hA : ∀ s < n, ContDiffOn ℝ 2 (A s) Δ)
    (hrec : ∀ s < n, ∀ x ∈ Δ,
      HasDerivAt (A (s + 1)) (-iteratedDeriv 2 (A s) x / 2 + ψ x * A s x / 2) x)
    {u : ℝ} (hu : 0 < u) {x : ℝ} (hx : x ∈ Δ) :
    HasDerivAt (fun y ↦ ∑ s ∈ range n, A s y / (u : ℂ) ^ s)
        (∑ s ∈ range n, deriv (A s) x / (u : ℂ) ^ s) x ∧
      HasDerivAt (fun y ↦ ∑ s ∈ range n, deriv (A s) y / (u : ℂ) ^ s)
        (∑ s ∈ range n, iteratedDeriv 2 (A s) x / (u : ℂ) ^ s) x ∧
      ∑ s ∈ range n, iteratedDeriv 2 (A s) x / (u : ℂ) ^ s +
          2 * u * ∑ s ∈ range n, deriv (A s) x / (u : ℂ) ^ s -
          ψ x * ∑ s ∈ range n, A s x / (u : ℂ) ^ s =
        -(2 * u * deriv (A n) x / (u : ℂ) ^ n) := by
  have hAd (s : ℕ) (hs : s ∈ range n) :=
    (hA s (mem_range.1 hs)).hasDerivAt_and_hasDerivAt_deriv hΔ hx
  refine ⟨HasDerivAt.fun_sum fun s hs ↦ (hAd s hs).1.div_const _,
    HasDerivAt.fun_sum fun s hs ↦ (hAd s hs).2.div_const _, ?_⟩
  rw [← caseI_sum_residual hΔ hA0 hrec hu hx]
  simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun s _ ↦ ?_
  ring

/-- If `W'' = (u² + ψ) W` and `S'' + 2u S' - ψ S = -J` at `x`, then the error
`ε = e^{-uy} W - S` has derivative `ε₁ = e^{-uy} (W' - u W) - S'` at `x`, and
`ε₁' = ψ ε + J - 2u ε₁` there. -/
private lemma caseI_error_hasDerivAt {u x : ℝ} {W S S₁ : ℝ → ℂ} {S₂ ψx Jx : ℂ}
    (hW : HasDerivAt W (deriv W x) x) (hW' : HasDerivAt (deriv W) ((u ^ 2 + ψx) * W x) x)
    (hS : HasDerivAt S (S₁ x) x) (hS₁ : HasDerivAt S₁ S₂ x)
    (hkey : S₂ + 2 * u * S₁ x - ψx * S x = -Jx) :
    HasDerivAt (fun y ↦ (Real.exp (-(u * y)) : ℂ) * W y - S y)
        ((Real.exp (-(u * x)) : ℂ) * (deriv W x - u * W x) - S₁ x) x ∧
      HasDerivAt (fun y ↦ (Real.exp (-(u * y)) : ℂ) * (deriv W y - u * W y) - S₁ y)
        (ψx * ((Real.exp (-(u * x)) : ℂ) * W x - S x) + Jx -
          2 * u * ((Real.exp (-(u * x)) : ℂ) * (deriv W x - u * W x) - S₁ x)) x := by
  have hE : HasDerivAt (fun y : ℝ ↦ (Real.exp (-(u * y)) : ℂ))
      ((Real.exp (-(u * x)) : ℂ) * -u) x := by
    simpa only [neg_mul, Complex.ofReal_neg] using hasDerivAt_ofReal_exp_mul (-u) x
  refine ⟨(hE.mul hW).sub hS |>.congr_deriv (by ring), ?_⟩
  refine (hE.mul (hW'.fun_sub (hW.const_mul (u : ℂ)))).sub hS₁ |>.congr_deriv ?_
  linear_combination -hkey

/-- **Case I, explicit error bounds.** Let `Δ` be an open interval, `ψ` continuous on `Δ`, and
let `A₀ = 1, A₁, …, A_n` satisfy `A_{s+1}' = -A_s''/2 + ψ A_s/2` on `Δ` for `s < n`, with
`A₀, …, A_{n-1}` of class `C²` on `Δ`. For every `α ∈ Δ` and `u > 0`, the equation
`W'' = (u² + ψ) W` has a solution `W`, `C²` on `Δ`, of the form
`W(x) = e^{ux} (∑_{s<n} Aₛ(x) u⁻ˢ + ε(x))`, whose error satisfies, for `x ≥ α` in `Δ`,
`‖ε(x)‖ ≤ 2 exp((∫_α^x ‖ψ‖) / u) (∫_α^x ‖A_n'‖) / uⁿ` and
`‖ε'(x)‖ ≤ 2u exp((∫_α^x ‖ψ‖) / u) (∫_α^x ‖A_n'‖) / uⁿ`.
Since `A₁' = ψ / 2`, these are the bounds of DLMF 2.8.11–2.8.12 (Olver, Chapter 10,
Theorem 3.1) for real `x`, with the variations of `A₁` and `A_n` taken over `[α, x]`. -/
theorem exists_caseI_solution_norm_le (hΔ : IsOpen Δ) (hΔc : Δ.OrdConnected)
    (hψ : ContinuousOn ψ Δ) (hA0 : ∀ x ∈ Δ, A 0 x = 1) (hA : ∀ s < n, ContDiffOn ℝ 2 (A s) Δ)
    (hrec : ∀ s < n, ∀ x ∈ Δ,
      HasDerivAt (A (s + 1)) (-iteratedDeriv 2 (A s) x / 2 + ψ x * A s x / 2) x)
    (hα : α ∈ Δ) {u : ℝ} (hu : 0 < u) :
    ∃ W ε : ℝ → ℂ, ContDiffOn ℝ 2 W Δ ∧ DifferentiableOn ℝ ε Δ ∧
      ∀ x ∈ Δ, iteratedDeriv 2 W x = ((u : ℂ) ^ 2 + ψ x) * W x ∧
        W x = Real.exp (u * x) * (∑ s ∈ range n, A s x / (u : ℂ) ^ s + ε x) ∧
        (α ≤ x → ‖ε x‖ ≤ 2 * Real.exp ((∫ v in α..x, ‖ψ v‖) / u) *
            (∫ v in α..x, ‖deriv (A n) v‖) / u ^ n ∧
          ‖deriv ε x‖ ≤ 2 * u * Real.exp ((∫ v in α..x, ‖ψ v‖) / u) *
            (∫ v in α..x, ‖deriv (A n) v‖) / u ^ n) := by
  -- The truncated formal solution `S`, its derivative `S₁`, and the solution `W` with
  -- `W = e^{uα} S` and `W' = e^{uα} (u S + S₁)` at `α`.
  set S : ℝ → ℂ := fun y ↦ ∑ s ∈ range n, A s y / (u : ℂ) ^ s
  set S₁ : ℝ → ℂ := fun y ↦ ∑ s ∈ range n, deriv (A s) y / (u : ℂ) ^ s
  have hF (x : ℝ) (hx : x ∈ Δ) := caseI_formalSum hΔ hA0 hA hrec hu hx
  obtain ⟨W, hWc, hW, hWα, hW'α⟩ := exists_contDiffOn_iteratedDeriv_eq_mul hΔ hΔc
    (continuousOn_const.add hψ) hα ((Real.exp (u * α) : ℂ) * S α)
    ((Real.exp (u * α) : ℂ) * (u * S α + S₁ α))
  have hEE (y : ℝ) := ofReal_exp_neg_mul_ofReal_exp (u * y)
  -- The error `ε = e^{-ux} W - S` satisfies `ε'' + 2u ε' = ψ ε + J`, `ε(α) = ε'(α) = 0`.
  set ε : ℝ → ℂ := fun y ↦ (Real.exp (-(u * y)) : ℂ) * W y - S y
  set ε₁ : ℝ → ℂ := fun y ↦ (Real.exp (-(u * y)) : ℂ) * (deriv W y - u * W y) - S₁ y
  set J : ℝ → ℂ := fun y ↦ 2 * u * deriv (A n) y / (u : ℂ) ^ n
  have hε (x : ℝ) (hx : x ∈ Δ) : HasDerivAt ε (ε₁ x) x ∧
      HasDerivAt ε₁ (ψ x * ε x + J x - 2 * u * ε₁ x) x := by
    have hWd := hWc.hasDerivAt_and_hasDerivAt_deriv hΔ hx
    exact caseI_error_hasDerivAt hWd.1 (hW x hx ▸ hWd.2) (hF x hx).1 (hF x hx).2.1
      (hF x hx).2.2
  have h0 : ε α = 0 := by
    simp only [ε, hWα]
    linear_combination S α * hEE α
  have h1 : ε₁ α = 0 := by
    simp only [ε₁, hW'α, hWα]
    linear_combination S₁ α * hEE α
  have hJ : ContinuousOn J Δ :=
    (continuousOn_const.mul (continuousOn_deriv_caseI hΔ hψ hA0 hA hrec)).div_const _
  refine ⟨W, ε, hWc, fun x hx ↦ (hε x hx).1.differentiableAt.differentiableWithinAt,
    fun x hx ↦ ⟨hW x hx, by simp only [ε]; linear_combination (-(W x)) * hEE x, fun hαx ↦ ?_⟩⟩
  obtain ⟨hb, hb₁⟩ := norm_caseI_error_le_and hΔc hα hu hψ hJ (fun x hx ↦ (hε x hx).1)
    (fun x hx ↦ (hε x hx).2) h0 h1 hx hαx
  have hJn : (∫ v in α..x, ‖J v‖) / (2 * u) = (∫ v in α..x, ‖deriv (A n) v‖) / u ^ n := by
    have hn (v : ℝ) : ‖J v‖ = 2 * u / u ^ n * ‖deriv (A n) v‖ := by
      simp only [J, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le,
        Complex.norm_two]
      ring
    simp_rw [hn, intervalIntegral.integral_const_mul]
    field_simp
  rw [hJn, ← mul_div_assoc] at hb hb₁
  exact ⟨hb, (hε x hx).1.deriv ▸ hb₁⟩

/-- **Case I, the solution with `e^{-ux}`, explicit error bounds.** Under the hypotheses of
`TauCeti.exists_caseI_solution_norm_le`, for every `α ∈ Δ` and `u > 0` the equation
`W'' = (u² + ψ) W` has a solution `W`, `C²` on `Δ`, of the form
`W(x) = e^{-ux} (∑_{s<n} (-1)ˢ Aₛ(x) u⁻ˢ + ε(x))`, whose error satisfies, for `x ≤ α` in `Δ`,
`‖ε(x)‖ ≤ 2 exp((∫_x^α ‖ψ‖) / u) (∫_x^α ‖A_n'‖) / uⁿ` and
`‖ε'(x)‖ ≤ 2u exp((∫_x^α ‖ψ‖) / u) (∫_x^α ‖A_n'‖) / uⁿ` (DLMF 2.8.11–2.8.12 for `j = 2`). -/
theorem exists_caseI_solution_left_norm_le (hΔ : IsOpen Δ) (hΔc : Δ.OrdConnected)
    (hψ : ContinuousOn ψ Δ) (hA0 : ∀ x ∈ Δ, A 0 x = 1) (hA : ∀ s < n, ContDiffOn ℝ 2 (A s) Δ)
    (hrec : ∀ s < n, ∀ x ∈ Δ,
      HasDerivAt (A (s + 1)) (-iteratedDeriv 2 (A s) x / 2 + ψ x * A s x / 2) x)
    (hα : α ∈ Δ) {u : ℝ} (hu : 0 < u) :
    ∃ W ε : ℝ → ℂ, ContDiffOn ℝ 2 W Δ ∧ DifferentiableOn ℝ ε Δ ∧
      ∀ x ∈ Δ, iteratedDeriv 2 W x = ((u : ℂ) ^ 2 + ψ x) * W x ∧
        W x = Real.exp (-(u * x)) * (∑ s ∈ range n, (-1) ^ s * A s x / (u : ℂ) ^ s + ε x) ∧
        (x ≤ α → ‖ε x‖ ≤ 2 * Real.exp ((∫ v in x..α, ‖ψ v‖) / u) *
            (∫ v in x..α, ‖deriv (A n) v‖) / u ^ n ∧
          ‖deriv ε x‖ ≤ 2 * u * Real.exp ((∫ v in x..α, ‖ψ v‖) / u) *
            (∫ v in x..α, ‖deriv (A n) v‖) / u ^ n) := by
  -- Apply the first solution to the reflected data `ψ(-y)` and `(-1)ˢ Aₛ(-y)` on `-Δ`.
  have hmaps : MapsTo (fun y : ℝ ↦ -y) (Neg.neg ⁻¹' Δ) Δ := fun _ hy ↦ hy
  have hmaps' : MapsTo (fun y : ℝ ↦ -y) Δ (Neg.neg ⁻¹' Δ) := fun _ hy ↦ by simpa using hy
  obtain ⟨W, ε, hWc, hεd, h⟩ := exists_caseI_solution_norm_le (Δ := Neg.neg ⁻¹' Δ)
    (ψ := fun y ↦ ψ (-y)) (A := fun s y ↦ (-1) ^ s * A s (-y)) (n := n) (α := -α)
    (hΔ.preimage continuous_neg) (hΔc.preimage_anti fun _ _ h ↦ neg_le_neg h)
    (hψ.comp continuous_neg.continuousOn hmaps) (fun y hy ↦ by simp [hA0 _ hy])
    (fun s hs ↦ contDiffOn_const.mul ((hA s hs).comp contDiff_neg.contDiffOn hmaps))
    (fun s hs y hy ↦ by
      have h := ((hrec s hs (-y) hy).scomp y (hasDerivAt_neg y)).const_mul ((-1 : ℂ) ^ (s + 1))
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_neg]
      refine h.congr_deriv ?_
      rw [neg_one_sq, one_smul, neg_one_smul, pow_succ]
      ring) (by simpa using hα) hu
  have hψint (x : ℝ) : ∫ v in -α..-x, ‖ψ (-v)‖ = ∫ v in x..α, ‖ψ v‖ := by
    rw [intervalIntegral.integral_comp_neg (fun v ↦ ‖ψ v‖), neg_neg, neg_neg]
  have hAint (x : ℝ) : ∫ v in -α..-x, ‖deriv (fun y ↦ (-1 : ℂ) ^ n * A n (-y)) v‖ =
      ∫ v in x..α, ‖deriv (A n) v‖ := by
    have hv (v : ℝ) : ‖deriv (fun y ↦ (-1 : ℂ) ^ n * A n (-y)) v‖ = ‖deriv (A n) (-v)‖ := by
      rw [deriv_const_mul_field, deriv_comp_neg]
      simp
    simp_rw [hv]
    rw [intervalIntegral.integral_comp_neg (fun v ↦ ‖deriv (A n) v‖), neg_neg, neg_neg]
  refine ⟨fun x ↦ W (-x), fun x ↦ ε (-x), hWc.comp contDiff_neg.contDiffOn hmaps',
    hεd.comp (differentiableOn_neg _) hmaps', fun x hx ↦ ?_⟩
  obtain ⟨h1, h2, h3⟩ := h (-x) (hmaps' hx)
  refine ⟨?_, ?_, fun hxα ↦ ?_⟩
  · rw [iteratedDeriv_comp_neg, h1]
    simp
  · simpa only [neg_neg, mul_neg] using h2
  · obtain ⟨hb, hb'⟩ := h3 (neg_le_neg hxα)
    rw [hψint, hAint] at hb hb'
    refine ⟨hb, ?_⟩
    rwa [deriv_comp_neg, norm_neg]

/-- The derivative of `W = e^{σuy} (∑_{s<n} Bₛ u⁻ˢ + ε)` at `x ∈ Δ`. -/
private lemma caseI_deriv_eq {Δ : Set ℝ} (hΔ : IsOpen Δ) {σ u : ℝ} {B : ℕ → ℝ → ℂ}
    (hB : ∀ s < n, ∀ x ∈ Δ, DifferentiableAt ℝ (B s) x) {W ε : ℝ → ℂ}
    (hW : ∀ x ∈ Δ, W x = Real.exp (σ * u * x) * (∑ s ∈ range n, B s x / (u : ℂ) ^ s + ε x))
    (hεd : DifferentiableOn ℝ ε Δ) {x : ℝ} (hx : x ∈ Δ) :
    deriv W x = Real.exp (σ * u * x) * (σ * u * (∑ s ∈ range n, B s x / (u : ℂ) ^ s + ε x) +
      (∑ s ∈ range n, deriv (B s) x / (u : ℂ) ^ s + deriv ε x)) := by
  have he := hasDerivAt_ofReal_exp_mul (σ * u) x
  have hS : HasDerivAt (fun y ↦ ∑ s ∈ range n, B s y / (u : ℂ) ^ s + ε y)
      (∑ s ∈ range n, deriv (B s) x / (u : ℂ) ^ s + deriv ε x) x :=
    (HasDerivAt.fun_sum fun s hs ↦ ((hB s (mem_range.1 hs) x hx).hasDerivAt.div_const _)).add
      (hεd.differentiableAt (hΔ.mem_nhds hx)).hasDerivAt
  rw [Filter.EventuallyEq.deriv_eq (eventually_of_mem (hΔ.mem_nhds hx) hW)]
  exact (he.mul hS).deriv.trans (by push_cast; ring)

/-- Uniform expansions of `W u = e^{σux} (∑_{s<n} Bₛ u⁻ˢ + ε u)` and of its derivative from
bounds `‖ε u x‖ ≤ C / uⁿ` and `‖ε u' x‖ ≤ u C / uⁿ` for `u ≥ 1` and `x ∈ U`. -/
private lemma caseI_isBigO {Δ U : Set ℝ} (hΔ : IsOpen Δ) (hU : U ⊆ Δ) {σ : ℝ} (hσ : |σ| = 1)
    {B : ℕ → ℝ → ℂ} (hB : ∀ s < n, ∀ x ∈ Δ, DifferentiableAt ℝ (B s) x) {W ε : ℝ → ℝ → ℂ}
    {C : ℝ} (hW : ∀ u, 1 ≤ u → ∀ x ∈ Δ,
      W u x = Real.exp (σ * u * x) * (∑ s ∈ range n, B s x / (u : ℂ) ^ s + ε u x))
    (hεd : ∀ u, 1 ≤ u → DifferentiableOn ℝ (ε u) Δ)
    (hb : ∀ u, 1 ≤ u → ∀ x ∈ U, ‖ε u x‖ ≤ C / u ^ n ∧ ‖deriv (ε u) x‖ ≤ u * C / u ^ n) :
    (fun p : ℝ × ℝ ↦ (Real.exp (-(σ * p.2 * p.1)) : ℂ) * W p.2 p.1 -
        ∑ s ∈ range n, B s p.1 / (p.2 : ℂ) ^ s) =O[𝓟 U ×ˢ atTop] (fun p ↦ (p.2 ^ n)⁻¹) ∧
      (fun p : ℝ × ℝ ↦ (Real.exp (-(σ * p.2 * p.1)) : ℂ) * deriv (W p.2) p.1 -
        ∑ s ∈ range n, ((σ : ℂ) * p.2 * B s p.1 + deriv (B s) p.1) / (p.2 : ℂ) ^ s)
        =O[𝓟 U ×ˢ atTop] (fun p ↦ p.2 / p.2 ^ n) := by
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓟 U ×ˢ atTop, p.1 ∈ U ∧ 1 ≤ p.2 :=
    prod_mem_prod (mem_principal_self U) (eventually_ge_atTop 1)
  have hEE (u x : ℝ) := ofReal_exp_neg_mul_ofReal_exp (σ * u * x)
  refine ⟨IsBigO.of_bound C ?_, IsBigO.of_bound (2 * C) ?_⟩
  · filter_upwards [hev] with ⟨x, u⟩ ⟨hx, hu⟩
    rw [hW u hu x (hU hx), ← mul_assoc, hEE, one_mul, add_sub_cancel_left,
      Real.norm_of_nonneg (inv_nonneg.2 (pow_nonneg (zero_le_one.trans hu) n)),
      ← div_eq_mul_inv]
    exact (hb u hu x hx).1
  · filter_upwards [hev] with ⟨x, u⟩ ⟨hx, hu⟩
    have hu0 : 0 < u := one_pos.trans_le hu
    -- The remainder is `σ u ε + ε'`.
    have heq : (σ : ℂ) * u * (∑ s ∈ range n, B s x / (u : ℂ) ^ s + ε u x) +
        (∑ s ∈ range n, deriv (B s) x / (u : ℂ) ^ s + deriv (ε u) x) -
        ∑ s ∈ range n, ((σ : ℂ) * u * B s x + deriv (B s) x) / (u : ℂ) ^ s =
        (σ : ℂ) * u * ε u x + deriv (ε u) x := by
      simp only [add_div, sum_add_distrib, mul_div_assoc, ← mul_sum]
      ring
    have h1 : ‖(σ : ℂ) * u * ε u x‖ = u * ‖ε u x‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, hσ,
        one_mul, Real.norm_of_nonneg hu0.le]
    rw [caseI_deriv_eq hΔ hB (hW u hu) (hεd u hu) (hU hx), ← mul_assoc, hEE, one_mul, heq,
      Real.norm_of_nonneg (div_nonneg hu0.le (pow_nonneg hu0.le n))]
    obtain ⟨hb1, hb2⟩ := hb u hu x hx
    calc ‖(σ : ℂ) * u * ε u x + deriv (ε u) x‖ ≤ u * ‖ε u x‖ + ‖deriv (ε u) x‖ :=
          h1 ▸ norm_add_le _ _
      _ ≤ u * (C / u ^ n) + u * C / u ^ n := by gcongr
      _ = 2 * C * (u / u ^ n) := by ring

/-- The explicit bounds `2 exp((∫_a^b ‖f‖) / u) (∫_a^b ‖g‖) / uⁿ` and `2u` times it, for
`f` and `g` integrable on a set `U ⊇ (a, b]` and `u ≥ 1`, are at most `C / uⁿ` and `u C / uⁿ`
with `C = 2 exp(∫_U ‖f‖) ∫_U ‖g‖`. -/
private lemma caseI_bounds_le {U : Set ℝ} {f g : ℝ → ℂ} (hf : IntegrableOn f U)
    (hg : IntegrableOn g U) {a b u e e' : ℝ} (hab : a ≤ b) (hsub : Ioc a b ⊆ U) (hu : 1 ≤ u)
    (he : e ≤ 2 * Real.exp ((∫ v in a..b, ‖f v‖) / u) * (∫ v in a..b, ‖g v‖) / u ^ n)
    (he' : e' ≤ 2 * u * Real.exp ((∫ v in a..b, ‖f v‖) / u) * (∫ v in a..b, ‖g v‖) / u ^ n) :
    e ≤ 2 * Real.exp (∫ v in U, ‖f v‖) * (∫ v in U, ‖g v‖) / u ^ n ∧
      e' ≤ u * (2 * Real.exp (∫ v in U, ‖f v‖) * ∫ v in U, ‖g v‖) / u ^ n := by
  have hu0 : 0 < u := one_pos.trans_le hu
  have hint {h : ℝ → ℂ} (hh : IntegrableOn h U) : ∫ v in a..b, ‖h v‖ ≤ ∫ v in U, ‖h v‖ := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_mono_set hh.norm (ae_of_all _ fun _ ↦ norm_nonneg _)
      (Eventually.of_forall hsub)
  have hP : 0 ≤ ∫ v in a..b, ‖f v‖ := intervalIntegral.integral_nonneg hab fun _ _ ↦ norm_nonneg _
  have hle : 2 * Real.exp ((∫ v in a..b, ‖f v‖) / u) * (∫ v in a..b, ‖g v‖) / u ^ n ≤
      2 * Real.exp (∫ v in U, ‖f v‖) * (∫ v in U, ‖g v‖) / u ^ n := by
    have hPu := (div_le_self hP hu).trans (hint hf)
    have hQ : 0 ≤ ∫ v in a..b, ‖g v‖ := intervalIntegral.integral_nonneg hab fun _ _ ↦ norm_nonneg _
    gcongr
    exact hint hg
  refine ⟨he.trans hle, he'.trans (le_trans (le_of_eq ?_)
    ((mul_le_mul_of_nonneg_left hle hu0.le).trans_eq ?_))⟩ <;> ring

/-- **Case I** (DLMF 2.8.10–2.8.13; Olver, Chapter 10, Theorem 3.1). Let `Δ` be an open
interval, `ψ` continuous on `Δ`, and let `A₀ = 1, A₁, …, A_n` satisfy
`A_{s+1}' = -A_s''/2 + ψ A_s/2` on `Δ` for `s < n`, with `A₀, …, A_{n-1}` of class `C²`. Let
`α ∈ Δ`, and let `ψ` (that is, `2 A₁'` when `n ≥ 1`) and `A_n'` be integrable on
`Δ₁ = [α, ∞) ∩ Δ`. Then there are solutions
`W u` of `W'' = (u² + ψ) W` on `Δ`, for `u > 0`, with
`e^{-ux} W u x - ∑_{s<n} Aₛ(x) u⁻ˢ = O(u⁻ⁿ)` and
`e^{-ux} (W u)'(x) - ∑_{s<n} (u Aₛ(x) + Aₛ'(x)) u⁻ˢ = O(u^{1-n})` as `u → ∞`, uniformly for
`x ∈ Δ₁`. -/
theorem exists_caseI_solution (hΔ : IsOpen Δ) (hΔc : Δ.OrdConnected)
    (hψ : ContinuousOn ψ Δ) (hA0 : ∀ x ∈ Δ, A 0 x = 1) (hA : ∀ s < n, ContDiffOn ℝ 2 (A s) Δ)
    (hrec : ∀ s < n, ∀ x ∈ Δ,
      HasDerivAt (A (s + 1)) (-iteratedDeriv 2 (A s) x / 2 + ψ x * A s x / 2) x)
    (hα : α ∈ Δ) (hψi : IntegrableOn ψ (Ici α ∩ Δ))
    (hAi : IntegrableOn (deriv (A n)) (Ici α ∩ Δ)) :
    ∃ W : ℝ → ℝ → ℂ, (∀ u > 0, ContDiffOn ℝ 2 (W u) Δ ∧
        ∀ x ∈ Δ, iteratedDeriv 2 (W u) x = ((u : ℂ) ^ 2 + ψ x) * W u x) ∧
      (fun p : ℝ × ℝ ↦ (Real.exp (-(p.2 * p.1)) : ℂ) * W p.2 p.1 -
        ∑ s ∈ range n, A s p.1 / (p.2 : ℂ) ^ s) =O[𝓟 (Ici α ∩ Δ) ×ˢ atTop]
          (fun p ↦ (p.2 ^ n)⁻¹) ∧
      (fun p : ℝ × ℝ ↦ (Real.exp (-(p.2 * p.1)) : ℂ) * deriv (W p.2) p.1 -
        ∑ s ∈ range n, (p.2 * A s p.1 + deriv (A s) p.1) / (p.2 : ℂ) ^ s)
          =O[𝓟 (Ici α ∩ Δ) ×ˢ atTop] (fun p ↦ p.2 / p.2 ^ n) := by
  choose! W ε hWc hεd h using fun u (hu : 0 < u) ↦
    exists_caseI_solution_norm_le hΔ hΔc hψ hA0 hA hrec hα hu
  have hsub (x : ℝ) (hx : x ∈ Ici α ∩ Δ) : Ioc α x ⊆ Ici α ∩ Δ := fun v hv ↦
    ⟨le_of_lt hv.1, hΔc.out hα hx.2 ⟨le_of_lt hv.1, hv.2⟩⟩
  have hB (s : ℕ) (hs : s < n) (x : ℝ) (hx : x ∈ Δ) : DifferentiableAt ℝ (A s) x :=
    ((hA s hs).differentiableOn (by norm_num)).differentiableAt (hΔ.mem_nhds hx)
  obtain ⟨h1, h2⟩ := caseI_isBigO (U := Ici α ∩ Δ) (σ := 1) (W := W) (ε := ε)
    (C := 2 * Real.exp (∫ v in Ici α ∩ Δ, ‖ψ v‖) * ∫ v in Ici α ∩ Δ, ‖deriv (A n) v‖)
    hΔ inter_subset_right (by simp) hB
    (fun u hu x hx ↦ by simpa using (h u (one_pos.trans_le hu) x hx).2.1)
    (fun u hu ↦ hεd u (one_pos.trans_le hu)) fun u hu x hx ↦
      caseI_bounds_le hψi hAi hx.1 (hsub x hx) hu
        ((h u (one_pos.trans_le hu) x hx.2).2.2 hx.1).1
        ((h u (one_pos.trans_le hu) x hx.2).2.2 hx.1).2
  refine ⟨W, fun u hu ↦ ⟨hWc u hu, fun x hx ↦ (h u hu x hx).1⟩, ?_, ?_⟩
  · simpa using h1
  · simpa using h2

/-- **Case I, the solution with `e^{-ux}`** (DLMF 2.8.10–2.8.13 for `j = 2`). Under the
hypotheses of `TauCeti.exists_caseI_solution`, with `ψ` and `A_n'` integrable on
`Δ₂ = (-∞, α] ∩ Δ` instead, there are solutions `W u` of `W'' = (u² + ψ) W` on `Δ`, for
`u > 0`, with `e^{ux} W u x - ∑_{s<n} (-1)ˢ Aₛ(x) u⁻ˢ = O(u⁻ⁿ)` and
`e^{ux} (W u)'(x) - ∑_{s<n} (-1)ˢ (-u Aₛ(x) + Aₛ'(x)) u⁻ˢ = O(u^{1-n})` as `u → ∞`,
uniformly for `x ∈ Δ₂`. -/
theorem exists_caseI_solution_left (hΔ : IsOpen Δ) (hΔc : Δ.OrdConnected)
    (hψ : ContinuousOn ψ Δ) (hA0 : ∀ x ∈ Δ, A 0 x = 1) (hA : ∀ s < n, ContDiffOn ℝ 2 (A s) Δ)
    (hrec : ∀ s < n, ∀ x ∈ Δ,
      HasDerivAt (A (s + 1)) (-iteratedDeriv 2 (A s) x / 2 + ψ x * A s x / 2) x)
    (hα : α ∈ Δ) (hψi : IntegrableOn ψ (Iic α ∩ Δ))
    (hAi : IntegrableOn (deriv (A n)) (Iic α ∩ Δ)) :
    ∃ W : ℝ → ℝ → ℂ, (∀ u > 0, ContDiffOn ℝ 2 (W u) Δ ∧
        ∀ x ∈ Δ, iteratedDeriv 2 (W u) x = ((u : ℂ) ^ 2 + ψ x) * W u x) ∧
      (fun p : ℝ × ℝ ↦ (Real.exp (p.2 * p.1) : ℂ) * W p.2 p.1 -
        ∑ s ∈ range n, (-1) ^ s * A s p.1 / (p.2 : ℂ) ^ s) =O[𝓟 (Iic α ∩ Δ) ×ˢ atTop]
          (fun p ↦ (p.2 ^ n)⁻¹) ∧
      (fun p : ℝ × ℝ ↦ (Real.exp (p.2 * p.1) : ℂ) * deriv (W p.2) p.1 -
        ∑ s ∈ range n, (-1) ^ s * (-(p.2 * A s p.1) + deriv (A s) p.1) / (p.2 : ℂ) ^ s)
          =O[𝓟 (Iic α ∩ Δ) ×ˢ atTop] (fun p ↦ p.2 / p.2 ^ n) := by
  choose! W ε hWc hεd h using fun u (hu : 0 < u) ↦
    exists_caseI_solution_left_norm_le hΔ hΔc hψ hA0 hA hrec hα hu
  have hsub (x : ℝ) (hx : x ∈ Iic α ∩ Δ) : Ioc x α ⊆ Iic α ∩ Δ := fun v hv ↦
    ⟨hv.2, hΔc.out hx.2 hα ⟨le_of_lt hv.1, hv.2⟩⟩
  have hB (s : ℕ) (hs : s < n) (x : ℝ) (hx : x ∈ Δ) :
      DifferentiableAt ℝ (fun y ↦ (-1 : ℂ) ^ s * A s y) x :=
    (((hA s hs).differentiableOn (by norm_num)).differentiableAt (hΔ.mem_nhds hx)).const_mul _
  obtain ⟨h1, h2⟩ := caseI_isBigO (U := Iic α ∩ Δ) (σ := -1) (W := W) (ε := ε)
    (C := 2 * Real.exp (∫ v in Iic α ∩ Δ, ‖ψ v‖) * ∫ v in Iic α ∩ Δ, ‖deriv (A n) v‖)
    hΔ inter_subset_right (by simp) hB
    (fun u hu x hx ↦ by
      simpa [mul_div_assoc] using (h u (one_pos.trans_le hu) x hx).2.1)
    (fun u hu ↦ hεd u (one_pos.trans_le hu)) fun u hu x hx ↦
      caseI_bounds_le hψi hAi hx.1 (hsub x hx) hu
        ((h u (one_pos.trans_le hu) x hx.2).2.2 hx.1).1
        ((h u (one_pos.trans_le hu) x hx.2).2.2 hx.1).2
  refine ⟨W, fun u hu ↦ ⟨hWc u hu, fun x hx ↦ (h u hu x hx).1⟩, ?_, ?_⟩
  · simpa [mul_div_assoc] using h1
  · refine (h2.congr_left fun p ↦ ?_)
    simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, neg_neg,
      deriv_const_mul_field]
    congr 1
    refine sum_congr rfl fun s _ ↦ ?_
    ring

end CaseI

end TauCeti
