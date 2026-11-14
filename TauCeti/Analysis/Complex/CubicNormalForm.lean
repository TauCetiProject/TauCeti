/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Compact
import TauCeti.Analysis.Analytic.Inverse
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.ImplicitFunction
import TauCeti.Analysis.Complex.LocalNormalForm
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Complex.Weierstrass

/-!
# The holomorphic Chester-Friedman-Ursell cubic normal form

Let `p(α, t)` be a holomorphic function of two complex variables near `(α₀, t₀)` at which two
critical points in `t` coalesce: `∂p/∂t = ∂²p/∂t² = 0` and `∂³p/∂t³ ≠ 0` at `(α₀, t₀)`. The
theorem of Chester, Friedman and Ursell (proved holomorphically in several variables by Levinson)
provides a parameter-dependent biholomorphic change of the integration variable `t ↦ w(α, t)` near
`(α₀, t₀)` together with holomorphic coefficient functions `ζ(α)` and `η(α)` near `α₀` such that
`ζ(α₀) = 0`, `η(α₀) = p(α₀, t₀)`, `w(α₀, t₀) = 0`, `∂w/∂t (α₀, t₀) ≠ 0`, and locally
`p(α, t) = w(α, t) ^ 3 / 3 - ζ(α) * w(α, t) + η(α)`.

This reduction is the geometric heart of uniform Airy asymptotic approximations for contour
integrals with two coalescing saddle points: under `u = w(α, t)` with local inverse `t = T(α, u)`,
an oscillatory integral `∫ exp(-z p(α, t)) q(α, t) dt` becomes
`exp(-z η(α)) ∫ exp(-z (u ^ 3 / 3 - ζ(α) u)) f(α, u) du` with holomorphic transformed amplitude
`f(α, u) = q(α, T(α, u)) ∂T/∂u (α, u)`, and the critical points `∂p/∂t = 0` near `(α₀, t₀)` map
bijectively to the two square roots `w ^ 2 = ζ(α)`.

The existence of the cubic normal form requires only `∂p/∂t = ∂²p/∂t² = 0` and `∂³p/∂t³ ≠ 0`. The
mixed-derivative condition `∂²p/∂α∂t (α₀, t₀) ≠ 0` is instead equivalent to `ζ'(α₀) ≠ 0`
(`TauCeti.deriv_zeta_ne_zero_iff`), which governs whether `ζ` is a local coordinate in `α` so that
the critical points coalesce at the generic square-root rate `√(α - α₀)`.

## Main results

* `TauCeti.exists_deriv_eq_add_sq_mul`: local inflection curve `τ(α)` with `∂²p/∂t² (α, τ(α)) = 0`
  and quadratic remainder `∂p/∂t (α, τ(α) + s) = c(α) + s ^ 2 * U(α, s)`.
* `AnalyticAt.exists_cubic_normal_form`, `TauCeti.exists_cubic_normal_form`: the holomorphic
  Chester-Friedman-Ursell cubic normal form `p(α, t) = w(α, t) ^ 3 / 3 - ζ(α) * w(α, t) + η(α)`.
* `TauCeti.cubic_add_div_three_sub_mul_add`, `TauCeti.exists_translated_cubic_normal_form`:
  equivalence with the translated cubic normal form `u ^ 3 / 3 + a(α) u ^ 2 + b(α) u + c(α)`.
* `TauCeti.deriv_eq_sq_sub_mul_deriv`, `TauCeti.deriv_eq_zero_iff_sq_eq`,
  `TauCeti.eventually_deriv_eq_zero_iff_sq_eq`: derivative factorization
  `∂p/∂t = (w ^ 2 - ζ) ∂w/∂t` and critical-point correspondence
  `∂p/∂t (α, t) = 0 ↔ w(α, t) ^ 2 = ζ(α)`.
* `TauCeti.deriv_deriv_deriv_eq_two_mul_pow_three`, `TauCeti.deriv_deriv_eq_neg_deriv_mul_deriv`,
  `TauCeti.deriv_zeta_ne_zero_iff`: jet identities `∂³p/∂t³ = 2 (∂w/∂t) ^ 3` and
  `∂²p/∂α∂t = -ζ'(α₀) ∂w/∂t`, characterizing nondegenerate square-root coalescence `ζ'(α₀) ≠ 0`.
* `TauCeti.exists_analyticAt_mul_deriv_eq`: analytic local inverse `T(α, u)` and transformed
  amplitude `f(α, u) = q(α, T(α, u)) ∂T/∂u (α, u)` satisfying
  `f(α, w(α, t)) ∂w/∂t (α, t) = q(α, t)`.
* `TauCeti.deriv_cubic_sub_mul_eq_zero_iff`, `TauCeti.deriv_deriv_cubic_sub_mul`,
  `TauCeti.deriv_deriv_cubic_add_sq_mul`, `TauCeti.deriv_cubic_add_sq_mul_eq_zero_iff`: canonical
  `t ^ 3 / 3 - α t` and degenerate `t ^ 3 / 3 + α ^ 2 t` coalescing critical-point models.

## References

* C. Chester, B. Friedman, F. Ursell, *An extension of the method of steepest descents*, Proc.
  Cambridge Philos. Soc. **53** (1957), 599-611.
* N. Levinson, *Transformation of an analytic function of several variables to a canonical form*,
  Duke Math. J. **28** (1961), 345-353.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press (1974), Chapter 9, §12.
* NIST Digital Library of Mathematical Functions, §2.4(v), equations (2.4.17)-(2.4.20),
  <https://dlmf.nist.gov/2.4.v>.
-/

public section

open Complex Filter Metric Set Topology

namespace TauCeti

/-! ### Partial derivatives and local inflection decomposition -/

/-- If `g : ℂ × ℂ → ℂ` is analytic at `q₀`, its partial derivative in the second variable is
analytic at `q₀`. -/
private theorem analyticAt_deriv_snd {g : ℂ × ℂ → ℂ} {q₀ : ℂ × ℂ} (hg : AnalyticAt ℂ g q₀) :
    AnalyticAt ℂ (fun q => deriv (fun t => g (q.1, t)) q.2) q₀ := by
  have hclm : AnalyticAt ℂ (fun q => fderiv ℂ g q (0, 1)) q₀ :=
    ((ContinuousLinearMap.apply ℂ ℂ ((0 : ℂ), (1 : ℂ))).analyticAt _).comp hg.fderiv
  refine hclm.congr ?_
  filter_upwards [hg.eventually_analyticAt] with q hq
  have hd := (hq.differentiableAt.hasFDerivAt.comp q.2
    (hasFDerivAt_prodMk_right q.1 q.2)).hasDerivAt.deriv
  simpa [Function.comp_def] using hd.symm

/-- If `g : ℂ × ℂ → ℂ` is analytic at `q₀`, its partial derivative in the first variable is
analytic at `q₀`. -/
private theorem analyticAt_deriv_fst {g : ℂ × ℂ → ℂ} {q₀ : ℂ × ℂ} (hg : AnalyticAt ℂ g q₀) :
    AnalyticAt ℂ (fun q => deriv (fun α => g (α, q.2)) q.1) q₀ := by
  have hclm : AnalyticAt ℂ (fun q => fderiv ℂ g q (1, 0)) q₀ :=
    ((ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : ℂ))).analyticAt _).comp hg.fderiv
  refine hclm.congr ?_
  filter_upwards [hg.eventually_analyticAt] with q hq
  have hd := (hq.differentiableAt.hasFDerivAt.comp q.1
    (hasFDerivAt_prodMk_left q.1 q.2)).hasDerivAt.deriv
  simpa [Function.comp_def] using hd.symm

/-- Second derivative at `0` of `s ↦ a + s ^ 2 * h s`. -/
private theorem deriv_deriv_add_sq_mul_zero {f h : ℂ → ℂ} {a : ℂ} (hh : AnalyticAt ℂ h 0)
    (hf : f =ᶠ[𝓝 0] fun s => a + s ^ 2 * h s) :
    deriv (deriv f) 0 = 2 * h 0 := by
  have hd₁ : deriv f =ᶠ[𝓝 0] fun s => 2 * s * h s + s ^ 2 * deriv h s := by
    filter_upwards [hf.eventually_nhds, hh.eventually_analyticAt] with s hs hhs
    rw [Filter.EventuallyEq.deriv_eq hs]
    have hd := (((hasDerivAt_pow 2 s).mul hhs.differentiableAt.hasDerivAt).const_add a).deriv
    simp only [Pi.mul_def, Nat.cast_ofNat] at hd
    rw [hd]
    ring
  rw [Filter.EventuallyEq.deriv_eq hd₁]
  have hd₂ := ((((hasDerivAt_id (0 : ℂ)).const_mul 2).mul hh.differentiableAt.hasDerivAt).add
    ((hasDerivAt_pow 2 (0 : ℂ)).mul hh.deriv.differentiableAt.hasDerivAt)).deriv
  simp only [Pi.add_def, Pi.mul_def, id, Nat.cast_ofNat] at hd₂
  rw [hd₂]
  ring

/-- Quadratic Taylor remainder in the second variable along `s = 0` when the first partial
derivative in `s` vanishes there. -/
private theorem exists_quadratic_remainder_of_deriv_eq_zero {g : ℂ × ℂ → ℂ} {α₀ : ℂ}
    (hg : AnalyticAt ℂ g (α₀, 0))
    (hderiv0 : ∀ᶠ α in 𝓝 α₀, deriv (fun s => g (α, s)) 0 = 0) :
    ∃ U : ℂ × ℂ → ℂ, AnalyticAt ℂ U (α₀, 0) ∧
      U (α₀, 0) = deriv (deriv fun s => g (α₀, s)) 0 / 2 ∧
      ∀ᶠ q in 𝓝 (α₀, 0), g q = g (q.1, 0) + q.2 ^ 2 * U q := by
  obtain ⟨U, r, hU, -, hdiv⟩ := hg.exists_weierstrassDivision_monicOfCoeff
    (d := 2) (c := 0) (fun _ => analyticAt_const) (fun _ => rfl)
  have hdiv' : ∀ᶠ q in 𝓝 (α₀, 0), g q = r 0 q.1 + r 1 q.1 * q.2 + q.2 ^ 2 * U q := by
    filter_upwards [hdiv] with q hq
    rw [hq, TauCeti.Polynomial.eval_monicOfCoeff]
    simp [Fin.sum_univ_two]
    ring
  have hdiv_prod : ∀ᶠ q in 𝓝 α₀ ×ˢ 𝓝 (0 : ℂ),
      g q = r 0 q.1 + r 1 q.1 * q.2 + q.2 ^ 2 * U q := by rwa [← nhds_prod_eq]
  have hr₀ : ∀ᶠ α in 𝓝 α₀, r 0 α = g (α, 0) := by
    filter_upwards [hdiv_prod.curry] with α hα
    have h0 := hα.self_of_nhds
    linear_combination -h0
  have hU_prod : ∀ᶠ q in 𝓝 α₀ ×ˢ 𝓝 (0 : ℂ), AnalyticAt ℂ U q := by
    rw [← nhds_prod_eq]
    exact hU.eventually_analyticAt
  have hr₁ : ∀ᶠ α in 𝓝 α₀, r 1 α = 0 := by
    filter_upwards [hdiv_prod.curry, hderiv0, hU_prod.curry] with α hα hdα hUα
    have hU0 : DifferentiableAt ℂ (fun s => U (α, s)) 0 :=
      (hUα.self_of_nhds.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl).differentiableAt
    have hd_rhs : deriv (fun s => r 0 α + r 1 α * s + s ^ 2 * U (α, s)) 0 = r 1 α := by
      have hd := ((((hasDerivAt_id (0 : ℂ)).const_mul (r 1 α)).const_add (r 0 α)).add
        ((hasDerivAt_pow 2 (0 : ℂ)).mul hU0.hasDerivAt)).deriv
      simp only [Pi.add_def, Pi.mul_def, id] at hd
      rw [hd]
      simp
    exact ((Filter.EventuallyEq.deriv_eq hα).trans hd_rhs).symm.trans hdα
  have hmain : ∀ᶠ q in 𝓝 (α₀, 0), g q = g (q.1, 0) + q.2 ^ 2 * U q := by
    filter_upwards [hdiv', continuous_fst.continuousAt.eventually (hr₀.and hr₁)]
      with q hq ⟨h0, h1⟩
    rw [hq, h0, h1]
    ring
  have hUs : AnalyticAt ℂ (fun s => U (α₀, s)) 0 :=
    hU.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hmain_s : (fun s => g (α₀, s)) =ᶠ[𝓝 0] fun s => g (α₀, 0) + s ^ 2 * U (α₀, s) :=
    ((continuous_const.prodMk continuous_id).tendsto (0 : ℂ)).eventually hmain
  have hdd := deriv_deriv_add_sq_mul_zero hUs hmain_s
  exact ⟨U, hU, by rw [hdd, mul_div_cancel_left₀ _ two_ne_zero], hmain⟩

/-- Derivative along `(α, τ α)` when the vertical partial derivative vanishes at `(α₀, t₀)`. -/
private theorem deriv_comp_curve_of_deriv_snd_eq_zero {p₁ : ℂ × ℂ → ℂ} {τ : ℂ → ℂ} {α₀ t₀ : ℂ}
    (hp₁ : DifferentiableAt ℂ p₁ (α₀, t₀)) (hτ : DifferentiableAt ℂ τ α₀) (hτ0 : τ α₀ = t₀)
    (h₂ : deriv (fun t => p₁ (α₀, t)) t₀ = 0) :
    deriv (fun α => p₁ (α, τ α)) α₀ = deriv (fun α => p₁ (α, t₀)) α₀ := by
  have hp₁d : HasFDerivAt p₁ (fderiv ℂ p₁ (α₀, t₀)) (α₀, τ α₀) := hτ0 ▸ hp₁.hasFDerivAt
  have hdc :=
    (hp₁d.comp α₀ ((hasFDerivAt_id α₀).prodMk hτ.hasDerivAt.hasFDerivAt)).hasDerivAt.deriv
  dsimp only [Function.comp_def, id] at hdc
  have hsplit : ((1 : ℂ), deriv τ α₀) = (1, 0) + deriv τ α₀ • ((0 : ℂ), (1 : ℂ)) := by simp
  have h01 : fderiv ℂ p₁ (α₀, t₀) (0, 1) = 0 := by
    have hd := (hp₁.hasFDerivAt.comp t₀ (hasFDerivAt_prodMk_right α₀ t₀)).hasDerivAt.deriv
    simpa [Function.comp_def, h₂] using hd.symm
  have h10 : fderiv ℂ p₁ (α₀, t₀) (1, 0) = deriv (fun α => p₁ (α, t₀)) α₀ := by
    have hd := (hp₁.hasFDerivAt.comp α₀ (hasFDerivAt_prodMk_left α₀ t₀)).hasDerivAt.deriv
    simpa [Function.comp_def] using hd.symm
  rw [hdc]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  rw [hsplit, map_add, map_smul, h01, h10]
  simp

/-- **Local inflection curve and quadratic remainder of `∂p/∂t`.** Let `p(α, t)` be holomorphic on
a neighbourhood `V` of `(α₀, t₀)` with `∂²p/∂t² (α₀, t₀) = 0` and `∂³p/∂t³ (α₀, t₀) ≠ 0`. Then
there exist analytic functions `τ` and `c` at `α₀` and `U` at `(α₀, 0)` such that `τ(α₀) = t₀`,
`∂²p/∂t² (α, τ(α)) = 0` near `α₀`, and `∂p/∂t (α, τ(α) + s) = c(α) + s ^ 2 * U(α, s)` near
`(α₀, 0)`, with `c(α₀) = ∂p/∂t (α₀, t₀)`, `c'(α₀) = ∂²p/∂α∂t (α₀, t₀)`, and
`U(α₀, 0) = ½ ∂³p/∂t³ (α₀, t₀)`. -/
theorem exists_deriv_eq_add_sq_mul {p : ℂ × ℂ → ℂ} {V : Set (ℂ × ℂ)} {α₀ t₀ : ℂ}
    (hV : V ∈ 𝓝 (α₀, t₀)) (hp : DifferentiableOn ℂ p V)
    (h₂ : deriv (deriv fun t => p (α₀, t)) t₀ = 0)
    (h₃ : deriv (deriv (deriv fun t => p (α₀, t))) t₀ ≠ 0) :
    ∃ τ c : ℂ → ℂ, ∃ U : ℂ × ℂ → ℂ,
      AnalyticAt ℂ τ α₀ ∧ AnalyticAt ℂ c α₀ ∧ AnalyticAt ℂ U (α₀, 0) ∧
      τ α₀ = t₀ ∧ c α₀ = deriv (fun t => p (α₀, t)) t₀ ∧
      deriv c α₀ = deriv (fun α => deriv (fun t => p (α, t)) t₀) α₀ ∧
      U (α₀, 0) = deriv (deriv (deriv fun t => p (α₀, t))) t₀ / 2 ∧
      (∀ᶠ α in 𝓝 α₀, deriv (deriv fun t => p (α, t)) (τ α) = 0) ∧
      ∀ᶠ q in 𝓝 (α₀, 0),
        deriv (fun t => p (q.1, t)) (τ q.1 + q.2) = c q.1 + q.2 ^ 2 * U q := by
  have hpa : AnalyticAt ℂ p (α₀, t₀) := hp.analyticAt_of_finiteDimensional hV
  set p₁ : ℂ × ℂ → ℂ := fun q => deriv (fun t => p (q.1, t)) q.2
  set p₂ : ℂ × ℂ → ℂ := fun q => deriv (deriv fun t => p (q.1, t)) q.2
  have hp₁ : AnalyticAt ℂ p₁ (α₀, t₀) := analyticAt_deriv_snd hpa
  have hp₂ : AnalyticAt ℂ p₂ (α₀, t₀) := analyticAt_deriv_snd hp₁
  obtain ⟨τ, hτ, hτ0, hτeq, -⟩ := hp₂.exists_analyticAt_eventually_eq_zero_iff h₂ h₃
  dsimp only at hτ hτ0 hτeq
  set c : ℂ → ℂ := fun α => p₁ (α, τ α)
  have hc : AnalyticAt ℂ c α₀ := hp₁.comp_of_eq (analyticAt_id.prod hτ) (by simp [hτ0])
  have hc_deriv :=
    deriv_comp_curve_of_deriv_snd_eq_zero hp₁.differentiableAt hτ.differentiableAt hτ0 h₂
  set g : ℂ × ℂ → ℂ := fun q => p₁ (q.1, τ q.1 + q.2)
  have hg : AnalyticAt ℂ g (α₀, 0) :=
    hp₁.comp_of_eq (analyticAt_fst.prod
      ((hτ.comp_of_eq analyticAt_fst rfl).add analyticAt_snd)) (by simp [hτ0])
  have hg_deriv0 : ∀ᶠ α in 𝓝 α₀, deriv (fun s => g (α, s)) 0 = 0 := by
    have hline : Tendsto (fun α => (α, τ α)) (𝓝 α₀) (𝓝 (α₀, t₀)) :=
      hτ0 ▸ continuousAt_id.prodMk hτ.continuousAt
    filter_upwards [hτeq, hline.eventually hp₁.eventually_analyticAt] with α hα hp₁α
    have hp₁s : DifferentiableAt ℂ (fun t => p₁ (α, t)) (τ α + 0) := by
      rw [add_zero]
      exact (hp₁α.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl).differentiableAt
    have hd := (hp₁s.hasDerivAt.comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_add (τ α))).deriv
    dsimp only [Function.comp_def, id, g, p₁] at hd
    rw [add_zero, mul_one] at hd
    exact hd.trans hα
  obtain ⟨U, hU, hU0, hgeq⟩ := exists_quadratic_remainder_of_deriv_eq_zero hg hg_deriv0
  have hU0' : U (α₀, 0) = deriv (deriv (deriv fun t => p (α₀, t))) t₀ / 2 := by
    have hgs : (fun s => g (α₀, s)) = fun s => p₁ (α₀, t₀ + s) := by ext s; simp [g, hτ0]
    have hd1 : deriv (fun u => p₁ (α₀, t₀ + u)) = fun s => p₂ (α₀, t₀ + s) := by
      ext s; simpa [p₂] using deriv_comp_const_add (fun t => p₁ (α₀, t)) t₀ s
    have hd2 : deriv (fun s => p₂ (α₀, t₀ + s)) 0 = deriv (fun t => p₂ (α₀, t)) t₀ := by
      simpa using deriv_comp_const_add (fun t => p₂ (α₀, t)) t₀ 0
    rw [hU0, hgs, hd1, hd2]
  refine ⟨τ, c, U, hτ, hc, hU, hτ0, by simp [c, p₁, hτ0], hc_deriv, hU0', hτeq, ?_⟩
  filter_upwards [hgeq] with q hq
  simpa [g, c, p₁] using hq

/-! ### Disc-algebra inverse function construction -/

section DiscAlgebra

/-- Zero-extension of a continuous function on `closedBall (0 : ℂ) R` to all of `ℂ`. -/
private noncomputable def extZero (R : ℝ) (u : C(closedBall (0 : ℂ) R, ℂ)) (z : ℂ) : ℂ :=
  open Classical in
  if hz : z ∈ closedBall (0 : ℂ) R then u ⟨z, hz⟩ else 0

private theorem extZero_of_mem {R : ℝ} (u : C(closedBall (0 : ℂ) R, ℂ)) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) R) : extZero R u z = u ⟨z, hz⟩ := by
  dsimp only [extZero]
  exact dite_eq_left hz

private theorem continuousOn_extZero (R : ℝ) (u : C(closedBall (0 : ℂ) R, ℂ)) :
    ContinuousOn (extZero R u) (closedBall (0 : ℂ) R) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact u.continuous.congr fun z => (extZero_of_mem u z.2).symm

/-- The Banach subalgebra of `C(closedBall 0 R, ℂ)` consisting of functions holomorphic on
`ball 0 R`. -/
private noncomputable def discAlgebra (R : ℝ) : Subalgebra ℂ C(closedBall (0 : ℂ) R, ℂ) where
  carrier := {u | DifferentiableOn ℂ (extZero R u) (ball (0 : ℂ) R)}
  mul_mem' {u v} hu hv := (hu.mul hv).congr fun _ hz => by
    simp [extZero_of_mem _ (ball_subset_closedBall hz)]
  one_mem' := (differentiableOn_const 1).congr fun _ hz => by
    simp [extZero_of_mem _ (ball_subset_closedBall hz)]
  add_mem' {u v} hu hv := (hu.add hv).congr fun _ hz => by
    simp [extZero_of_mem _ (ball_subset_closedBall hz)]
  zero_mem' := (differentiableOn_const 0).congr fun _ hz => by
    simp [extZero_of_mem _ (ball_subset_closedBall hz)]
  algebraMap_mem' c := (differentiableOn_const c).congr fun _ hz => by
    simp [extZero_of_mem _ (ball_subset_closedBall hz)]

private theorem isClosed_discAlgebra (R : ℝ) :
    IsClosed (discAlgebra R : Set C(closedBall (0 : ℂ) R, ℂ)) := by
  refine IsSeqClosed.isClosed fun u u₀ hu hut => ?_
  have hunif : TendstoUniformlyOn (fun n => extZero R (u n)) (extZero R u₀) atTop
      (ball (0 : ℂ) R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.1 hut ε hε] with n hn z hz
    have hzc : z ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hz
    rw [extZero_of_mem _ hzc, extZero_of_mem _ hzc]
    exact (ContinuousMap.dist_apply_le_dist (f := u₀) (g := u n) ⟨z, hzc⟩).trans_lt
      (by rwa [dist_comm])
  exact hunif.differentiableOn (Eventually.of_forall hu) isOpen_ball

private instance completeSpace_discAlgebra (R : ℝ) : CompleteSpace (discAlgebra R) :=
  (isClosed_discAlgebra R).completeSpace_coe

/-- The coordinate element `z ↦ z` of `discAlgebra R`. -/
private noncomputable def idDisc (R : ℝ) : discAlgebra R :=
  ⟨⟨Subtype.val, continuous_subtype_val⟩,
    differentiableOn_id.congr fun _ hz => extZero_of_mem _ (ball_subset_closedBall hz)⟩

/-- Iterated `dslope` at `0` dividing off `u(0) + u'(0) z` by `z ^ 2`. -/
private noncomputable def dslope₂ (R : ℝ) (u : discAlgebra R) : ℂ → ℂ :=
  dslope (dslope (extZero R u.1) 0) 0

private theorem differentiableOn_dslope₂ {R : ℝ} (hR : 0 < R) (u : discAlgebra R) :
    DifferentiableOn ℂ (dslope₂ R u) (ball (0 : ℂ) R) :=
  (Complex.differentiableOn_dslope (ball_mem_nhds 0 hR)).2
    ((Complex.differentiableOn_dslope (ball_mem_nhds 0 hR)).2 u.2)

private theorem sq_mul_dslope₂ (R : ℝ) (u : discAlgebra R) (z : ℂ) :
    z ^ 2 * dslope₂ R u z - (-deriv (extZero R u.1) 0) * z + extZero R u.1 0 =
      extZero R u.1 z := by
  have h1 := sub_smul_dslope (dslope (extZero R u.1) 0) 0 z
  have h2 := sub_smul_dslope (extZero R u.1) 0 z
  simp only [sub_zero, smul_eq_mul, dslope_same] at h1 h2
  dsimp [dslope₂]
  linear_combination z * h1 + h2

private theorem continuousOn_dslope₂ {R : ℝ} (hR : 0 < R) (u : discAlgebra R) :
    ContinuousOn (dslope₂ R u) (closedBall (0 : ℂ) R) := by
  have hd₁ : DifferentiableOn ℂ (dslope (extZero R u.1) 0) (ball (0 : ℂ) R) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds 0 hR)).2 u.2
  have hc₁ : ContinuousOn (dslope (extZero R u.1) 0) (closedBall (0 : ℂ) R) :=
    (continuousOn_dslope (closedBall_mem_nhds 0 hR)).2
      ⟨continuousOn_extZero R u.1, u.2.differentiableAt (ball_mem_nhds 0 hR)⟩
  exact (continuousOn_dslope (closedBall_mem_nhds 0 hR)).2
    ⟨hc₁, hd₁.differentiableAt (ball_mem_nhds 0 hR)⟩

private noncomputable def dslope₂Disc {R : ℝ} (hR : 0 < R) (u : discAlgebra R) : discAlgebra R :=
  ⟨⟨fun z => dslope₂ R u z.1, (continuousOn_dslope₂ hR u).comp_continuous continuous_subtype_val
    fun z => z.2⟩,
    (differentiableOn_dslope₂ hR u).congr fun _ hz => extZero_of_mem _ (ball_subset_closedBall hz)⟩

/-- Linearization `(δu, (δζ, δη)) ↦ z ^ 2 * δu - δζ * z + δη` of the cubic normal-form operator at
`(idDisc R, (0, 0))`. -/
private noncomputable def cubicLinearCLM (R : ℝ) :
    (discAlgebra R × (ℂ × ℂ)) →L[ℂ] discAlgebra R :=
  (ContinuousLinearMap.mul ℂ (discAlgebra R) (idDisc R ^ 2)).comp (.fst ℂ _ _) -
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight (idDisc R)).comp (.snd ℂ _ _) +
    (algebraMapCLM ℂ (discAlgebra R)).comp ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (.snd ℂ _ _))

private theorem cubicLinearCLM_apply_coe (R : ℝ) (x : discAlgebra R × (ℂ × ℂ))
    (z : closedBall (0 : ℂ) R) :
    (cubicLinearCLM R x).1 z = z.1 ^ 2 * x.1.1 z - x.2.1 * z.1 + x.2.2 := by
  simp [cubicLinearCLM, idDisc]

private theorem tendsto_div_nat_add_two (R : ℝ) :
    Tendsto (fun n : ℕ => ((R / (n + 2 : ℝ) : ℝ) : ℂ)) atTop (𝓝 0) := by
  simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := R)).div_atTop
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (2 : ℝ)))))

private theorem ker_cubicLinearCLM {R : ℝ} (hR : 0 < R) :
    LinearMap.ker (cubicLinearCLM R : (discAlgebra R × (ℂ × ℂ)) →ₗ[ℂ] discAlgebra R) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  rintro ⟨δu, δζ, δη⟩ hx
  have hval (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R) :
      z ^ 2 * δu.1 ⟨z, hz⟩ - δζ * z + δη = 0 := by
    simpa [cubicLinearCLM_apply_coe] using congrArg (fun f : discAlgebra R => f.1 ⟨z, hz⟩) hx
  have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) R := mem_closedBall_self hR.le
  have hη : δη = 0 := by simpa using hval 0 h0mem
  subst hη
  have hseq (n : ℕ) : ((R / (n + 2 : ℝ) : ℝ) : ℂ) ∈ closedBall (0 : ℂ) R ∧
      ((R / (n + 2 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    have hpos : 0 < R / (n + 2 : ℝ) := by positivity
    refine ⟨?_, Complex.ofReal_ne_zero.2 hpos.ne'⟩
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    exact div_le_self hR.le (by linarith)
  have htend := tendsto_div_nat_add_two R
  have htend_sub : Tendsto (fun n : ℕ => (⟨_, (hseq n).1⟩ : closedBall (0 : ℂ) R))
      atTop (𝓝 ⟨0, h0mem⟩) := tendsto_subtype_rng.2 htend
  have hζ : δζ = 0 := by
    have hlim : Tendsto (fun n : ℕ =>
        ((R / (n + 2 : ℝ) : ℝ) : ℂ) * δu.1 ⟨_, (hseq n).1⟩) atTop (𝓝 0) := by
      simpa using htend.mul ((δu.1.continuous.tendsto ⟨0, h0mem⟩).comp htend_sub)
    have hconst (n : ℕ) : ((R / (n + 2 : ℝ) : ℝ) : ℂ) * δu.1 ⟨_, (hseq n).1⟩ = δζ :=
      mul_right_cancel₀ (hseq n).2 (by linear_combination hval _ (hseq n).1)
    exact tendsto_nhds_unique (tendsto_const_nhds.congr fun n => (hconst n).symm) hlim
  subst hζ
  have hδu : δu = 0 := by
    ext ⟨z, hz⟩
    by_cases hz0 : z = 0
    · subst hz0
      have hzero_n (n : ℕ) : δu.1 ⟨_, (hseq n).1⟩ = 0 :=
        (mul_eq_zero.1 (by simpa using hval _ (hseq n).1)).resolve_left (pow_ne_zero 2 (hseq n).2)
      exact tendsto_nhds_unique ((δu.1.continuous.tendsto ⟨0, h0mem⟩).comp htend_sub)
        (tendsto_const_nhds.congr fun n => (hzero_n n).symm)
    · exact (mul_eq_zero.1 (by simpa using hval z hz)).resolve_left (pow_ne_zero 2 hz0)
  simp [hδu]

private noncomputable def cubicLinearEquiv {R : ℝ} (hR : 0 < R) :
    (discAlgebra R × (ℂ × ℂ)) ≃L[ℂ] discAlgebra R :=
  ContinuousLinearEquiv.ofBijective (cubicLinearCLM R) (ker_cubicLinearCLM hR) <| by
    rw [LinearMap.range_eq_top]
    intro u
    refine ⟨(dslope₂Disc hR u, (-deriv (extZero R u.1) 0, extZero R u.1 0)), ?_⟩
    ext z
    simpa [cubicLinearCLM_apply_coe, dslope₂Disc, extZero_of_mem u.1 z.2] using
      sq_mul_dslope₂ R u z.1

/-- The nonlinear cubic normal-form operator `(u, (ζ, η)) ↦ u ^ 3 / 3 - ζ u + η` on
`discAlgebra R`. -/
private noncomputable def cubicMap (R : ℝ) (x : discAlgebra R × (ℂ × ℂ)) : discAlgebra R :=
  (3⁻¹ : ℂ) • x.1 ^ 3 - x.2.1 • x.1 + algebraMapCLM ℂ (discAlgebra R) x.2.2

private theorem cubicMap_apply_coe (R : ℝ) (x : discAlgebra R × (ℂ × ℂ))
    (z : closedBall (0 : ℂ) R) :
    (cubicMap R x).1 z = (x.1.1 z) ^ 3 / 3 - x.2.1 * x.1.1 z + x.2.2 := by
  simp [cubicMap, div_eq_inv_mul]

private theorem analyticAt_cubicMap (R : ℝ) (x : discAlgebra R × (ℂ × ℂ)) :
    AnalyticAt ℂ (cubicMap R) x := by
  have hu : AnalyticAt ℂ (fun y : discAlgebra R × (ℂ × ℂ) => y.1) x :=
    (ContinuousLinearMap.fst ℂ (discAlgebra R) (ℂ × ℂ)).analyticAt x
  have hζ : AnalyticAt ℂ (fun y : discAlgebra R × (ℂ × ℂ) => y.2.1) x :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (.snd ℂ (discAlgebra R) (ℂ × ℂ))).analyticAt x
  have hη : AnalyticAt ℂ (fun y : discAlgebra R × (ℂ × ℂ) =>
      algebraMapCLM ℂ (discAlgebra R) y.2.2) x :=
    ((algebraMapCLM ℂ (discAlgebra R)).comp
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (.snd ℂ (discAlgebra R) (ℂ × ℂ)))).analyticAt x
  refine ((((hu.mul (hu.mul hu)).const_smul (c := (3⁻¹ : ℂ))).sub (hζ.smul hu)).add hη).congr ?_
  exact .of_forall fun y => by simp [cubicMap, pow_three]

private theorem hasFDerivAt_cubicMap (R : ℝ) :
    HasFDerivAt (cubicMap R) (cubicLinearCLM R) (idDisc R, (0, 0)) := by
  set x₀ : discAlgebra R × (ℂ × ℂ) := (idDisc R, (0, 0))
  have hu : HasFDerivAt (fun x : discAlgebra R × (ℂ × ℂ) => x.1)
      (.fst ℂ (discAlgebra R) (ℂ × ℂ)) x₀ :=
    (ContinuousLinearMap.fst ℂ (discAlgebra R) (ℂ × ℂ)).hasFDerivAt
  have hu3 := (hu.mul (hu.mul hu)).const_smul (3⁻¹ : ℂ)
  have hζ : HasFDerivAt (fun x : discAlgebra R × (ℂ × ℂ) => x.2.1)
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (.snd ℂ (discAlgebra R) (ℂ × ℂ))) x₀ :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (.snd ℂ (discAlgebra R) (ℂ × ℂ))).hasFDerivAt
  have hη : HasFDerivAt (fun x : discAlgebra R × (ℂ × ℂ) =>
      algebraMapCLM ℂ (discAlgebra R) x.2.2)
      ((algebraMapCLM ℂ (discAlgebra R)).comp
        ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (.snd ℂ (discAlgebra R) (ℂ × ℂ)))) x₀ :=
    ((algebraMapCLM ℂ (discAlgebra R)).comp
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (.snd ℂ (discAlgebra R) (ℂ × ℂ)))).hasFDerivAt
  have hcomb := (hu3.sub (hζ.smul hu)).add hη
  refine (hcomb.congr_of_eventuallyEq
    (.of_forall fun x => by simp [cubicMap, pow_three])).congr_fderiv ?_
  apply ContinuousLinearMap.ext
  rintro ⟨δu, δζ, δη⟩
  apply Subtype.ext
  ext z
  simp [cubicLinearCLM_apply_coe, x₀, idDisc]
  ring

/-- A family `F(β, s)` jointly analytic on `ball 0 δ ×ˢ closedBall 0 R` induces a curve
`β ↦ F(β, ·)` in `discAlgebra R`. -/
private noncomputable def sliceDiscMap {F : ℂ × ℂ → ℂ} {δ R : ℝ}
    (hF : ∀ β ∈ ball (0 : ℂ) δ, ∀ s ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ F (β, s))
    (β : ℂ) : discAlgebra R :=
  open Classical in
  if hβ : β ∈ ball (0 : ℂ) δ then
    ⟨⟨fun s => F (β, s.1), continuous_iff_continuousAt.2 fun s =>
      ContinuousAt.comp (g := F) (f := fun z : closedBall (0 : ℂ) R => (β, z.1))
        (hF β hβ s.1 s.2).continuousAt
        (continuous_const.prodMk continuous_subtype_val).continuousAt⟩,
      fun s hs => (((hF β hβ s (ball_subset_closedBall hs)).comp_of_eq
        (analyticAt_const.prod analyticAt_id) rfl).differentiableAt.differentiableWithinAt).congr
        (fun _ hw => extZero_of_mem _ (ball_subset_closedBall hw))
        (extZero_of_mem _ (ball_subset_closedBall hs))⟩
  else 0

private theorem sliceDiscMap_apply_coe {F : ℂ × ℂ → ℂ} {δ R : ℝ}
    (hF : ∀ β ∈ ball (0 : ℂ) δ, ∀ s ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ F (β, s))
    {β : ℂ} (hβ : β ∈ ball (0 : ℂ) δ) (s : closedBall (0 : ℂ) R) :
    (sliceDiscMap hF β).1 s = F (β, s.1) := by
  dsimp only [sliceDiscMap]
  rw [dite_eq_left hβ]
  rfl

private theorem differentiableAt_sliceDiscMap {F : ℂ × ℂ → ℂ} {δ R : ℝ}
    (hF : ∀ β ∈ ball (0 : ℂ) δ, ∀ s ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ F (β, s))
    {β₀ : ℂ} (hβ₀ : β₀ ∈ ball (0 : ℂ) δ) :
    DifferentiableAt ℂ (sliceDiscMap hF) β₀ := by
  set F₁ : ℂ × ℂ → ℂ := fun q => deriv (fun β => F (β, q.2)) q.1
  have hF₁ (β : ℂ) (hβ : β ∈ ball (0 : ℂ) δ) (s : ℂ) (hs : s ∈ closedBall (0 : ℂ) R) :
      AnalyticAt ℂ F₁ (β, s) := analyticAt_deriv_fst (hF β hβ s hs)
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.isOpen_iff.1 isOpen_ball β₀ hβ₀
  set r : ℝ := r₀ / 2
  have hr : 0 < r := half_pos hr₀
  have hrsub : closedBall β₀ r ⊆ ball (0 : ℂ) δ :=
    (closedBall_subset_ball (half_lt_self hr₀)).trans hr₀sub
  have hK : IsCompact (closedBall β₀ r ×ˢ closedBall (0 : ℂ) R) :=
    (isCompact_closedBall β₀ r).prod (isCompact_closedBall 0 R)
  have hF₁c : ContinuousOn F₁ (closedBall β₀ r ×ˢ closedBall (0 : ℂ) R) :=
    fun q hq => (hF₁ q.1 (hrsub hq.1) q.2 hq.2).continuousAt.continuousWithinAt
  have hunif := Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hF₁c)
  set d₀ : discAlgebra R := sliceDiscMap hF₁ β₀
  suffices HasDerivAt (sliceDiscMap hF) d₀ β₀ from this.differentiableAt
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨η, hη, hη_unif⟩ := hunif ε hε
  filter_upwards [ball_mem_nhds β₀ (lt_min hr hη)] with β hβ
  have hβ_cb : β ∈ closedBall β₀ r :=
    ball_subset_closedBall (mem_ball.2 ((mem_ball.1 hβ).trans_le (min_le_left _ _)))
  refine (ContinuousMap.norm_le
    ((sliceDiscMap hF β - sliceDiscMap hF β₀ - (β - β₀) • d₀).1)
    (mul_nonneg hε.le (norm_nonneg (β - β₀)))).2 fun s => ?_
  have heval : ((sliceDiscMap hF β - sliceDiscMap hF β₀ - (β - β₀) • d₀).1 s) =
      F (β, s.1) - F (β₀, s.1) - (β - β₀) * F₁ (β₀, s.1) := by
    simp [d₀, sliceDiscMap_apply_coe hF (hrsub hβ_cb), sliceDiscMap_apply_coe hF hβ₀,
      sliceDiscMap_apply_coe hF₁ hβ₀]
  rw [heval]
  set s₀ : Set ℂ := closedBall β₀ (dist β β₀)
  have hs₀_sub : s₀ ⊆ closedBall β₀ r := closedBall_subset_closedBall (mem_closedBall.1 hβ_cb)
  have hf' (z : ℂ) (hz : z ∈ s₀) :
      HasFDerivWithinAt (fun w => F (w, s.1))
        (ContinuousLinearMap.toSpanSingleton ℂ (F₁ (z, s.1))) s₀ z :=
    (((hF z (hrsub (hs₀_sub hz)) s.1 s.2).comp_of_eq (analyticAt_id.prod analyticAt_const)
      rfl).differentiableAt.hasDerivAt.hasDerivWithinAt).hasFDerivWithinAt
  have hbound (z : ℂ) (hz : z ∈ s₀) :
      ‖ContinuousLinearMap.toSpanSingleton ℂ (F₁ (z, s.1)) -
        ContinuousLinearMap.toSpanSingleton ℂ (F₁ (β₀, s.1))‖ ≤ ε := by
    rw [← dist_eq_norm, ← ContinuousLinearMap.toSpanSingletonLIE_apply,
      ← ContinuousLinearMap.toSpanSingletonLIE_apply,
      (ContinuousLinearMap.toSpanSingletonLIE ℂ ℂ).dist_map]
    have hdist : dist z β₀ < η :=
      (mem_closedBall.1 hz).trans_lt ((mem_ball.1 hβ).trans_le (min_le_right _ _))
    exact (hη_unif (z, s.1) ⟨hs₀_sub hz, s.2⟩ (β₀, s.1) ⟨mem_closedBall_self hr.le, s.2⟩
      (by simp [Prod.dist_eq, hdist])).le
  simpa using (convex_closedBall β₀ (dist β β₀)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    hf' hbound (mem_closedBall_self dist_nonneg) (mem_closedBall.2 le_rfl)

private theorem analyticAt_sliceDiscMap {F : ℂ × ℂ → ℂ} {δ R : ℝ} (hδ : 0 < δ)
    (hF : ∀ β ∈ ball (0 : ℂ) δ, ∀ s ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ F (β, s)) :
    AnalyticAt ℂ (sliceDiscMap hF) 0 :=
  DifferentiableOn.analyticAt
    (fun _ hβ => (differentiableAt_sliceDiscMap hF hβ).differentiableWithinAt)
    (ball_mem_nhds 0 hδ)

private theorem continuousAt_eval_discAlgebra {R δ : ℝ} {W : ℂ → discAlgebra R}
    (hW : AnalyticOnNhd ℂ W (ball 0 δ)) {q : ℂ × ℂ}
    (hq : q ∈ ball (0 : ℂ) δ ×ˢ ball (0 : ℂ) R) :
    ContinuousAt (fun p : ℂ × ℂ => extZero R (W p.1).1 p.2) q := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  set u₀ : C(closedBall (0 : ℂ) R, ℂ) := (W q.1).1
  have hu₀c : ContinuousAt (extZero R u₀) q.2 :=
    (continuousOn_extZero R u₀).continuousAt (closedBall_mem_nhds_of_mem hq.2)
  obtain ⟨r₁, hr₁, hW_ball⟩ := Metric.continuousAt_iff.1 (hW q.1 hq.1).continuousAt (ε / 2)
    (half_pos hε)
  obtain ⟨r₂, hr₂, hu₀_ball⟩ := Metric.continuousAt_iff.1 hu₀c (ε / 2) (half_pos hε)
  obtain ⟨r₃, hr₃, hs_sub⟩ := Metric.isOpen_iff.1 isOpen_ball q.2 hq.2
  refine ⟨min r₁ (min r₂ r₃), lt_min hr₁ (lt_min hr₂ hr₃), fun p hp => ?_⟩
  have hp1 : dist p.1 q.1 < r₁ :=
    (le_max_left _ _).trans_lt (hp.trans_le (min_le_left _ _))
  have hp2_r2 : dist p.2 q.2 < r₂ :=
    (le_max_right _ _).trans_lt (hp.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hp2_r3 : dist p.2 q.2 < r₃ :=
    (le_max_right _ _).trans_lt (hp.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hp2_cb : p.2 ∈ closedBall (0 : ℂ) R := ball_subset_closedBall (hs_sub hp2_r3)
  calc dist (extZero R (W p.1).1 p.2) (extZero R u₀ q.2)
      ≤ dist (extZero R (W p.1).1 p.2) (extZero R u₀ p.2) +
          dist (extZero R u₀ p.2) (extZero R u₀ q.2) := dist_triangle _ _ _
    _ = dist ((W p.1).1 ⟨p.2, hp2_cb⟩) (u₀ ⟨p.2, hp2_cb⟩) +
          dist (extZero R u₀ p.2) (extZero R u₀ q.2) := by
          rw [extZero_of_mem _ hp2_cb, extZero_of_mem _ hp2_cb]
    _ ≤ dist (W p.1) (W q.1) + dist (extZero R u₀ p.2) (extZero R u₀ q.2) := by
          gcongr; exact ContinuousMap.dist_apply_le_dist (f := (W p.1).1) (g := u₀) ⟨p.2, hp2_cb⟩
    _ < ε / 2 + ε / 2 := add_lt_add (hW_ball hp1) (hu₀_ball hp2_r2)
    _ = ε := add_halves ε

/-- An analytic curve `W : ℂ → discAlgebra R` at `0` evaluates to a jointly analytic function of
`(β, s)` at `(0, 0)`. -/
private theorem analyticAt_eval_discAlgebra_of_analyticAt {R : ℝ} (hR : 0 < R)
    {W : ℂ → discAlgebra R} (hW : AnalyticAt ℂ W 0) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => extZero R (W q.1).1 q.2) (0, 0) := by
  obtain ⟨δ, hδ, hWδ⟩ := Metric.mem_nhds_iff.1 ((isOpen_analyticAt ℂ W).mem_nhds hW)
  let e : (Fin 2 → ℂ) ≃L[ℂ] ℂ × ℂ := ContinuousLinearEquiv.finTwoArrow ℂ ℂ
  set Ψ : ℂ × ℂ → ℂ := fun q => extZero R (W q.1).1 q.2
  set S : Set (Fin 2 → ℂ) := e ⁻¹' (ball (0 : ℂ) δ ×ˢ ball (0 : ℂ) R)
  have hball : ball (0 : ℂ) δ ×ˢ ball (0 : ℂ) R ∈ 𝓝 (0 : ℂ × ℂ) := by
    rw [← Prod.mk_zero_zero]
    exact prod_mem_nhds (ball_mem_nhds 0 hδ) (ball_mem_nhds 0 hR)
  have hS : S ∈ 𝓝 0 := (e.continuous.tendsto 0).eventually hball
  have hc : ContinuousOn (Ψ ∘ e) S := fun y hy =>
    ((continuousAt_eval_discAlgebra (fun _ hβ => hWδ hβ) hy).comp
      e.continuous.continuousAt).continuousWithinAt
  have hd : ∀ y ∈ S, ∀ i : Fin 2,
      DifferentiableAt ℂ (fun x => (Ψ ∘ e) (Function.update y i x)) (y i) := by
    intro y hy i
    fin_cases i
    · have hsc : y 1 ∈ closedBall (0 : ℂ) R := ball_subset_closedBall (by simpa [e] using hy.2)
      exact ((((ContinuousMap.evalCLM ℂ ⟨y 1, hsc⟩).comp
        (Submodule.subtypeL (discAlgebra R).toSubmodule)).differentiableAt.comp (y 0)
          (hWδ (by simpa [e] using hy.1)).differentiableAt)).congr_of_eventuallyEq
        (.of_forall fun x => by simp [Ψ, e, extZero_of_mem _ hsc]; rfl)
    · have hWdiff : DifferentiableOn ℂ (extZero R (W (y 0)).1) (ball (0 : ℂ) R) := (W (y 0)).2
      have h1 : y 1 ∈ ball (0 : ℂ) R := by simpa [e] using hy.2
      exact (hWdiff.differentiableAt (isOpen_ball.mem_nhds h1)).congr_of_eventuallyEq
        (.of_forall fun x => by simp [Ψ, e])
  have hΨe : AnalyticAt ℂ (Ψ ∘ e) 0 := hc.analyticAt_of_differentiableAt_update hS hd
  have he0 : e.symm (0, 0) = 0 := map_zero e.symm
  have hcomp : (Ψ ∘ e) ∘ e.symm = Ψ := funext fun q => congrArg Ψ (e.apply_symm_apply q)
  exact hcomp ▸ (he0.symm ▸ hΨe).comp (e.symm.analyticAt (0, 0))

/-- Choose radii `δ, R > 0` so that `F` is jointly analytic on `ball 0 δ ×ˢ closedBall 0 R` and
`F(0, s) = s ^ 3 / 3` on `closedBall 0 R`. -/
private theorem exists_analyticAt_ball_closedBall {F : ℂ × ℂ → ℂ}
    (hF : AnalyticAt ℂ F (0, 0)) (hF0 : ∀ᶠ s in 𝓝 (0 : ℂ), F (0, s) = s ^ 3 / 3) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧
      (∀ β ∈ ball (0 : ℂ) δ, ∀ s ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ F (β, s)) ∧
      ∀ s ∈ closedBall (0 : ℂ) R, F (0, s) = s ^ 3 / 3 := by
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.1 ((isOpen_analyticAt ℂ F).mem_nhds hF)
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.mem_nhds_iff.1 hF0
  set R : ℝ := min r₁ r₂ / 2
  have hR : 0 < R := half_pos (lt_min hr₁ hr₂)
  have hF0_an {s : ℂ} (hs : s ∈ closedBall (0 : ℂ) R) : AnalyticAt ℂ F (0, s) :=
    hball₁ (by simp [Prod.dist_eq, (mem_closedBall_zero_iff.1 hs).trans_lt
      ((half_lt_self (lt_min hr₁ hr₂)).trans_le (min_le_left _ _))])
  have hev_an : ∀ᶠ β in 𝓝 (0 : ℂ), ∀ s ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ F (β, s) :=
    (isCompact_closedBall (0 : ℂ) R).eventually_forall_of_forall_eventually fun _ hs =>
      (hF0_an hs).eventually_analyticAt
  obtain ⟨δ, hδ, hFδ⟩ := Metric.mem_nhds_iff.1 hev_an
  refine ⟨δ, R, hδ, hR, hFδ, fun s hs => hball₂ ?_⟩
  exact mem_ball.2 ((mem_closedBall.1 hs).trans_lt
    ((half_lt_self (lt_min hr₁ hr₂)).trans_le (min_le_right _ _)))

/-- Normalized cubic normal-form existence when `F(0, s) = s ^ 3 / 3` near `s = 0`. -/
private theorem exists_cubic_normal_form_of_normalized {F : ℂ × ℂ → ℂ}
    (hF : AnalyticAt ℂ F (0, 0)) (hF0 : ∀ᶠ s in 𝓝 (0 : ℂ), F (0, s) = s ^ 3 / 3) :
    ∃ ζ₀ η₀ : ℂ → ℂ, ∃ W : ℂ × ℂ → ℂ,
      AnalyticAt ℂ ζ₀ 0 ∧ AnalyticAt ℂ η₀ 0 ∧ AnalyticAt ℂ W (0, 0) ∧
      ζ₀ 0 = 0 ∧ η₀ 0 = 0 ∧ W (0, 0) = 0 ∧ deriv (fun s => W (0, s)) 0 = 1 ∧
      ∀ᶠ q in 𝓝 (0, 0), F q = W q ^ 3 / 3 - ζ₀ q.1 * W q + η₀ q.1 := by
  obtain ⟨δ, R, hδ, hR, hFδ, hF0_cb⟩ := exists_analyticAt_ball_closedBall hF hF0
  set x₀ : discAlgebra R × (ℂ × ℂ) := (idDisc R, (0, 0))
  have hfderiv : fderiv ℂ (cubicMap R) x₀ = cubicLinearEquiv hR :=
    (hasFDerivAt_cubicMap R).fderiv
  obtain ⟨Θ, hΘ, hx₀_src, -, -, hΘsymm⟩ :=
    (analyticAt_cubicMap R x₀).exists_openPartialHomeomorph hfderiv univ_mem
  have hslice_eq : sliceDiscMap hFδ 0 = cubicMap R x₀ := by
    ext s
    rw [sliceDiscMap_apply_coe hFδ (mem_ball_self hδ)]
    simpa [cubicMap_apply_coe, x₀, idDisc] using hF0_cb s.1 s.2
  have hslice_an : AnalyticAt ℂ (sliceDiscMap hFδ) 0 := analyticAt_sliceDiscMap hδ hFδ
  have hmem_tgt : sliceDiscMap hFδ 0 ∈ Θ.target := by
    rw [hslice_eq, ← hΘ]; exact Θ.map_source hx₀_src
  set Φ : ℂ → discAlgebra R × (ℂ × ℂ) := Θ.symm ∘ sliceDiscMap hFδ
  have hΦ_an : AnalyticAt ℂ Φ 0 := (hΘsymm _ hmem_tgt).comp hslice_an
  have hΦ0 : Φ 0 = x₀ := by
    simp only [Φ, Function.comp_apply, hslice_eq, ← hΘ]
    exact Θ.left_inv hx₀_src
  set W : ℂ × ℂ → ℂ := fun q => extZero R (Φ q.1).1.1 q.2
  have hW_an : AnalyticAt ℂ W (0, 0) :=
    analyticAt_eval_discAlgebra_of_analyticAt hR
      (((ContinuousLinearMap.fst ℂ (discAlgebra R) (ℂ × ℂ)).analyticAt _).comp hΦ_an)
  have hW0_slice : ∀ s ∈ closedBall (0 : ℂ) R, W (0, s) = s := fun s hs => by
    simp [W, hΦ0, x₀, idDisc, extZero_of_mem _ hs]
  have hW_deriv : deriv (fun s => W (0, s)) 0 = 1 := by
    have heq : (fun s => W (0, s)) =ᶠ[𝓝 0] id := by
      filter_upwards [closedBall_mem_nhds (0 : ℂ) hR] with s hs using hW0_slice s hs
    rw [heq.deriv_eq, deriv_id]
  refine ⟨fun β => (Φ β).2.1, fun β => (Φ β).2.2, W,
    (((ContinuousLinearMap.fst ℂ ℂ ℂ).comp
      (.snd ℂ (discAlgebra R) (ℂ × ℂ))).analyticAt _).comp hΦ_an,
    (((ContinuousLinearMap.snd ℂ ℂ ℂ).comp
      (.snd ℂ (discAlgebra R) (ℂ × ℂ))).analyticAt _).comp hΦ_an,
    hW_an, by simp [hΦ0, x₀], by simp [hΦ0, x₀], hW0_slice 0 (mem_closedBall_self hR.le),
    hW_deriv, ?_⟩
  have hev_tgt : ∀ᶠ β in 𝓝 (0 : ℂ), sliceDiscMap hFδ β ∈ Θ.target :=
    hslice_an.continuousAt.eventually (Θ.open_target.mem_nhds hmem_tgt)
  filter_upwards [prod_mem_nhds (hev_tgt.and (ball_mem_nhds 0 hδ)) (ball_mem_nhds 0 hR)]
    with ⟨β, s⟩ ⟨⟨hβ_tgt, hβ_δ⟩, hs_R⟩
  have hs_cb : s ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hs_R
  have hright : cubicMap R (Φ β) = sliceDiscMap hFδ β := by
    simpa [Φ, hΘ] using Θ.right_inv hβ_tgt
  have hval := congrArg (fun f : discAlgebra R => f.1 ⟨s, hs_cb⟩) hright
  simp only [cubicMap_apply_coe, sliceDiscMap_apply_coe hFδ hβ_δ] at hval
  simpa [W, extZero_of_mem _ hs_cb] using hval.symm

end DiscAlgebra

/-! ### The holomorphic cubic normal form -/

/-- Vanishing of the first two derivatives and nonvanishing of the third gives analytic order `3`
after subtracting the base value and multiplying by `3`. -/
private theorem analyticOrderAt_three_mul_sub_eq_three {g : ℂ → ℂ} {t₀ : ℂ}
    (hg : AnalyticAt ℂ g t₀) (h₁ : deriv g t₀ = 0) (h₂ : deriv (deriv g) t₀ = 0)
    (h₃ : deriv (deriv (deriv g)) t₀ ≠ 0) :
    analyticOrderAt (fun z => 3 * (g z - g t₀)) t₀ = 3 := by
  have ho₂ : analyticOrderAt (deriv (deriv g)) t₀ = 1 :=
    hg.deriv.deriv.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h₂ h₃
  have ho₁ : analyticOrderAt (deriv g) t₀ = 2 := by
    have h := hg.deriv.analyticOrderAt_deriv_add_one
    rw [h₁, ho₂] at h
    norm_num at h
    exact h.symm
  have ho₀ : analyticOrderAt (fun z => g z - g t₀) t₀ = 3 := by
    have h := hg.analyticOrderAt_deriv_add_one
    rw [ho₁] at h
    norm_num at h
    exact h.symm
  classical
  simpa [ho₀] using
    analyticOrderAt_fun_const_mul (hg.fun_sub (analyticAt_const (v := g t₀))) (3 : ℂ)

/-- Local coordinate `e` in `t` at `t₀` normalizing the slice `p(α₀, t) - p(α₀, t₀)` to
`s ^ 3 / 3`. -/
private theorem exists_slice_cubic_coord {p : ℂ × ℂ → ℂ} {α₀ t₀ : ℂ}
    (hp : AnalyticAt ℂ p (α₀, t₀))
    (h₁ : deriv (fun t => p (α₀, t)) t₀ = 0)
    (h₂ : deriv (deriv fun t => p (α₀, t)) t₀ = 0)
    (h₃ : deriv (deriv (deriv fun t => p (α₀, t))) t₀ ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, t₀ ∈ e.source ∧ e t₀ = 0 ∧
      AnalyticAt ℂ e t₀ ∧ AnalyticAt ℂ e.symm 0 ∧ deriv e t₀ ≠ 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), p (α₀, e.symm s) - p (α₀, t₀) = s ^ 3 / 3 := by
  have hp₀ : AnalyticAt ℂ (fun t => p (α₀, t)) t₀ :=
    hp.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hord : analyticOrderAt (fun z => (3 * (p (α₀, z) - p (α₀, t₀))) -
      (3 * (p (α₀, t₀) - p (α₀, t₀)))) t₀ = 3 := by
    simpa using analyticOrderAt_three_mul_sub_eq_three hp₀ h₁ h₂ h₃
  obtain ⟨e, ht₀_src, he_t₀, -, he_an, he_symm_an, he_pow⟩ :=
    ((analyticAt_const (v := (3 : ℂ))).mul
      (hp₀.sub analyticAt_const)).exists_openPartialHomeomorph_sub_eq_pow
      (by norm_num : 0 < 3) hord univ_mem
  have h0_tgt : (0 : ℂ) ∈ e.target := he_t₀ ▸ e.map_source ht₀_src
  have he_deriv_ne : deriv e t₀ ≠ 0 := by
    intro hzero
    have hcomp := ((he_t₀ ▸ (he_symm_an 0 h0_tgt).differentiableAt.hasDerivAt).comp t₀
      (he_an t₀ ht₀_src).differentiableAt.hasDerivAt).deriv
    have hid : (e.symm ∘ e) =ᶠ[𝓝 t₀] id := by
      filter_upwards [e.open_source.mem_nhds ht₀_src] with z hz using e.left_inv hz
    have h1 : deriv (e.symm ∘ e) t₀ = 1 := by rw [hid.deriv_eq, deriv_id]
    exact one_ne_zero (h1.symm.trans (by simpa [hzero] using hcomp))
  refine ⟨e, ht₀_src, he_t₀, he_an t₀ ht₀_src, he_symm_an 0 h0_tgt, he_deriv_ne, ?_⟩
  filter_upwards [e.open_target.mem_nhds h0_tgt] with s hs
  have h := he_pow (e.symm s) (e.map_target hs)
  rw [e.right_inv hs] at h
  simp only [Pi.mul_apply, Pi.sub_apply] at h
  linear_combination (3⁻¹ : ℂ) * h

end TauCeti

namespace AnalyticAt

open TauCeti

/-- **The analytic Chester-Friedman-Ursell cubic normal form.** If `p : ℂ × ℂ → ℂ` is analytic at
`(α₀, t₀)` with `∂p/∂t (α₀, t₀) = 0`, `∂²p/∂t² (α₀, t₀) = 0`, and `∂³p/∂t³ (α₀, t₀) ≠ 0`, then
there exist functions `ζ` and `η` analytic at `α₀` and `w` analytic at `(α₀, t₀)` with
`ζ(α₀) = 0`, `η(α₀) = p(α₀, t₀)`, `w(α₀, t₀) = 0`, `∂w/∂t (α₀, t₀) ≠ 0`, and
`p(α, t) = w(α, t) ^ 3 / 3 - ζ(α) * w(α, t) + η(α)` near `(α₀, t₀)`. -/
theorem exists_cubic_normal_form {p : ℂ × ℂ → ℂ} {α₀ t₀ : ℂ} (hp : AnalyticAt ℂ p (α₀, t₀))
    (h₁ : deriv (fun t => p (α₀, t)) t₀ = 0)
    (h₂ : deriv (deriv fun t => p (α₀, t)) t₀ = 0)
    (h₃ : deriv (deriv (deriv fun t => p (α₀, t))) t₀ ≠ 0) :
    ∃ ζ η : ℂ → ℂ, ∃ w : ℂ × ℂ → ℂ,
      AnalyticAt ℂ ζ α₀ ∧ AnalyticAt ℂ η α₀ ∧ AnalyticAt ℂ w (α₀, t₀) ∧
      ζ α₀ = 0 ∧ η α₀ = p (α₀, t₀) ∧ w (α₀, t₀) = 0 ∧
      deriv (fun t => w (α₀, t)) t₀ ≠ 0 ∧
      ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1 := by
  obtain ⟨e, ht₀_src, he_t₀, he_an, he_symm_an, he_deriv_ne, he_pow⟩ :=
    exists_slice_cubic_coord hp h₁ h₂ h₃
  have he_symm0 : e.symm 0 = t₀ := he_t₀ ▸ e.left_inv ht₀_src
  set F : ℂ × ℂ → ℂ := fun q => p (α₀ + q.1, e.symm q.2) - p (α₀, t₀)
  have hF : AnalyticAt ℂ F (0, 0) :=
    (hp.comp_of_eq (((analyticAt_const (v := α₀)).add analyticAt_fst).prod
      (he_symm_an.comp_of_eq analyticAt_snd rfl)) (by simp [he_symm0])).sub analyticAt_const
  have hF0 : ∀ᶠ s in 𝓝 (0 : ℂ), F (0, s) = s ^ 3 / 3 := by simpa [F] using he_pow
  obtain ⟨ζ₀, η₀, W, hζ₀, hη₀, hW, hζ₀0, hη₀0, hW0, hW_deriv, hFeq⟩ :=
    exists_cubic_normal_form_of_normalized hF hF0
  set w : ℂ × ℂ → ℂ := fun q => W (q.1 - α₀, e q.2)
  have hw_an : AnalyticAt ℂ w (α₀, t₀) :=
    hW.comp_of_eq ((analyticAt_fst.sub analyticAt_const).prod
      (he_an.comp_of_eq analyticAt_snd rfl)) (by simp [he_t₀])
  have hw_deriv : deriv (fun t => w (α₀, t)) t₀ ≠ 0 := by
    set gW : ℂ → ℂ := fun s => W (0, s)
    have hgW : DifferentiableAt ℂ gW (e t₀) :=
      he_t₀ ▸ (hW.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl).differentiableAt
    have hd := (hgW.hasDerivAt.comp t₀ he_an.differentiableAt.hasDerivAt).deriv
    simp only [Function.comp_def, gW] at hd
    have heq : (fun t => w (α₀, t)) = fun t => W (0, e t) := by ext t; simp [w]
    rw [heq, hd, he_t₀, hW_deriv, one_mul]
    exact he_deriv_ne
  refine ⟨fun α => ζ₀ (α - α₀), fun α => η₀ (α - α₀) + p (α₀, t₀), w,
    hζ₀.comp_of_eq (analyticAt_id.sub analyticAt_const) (sub_self α₀),
    (hη₀.comp_of_eq (analyticAt_id.sub analyticAt_const) (sub_self α₀)).add analyticAt_const,
    hw_an, by simp [hζ₀0], by simp [hη₀0], by simp [w, he_t₀, hW0], hw_deriv, ?_⟩
  have hmap : ContinuousAt (fun q : ℂ × ℂ => (q.1 - α₀, e q.2)) (α₀, t₀) :=
    (continuousAt_fst.sub continuousAt_const).prodMk
      (he_an.continuousAt.comp continuousAt_snd)
  have hnhds : ∀ᶠ q in 𝓝 (α₀, t₀),
      (q.1 - α₀, e q.2) ∈ {r | F r = W r ^ 3 / 3 - ζ₀ r.1 * W r + η₀ r.1} := by
    refine hmap.eventually ?_
    simpa [he_t₀] using hFeq
  filter_upwards [hnhds, prod_mem_nhds univ_mem (e.open_source.mem_nhds ht₀_src)]
    with ⟨α, t⟩ hq ⟨_, ht_src⟩
  dsimp [F] at hq
  rw [add_sub_cancel, e.left_inv ht_src] at hq
  dsimp [w]
  linear_combination hq

end AnalyticAt

namespace TauCeti

/-- **The Chester-Friedman-Ursell holomorphic cubic normal form** (DLMF 2.4.18). Let `p(α, t)` be
complex differentiable on a neighbourhood `U` of `(α₀, t₀)` with `∂p/∂t (α₀, t₀) = 0`,
`∂²p/∂t² (α₀, t₀) = 0`, and `∂³p/∂t³ (α₀, t₀) ≠ 0`. Then there exist `ζ` and `η` complex
differentiable near `α₀` and `w` complex differentiable near `(α₀, t₀)` with `ζ(α₀) = 0`,
`η(α₀) = p(α₀, t₀)`, `w(α₀, t₀) = 0`, `∂w/∂t (α₀, t₀) ≠ 0`, and
`p(α, t) = w(α, t) ^ 3 / 3 - ζ(α) * w(α, t) + η(α)` near `(α₀, t₀)`. -/
theorem exists_cubic_normal_form {p : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)} {α₀ t₀ : ℂ}
    (hU : U ∈ 𝓝 (α₀, t₀)) (hp : DifferentiableOn ℂ p U)
    (h₁ : deriv (fun t => p (α₀, t)) t₀ = 0)
    (h₂ : deriv (deriv fun t => p (α₀, t)) t₀ = 0)
    (h₃ : deriv (deriv (deriv fun t => p (α₀, t))) t₀ ≠ 0) :
    ∃ ζ η : ℂ → ℂ, ∃ w : ℂ × ℂ → ℂ,
      ζ α₀ = 0 ∧ η α₀ = p (α₀, t₀) ∧ w (α₀, t₀) = 0 ∧
      (∀ᶠ α in 𝓝 α₀, DifferentiableAt ℂ ζ α ∧ DifferentiableAt ℂ η α) ∧
      deriv (fun t => w (α₀, t)) t₀ ≠ 0 ∧
      ∀ᶠ q in 𝓝 (α₀, t₀),
        DifferentiableAt ℂ w q ∧ p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1 := by
  obtain ⟨ζ, η, w, hζ, hη, hw, hζ0, hη0, hw0, hdw, hpq⟩ :=
    (hp.analyticAt_of_finiteDimensional hU).exists_cubic_normal_form h₁ h₂ h₃
  refine ⟨ζ, η, w, hζ0, hη0, hw0, ?_, hdw, ?_⟩
  · filter_upwards [hζ.eventually_analyticAt, hη.eventually_analyticAt] with α hζα hηα
    exact ⟨hζα.differentiableAt, hηα.differentiableAt⟩
  · filter_upwards [hw.eventually_analyticAt, hpq] with q hwq heq
    exact ⟨hwq.differentiableAt, heq⟩

/-- Algebraic translation identity relating the depressed cubic `w ^ 3 / 3 - ζ * w + η` (with
`w = u + a`) and DLMF's general cubic `u ^ 3 / 3 + a * u ^ 2 + b * u + c` (DLMF 2.4.18). -/
theorem cubic_add_div_three_sub_mul_add (u a b c : ℂ) :
    (u + a) ^ 3 / 3 - (a ^ 2 - b) * (u + a) + (c - a * b + 2 * a ^ 3 / 3) =
      u ^ 3 / 3 + a * u ^ 2 + b * u + c := by
  ring

/-- **Translated cubic normal form** (DLMF 2.4.18). Given any holomorphic shift `a` near `α₀`,
translating `w` by `-a(α)` writes `p(α, t)` in the form
`u(α, t) ^ 3 / 3 + a(α) * u(α, t) ^ 2 + b(α) * u(α, t) + c(α)`. -/
theorem exists_translated_cubic_normal_form {p : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)} {a : ℂ → ℂ}
    {α₀ t₀ : ℂ} (hU : U ∈ 𝓝 (α₀, t₀)) (hp : DifferentiableOn ℂ p U)
    (h₁ : deriv (fun t => p (α₀, t)) t₀ = 0)
    (h₂ : deriv (deriv fun t => p (α₀, t)) t₀ = 0)
    (h₃ : deriv (deriv (deriv fun t => p (α₀, t))) t₀ ≠ 0)
    (ha : ∀ᶠ α in 𝓝 α₀, DifferentiableAt ℂ a α) :
    ∃ b c : ℂ → ℂ, ∃ u : ℂ × ℂ → ℂ,
      b α₀ = a α₀ ^ 2 ∧ c α₀ = p (α₀, t₀) + a α₀ ^ 3 / 3 ∧ u (α₀, t₀) = -a α₀ ∧
      (∀ᶠ α in 𝓝 α₀, DifferentiableAt ℂ b α ∧ DifferentiableAt ℂ c α) ∧
      deriv (fun t => u (α₀, t)) t₀ ≠ 0 ∧
      ∀ᶠ q in 𝓝 (α₀, t₀),
        DifferentiableAt ℂ u q ∧
          p q = u q ^ 3 / 3 + a q.1 * u q ^ 2 + b q.1 * u q + c q.1 := by
  obtain ⟨ζ, η, w, hζ0, hη0, hw0, hζη, hdw, hw⟩ := exists_cubic_normal_form hU hp h₁ h₂ h₃
  refine ⟨fun α => a α ^ 2 - ζ α, fun α => η α - a α * ζ α + a α ^ 3 / 3,
    fun q => w q - a q.1, by simp [hζ0], by simp [hζ0, hη0], by simp [hw0], ?_,
    by simpa [deriv_sub_const] using hdw, ?_⟩
  · filter_upwards [ha, hζη] with α haα ⟨hζα, hηα⟩
    exact ⟨(haα.pow 2).sub hζα, (hηα.sub (haα.mul hζα)).add ((haα.pow 3).div_const 3)⟩
  · filter_upwards [hw, continuousAt_fst.eventually ha] with q ⟨hwq, hpq⟩ haq
    refine ⟨hwq.sub (haq.comp q differentiableAt_fst), ?_⟩
    rw [hpq]
    ring

/-! ### Critical points, jet identities, and nondegeneracy -/

private theorem analyticAt_of_eventually_differentiableAt {w : ℂ × ℂ → ℂ} {q₀ : ℂ × ℂ}
    (hw : ∀ᶠ q in 𝓝 q₀, DifferentiableAt ℂ w q) : AnalyticAt ℂ w q₀ :=
  DifferentiableOn.analyticAt_of_finiteDimensional
    (s := {q | DifferentiableAt ℂ w q}) (fun _ hq => hq.differentiableWithinAt) hw

/-- Differentiating `g(s) = u(s) ^ 3 / 3 - ζ * u(s) + c` at `t` factors `g'(t)` as
`(u(t) ^ 2 - ζ) * u'(t)`. -/
theorem deriv_eq_sq_sub_mul_deriv {g u : ℂ → ℂ} {t ζ c : ℂ}
    (hu : DifferentiableAt ℂ u t)
    (hgu : ∀ᶠ s in 𝓝 t, g s = u s ^ 3 / 3 - ζ * u s + c) :
    deriv g t = (u t ^ 2 - ζ) * deriv u t := by
  rw [Filter.EventuallyEq.deriv_eq hgu]
  have hd : HasDerivAt (fun s => u s ^ 3 / 3 - ζ * u s + c)
      ((3 * u t ^ (3 - 1) * deriv u t) / 3 - ζ * deriv u t) t :=
    (((hu.hasDerivAt.pow 3).div_const 3).sub (hu.hasDerivAt.const_mul ζ)).add_const c
  rw [hd.deriv]
  ring

/-- At any point where `u'(t) ≠ 0` and `g(s) = u(s) ^ 3 / 3 - ζ * u(s) + c` near `t`, the
critical-point equation `g'(t) = 0` is equivalent to `u(t) ^ 2 = ζ`. -/
theorem deriv_eq_zero_iff_sq_eq {g u : ℂ → ℂ} {t ζ c : ℂ}
    (hdu : deriv u t ≠ 0)
    (hgu : ∀ᶠ s in 𝓝 t, g s = u s ^ 3 / 3 - ζ * u s + c) :
    deriv g t = 0 ↔ u t ^ 2 = ζ := by
  rw [deriv_eq_sq_sub_mul_deriv (differentiableAt_of_deriv_ne_zero hdu) hgu, mul_eq_zero,
    or_iff_left hdu, sub_eq_zero]

/-- Near `(α₀, t₀)`, the critical points `∂p/∂t (α, t) = 0` are mapped by `w` to the square roots
`w(α, t) ^ 2 = ζ(α)`. -/
theorem eventually_deriv_eq_zero_iff_sq_eq {p w : ℂ × ℂ → ℂ} {ζ η : ℂ → ℂ} {α₀ t₀ : ℂ}
    (hw : ∀ᶠ q in 𝓝 (α₀, t₀), DifferentiableAt ℂ w q)
    (hdw : deriv (fun t => w (α₀, t)) t₀ ≠ 0)
    (hpw : ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1) :
    ∀ᶠ q in 𝓝 (α₀, t₀), deriv (fun t => p (q.1, t)) q.2 = 0 ↔ w q ^ 2 = ζ q.1 := by
  have hd_cont : ContinuousAt (fun q : ℂ × ℂ => deriv (fun t => w (q.1, t)) q.2) (α₀, t₀) :=
    (analyticAt_deriv_snd (analyticAt_of_eventually_differentiableAt hw)).continuousAt
  filter_upwards [hd_cont.eventually_ne hdw, hpw.eventually_nhds] with q hq_ne hq_eq
  exact deriv_eq_zero_iff_sq_eq hq_ne
    (by simpa using (Continuous.prodMk_right q.1).continuousAt.eventually hq_eq)

/-- For a one-variable germ `g(t) = u(t) ^ 3 / 3 + c` with `u(t₀) = 0`, the third derivative of `g`
at `t₀` is `2 * u'(t₀) ^ 3`. -/
theorem deriv_deriv_deriv_eq_two_mul_pow_three {g u : ℂ → ℂ} {t₀ c : ℂ}
    (hu0 : u t₀ = 0) (hu : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℂ u t)
    (hgu : ∀ᶠ t in 𝓝 t₀, g t = u t ^ 3 / 3 + c) :
    deriv (deriv (deriv g)) t₀ = 2 * deriv u t₀ ^ 3 := by
  have hua : AnalyticAt ℂ u t₀ := Complex.analyticAt_iff_eventually_differentiableAt.2 hu
  have hd₁ : deriv g =ᶠ[𝓝 t₀] fun t => u t ^ 2 * deriv u t := by
    filter_upwards [hgu.eventually_nhds, hua.eventually_analyticAt] with t ht hut
    rw [Filter.EventuallyEq.deriv_eq ht]
    have hd : HasDerivAt (fun s => u s ^ 3 / 3 + c)
        ((3 * u t ^ (3 - 1) * deriv u t) / 3) t :=
      ((hut.differentiableAt.hasDerivAt.pow 3).div_const 3).add_const c
    rw [hd.deriv]
    ring
  have hd₂ : deriv (deriv g) =ᶠ[𝓝 t₀]
      fun t => 2 * u t * deriv u t ^ 2 + u t ^ 2 * deriv (deriv u) t := by
    filter_upwards [hd₁.eventually_nhds, hua.eventually_analyticAt,
      hua.deriv.eventually_analyticAt] with t ht hut hu't
    rw [Filter.EventuallyEq.deriv_eq ht]
    have h1 : HasDerivAt (fun s => u s ^ 2) (2 * u t ^ (2 - 1) * deriv u t) t :=
      hut.differentiableAt.hasDerivAt.pow 2
    have hd := (h1.mul hu't.differentiableAt.hasDerivAt).deriv
    simp only [Pi.mul_def] at hd
    rw [hd]
    ring
  rw [hd₂.deriv_eq]
  have h_left : HasDerivAt (fun t => 2 * u t * deriv u t ^ 2) (2 * deriv u t₀ ^ 3) t₀ := by
    have h := (hua.differentiableAt.hasDerivAt.const_mul 2).mul
      (hua.deriv.differentiableAt.hasDerivAt.pow 2)
    convert h using 1
    simp [hu0]
    ring
  have h_right : HasDerivAt (fun t => u t ^ 2 * deriv (deriv u) t) 0 t₀ := by
    have h := (hua.differentiableAt.hasDerivAt.pow 2).mul
      hua.deriv.deriv.differentiableAt.hasDerivAt
    convert h using 1
    simp [hu0]
  have hd := (h_left.add h_right).deriv
  simpa [Pi.add_def] using hd

/-- Derivative of `(h - ζ) * g` at `α₀` when `h α₀ = 0`, `h' α₀ = 0`, `ζ α₀ = 0`, and `g α₀ ≠ 0`,
with no regularity assumption on `ζ`. -/
private theorem deriv_sub_mul_of_ne_zero {h ζ g : ℂ → ℂ} {α₀ : ℂ}
    (hh : DifferentiableAt ℂ h α₀) (hh0 : h α₀ = 0) (hh' : deriv h α₀ = 0)
    (hζ0 : ζ α₀ = 0) (hg : AnalyticAt ℂ g α₀) (hg0 : g α₀ ≠ 0) :
    deriv (fun α => (h α - ζ α) * g α) α₀ = -deriv ζ α₀ * g α₀ := by
  by_cases hζd : DifferentiableAt ℂ ζ α₀
  · have hd := ((hh.hasDerivAt.sub hζd.hasDerivAt).mul hg.differentiableAt.hasDerivAt).deriv
    simp only [Pi.mul_def, Pi.sub_def] at hd
    rw [hd, hh', hh0, hζ0]
    ring
  · have hnot : ¬DifferentiableAt ℂ (fun α => (h α - ζ α) * g α) α₀ := by
      intro hfd
      have hζ_eq : ζ =ᶠ[𝓝 α₀] fun α => h α - ((h α - ζ α) * g α) / g α := by
        filter_upwards [hg.continuousAt.eventually_ne hg0] with α hgα
        rw [mul_div_cancel_right₀ _ hgα, sub_sub_cancel]
      exact hζd ((hh.sub (hfd.div hg.differentiableAt hg0)).congr_of_eventuallyEq hζ_eq)
    rw [deriv_zero_of_not_differentiableAt hnot, deriv_zero_of_not_differentiableAt hζd,
      neg_zero, zero_mul]

/-- Along `t = t₀`, `∂p/∂t (α, t₀)` agrees near `α₀` with
`(w(α, t₀) ^ 2 - ζ(α)) * ∂w/∂t (α, t₀)`. -/
private theorem eventuallyEq_deriv_snd_slice {p w : ℂ × ℂ → ℂ} {ζ η : ℂ → ℂ} {α₀ t₀ : ℂ}
    (hwa : AnalyticAt ℂ w (α₀, t₀))
    (hpw : ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1) :
    (fun α => deriv (fun t => p (α, t)) t₀) =ᶠ[𝓝 α₀]
      fun α => (w (α, t₀) ^ 2 - ζ α) * deriv (fun t => w (α, t)) t₀ := by
  filter_upwards [(Continuous.prodMk_left t₀).continuousAt.eventually
    (hwa.eventually_analyticAt.and hpw.eventually_nhds)] with α ⟨hwα, hpα⟩
  have hwt : DifferentiableAt ℂ (fun t => w (α, t)) t₀ :=
    (hwα.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl).differentiableAt
  exact deriv_eq_sq_sub_mul_deriv hwt
    (by simpa using (Continuous.prodMk_right α).continuousAt.eventually hpα)

/-- Mixed-derivative identity when `∂w/∂t (α₀, t₀) ≠ 0`, requiring no continuity hypothesis on
`ζ`. -/
private theorem deriv_deriv_eq_neg_deriv_mul_deriv_of_ne_zero {p w : ℂ × ℂ → ℂ} {ζ η : ℂ → ℂ}
    {α₀ t₀ : ℂ} (hζ0 : ζ α₀ = 0) (hw0 : w (α₀, t₀) = 0)
    (hdw : deriv (fun t => w (α₀, t)) t₀ ≠ 0)
    (hw : ∀ᶠ q in 𝓝 (α₀, t₀), DifferentiableAt ℂ w q)
    (hpw : ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1) :
    deriv (fun α => deriv (fun t => p (α, t)) t₀) α₀ =
      -deriv ζ α₀ * deriv (fun t => w (α₀, t)) t₀ := by
  have hwa : AnalyticAt ℂ w (α₀, t₀) := analyticAt_of_eventually_differentiableAt hw
  have hg : AnalyticAt ℂ (fun α => deriv (fun t => w (α, t)) t₀) α₀ :=
    (analyticAt_deriv_snd hwa).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
  have hw_slice : AnalyticAt ℂ (fun α => w (α, t₀)) α₀ :=
    hwa.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
  have hh' : deriv (fun α => w (α, t₀) ^ 2) α₀ = 0 := by
    have hd := (hw_slice.differentiableAt.hasDerivAt.pow 2).deriv
    simpa [Pi.pow_def, hw0] using hd
  rw [(eventuallyEq_deriv_snd_slice hwa hpw).deriv_eq]
  exact deriv_sub_mul_of_ne_zero (hw_slice.pow 2).differentiableAt (by simp [hw0]) hh' hζ0 hg hdw

/-- **Mixed-derivative identity for the cubic normal form.** For any cubic normal form
`p(α, t) = w(α, t) ^ 3 / 3 - ζ(α) * w(α, t) + η(α)` with `ζ(α₀) = 0`, `w(α₀, t₀) = 0`, and `ζ`
continuous at `α₀`, one has `∂²p/∂α∂t (α₀, t₀) = -ζ'(α₀) * ∂w/∂t (α₀, t₀)`. -/
theorem deriv_deriv_eq_neg_deriv_mul_deriv {p w : ℂ × ℂ → ℂ} {ζ η : ℂ → ℂ} {α₀ t₀ : ℂ}
    (hζ0 : ζ α₀ = 0) (hw0 : w (α₀, t₀) = 0) (hζ : ContinuousAt ζ α₀)
    (hw : ∀ᶠ q in 𝓝 (α₀, t₀), DifferentiableAt ℂ w q)
    (hpw : ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1) :
    deriv (fun α => deriv (fun t => p (α, t)) t₀) α₀ =
      -deriv ζ α₀ * deriv (fun t => w (α₀, t)) t₀ := by
  by_cases hdw : deriv (fun t => w (α₀, t)) t₀ = 0
  · have hwa : AnalyticAt ℂ w (α₀, t₀) := analyticAt_of_eventually_differentiableAt hw
    have hg : AnalyticAt ℂ (fun α => deriv (fun t => w (α, t)) t₀) α₀ :=
      (analyticAt_deriv_snd hwa).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
    have hh : AnalyticAt ℂ (fun α => w (α, t₀) ^ 2) α₀ :=
      (hwa.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl).pow 2
    have ho₁ : (fun α => w (α, t₀) ^ 2 - ζ α) =o[𝓝 α₀] fun _ : ℂ => (1 : ℂ) := by
      rw [Asymptotics.isLittleO_one_iff]
      simpa [Pi.sub_def, hw0, hζ0] using (hh.continuousAt.sub hζ).tendsto
    have ho₂ : (fun α => deriv (fun t => w (α, t)) t₀) =O[𝓝 α₀] fun α => α - α₀ := by
      simpa [hdw] using hg.differentiableAt.hasDerivAt.isBigO_sub
    have hd0 : HasDerivAt
        (fun α => (w (α, t₀) ^ 2 - ζ α) * deriv (fun t => w (α, t)) t₀) 0 α₀ := by
      rw [hasDerivAt_iff_isLittleO]
      simpa [hw0, hζ0, hdw] using ho₁.mul_isBigO ho₂
    rw [(eventuallyEq_deriv_snd_slice hwa hpw).deriv_eq, hd0.deriv, hdw, mul_zero]
  · exact deriv_deriv_eq_neg_deriv_mul_deriv_of_ne_zero hζ0 hw0 hdw hw hpw

/-- **Nondegeneracy criterion for square-root coalescence.** In any cubic normal form
`p(α, t) = w(α, t) ^ 3 / 3 - ζ(α) * w(α, t) + η(α)` with `ζ(α₀) = 0`, `w(α₀, t₀) = 0`, and
`∂w/∂t (α₀, t₀) ≠ 0`, one has `ζ'(α₀) ≠ 0` if and only if `∂²p/∂α∂t (α₀, t₀) ≠ 0`. -/
theorem deriv_zeta_ne_zero_iff {p w : ℂ × ℂ → ℂ} {ζ η : ℂ → ℂ} {α₀ t₀ : ℂ}
    (hζ0 : ζ α₀ = 0) (hw0 : w (α₀, t₀) = 0)
    (hdw : deriv (fun t => w (α₀, t)) t₀ ≠ 0)
    (hw : ∀ᶠ q in 𝓝 (α₀, t₀), DifferentiableAt ℂ w q)
    (hpw : ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1) :
    deriv ζ α₀ ≠ 0 ↔ deriv (fun α => deriv (fun t => p (α, t)) t₀) α₀ ≠ 0 := by
  rw [deriv_deriv_eq_neg_deriv_mul_deriv_of_ne_zero hζ0 hw0 hdw hw hpw,
    mul_ne_zero_iff, neg_ne_zero]
  exact ⟨fun hne => ⟨hne, hdw⟩, fun hne => hne.1⟩

/-! ### Local inverse coordinate and holomorphic transformed amplitude -/

/-- **Holomorphic inverse coordinate and transformed amplitude** (DLMF 2.4.20). Given a coordinate
`w(α, t)` holomorphic near `(α₀, t₀)` with `w(α₀, t₀) = 0` and `∂w/∂t (α₀, t₀) ≠ 0`, and an
amplitude `q(α, t)` holomorphic on `V ∈ 𝓝 (α₀, t₀)`, there exist analytic functions `T` and `f` at
`(α₀, 0)` such that `T(α₀, 0) = t₀`, `w(α, T(α, u)) = u` and `f(α, u) = q(α, T(α, u)) ∂T/∂u (α, u)`
near `(α₀, 0)`, while `T(α, w(α, t)) = t` and `f(α, w(α, t)) ∂w/∂t (α, t) = q(α, t)` near
`(α₀, t₀)`. -/
theorem exists_analyticAt_mul_deriv_eq {w q : ℂ × ℂ → ℂ} {V : Set (ℂ × ℂ)} {α₀ t₀ : ℂ}
    (hw : ∀ᶠ x in 𝓝 (α₀, t₀), DifferentiableAt ℂ w x)
    (hw0 : w (α₀, t₀) = 0)
    (hdw : deriv (fun t => w (α₀, t)) t₀ ≠ 0)
    (hV : V ∈ 𝓝 (α₀, t₀)) (hq : DifferentiableOn ℂ q V) :
    ∃ T f : ℂ × ℂ → ℂ,
      AnalyticAt ℂ T (α₀, 0) ∧ AnalyticAt ℂ f (α₀, 0) ∧ T (α₀, 0) = t₀ ∧
      (∀ᶠ u in 𝓝 (α₀, 0),
        w (u.1, T u) = u.2 ∧ f u = q (u.1, T u) * deriv (fun s => T (u.1, s)) u.2) ∧
      ∀ᶠ x in 𝓝 (α₀, t₀),
        T (x.1, w x) = x.2 ∧ f (x.1, w x) * deriv (fun t => w (x.1, t)) x.2 = q x := by
  have hwa : AnalyticAt ℂ w (α₀, t₀) := analyticAt_of_eventually_differentiableAt hw
  have hqa : AnalyticAt ℂ q (α₀, t₀) := hq.analyticAt_of_finiteDimensional hV
  have hinv : (fderiv ℂ w (α₀, t₀) ∘L .inr ℂ ℂ ℂ).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (.mk0 _ hdw), ?_⟩
    have hd : HasFDerivAt (fun t => w (α₀, t))
        (fderiv ℂ w (α₀, t₀) ∘L .inr ℂ ℂ ℂ) t₀ :=
      hwa.differentiableAt.hasFDerivAt.comp t₀ (hasFDerivAt_prodMk_right α₀ t₀)
    ext
    simp [hd.hasDerivAt.deriv]
  obtain ⟨T, hT_ev, hT0, hT_right, hT_iff⟩ :=
    exists_jointImplicitFunction_of_eventually_differentiableAt hw hinv
  dsimp only at hT_ev hT0 hT_right hT_iff
  rw [hw0] at hT_ev hT0 hT_right hT_iff
  have hTa : AnalyticAt ℂ T (α₀, 0) := hT_ev.self_of_nhds
  set f : ℂ × ℂ → ℂ := fun u => q (u.1, T u) * deriv (fun s => T (u.1, s)) u.2
  have hfa : AnalyticAt ℂ f (α₀, 0) :=
    (hqa.comp_of_eq (analyticAt_fst.prod hTa) (by simp [hT0])).mul (analyticAt_deriv_snd hTa)
  have hT_left : ∀ᶠ x in 𝓝 (α₀, t₀), T (x.1, w x) = x.2 := by
    have hmap : ContinuousAt (fun x : ℂ × ℂ => (x, w x)) (α₀, t₀) :=
      continuousAt_id.prodMk hwa.continuousAt
    filter_upwards [hmap.eventually (by simpa [hw0] using hT_iff)] with x hx
    exact hx.1 rfl
  refine ⟨T, f, hTa, hfa, hT0, hT_right.mono fun _ hu => ⟨hu, rfl⟩, ?_⟩
  have hpull : ContinuousAt (fun x : ℂ × ℂ => (x.1, w x)) (α₀, t₀) :=
    continuousAt_fst.prodMk hwa.continuousAt
  filter_upwards [hT_left.eventually_nhds, hwa.eventually_analyticAt,
    hpull.eventually (by simpa [hw0] using hTa.eventually_analyticAt)] with x hx_nhds hwx hTx
  have hx_eq : T (x.1, w x) = x.2 := hx_nhds.self_of_nhds
  refine ⟨hx_eq, ?_⟩
  have hTs : DifferentiableAt ℂ (fun s => T (x.1, s)) (w x) :=
    (hTx.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl).differentiableAt
  have hwt : DifferentiableAt ℂ (fun t => w (x.1, t)) x.2 :=
    (hwx.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl).differentiableAt
  have hchain := (hTs.hasDerivAt.comp x.2 hwt.hasDerivAt).deriv
  simp only [Function.comp_def] at hchain
  have hid : (fun t => T (x.1, w (x.1, t))) =ᶠ[𝓝 x.2] id :=
    ((continuous_const.prodMk continuous_id).tendsto x.2).eventually hx_nhds
  have hjac : deriv (fun s => T (x.1, s)) (w x) * deriv (fun t => w (x.1, t)) x.2 = 1 := by
    rw [← hchain, hid.deriv_eq, deriv_id]
  dsimp [f]
  rw [hx_eq, mul_assoc, hjac, mul_one]

/-! ### Canonical and degenerate coalescing critical-point models -/

/-- For the canonical Airy potential `p(α, t) = t ^ 3 / 3 - α * t`, the critical points satisfy
`t ^ 2 = α`, coalescing at rate `√α` as `α → 0`. -/
theorem deriv_cubic_sub_mul_eq_zero_iff (α t : ℂ) :
    deriv (fun s : ℂ => s ^ 3 / 3 - α * s) t = 0 ↔ t ^ 2 = α :=
  deriv_eq_zero_iff_sq_eq (u := id) (c := 0) (by simp) (.of_forall fun _ => by simp)

/-- The canonical Airy potential `p(α, t) = t ^ 3 / 3 - α * t` has nonvanishing mixed derivative
`∂²p/∂α∂t (0, 0) = -1`. -/
theorem deriv_deriv_cubic_sub_mul :
    deriv (fun α : ℂ => deriv (fun t : ℂ => t ^ 3 / 3 - α * t) 0) 0 = -1 := by
  have hd : ∀ α : ℂ, deriv (fun t : ℂ => t ^ 3 / 3 - α * t) 0 = -α := fun α => by
    have h := (((hasDerivAt_pow 3 (0 : ℂ)).div_const 3).sub ((hasDerivAt_id 0).const_mul α)).deriv
    simpa [Pi.sub_def] using h
  simp_rw [hd]
  simp

/-- For `p(α, t) = t ^ 3 / 3 + α ^ 2 * t`, the mixed derivative `∂²p/∂α∂t` vanishes at `(0, 0)`,
so any cubic normal form has `ζ'(0) = 0` by `TauCeti.deriv_zeta_ne_zero_iff`. -/
theorem deriv_deriv_cubic_add_sq_mul :
    deriv (fun α : ℂ => deriv (fun t : ℂ => t ^ 3 / 3 + α ^ 2 * t) 0) 0 = 0 := by
  have hd : ∀ α : ℂ, deriv (fun t : ℂ => t ^ 3 / 3 + α ^ 2 * t) 0 = α ^ 2 := fun α => by
    have h :=
      (((hasDerivAt_pow 3 (0 : ℂ)).div_const 3).add ((hasDerivAt_id 0).const_mul (α ^ 2))).deriv
    simpa [Pi.add_def] using h
  simp_rw [hd]
  simp

/-- For `p(α, t) = t ^ 3 / 3 + α ^ 2 * t`, the critical points are `t = ±i * α`, coalescing
linearly in `α` rather than at rate `√α`. -/
theorem deriv_cubic_add_sq_mul_eq_zero_iff (α t : ℂ) :
    deriv (fun s : ℂ => s ^ 3 / 3 + α ^ 2 * s) t = 0 ↔
      t = Complex.I * α ∨ t = -(Complex.I * α) := by
  have hd : deriv (fun s : ℂ => s ^ 3 / 3 + α ^ 2 * s) t = t ^ 2 + α ^ 2 := by
    have h : HasDerivAt (fun s : ℂ => s ^ 3 / 3 + α ^ 2 * s)
        (3 * t ^ (3 - 1) / 3 + α ^ 2 * 1) t :=
      ((hasDerivAt_pow 3 t).div_const 3).add ((hasDerivAt_id t).const_mul (α ^ 2))
    rw [h.deriv]
    ring
  have hfac : t ^ 2 + α ^ 2 = (t - Complex.I * α) * (t - -(Complex.I * α)) := by
    calc t ^ 2 + α ^ 2 = t ^ 2 - (Complex.I ^ 2) * α ^ 2 := by rw [Complex.I_sq]; ring
      _ = (t - Complex.I * α) * (t - -(Complex.I * α)) := by ring
  rw [hd, hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]

end TauCeti
