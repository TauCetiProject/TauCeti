/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Duality

import TauCeti.MeasureTheory.Measure.Decomposition.Prod

/-!
# Schrödinger potentials and entropic duality beyond bounded costs

Let `μ` and `ν` be finite measures on measurable spaces `X` and `Y`, and let `R` be a finite
reference measure on `X × Y` mutually absolutely continuous with respect to `μ.prod ν`. When the
static Schrödinger problem `schroedingerValue R μ ν` is finite, its unique minimizing coupling `γ`
has a positive Radon–Nikodym density against `R` whose logarithm splits into a sum of measurable
marginal potentials,

`dγ / dR (x, y) = exp (φ x + ψ y)`

`R`-almost everywhere, with `(φ, ψ)` `μ`- and `ν`-almost everywhere unique modulo `(a, -a)` for one
real constant `a`. Unlike the bounded log-density construction of
`TauCeti/MeasureTheory/OptimalTransport/Entropic/SchroedingerSystem.lean`, no uniform bound on
`log (dR / d(μ ⊗ ν))` is needed: positivity and additivity of `log (dγ / dR)` follow directly from
optimality of `γ` under bounded four-point cyclic perturbations of its density on truncated level
sets of `dR / d(μ ⊗ ν)` and `dγ / dR`. Because the splitting is extracted from an almost everywhere
section of `(μ ⊗ ν) ⊗ (μ ⊗ ν)`, neither a topology on `X` or `Y` nor separability of the measure
algebras is needed.

When the log-density `llr R (μ.prod ν)` is integrable against `μ.prod ν`, both potentials `φ` and
`ψ` are integrable against their respective marginals: the upper bound `t ≤ exp t` controls the
positive part of `φ(x) + ψ(y)` in `L¹(μ ⊗ ν)`, Fubini's theorem extracts integrable upper bounds on
`φ` and `ψ`, and finite relative entropy `klDiv γ R ≠ ∞` controls `φ(x) + ψ(y)` in `L¹(γ)`.

Applied to the Gibbs reference measure `R = (μ.prod ν).tilted (fun z ↦ -((c z).toReal / ε))` of
entropically regularised optimal transport at temperature `ε > 0`, these two results give:

* the Gibbs density `dπ / d(μ ⊗ ν) = exp ((φ(x) + ψ(y) - c(x, y)) / ε)` of the optimal coupling for
  every `μ ⊗ ν`-almost everywhere finite cost with `entropicTransportCost c ε μ ν ≠ ∞`;
* strong entropic duality and dual attainment by integrable potentials for every cost of finite
  integral against `μ ⊗ ν`, together with uniqueness of dual maximisers up to one additive constant.

## Main statements

* `TauCeti.exists_rnDeriv_eq_exp_add_of_isCoupling_of_forall_klDiv_le`: for finite `μ` and `R` with
  `R ∼ μ ⊗ ν`, a finite-entropy Schrödinger minimizer `γ` has density `exp (φ(x) + ψ(y))` against
  `R`, for measurable potentials unique up to `(a, -a)`.
* `TauCeti.exists_isCoupling_eq_withDensity_exp_add_of_schroedingerValue_ne_top`: when
  `schroedingerValue R μ ν ≠ ∞` and `R ∼ μ ⊗ ν`, there is a minimizing coupling of density
  `exp (φ(x) + ψ(y))` against `R`.
* `TauCeti.IsCoupling.integrable_of_eq_withDensity_exp_add`: when in addition
  `Integrable (llr R (μ.prod ν)) (μ.prod ν)`, any coupling `π` of finite relative entropy against
  `R` with density `exp (φ(x) + ψ(y))` has `φ ∈ L¹(μ)` and `ψ ∈ L¹(ν)`.
* `TauCeti.exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost_of_ne_top`: for
  probability measures, `ε > 0`, and a `μ ⊗ ν`-almost everywhere finite cost of finite regularised
  transport cost, an optimal coupling exists and has the Gibbs factor as density against `μ ⊗ ν`.
* `TauCeti.exists_entropicDualValue_eq_toReal_entropicTransportCost_of_lintegral_ne_top`,
  `TauCeti.isGreatest_entropicDualValue_integrable_of_lintegral_ne_top`, and
  `TauCeti.exists_ae_eq_add_const_of_entropicDualValue_eq_toReal_entropicTransportCost_of_ne_top`:
  strong entropic duality, dual attainment by integrable potentials for `c ∈ L¹(μ ⊗ ν)`, and
  uniqueness of dual maximisers up to one additive constant.

## References

* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  Theorem 2.1 (existence, uniqueness up to a constant, and integrability of Schrödinger potentials
  via cyclic perturbations) and Theorem 4.2 (entropic duality for `L¹` costs).
* L. Rüschendorf and W. Thomsen, *Note on the Schrödinger equation and I-projections*, Statist.
  Probab. Lett. 17 (1993), 369–375.
* I. Csiszár, *I-divergence geometry of probability distributions and minimization problems*, Ann.
  Probab. 3 (1975), 146–158.
-/

public section

noncomputable section

open MeasureTheory InformationTheory Set
open Real (exp log exp_pos exp_log exp_sub exp_add log_exp add_one_le_exp log_zero log_le_log
  log_inv log_nonneg)
open scoped ENNReal NNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} {R γ π : Measure (X × Y)}
  {c : X × Y → ℝ≥0∞} {ε : ℝ≥0} {φ φ' : X → ℝ} {ψ ψ' : Y → ℝ}

/-! ### Four-point cyclic perturbations -/

section FourPoint

/-- Measurable involution on `(X × Y) × (X × Y)` exchanging the two `Y`-coordinates. -/
private def crossSwapEquiv : ((X × Y) × (X × Y)) ≃ᵐ ((X × Y) × (X × Y)) where
  toFun q := ((q.1.1, q.2.2), (q.2.1, q.1.2))
  invFun q := ((q.1.1, q.2.2), (q.2.1, q.1.2))
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by dsimp; fun_prop
  measurable_invFun := by dsimp; fun_prop

private theorem crossSwapEquiv_apply (q : (X × Y) × (X × Y)) :
    crossSwapEquiv q = ((q.1.1, q.2.2), (q.2.1, q.1.2)) := rfl

/-- Exchanging the two `Y`-coordinates preserves `(μ.prod ν).prod (μ.prod ν)`. -/
private theorem measurePreserving_crossSwapEquiv [SFinite μ] [SFinite ν] :
    MeasurePreserving crossSwapEquiv ((μ.prod ν).prod (μ.prod ν))
      ((μ.prod ν).prod (μ.prod ν)) where
  measurable := crossSwapEquiv.measurable
  map_eq := by
    ext s hs
    have hsm : Measurable (s.indicator (1 : ((X × Y) × (X × Y)) → ℝ≥0∞)) :=
      measurable_const.indicator hs
    rw [Measure.map_apply crossSwapEquiv.measurable hs,
      ← lintegral_indicator_one (crossSwapEquiv.measurable hs), ← lintegral_indicator_one hs]
    have hpre : ∀ q, (crossSwapEquiv ⁻¹' s).indicator (1 : ((X × Y) × (X × Y)) → ℝ≥0∞) q =
        s.indicator 1 (crossSwapEquiv q) := fun _ ↦ rfl
    simp_rw [hpre]
    rw [lintegral_prod (fun q ↦ s.indicator 1 (crossSwapEquiv q))
        (hsm.comp crossSwapEquiv.measurable).aemeasurable,
      lintegral_prod (s.indicator 1) hsm.aemeasurable,
      lintegral_prod (fun z₁ ↦ ∫⁻ z₂, s.indicator 1 (crossSwapEquiv (z₁, z₂)) ∂μ.prod ν)
        (by fun_prop),
      lintegral_prod (fun z₁ ↦ ∫⁻ z₂, s.indicator 1 (z₁, z₂) ∂μ.prod ν) (by fun_prop)]
    refine lintegral_congr fun x₁ ↦ ?_
    conv_lhs => arg 2; ext y₁; rw [lintegral_prod (fun z₂ ↦
      s.indicator 1 (crossSwapEquiv ((x₁, y₁), z₂))) (by fun_prop)]
    conv_rhs => arg 2; ext y₁; rw [lintegral_prod (fun z₂ ↦
      s.indicator 1 ((x₁, y₁), z₂)) (by fun_prop)]
    rw [lintegral_lintegral_swap (by fun_prop)]
    conv_lhs => arg 2; ext x₂; rw [lintegral_lintegral_swap (by fun_prop)]
    rw [lintegral_lintegral_swap (by fun_prop)]
    rfl

/-- Given a bounded measurable four-point weight `W` on `(X × Y) × (X × Y)`, its cyclic projection
onto `X × Y` adds mass at `q.1` and `q.2` and removes mass at `(q.1.1, q.2.2)` and
`(q.2.1, q.1.2)`, so both marginals vanish. -/
private def fourPointDelta (μ : Measure X) (ν : Measure Y)
    (W : (X × Y) × (X × Y) → ℝ) (z : X × Y) : ℝ :=
  (∫ w, W (z, w) ∂μ.prod ν + ∫ w, W (w, z) ∂μ.prod ν) -
    (∫ w, W (crossSwapEquiv (z, w)) ∂μ.prod ν + ∫ w, W (crossSwapEquiv (w, z)) ∂μ.prod ν)

private theorem measurable_fourPointDelta [SFinite μ] [SFinite ν]
    {W : (X × Y) × (X × Y) → ℝ} (hW : Measurable W) :
    Measurable (fourPointDelta μ ν W) := by
  have h1 : Measurable fun z ↦ ∫ w, W (z, w) ∂μ.prod ν :=
    hW.stronglyMeasurable.integral_prod_right'.measurable
  have h2 : Measurable fun z ↦ ∫ w, W (w, z) ∂μ.prod ν :=
    (hW.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable
  have h3 : Measurable fun z ↦ ∫ w, W (crossSwapEquiv (z, w)) ∂μ.prod ν :=
    (hW.comp crossSwapEquiv.measurable).stronglyMeasurable.integral_prod_right'.measurable
  have h4 : Measurable fun z ↦ ∫ w, W (crossSwapEquiv (w, z)) ∂μ.prod ν :=
    (hW.comp (crossSwapEquiv.measurable.comp
      measurable_swap)).stronglyMeasurable.integral_prod_right'.measurable
  exact (h1.add h2).sub (h3.add h4)

private theorem abs_integral_le_measure_real_univ [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X × Y → ℝ} (hf : ∀ w, |f w| ≤ 1) :
    |∫ w, f w ∂μ.prod ν| ≤ (μ.prod ν).real univ :=
  calc |∫ w, f w ∂μ.prod ν|
      = ‖∫ w, f w ∂μ.prod ν‖ := (Real.norm_eq_abs _).symm
    _ ≤ 1 * (μ.prod ν).real univ :=
        norm_integral_le_of_norm_le_const (ae_of_all _ fun w ↦ by rw [Real.norm_eq_abs]; exact hf w)
    _ = (μ.prod ν).real univ := one_mul _

private theorem abs_fourPointDelta_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {W : (X × Y) × (X × Y) → ℝ} (hWB : ∀ q, |W q| ≤ 1) (z : X × Y) :
    |fourPointDelta μ ν W z| ≤ 4 * (μ.prod ν).real univ := by
  have h1 := abs_integral_le_measure_real_univ (μ := μ) (ν := ν) fun w ↦ hWB (z, w)
  have h2 := abs_integral_le_measure_real_univ (μ := μ) (ν := ν) fun w ↦ hWB (w, z)
  have h3 := abs_integral_le_measure_real_univ (μ := μ) (ν := ν) fun w ↦
    hWB (crossSwapEquiv (z, w))
  have h4 := abs_integral_le_measure_real_univ (μ := μ) (ν := ν) fun w ↦
    hWB (crossSwapEquiv (w, z))
  unfold fourPointDelta
  linarith [abs_sub ((∫ w, W (z, w) ∂μ.prod ν) + ∫ w, W (w, z) ∂μ.prod ν)
      ((∫ w, W (crossSwapEquiv (z, w)) ∂μ.prod ν) + ∫ w, W (crossSwapEquiv (w, z)) ∂μ.prod ν),
    abs_add_le (∫ w, W (z, w) ∂μ.prod ν) (∫ w, W (w, z) ∂μ.prod ν),
    abs_add_le (∫ w, W (crossSwapEquiv (z, w)) ∂μ.prod ν)
      (∫ w, W (crossSwapEquiv (w, z)) ∂μ.prod ν)]

private theorem fourPointDelta_eq_zero_of_notMem {S : Set (X × Y)}
    {W : (X × Y) × (X × Y) → ℝ}
    (hWS : ∀ q, q.1 ∉ S ∨ q.2 ∉ S ∨ (crossSwapEquiv q).1 ∉ S ∨ (crossSwapEquiv q).2 ∉ S →
      W q = 0)
    {z : X × Y} (hz : z ∉ S) :
    fourPointDelta μ ν W z = 0 := by
  have h1 (w : X × Y) : W (z, w) = 0 := hWS (z, w) (.inl hz)
  have h2 (w : X × Y) : W (w, z) = 0 := hWS (w, z) (.inr (.inl hz))
  have h3 (w : X × Y) : W (crossSwapEquiv (z, w)) = 0 :=
    hWS (crossSwapEquiv (z, w)) (.inr (.inr (.inl hz)))
  have h4 (w : X × Y) : W (crossSwapEquiv (w, z)) = 0 :=
    hWS (crossSwapEquiv (w, z)) (.inr (.inr (.inr hz)))
  simp [fourPointDelta, h1, h2, h3, h4]

/-- Integrating `g * fourPointDelta μ ν W` against `μ ⊗ ν` integrates `W` against the four-point
cross-difference of `g`. -/
private theorem integral_mul_fourPointDelta [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {W : (X × Y) × (X × Y) → ℝ} (hW : Measurable W) (hWB : ∀ q, |W q| ≤ 1)
    {g : X × Y → ℝ} (hg : Measurable g) {M : ℝ} (hgM : ∀ z, |g z| ≤ M) :
    ∫ z, g z * fourPointDelta μ ν W z ∂μ.prod ν =
      ∫ q, (g q.1 + g q.2 - g (crossSwapEquiv q).1 - g (crossSwapEquiv q).2) * W q
        ∂((μ.prod ν).prod (μ.prod ν)) := by
  set P := μ.prod ν
  set Q := P.prod P
  set C := max M 0
  have hC0 : 0 ≤ C := le_max_right M 0
  have hgC (z : X × Y) : |g z| ≤ C := (hgM z).trans (le_max_left M 0)
  have hintQ {F : (X × Y) × (X × Y) → ℝ} (hF : Measurable F) (hFB : ∀ q, |F q| ≤ C) :
      Integrable F Q :=
    .of_bound hF.aestronglyMeasurable C
      (ae_of_all _ fun q ↦ by simpa [Real.norm_eq_abs] using hFB q)
  have hbP {u : X × Y → ℝ} (hu : Measurable u) (huB : ∀ z, |u z| ≤ P.real univ) :
      Integrable (fun z ↦ g z * u z) P :=
    .of_bound (by fun_prop) (C * P.real univ) <| ae_of_all _ fun z ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hgC z) (huB z) (abs_nonneg _) hC0
  have hi1 : Integrable (fun q : (X × Y) × (X × Y) ↦ g q.1 * W q) Q :=
    hintQ (by fun_prop) fun q ↦ by
      rw [abs_mul]; exact (mul_le_mul (hgC q.1) (hWB q) (abs_nonneg _) hC0).trans_eq (mul_one _)
  have hi2 : Integrable (fun q : (X × Y) × (X × Y) ↦ g q.2 * W q) Q :=
    hintQ (by fun_prop) fun q ↦ by
      rw [abs_mul]; exact (mul_le_mul (hgC q.2) (hWB q) (abs_nonneg _) hC0).trans_eq (mul_one _)
  have hi3 : Integrable (fun q : (X × Y) × (X × Y) ↦ g (crossSwapEquiv q).1 * W q) Q :=
    hintQ (by fun_prop) fun q ↦ by
      rw [abs_mul]
      exact (mul_le_mul (hgC (crossSwapEquiv q).1) (hWB q) (abs_nonneg _) hC0).trans_eq (mul_one _)
  have hi4 : Integrable (fun q : (X × Y) × (X × Y) ↦ g (crossSwapEquiv q).2 * W q) Q :=
    hintQ (by fun_prop) fun q ↦ by
      rw [abs_mul]
      exact (mul_le_mul (hgC (crossSwapEquiv q).2) (hWB q) (abs_nonneg _) hC0).trans_eq (mul_one _)
  have ht1 : ∫ z, g z * (∫ w, W (z, w) ∂P) ∂P = ∫ q, g q.1 * W q ∂Q := by
    simp_rw [← integral_const_mul]
    exact (integral_prod (fun q ↦ g q.1 * W q) hi1).symm
  have ht2 : ∫ z, g z * (∫ w, W (w, z) ∂P) ∂P = ∫ q, g q.2 * W q ∂Q := by
    simp_rw [← integral_const_mul]
    exact (integral_prod_symm (fun q ↦ g q.2 * W q) hi2).symm
  have ht3 : ∫ z, g z * (∫ w, W (crossSwapEquiv (z, w)) ∂P) ∂P =
      ∫ q, g (crossSwapEquiv q).1 * W q ∂Q := by
    simp_rw [← integral_const_mul]
    have hi3' : Integrable (fun q : (X × Y) × (X × Y) ↦ g q.1 * W (crossSwapEquiv q)) Q :=
      hintQ (by fun_prop) fun q ↦ by
        rw [abs_mul]
        exact (mul_le_mul (hgC q.1) (hWB (crossSwapEquiv q)) (abs_nonneg _) hC0).trans_eq
          (mul_one _)
    rw [← integral_prod (fun q ↦ g q.1 * W (crossSwapEquiv q)) hi3']
    exact measurePreserving_crossSwapEquiv.integral_comp'
      (fun r ↦ g (crossSwapEquiv r).1 * W r)
  have ht4 : ∫ z, g z * (∫ w, W (crossSwapEquiv (w, z)) ∂P) ∂P =
      ∫ q, g (crossSwapEquiv q).2 * W q ∂Q := by
    simp_rw [← integral_const_mul]
    have hi4' : Integrable (fun q : (X × Y) × (X × Y) ↦ g q.2 * W (crossSwapEquiv q)) Q :=
      hintQ (by fun_prop) fun q ↦ by
        rw [abs_mul]
        exact (mul_le_mul (hgC q.2) (hWB (crossSwapEquiv q)) (abs_nonneg _) hC0).trans_eq
          (mul_one _)
    rw [← integral_prod_symm (fun q ↦ g q.2 * W (crossSwapEquiv q)) hi4']
    exact measurePreserving_crossSwapEquiv.integral_comp'
      (fun r ↦ g (crossSwapEquiv r).2 * W r)
  have hp1 : Integrable (fun z ↦ g z * ∫ w, W (z, w) ∂P) P :=
    hbP hW.stronglyMeasurable.integral_prod_right'.measurable fun z ↦
      abs_integral_le_measure_real_univ fun w ↦ hWB (z, w)
  have hp2 : Integrable (fun z ↦ g z * ∫ w, W (w, z) ∂P) P :=
    hbP (hW.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable
      fun z ↦ abs_integral_le_measure_real_univ fun w ↦ hWB (w, z)
  have hp3 : Integrable (fun z ↦ g z * ∫ w, W (crossSwapEquiv (z, w)) ∂P) P :=
    hbP (hW.comp crossSwapEquiv.measurable).stronglyMeasurable.integral_prod_right'.measurable
      fun z ↦ abs_integral_le_measure_real_univ fun w ↦ hWB (crossSwapEquiv (z, w))
  have hp4 : Integrable (fun z ↦ g z * ∫ w, W (crossSwapEquiv (w, z)) ∂P) P :=
    hbP (hW.comp (crossSwapEquiv.measurable.comp
        measurable_swap)).stronglyMeasurable.integral_prod_right'.measurable
      fun z ↦ abs_integral_le_measure_real_univ fun w ↦ hWB (crossSwapEquiv (w, z))
  have hp12 : Integrable (fun z ↦ g z * ∫ w, W (z, w) ∂P + g z * ∫ w, W (w, z) ∂P) P :=
    hp1.add hp2
  have hp34 : Integrable (fun z ↦ g z * ∫ w, W (crossSwapEquiv (z, w)) ∂P +
      g z * ∫ w, W (crossSwapEquiv (w, z)) ∂P) P := hp3.add hp4
  have hi12 : Integrable (fun q : (X × Y) × (X × Y) ↦ g q.1 * W q + g q.2 * W q) Q := hi1.add hi2
  have hi34 : Integrable (fun q : (X × Y) × (X × Y) ↦
      g (crossSwapEquiv q).1 * W q + g (crossSwapEquiv q).2 * W q) Q := hi3.add hi4
  have hexpand : (fun z ↦ g z * fourPointDelta μ ν W z) =
      fun z ↦ (g z * ∫ w, W (z, w) ∂P + g z * ∫ w, W (w, z) ∂P) -
        (g z * ∫ w, W (crossSwapEquiv (z, w)) ∂P + g z * ∫ w, W (crossSwapEquiv (w, z)) ∂P) :=
    funext fun _ ↦ by unfold fourPointDelta; ring
  have hQexpand : (fun q : (X × Y) × (X × Y) ↦
      (g q.1 + g q.2 - g (crossSwapEquiv q).1 - g (crossSwapEquiv q).2) * W q) =
      fun q ↦ (g q.1 * W q + g q.2 * W q) -
        (g (crossSwapEquiv q).1 * W q + g (crossSwapEquiv q).2 * W q) :=
    funext fun _ ↦ by ring
  rw [hexpand, integral_sub hp12 hp34, integral_add hp1 hp2, integral_add hp3 hp4,
    ht1, ht2, ht3, ht4, hQexpand, integral_sub hi12 hi34, integral_add hi1 hi2,
    integral_add hi3 hi4]

private theorem setIntegral_fourPointDelta_eq_zero [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {W : (X × Y) × (X × Y) → ℝ} (hW : Measurable W) (hWB : ∀ q, |W q| ≤ 1)
    {T : Set (X × Y)} (hT : MeasurableSet T)
    (hcross : ∀ q : (X × Y) × (X × Y),
      T.indicator (1 : X × Y → ℝ) q.1 + T.indicator 1 q.2 -
        T.indicator 1 (crossSwapEquiv q).1 - T.indicator 1 (crossSwapEquiv q).2 = 0) :
    ∫ z in T, fourPointDelta μ ν W z ∂μ.prod ν = 0 := by
  have hind : ∫ z in T, fourPointDelta μ ν W z ∂μ.prod ν =
      ∫ z, T.indicator (1 : X × Y → ℝ) z * fourPointDelta μ ν W z ∂μ.prod ν := by
    rw [← integral_indicator hT]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    by_cases hz : z ∈ T <;> simp [hz]
  have hB (z : X × Y) : |T.indicator (1 : X × Y → ℝ) z| ≤ 1 := by
    by_cases hz : z ∈ T <;> simp [hz]
  rw [hind, integral_mul_fourPointDelta hW hWB (measurable_one.indicator hT) hB]
  simp [hcross]

/-- Perturbing the `R`-density of a coupling `γ ≪ R` by `t * δZ`, where
`δZ * (dR / d(μ ⊗ ν)) = fourPointDelta μ ν W` and the perturbed density remains nonnegative,
produces a coupling of `μ` and `ν`. -/
private theorem isCoupling_withDensity_add_mul_fourPointDelta
    [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) (hγ : IsCoupling γ μ ν) (hγR : γ ≪ R)
    {W : (X × Y) × (X × Y) → ℝ} (hW : Measurable W) (hWB : ∀ q, |W q| ≤ 1)
    {δZ : X × Y → ℝ} (hδZ : Measurable δZ)
    (hδZr : ∀ z, δZ z * (R.rnDeriv (μ.prod ν) z).toReal = fourPointDelta μ ν W z)
    {t : ℝ} (hpos : ∀ z, 0 ≤ (γ.rnDeriv R z).toReal + t * δZ z) :
    IsCoupling
      (R.withDensity fun z ↦ ENNReal.ofReal ((γ.rnDeriv R z).toReal + t * δZ z)) μ ν := by
  have := hγ.isFiniteMeasure
  have : IsFiniteMeasure ν := ⟨by rw [← hγ.measure_univ_eq]; exact measure_lt_top μ univ⟩
  set P := μ.prod ν
  set Z : X × Y → ℝ := fun z ↦ (γ.rnDeriv R z).toReal
  set r : X × Y → ℝ := fun z ↦ (R.rnDeriv P z).toReal
  have hZ_meas : Measurable Z := by fun_prop
  have hr_meas : Measurable r := by fun_prop
  have hR_eq : P.withDensity (fun z ↦ ENNReal.ofReal (r z)) = R :=
    (withDensity_congr_ae <| (Measure.rnDeriv_lt_top R P).mono fun z hz ↦
      ENNReal.ofReal_toReal hz.ne).trans (Measure.withDensity_rnDeriv_eq R P hRμν)
  have hγ_eq : R.withDensity (fun z ↦ ENNReal.ofReal (Z z)) = γ :=
    (withDensity_congr_ae <| (Measure.rnDeriv_lt_top γ R).mono fun z hz ↦
      ENNReal.ofReal_toReal hz.ne).trans (Measure.withDensity_rnDeriv_eq γ R hγR)
  have hγ_P : P.withDensity (fun z ↦ ENNReal.ofReal (Z z * r z)) = γ := by
    rw [← hγ_eq, ← hR_eq, ← withDensity_mul _ (by fun_prop) (by fun_prop)]
    congr 1; funext z
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_comm (r z)]
  have hγt_P : (R.withDensity fun z ↦ ENNReal.ofReal (Z z + t * δZ z)) =
      P.withDensity fun z ↦ ENNReal.ofReal (Z z * r z + t * fourPointDelta μ ν W z) := by
    conv_lhs => rw [← hR_eq]
    rw [← withDensity_mul _ (by fun_prop) (by fun_prop)]
    congr 1; funext z
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    congr 1
    calc r z * (Z z + t * δZ z) = Z z * r z + t * (δZ z * r z) := by ring
      _ = Z z * r z + t * fourPointDelta μ ν W z := by rw [hδZr z]
  have hp_int : Integrable (fun z ↦ Z z * r z) P := by
    refine (lintegral_ofReal_ne_top_iff_integrable
      (f := fun z ↦ Z z * r z) (by fun_prop)
      (ae_of_all _ fun z ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).1 ?_
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, hγ_P]
    exact measure_ne_top γ univ
  have hΔ_int : Integrable (fourPointDelta μ ν W) P :=
    .of_bound (measurable_fourPointDelta hW).aestronglyMeasurable (4 * P.real univ)
      (ae_of_all _ fun z ↦ by simpa [Real.norm_eq_abs] using abs_fourPointDelta_le hWB z)
  have hpt_int : Integrable (fun z ↦ Z z * r z + t * fourPointDelta μ ν W z) P :=
    hp_int.add (hΔ_int.const_mul t)
  have hpt_nonneg (z : X × Y) : 0 ≤ Z z * r z + t * fourPointDelta μ ν W z := by
    have hmul : Z z * r z + t * fourPointDelta μ ν W z = (Z z + t * δZ z) * r z := by
      rw [← hδZr z]; ring
    rw [hmul]
    exact mul_nonneg (hpos z) ENNReal.toReal_nonneg
  have hrect_apply {T : Set (X × Y)} (hT : MeasurableSet T)
      (hvanish : ∫ z in T, fourPointDelta μ ν W z ∂P = 0) :
      (P.withDensity fun z ↦ ENNReal.ofReal (Z z * r z + t * fourPointDelta μ ν W z)) T =
        γ T := by
    rw [withDensity_apply _ hT,
      ← ofReal_integral_eq_lintegral_ofReal hpt_int.integrableOn (ae_of_all _ hpt_nonneg),
      integral_add hp_int.integrableOn (hΔ_int.const_mul t).integrableOn,
      integral_const_mul, hvanish, mul_zero, add_zero,
      ofReal_integral_eq_lintegral_ofReal hp_int.integrableOn
        (ae_of_all _ fun _ ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
      ← withDensity_apply _ hT, hγ_P]
  rw [hγt_P]
  refine isCoupling_of_measure_prod_univ_of_measure_univ_prod (fun s hs ↦ ?_) (fun u hu ↦ ?_)
  · rw [hrect_apply (hs.prod MeasurableSet.univ), hγ.measure_prod_univ hs]
    refine setIntegral_fourPointDelta_eq_zero hW hWB (hs.prod MeasurableSet.univ) fun q ↦ ?_
    have hmem (z : X × Y) : (s ×ˢ (univ : Set Y)).indicator (1 : X × Y → ℝ) z =
        s.indicator 1 z.1 := by
      by_cases hzs : z.1 ∈ s <;> simp [hzs]
    simp only [hmem, crossSwapEquiv_apply]
    ring
  · rw [hrect_apply (MeasurableSet.univ.prod hu), hγ.measure_univ_prod hu]
    refine setIntegral_fourPointDelta_eq_zero hW hWB (MeasurableSet.univ.prod hu) fun q ↦ ?_
    have hmem (z : X × Y) : ((univ : Set X) ×ˢ u).indicator (1 : X × Y → ℝ) z =
        u.indicator 1 z.2 := by
      by_cases hzu : z.2 ∈ u <;> simp [hzu]
    simp only [hmem, crossSwapEquiv_apply]
    ring

/-- Truncated perturbation density `S.indicator (fourPointDelta μ ν W / r)` where
`r = (R.rnDeriv (μ.prod ν) ·).toReal`. -/
private def scaledFourPointDelta (μ : Measure X) (ν : Measure Y) (R : Measure (X × Y))
    (S : Set (X × Y)) (W : (X × Y) × (X × Y) → ℝ) : X × Y → ℝ :=
  S.indicator fun z ↦ fourPointDelta μ ν W z / (R.rnDeriv (μ.prod ν) z).toReal

private theorem measurable_scaledFourPointDelta [SFinite μ] [SFinite ν]
    {S : Set (X × Y)} (hS : MeasurableSet S) {W : (X × Y) × (X × Y) → ℝ} (hW : Measurable W) :
    Measurable (scaledFourPointDelta μ ν R S W) :=
  ((measurable_fourPointDelta hW).div
    (Measure.measurable_rnDeriv R (μ.prod ν)).ennreal_toReal).indicator hS

private theorem scaledFourPointDelta_mul_rnDeriv
    {S : Set (X × Y)} {W : (X × Y) × (X × Y) → ℝ}
    (hrS : ∀ z ∈ S, 0 < (R.rnDeriv (μ.prod ν) z).toReal)
    (hWS : ∀ q, q.1 ∉ S ∨ q.2 ∉ S ∨ (crossSwapEquiv q).1 ∉ S ∨ (crossSwapEquiv q).2 ∉ S →
      W q = 0)
    (z : X × Y) :
    scaledFourPointDelta μ ν R S W z * (R.rnDeriv (μ.prod ν) z).toReal =
      fourPointDelta μ ν W z := by
  by_cases hz : z ∈ S
  · simp [scaledFourPointDelta, indicator_of_mem hz, div_mul_cancel₀ _ (hrS z hz).ne']
  · simp [scaledFourPointDelta, indicator_of_notMem hz, fourPointDelta_eq_zero_of_notMem hWS hz]

private theorem abs_scaledFourPointDelta_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set (X × Y)} {W : (X × Y) × (X × Y) → ℝ} (hWB : ∀ q, |W q| ≤ 1)
    {c : ℝ} (hc : 0 < c) (hrS : ∀ z ∈ S, c⁻¹ ≤ (R.rnDeriv (μ.prod ν) z).toReal) (z : X × Y) :
    |scaledFourPointDelta μ ν R S W z| ≤ 4 * c * (μ.prod ν).real univ := by
  by_cases hz : z ∈ S
  · have hrpos : 0 < (R.rnDeriv (μ.prod ν) z).toReal := (inv_pos.2 hc).trans_le (hrS z hz)
    simp only [scaledFourPointDelta, indicator_of_mem hz]
    rw [abs_div, abs_of_pos hrpos, div_le_iff₀ hrpos]
    calc |fourPointDelta μ ν W z| ≤ 4 * (μ.prod ν).real univ := abs_fourPointDelta_le hWB z
      _ = 4 * (μ.prod ν).real univ * (c⁻¹ * c) := by rw [inv_mul_cancel₀ hc.ne', mul_one]
      _ ≤ 4 * (μ.prod ν).real univ * ((R.rnDeriv (μ.prod ν) z).toReal * c) := by
          gcongr; exact hrS z hz
      _ = 4 * c * (μ.prod ν).real univ * (R.rnDeriv (μ.prod ν) z).toReal := by ring
  · simp only [scaledFourPointDelta, indicator_of_notMem hz, abs_zero]
    positivity

end FourPoint

/-! ### Positivity and additive splitting of the Schrödinger minimizer's log-density -/

section MinimizerDensity

/-- If `Z'` agrees with `(γ.rnDeriv R ·).toReal` outside a measurable set `S` and is bounded by `M`
on `S`, then `klFun ∘ Z'` is `R`-integrable and gives the real relative entropy difference of
`R.withDensity (ENNReal.ofReal ∘ Z')` and `γ`. -/
private theorem klDiv_withDensity_ne_top_and_toReal_sub_eq
    [IsFiniteMeasure γ] [IsFiniteMeasure R] (hKL : klDiv γ R ≠ ∞)
    {Z' : X × Y → ℝ} (hZ' : Measurable Z') (hZ'0 : ∀ z, 0 ≤ Z' z)
    [IsFiniteMeasure (R.withDensity fun z ↦ ENNReal.ofReal (Z' z))]
    {S : Set (X × Y)} (hS : MeasurableSet S) {M : ℝ}
    (h_out : ∀ z ∉ S, Z' z = (γ.rnDeriv R z).toReal)
    (h_in : ∀ z ∈ S, Z' z ≤ M) :
    klDiv (R.withDensity fun z ↦ ENNReal.ofReal (Z' z)) R ≠ ∞ ∧
      (klDiv (R.withDensity fun z ↦ ENNReal.ofReal (Z' z)) R).toReal - (klDiv γ R).toReal =
        ∫ z, (klFun (Z' z) - klFun (γ.rnDeriv R z).toReal) ∂R ∧
      Integrable (fun z ↦ klFun (Z' z) - klFun (γ.rnDeriv R z).toReal) R := by
  obtain ⟨hγR, hllr⟩ := klDiv_ne_top_iff.1 hKL
  set Z : X × Y → ℝ := fun z ↦ (γ.rnDeriv R z).toReal
  have hklZ : Integrable (fun z ↦ klFun (Z z)) R := (integrable_klFun_rnDeriv_iff hγR).2 hllr
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) M) continuous_klFun.continuousOn
  have hSZ' : Integrable (S.indicator fun z ↦ klFun (Z' z)) R := by
    refine .of_bound ((measurable_klFun.comp hZ').indicator hS).aestronglyMeasurable (max K 0) <|
      ae_of_all _ fun z ↦ ?_
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz]
      exact (hK (Z' z) ⟨hZ'0 z, h_in z hz⟩).trans (le_max_left K 0)
    · simp [indicator_of_notMem hz]
  have hdiff_eq : (fun z ↦ klFun (Z' z) - klFun (Z z)) =
      fun z ↦ S.indicator (fun w ↦ klFun (Z' w)) z - S.indicator (fun w ↦ klFun (Z w)) z := by
    funext z
    by_cases hz : z ∈ S
    · simp [indicator_of_mem hz]
    · simp [Z, indicator_of_notMem hz, h_out z hz]
  have hdiff_int : Integrable (fun z ↦ klFun (Z' z) - klFun (Z z)) R := by
    rw [hdiff_eq]
    exact hSZ'.sub (hklZ.indicator hS)
  have hklZ' : Integrable (fun z ↦ klFun (Z' z)) R :=
    (hdiff_int.add hklZ).congr (ae_of_all _ fun _ ↦ sub_add_cancel _ _)
  set γ' := R.withDensity fun z ↦ ENNReal.ofReal (Z' z)
  have hγ'R : γ' ≪ R := withDensity_absolutelyContinuous _ _
  have hrn : (fun z ↦ (γ'.rnDeriv R z).toReal) =ᵐ[R] Z' := by
    filter_upwards [Measure.rnDeriv_withDensity₀ R (f := fun z ↦ ENNReal.ofReal (Z' z))
      (by fun_prop)] with z hz
    rw [hz, ENNReal.toReal_ofReal (hZ'0 z)]
  have hkl_rn : Integrable (fun z ↦ klFun (γ'.rnDeriv R z).toReal) R :=
    (integrable_congr (hrn.mono fun z hz ↦ congrArg klFun hz.symm)).1 hklZ'
  have hKL' : klDiv γ' R ≠ ∞ := klDiv_ne_top hγ'R ((integrable_klFun_rnDeriv_iff hγ'R).1 hkl_rn)
  refine ⟨hKL', ?_, hdiff_int⟩
  rw [toReal_klDiv_eq_integral_klFun hγ'R, toReal_klDiv_eq_integral_klFun hγR,
    integral_congr_ae (hrn.mono fun z hz ↦ congrArg klFun hz), ← integral_sub hklZ' hklZ]

/-- If the zero set `N = {z | (γ.rnDeriv R z).toReal = 0}` of a coupling `γ` has positive
`μ ⊗ ν`-measure, some truncated four-point configuration placing `q.1` in `N` and both
cross-points in `{Z > 0}` has positive `(μ ⊗ ν) ⊗ (μ ⊗ ν)`-measure. -/
private theorem exists_measure_pos_fourPointZeroSet
    [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) (hμνR : μ.prod ν ≪ R) (hγ : IsCoupling γ μ ν) (hγR : γ ≪ R)
    (hN : μ.prod ν {z | (γ.rnDeriv R z).toReal = 0} ≠ 0) :
    ∃ n : ℕ,
      let G := {z : X × Y | ((n : ℝ) + 1)⁻¹ ≤ (R.rnDeriv (μ.prod ν) z).toReal ∧
        (R.rnDeriv (μ.prod ν) z).toReal ≤ (n : ℝ) + 1}
      let H := G ∩ {z : X × Y | ((n : ℝ) + 1)⁻¹ ≤ (γ.rnDeriv R z).toReal ∧
        (γ.rnDeriv R z).toReal ≤ (n : ℝ) + 1}
      let N := {z : X × Y | (γ.rnDeriv R z).toReal = 0}
      ((μ.prod ν).prod (μ.prod ν))
        {q | q.1 ∈ G ∩ N ∧ q.2 ∈ (G ∩ N) ∪ H ∧
          (crossSwapEquiv q).1 ∈ H ∧ (crossSwapEquiv q).2 ∈ H} ≠ 0 := by
  have := hγ.isFiniteMeasure
  have : IsFiniteMeasure ν := ⟨by rw [← hγ.measure_univ_eq]; exact measure_lt_top μ univ⟩
  set P := μ.prod ν
  set Q := P.prod P
  set Z : X × Y → ℝ := fun z ↦ (γ.rnDeriv R z).toReal
  set r : X × Y → ℝ := fun z ↦ (R.rnDeriv P z).toReal
  set N : Set (X × Y) := {z | Z z = 0}
  set G : ℕ → Set (X × Y) := fun n ↦ {z | ((n : ℝ) + 1)⁻¹ ≤ r z ∧ r z ≤ (n : ℝ) + 1}
  set H : ℕ → Set (X × Y) := fun n ↦ G n ∩ {z | ((n : ℝ) + 1)⁻¹ ≤ Z z ∧ Z z ≤ (n : ℝ) + 1}
  set K : ℕ → Set (X × Y) := fun n ↦ (G n ∩ N) ∪ H n
  set M : ℕ → Set ((X × Y) × (X × Y)) := fun n ↦
    {q | q.1 ∈ G n ∩ N ∧ q.2 ∈ K n ∧ (crossSwapEquiv q).1 ∈ H n ∧ (crossSwapEquiv q).2 ∈ H n}
  have hZ_meas : Measurable Z := by fun_prop
  have hr_meas : Measurable r := by fun_prop
  have hN_meas : MeasurableSet N := measurableSet_eq_fun hZ_meas measurable_const
  have hG_mono : Monotone G := fun m n hmn z hz ↦ by
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    exact ⟨(inv_anti₀ (by positivity) hmn').trans hz.1, hz.2.trans hmn'⟩
  have hH_mono : Monotone H := fun m n hmn z hz ↦ by
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    exact ⟨hG_mono hmn hz.1, (inv_anti₀ (by positivity) hmn').trans hz.2.1, hz.2.2.trans hmn'⟩
  -- Every positive real lies in `[((n : ℝ) + 1)⁻¹, n + 1]` for a large `n : ℕ`.
  have hex_nat {u : ℝ} (hu : 0 < u) : ∃ n : ℕ, ((n : ℝ) + 1)⁻¹ ≤ u ∧ u ≤ (n : ℝ) + 1 := by
    obtain ⟨n, hn⟩ := exists_nat_ge (max u⁻¹ u)
    have hn1 : max u⁻¹ u ≤ (n : ℝ) + 1 := hn.trans (by linarith)
    refine ⟨n, ?_, (le_max_right _ _).trans hn1⟩
    rw [inv_le_comm₀ (by positivity) hu]
    exact (le_max_left _ _).trans hn1
  set S : Set (X × Y) := {z | 0 < r z ∧ 0 < Z z}
  have hS_meas : MeasurableSet S :=
    (measurableSet_lt measurable_const hr_meas).inter (measurableSet_lt measurable_const hZ_meas)
  have hr_pos : ∀ᵐ z ∂P, 0 < r z := by
    filter_upwards [hμνR.ae_le (Measure.rnDeriv_pos hRμν), Measure.rnDeriv_lt_top R P]
      with z hpos hlt using ENNReal.toReal_pos hpos.ne' hlt.ne
  -- Row and column sections of `S` have positive marginal measure almost everywhere because
  -- the row and column integrals of `dγ / d(μ ⊗ ν)` equal `1`.
  have hγP : γ ≪ P := hγR.trans hRμν
  have hchain : γ.rnDeriv P =ᵐ[P] fun z ↦ γ.rnDeriv R z * R.rnDeriv P z :=
    (Measure.rnDeriv_mul_rnDeriv hγR).symm
  have hrn_zero {z : X × Y} (hz : z ∉ S) (hZlt : γ.rnDeriv R z < ∞) (hrlt : R.rnDeriv P z < ∞) :
      γ.rnDeriv R z * R.rnDeriv P z = 0 := by
    by_cases hr0 : r z ≤ 0
    · have h0 : (R.rnDeriv P z).toReal = 0 := le_antisymm hr0 ENNReal.toReal_nonneg
      rw [((ENNReal.toReal_eq_zero_iff _).1 h0).resolve_right hrlt.ne, mul_zero]
    · have hZ0 : Z z ≤ 0 := not_lt.1 fun hZp ↦ hz ⟨not_le.1 hr0, hZp⟩
      have h0 : (γ.rnDeriv R z).toReal = 0 := le_antisymm hZ0 ENNReal.toReal_nonneg
      rw [((ENNReal.toReal_eq_zero_iff _).1 h0).resolve_right hZlt.ne, zero_mul]
  have hZltP : ∀ᵐ z ∂P, γ.rnDeriv R z < ∞ := hμνR.ae_le (Measure.rnDeriv_lt_top γ R)
  have hS_row : ∀ᵐ x ∂μ, ν (Prod.mk x ⁻¹' S) ≠ 0 := by
    filter_upwards [Measure.ae_lintegral_rnDeriv_prod_right_eq_one hγ.fst_eq hγP,
      Measure.ae_ae_of_ae_prod hchain, Measure.ae_ae_of_ae_prod hZltP,
      Measure.ae_ae_of_ae_prod (Measure.rnDeriv_lt_top R P)] with x h1 hch hZlt hrlt h0
    have hzero : ∀ᵐ y ∂ν, γ.rnDeriv P (x, y) = 0 := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0, hch, hZlt, hrlt] with y hy hcy hZy hry
      exact hcy.trans (hrn_zero hy hZy hry)
    rw [lintegral_congr_ae hzero, lintegral_zero] at h1
    exact zero_ne_one h1
  have hS_col : ∀ᵐ y ∂ν, μ {x | (x, y) ∈ S} ≠ 0 := by
    filter_upwards [Measure.ae_lintegral_rnDeriv_prod_left_eq_one hγ.snd_eq hγP,
      Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hchain),
      Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hZltP),
      Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae
        (Measure.rnDeriv_lt_top R P))] with y h1 hch hZlt hrlt h0
    have hzero : ∀ᵐ x ∂μ, γ.rnDeriv P (x, y) = 0 := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0, hch, hZlt, hrlt] with x hx hcx hZx hrx
      rw [Prod.swap_prod_mk] at hcx hZx hrx
      exact hcx.trans (hrn_zero hx hZx hrx)
    rw [lintegral_congr_ae hzero, lintegral_zero] at h1
    exact zero_ne_one h1
  by_contra! hall
  have hunion : Q (⋃ n, M n) = 0 := measure_iUnion_null fun n ↦ not_not.1 (hall n)
  set U : Set ((X × Y) × (X × Y)) :=
    {q | (0 < r q.1 ∧ q.1 ∈ N) ∧ 0 < r q.2 ∧ (crossSwapEquiv q).1 ∈ S ∧ (crossSwapEquiv q).2 ∈ S}
  have hU_meas : MeasurableSet U :=
    ((measurableSet_lt measurable_const (hr_meas.comp measurable_fst)).inter
      (measurable_fst hN_meas)).inter <|
      (measurableSet_lt measurable_const (hr_meas.comp measurable_snd)).inter <|
        ((measurable_fst.comp crossSwapEquiv.measurable) hS_meas).inter
          ((measurable_snd.comp crossSwapEquiv.measurable) hS_meas)
  have hex_H {z : X × Y} (hz : z ∈ S) : ∃ n, z ∈ H n := by
    obtain ⟨n₁, hn₁⟩ := hex_nat hz.1
    obtain ⟨n₂, hn₂⟩ := hex_nat hz.2
    have h12 : (n₂ : ℝ) + 1 ≤ ((max n₁ n₂ : ℕ) : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right (le_max_right n₁ n₂) 1
    exact ⟨max n₁ n₂, hG_mono (le_max_left n₁ n₂) hn₁,
      (inv_anti₀ (by positivity) h12).trans hn₂.1, hn₂.2.trans h12⟩
  have hU_sub : U ⊆ ⋃ n, M n := by
    intro q ⟨⟨hr1, hN1⟩, hr2, hS1, hS2⟩
    obtain ⟨n₁, hn₁⟩ := hex_nat hr1
    obtain ⟨n₂, hn₂⟩ := hex_nat hr2
    obtain ⟨n₃, hn₃⟩ := hex_H hS1
    obtain ⟨n₄, hn₄⟩ := hex_H hS2
    rcases (ENNReal.toReal_nonneg : 0 ≤ Z q.2).eq_or_lt with hZq2 | hZq2
    · refine mem_iUnion.2 ⟨max (max n₁ n₂) (max n₃ n₄),
        ⟨hG_mono (by omega) hn₁, hN1⟩, .inl ⟨hG_mono (by omega) hn₂, hZq2.symm⟩,
        hH_mono (by omega) hn₃, hH_mono (by omega) hn₄⟩
    · obtain ⟨n₅, hn₅⟩ := hex_H ⟨hr2, hZq2⟩
      refine mem_iUnion.2 ⟨max n₅ (max (max n₁ n₂) (max n₃ n₄)),
        ⟨hG_mono (by omega) hn₁, hN1⟩, .inr (hH_mono (by omega) hn₅),
        hH_mono (by omega) hn₃, hH_mono (by omega) hn₄⟩
  have hQU : Q U = 0 := measure_mono_null hU_sub hunion
  -- By Tonelli on `Q = P.prod P`, `Q U = 0` forces `P (Prod.mk z₁ ⁻¹' U) = 0` for `P`-a.e. `z₁`.
  rw [Measure.prod_apply hU_meas, lintegral_eq_zero_iff (measurable_measure_prodMk_left hU_meas)]
    at hQU
  have hNr : P {z | 0 < r z ∧ z ∈ N} ≠ 0 := by
    intro h0
    apply hN
    refine measure_mono_null (fun z hz ↦ ?_) (measure_union_null h0 (ae_iff.1 hr_pos))
    by_cases hrz : 0 < r z
    · exact .inl ⟨hrz, hz⟩
    · exact .inr hrz
  have hae : ∀ᵐ z₁ ∂P, z₁ ∉ {z | 0 < r z ∧ z ∈ N} := by
    filter_upwards [hQU, ae_of_ae_fst hS_row, ae_of_ae_snd hS_col] with z₁ hz₁ hrow hcol hmem
    have hrect : P ({x₂ | (x₂, z₁.2) ∈ S} ×ˢ (Prod.mk z₁.1 ⁻¹' S)) = 0 := by
      refine nonpos_iff_eq_zero.1 ?_
      calc P ({x₂ | (x₂, z₁.2) ∈ S} ×ˢ (Prod.mk z₁.1 ⁻¹' S))
          ≤ P ((Prod.mk z₁ ⁻¹' U) ∪ {z₂ | ¬ 0 < r z₂}) := by
            refine measure_mono fun z₂ hz₂ ↦ ?_
            by_cases hrz₂ : 0 < r z₂
            · exact .inl ⟨hmem, hrz₂, hz₂.2, hz₂.1⟩
            · exact .inr hrz₂
        _ ≤ P (Prod.mk z₁ ⁻¹' U) + P {z₂ | ¬ 0 < r z₂} := measure_union_le _ _
        _ = 0 := by rw [hz₁, Pi.zero_apply, ae_iff.1 hr_pos, add_zero]
    rw [Measure.prod_prod, mul_eq_zero] at hrect
    exact hrect.elim hcol hrow
  exact hNr (measure_eq_zero_iff_ae_notMem.2 hae)

/-- **Positivity of the Schrödinger minimizer's density.** When `R ∼ μ ⊗ ν` and `γ` minimizes
`klDiv · R` with `klDiv γ R ≠ ∞`, the Radon–Nikodym density `dγ / dR` is strictly positive
`R`-almost everywhere. -/
private theorem ae_rnDeriv_pos_of_forall_klDiv_le
    [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) (hμνR : μ.prod ν ≪ R)
    (hγ : IsCoupling γ μ ν) (hKL : klDiv γ R ≠ ∞)
    (hmin : ∀ γ', IsCoupling γ' μ ν → klDiv γ R ≤ klDiv γ' R) :
    ∀ᵐ z ∂R, 0 < (γ.rnDeriv R z).toReal := by
  have := hγ.isFiniteMeasure
  have : IsFiniteMeasure ν := ⟨by rw [← hγ.measure_univ_eq]; exact measure_lt_top μ univ⟩
  obtain ⟨hγR, _⟩ := klDiv_ne_top_iff.1 hKL
  set P := μ.prod ν
  set Q := P.prod P
  set Z : X × Y → ℝ := fun z ↦ (γ.rnDeriv R z).toReal
  set r : X × Y → ℝ := fun z ↦ (R.rnDeriv P z).toReal
  set N : Set (X × Y) := {z | Z z = 0}
  suffices hPN : P N = 0 by
    refine hRμν.ae_le ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hPN] with z hz
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
  by_contra hPN
  obtain ⟨n, hQM⟩ := exists_measure_pos_fourPointZeroSet hRμν hμνR hγ hγR hPN
  dsimp only at hQM
  set G : Set (X × Y) := {z | ((n : ℝ) + 1)⁻¹ ≤ r z ∧ r z ≤ (n : ℝ) + 1}
  set H : Set (X × Y) := G ∩ {z | ((n : ℝ) + 1)⁻¹ ≤ Z z ∧ Z z ≤ (n : ℝ) + 1}
  set K : Set (X × Y) := (G ∩ N) ∪ H
  set M : Set ((X × Y) × (X × Y)) :=
    {q | q.1 ∈ G ∩ N ∧ q.2 ∈ K ∧ (crossSwapEquiv q).1 ∈ H ∧ (crossSwapEquiv q).2 ∈ H}
  have hZ_meas : Measurable Z := by fun_prop
  have hr_meas : Measurable r := by fun_prop
  have hN_meas : MeasurableSet N := measurableSet_eq_fun hZ_meas measurable_const
  have hG_meas : MeasurableSet G :=
    (measurableSet_le measurable_const hr_meas).inter (measurableSet_le hr_meas measurable_const)
  have hH_meas : MeasurableSet H := hG_meas.inter
    ((measurableSet_le measurable_const hZ_meas).inter (measurableSet_le hZ_meas measurable_const))
  have hK_meas : MeasurableSet K := (hG_meas.inter hN_meas).union hH_meas
  have hM_meas : MeasurableSet M :=
    (measurable_fst (hG_meas.inter hN_meas)).inter <| (measurable_snd hK_meas).inter <|
      ((measurable_fst.comp crossSwapEquiv.measurable) hH_meas).inter
        ((measurable_snd.comp crossSwapEquiv.measurable) hH_meas)
  set W : (X × Y) × (X × Y) → ℝ := M.indicator 1
  have hW_meas : Measurable W := measurable_const.indicator hM_meas
  have hWB (q : (X × Y) × (X × Y)) : |W q| ≤ 1 := by
    by_cases hq : q ∈ M <;> simp [W, hq]
  have hWK (q : (X × Y) × (X × Y))
      (hq : q.1 ∉ K ∨ q.2 ∉ K ∨ (crossSwapEquiv q).1 ∉ K ∨ (crossSwapEquiv q).2 ∉ K) : W q = 0 := by
    refine indicator_of_notMem (fun hm ↦ ?_) _
    rcases hq with h1 | h2 | h3 | h4
    · exact h1 (.inl hm.1)
    · exact h2 hm.2.1
    · exact h3 (.inr hm.2.2.1)
    · exact h4 (.inr hm.2.2.2)
  have hrK_lb (z : X × Y) (hz : z ∈ K) : ((n : ℝ) + 1)⁻¹ ≤ r z := (hz.elim And.left And.left).1
  set δZ : X × Y → ℝ := scaledFourPointDelta μ ν R K W
  have hδZ_meas : Measurable δZ := measurable_scaledFourPointDelta hK_meas hW_meas
  have hδZr (z : X × Y) : δZ z * r z = fourPointDelta μ ν W z :=
    scaledFourPointDelta_mul_rnDeriv
      (fun w hw ↦ (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹).trans_le (hrK_lb w hw)) hWK z
  set B := 4 * ((n : ℝ) + 1) * P.real univ
  have hB0 : 0 ≤ B := by positivity
  have hδZ_abs (z : X × Y) : |δZ z| ≤ B :=
    abs_scaledFourPointDelta_le hWB (by positivity) hrK_lb z
  -- On `G ∩ N`, both cross-terms vanish and `δZ ≥ 0`, with strictly positive `R`-integral.
  have hGN_nonneg {z : X × Y} (hz : z ∈ G ∩ N) :
      ∫ w, W (z, w) ∂P ≤ fourPointDelta μ ν W z := by
    have hzH : z ∉ H := fun hh ↦ by
      have hZ0 : Z z = 0 := hz.2
      have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      linarith [hh.2.1]
    have h3 (w : X × Y) : W (crossSwapEquiv (z, w)) = 0 :=
      indicator_of_notMem (fun hm : crossSwapEquiv (z, w) ∈ M ↦ hzH hm.2.2.1) _
    have h4 (w : X × Y) : W (crossSwapEquiv (w, z)) = 0 :=
      indicator_of_notMem (fun hm : crossSwapEquiv (w, z) ∈ M ↦ hzH hm.2.2.2) _
    have h2 : 0 ≤ ∫ w, W (w, z) ∂P :=
      integral_nonneg fun _ ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) _
    simp only [fourPointDelta, h3, h4, integral_zero, add_zero, sub_zero]
    linarith
  have hδZ_GN_nonneg {z : X × Y} (hz : z ∈ G ∩ N) : 0 ≤ δZ z := by
    have hzK : z ∈ K := Or.inl hz
    simp only [δZ, scaledFourPointDelta, indicator_of_mem hzK]
    refine div_nonneg ?_ ENNReal.toReal_nonneg
    exact (integral_nonneg fun _ ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) _).trans
      (hGN_nonneg hz)
  have hδZ_int : Integrable δZ R :=
    .of_bound hδZ_meas.aestronglyMeasurable B
      (ae_of_all _ fun z ↦ by simpa [Real.norm_eq_abs] using hδZ_abs z)
  set α := ∫ z in G ∩ N, δZ z ∂R
  have hα_pos : 0 < α := by
    have hα_eq : α = ∫ z in G ∩ N, fourPointDelta μ ν W z ∂P := by
      simp only [α]
      conv_lhs => rw [← Measure.withDensity_rnDeriv_eq R P hRμν]
      rw [setIntegral_withDensity_eq_setIntegral_toReal_smul (Measure.measurable_rnDeriv R P)
        (ae_restrict_of_ae (Measure.rnDeriv_lt_top R P)) δZ (hG_meas.inter hN_meas)]
      refine setIntegral_congr_fun (hG_meas.inter hN_meas) fun z _ ↦ ?_
      rw [smul_eq_mul, mul_comm, hδZr z]
    have hW_int : Integrable W Q :=
      .of_bound hW_meas.aestronglyMeasurable 1
        (ae_of_all _ fun q ↦ by simpa [Real.norm_eq_abs] using hWB q)
    have hu1_int : Integrable (fun z ↦ ∫ w, W (z, w) ∂P) P := hW_int.integral_prod_left
    have hΔ_int : Integrable (fourPointDelta μ ν W) P :=
      .of_bound (measurable_fourPointDelta hW_meas).aestronglyMeasurable (4 * P.real univ)
        (ae_of_all _ fun z ↦ by simpa [Real.norm_eq_abs] using abs_fourPointDelta_le hWB z)
    have hu1_out {z : X × Y} (hz : z ∉ G ∩ N) : ∫ w, W (z, w) ∂P = 0 := by
      have hw (w : X × Y) : W (z, w) = 0 := indicator_of_notMem (fun hm : _ ∈ M ↦ hz hm.1) _
      simp [hw]
    have hQM_pos : 0 < Q.real M := ENNReal.toReal_pos hQM (measure_ne_top Q M)
    have hQ_eq : Q.real M = ∫ z in G ∩ N, (∫ w, W (z, w) ∂P) ∂P := by
      have htot : ∫ q, W q ∂Q = Q.real M := by simp [W, integral_indicator_one hM_meas]
      rw [← htot, integral_prod W hW_int, ← integral_indicator (hG_meas.inter hN_meas)]
      refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
      by_cases hz : z ∈ G ∩ N
      · simp [hz]
      · simp [hz, hu1_out hz]
    rw [hα_eq]
    exact hQM_pos.trans_le <| hQ_eq ▸ setIntegral_mono_on hu1_int.integrableOn hΔ_int.integrableOn
      (hG_meas.inter hN_meas) fun _ hz ↦ hGN_nonneg hz
  -- Choose a small positive step `t` making the logarithmic drop on `G ∩ N` beat the `O(t)` cost
  -- on `H`.
  set C := (B * log ((n : ℝ) + 1) + ((n : ℝ) + 1) * B ^ 2) * R.real univ
  set t := min 1 (min (((n : ℝ) + 1) * (B + 1))⁻¹ (exp (-(C / α)) / (B + 1)))
  have ht_pos : 0 < t := by
    simp only [t, lt_min_iff]
    exact ⟨zero_lt_one, inv_pos.2 (by positivity), div_pos (exp_pos _) (by positivity)⟩
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht_inv : t ≤ (((n : ℝ) + 1) * (B + 1))⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
  have ht_exp : t ≤ exp (-(C / α)) / (B + 1) := (min_le_right _ _).trans (min_le_right _ _)
  set Zt : X × Y → ℝ := fun z ↦ Z z + t * δZ z
  have hZt0 (z : X × Y) : 0 ≤ Zt z := by
    by_cases hz : z ∈ K
    · rcases hz with hzGN | hzH
      · have hZ0 : Z z = 0 := hzGN.2
        simp only [Zt, hZ0, zero_add]
        exact mul_nonneg ht_pos.le (hδZ_GN_nonneg hzGN)
      · have hstep : t * |δZ z| ≤ ((n : ℝ) + 1)⁻¹ := by
          calc t * |δZ z| ≤ (((n : ℝ) + 1) * (B + 1))⁻¹ * (B + 1) :=
                mul_le_mul ht_inv ((hδZ_abs z).trans (by linarith)) (abs_nonneg _) (by positivity)
            _ = ((n : ℝ) + 1)⁻¹ := by
                rw [mul_inv, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
        have habs : |t * δZ z| = t * |δZ z| := by rw [abs_mul, abs_of_pos ht_pos]
        simp only [Zt]
        linarith [hzH.2.1, neg_abs_le (t * δZ z)]
    · simp [Zt, Z, δZ, scaledFourPointDelta, indicator_of_notMem hz]
  have hγt : IsCoupling (R.withDensity fun z ↦ ENNReal.ofReal (Zt z)) μ ν :=
    isCoupling_withDensity_add_mul_fourPointDelta hRμν hγ hγR hW_meas hWB hδZ_meas hδZr hZt0
  have := hγt.isFiniteMeasure
  have hZt_out (z : X × Y) (hz : z ∉ K) : Zt z = Z z := by
    simp [Zt, δZ, scaledFourPointDelta, indicator_of_notMem hz]
  have hZt_in (z : X × Y) (hz : z ∈ K) : Zt z ≤ (n : ℝ) + 1 + B := by
    have hZle : Z z ≤ (n : ℝ) + 1 := by
      rcases hz with hzGN | hzH
      · have hZ0 : Z z = 0 := hzGN.2
        rw [hZ0]; positivity
      · exact hzH.2.2
    have htB : t * δZ z ≤ B := by
      calc t * δZ z ≤ t * |δZ z| := mul_le_mul_of_nonneg_left (le_abs_self _) ht_pos.le
        _ ≤ 1 * B := mul_le_mul ht1 (hδZ_abs z) (abs_nonneg _) zero_le_one
        _ = B := one_mul B
    simp only [Zt]
    linarith
  obtain ⟨hKLt, hsub, hdiff_int⟩ := klDiv_withDensity_ne_top_and_toReal_sub_eq hKL
    (Z' := Zt) (by fun_prop) hZt0 hK_meas hZt_out hZt_in
  have hZ_def (z : X × Y) : (γ.rnDeriv R z).toReal = Z z := rfl
  simp_rw [hZ_def] at hsub hdiff_int
  have hdisj : Disjoint (G ∩ N) H :=
    Set.disjoint_left.2 fun z hzGN hzH ↦ by
      have hZ0 : Z z = 0 := hzGN.2
      have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      linarith [hzH.2.1]
  -- Bound the entropy change separately on `G ∩ N` and on `H`.
  have hbound_GN : ∫ z in G ∩ N, (klFun (Zt z) - klFun (Z z)) ∂R ≤
      t * α * (log (t * (B + 1)) - 1) := by
    have hpt {z : X × Y} (hz : z ∈ G ∩ N) :
        klFun (Zt z) - klFun (Z z) ≤ (t * (log (t * (B + 1)) - 1)) * δZ z := by
      have hZ0 : Z z = 0 := hz.2
      have hu0 : 0 ≤ δZ z := hδZ_GN_nonneg hz
      have huB : δZ z ≤ B + 1 := (le_abs_self _).trans ((hδZ_abs z).trans (by linarith))
      have hkl0 : klFun (Zt z) - klFun (Z z) = t * δZ z * log (t * δZ z) - t * δZ z := by
        simp only [Zt, hZ0, klFun, log_zero, zero_add]; ring
      rw [hkl0]
      rcases hu0.eq_or_lt with h0 | hupos
      · simp [← h0]
      · have hlog : log (t * δZ z) ≤ log (t * (B + 1)) :=
          log_le_log (mul_pos ht_pos hupos) (mul_le_mul_of_nonneg_left huB ht_pos.le)
        nlinarith [mul_le_mul_of_nonneg_left hlog (mul_nonneg ht_pos.le hu0)]
    calc ∫ z in G ∩ N, (klFun (Zt z) - klFun (Z z)) ∂R
        ≤ ∫ z in G ∩ N, (t * (log (t * (B + 1)) - 1)) * δZ z ∂R :=
          setIntegral_mono_on hdiff_int.integrableOn (hδZ_int.const_mul _).integrableOn
            (hG_meas.inter hN_meas) fun _ hz ↦ hpt hz
      _ = t * α * (log (t * (B + 1)) - 1) := by rw [integral_const_mul]; ring
  have hbound_H : ∫ z in H, (klFun (Zt z) - klFun (Z z)) ∂R ≤ t * C := by
    have hpt {z : X × Y} (hz : z ∈ H) :
        klFun (Zt z) - klFun (Z z) ≤ t * (B * log ((n : ℝ) + 1) + ((n : ℝ) + 1) * B ^ 2) := by
      have hZp : 0 < Z z := (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹).trans_le hz.2.1
      have hquad := mul_log_sub_mul_log_sub_le_sq_div hZp (hZt0 z)
      have hkl_id : klFun (Zt z) - klFun (Z z) - (Zt z - Z z) * log (Z z) =
          Zt z * log (Zt z) - Z z * log (Z z) - (Zt z - Z z) * (log (Z z) + 1) := by
        simp only [klFun]; ring
      have hdiffZ : Zt z - Z z = t * δZ z := by simp [Zt]
      have hlog_abs : |log (Z z)| ≤ log ((n : ℝ) + 1) := by
        rw [abs_le]
        refine ⟨?_, log_le_log hZp hz.2.2⟩
        rw [← log_inv]
        exact log_le_log (by positivity) hz.2.1
      have hlin : (t * δZ z) * log (Z z) ≤ t * (B * log ((n : ℝ) + 1)) := by
        calc (t * δZ z) * log (Z z) ≤ |t * δZ z * log (Z z)| := le_abs_self _
          _ = t * (|δZ z| * |log (Z z)|) := by
              rw [abs_mul, abs_mul, abs_of_pos ht_pos, mul_assoc]
          _ ≤ t * (B * log ((n : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul (hδZ_abs z) hlog_abs (abs_nonneg _) hB0)
                ht_pos.le
      have hsq : (t * δZ z) ^ 2 / Z z ≤ t * (((n : ℝ) + 1) * B ^ 2) := by
        have h1 : (t * δZ z) ^ 2 / Z z ≤ (t * δZ z) ^ 2 / ((n : ℝ) + 1)⁻¹ :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hz.2.1
        have h2 : (t * δZ z) ^ 2 / ((n : ℝ) + 1)⁻¹ = ((n : ℝ) + 1) * (t ^ 2 * (δZ z) ^ 2) := by
          rw [div_inv_eq_mul]; ring
        have h3 : t ^ 2 * (δZ z) ^ 2 ≤ t * B ^ 2 := by
          have hδ2 : (δZ z) ^ 2 ≤ B ^ 2 :=
            sq_le_sq.2 ((hδZ_abs z).trans_eq (abs_of_nonneg hB0).symm)
          have ht2 : t ^ 2 ≤ t := by nlinarith
          exact mul_le_mul ht2 hδ2 (sq_nonneg _) ht_pos.le
        linarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
      rw [← hkl_id, hdiffZ] at hquad
      linarith
    calc ∫ z in H, (klFun (Zt z) - klFun (Z z)) ∂R
        ≤ ∫ _ in H, t * (B * log ((n : ℝ) + 1) + ((n : ℝ) + 1) * B ^ 2) ∂R :=
          setIntegral_mono_on hdiff_int.integrableOn (integrable_const _).integrableOn hH_meas
            fun _ hz ↦ hpt hz
      _ = R.real H * (t * (B * log ((n : ℝ) + 1) + ((n : ℝ) + 1) * B ^ 2)) := by
          simp [integral_const]
      _ ≤ R.real univ * (t * (B * log ((n : ℝ) + 1) + ((n : ℝ) + 1) * B ^ 2)) := by
          refine mul_le_mul_of_nonneg_right (ENNReal.toReal_mono (measure_ne_top R univ)
            (measure_mono (subset_univ H))) ?_
          exact mul_nonneg ht_pos.le (add_nonneg (mul_nonneg hB0 (log_nonneg (by linarith)))
            (by positivity))
      _ = t * C := by simp only [C]; ring
  have htot_eq : ∫ z, (klFun (Zt z) - klFun (Z z)) ∂R =
      (∫ z in G ∩ N, (klFun (Zt z) - klFun (Z z)) ∂R) +
        ∫ z in H, (klFun (Zt z) - klFun (Z z)) ∂R := by
    rw [← setIntegral_union hdisj hH_meas hdiff_int.integrableOn hdiff_int.integrableOn,
      ← integral_indicator hK_meas]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    by_cases hz : z ∈ K
    · simp [indicator_of_mem hz]
    · simp [indicator_of_notMem hz, hZt_out z hz]
  have hlog_t : log (t * (B + 1)) ≤ -(C / α) := by
    have htB : t * (B + 1) ≤ exp (-(C / α)) := (le_div_iff₀ (by positivity)).1 ht_exp
    exact (log_le_log (mul_pos ht_pos (by positivity)) htB).trans_eq (log_exp _)
  have hneg : (klDiv (R.withDensity fun z ↦ ENNReal.ofReal (Zt z)) R).toReal -
      (klDiv γ R).toReal < 0 := by
    rw [hsub, htot_eq]
    have hmul : t * α * (log (t * (B + 1)) - 1) ≤ t * (-C - α) := by
      have h1 : α * (log (t * (B + 1)) - 1) ≤ -C - α := by
        have hle := mul_le_mul_of_nonneg_left hlog_t hα_pos.le
        have hcancel : α * -(C / α) = -C := by field_simp [hα_pos.ne']
        linarith
      nlinarith
    linarith [mul_pos ht_pos hα_pos]
  have hge : (klDiv γ R).toReal ≤
      (klDiv (R.withDensity fun z ↦ ENNReal.ofReal (Zt z)) R).toReal :=
    ENNReal.toReal_mono hKLt (hmin _ hγt)
  linarith

/-- For a minimizing coupling `γ`, the four-point cross-difference of `log (dγ / dR)` is
`(μ ⊗ ν) ⊗ (μ ⊗ ν)`-almost everywhere nonpositive. -/
private theorem ae_crossDiff_log_rnDeriv_nonpos_of_forall_klDiv_le
    [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) (hμνR : μ.prod ν ≪ R)
    (hγ : IsCoupling γ μ ν) (hKL : klDiv γ R ≠ ∞)
    (hmin : ∀ γ', IsCoupling γ' μ ν → klDiv γ R ≤ klDiv γ' R) :
    ∀ᵐ q ∂((μ.prod ν).prod (μ.prod ν)),
      log (γ.rnDeriv R q.1).toReal + log (γ.rnDeriv R q.2).toReal -
        log (γ.rnDeriv R (crossSwapEquiv q).1).toReal -
        log (γ.rnDeriv R (crossSwapEquiv q).2).toReal ≤ 0 := by
  have := hγ.isFiniteMeasure
  have : IsFiniteMeasure ν := ⟨by rw [← hγ.measure_univ_eq]; exact measure_lt_top μ univ⟩
  obtain ⟨hγR, _⟩ := klDiv_ne_top_iff.1 hKL
  set P := μ.prod ν
  set Q := P.prod P
  set Z : X × Y → ℝ := fun z ↦ (γ.rnDeriv R z).toReal
  set r : X × Y → ℝ := fun z ↦ (R.rnDeriv P z).toReal
  set f : X × Y → ℝ := fun z ↦ log (Z z)
  set D : (X × Y) × (X × Y) → ℝ := fun q ↦
    f q.1 + f q.2 - f (crossSwapEquiv q).1 - f (crossSwapEquiv q).2
  set Spos : Set ((X × Y) × (X × Y)) := {q | 0 < D q}
  have hZ_meas : Measurable Z := by fun_prop
  have hr_meas : Measurable r := by fun_prop
  have hf_meas : Measurable f := by fun_prop
  have hD_meas : Measurable D := by dsimp only [D]; fun_prop
  have hSpos_meas : MeasurableSet Spos := measurableSet_lt measurable_const hD_meas
  set H : ℕ → Set (X × Y) := fun n ↦
    {z | ((n : ℝ) + 1)⁻¹ ≤ r z ∧ r z ≤ (n : ℝ) + 1 ∧
      ((n : ℝ) + 1)⁻¹ ≤ Z z ∧ Z z ≤ (n : ℝ) + 1}
  set A : ℕ → Set ((X × Y) × (X × Y)) := fun n ↦
    {q | q ∈ Spos ∧ q.1 ∈ H n ∧ q.2 ∈ H n ∧
      (crossSwapEquiv q).1 ∈ H n ∧ (crossSwapEquiv q).2 ∈ H n}
  have hH_meas (n : ℕ) : MeasurableSet (H n) :=
    (measurableSet_le measurable_const hr_meas).inter <|
      (measurableSet_le hr_meas measurable_const).inter <|
        (measurableSet_le measurable_const hZ_meas).inter
          (measurableSet_le hZ_meas measurable_const)
  have hA_meas (n : ℕ) : MeasurableSet (A n) :=
    hSpos_meas.inter <| (measurable_fst (hH_meas n)).inter <| (measurable_snd (hH_meas n)).inter <|
      ((measurable_fst.comp crossSwapEquiv.measurable) (hH_meas n)).inter
        ((measurable_snd.comp crossSwapEquiv.measurable) (hH_meas n))
  -- Each truncated positive-defect set `A n` is `Q`-null by optimality under `-t * δZ`.
  have hQA (n : ℕ) : Q (A n) = 0 := by
    set W : (X × Y) × (X × Y) → ℝ := (A n).indicator 1
    have hW_meas : Measurable W := measurable_const.indicator (hA_meas n)
    have hWB (q : (X × Y) × (X × Y)) : |W q| ≤ 1 := by
      by_cases hq : q ∈ A n <;> simp [W, hq]
    have hWH (q : (X × Y) × (X × Y))
        (hq : q.1 ∉ H n ∨ q.2 ∉ H n ∨ (crossSwapEquiv q).1 ∉ H n ∨ (crossSwapEquiv q).2 ∉ H n) :
        W q = 0 := by
      refine indicator_of_notMem (fun hm ↦ ?_) _
      rcases hq with hq1 | hq2 | hq3 | hq4
      · exact hq1 hm.2.1
      · exact hq2 hm.2.2.1
      · exact hq3 hm.2.2.2.1
      · exact hq4 hm.2.2.2.2
    set δZ : X × Y → ℝ := scaledFourPointDelta μ ν R (H n) W
    have hδZ_meas : Measurable δZ := measurable_scaledFourPointDelta (hH_meas n) hW_meas
    have hδZr (z : X × Y) : δZ z * r z = fourPointDelta μ ν W z :=
      scaledFourPointDelta_mul_rnDeriv
        (fun _ (hw : _ ∈ H n) ↦ (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹).trans_le hw.1) hWH z
    set B := 4 * ((n : ℝ) + 1) * P.real univ
    have hB0 : 0 ≤ B := by positivity
    have hδZ_abs (z : X × Y) : |δZ z| ≤ B :=
      abs_scaledFourPointDelta_le hWB (by positivity) (fun _ (hw : _ ∈ H n) ↦ hw.1) z
    set g : X × Y → ℝ := (H n).indicator f
    have hg_meas : Measurable g := hf_meas.indicator (hH_meas n)
    have hgB (z : X × Y) : |g z| ≤ log ((n : ℝ) + 1) := by
      by_cases hz : z ∈ H n
      · simp only [g, indicator_of_mem hz]
        rw [abs_le]
        have hZp : 0 < Z z := (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹).trans_le hz.2.2.1
        refine ⟨?_, log_le_log hZp hz.2.2.2⟩
        rw [← log_inv]
        exact log_le_log (by positivity) hz.2.2.1
      · simp only [g, indicator_of_notMem hz, abs_zero]
        exact log_nonneg (by linarith)
    have hD_bound {q : (X × Y) × (X × Y)} (hq : q ∈ A n) :
        |D q| ≤ 4 * log ((n : ℝ) + 1) := by
      have heq : D q = g q.1 + g q.2 - g (crossSwapEquiv q).1 - g (crossSwapEquiv q).2 := by
        simp [D, g, indicator_of_mem hq.2.1, indicator_of_mem hq.2.2.1,
          indicator_of_mem hq.2.2.2.1, indicator_of_mem hq.2.2.2.2]
      rw [heq]
      linarith [abs_sub (g q.1 + g q.2 - g (crossSwapEquiv q).1) (g (crossSwapEquiv q).2),
        abs_sub (g q.1 + g q.2) (g (crossSwapEquiv q).1), abs_add_le (g q.1) (g q.2),
        hgB q.1, hgB q.2, hgB (crossSwapEquiv q).1, hgB (crossSwapEquiv q).2]
    have hD_intOn : IntegrableOn D (A n) Q := by
      rw [← integrable_indicator_iff (hA_meas n)]
      refine .of_bound (hD_meas.indicator (hA_meas n)).aestronglyMeasurable
        (4 * log ((n : ℝ) + 1)) (ae_of_all _ fun q ↦ ?_)
      by_cases hq : q ∈ A n
      · simpa [Real.norm_eq_abs, indicator_of_mem hq] using hD_bound hq
      · simp only [indicator_of_notMem hq, Real.norm_eq_abs, abs_zero]
        exact mul_nonneg (by positivity) (log_nonneg (by linarith))
    have hpair : ∫ z, g z * δZ z ∂R = ∫ q in A n, D q ∂Q := by
      have h1 : ∫ z, g z * δZ z ∂R = ∫ z, g z * fourPointDelta μ ν W z ∂P := by
        conv_lhs => rw [← Measure.withDensity_rnDeriv_eq R P hRμν]
        rw [integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv R P)
          (Measure.rnDeriv_lt_top R P)]
        refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
        dsimp only
        rw [smul_eq_mul]
        calc r z * (g z * δZ z) = g z * (δZ z * r z) := by ring
          _ = g z * fourPointDelta μ ν W z := by rw [hδZr z]
      rw [h1, integral_mul_fourPointDelta hW_meas hWB hg_meas hgB, ← integral_indicator (hA_meas n)]
      refine integral_congr_ae (ae_of_all _ fun q ↦ ?_)
      by_cases hq : q ∈ A n
      · simp [W, D, g, indicator_of_mem hq, indicator_of_mem hq.2.1, indicator_of_mem hq.2.2.1,
          indicator_of_mem hq.2.2.2.1, indicator_of_mem hq.2.2.2.2]
      · simp [W, indicator_of_notMem hq]
    -- Show `∫ q in A n, D q ∂Q ≤ 0` via first-variation optimality at a small step `-t`.
    have hle_zero : ∫ q in A n, D q ∂Q ≤ 0 := by
      by_contra! hpos_int
      set I := ∫ q in A n, D q ∂Q
      set Kquad := ((n : ℝ) + 1) * B ^ 2 * R.real univ
      set t := min 1 (min (((n : ℝ) + 1) * (B + 1))⁻¹ (I / (2 * (Kquad + 1))))
      have ht_pos : 0 < t := by
        simp only [t, lt_min_iff]
        exact ⟨zero_lt_one, inv_pos.2 (by positivity), div_pos hpos_int (by positivity)⟩
      have ht1 : t ≤ 1 := min_le_left _ _
      have ht_inv : t ≤ (((n : ℝ) + 1) * (B + 1))⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
      have ht_I : t ≤ I / (2 * (Kquad + 1)) := (min_le_right _ _).trans (min_le_right _ _)
      set Zt : X × Y → ℝ := fun z ↦ Z z + (-t) * δZ z
      have hZt0 (z : X × Y) : 0 ≤ Zt z := by
        by_cases hz : z ∈ H n
        · have hstep : t * |δZ z| ≤ ((n : ℝ) + 1)⁻¹ := by
            calc t * |δZ z| ≤ (((n : ℝ) + 1) * (B + 1))⁻¹ * (B + 1) :=
                  mul_le_mul ht_inv ((hδZ_abs z).trans (by linarith)) (abs_nonneg _) (by positivity)
              _ = ((n : ℝ) + 1)⁻¹ := by
                  rw [mul_inv, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
          have habs : |t * δZ z| = t * |δZ z| := by rw [abs_mul, abs_of_pos ht_pos]
          simp only [Zt]
          linarith [hz.2.2.1, le_abs_self (t * δZ z)]
        · simp [Zt, Z, δZ, scaledFourPointDelta, indicator_of_notMem hz]
      have hγt : IsCoupling (R.withDensity fun z ↦ ENNReal.ofReal (Zt z)) μ ν :=
        isCoupling_withDensity_add_mul_fourPointDelta hRμν hγ hγR hW_meas hWB hδZ_meas hδZr hZt0
      have := hγt.isFiniteMeasure
      have hZt_out (z : X × Y) (hz : z ∉ H n) : Zt z = Z z := by
        simp [Zt, δZ, scaledFourPointDelta, indicator_of_notMem hz]
      have hZt_in (z : X × Y) (hz : z ∈ H n) : Zt z ≤ (n : ℝ) + 1 + B := by
        have htB : (-t) * δZ z ≤ B := by
          calc (-t) * δZ z ≤ |(-t) * δZ z| := le_abs_self _
            _ = t * |δZ z| := by rw [abs_mul, abs_neg, abs_of_pos ht_pos]
            _ ≤ 1 * B := mul_le_mul ht1 (hδZ_abs z) (abs_nonneg _) zero_le_one
            _ = B := one_mul B
        simp only [Zt]
        linarith [hz.2.2.2]
      obtain ⟨hKLt, hsub, hdiff_int⟩ := klDiv_withDensity_ne_top_and_toReal_sub_eq hKL
        (Z' := Zt) (by fun_prop) hZt0 (hH_meas n) hZt_out hZt_in
      have hgδ_int : Integrable (fun z ↦ g z * δZ z) R :=
        .of_bound (by fun_prop) (log ((n : ℝ) + 1) * B) <| ae_of_all _ fun z ↦ by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hgB z) (hδZ_abs z) (abs_nonneg _)
            (log_nonneg (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1))
      have hpt (z : X × Y) :
          klFun (Zt z) - klFun (Z z) ≤ -t * (g z * δZ z) + t ^ 2 * (((n : ℝ) + 1) * B ^ 2) := by
        by_cases hz : z ∈ H n
        · have hZp : 0 < Z z := (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹).trans_le hz.2.2.1
          have hquad := mul_log_sub_mul_log_sub_le_sq_div hZp (hZt0 z)
          have hkl_id : klFun (Zt z) - klFun (Z z) - (Zt z - Z z) * log (Z z) =
              Zt z * log (Zt z) - Z z * log (Z z) - (Zt z - Z z) * (log (Z z) + 1) := by
            simp only [klFun]; ring
          have hdiffZ : Zt z - Z z = -t * δZ z := by simp [Zt]
          have hgz : g z = log (Z z) := indicator_of_mem hz _
          have hsq : (-t * δZ z) ^ 2 / Z z ≤ t ^ 2 * (((n : ℝ) + 1) * B ^ 2) := by
            have h1 : (-t * δZ z) ^ 2 / Z z ≤ (-t * δZ z) ^ 2 / ((n : ℝ) + 1)⁻¹ :=
              div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hz.2.2.1
            have h2 : (-t * δZ z) ^ 2 / ((n : ℝ) + 1)⁻¹ = t ^ 2 * ((n : ℝ) + 1) * (δZ z) ^ 2 := by
              rw [div_inv_eq_mul]; ring
            have hδ2 : (δZ z) ^ 2 ≤ B ^ 2 :=
              sq_le_sq.2 ((hδZ_abs z).trans_eq (abs_of_nonneg hB0).symm)
            linarith [mul_le_mul_of_nonneg_left hδ2 (by positivity : 0 ≤ t ^ 2 * ((n : ℝ) + 1))]
          rw [← hkl_id, hdiffZ, ← hgz] at hquad
          linarith
        · simp only [hZt_out z hz, g, δZ, scaledFourPointDelta, indicator_of_notMem hz,
            sub_self, mul_zero, zero_add]
          positivity
      have hint_ub : ∫ z, (klFun (Zt z) - klFun (Z z)) ∂R ≤ -t * I + t ^ 2 * Kquad := by
        calc ∫ z, (klFun (Zt z) - klFun (Z z)) ∂R
            ≤ ∫ z, (-t * (g z * δZ z) + t ^ 2 * (((n : ℝ) + 1) * B ^ 2)) ∂R :=
              integral_mono hdiff_int ((hgδ_int.const_mul (-t)).add (integrable_const _)) hpt
          _ = -t * ∫ z, g z * δZ z ∂R + R.real univ * (t ^ 2 * (((n : ℝ) + 1) * B ^ 2)) := by
              rw [integral_add (hgδ_int.const_mul (-t)) (integrable_const _),
                integral_const_mul, integral_const, smul_eq_mul]
          _ = -t * I + t ^ 2 * Kquad := by rw [hpair]; simp only [Kquad]; ring
      have hge : 0 ≤ ∫ z, (klFun (Zt z) - klFun (Z z)) ∂R := by
        rw [← hsub, sub_nonneg]
        exact ENNReal.toReal_mono hKLt (hmin _ hγt)
      have htK : t * Kquad ≤ I / 2 := by
        have h1 : t * (Kquad + 1) ≤ I / 2 := by
          have h2 := (le_div_iff₀ (by positivity : 0 < 2 * (Kquad + 1))).1 ht_I
          linarith
        nlinarith [ht_pos]
      nlinarith [mul_pos ht_pos hpos_int, mul_le_mul_of_nonneg_left htK ht_pos.le]
    have hzero_int : ∫ q in A n, D q ∂Q = 0 :=
      le_antisymm hle_zero (setIntegral_nonneg (hA_meas n) fun _ hq ↦ hq.1.le)
    have hae_zero : ∀ᵐ q ∂Q.restrict (A n), D q = 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        ((ae_restrict_mem (hA_meas n)).mono fun _ hq ↦ hq.1.le) hD_intOn).1 hzero_int
    have hae_false : ∀ᵐ _ ∂Q.restrict (A n), False := by
      filter_upwards [hae_zero, ae_restrict_mem (hA_meas n)] with _ h0 hq
      exact hq.1.ne' h0
    rw [← Measure.restrict_apply_univ]
    exact measure_eq_zero_iff_ae_notMem.2 (hae_false.mono fun _ h _ ↦ h)
  -- Every point with positive `r` and `Z` lies in `H n` for some `n`, so `Spos` is `Q`-null.
  have hrZ_pos : ∀ᵐ z ∂P, 0 < r z ∧ 0 < Z z := by
    have hZ_pos : ∀ᵐ z ∂P, 0 < Z z :=
      hμνR.ae_le (ae_rnDeriv_pos_of_forall_klDiv_le hRμν hμνR hγ hKL hmin)
    have hr_pos : ∀ᵐ z ∂P, 0 < r z := by
      filter_upwards [hμνR.ae_le (Measure.rnDeriv_pos hRμν), Measure.rnDeriv_lt_top R P]
        with _ hpos hlt using ENNReal.toReal_pos hpos.ne' hlt.ne
    exact hr_pos.and hZ_pos
  have hex_H : ∀ᵐ z ∂P, ∃ n, z ∈ H n := by
    filter_upwards [hrZ_pos] with z ⟨hrz, hZz⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (max (max (r z)⁻¹ (r z)) (max (Z z)⁻¹ (Z z)))
    have hn1 : max (max (r z)⁻¹ (r z)) (max (Z z)⁻¹ (Z z)) ≤ (n : ℝ) + 1 :=
      hn.trans (by linarith)
    refine ⟨n, ?_, ((le_max_right _ _).trans (le_max_left _ _)).trans hn1, ?_,
      ((le_max_right _ _).trans (le_max_right _ _)).trans hn1⟩
    · rw [inv_le_comm₀ (by positivity) hrz]
      exact ((le_max_left _ _).trans (le_max_left _ _)).trans hn1
    · rw [inv_le_comm₀ (by positivity) hZz]
      exact ((le_max_left _ _).trans (le_max_right _ _)).trans hn1
  have hH_mono : Monotone H := fun m n hmn _ hz ↦ by
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    exact ⟨(inv_anti₀ (by positivity) hmn').trans hz.1, hz.2.1.trans hmn',
      (inv_anti₀ (by positivity) hmn').trans hz.2.2.1, hz.2.2.2.trans hmn'⟩
  have hQ_allH : ∀ᵐ q ∂Q, ∃ n,
      q.1 ∈ H n ∧ q.2 ∈ H n ∧ (crossSwapEquiv q).1 ∈ H n ∧ (crossSwapEquiv q).2 ∈ H n := by
    have h12 : ∀ᵐ q ∂Q, (∃ n, q.1 ∈ H n) ∧ (∃ n, q.2 ∈ H n) :=
      (ae_of_ae_fst hex_H).and (ae_of_ae_snd hex_H)
    have h34 : ∀ᵐ q ∂Q, (∃ n, (crossSwapEquiv q).1 ∈ H n) ∧ (∃ n, (crossSwapEquiv q).2 ∈ H n) :=
      measurePreserving_crossSwapEquiv.quasiMeasurePreserving.ae h12
    filter_upwards [h12, h34] with _ ⟨⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩ ⟨⟨n₃, h₃⟩, ⟨n₄, h₄⟩⟩
    exact ⟨max (max n₁ n₂) (max n₃ n₄),
      hH_mono (by omega) h₁, hH_mono (by omega) h₂,
      hH_mono (by omega) h₃, hH_mono (by omega) h₄⟩
  have hQ_unionA : ∀ᵐ q ∂Q, q ∉ ⋃ n, A n :=
    measure_eq_zero_iff_ae_notMem.1 (measure_iUnion_null_iff.2 hQA)
  filter_upwards [hQ_allH, hQ_unionA] with _ ⟨n, hn⟩ hnot
  exact not_lt.1 fun hpos ↦ hnot (mem_iUnion.2 ⟨n, hpos, hn⟩)

end MinimizerDensity

/-! ### Existence, uniqueness, and integrability of Schrödinger potentials -/

/-- **Schrödinger potentials.** Let `μ` be a finite source measure and `R` a finite reference
measure on `X × Y` mutually absolutely continuous with respect to `μ ⊗ ν`. If `γ` is a coupling of
`μ` and `ν` with `klDiv γ R ≠ ∞` that minimizes `klDiv · R`, then there are measurable real
potentials `φ` on `X` and `ψ` on `Y` such that `dγ / dR (x, y) = exp (φ x + ψ y)` `R`-almost
everywhere, and any other measurable pair giving this density differs from `(φ, ψ)` by `(a, -a)`
`μ`- and `ν`-almost everywhere, for one real constant `a`. -/
theorem exists_rnDeriv_eq_exp_add_of_isCoupling_of_forall_klDiv_le
    [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) (hμνR : μ.prod ν ≪ R)
    (hγ : IsCoupling γ μ ν) (hKL : klDiv γ R ≠ ∞)
    (hmin : ∀ γ', IsCoupling γ' μ ν → klDiv γ R ≤ klDiv γ' R) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), Measurable φ ∧ Measurable ψ ∧
      γ.rnDeriv R =ᵐ[R] (fun z ↦ ENNReal.ofReal (exp (φ z.1 + ψ z.2))) ∧
      ∀ (φ' : X → ℝ) (ψ' : Y → ℝ), Measurable φ' → Measurable ψ' →
        γ.rnDeriv R =ᵐ[R] (fun z ↦ ENNReal.ofReal (exp (φ' z.1 + ψ' z.2))) →
        ∃ a : ℝ, φ' =ᵐ[μ] (fun x ↦ φ x + a) ∧ ψ' =ᵐ[ν] (fun y ↦ ψ y - a) := by
  by_cases hμ : μ = 0
  · have hν : ν = 0 := by
      rw [← Measure.measure_univ_eq_zero, ← hγ.measure_univ_eq, hμ]
      simp
    subst hμ hν
    have hR0 : R = 0 := Measure.absolutelyContinuous_zero_iff.1 (by simpa using hRμν)
    subst hR0
    exact ⟨0, 0, measurable_const, measurable_const, by simp [Filter.EventuallyEq],
      fun _ _ _ _ _ ↦ ⟨0, by simp [Filter.EventuallyEq]⟩⟩
  have := hγ.isFiniteMeasure
  have : IsFiniteMeasure ν := ⟨by rw [← hγ.measure_univ_eq]; exact measure_lt_top μ univ⟩
  have hν : ν ≠ 0 := by
    rwa [Ne, ← Measure.measure_univ_eq_zero, ← hγ.measure_univ_eq, Measure.measure_univ_eq_zero]
  set P := μ.prod ν
  have hP : P ≠ 0 := by
    rw [Ne, ← Measure.measure_univ_eq_zero, ← univ_prod_univ, Measure.prod_prod, mul_eq_zero]
    push Not
    exact ⟨Measure.measure_univ_ne_zero.2 hμ, Measure.measure_univ_ne_zero.2 hν⟩
  set f : X × Y → ℝ := fun z ↦ log (γ.rnDeriv R z).toReal
  have hf_meas : Measurable f := by fun_prop
  have hle := ae_crossDiff_log_rnDeriv_nonpos_of_forall_klDiv_le hRμν hμνR hγ hKL hmin
  have hge := measurePreserving_crossSwapEquiv.quasiMeasurePreserving.ae hle
  have hsplit : ∀ᵐ q ∂P.prod P,
      f q.1 + f q.2 = f (q.1.1, q.2.2) + f (q.2.1, q.1.2) := by
    filter_upwards [hle, hge] with q h1 h2
    simp only [f, crossSwapEquiv_apply] at h1 h2 ⊢
    linarith
  have : (ae P).NeBot := ae_neBot.2 hP
  obtain ⟨z₀, hz₀⟩ := (Measure.ae_ae_of_ae_prod hsplit).exists
  set φ : X → ℝ := fun x ↦ f (x, z₀.2)
  set ψ : Y → ℝ := fun y ↦ f (z₀.1, y) - f z₀
  have hφ : Measurable φ := hf_meas.comp (measurable_id.prodMk measurable_const)
  have hψ : Measurable ψ := (hf_meas.comp (measurable_const.prodMk measurable_id)).sub_const _
  have hrn : γ.rnDeriv R =ᵐ[R] fun z ↦ ENNReal.ofReal (exp (φ z.1 + ψ z.2)) := by
    filter_upwards [hRμν.ae_le hz₀, ae_rnDeriv_pos_of_forall_klDiv_le hRμν hμνR hγ hKL hmin,
      Measure.rnDeriv_lt_top γ R] with z hz hpos hlt
    have hsum : φ z.1 + ψ z.2 = f z := by simp only [φ, ψ]; linarith
    rw [hsum, exp_log hpos, ENNReal.ofReal_toReal hlt.ne]
  refine ⟨φ, ψ, hφ, hψ, hrn, fun φ' ψ' hφ' hψ' hrn' ↦ ?_⟩
  have hwd : (R.withDensity fun z ↦ ENNReal.ofReal (exp (φ' z.1 + ψ' z.2))) =
      R.withDensity fun z ↦ ENNReal.ofReal (exp (φ z.1 + ψ z.2)) :=
    withDensity_congr_ae (hrn'.symm.trans hrn)
  exact exists_ae_eq_add_const_of_withDensity_exp_eq hμ hν hμνR hφ' hψ' hφ hψ hwd

/-- **Product density of the Schrödinger minimizer.** For a finite source measure `μ` and a finite
reference measure `R` mutually absolutely continuous with respect to `μ ⊗ ν`, a finite Schrödinger
value `schroedingerValue R μ ν ≠ ∞` is attained by a coupling of density `exp (φ(x) + ψ(y))`
against `R`, for measurable potentials `φ` and `ψ`. -/
theorem exists_isCoupling_eq_withDensity_exp_add_of_schroedingerValue_ne_top
    [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hRμν : R ≪ μ.prod ν) (hμνR : μ.prod ν ≪ R) (hfin : schroedingerValue R μ ν ≠ ∞) :
    ∃ π, IsCoupling π μ ν ∧ klDiv π R = schroedingerValue R μ ν ∧
      ∃ (φ : X → ℝ) (ψ : Y → ℝ), Measurable φ ∧ Measurable ψ ∧
        π = R.withDensity fun z ↦ ENNReal.ofReal (exp (φ z.1 + ψ z.2)) := by
  obtain ⟨π, hπ, hπval⟩ := exists_isCoupling_klDiv_eq_schroedingerValue hfin
  have := hπ.isFiniteMeasure
  have hKL : klDiv π R ≠ ∞ := hπval ▸ hfin
  obtain ⟨φ, ψ, hφ, hψ, hrn, -⟩ := exists_rnDeriv_eq_exp_add_of_isCoupling_of_forall_klDiv_le
    hRμν hμνR hπ hKL fun _ hγ' ↦ hπval.le.trans (schroedingerValue_le_klDiv hγ' R)
  refine ⟨π, hπ, hπval, φ, ψ, hφ, hψ, ?_⟩
  exact (Measure.withDensity_rnDeriv_eq π R (klDiv_ne_top_iff.1 hKL).1).symm.trans
    (withDensity_congr_ae hrn)

/-- **Integrability of the Schrödinger potentials.** Let `π` be a coupling of `μ` and `ν` of finite
relative entropy against `R` whose density against `R` is `exp (φ(x) + ψ(y))`, where `R ∼ μ ⊗ ν`
has integrable log-density `llr R (μ.prod ν)` against `μ.prod ν`. Then `φ ∈ L¹(μ)` and
`ψ ∈ L¹(ν)`. -/
theorem IsCoupling.integrable_of_eq_withDensity_exp_add
    [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hπ : IsCoupling π μ ν) (hRμν : R ≪ μ.prod ν) (hμνR : μ.prod ν ≪ R)
    (hllr : Integrable (llr R (μ.prod ν)) (μ.prod ν)) (hKL : klDiv π R ≠ ∞)
    (hφ : Measurable φ) (hψ : Measurable ψ)
    (hπR : π = R.withDensity fun z ↦ ENNReal.ofReal (exp (φ z.1 + ψ z.2))) :
    Integrable φ μ ∧ Integrable ψ ν := by
  by_cases hμ : μ = 0
  · have hν : ν = 0 := by
      rw [← Measure.measure_univ_eq_zero, ← hπ.measure_univ_eq, hμ]
      simp
    subst hμ hν
    exact ⟨integrable_zero_measure, integrable_zero_measure⟩
  have := hπ.isFiniteMeasure
  have : IsFiniteMeasure ν := ⟨by rw [← hπ.measure_univ_eq]; exact measure_lt_top μ univ⟩
  have hν : ν ≠ 0 := by
    rwa [Ne, ← Measure.measure_univ_eq_zero, ← hπ.measure_univ_eq, Measure.measure_univ_eq_zero]
  set P := μ.prod ν
  obtain ⟨hπR_ac, hllr_πR⟩ := klDiv_ne_top_iff.1 hKL
  -- First, `φ ⊕ ψ` equals `llr π R` `π`-almost everywhere, hence is `π`-integrable.
  have hllr_eq : llr π R =ᵐ[π] fun z ↦ φ z.1 + ψ z.2 := by
    have h := hπR_ac.ae_le (llr_withDensity_exp (R := R) (f := fun z ↦ φ z.1 + ψ z.2)
      (by fun_prop))
    rwa [← hπR] at h
  have hsum_π : Integrable (fun z ↦ φ z.1 + ψ z.2) π := (integrable_congr hllr_eq).1 hllr_πR
  -- Next, `exp (φ ⊕ ψ + llr R P)` is the `P`-density of `π`, hence `P`-integrable.
  have hπ_P : P.withDensity (fun z ↦ ENNReal.ofReal (exp (φ z.1 + ψ z.2 + llr R P z))) = π := by
    have hR_P : P.withDensity (R.rnDeriv P) = R := Measure.withDensity_rnDeriv_eq R P hRμν
    conv_rhs => rw [hπR, ← hR_P]
    rw [← withDensity_mul _ (Measure.measurable_rnDeriv R P) (by fun_prop)]
    refine withDensity_congr_ae ?_
    filter_upwards [hμνR.ae_le (Measure.rnDeriv_pos hRμν), Measure.rnDeriv_lt_top R P]
      with z hpos hlt
    have hrpos : 0 < (R.rnDeriv P z).toReal := ENNReal.toReal_pos hpos.ne' hlt.ne
    rw [Pi.mul_apply, exp_add, ENNReal.ofReal_mul (exp_pos _).le, llr_def, exp_log hrpos,
      ENNReal.ofReal_toReal hlt.ne, mul_comm]
  have hexp_int : Integrable (fun z ↦ exp (φ z.1 + ψ z.2 + llr R P z)) P := by
    refine (lintegral_ofReal_ne_top_iff_integrable
      (f := fun z ↦ exp (φ z.1 + ψ z.2 + llr R P z))
      (((hφ.comp measurable_fst).add (hψ.comp measurable_snd)).add
        (measurable_llr R P)).exp.aestronglyMeasurable
      (ae_of_all _ fun _ ↦ (exp_pos _).le)).1 ?_
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, hπ_P]
    exact measure_ne_top π univ
  have hpos_int : Integrable (fun z ↦ max (φ z.1 + ψ z.2) 0) P := by
    refine (hexp_int.add hllr.abs).mono'
      (((hφ.comp measurable_fst).add (hψ.comp measurable_snd)).max
        measurable_const).aestronglyMeasurable
      (ae_of_all _ fun z ↦ ?_)
    simp only [Pi.add_apply]
    have hnn : 0 ≤ max (φ z.1 + ψ z.2) 0 := le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    rcases le_total (φ z.1 + ψ z.2) 0 with hle | hge
    · rw [max_eq_right hle]
      exact add_nonneg (exp_pos _).le (abs_nonneg _)
    · rw [max_eq_left hge]
      linarith [add_one_le_exp (φ z.1 + ψ z.2 + llr R P z), neg_le_abs (llr R P z)]
  -- Fubini slices give integrable upper bounds `φ ≤ U` and `ψ ≤ V`.
  have : (ae μ).NeBot := ae_neBot.2 hμ
  have : (ae ν).NeBot := ae_neBot.2 hν
  obtain ⟨y₀, hy₀⟩ := hpos_int.prod_left_ae.exists
  obtain ⟨x₀, hx₀⟩ := hpos_int.prod_right_ae.exists
  set U : X → ℝ := fun x ↦ max (φ x + ψ y₀) 0 - ψ y₀
  set V : Y → ℝ := fun y ↦ max (φ x₀ + ψ y) 0 - φ x₀
  have hU_int : Integrable U μ := hy₀.sub (integrable_const _)
  have hV_int : Integrable V ν := hx₀.sub (integrable_const _)
  have hφU (x : X) : φ x ≤ U x := by simp only [U]; linarith [le_max_left (φ x + ψ y₀) 0]
  have hψV (y : Y) : ψ y ≤ V y := by simp only [V]; linarith [le_max_left (φ x₀ + ψ y) 0]
  have hdom : Integrable (fun z : X × Y ↦ |U z.1| + |V z.2| + |φ z.1 + ψ z.2|) π :=
    (hπ.integrable_add_split hU_int.abs hV_int.abs).add hsum_π.abs
  refine ⟨(hπ.measurePreserving_fst.integrable_comp hφ.aestronglyMeasurable).1 <|
      hdom.mono' (hφ.comp measurable_fst).aestronglyMeasurable <| ae_of_all _ fun z ↦ ?_,
    (hπ.measurePreserving_snd.integrable_comp hψ.aestronglyMeasurable).1 <|
      hdom.mono' (hψ.comp measurable_snd).aestronglyMeasurable <| ae_of_all _ fun z ↦ ?_⟩
  · simp only [Function.comp_apply, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hψV z.2, le_abs_self (V z.2), abs_nonneg (U z.1),
        neg_abs_le (φ z.1 + ψ z.2)],
      by linarith [hφU z.1, le_abs_self (U z.1), abs_nonneg (V z.2), abs_nonneg (φ z.1 + ψ z.2)]⟩
  · simp only [Function.comp_apply, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hφU z.1, le_abs_self (U z.1), abs_nonneg (V z.2),
        neg_abs_le (φ z.1 + ψ z.2)],
      by linarith [hψV z.2, le_abs_self (V z.2), abs_nonneg (U z.1), abs_nonneg (φ z.1 + ψ z.2)]⟩

/-! ### Gibbs density and strong entropic duality beyond bounded costs -/

section EntropicDuality

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Rescales Schrödinger potentials against the tilted Gibbs measure into entropic Kantorovich
potentials against `μ ⊗ ν`. -/
private theorem withDensity_tilted_exp_add_eq_withDensity_entropicGibbsFactor
    (hc : AEMeasurable c (μ.prod ν)) (hc_top : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞) (hε : ε ≠ 0)
    {φ₀ : X → ℝ} {ψ₀ : Y → ℝ} (hφ₀ : Measurable φ₀) (hψ₀ : Measurable ψ₀) :
    let Z := ∫ z, exp (-((c z).toReal / ε)) ∂μ.prod ν
    ((μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)).withDensity
        (fun z ↦ ENNReal.ofReal (exp (φ₀ z.1 + ψ₀ z.2))) =
      (μ.prod ν).withDensity fun z ↦ ENNReal.ofReal
        (entropicGibbsFactor c ε (fun x ↦ ε * (φ₀ x - log Z)) (fun y ↦ ε * ψ₀ y) z) := by
  intro Z
  have hexp : Integrable (fun z ↦ exp (-((c z).toReal / ε))) (μ.prod ν) :=
    MeasureTheory.integrable_exp_neg_of_ae_nonneg (hc.ennreal_toReal.div_const _) <|
      ae_of_all _ fun _ ↦ by positivity
  have hZ : 0 < Z := integral_exp_pos hexp
  have hε' : (ε : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hε
  rw [Measure.tilted, ← withDensity_mul₀ (by fun_prop) (by fun_prop)]
  refine withDensity_congr_ae ?_
  filter_upwards [hc_top] with z hz
  rw [Pi.mul_apply, entropicGibbsFactor_of_ne_top hz,
    ← ENNReal.ofReal_mul (div_nonneg (exp_pos _).le hZ.le)]
  congr 1
  have hexponent : ((ε : ℝ) * (φ₀ z.1 - log Z) + (ε : ℝ) * ψ₀ z.2 - (c z).toReal) / ε =
      -((c z).toReal / ε) + (φ₀ z.1 + ψ₀ z.2) - log Z := by field_simp; ring
  rw [hexponent, exp_sub, exp_log hZ, exp_add (-((c z).toReal / ε)) (φ₀ z.1 + ψ₀ z.2),
    div_mul_eq_mul_div]

/-- **Gibbs density of the entropic optimal plan.** For probability measures `μ` and `ν`, a
positive temperature `ε`, and an almost everywhere measurable cost `c` that is finite `μ ⊗ ν`-almost
everywhere with `entropicTransportCost c ε μ ν ≠ ∞`, there exist an optimal coupling `π` and
measurable potentials `φ` and `ψ` such that `π` has `entropicGibbsFactor c ε φ ψ` as density
against `μ ⊗ ν`. -/
theorem exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost_of_ne_top
    (hc : AEMeasurable c (μ.prod ν)) (hc_top : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞)
    (hfin : entropicTransportCost c ε μ ν ≠ ∞) (hε : ε ≠ 0) :
    ∃ π, IsCoupling π μ ν ∧
      ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) = entropicTransportCost c ε μ ν ∧
      ∃ (φ : X → ℝ) (ψ : Y → ℝ), Measurable φ ∧ Measurable ψ ∧
        π = (μ.prod ν).withDensity fun z ↦ ENNReal.ofReal (entropicGibbsFactor c ε φ ψ z) := by
  have hexp : Integrable (fun z ↦ exp (-((c z).toReal / ε))) (μ.prod ν) :=
    MeasureTheory.integrable_exp_neg_of_ae_nonneg (hc.ennreal_toReal.div_const _) <|
      ae_of_all _ fun _ ↦ by positivity
  set R := (μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)
  have : IsProbabilityMeasure R := isProbabilityMeasure_tilted hexp
  have hS_ne_top : schroedingerValue R μ ν ≠ ∞ := fun hS ↦ hfin <| by
    rw [entropicTransportCost_eq_mul_schroedingerValue_add hc hc_top hε, hS,
      ENNReal.mul_top (ENNReal.coe_ne_zero.2 hε), top_add]
  obtain ⟨π, hπ, hπR, φ₀, ψ₀, hφ₀, hψ₀, hπ_wd⟩ :=
    exists_isCoupling_eq_withDensity_exp_add_of_schroedingerValue_ne_top
      (tilted_absolutelyContinuous _ _) (absolutelyContinuous_tilted hexp) hS_ne_top
  refine ⟨π, hπ, (lintegral_add_mul_klDiv_eq_entropicTransportCost_iff hπ hc hc_top hε).2 hπR,
    _, _, (hφ₀.sub_const _).const_mul _, hψ₀.const_mul _,
    hπ_wd.trans (withDensity_tilted_exp_add_eq_withDensity_entropicGibbsFactor hc hc_top hε hφ₀
      hψ₀)⟩

/-- **Strong entropic duality for an `L¹` cost, with attainment.** For probability measures, a
positive temperature, and an almost everywhere measurable cost of finite integral against `μ ⊗ ν`,
the dual problem is attained by integrable measurable potentials with integrable Gibbs factor, with
value the regularised transport cost. -/
theorem exists_entropicDualValue_eq_toReal_entropicTransportCost_of_lintegral_ne_top
    (hc : AEMeasurable c (μ.prod ν)) (hc_int : ∫⁻ z, c z ∂μ.prod ν ≠ ∞) (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), Measurable φ ∧ Measurable ψ ∧
      Integrable φ μ ∧ Integrable ψ ν ∧
      Integrable (entropicGibbsFactor c ε φ ψ) (μ.prod ν) ∧
      entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
  have hc_top : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞ := (ae_lt_top' hc hc_int).mono fun _ hz ↦ hz.ne
  have hfin : entropicTransportCost c ε μ ν ≠ ∞ :=
    entropicTransportCost_ne_top_of_lintegral_ne_top hc_int ε
  have hexp : Integrable (fun z ↦ exp (-((c z).toReal / ε))) (μ.prod ν) :=
    MeasureTheory.integrable_exp_neg_of_ae_nonneg (hc.ennreal_toReal.div_const _) <|
      ae_of_all _ fun _ ↦ by positivity
  set R := (μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)
  have : IsProbabilityMeasure R := isProbabilityMeasure_tilted hexp
  have hRμν : R ≪ μ.prod ν := tilted_absolutelyContinuous _ _
  have hμνR : μ.prod ν ≪ R := absolutelyContinuous_tilted hexp
  have hS_ne_top : schroedingerValue R μ ν ≠ ∞ := fun hS ↦ hfin <| by
    rw [entropicTransportCost_eq_mul_schroedingerValue_add hc hc_top hε, hS,
      ENNReal.mul_top (ENNReal.coe_ne_zero.2 hε), top_add]
  obtain ⟨π, hπ, hπR, φ₀, ψ₀, hφ₀, hψ₀, hπ_wd⟩ :=
    exists_isCoupling_eq_withDensity_exp_add_of_schroedingerValue_ne_top hRμν hμνR hS_ne_top
  set Z := ∫ z, exp (-((c z).toReal / ε)) ∂μ.prod ν
  have hZ : 0 < Z := integral_exp_pos hexp
  have hR_exp : R = (μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (exp (-((c z).toReal / ε) - log Z)) := by
    dsimp only [R]; rw [Measure.tilted]; congr 1; funext z; rw [exp_sub, exp_log hZ]
  have hllr_int : Integrable (llr R (μ.prod ν)) (μ.prod ν) := by
    have hllr_eq := llr_withDensity_exp (R := μ.prod ν)
      (f := fun z ↦ -((c z).toReal / ε) - log Z) ((hc.ennreal_toReal.div_const _).neg.sub_const _)
    rw [← hR_exp] at hllr_eq
    exact (integrable_congr hllr_eq).2 <|
      (((integrable_toReal_of_lintegral_ne_top hc hc_int).div_const _).neg).sub (integrable_const _)
  obtain ⟨hφ₀_int, hψ₀_int⟩ := hπ.integrable_of_eq_withDensity_exp_add hRμν hμνR hllr_int
    (hπR ▸ hS_ne_top) hφ₀ hψ₀ hπ_wd
  set φ : X → ℝ := fun x ↦ ε * (φ₀ x - log Z)
  set ψ : Y → ℝ := fun y ↦ ε * ψ₀ y
  have hφ_meas : Measurable φ := (hφ₀.sub_const _).const_mul _
  have hψ_meas : Measurable ψ := hψ₀.const_mul _
  have hφ_int : Integrable φ μ := (hφ₀_int.sub (integrable_const _)).const_mul _
  have hψ_int : Integrable ψ ν := hψ₀_int.const_mul _
  have hπ_gibbs : π = (μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (entropicGibbsFactor c ε φ ψ z) :=
    hπ_wd.trans (withDensity_tilted_exp_add_eq_withDensity_entropicGibbsFactor hc hc_top hε hφ₀ hψ₀)
  have := hπ.isProbabilityMeasure
  have hgibbs_aemeas : AEMeasurable (entropicGibbsFactor c ε φ ψ) (μ.prod ν) := by
    have hae : entropicGibbsFactor c ε φ ψ =ᵐ[μ.prod ν]
        fun z ↦ exp ((φ z.1 + ψ z.2 - (c z).toReal) / ε) :=
      hc_top.mono fun _ hz ↦ entropicGibbsFactor_of_ne_top hz
    exact AEMeasurable.congr
      ((((hφ_meas.comp measurable_fst).add (hψ_meas.comp measurable_snd)).aemeasurable.sub
        hc.ennreal_toReal).div_const _).exp hae.symm
  have hgibbs_int : Integrable (entropicGibbsFactor c ε φ ψ) (μ.prod ν) := by
    refine (lintegral_ofReal_ne_top_iff_integrable hgibbs_aemeas.aestronglyMeasurable
      (ae_of_all _ entropicGibbsFactor_nonneg)).1 ?_
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hπ_gibbs]
    exact measure_ne_top π univ
  have hopt : ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) = entropicTransportCost c ε μ ν :=
    (lintegral_add_mul_klDiv_eq_entropicTransportCost_iff hπ hc hc_top hε).2 hπR
  refine ⟨φ, ψ, hφ_meas, hψ_meas, hφ_int, hψ_int, hgibbs_int, ?_⟩
  rw [← hopt]
  exact (hπ.entropicDualValue_eq_toReal_lintegral_add_mul_klDiv_iff hc hε hφ_int hψ_int hgibbs_int
    (hopt ▸ hfin)).2 hπ_gibbs

/-- **Strong entropic duality for an `L¹` cost.** For probability measures, a positive temperature,
and an almost everywhere measurable cost of finite integral against `μ ⊗ ν`, the regularised
transport cost is the greatest entropic dual value of integrable potentials with integrable Gibbs
factor. -/
theorem isGreatest_entropicDualValue_integrable_of_lintegral_ne_top
    (hc : AEMeasurable c (μ.prod ν)) (hc_int : ∫⁻ z, c z ∂μ.prod ν ≠ ∞) (hε : ε ≠ 0) :
    IsGreatest {r : ℝ | ∃ (φ : X → ℝ) (ψ : Y → ℝ), Integrable φ μ ∧ Integrable ψ ν ∧
        Integrable (entropicGibbsFactor c ε φ ψ) (μ.prod ν) ∧
        entropicDualValue c ε μ ν φ ψ = r}
      (entropicTransportCost c ε μ ν).toReal := by
  obtain ⟨φ, ψ, _, _, hφ, hψ, hexp, hval⟩ :=
    exists_entropicDualValue_eq_toReal_entropicTransportCost_of_lintegral_ne_top hc hc_int hε
  refine ⟨⟨φ, ψ, hφ, hψ, hexp, hval⟩, ?_⟩
  rintro r ⟨φ', ψ', hφ', hψ', hexp', rfl⟩
  exact entropicDualValue_le_toReal_entropicTransportCost
    (entropicTransportCost_ne_top_of_lintegral_ne_top hc_int ε) hc hε hφ' hψ' hexp'

/-- **Uniqueness of the entropic dual maximisers.** For probability measures, a positive
temperature, and an almost everywhere measurable cost that is finite `μ ⊗ ν`-almost everywhere with
finite regularised transport cost, two pairs of integrable potentials with integrable Gibbs factors
whose entropic dual values both equal the regularised transport cost differ by one additive
constant, `μ`- and `ν`-almost everywhere. -/
theorem exists_ae_eq_add_const_of_entropicDualValue_eq_toReal_entropicTransportCost_of_ne_top
    (hc : AEMeasurable c (μ.prod ν)) (hc_top : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞)
    (hfin : entropicTransportCost c ε μ ν ≠ ∞) (hε : ε ≠ 0)
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν)
    (hexp : Integrable (entropicGibbsFactor c ε φ ψ) (μ.prod ν))
    (h : entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal)
    (hφ' : Integrable φ' μ) (hψ' : Integrable ψ' ν)
    (hexp' : Integrable (entropicGibbsFactor c ε φ' ψ') (μ.prod ν))
    (h' : entropicDualValue c ε μ ν φ' ψ' = (entropicTransportCost c ε μ ν).toReal) :
    ∃ a, φ =ᵐ[μ] (fun x ↦ φ' x + a) ∧ ψ =ᵐ[ν] (fun y ↦ ψ' y - a) := by
  obtain ⟨π, hπ, hopt, -⟩ :=
    exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost_of_ne_top hc hc_top hfin hε
  rw [← hopt] at h h'
  exact hπ.exists_ae_eq_add_const_of_entropicDualValue_eq (IsProbabilityMeasure.ne_zero μ)
    hc hc_top hε (hopt ▸ hfin) hφ hψ hexp h hφ' hψ' hexp' h'

end EntropicDuality

end TauCeti
