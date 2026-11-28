/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.Koopman
public import TauCeti.Analysis.Semigroups.Group.Eigenspace
public import Mathlib.Dynamics.Ergodic.Action.Basic
public import TauCeti.MeasureTheory.Group.ErgodicExtreme

/-!
# Measurable eigenfunctions of an ergodic action of `ℝ`

Let `ℝ` act jointly measurably on `X`, preserving a measure `μ`. A class `g` in complex `L²(μ)`
lies in the eigenspace at angular frequency `ω` of the Koopman group exactly when, for every `t`,
`g(t +ᵥ x) = exp(iωt) g(x)` for almost every `x` (`TauCeti.mem_eigenspace_koopmanGroup_iff`).

Now let the action be ergodic and `μ` finite. An a.e. strongly measurable `f : X → ℂ` is an
eigenfunction of frequency `a` when, for every `t`, `f(t +ᵥ x) = exp(2πiat) f(x)` for almost
every `x`. Its modulus is then almost invariant, hence almost everywhere constant
(`TauCeti.exists_ae_eq_const_norm_of_eigenfunction`), so `f` is in every `Lᵖ(μ)`
(`TauCeti.memLp_of_eigenfunction`), and its class lies in the eigenspace at angular frequency
`2πa` of the Koopman group (`TauCeti.toLp_mem_eigenspace_koopmanGroup`). This passes between
measurable eigenfunctions and the `L²` eigenvectors of the spectral theory of the Koopman group.

For `a ≠ 0` the factor `exp(2πiat)` is `-1` at `t = 1/(2a)`
(`TauCeti.exp_two_pi_mul_one_div_two_mul_mul_I_eq_neg_one`), so the equation there reads
`f(t +ᵥ x) = -f(x)`.

The constant-modulus step is `ErgodicVAdd.ae_eq_const_of_forall_ae_eq_comp_vadd₀`: for an
ergodic action, an almost invariant function is almost everywhere constant.

## References

* M. Hochman, *Notes on ergodic theory* (2012), Chapter 6.
-/

public section

noncomputable section

open MeasureTheory Filter Function Set
open scoped ENNReal

namespace TauCeti

/-- At `t = 1/(2a)` the factor `exp(2πiat)` of the eigenfunction equation of frequency `a ≠ 0`
is `-1`. -/
theorem exp_two_pi_mul_one_div_two_mul_mul_I_eq_neg_one {a : ℝ} (ha : a ≠ 0) :
    Complex.exp (2 * Real.pi * a * (1 / (2 * a) : ℝ) * Complex.I) = -1 := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha
  rw [show (2 * Real.pi * a * (1 / (2 * a) : ℝ) * Complex.I : ℂ) = Real.pi * Complex.I by
    push_cast; field_simp, Complex.exp_pi_mul_I]

variable {X : Type*} [MeasurableSpace X] [AddAction ℝ X] {μ : Measure X}

/-- **Koopman eigenvectors are a.e. eigenfunctions.** A class `g` in complex `L²(μ)` lies in the
eigenspace at angular frequency `ω` of the Koopman group if and only if, for every `t`,
`g(t +ᵥ x) = exp(iωt) g(x)` for almost every `x`. -/
theorem mem_eigenspace_koopmanGroup_iff [MeasurableVAdd₂ ℝ X] [SFinite μ]
    [VAddInvariantMeasure ℝ X μ] (ω : ℝ) (g : Lp ℂ 2 μ) :
    g ∈ (koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top).eigenspace
        (koopmanGroup_isUnitary μ ℂ).isComplexLinear ω ↔
      ∀ t : ℝ, (fun x => g (t +ᵥ x)) =ᵐ[μ] fun x => Complex.exp (ω * t * Complex.I) * g x := by
  refine (Semigroups.StronglyContinuousGroup.mem_eigenspace_iff _ _ _ _).trans
    (forall_congr' fun t => ?_)
  -- `eigenspace` sees `koopmanGroup` through the real structure of `Lp ℂ 2 μ` restricted from
  -- its complex one, while `koopmanGroup_apply` is stated for `Lp.instNormedSpace`. The two agree
  -- by unfolding but not at instance transparency, so `rw [koopmanGroup_apply]` fails;
  -- `Eq.congr_left` unifies them by unfolding.
  refine (Eq.congr_left (koopmanGroup_apply μ ℂ 2 ENNReal.ofNat_ne_top t g)).trans ?_
  rw [Lp.ext_iff, (Lp.coeFn_compMeasurePreserving g (measurePreserving_vadd t μ)).congr_left,
    (Lp.coeFn_smul (Complex.exp (ω * t * Complex.I)) g).congr_right]
  rfl

variable [ErgodicVAdd ℝ X μ]

/-- **Eigenfunctions of an ergodic action have constant modulus.** If `f` is an a.e. strongly
measurable eigenfunction of frequency `a`, `f(t +ᵥ x) = exp(2πiat) f(x)` almost everywhere for
every `t`, then `‖f‖` is almost everywhere constant. -/
theorem exists_ae_eq_const_norm_of_eigenfunction {f : X → ℂ} (hf : AEStronglyMeasurable f μ)
    {a : ℝ} (heig : ∀ t : ℝ, (fun x => f (t +ᵥ x)) =ᵐ[μ]
      fun x => Complex.exp (2 * Real.pi * a * t * Complex.I) * f x) :
    ∃ c : ℝ, (fun x => ‖f x‖) =ᵐ[μ] const X c := by
  refine ErgodicVAdd.ae_eq_const_of_forall_ae_eq_comp_vadd₀ ℝ hf.norm.aemeasurable.nullMeasurable
    fun t => ?_
  filter_upwards [heig t] with x hx
  simp only [comp_apply]
  rw [hx, norm_mul]
  simp only [show (2 * Real.pi * a * t * Complex.I) = ((2 * Real.pi * a * t : ℝ) : ℂ) * Complex.I
    by push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]

variable [IsFiniteMeasure μ]

/-- An a.e. strongly measurable eigenfunction of an ergodic action preserving a finite measure is
in `Lᵖ` for every `p`. -/
theorem memLp_of_eigenfunction (p : ℝ≥0∞) {f : X → ℂ} (hf : AEStronglyMeasurable f μ) {a : ℝ}
    (heig : ∀ t : ℝ, (fun x => f (t +ᵥ x)) =ᵐ[μ]
      fun x => Complex.exp (2 * Real.pi * a * t * Complex.I) * f x) :
    MemLp f p μ := by
  obtain ⟨c, hc⟩ := exists_ae_eq_const_norm_of_eigenfunction hf heig
  exact MemLp.of_bound hf c (hc.mono fun x hx => hx.le)

/-- **Measurable eigenfunctions are Koopman eigenvectors.** For an ergodic action of `ℝ`
preserving a finite measure, the `L²` class of an a.e. strongly measurable eigenfunction of
frequency `a` lies in the eigenspace at angular frequency `2πa` of the Koopman group. -/
theorem toLp_mem_eigenspace_koopmanGroup [MeasurableVAdd₂ ℝ X] {f : X → ℂ}
    (hf : AEStronglyMeasurable f μ) {a : ℝ}
    (heig : ∀ t : ℝ, (fun x => f (t +ᵥ x)) =ᵐ[μ]
      fun x => Complex.exp (2 * Real.pi * a * t * Complex.I) * f x) :
    (memLp_of_eigenfunction 2 hf heig).toLp f ∈
      (koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top).eigenspace
        (koopmanGroup_isUnitary μ ℂ).isComplexLinear (2 * Real.pi * a) := by
  have hF := memLp_of_eigenfunction 2 hf heig
  refine (mem_eigenspace_koopmanGroup_iff _ _).2 fun t => ?_
  filter_upwards [(measurePreserving_vadd t μ).quasiMeasurePreserving.ae_eq_comp hF.coeFn_toLp,
    hF.coeFn_toLp, heig t] with x h₁ h₂ h₃
  simp only [comp_apply] at h₁
  rw [h₁, h₂, h₃]
  push_cast
  ring_nf

end TauCeti
