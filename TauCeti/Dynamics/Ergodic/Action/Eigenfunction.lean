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

Let `ℝ` act jointly measurably on `X`, preserving a probability measure `μ` ergodically. A
measurable `f : X → ℂ` is an eigenfunction of frequency `a` when, for every `t`,
`f(t +ᵥ x) = exp(2πiat) f(x)` for almost every `x`. Its modulus is then almost invariant, hence
almost everywhere constant (`TauCeti.exists_ae_eq_const_norm_of_eigenfunction`), so `f` is in
`L²(μ)`, and its class lies in the eigenspace at angular frequency `2πa` of the Koopman group
(`TauCeti.toLp_mem_eigenspace_koopmanGroup`). This passes from measurable eigenfunctions to the
`L²` eigenvectors of the spectral theory of the Koopman group.

The first step is `ErgodicVAdd.ae_eq_const_of_forall_ae_eq_comp_vadd₀`: for an ergodic action, an
almost invariant function is almost everywhere constant.

## References

* M. Hochman, *Notes on ergodic theory* (2012), Chapter 6.
-/

public section

noncomputable section

open MeasureTheory Filter Function Set
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] [AddAction ℝ X] [MeasurableVAdd₂ ℝ X] {μ : Measure X}
  [ErgodicVAdd ℝ X μ]

omit [MeasurableVAdd₂ ℝ X] in
/-- **Eigenfunctions of an ergodic action have constant modulus.** If `f` is a measurable
eigenfunction of frequency `a`, `f(t +ᵥ x) = exp(2πiat) f(x)` almost everywhere for every `t`,
then `‖f‖` is almost everywhere constant. -/
theorem exists_ae_eq_const_norm_of_eigenfunction {f : X → ℂ} (hf : Measurable f) {a : ℝ}
    (heig : ∀ t : ℝ, (fun x => f (t +ᵥ x)) =ᵐ[μ]
      fun x => Complex.exp (2 * Real.pi * a * t * Complex.I) * f x) :
    ∃ c : ℝ, (fun x => ‖f x‖) =ᵐ[μ] const X c := by
  refine ErgodicVAdd.ae_eq_const_of_forall_ae_eq_comp_vadd₀ ℝ hf.norm.nullMeasurable fun t => ?_
  filter_upwards [heig t] with x hx
  simp only [comp_apply]
  rw [hx, norm_mul]
  simp only [show (2 * Real.pi * a * t * Complex.I) = ((2 * Real.pi * a * t : ℝ) : ℂ) * Complex.I
    by push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]

variable [IsFiniteMeasure μ]

omit [MeasurableVAdd₂ ℝ X] in
/-- A measurable eigenfunction of an ergodic action preserving a finite measure is in `L²`. -/
theorem memLp_two_of_eigenfunction {f : X → ℂ} (hf : Measurable f) {a : ℝ}
    (heig : ∀ t : ℝ, (fun x => f (t +ᵥ x)) =ᵐ[μ]
      fun x => Complex.exp (2 * Real.pi * a * t * Complex.I) * f x) :
    MemLp f 2 μ := by
  obtain ⟨c, hc⟩ := exists_ae_eq_const_norm_of_eigenfunction hf heig
  exact MemLp.of_bound hf.aestronglyMeasurable c (hc.mono fun x hx => hx.le)

/-- **Measurable eigenfunctions are Koopman eigenvectors.** For an ergodic action of `ℝ`
preserving a finite measure, the `L²` class of a measurable eigenfunction of frequency `a` lies in
the eigenspace at angular frequency `2πa` of the Koopman group. -/
theorem toLp_mem_eigenspace_koopmanGroup {f : X → ℂ} (hf : Measurable f) {a : ℝ}
    (heig : ∀ t : ℝ, (fun x => f (t +ᵥ x)) =ᵐ[μ]
      fun x => Complex.exp (2 * Real.pi * a * t * Complex.I) * f x) :
    (memLp_two_of_eigenfunction hf heig).toLp f ∈
      (koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top).eigenspace
        (koopmanGroup_isUnitary μ ℂ).isComplexLinear (2 * Real.pi * a) := by
  refine (Semigroups.StronglyContinuousGroup.mem_eigenspace_iff _ _ _ _).2 fun t => ?_
  have hF := memLp_two_of_eigenfunction hf heig
  refine (koopmanGroup_apply μ ℂ 2 ENNReal.ofNat_ne_top t (hF.toLp f)).trans (Lp.ext ?_)
  filter_upwards [Lp.coeFn_compMeasurePreserving (hF.toLp f) (measurePreserving_vadd t μ),
    Lp.coeFn_smul (Complex.exp ((2 * Real.pi * a : ℝ) * t * Complex.I)) (hF.toLp f),
    (measurePreserving_vadd t μ).quasiMeasurePreserving.ae_eq_comp hF.coeFn_toLp,
    hF.coeFn_toLp, heig t] with x h₁ h₂ h₃ h₄ h₅
  simp only [comp_apply] at h₁ h₃
  rw [h₁, h₂, h₃, Pi.smul_apply, h₄, smul_eq_mul, h₅]
  push_cast
  ring_nf

end TauCeti
