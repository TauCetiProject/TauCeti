/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Basic

import TauCeti.MeasureTheory.Integral.Bochner.WithDensity
import TauCeti.MeasureTheory.OptimalTransport.Entropic.CyclicPerturbation

/-!
# Existence, uniqueness, and integrability of Schrödinger potentials

Let `μ` and `ν` be finite measures on measurable spaces `X` and `Y`, and let `R` be a finite
reference measure on `X × Y` mutually absolutely continuous with respect to `μ.prod ν`. When a
coupling `γ` of `μ` and `ν` has finite relative entropy `klDiv γ R ≠ ∞` and minimizes `klDiv · R`
over all couplings, `TauCeti/MeasureTheory/OptimalTransport/Entropic/CyclicPerturbation.lean` shows
that `R ≪ γ` and that `llr γ R` satisfies four-point cyclic additivity `(μ ⊗ ν) ⊗ (μ ⊗ ν)`-almost
everywhere.

Fixing a Fubini slice `z₀` of that identity defines measurable potentials `φ(x) = llr γ R (x, z₀.2)`
and `ψ(y) = llr γ R (z₀.1, y) - llr γ R z₀` such that `dγ / dR (x, y) = exp (φ x + ψ y)` `R`-almost
everywhere, unique up to an opposite additive shift `(a, -a)`. When `llr R (μ.prod ν)` is
integrable against `μ.prod ν`, slicing the integrable positive part `max (φ ⊕ ψ) 0` yields upper
bounds in `L¹(μ)` and `L¹(ν)` that combine with `φ ⊕ ψ ∈ L¹(γ)` to prove `φ ∈ L¹(μ)` and
`ψ ∈ L¹(ν)`. Consequences for entropic optimal transport with `L¹` cost are deduced in
`TauCeti/MeasureTheory/OptimalTransport/Entropic/Duality.lean`.

## Main statements

* `TauCeti.exists_rnDeriv_eq_exp_add_of_isCoupling_of_forall_klDiv_le`: for finite `μ` and `R`
  mutually absolutely continuous with respect to `μ ⊗ ν`, any coupling `γ` with `klDiv γ R ≠ ∞`
  minimizing `klDiv · R` has density `exp (φ(x) + ψ(y))` against `R` for measurable real potentials
  `φ` and `ψ` unique up to `(a, -a)`.
* `TauCeti.exists_isCoupling_eq_withDensity_exp_add_of_schroedingerValue_ne_top`: when
  `schroedingerValue R μ ν ≠ ∞` and `R ∼ μ ⊗ ν`, the Schrödinger problem is attained by a coupling
  of product exponential density against `R`.
* `TauCeti.IsCoupling.integrable_and_integrable_of_eq_withDensity_exp_add`: if `R ∼ μ ⊗ ν` has
  `μ ⊗ ν`-integrable log-density `llr R (μ.prod ν)`, any finite-entropy coupling `π` with density
  `exp (φ(x) + ψ(y))` against `R` has `φ ∈ L¹(μ)` and `ψ ∈ L¹(ν)`.

## References

* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  Theorem 2.1.
* L. Rüschendorf and W. Thomsen, *Note on the Schrödinger equation and I-projections*, Statist.
  Probab. Lett. 17 (1993), 369–375.
* I. Csiszár, *I-divergence geometry of probability distributions and minimization problems*, Ann.
  Probab. 3 (1975), 146–158.
-/

public section

open MeasureTheory InformationTheory Set Filter
open Real (exp exp_pos exp_add add_one_le_exp)
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} {R γ π : Measure (X × Y)} {φ : X → ℝ} {ψ : Y → ℝ}

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
  · obtain rfl : ν = 0 := hγ.left_eq_zero_iff.1 hμ
    subst hμ
    obtain rfl : R = 0 := Measure.absolutelyContinuous_zero_iff.1 (by simpa using hRμν)
    exact ⟨0, 0, measurable_const, measurable_const, by simp [EventuallyEq],
      fun _ _ _ _ _ ↦ ⟨0, by simp [EventuallyEq]⟩⟩
  have := hγ.isFiniteMeasure
  have := hγ.isFiniteMeasure_right
  have hν : ν ≠ 0 := hγ.left_eq_zero_iff.not.1 hμ
  have hP : μ.prod ν ≠ 0 := by
    rw [Ne, ← Measure.measure_univ_eq_zero, ← univ_prod_univ, Measure.prod_prod, mul_eq_zero]
    exact not_or.2 ⟨Measure.measure_univ_ne_zero.2 hμ, Measure.measure_univ_ne_zero.2 hν⟩
  have : (ae (μ.prod ν)).NeBot := ae_neBot.2 hP
  obtain ⟨z₀, hz₀⟩ :=
    (Measure.ae_ae_of_ae_prod (hγ.ae_llr_add_llr_eq_of_forall_klDiv_le hRμν hμνR hKL hmin)).exists
  set φ : X → ℝ := fun x ↦ llr γ R (x, z₀.2)
  set ψ : Y → ℝ := fun y ↦ llr γ R (z₀.1, y) - llr γ R z₀
  have hφ : Measurable φ := (measurable_llr γ R).comp (measurable_id.prodMk measurable_const)
  have hψ : Measurable ψ :=
    ((measurable_llr γ R).comp (measurable_const.prodMk measurable_id)).sub_const _
  have hRγ : R ≪ γ := hγ.absolutelyContinuous_of_forall_klDiv_le hRμν hμνR hKL hmin
  have hrn : γ.rnDeriv R =ᵐ[R] fun z ↦ ENNReal.ofReal (exp (φ z.1 + ψ z.2)) := by
    filter_upwards [hRμν.ae_le hz₀, exp_llr_of_ac' γ R hRγ, Measure.rnDeriv_lt_top γ R]
      with z hz hexp hlt
    have hsum : φ z.1 + ψ z.2 = llr γ R z := by simp only [φ, ψ]; linarith
    rw [hsum, hexp, ENNReal.ofReal_toReal hlt.ne]
  refine ⟨φ, ψ, hφ, hψ, hrn, fun φ' ψ' hφ' hψ' hrn' ↦ ?_⟩
  exact exists_ae_eq_add_const_of_withDensity_exp_eq hμ hν hμνR hφ' hψ' hφ hψ
    (withDensity_congr_ae (hrn'.symm.trans hrn))

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
theorem IsCoupling.integrable_and_integrable_of_eq_withDensity_exp_add
    [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hπ : IsCoupling π μ ν) (hRμν : R ≪ μ.prod ν) (hμνR : μ.prod ν ≪ R)
    (hllr : Integrable (llr R (μ.prod ν)) (μ.prod ν)) (hKL : klDiv π R ≠ ∞)
    (hφ : Measurable φ) (hψ : Measurable ψ)
    (hπR : π = R.withDensity fun z ↦ ENNReal.ofReal (exp (φ z.1 + ψ z.2))) :
    Integrable φ μ ∧ Integrable ψ ν := by
  have := hπ.isFiniteMeasure
  have := hπ.isFiniteMeasure_right
  set P := μ.prod ν
  obtain ⟨hπR_ac, hllr_πR⟩ := klDiv_ne_top_iff.1 hKL
  have hllr_eq : llr π R =ᵐ[π] fun z ↦ φ z.1 + ψ z.2 := by
    have h := hπR_ac.ae_le (llr_withDensity_exp (R := R) (f := fun z ↦ φ z.1 + ψ z.2)
      (by fun_prop))
    rwa [← hπR] at h
  have hπ_P : P.withDensity (fun z ↦ ENNReal.ofReal (exp (φ z.1 + ψ z.2 + llr R P z))) = π := by
    have hR_P : P.withDensity (R.rnDeriv P) = R := Measure.withDensity_rnDeriv_eq R P hRμν
    conv_rhs => rw [hπR, ← hR_P]
    rw [← withDensity_mul _ (Measure.measurable_rnDeriv R P) (by fun_prop)]
    refine withDensity_congr_ae ?_
    filter_upwards [exp_llr_of_ac' R P hμνR, Measure.rnDeriv_lt_top R P] with z hexp hlt
    rw [Pi.mul_apply, exp_add, ENNReal.ofReal_mul (exp_pos _).le, hexp,
      ENNReal.ofReal_toReal hlt.ne, mul_comm]
  have hexp_int : Integrable (fun z ↦ exp (φ z.1 + ψ z.2 + llr R P z)) P :=
    MeasureTheory.integrable_of_eq_withDensity hπ_P.symm (by fun_prop)
      (ae_of_all _ fun _ ↦ (exp_pos _).le)
  refine hπ.integrable_and_integrable_of_integrable_add_of_integrable_max
    hφ.aestronglyMeasurable hψ.aestronglyMeasurable ((integrable_congr hllr_eq).1 hllr_πR) ?_
  refine (hexp_int.add hllr.abs).mono' (by fun_prop) (ae_of_all _ fun z ↦ ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (le_max_right (φ z.1 + ψ z.2) 0)]
  rcases le_total (φ z.1 + ψ z.2) 0 with hle | hge
  · rw [max_eq_right hle]
    exact add_nonneg (exp_pos _).le (abs_nonneg _)
  · rw [max_eq_left hge]
    linarith [add_one_le_exp (φ z.1 + ψ z.2 + llr R P z), neg_le_abs (llr R P z)]

end TauCeti
