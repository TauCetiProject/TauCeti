/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Asymptotics
public import TauCeti.Analysis.PDE.Vortex.Divisor.Basic
public import TauCeti.Analysis.PDE.Vortex.EulerLagrange
public import TauCeti.Analysis.PDE.Vortex.Minimizer
public import TauCeti.Analysis.PDE.Vortex.Regularity
public import TauCeti.Analysis.PDE.Vortex.Smoothness
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Existence of framed plane vortices with prescribed zeros

A smooth plane vortex with the degree-`m` end framing is a smooth field `x` on `ℂ` solving the
vortex equations `TauCeti.Vortex.equation x = 0` whose section satisfies
`α(z) (z / |z|)⁻ᵐ → 1` at infinity. Its zeros, counted with multiplicity, form a point of
`Sym ℂ m` (`TauCeti.Vortex.exists_sym_sectionValue_eq_pow_count_mul`), and two such vortices
differ by a smooth framed gauge exactly when their divisors agree
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_eq_iff`). This file proves Taubes's existence
theorem: every effective divisor of degree `m`, repeated points included, is the divisor of a
smooth framed vortex. Together with uniqueness this identifies the framed gauge orbits of smooth
framed degree-`m` vortices with `Sym ℂ m`; that identification, at every positive coupling, is
`TauCeti.Vortex.framedVortexModuliEquiv`.

Existence follows Taubes's variational argument, whose steps are already available.

1. For a polynomial `P` of degree `m ≥ 1` the reduced functional has a minimizer `u ∈ H¹(ℂ)`
   (`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`), which solves the reduced
   equation weakly (`TauCeti.Vortex.integral_inner_gradient_add_integral_mul_eq_zero`).
2. Weak solutions agree almost everywhere with `C²` classical solutions `w`
   (`TauCeti.Vortex.exists_contDiff_two_ae_eq_and_laplacian_eq`); Green's identity turns the
   classical equation back into a distributional one, so `w` is smooth
   (`TauCeti.Vortex.contDiffOn_of_forall_integral_laplacian_mul_eq_reduced`). Thus a minimizer has
   a smooth representative solving the reduced equation everywhere
   (`TauCeti.Vortex.exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le`).
3. Since `w ∈ L²(ℂ)`, it tends to zero at infinity
   (`TauCeti.Vortex.tendsto_cocompact_of_memLp_of_laplacian_eq`), so for monic `P` the field
   with amplitude `u₀ + w` and section `exp(u₀ + w) P`, `u₀` the background amplitude, is a vortex
   with the degree-`m` end framing
   (`TauCeti.Vortex.equation_amplitudeField_eq_zero_and_tendsto_sectionValue_of_memLp`,
   `TauCeti.Vortex.exists_contDiff_equation_amplitudeField_eq_zero_and_tendsto`).

For `D ∈ Sym ℂ m` take `P = ∏_{a ∈ D} (X - a)`; its section `exp(u₀ + w) P` has zero divisor
`D`. For `m = 0` the vacuum, with section `1` and zero connection, is the vortex.

## Main results

All in the namespace `TauCeti.Vortex`:

* `exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le`: a minimizer of
  Taubes's functional has a smooth representative solving the reduced vortex equation everywhere.
* `exists_contDiff_equation_amplitudeField_eq_zero_and_tendsto`: for monic `P` of degree `m ≥ 1`,
  there is a smooth square-integrable correction `w` for which the field reconstructed from
  `u₀ + w` and `P` is a smooth framed degree-`m` vortex.
* `exists_contDiff_memLp_laplacian_eq_reduced`: for a polynomial of positive degree, the reduced
  vortex equation has a smooth square-integrable solution tending to zero at infinity.
* `reducedSolution`: the smooth representative of the minimizer of Taubes's functional, a
  canonical such solution (`laplacian_reducedSolution`, `memLp_reducedSolution`,
  `tendsto_reducedSolution_cocompact`), characterized by `eq_reducedSolution_of_ae_eq`; for monic
  `P` it gives a framed vortex
  (`equation_amplitudeField_reducedSolution_eq_zero_and_tendsto_sectionValue`).
* `exists_contDiff_equation_eq_zero_isZeroMultiplicity`: every `D ∈ Sym ℂ m` is the zero divisor
  of a smooth vortex with the degree-`m` end framing.
* `framedVortexSubMulAction`: the smooth framed degree-`m` vortices of a coupling `c`, preserved
  by smooth framed gauges.
* `framedVortexDivisor`: the zero divisor of a smooth framed degree-`m` vortex, a point of
  `Sym ℂ m`, characterized by `framedVortexDivisor_eq_iff`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

open Complex Filter Set Topology TopologicalSpace InnerProductSpace Laplacian MeasureTheory
  Polynomial
open scoped ContDiff Distributions Gradient RealInnerProductSpace

namespace TauCeti.Vortex

/-! ### The reduced equation -/

section Minimizer

variable {P : Polynomial ℂ}

/-- **Smoothness of the minimizer of Taubes's functional.** Let `P` have degree at least one and
let `u ∈ H¹(ℂ)` minimize Taubes's functional `TauCeti.Vortex.sobolevReducedFunctional P`. Then `u`
agrees almost everywhere with a smooth function `w` that solves the reduced vortex equation

`Δw = (exp (2w) h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²`,    `h = ‖P‖² / (1 + ‖P‖²)`,

at every point of the plane. -/
theorem exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le
    (hm : 0 < P.natDegree) {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v) :
    ∃ w : ℂ → ℝ, ContDiff ℝ ∞ w ∧ W1p.value u =ᵐ[volume] w ∧
      ∀ z, Δ w z = (Real.exp (2 * w z) * backgroundWeight P.eval z - 1) / 8 +
        2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by
  -- The weak Euler–Lagrange equation, written with the coefficients `h` and `k` of the reduced
  -- equation `Δw = h (exp (2w) - 1) / 8 + k`.
  have hw : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ z, ⟪W1p.gradient u z, ∇ φ z⟫) +
        ∫ z, (backgroundWeight P.eval z * (Real.exp (2 * W1p.value u z) - 1) / 8 +
          backgroundSource P.eval z) * φ z = 0 := by
    intro φ hφ hφc
    rw [← integral_inner_gradient_add_integral_mul_eq_zero hm hu
      (hφ.of_le (by exact_mod_cast le_top)) hφc]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [backgroundSource_def, backgroundWeight_def, Polynomial.deriv]
    ring
  -- A `C²` classical solution, which is then smooth by the planar semilinear bootstrap.
  obtain ⟨w, hw2, huw, hΔ⟩ := exists_contDiff_two_ae_eq_and_laplacian_eq
    Complex.finrank_real_complex (contDiff_backgroundWeight
      ((P.differentiable.contDiff).restrict_scalars ℝ)) (contDiff_backgroundSource P.differentiable)
    hw
  have hΔ' : ∀ z, Δ w z = (Real.exp (2 * w z) * backgroundWeight P.eval z - 1) / 8 +
      2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := fun z => by
    rw [hΔ z, backgroundSource_def]
    ring
  have hws : ContDiffOn ℝ ∞ w (⊤ : Opens ℂ) :=
    contDiffOn_of_forall_integral_laplacian_mul_eq_reduced
      (fun z _ => P.differentiable.analyticAt z) hw2.continuous.continuousOn fun φ => by
        simpa only [smul_eq_mul, hΔ'] using
          hw2.contDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian (μ := volume) φ
  exact ⟨w, contDiffOn_univ.1 (by simpa using hws), huw, hΔ'⟩

end Minimizer

/-! ### The smooth solution of the reduced equation -/

section ReducedSolution

variable {P : Polynomial ℂ}

variable (P) in
/-- **The smooth solution of Taubes's reduced equation.** For a polynomial `P` of positive degree,
the smooth function that agrees almost everywhere with the minimizer
`TauCeti.Vortex.reducedMinimizer P` of Taubes's functional. It solves the reduced equation
`Δw = (exp (2w) h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²` at every point
(`TauCeti.Vortex.laplacian_reducedSolution`), and the field with amplitude `u₀ + w` and section
`P`, `u₀` the background amplitude, is a framed vortex when `P` is monic
(`TauCeti.Vortex.equation_amplitudeField_reducedSolution_eq_zero_and_tendsto_sectionValue`). It is
`0` for constant `P`. -/
def reducedSolution : ℂ → ℝ :=
  if hm : 0 < P.natDegree then
    (exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le hm
      (forall_sobolevReducedFunctional_reducedMinimizer_le hm)).choose
  else 0

private theorem reducedSolution_spec (hm : 0 < P.natDegree) :
    ContDiff ℝ ∞ (reducedSolution P) ∧
      W1p.value (reducedMinimizer P) =ᵐ[volume] reducedSolution P ∧
      ∀ z, Δ (reducedSolution P) z =
        (Real.exp (2 * reducedSolution P z) * backgroundWeight P.eval z - 1) / 8 +
          2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by
  rw [reducedSolution, dite_eq_left_of_eq_true (eq_true hm)]
  exact (exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le hm
    (forall_sobolevReducedFunctional_reducedMinimizer_le hm)).choose_spec

/-- The reduced solution of a constant polynomial is `0`. -/
theorem reducedSolution_eq_zero_of_natDegree_eq_zero (hm : P.natDegree = 0) :
    reducedSolution P = 0 := by
  simp [reducedSolution, hm]

variable (P) in
/-- The reduced solution is smooth. -/
theorem contDiff_reducedSolution : ContDiff ℝ ∞ (reducedSolution P) := by
  rcases Nat.eq_zero_or_pos P.natDegree with hm | hm
  · rw [reducedSolution_eq_zero_of_natDegree_eq_zero hm]
    exact contDiff_const
  · exact (reducedSolution_spec hm).1

/-- For `P` of positive degree, the reduced solution is a representative of the minimizer of
Taubes's functional. -/
theorem value_reducedMinimizer_ae_eq_reducedSolution (hm : 0 < P.natDegree) :
    W1p.value (reducedMinimizer P) =ᵐ[volume] reducedSolution P :=
  (reducedSolution_spec hm).2.1

/-- **The reduced equation.** For `P` of positive degree, the reduced solution `w` satisfies
`Δw = (exp (2w) h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²` everywhere, where `h = ‖P‖² / (1 + ‖P‖²)` is
`TauCeti.Vortex.backgroundWeight P.eval`. -/
theorem laplacian_reducedSolution (hm : 0 < P.natDegree) (z : ℂ) :
    Δ (reducedSolution P) z =
      (Real.exp (2 * reducedSolution P z) * backgroundWeight P.eval z - 1) / 8 +
        2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 :=
  (reducedSolution_spec hm).2.2 z

/-- The reduced solution is the only continuous representative of the minimizer of Taubes's
functional. -/
theorem eq_reducedSolution_of_ae_eq (hm : 0 < P.natDegree) {w : ℂ → ℝ} (hw : Continuous w)
    (h : W1p.value (reducedMinimizer P) =ᵐ[volume] w) : w = reducedSolution P :=
  (Continuous.ae_eq_iff_eq volume hw (contDiff_reducedSolution P).continuous).1
    (h.symm.trans (value_reducedMinimizer_ae_eq_reducedSolution hm))

variable (P) in
/-- The reduced solution is square integrable. -/
theorem memLp_reducedSolution : MemLp (reducedSolution P) 2 := by
  rcases Nat.eq_zero_or_pos P.natDegree with hm | hm
  · rw [reducedSolution_eq_zero_of_natDegree_eq_zero hm]
    exact MemLp.zero
  · exact (W1p.memLp_value (reducedMinimizer P)).ae_eq
      (by simpa using value_reducedMinimizer_ae_eq_reducedSolution hm)

variable (P) in
/-- The reduced solution tends to zero at infinity. -/
theorem tendsto_reducedSolution_cocompact :
    Tendsto (reducedSolution P) (cocompact ℂ) (𝓝 0) := by
  rcases Nat.eq_zero_or_pos P.natDegree with hm | hm
  · rw [reducedSolution_eq_zero_of_natDegree_eq_zero hm]
    exact tendsto_const_nhds
  · exact tendsto_cocompact_of_memLp_of_laplacian_eq
      (.of_forall fun _ ↦ ((contDiff_reducedSolution P).of_le (by simp)).contDiffAt)
      (memLp_reducedSolution P) one_le_two ENNReal.ofNat_ne_top
      (.of_forall (laplacian_reducedSolution hm))

/-- **The vortex of a monic polynomial.** For a monic polynomial `P` of degree `m ≥ 1`, the field
reconstructed from the amplitude `u₀ + w`, with `u₀` the background amplitude and `w` the reduced
solution, and the section `P` solves the vortex equations everywhere and has the degree-`m` end
framing `α(z) (z / ‖z‖)⁻ᵐ → 1` at infinity. -/
theorem equation_amplitudeField_reducedSolution_eq_zero_and_tendsto_sectionValue (hP : P.Monic)
    (hm : 0 < P.natDegree) :
    (∀ z, equation (amplitudeField
      (fun z ↦ backgroundAmplitude P.eval z + reducedSolution P z) P.eval) z = 0) ∧
      Tendsto (fun z ↦ sectionValue
        (amplitudeField (fun z ↦ backgroundAmplitude P.eval z + reducedSolution P z) P.eval) z *
          ((z / (‖z‖ : ℂ)) ^ P.natDegree)⁻¹) (cocompact ℂ) (𝓝 1) :=
  equation_amplitudeField_eq_zero_and_tendsto_sectionValue_of_memLp hP hm
    ((contDiff_reducedSolution P).of_le (by simp)) (memLp_reducedSolution P) one_le_two
    ENNReal.ofNat_ne_top (laplacian_reducedSolution hm)

/-- **Existence of framed plane vortices with prescribed zeros.** Let `P` be a monic complex
polynomial of degree `m ≥ 1` and let `u₀ = -log (1 + ‖P‖²) / 2` be its background amplitude. There
is a smooth square-integrable function `w` on the plane such that the field reconstructed from the
amplitude `u₀ + w` and the section `P` is smooth, solves the vortex equations everywhere, and has
the degree-`m` end framing `α(z) (z / ‖z‖)⁻ᵐ → 1` at infinity. Its section is `exp (u₀ + w) P`
(`TauCeti.Vortex.sectionValue_amplitudeField`), so its zeros are those of `P`, with
multiplicity. -/
theorem exists_contDiff_equation_amplitudeField_eq_zero_and_tendsto (hP : P.Monic)
    (hm : 0 < P.natDegree) :
    ∃ w : ℂ → ℝ, ContDiff ℝ ∞ w ∧ MemLp w 2 ∧
      ContDiff ℝ ∞ (amplitudeField (fun z ↦ backgroundAmplitude P.eval z + w z) P.eval) ∧
      (∀ z, equation (amplitudeField (fun z ↦ backgroundAmplitude P.eval z + w z) P.eval) z = 0) ∧
      Tendsto (fun z ↦ sectionValue
        (amplitudeField (fun z ↦ backgroundAmplitude P.eval z + w z) P.eval) z *
          ((z / (‖z‖ : ℂ)) ^ P.natDegree)⁻¹) (cocompact ℂ) (𝓝 1) :=
  ⟨reducedSolution P, contDiff_reducedSolution P, memLp_reducedSolution P,
    contDiff_amplitudeField (n := ⊤) ((contDiff_backgroundAmplitude
      ((P.differentiable.contDiff).restrict_scalars ℝ)).add (contDiff_reducedSolution P))
      ((P.differentiable.contDiff).restrict_scalars ℝ),
    equation_amplitudeField_reducedSolution_eq_zero_and_tendsto_sectionValue hP hm⟩

end ReducedSolution

/-- **Existence for the reduced vortex equation.** For a complex polynomial `P` of positive
degree there is a smooth function `w ∈ L²(ℂ)` with `w → 0` at infinity solving Taubes's reduced
equation `Δw = (exp (2w) h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²` at every point, where
`h = ‖P‖² / (1 + ‖P‖²)` is `TauCeti.Vortex.backgroundWeight P.eval`. -/
theorem exists_contDiff_memLp_laplacian_eq_reduced {P : ℂ[X]} (hm : 0 < P.natDegree) :
    ∃ w : ℂ → ℝ, ContDiff ℝ ∞ w ∧ MemLp w 2 ∧ Tendsto w (cocompact ℂ) (𝓝 0) ∧
      ∀ z, Δ w z = (Real.exp (2 * w z) * backgroundWeight P.eval z - 1) / 8 +
        2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 :=
  ⟨reducedSolution P, contDiff_reducedSolution P, memLp_reducedSolution P,
    tendsto_reducedSolution_cocompact P, laplacian_reducedSolution hm⟩

/-! ### Vortices with prescribed zeros -/

/-- **Existence of framed plane vortices with prescribed zeros** (Taubes). For every effective
divisor `D ∈ Sym ℂ m`, repeated points allowed, there is a smooth solution `x` of the vortex
equations on `ℂ` whose section has the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1` and
vanishes exactly at the points of `D`, to the order of their multiplicities. -/
theorem exists_contDiff_equation_eq_zero_isZeroMultiplicity {m : ℕ} (D : Sym ℂ m) :
    ∃ x : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ x ∧ (∀ z, equation x z = 0) ∧
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) ∧
      IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z := by
  set f : ℂ → ℂ := fun w ↦ ((D : Multiset ℂ).map fun a ↦ w - a).prod with hf
  set P : ℂ[X] := ((D : Multiset ℂ).map fun a ↦ X - C a).prod with hP
  have hPf : P.eval = f := funext fun w ↦ by simp [hP, hf, eval_multiset_prod, Multiset.map_map]
  have hdeg : P.natDegree = m := by
    rw [hP, natDegree_multiset_prod_X_sub_C_eq_card]
    exact D.property
  have hfc : ContDiff ℝ ∞ f := hPf ▸ (P.differentiable.contDiff).restrict_scalars ℝ
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- The vacuum: amplitude zero and section `1`.
    have hf1 : f = 1 := by
      rw [hf, Sym.eq_nil_of_card_zero D]
      funext _
      simp
    refine ⟨amplitudeField 0 f, contDiff_amplitudeField (n := ⊤) contDiff_const hfc,
      fun z ↦ ?_, ?_, isZeroMultiplicity_sectionValue_amplitudeField_prod_sub continuous_const _⟩
    · rw [equation_amplitudeField_eq_zero_iff (u := 0) (f := f) contDiffAt_const
        (hPf ▸ P.differentiable z)]
      simp [hf1, Pi.zero_def]
    · simp [sectionValue_amplitudeField, hf1]
  · -- A degree-`m` vortex from the solution of the reduced equation for `P`.
    have hm' : 0 < P.natDegree := by omega
    obtain ⟨w, hw, hwp, -, hΔ⟩ := exists_contDiff_memLp_laplacian_eq_reduced hm'
    obtain ⟨hsol, hfr⟩ := equation_amplitudeField_eq_zero_and_tendsto_sectionValue_of_memLp
      (monic_multiset_prod_of_monic _ _ fun a _ ↦ monic_X_sub_C a) hm'
      (hw.of_le (by simp)) hwp one_le_two ENNReal.ofNat_ne_top hΔ
    rw [hPf, hdeg] at hfr
    rw [hPf] at hsol
    have hu : ContDiff ℝ ∞ fun z ↦ backgroundAmplitude f z + w z :=
      (contDiff_backgroundAmplitude hfc).add hw
    exact ⟨_, contDiff_amplitudeField (n := ⊤) (hu.of_le (by simp)) hfc, hsol, hfr,
      isZeroMultiplicity_sectionValue_amplitudeField_prod_sub hu.continuous _⟩

/-! ### Framed vortices and their zero divisors -/

/-- **Smooth framed vortices of degree `m` and coupling `c`.** The smooth solutions `x` of
`∂bar_a α = 0`, `*iF_a = c (1 - |α|²) / 8` (`TauCeti.Vortex.coupledEquation c`) on `ℂ` whose
section has the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Coupling one is the normalized
vortex equation `TauCeti.Vortex.equation`. Smooth framed gauges preserve them. -/
def framedVortexSubMulAction (c : ℝ) (m : ℕ) :
    SubMulAction framedGaugeGroup (ℂ → EuclideanSpace ℝ (Fin 4)) where
  carrier := {x | ContDiff ℝ ∞ x ∧ (∀ z, coupledEquation c x z = 0) ∧
    Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)}
  smul_mem' u x := by
    rintro ⟨hx, hsol, hfr⟩
    obtain ⟨hu, hu1⟩ := (mem_framedGaugeGroup _).1 u.property
    simp only [Set.mem_ofPred_eq, framedGaugeGroup_smul]
    refine ⟨by simpa using contDiff_framedGaugeGroup_smul u hx, fun z ↦ ?_,
      tendsto_sectionValue_gaugeTransform hu1 hfr⟩
    rw [coupledEquation_gaugeTransform_eq_zero_iff c (hu.contDiffAt.of_le (by simp)) fun i ↦
      (((contDiff_piLp 2).1 hx i).differentiable (by simp)).differentiableAt]
    exact hsol z

/-- The members of `framedVortexSubMulAction c m` are the smooth framed degree-`m` vortices of
coupling `c`. -/
@[simp]
theorem mem_framedVortexSubMulAction {c : ℝ} {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)} :
    x ∈ framedVortexSubMulAction c m ↔ ContDiff ℝ ∞ x ∧ (∀ z, coupledEquation c x z = 0) ∧
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) :=
  Iff.rfl

variable {c : ℝ} {m : ℕ}

/-- The zeros of a smooth framed degree-`m` vortex of any coupling form an effective divisor of
degree `m`; only the holomorphicity rows are used. -/
private theorem exists_sym_isZeroMultiplicity_of_mem_framedVortexSubMulAction
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedVortexSubMulAction c m) :
    ∃ D : Sym ℂ m, IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z := by
  obtain ⟨hx, hsol, hfr⟩ := hx
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := (contDiff_piLp 2).1 hx i
  have hd (i : Fin 4) : Differentiable ℝ fun w ↦ x w i := (hxi i).differentiable (by simp)
  refine exists_sym_isZeroMultiplicity_sectionValue (k := ⊤) le_top (hxi 0) (hxi 1) (hd 2) (hd 3)
    (fun w ↦ ⟨?_, ?_⟩) hfr
  · simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) (hsol w)
  · simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 2) (hsol w)

/-- **The zero divisor of a smooth framed degree-`m` vortex** of coupling `c`, the point of
`Sym ℂ m` listing the zeros of its section with multiplicity. It is characterized by
`framedVortexDivisor_eq_iff`. -/
def framedVortexDivisor (x : framedVortexSubMulAction c m) : Sym ℂ m :=
  (exists_sym_isZeroMultiplicity_of_mem_framedVortexSubMulAction x.property).choose

/-- The section of a smooth framed vortex vanishes at the points of its divisor, to the order of
their multiplicities. -/
theorem isZeroMultiplicity_sectionValue_framedVortexDivisor (x : framedVortexSubMulAction c m) :
    IsZeroMultiplicity (sectionValue x) fun z ↦ (framedVortexDivisor x : Multiset ℂ).count z :=
  (exists_sym_isZeroMultiplicity_of_mem_framedVortexSubMulAction x.property).choose_spec

/-- **Characterization of the divisor.** The divisor of a smooth framed vortex is the unique
`D ∈ Sym ℂ m` whose counts are the zero multiplicities of its section. -/
theorem framedVortexDivisor_eq_iff {x : framedVortexSubMulAction c m} {D : Sym ℂ m} :
    framedVortexDivisor x = D ↔
      IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z := by
  refine ⟨fun h ↦ h ▸ isZeroMultiplicity_sectionValue_framedVortexDivisor x, fun h ↦ ?_⟩
  exact Sym.coe_injective <| Multiset.ext.2 fun z ↦
    congrFun ((isZeroMultiplicity_sectionValue_framedVortexDivisor x).unique h) z

/-- Smooth framed gauges do not change the divisor. -/
@[simp]
theorem framedVortexDivisor_smul (u : framedGaugeGroup) (x : framedVortexSubMulAction c m) :
    framedVortexDivisor (u • x) = framedVortexDivisor x := by
  rw [framedVortexDivisor_eq_iff, SubMulAction.val_smul]
  exact isZeroMultiplicity_sectionValue_framedGaugeGroup_smul
    (isZeroMultiplicity_sectionValue_framedVortexDivisor x) u

end TauCeti.Vortex
