/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ComplexGauge
public import TauCeti.Analysis.PDE.Vortex.LogVariation
public import TauCeti.Analysis.PDE.Vortex.PrincipalPart
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Algebra.Polynomial.HermiteInterpolation
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Analysis.PDE.Schrodinger.Stationary
import TauCeti.Analysis.PDE.Vortex.ExteriorEstimate
import TauCeti.Analysis.PDE.Vortex.ScalarEquation
import TauCeti.Analysis.Sobolev.BesselPotential.Basic

/-!
# The kernel of the gauge-fixed operator at a framed plane vortex

At a field `x = (a, α)`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.gaugeFixedOperator`) is the linearization of the vortex equations together with
the Coulomb gauge condition. This file identifies the space of `C²` square-integrable solutions
`y` of `L_x y = 0` with the real tangent space `ℂᵐ` of the divisor space `Sym^m ℂ`, following
Samols.

**The upper bound.** Let `x` be a field whose holomorphicity rows `∂bar_a α = 0` vanish, with
`|α| → 1` at infinity, and let the zeros of its section `α`, counted with multiplicity, form the
effective divisor `D`. Every real vector space of `C²` square-integrable solutions of
`L_x y = 0` has dimension at most `2 |D|`
(`TauCeti.Vortex.finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero`). For a vortex with the
degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1` the bound is `2m`
(`TauCeti.Vortex.finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow`). Only the
holomorphicity rows of the vortex equation are used. The last two rows of `L_x y = 0` are the
holomorphicity rows of the linearized equation, so the section variation decomposes as
`δα = α G + e^ν H` with `G` continuous and `H` entire, and the derivatives of `H` at the zeros of
`α` record the principal parts of `δα / α` (`TauCeti.Vortex.principalPartMap`). This real-linear
map to `ℂ^|D|` is injective (`TauCeti.Vortex.principalPartMap_injective`) as soon as every kernel
element with `δα = α η`, `η` of class `C²`, vanishes. That is the vanishing theorem
`TauCeti.Vortex.eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto`.

**Equality.** At a smooth vortex with the degree-`m` end framing, the kernel
`gaugeFixedKernel x` (`TauCeti.Vortex.gaugeFixedKernel`), of real dimension at most `2m` by
`TauCeti.Vortex.finrank_gaugeFixedKernel_le`, has real dimension exactly `2m`
(`TauCeti.Vortex.finrank_gaugeFixedKernel`), since every entire `H` is the holomorphic part of a
kernel element (`TauCeti.Vortex.exists_mem_gaugeFixedKernel_sectionValue_eq_mul_add_exp_mul`). Write
`α = e^ν f` with `f` entire (`TauCeti.Vortex.differentiable_exp_neg_mul_sectionValue`). Take a
cutoff `ρ` equal to one near the finitely many zeros of `α`, and let `y₀` be the compactly
supported smooth field with section `ρ e^ν H` and connection variation `2 i (∂bar ρ) H / f`. Off
the zeros of `α` it is the complexified gauge direction of `ρ H / f`
(`TauCeti.Vortex.complexGaugeDirection`), so the holomorphicity rows of `L_x y₀` vanish, and the
two remaining rows are a smooth compactly supported defect. The correction is the complexified
gauge direction of a smooth `h`, with `h` and `∇h` square integrable, solving
`Δh = P h + (defect)` with `P = |α|² / 4` (`TauCeti.exists_contDiff_laplacian_eq_mul_add`). The
principal parts of `y₀ + complexGaugeDirection x h` are the derivatives of `H`, and these can be
prescribed arbitrarily by Hermite interpolation
(`Polynomial.exists_degree_lt_eval_iterate_derivative_eq`).

These are statements about classical solutions; the Fredholm property of the Sobolev realization
of `L_x` and the vanishing of its cokernel are not treated here.

## Main results

* `TauCeti.Vortex.finiteDimensional_of_gaugeFixedOperator_eq_zero` and
  `TauCeti.Vortex.finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero`: a space of `C²`
  square-integrable kernel elements is finite dimensional, of dimension at most `2 |D|`.
* `TauCeti.Vortex.finiteDimensional_of_tendsto_sectionValue_mul_inv_pow` and
  `TauCeti.Vortex.finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow`: the same for a vortex
  framed in degree `m`, with bound `2m`.
* `TauCeti.Vortex.exists_mem_gaugeFixedKernel_sectionValue_eq_mul_add_exp_mul`: every entire
  function is the holomorphic part of a kernel element.
* `TauCeti.Vortex.finrank_gaugeFixedKernel`: the kernel at a framed degree-`m` vortex has real
  dimension `2m`.

## References

* E. J. Weinberg, *Multivortex solutions of the Ginzburg-Landau equations*, Phys. Rev. D 19
  (1979), 3008–3012 (the index `2 m`).
* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179, Section 3 (the zero
  modes through `η = δα / α` and the equation `Δη = |φ|² η`).
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Metric Set TemperedDistribution Topology
open scoped Laplacian ContDiff

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}
  {D : Multiset ℂ} {V : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4))}

/-! ### The upper bound -/

omit [μ.IsAddHaarMeasure] in
/-- A `C²` kernel element of `L_x` has `C²` components and satisfies the holomorphicity rows of
the linearized equation, which are the last two rows of `L_x y = 0`. -/
private theorem forall_mem_linearizedEquation_eq_zero
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    ∀ y ∈ V, ContDiff ℝ 2 (fun w ↦ y w 0) ∧ ContDiff ℝ 2 (fun w ↦ y w 1) ∧
      Differentiable ℝ (fun w ↦ y w 2) ∧ Differentiable ℝ (fun w ↦ y w 3) ∧
      ∀ w, linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0 := by
  intro y hy
  obtain ⟨hy, -, hker⟩ := hV y hy
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ y w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hy
  refine ⟨hi 0, hi 1, (hi 2).differentiable (by norm_num), (hi 3).differentiable (by norm_num),
    fun w ↦ ⟨?_, ?_⟩⟩
  · rw [← gaugeFixedOperator_apply_two, hker w, PiLp.zero_apply]
  · rw [← gaugeFixedOperator_apply_three, hker w, PiLp.zero_apply]

omit [μ.IsAddHaarMeasure] in
/-- The section variation of a `C²` kernel element of `L_x` decomposes as `δα = α G + e^ν H` with
`G` continuous and `H` entire. -/
private theorem exists_sectionValue_eq_mul_add_exp_mul_of_mem {ν : ℂ → ℂ}
    (hp : Differentiable ℝ fun w ↦ x w 2) (hq : Differentiable ℝ fun w ↦ x w 3)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ V) :
    ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := forall_mem_linearizedEquation_eq_zero hV y hy
  obtain ⟨G, hG, H, hH, hGH⟩ := exists_sectionValue_eq_mul_add_exp_mul (k := 2) (by norm_num)
    hp hq hhol hν hνeq h₁ h₂ h₃ h₄ h₅
  exact ⟨G, hG.continuous, H, hH, hGH⟩

/-- **The principal-part map on the kernel.** For a space `V` of `C²` square-integrable kernel
elements, the principal-part map `TauCeti.Vortex.principalPartMap` gives an injective real-linear
map from `V` to `ℂ^|D|`. -/
private theorem exists_injective_linearMap (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    ∃ Φ : V →ₗ[ℝ] Multiset.ToType D → ℂ, Function.Injective Φ := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hx
  have hp := (hi 2).differentiable (by norm_num)
  have hq := (hi 3).differentiable (by norm_num)
  have hlin := forall_mem_linearizedEquation_eq_zero hV
  -- An integrating factor `ν` with `∂bar ν = (b₂ - i b₁) / 2`.
  obtain ⟨ν, hν, hνeq⟩ :=
    exists_contDiff_conjWirtingerDeriv_apply_one_eq (by norm_num) (contDiff_connectionCoeff
      (hi 0) (hi 1))
  have hdec (y) (hy : y ∈ V) := exists_sectionValue_eq_mul_add_exp_mul_of_mem hp hq hhol
    (hν.differentiable (by norm_num)) hνeq hV hy
  exact ⟨principalPartMap hD hν.continuous hdec,
    principalPartMap_injective (k := 2) (by norm_num) (hi 0) (hi 1) hp hq hhol hD hν hνeq hlin hdec
      fun y hy η hη hyη ↦ eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
        (hx.of_le (by norm_num)) hhol hlim (hV y hy).1.continuous (hV y hy).2.1 (hV y hy).2.2 hη
        hyη⟩

/-- **Kernel elements of the gauge-fixed operator form a finite-dimensional space.** Let `x` be a
`C²` field with vanishing holomorphicity rows and `|α|² → 1` at infinity, whose section has zero
divisor `D`. Then every real vector space of `C²` square-integrable solutions of `L_x y = 0` is
finite dimensional. -/
theorem finiteDimensional_of_gaugeFixedOperator_eq_zero (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    FiniteDimensional ℝ V :=
  let ⟨Φ, hΦ⟩ := exists_injective_linearMap hx hhol hlim hD hV
  FiniteDimensional.of_injective Φ hΦ

/-- **The kernel of the gauge-fixed operator at a vortex has dimension at most `2 |D|`.** Let `x`
be a `C²` field with vanishing holomorphicity rows and `|α|² → 1` at infinity, whose section has
zero divisor `D`. Then every real vector space of `C²` square-integrable solutions of `L_x y = 0`
has dimension at most twice the degree of `D`. -/
theorem finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    Module.finrank ℝ V ≤ 2 * Multiset.card D := by
  obtain ⟨Φ, hΦ⟩ := exists_injective_linearMap hx hhol hlim hD hV
  refine (LinearMap.finrank_le_finrank_of_injective hΦ).trans_eq ?_
  rw [Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul,
    Finset.card_univ, Multiset.card_coe, mul_comm]

/-- **Kernel elements at a framed vortex form a finite-dimensional space.** At a `C²` field with
vanishing holomorphicity rows and the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`, every real
vector space of `C²` square-integrable solutions of `L_x y = 0` is finite dimensional. -/
theorem finiteDimensional_of_tendsto_sectionValue_mul_inv_pow {m : ℕ} (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    FiniteDimensional ℝ V := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hx
  exact finiteDimensional_of_forall_sectionValue_eq_mul_eq_zero (k := 2) (by norm_num) (hi 0)
    (hi 1) ((hi 2).differentiable (by norm_num)) ((hi 3).differentiable (by norm_num)) hhol hframe
    (forall_mem_linearizedEquation_eq_zero hV) fun y hy η hη hyη ↦
      eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
        (hx.of_le (by norm_num)) hhol (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe)
        (hV y hy).1.continuous (hV y hy).2.1 (hV y hy).2.2 hη hyη

/-- **The kernel of the gauge-fixed operator at a framed vortex has dimension at most `2m`.** At a
`C²` field with vanishing holomorphicity rows and the degree-`m` end framing
`α(z) (z / |z|)⁻ᵐ → 1`, every real vector space of `C²` square-integrable solutions of
`L_x y = 0` has dimension at most `2m`, the real dimension of the divisor space `Sym^m ℂ`. -/
theorem finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow {m : ℕ} (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    Module.finrank ℝ V ≤ 2 * m := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hx
  exact finrank_le_two_mul_of_forall_sectionValue_eq_mul_eq_zero (k := 2) (by norm_num) (hi 0)
    (hi 1) ((hi 2).differentiable (by norm_num)) ((hi 3).differentiable (by norm_num)) hhol hframe
    (forall_mem_linearizedEquation_eq_zero hV) fun y hy η hη hyη ↦
      eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
        (hx.of_le (by norm_num)) hhol (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe)
        (hV y hy).1.continuous (hV y hy).2.1 (hV y hy).2.2 hη hyη

/-! ### A compactly supported seed with prescribed holomorphic part -/

section Seed

/-- The quotient `w = H / f` of `H` by the holomorphic factor `f = e^(-ν) α` of the section. -/
private def seedQuotient (x : ℂ → EuclideanSpace ℝ (Fin 4)) (ν H : ℂ → ℂ) (z : ℂ) : ℂ :=
  H z / (exp (-ν z) * sectionValue x z)

/-- The seed field: section `ρ e^ν H`, and connection variation `2 i ∂bar ρ · w` with
`w = seedQuotient x ν H`, written in the real coordinates. Off the zeros of `α` it is the
complexified gauge direction of `ρ w`. -/
private def seedField (x : ℂ → EuclideanSpace ℝ (Fin 4)) (ρ : ℂ → ℝ) (ν H : ℂ → ℂ) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) :=
  !₂[-fderiv ℝ ρ z 1 * (seedQuotient x ν H z).im - fderiv ℝ ρ z I * (seedQuotient x ν H z).re,
    fderiv ℝ ρ z 1 * (seedQuotient x ν H z).re - fderiv ℝ ρ z I * (seedQuotient x ν H z).im,
    ((ρ z : ℂ) * exp (ν z) * H z).re / 2, ((ρ z : ℂ) * exp (ν z) * H z).im / 2]

variable {ρ : ℂ → ℝ} {ν H : ℂ → ℂ}

private theorem seedField_apply_zero (z : ℂ) : seedField x ρ ν H z 0 =
    -fderiv ℝ ρ z 1 * (seedQuotient x ν H z).im - fderiv ℝ ρ z I * (seedQuotient x ν H z).re :=
  rfl

private theorem seedField_apply_one (z : ℂ) : seedField x ρ ν H z 1 =
    fderiv ℝ ρ z 1 * (seedQuotient x ν H z).re - fderiv ℝ ρ z I * (seedQuotient x ν H z).im :=
  rfl

private theorem seedField_apply_two (z : ℂ) :
    seedField x ρ ν H z 2 = ((ρ z : ℂ) * exp (ν z) * H z).re / 2 :=
  rfl

private theorem seedField_apply_three (z : ℂ) :
    seedField x ρ ν H z 3 = ((ρ z : ℂ) * exp (ν z) * H z).im / 2 :=
  rfl

/-- The section of the seed field is `ρ e^ν H`. -/
private theorem sectionValue_seedField (z : ℂ) :
    sectionValue (seedField x ρ ν H) z = ρ z * exp (ν z) * H z := by
  rw [sectionValue_apply, seedField_apply_two, seedField_apply_three]
  push_cast
  linear_combination re_add_im ((ρ z : ℂ) * exp (ν z) * H z)

/-- Off the zeros of `α`, the seed field is the complexified gauge direction of `ρ w`,
`w = seedQuotient x ν H = H / (e^(-ν) α)`. -/
private theorem seedField_eventuallyEq (hρ : Differentiable ℝ ρ) (hH : Differentiable ℂ H)
    (hf : Differentiable ℂ fun w ↦ exp (-ν w) * sectionValue x w)
    (hαc : Continuous (sectionValue x)) {z : ℂ} (hz : sectionValue x z ≠ 0) :
    seedField x ρ ν H =ᶠ[𝓝 z]
      complexGaugeDirection x fun u ↦ (ρ u : ℂ) * seedQuotient x ν H u := by
  filter_upwards [hαc.continuousAt.eventually_ne hz] with u hu
  have hfu : exp (-ν u) * sectionValue x u ≠ 0 := mul_ne_zero (exp_ne_zero _) hu
  have hw : DifferentiableAt ℂ (seedQuotient x ν H) u := (hH u).div (hf u) hfu
  have hD : HasFDerivAt (fun u ↦ (ρ u : ℂ) * seedQuotient x ν H u)
      ((ρ u : ℂ) • (((1 : ℂ →L[ℂ] ℂ).smulRight (deriv (seedQuotient x ν H) u)).restrictScalars ℝ)
        + seedQuotient x ν H u • (ofRealCLM.comp (fderiv ℝ ρ u))) u :=
    (ofRealCLM.hasFDerivAt.comp u (hρ u).hasFDerivAt).mul
      (hw.hasDerivAt.hasFDerivAt.restrictScalars ℝ)
  -- The section part: `ρ w (p + i q) = ρ e^ν H / 2`.
  have key : (ρ u : ℂ) * exp (ν u) * H u =
      2 * ((ρ u : ℂ) * seedQuotient x ν H u * ((x u 2 : ℂ) + x u 3 * I)) := by
    have hα2 : (x u 2 : ℂ) + x u 3 * I = sectionValue x u / 2 := by
      rw [sectionValue_apply]
      ring
    rw [hα2, seedQuotient, exp_neg]
    field_simp
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, seedField_apply_zero, complexGaugeDirection_apply_zero,
      hD.fderiv, add_apply, smul_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul, one_mul,
      ContinuousLinearMap.comp_apply, ofRealCLM_apply, add_re, add_im, mul_re, mul_im, ofReal_re,
      ofReal_im, I_re, I_im]
    ring
  · simp only [Fin.mk_one, Fin.isValue, seedField_apply_one, complexGaugeDirection_apply_one,
      hD.fderiv, add_apply, smul_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul, one_mul,
      ContinuousLinearMap.comp_apply, ofRealCLM_apply, add_re, add_im, mul_re, mul_im, ofReal_re,
      ofReal_im, I_re, I_im]
    ring
  · simp only [Fin.reduceFinMk, Fin.isValue, seedField_apply_two, key,
      complexGaugeDirection_apply_two]
    simp
  · simp only [Fin.reduceFinMk, Fin.isValue, seedField_apply_three, key,
      complexGaugeDirection_apply_three]
    simp

/-- The quotient `w = H / (e^(-ν) α)` is smooth off the zeros of `α`. -/
private theorem contDiffAt_seedQuotient (hν : ContDiff ℝ ∞ ν) (hH : Differentiable ℂ H)
    (hα : ContDiff ℝ ∞ (sectionValue x)) {z : ℂ} (hz : sectionValue x z ≠ 0) :
    ContDiffAt ℝ ∞ (seedQuotient x ν H) z := by
  have hq : seedQuotient x ν H = fun u ↦ H u * (exp (-ν u) * sectionValue x u)⁻¹ :=
    funext fun u ↦ div_eq_mul_inv _ _
  rw [hq]
  exact (hH.contDiff.restrict_scalars ℝ).contDiffAt.mul
    (((Complex.contDiff_exp.comp hν.neg).mul hα).contDiffAt.inv (mul_ne_zero (exp_ne_zero _) hz))

/-- The seed field is smooth when `ρ` is locally one near every zero of `α`. -/
private theorem contDiff_seedField (hρ : ContDiff ℝ ∞ ρ) (hν : ContDiff ℝ ∞ ν)
    (hH : Differentiable ℂ H) (hα : ContDiff ℝ ∞ (sectionValue x))
    (hρ₁ : ∀ z, sectionValue x z = 0 → ρ =ᶠ[𝓝 z] 1) :
    ContDiff ℝ ∞ (seedField x ρ ν H) := by
  have hH' : ContDiff ℝ ∞ H := hH.contDiff.restrict_scalars ℝ
  have hdρ (v : ℂ) : ContDiff ℝ ∞ fun z ↦ fderiv ℝ ρ z v :=
    (hρ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hs : ContDiff ℝ ∞ fun z ↦ (ρ z : ℂ) * exp (ν z) * H z :=
    ((ofRealCLM.contDiff.comp hρ).mul (Complex.contDiff_exp.comp hν)).mul hH'
  -- A connection coordinate `a (∂₁ ρ) + b (∂₂ ρ)` with coefficients `a`, `b` smooth off the zeros.
  have hconn {a b : ℂ → ℝ} (ha : ∀ z, sectionValue x z ≠ 0 → ContDiffAt ℝ ∞ a z)
      (hb : ∀ z, sectionValue x z ≠ 0 → ContDiffAt ℝ ∞ b z) :
      ContDiff ℝ ∞ fun z ↦ fderiv ℝ ρ z 1 * a z + fderiv ℝ ρ z I * b z := by
    refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
    by_cases hz : sectionValue x z = 0
    · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [(hρ₁ z hz).eventuallyEq_nhds] with u hu
      simp [hu.fderiv_eq]
    · exact ((hdρ 1).contDiffAt.mul (ha z hz)).add ((hdρ I).contDiffAt.mul (hb z hz))
  have hw (z : ℂ) (hz : sectionValue x z ≠ 0) : ContDiffAt ℝ ∞ (seedQuotient x ν H) z :=
    contDiffAt_seedQuotient hν hH hα hz
  have hre (z : ℂ) (hz : sectionValue x z ≠ 0) :
      ContDiffAt ℝ ∞ (fun u ↦ (seedQuotient x ν H u).re) z :=
    reCLM.contDiff.contDiffAt.comp z (hw z hz)
  have him (z : ℂ) (hz : sectionValue x z ≠ 0) :
      ContDiffAt ℝ ∞ (fun u ↦ (seedQuotient x ν H u).im) z :=
    imCLM.contDiff.contDiffAt.comp z (hw z hz)
  refine contDiff_euclidean.mpr fun i ↦ ?_
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, seedField_apply_zero]
    convert hconn (fun z hz ↦ (him z hz).neg) (fun z hz ↦ (hre z hz).neg) using 2
    ring
  · simp only [Fin.mk_one, Fin.isValue, seedField_apply_one]
    convert hconn (fun z hz ↦ hre z hz) (fun z hz ↦ (him z hz).neg) using 2
    ring
  · simp only [Fin.reduceFinMk, Fin.isValue, seedField_apply_two]
    exact (reCLM.contDiff.comp hs).div_const 2
  · simp only [Fin.reduceFinMk, Fin.isValue, seedField_apply_three]
    exact (imCLM.contDiff.comp hs).div_const 2

/-- The seed field is supported in the support of `ρ`. -/
private theorem hasCompactSupport_seedField (hρc : HasCompactSupport ρ) :
    HasCompactSupport (seedField x ρ ν H) := by
  refine hρc.mono' fun u hu ↦ ?_
  by_contra hρu
  have h0 : ρ =ᶠ[𝓝 u] 0 := notMem_tsupport_iff_eventuallyEq.1 hρu
  have hd : fderiv ℝ ρ u = 0 := by
    rw [h0.fderiv_eq]
    exact fderiv_const_apply _
  apply hu
  ext i
  fin_cases i <;>
    simp [seedField_apply_zero, seedField_apply_one, seedField_apply_two, seedField_apply_three,
      hd, h0.self_of_nhds]

end Seed

/-- The holomorphicity rows of `L_x` vanish on the seed field at a vortex whose section has finitely
many zeros: off the zeros the seed is a complexified gauge direction, and `L_x` of the seed is
continuous. -/
private theorem gaugeFixedOperator_seedField_eq_zero {ρ : ℂ → ℝ} {ν H : ℂ → ℂ}
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hZ : {z | sectionValue x z = 0}.Finite) (hρ : ContDiff ℝ ∞ ρ)
    (hρ₁ : ∀ z, sectionValue x z = 0 → ρ =ᶠ[𝓝 z] 1) (hν : ContDiff ℝ ∞ ν)
    (hH : Differentiable ℂ H) (hf : Differentiable ℂ fun w ↦ exp (-ν w) * sectionValue x w)
    {i : Fin 4} (hi : i = 2 ∨ i = 3) (z : ℂ) :
    gaugeFixedOperator x (seedField x ρ ν H) z i = 0 := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.mp hx i
  have hα : ContDiff ℝ ∞ (sectionValue x) := contDiff_sectionValue (hxi 2) (hxi 3)
  have hL : Continuous fun z ↦ gaugeFixedOperator x (seedField x ρ ν H) z i :=
    (contDiff_euclidean.mp (contDiff_gaugeFixedOperator hx
      ((contDiff_seedField hρ hν hH hα hρ₁).of_le (by simp))) i).continuous
  have hdense : Dense {z | sectionValue x z ≠ 0} :=
    (dense_univ.sdiff_finite hZ).mono fun z hz ↦ by simpa using hz
  refine congrFun (Continuous.ext_on hdense hL continuous_const fun w hw ↦ ?_) z
  have hcd : ContDiffAt ℝ 2 (fun u ↦ (ρ u : ℂ) * seedQuotient x ν H u) w :=
    ((ofRealCLM.contDiff.comp hρ).contDiffAt.mul (contDiffAt_seedQuotient hν hH hα hw)).of_le
      (by simp)
  have hw' := gaugeFixedOperator_complexGaugeDirection (((hxi 2).differentiable (by simp)) w)
    (((hxi 3).differentiable (by simp)) w) hcd
  rw [← gaugeFixedOperator_congr_nhds x (seedField_eventuallyEq (hρ.differentiable (by simp)) hH
    hf hα.continuous hw)] at hw'
  rcases hi with rfl | rfl <;> simp [hw', hsol w]

section OfRealAddMulI

variable {h₁ h₂ : ℂ → ℝ}

/-- The complex function `h₁ + i h₂` is `Cⁿ` when the real functions `h₁` and `h₂` are. -/
private theorem contDiff_ofReal_add_mul_I {n : WithTop ℕ∞} (hh₁ : ContDiff ℝ n h₁)
    (hh₂ : ContDiff ℝ n h₂) : ContDiff ℝ n fun z ↦ (h₁ z : ℂ) + h₂ z * I :=
  (ofRealCLM.contDiff.comp hh₁).add ((ofRealCLM.contDiff.comp hh₂).mul contDiff_const)

/-- The derivative of `h₁ + i h₂` is `h₁' + i h₂'`. -/
private theorem fderiv_ofReal_add_mul_I_apply {z : ℂ} (hh₁ : DifferentiableAt ℝ h₁ z)
    (hh₂ : DifferentiableAt ℝ h₂ z) (v : ℂ) :
    fderiv ℝ (fun z ↦ (h₁ z : ℂ) + h₂ z * I) z v =
      (fderiv ℝ h₁ z v : ℂ) + fderiv ℝ h₂ z v * I := by
  have hd : HasFDerivAt (fun z ↦ (h₁ z : ℂ) + h₂ z * I) _ z :=
    (ofRealCLM.hasFDerivAt.comp z hh₁.hasFDerivAt).add
      ((ofRealCLM.hasFDerivAt.comp z hh₂.hasFDerivAt).mul_const I)
  rw [hd.fderiv]
  simp [mul_comm I]

/-- The Laplacian of `h₁ + i h₂` is `Δ h₁ + i Δ h₂`. -/
private theorem laplacian_ofReal_add_mul_I {z : ℂ} (hh₁ : ContDiffAt ℝ 2 h₁ z)
    (hh₂ : ContDiffAt ℝ 2 h₂ z) :
    Δ (fun z ↦ (h₁ z : ℂ) + h₂ z * I) z = (Δ h₁ z : ℂ) + Δ h₂ z * I := by
  have hsplit : (fun z ↦ (h₁ z : ℂ) + h₂ z * I) =
      (ofRealCLM ∘ h₁) + ((1 : ℝ →L[ℝ] ℝ).smulRight I ∘ h₂) := by
    funext w
    simp [Complex.real_smul]
  rw [hsplit, (hh₁.continuousLinearMap_comp ofRealCLM).laplacian_add
    (hh₂.continuousLinearMap_comp _), hh₁.laplacian_CLM_comp_left, hh₂.laplacian_CLM_comp_left]
  simp [Complex.real_smul]

end OfRealAddMulI

/-- The complexified gauge direction of `h₁ + i h₂`, for `C¹` functions `h₁`, `h₂` which are square
integrable with square-integrable derivatives, at a field with continuous section coordinates
bounded by one, is square integrable. -/
private theorem memLp_complexGaugeDirection {h₁ h₂ : ℂ → ℝ} (hx₂ : Continuous fun z ↦ x z 2)
    (hx₃ : Continuous fun z ↦ x z 3) (hxb : ∀ z, ‖x z 2‖ ≤ 1 ∧ ‖x z 3‖ ≤ 1)
    (hh₁ : ContDiff ℝ 1 h₁) (hS₁ : MemLp h₁ 2 volume) (hD₁ : MemLp (fderiv ℝ h₁) 2 volume)
    (hh₂ : ContDiff ℝ 1 h₂) (hS₂ : MemLp h₂ 2 volume) (hD₂ : MemLp (fderiv ℝ h₂) 2 volume) :
    MemLp (complexGaugeDirection x fun z ↦ (h₁ z : ℂ) + h₂ z * I) 2 volume := by
  have hfd (z v : ℂ) := fderiv_ofReal_add_mul_I_apply ((hh₁.differentiable one_ne_zero) z)
    ((hh₂.differentiable one_ne_zero) z) v
  have hd {f : ℂ → ℝ} (hD : MemLp (fderiv ℝ f) 2 volume) (v : ℂ) :
      MemLp (fun z ↦ fderiv ℝ f z v) 2 volume :=
    (ContinuousLinearMap.apply ℝ ℝ v).comp_memLp' hD
  have hmul {f : ℂ → ℝ} (hf : Continuous f) (hS : MemLp f 2 volume) {g : ℂ → ℝ}
      (hg : Continuous g) (hgb : ∀ z, ‖g z‖ ≤ 1) : MemLp (fun z ↦ f z * g z) 2 volume :=
    hS.of_le (hf.mul hg).aestronglyMeasurable
      (ae_of_all _ fun z ↦ by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hgb z))
  refine memLp_piLp_iff.2 fun i ↦ ?_
  fin_cases i
  · convert ((hd hD₂ 1).neg).sub (hd hD₁ I) using 1
    funext z
    simp [hfd]
  · convert (hd hD₁ 1).sub (hd hD₂ I) using 1
    funext z
    simp [hfd]
  · convert (hmul hh₁.continuous hS₁ hx₂ fun z ↦ (hxb z).1).sub
      (hmul hh₂.continuous hS₂ hx₃ fun z ↦ (hxb z).2) using 1
    funext z
    simp
  · convert (hmul hh₁.continuous hS₁ hx₃ fun z ↦ (hxb z).2).add
      (hmul hh₂.continuous hS₂ hx₂ fun z ↦ (hxb z).1) using 1
    funext z
    simp

/-- Adding to `y₀` the complexified gauge direction of `h₁ + i h₂` cancels the gauge-type rows of
`L_x y₀` at a point where `-Δ h₁ + P h₁` and `-Δ h₂ + P h₂` are minus those rows,
`P = |α|² / 4`, and where the holomorphicity rows of `L_x y₀` and of the vortex equation vanish. -/
private theorem gaugeFixedOperator_add_complexGaugeDirection_eq_zero
    {y₀ : ℂ → EuclideanSpace ℝ (Fin 4)} {h₁ h₂ : ℂ → ℝ} {z : ℂ} (hx : ContDiff ℝ 1 x)
    (hhol : equation x z 1 = 0 ∧ equation x z 2 = 0) (hy₀ : ContDiff ℝ 1 y₀)
    (hrow : gaugeFixedOperator x y₀ z 2 = 0 ∧ gaugeFixedOperator x y₀ z 3 = 0)
    (hh₁ : ContDiff ℝ 3 h₁) (hh₂ : ContDiff ℝ 3 h₂)
    (hE₁ : -Δ h₁ z + (x z 2 ^ 2 + x z 3 ^ 2) * h₁ z = -gaugeFixedOperator x y₀ z 1)
    (hE₂ : -Δ h₂ z + (x z 2 ^ 2 + x z 3 ^ 2) * h₂ z = -gaugeFixedOperator x y₀ z 0) :
    gaugeFixedOperator x (y₀ + complexGaugeDirection x fun z ↦ (h₁ z : ℂ) + h₂ z * I) z = 0 := by
  have hxi (i : Fin 4) : ContDiff ℝ 1 fun w ↦ x w i := contDiff_euclidean.mp hx i
  have hh := contDiff_ofReal_add_mul_I hh₁ hh₂
  have hcg : ContDiff ℝ 1 (complexGaugeDirection x fun z ↦ (h₁ z : ℂ) + h₂ z * I) :=
    contDiff_complexGaugeDirection (hxi 2) (hxi 3) (hh.of_le (by norm_num))
  rw [gaugeFixedOperator_add x ((hy₀.differentiable (by simp)) z)
    ((hcg.differentiable (by simp)) z), gaugeFixedOperator_complexGaugeDirection
      (((hxi 2).differentiable (by simp)) z) (((hxi 3).differentiable (by simp)) z)
      (hh.of_le (by norm_num)).contDiffAt, laplacian_ofReal_add_mul_I
        (hh₁.of_le (by norm_num)).contDiffAt (hh₂.of_le (by norm_num)).contDiffAt]
  obtain ⟨r₂, r₃⟩ := hrow
  generalize gaugeFixedOperator x y₀ z = L at hE₁ hE₂ r₂ r₃ ⊢
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, PiLp.add_apply, PiLp.zero_apply, Matrix.cons_val_zero,
      equation_apply_one, equation_apply_two, smul_add, real_smul, neg_add_rev, add_re, add_im,
      neg_re, neg_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    linarith
  · simp only [Fin.mk_one, Fin.isValue, PiLp.add_apply, PiLp.zero_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero, equation_apply_one, equation_apply_two, smul_add, real_smul,
      neg_add_rev, add_re, add_im, neg_re, neg_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    linarith
  · simp [r₂, hhol.1, hhol.2]
  · simp [r₃, hhol.1, hhol.2]

/-- The section variation of the seed plus `complexGaugeDirection x h` decomposes as
`α (h + (ρ - 1) w) + e^ν H`, with a continuous first factor, when `ρ` is one near the zeros of
`α`. -/
private theorem sectionValue_add_eq_mul_add_exp_mul {ρ : ℂ → ℝ} {ν H h : ℂ → ℂ}
    (hρ : Continuous ρ) (hν : ContDiff ℝ ∞ ν) (hH : Differentiable ℂ H)
    (hα : ContDiff ℝ ∞ (sectionValue x)) (hρ₁ : ∀ z, sectionValue x z = 0 → ρ =ᶠ[𝓝 z] 1)
    (hh : Continuous h) :
    Continuous (fun z ↦ h z + ((ρ z : ℂ) - 1) * seedQuotient x ν H z) ∧
      ∀ z, sectionValue (seedField x ρ ν H + complexGaugeDirection x h) z =
        sectionValue x z * (h z + ((ρ z : ℂ) - 1) * seedQuotient x ν H z) +
          exp (ν z) * H z := by
  refine ⟨hh.add (continuous_iff_continuousAt.2 fun z ↦ ?_), fun z ↦ ?_⟩
  · -- `(ρ - 1) w` vanishes near the zeros of `α`, where `ρ = 1`.
    by_cases hz : sectionValue x z = 0
    · refine continuousAt_const (y := (0 : ℂ)).congr ?_
      filter_upwards [hρ₁ z hz] with u hu
      simp [hu]
    · exact ((ofRealCLM.continuous.comp hρ).sub continuous_const).continuousAt.mul
        (contDiffAt_seedQuotient hν hH hα hz).continuousAt
  · -- `α (ρ - 1) w = (ρ - 1) e^ν H`: off the zeros `α w = e^ν H`, at a zero `ρ = 1`.
    have hw : sectionValue x z * (((ρ z : ℂ) - 1) * seedQuotient x ν H z) =
        ((ρ z : ℂ) - 1) * (exp (ν z) * H z) := by
      by_cases hz : sectionValue x z = 0
      · have h1 : ρ z = 1 := (hρ₁ z hz).self_of_nhds
        simp [h1]
      · rw [seedQuotient, exp_neg]
        field_simp
    rw [sectionValue_add, sectionValue_seedField, sectionValue_complexGaugeDirection, mul_add, hw]
    ring

/-! ### Kernel elements with a prescribed holomorphic part -/

/-- **Every entire function is the holomorphic part of a kernel element.** Let `x` be a smooth
plane vortex whose section has unit modulus at infinity, and let `∂bar ν = (b₂ - i b₁) / 2` with
`ν` smooth, so that `α = e^ν f` with `f` entire. For every entire `H` there is a `C²`
square-integrable solution `y` of `L_x y = 0` whose section variation decomposes as
`δα = α G + e^ν H` with `G` continuous. Hence `δα / α = G + H / f`, whose principal parts at the
zeros of `α` are those of `H / f`. -/
theorem exists_mem_gaugeFixedKernel_sectionValue_eq_mul_add_exp_mul (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {ν : ℂ → ℂ} (hν : ContDiff ℝ ∞ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H) :
    ∃ y ∈ gaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧
      ∀ z, sectionValue y z = sectionValue x z * G z + exp (ν z) * H z := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.mp hx i
  have hp : Differentiable ℝ fun w ↦ x w 2 := (hxi 2).differentiable (by simp)
  have hq : Differentiable ℝ fun w ↦ x w 3 := (hxi 3).differentiable (by simp)
  have hhol (w : ℂ) : equation x w 1 = 0 ∧ equation x w 2 = 0 := by simp [hsol w]
  have hα : ContDiff ℝ ∞ (sectionValue x) := contDiff_sectionValue (hxi 2) (hxi 3)
  have hf := differentiable_exp_neg_mul_sectionValue hp hq hhol (hν.differentiable (by simp)) hνeq
  -- A cutoff `ρ` equal to one on a disc containing the finitely many zeros of `α`.
  have hZ := finite_setOfPred_sectionValue_eq_zero (k := ⊤) le_top (hxi 0) (hxi 1) hp hq hhol hlim
  obtain ⟨r, hr⟩ := hZ.isBounded.subset_ball 0
  let b : ContDiffBump (0 : ℂ) := ⟨max r 1, max r 1 + 1, by positivity, by linarith⟩
  have hb : ContDiff ℝ ∞ (b : ℂ → ℝ) := b.contDiff
  have hρ₁ (z : ℂ) (hz : sectionValue x z = 0) : ⇑b =ᶠ[𝓝 z] 1 := by
    have hzr : z ∈ ball (0 : ℂ) (max r 1) := ball_subset_ball (le_max_left _ _) (hr hz)
    filter_upwards [isOpen_ball.mem_nhds hzr] with u hu
    exact b.one_of_mem_closedBall (ball_subset_closedBall hu)
  -- The seed field `y₀`; the defect `L_x y₀` is smooth with compact support.
  set y₀ := seedField x b ν H
  have hy₀ : ContDiff ℝ ∞ y₀ := contDiff_seedField hb hν hH hα hρ₁
  have hy₀c : HasCompactSupport y₀ := hasCompactSupport_seedField b.hasCompactSupport
  have hLi (i : Fin 4) : ContDiff ℝ ∞ fun z ↦ gaugeFixedOperator x y₀ z i :=
    contDiff_euclidean.mp (contDiff_gaugeFixedOperator hx (hy₀.of_le (by simp))) i
  have hg (i : Fin 4) : MemLp (fun z ↦ gaugeFixedOperator x y₀ z i) 2 volume := by
    refine (hLi i).continuous.memLp_of_hasCompactSupport (hy₀c.mono' fun u hu ↦ ?_)
    by_contra h
    apply hu
    simp [gaugeFixedOperator_congr_nhds x (notMem_tsupport_iff_eventuallyEq.1 h),
      gaugeFixedOperator_zero]
  -- The potential `P = |α|² / 4` lies in `[0, 1 / 4]` and exceeds `1 / 8` outside a disc.
  set P : ℂ → ℝ := fun z ↦ x z 2 ^ 2 + x z 3 ^ 2
  have hP₀ (z : ℂ) : 0 ≤ P z := by positivity
  have hPle (z : ℂ) : 4 * P z ≤ 1 :=
    normSq_le_one_of_tendsto ((hxi 2).of_le (by simp)) ((hxi 3).of_le (by simp)) hsol hlim z
  obtain ⟨R, -, hR⟩ := exists_exterior_lt_mass hlim (by norm_num : (1 / 8 : ℝ) < 1 / 4)
  have hxb (z : ℂ) : ‖x z 2‖ ≤ 1 ∧ ‖x z 3‖ ≤ 1 := by
    have h4 := hPle z
    simp only [Real.norm_eq_abs, abs_le]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg (x z 2), sq_nonneg (x z 3)]
  -- Solve `Δ h = P h + L_x y₀` in the two gauge-type rows, and correct `y₀` by
  -- `complexGaugeDirection x (h₁ + i h₂)`.
  have hPC (z : ℂ) : P z ≤ 1 / 4 := by linarith [hPle z]
  obtain ⟨h₁, hh₁, hS₁, hD₁, -, hE₁⟩ := exists_contDiff_laplacian_eq_mul_add le_top
    (((hxi 2).pow 2).add ((hxi 3).pow 2)) hP₀ hPC (by norm_num : (0 : ℝ) < 1 / 8)
    (fun z hz ↦ (hR z hz).le) (hLi 1) (hg 1)
  obtain ⟨h₂, hh₂, hS₂, hD₂, -, hE₂⟩ := exists_contDiff_laplacian_eq_mul_add le_top
    (((hxi 2).pow 2).add ((hxi 3).pow 2)) hP₀ hPC (by norm_num : (0 : ℝ) < 1 / 8)
    (fun z hz ↦ (hR z hz).le) (hLi 0) (hg 0)
  replace hh₁ : ContDiff ℝ ∞ h₁ := hh₁.of_le le_self_add
  replace hh₂ : ContDiff ℝ ∞ h₂ := hh₂.of_le le_self_add
  have hh := contDiff_ofReal_add_mul_I hh₁ hh₂
  obtain ⟨hG, hdec⟩ := sectionValue_add_eq_mul_add_exp_mul hb.continuous hν hH hα hρ₁
    hh.continuous
  refine ⟨_, mem_gaugeFixedKernel.2 ⟨(hy₀.of_le (by simp)).add (contDiff_complexGaugeDirection
    ((hxi 2).of_le (by simp)) ((hxi 3).of_le (by simp)) (hh.of_le (by simp))),
    (hy₀.continuous.memLp_of_hasCompactSupport hy₀c).add (memLp_complexGaugeDirection
      (hxi 2).continuous (hxi 3).continuous hxb (hh₁.of_le (by simp)) hS₁ hD₁ (hh₂.of_le (by simp))
      hS₂ hD₂),
    fun z ↦ gaugeFixedOperator_add_complexGaugeDirection_eq_zero (hx.of_le (by simp)) (hhol z)
      (hy₀.of_le (by simp)) ⟨gaugeFixedOperator_seedField_eq_zero hx hsol hZ hb hρ₁ hν hH
        hf (by simp) z, gaugeFixedOperator_seedField_eq_zero hx hsol hZ hb hρ₁ hν hH
        hf (by simp) z⟩ (hh₁.of_le (by simp)) (hh₂.of_le (by simp)) (by linarith [hE₁ z])
        (by linarith [hE₂ z])⟩, _, hG, hdec⟩

/-! ### The dimension of the kernel -/

/-- **The kernel of `L_x` at a framed vortex has real dimension `2 m`.** Let `x` be a smooth plane
vortex whose section has the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Then the space of `C²`
square-integrable solutions of `L_x y = 0` has real dimension `2 m`, the real dimension of the
tangent space of the divisor space `Sym^m ℂ`. The upper bound is
`TauCeti.Vortex.finrank_gaugeFixedKernel_le`; for the lower bound, the
principal parts of `δα / α` at the zeros of `α` give a surjective real-linear map of this kernel
onto `ℂ^m`, by `TauCeti.Vortex.exists_mem_gaugeFixedKernel_sectionValue_eq_mul_add_exp_mul`
applied to Hermite interpolation polynomials. -/
theorem finrank_gaugeFixedKernel {m : ℕ} (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.mp hx i
  have hp : Differentiable ℝ fun w ↦ x w 2 := (hxi 2).differentiable (by simp)
  have hq : Differentiable ℝ fun w ↦ x w 3 := (hxi 3).differentiable (by simp)
  have hhol (w : ℂ) : equation x w 1 = 0 ∧ equation x w 2 = 0 := by simp [hsol w]
  have hlim := tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe
  have hker (y) (hy : y ∈ gaugeFixedKernel x) :
      ContDiff ℝ 2 y ∧ MemLp y 2 volume ∧ ∀ w, gaugeFixedOperator x y w = 0 :=
    mem_gaugeFixedKernel.1 hy
  -- The zero divisor `D ∈ Sym^m ℂ` of `α` and an integrating factor `ν`, `α = e^ν f`.
  obtain ⟨D, hD⟩ :=
    exists_sym_sectionValue_eq_pow_count_mul (k := ⊤) le_top (hxi 0) (hxi 1) hp hq hhol hframe
  have hα : IsZeroMultiplicity (sectionValue x) fun z ↦ Multiset.count z (D : Multiset ℂ) :=
    isZeroMultiplicity_iff.2 fun z ↦ by
      obtain ⟨v, hv, hv₀, hvf⟩ := hD z
      exact ⟨v, hv.continuousAt, hv₀, hvf⟩
  obtain ⟨ν, hν, hνeq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eq (n := ⊤) le_top
    (contDiff_connectionCoeff (hxi 0) (hxi 1))
  have hdec (y) (hy : y ∈ gaugeFixedKernel x) := exists_sectionValue_eq_mul_add_exp_mul_of_mem hp
    hq hhol (hν.differentiable (by simp)) hνeq hker hy
  -- By Hermite interpolation, the principal-part map on the kernel is surjective.
  have hsurj : Function.Surjective (principalPartMap hα hν.continuous hdec) := by
    intro t
    obtain ⟨p, -, hpt⟩ := Polynomial.exists_degree_lt_eval_iterate_derivative_eq (D : Multiset ℂ) t
    obtain ⟨y, hy, G, hG, hyG⟩ := exists_mem_gaugeFixedKernel_sectionValue_eq_mul_add_exp_mul
      hx hsol hlim hν hνeq (H := fun z ↦ p.eval z) p.differentiable
    refine ⟨⟨y, hy⟩, funext fun i ↦ ?_⟩
    rw [principalPartMap_apply, principalPart_eq_iteratedDeriv hα hν.continuous hG
      p.differentiable hyG i.2.2, Polynomial.iteratedDeriv]
    exact hpt i
  have := finiteDimensional_gaugeFixedKernel (hx.of_le (by simp)) hhol hframe
  refine le_antisymm (finrank_gaugeFixedKernel_le (hx.of_le (by simp)) hhol hframe) ?_
  calc 2 * m = Module.finrank ℝ (Multiset.ToType (D : Multiset ℂ) → ℂ) := by
        rw [Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex,
          smul_eq_mul, Finset.card_univ, Multiset.card_coe, Sym.card_coe, mul_comm]
    _ ≤ Module.finrank ℝ (gaugeFixedKernel x) :=
        LinearMap.finrank_le_finrank_of_surjective hsurj

end TauCeti.Vortex
