/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ComplexGauge
public import TauCeti.Analysis.PDE.Vortex.PrincipalPart
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Algebra.Polynomial.HermiteInterpolation
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Analysis.PDE.Schrodinger.Planar
import TauCeti.Analysis.PDE.Vortex.ExteriorEstimate
import TauCeti.Analysis.PDE.Vortex.ScalarEquation
import TauCeti.Analysis.Sobolev.BesselPotential.Basic

/-!
# The kernel of the gauge-fixed operator at a framed plane vortex

At a field `x = (a, α)`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.gaugeFixedOperator`) is the linearization of the vortex equations together with
the Coulomb gauge condition. Its kernel `gaugeFixedKernel x` is taken here to be the real vector
space of `C²` square-integrable variations `y` with `L_x y = 0` at every point. This file proves
that at a smooth vortex with the degree-`m` end framing this kernel has real dimension `2 m`
(`TauCeti.Vortex.finrank_gaugeFixedKernel`), the real dimension of the tangent space of the
divisor space `Sym^m ℂ`.

The kernel is identified with `ℂ^m` through principal parts. Write `α = e^ν f` with `f` entire and
`∂bar ν = (b₂ - i b₁) / 2` (`TauCeti.Vortex.differentiable_exp_neg_mul_sectionValue`). The section
variation of a kernel element decomposes as `δα = α G + e^ν H` with `G` continuous and `H` entire,
so `δα / α = G + H / f`, and the derivatives `H⁽ʲ⁾(a)`, `j` below the multiplicity of the zero `a`
of `α`, form the principal-part map `TauCeti.Vortex.principalPartMap` to `ℂ^m`.

* **Injectivity.** If all principal parts vanish, then `δα = α η` with `η` of class `C²`, and such a
  kernel element vanishes, since `|η|²` is subharmonic and square integrable
  (`TauCeti.Vortex.principalPartMap_injective`,
  `TauCeti.Vortex.eq_zero_of_memLp_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul`).
* **Surjectivity.** Every entire `H` is the holomorphic part of a kernel element
  (`TauCeti.Vortex.exists_mem_gaugeFixedKernel_sectionValue_eq_mul_add_exp_mul`). Take a cutoff
  `ρ` equal to one near the finitely many zeros of `α`, and let `y₀` be the compactly supported
  smooth field with section `ρ e^ν H` and connection variation `2 i (∂bar ρ) H / f`. Off the zeros
  of `α` it is the complexified gauge direction of `ρ H / f`
  (`TauCeti.Vortex.complexGaugeDirection`), so the holomorphicity rows of `L_x y₀` vanish, and
  the two remaining rows are a smooth compactly supported defect. The correction is the
  complexified gauge direction of a smooth `h ∈ H²` solving `-Δh + P h = -(defect)` with
  `P = |α|² / 4` (`TauCeti.exists_contDiff_mem_realSobolevFunctions_neg_laplacian_add_mul_eq`).
  The principal parts of `y₀ + complexGaugeDirection x h` are the derivatives of `H`, and these can
  be prescribed arbitrarily by Hermite interpolation
  (`Polynomial.exists_degree_lt_eval_iterate_derivative_eq`).

Thus the principal-part map is a real-linear isomorphism of the kernel onto `ℂ^m`. These are
statements about classical solutions; the Fredholm property of the Sobolev realization of `L_x`
and the vanishing of its cokernel are not treated here.

## Main results

* `TauCeti.Vortex.gaugeFixedKernel`: the `C²` square-integrable kernel of `L_x`.
* `TauCeti.Vortex.exists_mem_gaugeFixedKernel_sectionValue_eq_mul_add_exp_mul`: every entire
  function is the holomorphic part of a kernel element.
* `TauCeti.Vortex.finrank_gaugeFixedKernel`: the kernel at a framed degree-`m` vortex has real
  dimension `2 m`.

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

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### The kernel -/

/-- **The kernel of the gauge-fixed operator.** The real vector space of `C²` square-integrable
variations `y` with `L_x y = 0` at every point, for the gauge-fixed operator
`L_x = d₀* ⊕ d₁` (`TauCeti.Vortex.gaugeFixedOperator`). -/
def gaugeFixedKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4)) where
  carrier := {y | ContDiff ℝ 2 y ∧ MemLp y 2 volume ∧ ∀ z, gaugeFixedOperator x y z = 0}
  add_mem' {y v} hy hv := ⟨hy.1.add hv.1, hy.2.1.add hv.2.1, fun z ↦ by
    rw [gaugeFixedOperator_add x (hy.1.differentiable (by simp) z)
      (hv.1.differentiable (by simp) z), hy.2.2 z, hv.2.2 z, add_zero]⟩
  zero_mem' := ⟨contDiff_const, MemLp.zero, fun z ↦ by simp [gaugeFixedOperator_zero]⟩
  smul_mem' t y hy := ⟨hy.1.const_smul t, hy.2.1.const_smul t, fun z ↦ by
    rw [gaugeFixedOperator_smul, hy.2.2 z, smul_zero]⟩

/-- Membership in the kernel of the gauge-fixed operator. -/
@[simp]
theorem mem_gaugeFixedKernel {y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    y ∈ gaugeFixedKernel x ↔
      ContDiff ℝ 2 y ∧ MemLp y 2 volume ∧ ∀ z, gaugeFixedOperator x y z = 0 :=
  Iff.rfl

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
  apply Complex.ext <;> simp <;> ring

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
  · simp [seedField_apply_zero, complexGaugeDirection_apply_zero, hD.fderiv]
    ring
  · simp [seedField_apply_one, complexGaugeDirection_apply_one, hD.fderiv]
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

/-- The complexified gauge direction of `h₁ + i h₂`, for smooth `h₁`, `h₂ ∈ H²(ℂ)`, at a field with
continuous section coordinates bounded by one, is square integrable. -/
private theorem memLp_complexGaugeDirection {h₁ h₂ : ℂ → ℝ} (hx₂ : Continuous fun z ↦ x z 2)
    (hx₃ : Continuous fun z ↦ x z 3) (hxb : ∀ z, ‖x z 2‖ ≤ 1 ∧ ‖x z 3‖ ≤ 1)
    (hh₁ : ContDiff ℝ ∞ h₁) (hS₁ : h₁ ∈ realSobolevFunctions ℂ 2 2) (hh₂ : ContDiff ℝ ∞ h₂)
    (hS₂ : h₂ ∈ realSobolevFunctions ℂ 2 2) :
    MemLp (complexGaugeDirection x fun z ↦ (h₁ z : ℂ) + h₂ z * I) 2 volume := by
  have hfd (z v : ℂ) : fderiv ℝ (fun z ↦ (h₁ z : ℂ) + h₂ z * I) z v =
      (fderiv ℝ h₁ z v : ℂ) + fderiv ℝ h₂ z v * I := by
    have hd := (ofRealCLM.hasFDerivAt.comp z ((hh₁.differentiable (by simp)) z).hasFDerivAt).add
      ((ofRealCLM.hasFDerivAt.comp z ((hh₂.differentiable (by simp)) z).hasFDerivAt).mul_const I)
    rw [show fderiv ℝ (fun z ↦ (h₁ z : ℂ) + h₂ z * I) z = _ from hd.fderiv]
    simp [mul_comm I]
  -- Classical derivatives of smooth `H²` functions are in `H¹ ⊆ L²`.
  have hd (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f) (hS : f ∈ realSobolevFunctions ℂ 2 2) (v : ℂ) :
      MemLp (fun z ↦ fderiv ℝ f z v) 2 volume := by
    refine memLp_of_mem_realSobolevFunctions (s := 1) ?_
    refine fderiv_apply_mem_realSobolevFunctions ENNReal.one_lt_two ENNReal.ofNat_ne_top
      zero_le_one (hf.of_le (by simp)) ?_ v
    norm_num
    exact hS
  have hmul (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f) (hS : f ∈ realSobolevFunctions ℂ 2 2) {g : ℂ → ℝ}
      (hg : Continuous g) (hgb : ∀ z, ‖g z‖ ≤ 1) : MemLp (fun z ↦ f z * g z) 2 volume :=
    (memLp_of_mem_realSobolevFunctions hS).of_le (hf.continuous.mul hg).aestronglyMeasurable
      (ae_of_all _ fun z ↦ by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hgb z))
  refine memLp_piLp_iff.2 fun i ↦ ?_
  fin_cases i
  · convert ((hd h₂ hh₂ hS₂ 1).neg).sub (hd h₁ hh₁ hS₁ I) using 1
    funext z
    simp [hfd]
  · convert (hd h₁ hh₁ hS₁ 1).sub (hd h₂ hh₂ hS₂ I) using 1
    funext z
    simp [hfd]
  · convert (hmul h₁ hh₁ hS₁ hx₂ fun z ↦ (hxb z).1).sub
      (hmul h₂ hh₂ hS₂ hx₃ fun z ↦ (hxb z).2) using 1
    funext z
    simp
  · convert (hmul h₁ hh₁ hS₁ hx₃ fun z ↦ (hxb z).2).add
      (hmul h₂ hh₂ hS₂ hx₂ fun z ↦ (hxb z).1) using 1
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
  have hh : ContDiff ℝ 3 fun z ↦ (h₁ z : ℂ) + h₂ z * I :=
    (ofRealCLM.contDiff.comp hh₁).add ((ofRealCLM.contDiff.comp hh₂).mul contDiff_const)
  -- The Laplacian of `h₁ + i h₂` is `Δ h₁ + i Δ h₂`.
  have hΔ : Δ (fun z ↦ (h₁ z : ℂ) + h₂ z * I) z = (Δ h₁ z : ℂ) + Δ h₂ z * I := by
    have hsplit : (fun z ↦ (h₁ z : ℂ) + h₂ z * I) =
        (ofRealCLM ∘ h₁) + ((1 : ℝ →L[ℝ] ℝ).smulRight I ∘ h₂) := by
      funext w
      simp [Complex.real_smul]
    have c₁ : ContDiffAt ℝ 2 h₁ z := (hh₁.of_le (by norm_num)).contDiffAt
    have c₂ : ContDiffAt ℝ 2 h₂ z := (hh₂.of_le (by norm_num)).contDiffAt
    rw [hsplit, (c₁.continuousLinearMap_comp ofRealCLM).laplacian_add
      (c₂.continuousLinearMap_comp _), c₁.laplacian_CLM_comp_left, c₂.laplacian_CLM_comp_left]
    simp [Complex.real_smul]
  have hcg : ContDiff ℝ 1 (complexGaugeDirection x fun z ↦ (h₁ z : ℂ) + h₂ z * I) :=
    contDiff_complexGaugeDirection (hxi 2) (hxi 3) (hh.of_le (by norm_num))
  rw [gaugeFixedOperator_add x ((hy₀.differentiable (by simp)) z)
    ((hcg.differentiable (by simp)) z), gaugeFixedOperator_complexGaugeDirection
      (((hxi 2).differentiable (by simp)) z) (((hxi 3).differentiable (by simp)) z)
      (hh.of_le (by norm_num)).contDiffAt, hΔ]
  obtain ⟨r₂, r₃⟩ := hrow
  generalize gaugeFixedOperator x y₀ z = L at hE₁ hE₂ r₂ r₃ ⊢
  ext i
  fin_cases i
  · simp [-ofReal_pow, -ofReal_add]
    linarith
  · simp [-ofReal_pow, -ofReal_add]
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
  set y₀ := seedField x b ν H with hy₀def
  have hy₀ : ContDiff ℝ ∞ y₀ := contDiff_seedField hb hν hH hα hρ₁
  have hy₀c : HasCompactSupport y₀ := hasCompactSupport_seedField b.hasCompactSupport
  have hLi (i : Fin 4) : ContDiff ℝ ∞ fun z ↦ gaugeFixedOperator x y₀ z i :=
    contDiff_euclidean.mp (contDiff_gaugeFixedOperator hx (hy₀.of_le (by simp))) i
  have hg (i : Fin 4) : MemLp (fun z ↦ -gaugeFixedOperator x y₀ z i) 2 volume := by
    refine (hLi i).neg.continuous.memLp_of_hasCompactSupport (hy₀c.mono' fun u hu ↦ ?_)
    by_contra h
    apply hu
    simp [gaugeFixedOperator_congr_nhds x (notMem_tsupport_iff_eventuallyEq.1 h),
      gaugeFixedOperator_zero]
  -- The potential `P = |α|² / 4` lies in `[0, 1 / 4]` and exceeds `1 / 8` outside a disc.
  set P : ℂ → ℝ := fun z ↦ x z 2 ^ 2 + x z 3 ^ 2 with hPdef
  have hP₀ (z : ℂ) : 0 ≤ P z := by positivity
  have hPle (z : ℂ) : 4 * P z ≤ 1 :=
    normSq_le_one_of_tendsto ((hxi 0).differentiable (by simp)) ((hxi 1).differentiable (by simp))
      ((hxi 2).of_le (by simp)) ((hxi 3).of_le (by simp)) hsol hlim z
  have hPb : MemLp P ⊤ volume :=
    memLp_top_of_bound (((hxi 2).pow 2).add ((hxi 3).pow 2)).continuous.aestronglyMeasurable
      (1 / 4) (ae_of_all _ fun z ↦ by
        rw [Real.norm_of_nonneg (hP₀ z)]
        linarith [hPle z])
  obtain ⟨R, -, hR⟩ := exists_exterior_lt_mass hlim (by norm_num : (1 / 8 : ℝ) < 1 / 4)
  have hxb (z : ℂ) : ‖x z 2‖ ≤ 1 ∧ ‖x z 3‖ ≤ 1 := by
    have h4 := hPle z
    simp only [Real.norm_eq_abs, abs_le]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg (x z 2), sq_nonneg (x z 3)]
  -- Solve `-Δ h + P h = -(L_x y₀)` in the two gauge-type rows, and correct `y₀` by
  -- `complexGaugeDirection x (h₁ + i h₂)`.
  obtain ⟨h₁, hh₁, hS₁, hE₁⟩ := exists_contDiff_mem_realSobolevFunctions_neg_laplacian_add_mul_eq
    (((hxi 2).pow 2).add ((hxi 3).pow 2)) hPb hP₀ (by norm_num : (0 : ℝ) < 1 / 8)
    (fun z hz ↦ (hR z hz).le) (hLi 1).neg (hg 1)
  obtain ⟨h₂, hh₂, hS₂, hE₂⟩ := exists_contDiff_mem_realSobolevFunctions_neg_laplacian_add_mul_eq
    (((hxi 2).pow 2).add ((hxi 3).pow 2)) hPb hP₀ (by norm_num : (0 : ℝ) < 1 / 8)
    (fun z hz ↦ (hR z hz).le) (hLi 0).neg (hg 0)
  have hh : ContDiff ℝ ∞ fun z ↦ (h₁ z : ℂ) + h₂ z * I :=
    (ofRealCLM.contDiff.comp hh₁).add ((ofRealCLM.contDiff.comp hh₂).mul contDiff_const)
  obtain ⟨hG, hdec⟩ := sectionValue_add_eq_mul_add_exp_mul hb.continuous hν hH hα hρ₁
    hh.continuous
  refine ⟨_, ⟨(hy₀.of_le (by simp)).add (contDiff_complexGaugeDirection
    ((hxi 2).of_le (by simp)) ((hxi 3).of_le (by simp)) (hh.of_le (by simp))),
    (hy₀.continuous.memLp_of_hasCompactSupport hy₀c).add (memLp_complexGaugeDirection
      (hxi 2).continuous (hxi 3).continuous hxb hh₁ hS₁ hh₂ hS₂),
    fun z ↦ gaugeFixedOperator_add_complexGaugeDirection_eq_zero (hx.of_le (by simp)) (hhol z)
      (hy₀.of_le (by simp)) ⟨gaugeFixedOperator_seedField_eq_zero hx hsol hZ hb hρ₁ hν hH
        hf (by simp) z, gaugeFixedOperator_seedField_eq_zero hx hsol hZ hb hρ₁ hν hH
        hf (by simp) z⟩ (hh₁.of_le (by simp)) (hh₂.of_le (by simp)) (hE₁ z) (hE₂ z)⟩, _, hG, hdec⟩

/-! ### The dimension of the kernel -/

/-- **The kernel of `L_x` at a framed vortex has real dimension `2 m`.** Let `x` be a smooth plane
vortex whose section has the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Then the space of `C²`
square-integrable solutions of `L_x y = 0` has real dimension `2 m`, the real dimension of the
tangent space of the divisor space `Sym^m ℂ`. Indeed the principal parts of `δα / α` at the zeros
of `α` give a real-linear isomorphism of this kernel onto `ℂ^m`: it is injective since a kernel
element with `δα / α` regular vanishes, and surjective by
`TauCeti.Vortex.exists_mem_gaugeFixedKernel_sectionValue_eq_mul_add_exp_mul` applied to Hermite
interpolation polynomials. -/
theorem finrank_gaugeFixedKernel {m : ℕ} (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.mp hx i
  have hp : Differentiable ℝ fun w ↦ x w 2 := (hxi 2).differentiable (by simp)
  have hq : Differentiable ℝ fun w ↦ x w 3 := (hxi 3).differentiable (by simp)
  have hhol (w : ℂ) : equation x w 1 = 0 ∧ equation x w 2 = 0 := by simp [hsol w]
  have hlim := tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe
  -- The zero divisor `D ∈ Sym^m ℂ` of `α` and an integrating factor `ν`, `α = e^ν f`.
  obtain ⟨D, hD⟩ :=
    exists_sym_sectionValue_eq_pow_count_mul (k := ⊤) le_top (hxi 0) (hxi 1) hp hq hhol hframe
  have hα : IsZeroMultiplicity (sectionValue x) fun z ↦ Multiset.count z (D : Multiset ℂ) :=
    isZeroMultiplicity_iff.2 fun z ↦ by
      obtain ⟨v, hv, hv₀, hvf⟩ := hD z
      exact ⟨v, hv.continuousAt, hv₀, hvf⟩
  obtain ⟨ν, hν, hνeq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eq (n := ⊤) le_top
    (contDiff_connectionCoeff (hxi 0) (hxi 1))
  have hν2 : ContDiff ℝ (2 : ℕ∞) ν := hν.of_le (by exact_mod_cast le_top)
  -- The hypotheses of the principal-part map on the kernel.
  have hV : ∀ y ∈ gaugeFixedKernel x, ContDiff ℝ (2 : ℕ∞) (fun w ↦ y w 0) ∧
      ContDiff ℝ (2 : ℕ∞) (fun w ↦ y w 1) ∧ Differentiable ℝ (fun w ↦ y w 2) ∧
      Differentiable ℝ (fun w ↦ y w 3) ∧
      ∀ w, linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0 := by
    intro y hy
    have hyi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ y w i := contDiff_euclidean.mp hy.1 i
    refine ⟨hyi 0, hyi 1, (hyi 2).differentiable (by simp), (hyi 3).differentiable (by simp),
      fun w ↦ ?_⟩
    have h₂ := congrArg (fun v ↦ v 2) (hy.2.2 w)
    have h₃ := congrArg (fun v ↦ v 3) (hy.2.2 w)
    simp only [gaugeFixedOperator_apply_two, gaugeFixedOperator_apply_three,
      PiLp.zero_apply] at h₂ h₃
    exact ⟨h₂, h₃⟩
  have hdec (y) (hy : y ∈ gaugeFixedKernel x) : ∃ G : ℂ → ℂ, Continuous G ∧
      ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
        ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hV y hy
    obtain ⟨G, hG, H, hH, hGH⟩ := exists_sectionValue_eq_mul_add_exp_mul (k := 2) (by norm_num)
      hp hq hhol (hν.differentiable (by simp)) hνeq h₁ h₂ h₃ h₄ h₅
    exact ⟨G, hG.continuous, H, hH, hGH⟩
  have hdiv : ∀ y ∈ gaugeFixedKernel x, ∀ η : ℂ → ℂ, ContDiff ℝ (2 : ℕ∞) η →
      (∀ z, sectionValue y z = sectionValue x z * η z) → y = 0 := fun y hy η hη hyη ↦
    eq_zero_of_memLp_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul (μ := volume)
      (hx.of_le (by simp)) hhol hlim hy.1.continuous hy.2.1 hη hy.2.2
      fun z ↦ by rw [hyη, mul_comm]
  -- The principal-part map is injective and, by Hermite interpolation, surjective.
  have hinj := principalPartMap_injective (k := 2) (by norm_num)
    ((hxi 0).of_le (by exact_mod_cast le_top)) ((hxi 1).of_le (by exact_mod_cast le_top))
    hp hq hhol hα hν2 hνeq hV hdec hdiv
  have hsurj : Function.Surjective (principalPartMap hα hν2.continuous hdec) := by
    intro t
    obtain ⟨p, -, hpt⟩ := Polynomial.exists_degree_lt_eval_iterate_derivative_eq (D : Multiset ℂ) t
    obtain ⟨y, hy, G, hG, hyG⟩ := exists_mem_gaugeFixedKernel_sectionValue_eq_mul_add_exp_mul
      hx hsol hlim hν hνeq (H := fun z ↦ p.eval z) p.differentiable
    refine ⟨⟨y, hy⟩, funext fun i ↦ ?_⟩
    rw [principalPartMap_apply, principalPart_eq_iteratedDeriv hα hν.continuous hG
      p.differentiable hyG i.2.2, Polynomial.iteratedDeriv]
    exact hpt i
  calc Module.finrank ℝ (gaugeFixedKernel x)
      = Module.finrank ℝ (Multiset.ToType (D : Multiset ℂ) → ℂ) :=
        (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).finrank_eq
    _ = 2 * m := by
      rw [Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul,
        Finset.card_univ, Multiset.card_coe, Sym.card_coe, mul_comm]

end TauCeti.Vortex
