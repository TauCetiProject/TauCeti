/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Bootstrap
public import TauCeti.Analysis.PDE.Vortex.Existence
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Regularity
public import TauCeti.Analysis.PDE.Vortex.WindingPhase
import TauCeti.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplier

/-!
# Smooth framed vortices have representatives in every `A_m^s`

A smooth plane vortex with the degree-`m` end framing `α (z / |z|)⁻ᵐ → 1` is a smooth solution of
the vortex equations, and its orbits under the smooth framed gauge group are classified by
`Sym ℂ m` (`TauCeti.Vortex.framedVortexModuliEquiv`). The analytic theory of the moduli space works
instead on the affine Sobolev space `A_m^s = x_m + H^s` (`TauCeti.Vortex.framedFieldSpace`) with
the Sobolev gauge group `G_(s+1)` (`TauCeti.Vortex.sobolevGaugeGroup`). This file compares the two
descriptions: every smooth framed vortex is equivalent under the smooth framed gauge group to a
vortex lying in `A_m^s` for every `s`
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`). The representative is the
vortex normalized at its end, whose section is `|α|` times the winding phase `(z / |z|)^m` outside
a compact set (`TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq`). A general smooth
framed vortex need not lie in `A_m^s`: a smooth framed gauge `u` whose phase tends to one only like
`1 / |z|` moves a field `x` of `A_m^s` out of it, since `(u - 1) α` is not square integrable.

**The Coulomb defect.** Let `x` be a smooth vortex normalized at its end, with `|α| → 1` at
infinity, and let `y = x - x_m` be its difference from the reference field. The Coulomb defect
`d₀*_(x_m) y` vanishes outside a compact set
(`TauCeti.Vortex.hasCompactSupport_gaugeAdjoint_referenceField_sub`). Outside the cutoff disc the
connection part of `y` is `(i / 2) ⋆ d log |α|²`
(`TauCeti.Vortex.sub_referenceField_apply_zero_of_equation_eq_zero`), which is divergence free by
the symmetry of the second derivative, and the section part of `y` is `|α| - 1` times the reference
section, so its pairing `Im (conj α_ref δα)` with the reference section vanishes.

**Raising the order.** The field `y` and its first derivative decay like `exp (-c |z|)` for every
`c < 1 / 2` (`TauCeti.Vortex.exists_norm_sub_referenceField_le_mul_exp`,
`TauCeti.Vortex.exists_norm_fderiv_sub_referenceField_le_mul_exp`), so `y ∈ H¹`
(`TauCeti.Vortex.mem_sobolevFields_one_of_norm_le_mul_exp`). Write `L_x = d₀* ⊕ d₁` for the
gauge-fixed operator (`TauCeti.Vortex.gaugeFixedOperator`). The exact quadratic expansion of the
equation about the reference field gives
`L_(x_m) y = (d₀*_(x_m) y, -equation x_m - quadraticTerm y)`. The equation defect of `x_m` is
smooth with compact support. The quadratic term consists of products of coordinates of `y`, and
`L_(x_m) - L₀` multiplies `y` by the reference coordinates; both kinds of coefficient are smooth and
bounded with bounded first derivatives, so they preserve `H¹`
(`TemperedDistribution.mul_mem_realSobolevFunctions_of_bounded_derivatives`). Hence the vacuum
operator `L₀` maps `y` into `H¹`, and its elliptic regularity
(`TauCeti.Vortex.mem_sobolevFields_add_one_of_gaugeFixedOperator`) gives `y ∈ H²`. From `A_m^2`
the elliptic bootstrap
(`TauCeti.Vortex.mem_framedFieldSpace_of_equation_eq_zero_of_gaugeAdjoint_mem`) raises the order
one step at a time, since the Coulomb defect lies in every `H^j`. So `x` lies in every `A_m^s`
(`TauCeti.Vortex.mem_framedFieldSpace_of_sectionValue_eq_norm_mul_windingPhase`).

**Consequences for the moduli.** Every effective divisor `D ∈ Sym ℂ m` is the divisor of a smooth
framed vortex lying in every `A_m^s`
(`TauCeti.Vortex.exists_contDiff_equation_eq_zero_mem_framedFieldSpace`). Two smooth framed
vortices of `A_m^k`, `k ≥ 2`, with the same divisor differ by an element of `G_(k+1)`
(`TauCeti.Vortex.exists_mem_sobolevGaugeGroup_gaugeTransform_eq`), by Taubes's uniqueness theorem
and the regularity of gauges between fields of `A_m^k`
(`TauCeti.Vortex.mem_sobolevGaugeGroup_of_mem_framedFieldSpace`).

## Main results

* `TauCeti.Vortex.mem_sobolevFields_one_of_norm_le_mul_exp`: exponentially decaying `C¹` fields
  lie in `H¹`.
* `TauCeti.Vortex.hasCompactSupport_gaugeAdjoint_referenceField_sub`: the Coulomb defect of an
  end-normalized vortex relative to the reference field has compact support.
* `TauCeti.Vortex.mem_framedFieldSpace_of_sectionValue_eq_norm_mul_windingPhase`: a smooth
  end-normalized vortex lies in every `A_m^s`.
* `TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`: every smooth framed vortex
  has a smooth framed gauge transform lying in every `A_m^s`.
* `TauCeti.Vortex.exists_contDiff_equation_eq_zero_mem_framedFieldSpace`: existence, in every
  `A_m^s`, of a smooth framed vortex with prescribed zeros.
* `TauCeti.Vortex.exists_mem_sobolevGaugeGroup_gaugeTransform_eq`: smooth framed vortices of
  `A_m^k` with the same divisor differ by an element of `G_(k+1)`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric TemperedDistribution
open scoped ContDiff Topology

/-! ### Exponentially decaying fields -/

/-- **Exponentially decaying `C¹` fields are `H¹` fields.** A `C¹` field which is bounded,
together with its derivative, by `K exp (-(c |z|))` for some `c > 0` lies in `sobolevFields 1`. -/
theorem mem_sobolevFields_one_of_norm_le_mul_exp {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : ContDiff ℝ 1 y) {c K : ℝ} (hc : 0 < c) (hyK : ∀ z, ‖y z‖ ≤ K * Real.exp (-(c * ‖z‖)))
    (hdK : ∀ z, ‖fderiv ℝ y z‖ ≤ K * Real.exp (-(c * ‖z‖))) : y ∈ sobolevFields 1 :=
  mem_sobolevFields.2 fun i ↦ mem_realSobolevFunctions_one_of_norm_le_mul_exp
    (by norm_num) (by norm_num) (contDiff_euclidean.1 hy i) hc
    (fun z ↦ (PiLp.norm_apply_le (y z) i).trans (hyK z))
    fun z ↦ (norm_fderiv_apply_le (hy.differentiable one_ne_zero z) i).trans (hdK z)

/-! ### The Coulomb defect of a vortex normalized at its end -/

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}

/-- Outside the cutoff disc, at a point where the section of `x` is `|α|` times the winding phase,
the section of `x - x_m` is a real multiple of the reference section, so the zeroth-order part
`Im (conj α_ref δα) / 4` of the Coulomb defect of `x` relative to the reference field vanishes. -/
private theorem referenceField_mul_sub_sub_eq_zero (f : ContDiffBump (0 : ℝ)) {z : ℂ}
    (hrOut : f.rOut ≤ ‖z‖ ^ 2)
    (hphase : sectionValue x z = ‖sectionValue x z‖ * windingPhase m z) :
    referenceField f m z 2 * (x - referenceField f m) z 3 -
      referenceField f m z 3 * (x - referenceField f m) z 2 = 0 := by
  rw [coe_windingPhase m (ne_zero_of_rOut_le_norm_sq f hrOut), sectionValue_apply] at hphase
  have hre := congrArg Complex.re hphase
  have him := congrArg Complex.im hphase
  simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat,
    im_ofNat, mul_zero, mul_one, sub_zero, zero_add, add_zero, zero_mul] at hre him
  simp only [Pi.sub_apply, PiLp.sub_apply, referenceField_eq_of_rOut_le f m hrOut, Fin.isValue,
    Matrix.cons_val]
  linear_combination (((z / (‖z‖ : ℂ)) ^ m).re * him - ((z / (‖z‖ : ℂ)) ^ m).im * hre) / 4

/-- **The Coulomb defect of an end-normalized vortex has compact support.** Let `x` be a plane
vortex with `|α| → 1` at infinity whose section is `|α|` times the winding phase `(z / |z|)^m`
outside a compact set. Then the Coulomb defect `d₀*_(x_m) (x - x_m)` of `x` relative to the
reference field vanishes outside a compact set. -/
theorem hasCompactSupport_gaugeAdjoint_referenceField_sub (f : ContDiffBump (0 : ℝ))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z) :
    HasCompactSupport (gaugeAdjoint (referenceField f m) (x - referenceField f m)) := by
  set L : ℂ → ℝ := fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))
  -- Outside a compact set `t`: the end normalization, `α ≠ 0`, and the reference field is
  -- `(-i m dθ, (z / |z|)^m)`.
  have hfar : ∀ᶠ z in cocompact ℂ,
      sectionValue x z = ‖sectionValue x z‖ * windingPhase m z ∧
        1 / 4 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) ∧ f.rOut ≤ ‖z‖ ^ 2 :=
    hphase.and ((hlim.eventually (lt_mem_nhds (by norm_num))).and
      ((tendsto_norm_cocompact_atTop.eventually_gt_atTop (max 1 f.rOut)).mono
        fun z hz ↦ rOut_le_norm_sq f hz))
  obtain ⟨t, ht, hts⟩ := mem_cocompact.1 hfar
  refine HasCompactSupport.intro ht fun z hz ↦ ?_
  have hU : tᶜ ∈ 𝓝 z := ht.isClosed.isOpen_compl.mem_nhds hz
  have hα (w : ℂ) (hw : w ∈ tᶜ) : sectionValue x w ≠ 0 := by
    have h := (hts hw).2.1
    rw [← sq_norm_sectionValue] at h
    exact norm_ne_zero_iff.1 fun h0 ↦ by rw [h0] at h; norm_num at h
  have hph (w : ℂ) (hw : w ∈ tᶜ) :
      ∀ᶠ v in 𝓝 w, sectionValue x v = ‖sectionValue x v‖ * windingPhase m v :=
    Filter.eventually_of_mem (ht.isClosed.isOpen_compl.mem_nhds hw) fun v hv ↦ (hts hv).1
  -- Near `z` the connection part of `x - x_m` is `(1 / 2) (-∂_t L, ∂_s L)`, `L = log |α|²`.
  have h₀ : (fun w ↦ (x - referenceField f m) w 0) =ᶠ[𝓝 z]
      fun w ↦ (-1 / 2 : ℝ) * fderiv ℝ L w I := Filter.eventually_of_mem hU fun w hw ↦ by
    dsimp only
    rw [sub_referenceField_apply_zero_of_equation_eq_zero f (hts hw).2.2
      (hp.differentiable (by norm_num) w) (hq.differentiable (by norm_num) w)
      (by simp [hsol w]) (by simp [hsol w]) (hph w hw) (hα w hw)]
    ring
  have h₁ : (fun w ↦ (x - referenceField f m) w 1) =ᶠ[𝓝 z]
      fun w ↦ (1 / 2 : ℝ) * fderiv ℝ L w 1 := Filter.eventually_of_mem hU fun w hw ↦ by
    dsimp only
    rw [sub_referenceField_apply_one_of_equation_eq_zero f (hts hw).2.2
      (hp.differentiable (by norm_num) w) (hq.differentiable (by norm_num) w)
      (by simp [hsol w]) (by simp [hsol w]) (hph w hw) (hα w hw)]
    ring
  have hL : ContDiffAt ℝ 2 L z :=
    (contDiff_normSq hp hq).contDiffAt.log (by
      rw [← sq_norm_sectionValue]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hα z hz)))
  -- This connection is divergence free, since the second derivative of `L` is symmetric.
  have hdiv : fderiv ℝ (fun w ↦ (x - referenceField f m) w 0) z 1 +
      fderiv ℝ (fun w ↦ (x - referenceField f m) w 1) z I = 0 := by
    rw [h₀.fderiv_eq, h₁.fderiv_eq, ((hL.hasFDerivAt_fderiv_apply le_rfl I).const_mul _).fderiv,
      ((hL.hasFDerivAt_fderiv_apply le_rfl 1).const_mul _).fderiv]
    have hsymm := (hL.isSymmSndFDerivAt (by simp)).eq 1 I
    simp only [smul_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
    rw [hsymm]
    ring
  rw [gaugeAdjoint_def]
  linear_combination hdiv + referenceField_mul_sub_sub_eq_zero f (hts hz).2.2 (hts hz).1

/-! ### End-normalized vortices lie in every `A_m^s` -/

/-- A field bounded, with its derivative, by `K exp (-(c |z|))`, `c ≥ 0`, has bounded coordinates
with bounded first derivatives. -/
private theorem exists_forall_norm_iteratedFDeriv_apply_le {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : Differentiable ℝ y) {c K : ℝ} (hc : 0 ≤ c)
    (hyK : ∀ z, ‖y z‖ ≤ K * Real.exp (-(c * ‖z‖)))
    (hdK : ∀ z, ‖fderiv ℝ y z‖ ≤ K * Real.exp (-(c * ‖z‖))) (a : Fin 4) :
    ∀ j ≤ 1, ∃ C, ∀ z, ‖iteratedFDeriv ℝ j (fun w ↦ y w a) z‖ ≤ C := by
  have hexp (z : ℂ) : K * Real.exp (-(c * ‖z‖)) ≤ |K| := by
    have h₁ : Real.exp (-(c * ‖z‖)) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
    calc _ ≤ |K| * Real.exp (-(c * ‖z‖)) := by gcongr; exact le_abs_self _
      _ ≤ |K| := mul_le_of_le_one_right (abs_nonneg _) h₁
  intro j hj
  refine ⟨|K|, fun z ↦ ?_⟩
  interval_cases j
  · rw [norm_iteratedFDeriv_zero]
    exact (PiLp.norm_apply_le (y z) a).trans ((hyK z).trans (hexp z))
  · rw [norm_iteratedFDeriv_one]
    exact (norm_fderiv_apply_le (hy z) a).trans ((hdK z).trans (hexp z))

section EndNormalized

variable (f : ContDiffBump (0 : ℝ)) (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
  (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
  (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)

include hx hsol hlim hphase

/-- The difference of an end-normalized smooth vortex from the reference field decays, with its
derivative, like `exp (-|z| / 4)`. -/
private theorem exists_norm_sub_referenceField_le_and_norm_fderiv_le :
    ∃ K, ∀ z, ‖(x - referenceField f m) z‖ ≤ K * Real.exp (-(1 / 4 * ‖z‖)) ∧
      ‖fderiv ℝ (x - referenceField f m) z‖ ≤ K * Real.exp (-(1 / 4 * ‖z‖)) := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun w ↦ x w i) := contDiff_euclidean.1 hx i
  obtain ⟨K₀, hK₀⟩ := exists_norm_sub_referenceField_le_mul_exp (hxi 0).continuous
    (hxi 1).continuous ((hxi 2).of_le (by simp)) ((hxi 3).of_le (by simp)) hsol hlim hphase f
    (c := 1 / 4) (by norm_num)
  obtain ⟨K₁, hK₁⟩ := exists_norm_fderiv_sub_referenceField_le_mul_exp ((hxi 0).of_le (by simp))
    ((hxi 1).of_le (by simp)) ((hxi 2).of_le (by simp)) ((hxi 3).of_le (by simp)) hsol hlim hphase
    f (c := 1 / 4) (by norm_num)
  exact ⟨max K₀ K₁, fun z ↦ ⟨(hK₀ z).trans (by gcongr; exact le_max_left _ _),
    (hK₁ z).trans (by gcongr; exact le_max_right _ _)⟩⟩

/-- The Coulomb defect of an end-normalized smooth vortex relative to the reference field lies in
every Sobolev space. -/
private theorem gaugeAdjoint_referenceField_sub_mem (s : ℝ) :
    gaugeAdjoint (referenceField f m) (x - referenceField f m) ∈ realSobolevFunctions ℂ s 2 := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun w ↦ x w i) := contDiff_euclidean.1 hx i
  have hyc : ContDiff ℝ ∞ (x - referenceField f m) := hx.sub (contDiff_referenceField f m)
  have hgc : ContDiff ℝ ∞ (gaugeAdjoint (referenceField f m) (x - referenceField f m)) := by
    simpa only [gaugeFixedOperator_apply_zero] using contDiff_euclidean.1
      (contDiff_gaugeFixedOperator (contDiff_referenceField f m)
        (hyc.of_le ENat.coe_top_add_one.le)) 0
  exact mem_realSobolevFunctions_of_hasCompactSupport hgc
    (hasCompactSupport_gaugeAdjoint_referenceField_sub f ((hxi 2).of_le (by simp))
      ((hxi 3).of_le (by simp)) hsol hlim hphase) s

omit hlim hphase in
/-- The equation rows of `L_(x_m) (x - x_m)` at a smooth vortex are
`-equation x_m - quadraticTerm (x - x_m)`, by the exact quadratic expansion about `x_m`. -/
private theorem linearizedEquation_referenceField_sub_eq (z : ℂ) :
    linearizedEquation (referenceField f m) (x - referenceField f m) z =
      -equation (referenceField f m) z - quadraticTerm (x - referenceField f m) z := by
  have hyc : ContDiff ℝ ∞ (x - referenceField f m) := hx.sub (contDiff_referenceField f m)
  have h := equation_add_smul (x := referenceField f m) (y := x - referenceField f m) (z := z)
    (fun j ↦ (contDiff_euclidean.1 (contDiff_referenceField f m) j).differentiable (by simp) z)
    (fun j ↦ (contDiff_euclidean.1 hyc j).differentiable (by simp) z) 1
  simp only [one_smul, one_pow, add_sub_cancel, hsol z] at h
  ext i
  have hi := congrArg (· i) h
  simp only [PiLp.add_apply, PiLp.zero_apply] at hi
  simp only [PiLp.sub_apply, PiLp.neg_apply]
  linarith

/-- The difference of an end-normalized smooth vortex from the reference field lies in `H²`. -/
private theorem sub_referenceField_mem_sobolevFields_two :
    x - referenceField f m ∈ sobolevFields 2 := by
  set xm := referenceField f m
  set y := x - xm
  have hxmc : ContDiff ℝ ∞ xm := contDiff_referenceField f m
  have hyc : ContDiff ℝ ∞ y := hx.sub hxmc
  obtain ⟨K, hK⟩ := exists_norm_sub_referenceField_le_and_norm_fderiv_le f hx hsol hlim hphase
  have hy₁ : y ∈ sobolevFields 1 := mem_sobolevFields_one_of_norm_le_mul_exp
    (hyc.of_le (by simp)) (by norm_num) (fun z ↦ (hK z).1) fun z ↦ (hK z).2
  -- Smooth coefficients with bounded first derivatives, such as the coordinates of `y` and of
  -- the reference field, preserve `H¹`.
  have hmul {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
      (hb : ∀ j ≤ 1, ∃ C, ∀ z, ‖iteratedFDeriv ℝ j ψ z‖ ≤ C) (b : Fin 4) :
      (fun z ↦ ψ z * y z b) ∈ realSobolevFunctions ℂ 1 2 := by
    simpa using mul_mem_realSobolevFunctions_of_bounded_derivatives (p := 2) (by norm_num)
      (by norm_num) 1 hψ hb (by simpa using mem_sobolevFields.1 hy₁ b)
  have hyy (a b : Fin 4) : (fun z ↦ y z a * y z b) ∈ realSobolevFunctions ℂ 1 2 :=
    hmul (contDiff_euclidean.1 hyc a) (exists_forall_norm_iteratedFDeriv_apply_le
      (hyc.differentiable (by simp)) (by norm_num) (fun z ↦ (hK z).1) (fun z ↦ (hK z).2) a) b
  -- `L_(x_m) y ∈ H¹`: the Coulomb row, and the rows `-equation x_m - quadraticTerm y`.
  have hL : gaugeFixedOperator xm y ∈ sobolevFields 1 := by
    have hrow (i : Fin 3) :
        (fun z ↦ linearizedEquation xm y z i) ∈ realSobolevFunctions ℂ 1 2 := by
      convert sub_mem (neg_mem (equation_referenceField_apply_mem_realSobolevFunctions f m 1 i))
        (quadraticTerm_apply_mem_realSobolevFunctions_of_mul_mem hyy i) using 1
      ext z
      simp [linearizedEquation_referenceField_sub_eq f hx hsol z, xm, y]
    refine mem_sobolevFields.2 fun i ↦ ?_
    fin_cases i
    · simpa only [Fin.zero_eta, gaugeFixedOperator_apply_zero] using
        gaugeAdjoint_referenceField_sub_mem f hx hsol hlim hphase 1
    · simpa using hrow 0
    · simpa using hrow 1
    · simpa using hrow 2
  -- `L_(x_m) - L₀` multiplies `y` by the reference coordinates.
  have hdiff : gaugeFixedOperator xm y - gaugeFixedOperator vacuumField y ∈ sobolevFields 1 :=
    gaugeFixedOperator_sub_mem_sobolevFields_of_mul_mem hy₁ fun a b ↦
      hmul (contDiff_euclidean.1 hxmc a)
        (fun j _ ↦ exists_norm_iteratedFDeriv_referenceField_apply_le f m a j) b
  -- Elliptic regularity of the vacuum operator `L₀` gives `y ∈ H²`.
  have h := mem_sobolevFields_add_one_of_gaugeFixedOperator le_rfl hy₁ (hyc.of_le (by simp))
    (by simpa only [sub_sub_cancel] using sub_mem hL hdiff)
  norm_num at h
  exact h

/-- **End-normalized vortices lie in every `A_m^s`.** Let `x` be a smooth plane vortex with
`|α| → 1` at infinity whose section is `|α|` times the winding phase `(z / |z|)^m` outside a
compact set. Then `x` lies in the affine Sobolev space `A_m^s` of framed degree-`m` fields for
every order `s`. -/
theorem mem_framedFieldSpace_of_sectionValue_eq_norm_mul_windingPhase (s : ℝ) :
    x ∈ framedFieldSpace f m s := by
  -- From `A_m^2` the elliptic bootstrap raises the order one step at a time.
  have hj (j : ℕ) : x ∈ framedFieldSpace f m j :=
    mem_framedFieldSpace_of_equation_eq_zero_of_gaugeAdjoint_mem (k := 2) (by norm_num)
      (fun j ↦ referenceField_mem_framedFieldSpace f m j)
      ((contDiff_referenceField f m).of_le (by simp))
      (mem_framedFieldSpace.2 (by exact_mod_cast
        sub_referenceField_mem_sobolevFields_two f hx hsol hlim hphase))
      (hx.of_le (by simp)) hsol
      (fun j ↦ gaugeAdjoint_referenceField_sub_mem f hx hsol hlim hphase j) j
  exact framedFieldSpace_mono f m (Nat.le_ceil s) (hj ⌈s⌉₊)

end EndNormalized

/-! ### Framed gauge orbits -/

/-- **Smooth framed vortices have representatives in every `A_m^s`.** Every smooth plane vortex
with the degree-`m` end framing `α (z / |z|)⁻ᵐ → 1` is equivalent under the smooth framed gauge
group to a vortex lying in the affine Sobolev space `A_m^s` for every order `s`. -/
theorem exists_framedGaugeGroup_smul_mem_framedFieldSpace (f : ContDiffBump (0 : ℝ))
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ u : framedGaugeGroup, ∀ s : ℝ, u • x ∈ framedFieldSpace f m s := by
  obtain ⟨u, hu⟩ := exists_framedGaugeGroup_sectionValue_smul_eq hx hframe
  obtain ⟨hy, hysol, hyframe⟩ := mem_framedVortexSubMulAction.1 <|
    (framedVortexSubMulAction m).smul_mem u (mem_framedVortexSubMulAction.2 ⟨hx, hsol, hframe⟩)
  exact ⟨u, mem_framedFieldSpace_of_sectionValue_eq_norm_mul_windingPhase f hy hysol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hyframe) hu⟩

/-- **Framed vortices in every `A_m^s` with prescribed zeros.** For every effective divisor
`D ∈ Sym ℂ m`, repeated points allowed, there is a smooth solution `x` of the vortex equations,
lying in the affine Sobolev space `A_m^s` for every order `s`, whose section has the degree-`m` end
framing `α (z / |z|)⁻ᵐ → 1` and vanishes exactly at the points of `D`, to the order of their
multiplicities. -/
theorem exists_contDiff_equation_eq_zero_mem_framedFieldSpace (f : ContDiffBump (0 : ℝ))
    (D : Sym ℂ m) :
    ∃ x : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ x ∧ (∀ z, equation x z = 0) ∧
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) ∧
      IsZeroMultiplicity (sectionValue x) (fun z ↦ (D : Multiset ℂ).count z) ∧
      ∀ s : ℝ, x ∈ framedFieldSpace f m s := by
  obtain ⟨x, hx, hsol, hframe, hD⟩ := exists_contDiff_equation_eq_zero_isZeroMultiplicity D
  obtain ⟨u, hu⟩ := exists_framedGaugeGroup_smul_mem_framedFieldSpace f hx hsol hframe
  obtain ⟨hy, hysol, hyframe⟩ := mem_framedVortexSubMulAction.1 <|
    (framedVortexSubMulAction m).smul_mem u (mem_framedVortexSubMulAction.2 ⟨hx, hsol, hframe⟩)
  exact ⟨u • x, hy, hysol, hyframe, isZeroMultiplicity_sectionValue_framedGaugeGroup_smul hD u, hu⟩

/-- **Vortices of `A_m^k` with the same divisor are `G_(k+1)`-equivalent.** For an integer `k ≥ 2`,
two smooth framed degree-`m` vortices lying in `A_m^k` with the same divisor differ by an element
of the Sobolev gauge group `G_(k+1)`. -/
theorem exists_mem_sobolevGaugeGroup_gaugeTransform_eq {f : ContDiffBump (0 : ℝ)} {k : ℕ}
    (hk : 1 < k) {v w : framedVortexSubMulAction m}
    (hv : (v : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ framedFieldSpace f m k)
    (hw : (w : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ framedFieldSpace f m k)
    (hD : framedVortexDivisor v = framedVortexDivisor w) :
    ∃ u ∈ sobolevGaugeGroup (s := k + 1) (by norm_cast; omega), gaugeTransform u w = v := by
  obtain ⟨u, hu⟩ := framedVortexDivisor_eq_framedVortexDivisor_iff.1 hD
  have huw : gaugeTransform u w = v := by
    simpa only [Subtype.ext_iff, SubMulAction.val_smul, framedGaugeGroup_smul] using hu
  refine ⟨u, mem_sobolevGaugeGroup_of_mem_framedFieldSpace hk hw ?_ (huw ▸ hv), huw⟩
  exact ((mem_framedGaugeGroup _).1 u.2).1.of_le (by simp)

end TauCeti.Vortex
