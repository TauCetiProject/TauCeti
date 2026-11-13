/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.LogVariation
public import TauCeti.Analysis.PDE.Vortex.PrincipalPart
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Analysis.PDE.Vortex.Divisor
import TauCeti.Analysis.PDE.Vortex.ExteriorEstimate
import TauCeti.Analysis.PDE.Vortex.ZeroMode
import Mathlib.Algebra.Polynomial.Basis

/-!
# Kernel elements of the linearized vortex operator with prescribed principal parts

Let `x` be a smooth plane vortex, with section `α` and `P = |α|² / 4`, and let `ν` be an
integrating factor of its holomorphicity rows, `∂bar ν = (b₂ - i b₁) / 2`, so that `α = e^ν f` with
`f` entire (`TauCeti.Vortex.differentiable_exp_neg_mul_sectionValue`). A variation `y` in the
kernel of the gauge-fixed operator `L_x = d₀* ⊕ d₁` has section variation `δα = α G + e^ν H` with
`G` regular and `H` entire (`TauCeti.Vortex.exists_sectionValue_eq_mul_add_exp_mul`), and the
derivatives of `H` below the zero multiplicities of `α` are its principal-part data
(`TauCeti.Vortex.principalPart`): the principal parts of `δα / α = G + H / f` at the zeros of `α`.
For a framed vortex of degree `m` these data form `m` complex numbers. A continuous `L²` kernel
element whose quotient `δα / α` is regular vanishes
(`TauCeti.Vortex.eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto`), so a
kernel element is determined by its principal-part data, and spaces of such kernel elements have
real dimension at most `2 m`
(`TauCeti.Vortex.finrank_le_two_mul_of_forall_sectionValue_eq_mul_eq_zero`).

This file proves the converse: every entire `H` is realized. There is a smooth square-integrable
`y` with `L_x y = 0` everywhere and `δα = α G + e^ν H`, `G` smooth
(`TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_and_sectionValue_eq_mul_add_exp_mul`). So
every principal part `H⁽ʲ⁾(a)`, `j < n(a)`, is attained by a kernel element
(`TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_and_principalPart_eq`), and at a framed vortex
of degree `m` the smooth `L²` kernel of `L_x` contains `2 m` linearly independent elements
(`TauCeti.Vortex.exists_linearIndependent_gaugeFixedOperator_eq_zero`): the real dimension of the
tangent space of the divisor space `Sym^m ℂ`.

`TauCeti.Analysis.PDE.Vortex.KernelExistence` and `TauCeti.Analysis.PDE.Vortex.ZeroMode` realize
each pole `c / (w - z)^(j+1)` separately, one zero `z` and one order `j` at a time, given a local
factorization of `α` at `z`
(`TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_sectionValue_eq_mul_div_pow_add`,
`TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_eq_logVariation`). Their kernel elements have a
smooth but not holomorphic remainder in `δα / α`, so their principal-part data
`TauCeti.Vortex.principalPart` are not read off from those statements. This file instead
parametrizes kernel elements by the entire function `H` of the decomposition `δα = α G + e^ν H`
used by `TauCeti.Vortex.principalPart` and `TauCeti.Vortex.principalPartMap`, at all zeros at
once and without local factorizations. The principal-part data of the kernel element are then the
derivatives of `H`, which is what the linear independence argument and the injectivity of
`TauCeti.Vortex.principalPartMap` both use.

The construction follows Samols. Off the zeros of `α`, kernel elements are the logarithmic
variations (`TauCeti.Vortex.logVariation`) of solutions of `Δη = P η`, `η = δα / α`. The
meromorphic function `E = H / f = e^ν H / α` is harmonic off the zeros, but `P E` does not vanish,
and `E` need not be square integrable. Cut it off: for a smooth compactly supported `ρ` equal to
one near the zeros of `α`, put `σ = (1 - ρ) E`, which is smooth, and look for
`η = h - σ + E = h + ρ E` with `h` and `Dh` square integrable. The equation `Δη = P η` becomes
the stationary Schrödinger equation `-Δh + P h = P σ - Δσ - conj(α) e^ν H / 4`, whose right side
is smooth and vanishes where `ρ = 0`, because there `σ = E` and `P E = conj(α) e^ν H / 4`. The
potential `P` is nonnegative and tends to `1 / 4` at infinity, so the equation has a smooth
solution `h ∈ H²(ℂ; ℂ)` (`TauCeti.Vortex.exists_contDiff_laplacian_eq_mul_sub`). The kernel
element is the logarithmic variation of `h - σ` plus the variation of the section alone by
`e^ν H` (`TauCeti.Vortex.sectionVariation`). Off the zeros it is the logarithmic variation of
`η`, so `L_x y = 0` there by
`TauCeti.Vortex.gaugeFixedOperator_logVariation_eq_zero_iff`, and by continuity everywhere. Its
section variation is `α (h - σ) + e^ν H = α h + ρ e^ν H`.

## Main results

All in the namespace `TauCeti.Vortex`:

* `exists_gaugeFixedOperator_eq_zero_and_sectionValue_eq_mul_add_exp_mul`: for every entire `H`
  there is a smooth `L²` kernel element of `L_x` with section variation `α G + e^ν H`.
* `exists_gaugeFixedOperator_eq_zero_and_principalPart_eq`: its principal-part data are the
  derivatives of `H` below the zero multiplicities of `α`.
* `exists_linearIndependent_gaugeFixedOperator_eq_zero`: at a smooth framed vortex of degree `m`
  there are `2 m` linearly independent smooth `L²` kernel elements of `L_x`.

## References

* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179, Section 3.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Metric Set
open scoped ContDiff Laplacian Topology

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### The cut-off meromorphic part

Throughout, `f = e^(-ν) α` is entire (`differentiable_exp_neg_mul_sectionValue`), `H` is entire,
and `E = H / f`. The function `ρ` is smooth, compactly supported, and equal to one on the ball of
radius `R`, outside which `α` has no zeros. -/

section Cutoff

variable {ν H : ℂ → ℂ} {ρ : ℂ → ℝ} {R : ℝ}

/-- Off the zeros of `α`, the quotient `H / (e^(-ν) α)` is analytic. -/
private theorem analyticAt_div (hf : Differentiable ℂ fun w ↦ exp (-ν w) * sectionValue x w)
    (hH : Differentiable ℂ H) {z : ℂ} (hz : sectionValue x z ≠ 0) :
    AnalyticAt ℂ (fun w ↦ H w / (exp (-ν w) * sectionValue x w)) z :=
  (hH.analyticAt z).div (hf.analyticAt z) (mul_ne_zero (exp_ne_zero _) hz)

/-- `α E = e^ν H` off the zeros of `α`. -/
private theorem sectionValue_mul_div {z : ℂ} (hz : sectionValue x z ≠ 0) :
    sectionValue x z * (H z / (exp (-ν z) * sectionValue x z)) = exp (ν z) * H z := by
  rw [exp_neg]
  field_simp

/-- `P E = conj(α) e^ν H / 4` off the zeros of `α`. -/
private theorem potential_mul_div {z : ℂ} (hz : sectionValue x z ≠ 0) :
    ((x z 2 ^ 2 + x z 3 ^ 2 : ℝ) : ℂ) * (H z / (exp (-ν z) * sectionValue x z)) =
      starRingEnd ℂ (sectionValue x z) * (exp (ν z) * H z) / 4 := by
  rw [ofReal_potential_eq, ← sectionValue_mul_div hz]
  ring

/-- The cut-off part `σ = (1 - ρ) E` is smooth: it vanishes near the zeros of `α`, and away from
them `E` is analytic. -/
private theorem contDiff_cutoff (hf : Differentiable ℂ fun w ↦ exp (-ν w) * sectionValue x w)
    (hH : Differentiable ℂ H) (hρ : ContDiff ℝ ∞ ρ) (hρR : ∀ z, ‖z‖ < R → ρ z = 1)
    (hR : ∀ z, R ≤ ‖z‖ → sectionValue x z ≠ 0) :
    ContDiff ℝ ∞ fun w ↦ ((1 - ρ w : ℝ) : ℂ) * (H w / (exp (-ν w) * sectionValue x w)) := by
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  rcases lt_or_ge ‖z‖ R with hz | hz
  · refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hz] with w hw
    simp [hρR w hw]
  · exact (ofRealCLM.contDiff.comp (contDiff_const.sub hρ)).contDiffAt.mul
      ((analyticAt_div hf hH (hR z hz)).contDiffAt.restrict_scalars ℝ)

/-- Outside the support of `ρ`, the section has no zero. -/
private theorem sectionValue_ne_zero_of_notMem_tsupport (hρR : ∀ z, ‖z‖ < R → ρ z = 1)
    (hR : ∀ z, R ≤ ‖z‖ → sectionValue x z ≠ 0) {z : ℂ} (hz : z ∉ tsupport ρ) :
    sectionValue x z ≠ 0 := by
  refine hR z (not_lt.1 fun h ↦ hz (subset_tsupport _ ?_))
  simp [hρR z h]

/-- Outside the support of `ρ`, the cut-off part `σ = (1 - ρ) E` agrees with `E` near the
point. -/
private theorem cutoff_eventuallyEq {z : ℂ} (hz : z ∉ tsupport ρ) :
    (fun w ↦ ((1 - ρ w : ℝ) : ℂ) * (H w / (exp (-ν w) * sectionValue x w))) =ᶠ[𝓝 z]
      fun w ↦ H w / (exp (-ν w) * sectionValue x w) := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hz] with w hw
  simp [hw]

/-- Outside the support of `ρ`, the source `P σ - Δσ - conj(α) e^ν H / 4` of the equation for
the part `h` vanishes: there `σ = E` is harmonic and `P E = conj(α) e^ν H / 4`. -/
private theorem source_eq_zero_of_notMem_tsupport
    (hf : Differentiable ℂ fun w ↦ exp (-ν w) * sectionValue x w) (hH : Differentiable ℂ H)
    (hρR : ∀ z, ‖z‖ < R → ρ z = 1) (hR : ∀ z, R ≤ ‖z‖ → sectionValue x z ≠ 0) {z : ℂ}
    (hz : z ∉ tsupport ρ) :
    ((x z 2 ^ 2 + x z 3 ^ 2 : ℝ) : ℂ) *
        (((1 - ρ z : ℝ) : ℂ) * (H z / (exp (-ν z) * sectionValue x z))) -
      Δ (fun w ↦ ((1 - ρ w : ℝ) : ℂ) * (H w / (exp (-ν w) * sectionValue x w))) z -
      starRingEnd ℂ (sectionValue x z) * (exp (ν z) * H z) / 4 = 0 := by
  have hα := sectionValue_ne_zero_of_notMem_tsupport hρR hR hz
  have hloc := cutoff_eventuallyEq (x := x) (ν := ν) (H := H) hz
  rw [(InnerProductSpace.laplacian_congr_nhds hloc).eq_of_nhds,
    (analyticAt_div hf hH hα).harmonicAt.2.eq_of_nhds, hloc.eq_of_nhds, potential_mul_div hα]
  simp

/-- Outside the support of `ρ`, the logarithmic variation of `σ = (1 - ρ) E` is the variation of
the section alone by `α E = e^ν H`. -/
private theorem logVariation_cutoff_of_notMem_tsupport
    (hf : Differentiable ℂ fun w ↦ exp (-ν w) * sectionValue x w) (hH : Differentiable ℂ H)
    (hρR : ∀ z, ‖z‖ < R → ρ z = 1) (hR : ∀ z, R ≤ ‖z‖ → sectionValue x z ≠ 0) {z : ℂ}
    (hz : z ∉ tsupport ρ) :
    logVariation x (fun w ↦ ((1 - ρ w : ℝ) : ℂ) * (H w / (exp (-ν w) * sectionValue x w))) z =
      sectionVariation (fun w ↦ exp (ν w) * H w) z := by
  have hα := sectionValue_ne_zero_of_notMem_tsupport hρR hR hz
  rw [logVariation_congr_nhds x (cutoff_eventuallyEq hz),
    logVariation_eq_of_differentiableAt x (analyticAt_div hf hH hα).differentiableAt]
  exact apply_eq_of_sectionValue_eq (by simp) (by simp) (by simp [sectionValue_mul_div hα])

end Cutoff

/-! ### The kernel element -/

/-- **The kernel equation off the zeros.** Let `x` be a smooth field satisfying the holomorphicity
rows, with `|α|² → 1` at infinity, and `α = e^ν f`, `f` entire; let `H` be entire and let `σ`,
`h` be smooth with

`-Δh + P h = P σ - Δσ - conj(α) e^ν H / 4`.

Then the logarithmic variation of `h - σ` plus the variation of the section alone by `e^ν H` lies
in the kernel of `L_x`. Off the zeros of `α` it is the logarithmic variation of
`η = h - σ + H / f`, which solves `Δη = P η`; at the finitely many zeros, continuity takes over. -/
private theorem gaugeFixedOperator_logVariation_add_sectionVariation_eq_zero {ν H σ h : ℂ → ℂ}
    (hx : ContDiff ℝ ∞ x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hν : ContDiff ℝ ∞ ν) (hf : Differentiable ℂ fun w ↦ exp (-ν w) * sectionValue x w)
    (hH : Differentiable ℂ H) (hσ : ContDiff ℝ ∞ σ) (hh : ContDiff ℝ ∞ h)
    (heq : ∀ z, -Δ h z + ((x z 2 ^ 2 + x z 3 ^ 2 : ℝ) : ℂ) * h z =
      ((x z 2 ^ 2 + x z 3 ^ 2 : ℝ) : ℂ) * σ z - Δ σ z -
        starRingEnd ℂ (sectionValue x z) * (exp (ν z) * H z) / 4) (z : ℂ) :
    gaugeFixedOperator x
      (logVariation x (h - σ) + sectionVariation fun w ↦ exp (ν w) * H w) z = 0 := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.mp hx i
  have hdi (i : Fin 4) : Differentiable ℝ (fun z ↦ x z i) := (hxi i).differentiable (by simp)
  have hfin := finite_setOfPred_sectionValue_eq_zero (k := 1) le_rfl ((hxi 0).of_le (by simp))
    ((hxi 1).of_le (by simp)) (hdi 2) (hdi 3) hhol hlim
  have hdense : Dense {w | sectionValue x w ≠ 0} := by
    simpa only [compl_ofPred] using Set.Countable.dense_compl ℝ hfin.countable
  have hG : ContDiff ℝ ∞ (h - σ) := hh.sub hσ
  have hy : ContDiff ℝ ∞ (logVariation x (h - σ) + sectionVariation fun w ↦ exp (ν w) * H w) :=
    (contDiff_logVariation hx (by simpa using hG)).add
      (contDiff_sectionVariation (hν.cexp.mul (hH.contDiff.restrict_scalars ℝ)))
  have hcont := (contDiff_gaugeFixedOperator (n := 0) (hx.of_le (by simp))
    (hy.of_le (by simp))).continuous
  refine congrFun (hcont.ext_on hdense continuous_const fun w hw ↦ ?_) z
  -- Off the zeros, the variation is the logarithmic variation of `η = h - σ + H / f`.
  set E : ℂ → ℂ := fun w ↦ H w / (exp (-ν w) * sectionValue x w)
  have hU : IsOpen {w | sectionValue x w ≠ 0} :=
    isOpen_ne_fun (contDiff_sectionValue (hxi 2) (hxi 3)).continuous continuous_const
  have hloc : (logVariation x (h - σ) + sectionVariation fun w ↦ exp (ν w) * H w) =ᶠ[𝓝 w]
      logVariation x (h - σ + E) := by
    filter_upwards [hU.mem_nhds hw] with v hv
    have hEv := (analyticAt_div hf hH hv).differentiableAt
    rw [logVariation_add_apply x (hG.differentiable (by simp) v) (hEv.restrictScalars ℝ),
      logVariation_eq_of_differentiableAt x hEv, Pi.add_apply]
    congr 1
    exact apply_eq_of_sectionValue_eq (by simp) (by simp) (by simp [sectionValue_mul_div hv])
  have hE := analyticAt_div hf hH hw
  have hG2 : ContDiffAt ℝ 2 (h - σ) w := (hG.of_le (by simp)).contDiffAt
  have hE2 : ContDiffAt ℝ 2 E w := hE.contDiffAt.restrict_scalars ℝ
  have hη2 : ContDiffAt ℝ 2 (h - σ + E) w := hG2.add hE2
  rw [gaugeFixedOperator_congr_nhds x hloc,
    gaugeFixedOperator_logVariation_eq_zero_iff ((hx.differentiable (by simp)).differentiableAt)
      hη2 (hhol w).1 (hhol w).2, hG2.laplacian_add hE2, hE.harmonicAt.2.eq_of_nhds,
    (hh.of_le (by simp)).contDiffAt.laplacian_sub (hσ.of_le (by simp)).contDiffAt,
    Complex.real_smul]
  have hPE := potential_mul_div (H := H) (ν := ν) hw
  simp only [E, Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hPE ⊢
  linear_combination -heq w - hPE

/-- **Kernel elements with prescribed holomorphic part.** Let `x` be a smooth field satisfying the
holomorphicity rows of the vortex equation, with `|α|² → 1` at infinity, and let `ν` be smooth with
`∂bar ν = (b₂ - i b₁) / 2`. For every entire `H` there is a smooth square-integrable variation `y`
in the kernel of the gauge-fixed operator `L_x`, whose section variation is `δα = α G + e^ν H` with
`G` smooth. -/
theorem exists_gaugeFixedOperator_eq_zero_and_sectionValue_eq_mul_add_exp_mul
    (hx : ContDiff ℝ ∞ x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {ν : ℂ → ℂ} (hν : ContDiff ℝ ∞ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y ∧ MemLp y 2 volume ∧
      (∀ z, gaugeFixedOperator x y z = 0) ∧ ∃ G : ℂ → ℂ, ContDiff ℝ ∞ G ∧
        ∀ z, sectionValue y z = sectionValue x z * G z + exp (ν z) * H z := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.mp hx i
  have hf : Differentiable ℂ fun w ↦ exp (-ν w) * sectionValue x w :=
    differentiable_exp_neg_mul_sectionValue ((hxi 2).differentiable (by simp))
      ((hxi 3).differentiable (by simp)) hhol (hν.differentiable (by simp)) hνeq
  have hHs : ContDiff ℝ ∞ H := hH.contDiff.restrict_scalars ℝ
  -- A cutoff `ρ` equal to one on a disc outside which `α` has no zeros.
  obtain ⟨R, hR0, hR⟩ := exists_exterior_lt_mass hlim (by norm_num : (0 : ℝ) < 1 / 4)
  have hαR (z : ℂ) (hz : R + 1 ≤ ‖z‖) : sectionValue x z ≠ 0 := by
    rw [Ne, sectionValue_eq_zero_iff]
    exact (hR z (by linarith)).ne'
  let ρ : ContDiffBump (0 : ℂ) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  have hρR (z : ℂ) (hz : ‖z‖ < R + 1) : ρ z = 1 :=
    ρ.one_of_mem_closedBall (by simpa using hz.le)
  -- The cut-off part `σ = (1 - ρ) E` and the source `P σ - Δσ - conj(α) e^ν H / 4`.
  set σ : ℂ → ℂ := fun w ↦ ((1 - ρ w : ℝ) : ℂ) * (H w / (exp (-ν w) * sectionValue x w))
  have hσ : ContDiff ℝ ∞ σ := contDiff_cutoff hf hH ρ.contDiff hρR hαR
  set g : ℂ → ℂ := fun w ↦ ((x w 2 ^ 2 + x w 3 ^ 2 : ℝ) : ℂ) * σ w - Δ σ w -
    starRingEnd ℂ (sectionValue x w) * (exp (ν w) * H w) / 4
  have hg : ContDiff ℝ ∞ g :=
    (((ofRealCLM.contDiff.comp (((hxi 2).pow 2).add ((hxi 3).pow 2))).mul hσ).sub
      (hσ.laplacian (by simp))).sub (((conjCLE.contDiff.comp
        (contDiff_sectionValue (hxi 2) (hxi 3))).mul (hν.cexp.mul hHs)).div_const 4)
  -- Where `ρ = 0`, `σ = E` and the source vanishes.
  have hgc : HasCompactSupport g := ρ.hasCompactSupport.mono' fun z hz ↦
    by_contra fun hzρ ↦ hz (source_eq_zero_of_notMem_tsupport hf hH hρR hαR hzρ)
  -- Solve `-Δh + P h = g` with a smooth `h ∈ H²(ℂ; ℂ)`.
  obtain ⟨h, hh, hh₁, hh₂, hΔh⟩ := exists_contDiff_laplacian_eq_mul_sub hx hlim hg
    (hg.continuous.memLp_of_hasCompactSupport hgc)
  have heq (w : ℂ) : -Δ h w + ((x w 2 ^ 2 + x w 3 ^ 2 : ℝ) : ℂ) * h w = g w := by
    linear_combination -hΔh w
  have hG : ContDiff ℝ ∞ (h - σ) := hh.sub hσ
  refine ⟨logVariation x (h - σ) + sectionVariation fun w ↦ exp (ν w) * H w,
    (contDiff_logVariation hx (by simpa using hG)).add
      (contDiff_sectionVariation (hν.cexp.mul hHs)), ?_,
    gaugeFixedOperator_logVariation_add_sectionVariation_eq_zero hx hhol hlim hν hf hH hσ hh heq,
    h - σ, hG, fun z ↦ ?_⟩
  · -- The variation is `logVariation x h` plus a smooth compactly supported correction.
    set c := (sectionVariation fun w ↦ exp (ν w) * H w) - logVariation x σ
    have hc : Continuous c := ((contDiff_sectionVariation (hν.cexp.mul hHs)).sub
      (contDiff_logVariation hx (by simpa using hσ))).continuous
    have hcc : HasCompactSupport c := ρ.hasCompactSupport.mono' fun z hz ↦
      by_contra fun hzρ ↦ hz (sub_eq_zero.2
        (logVariation_cutoff_of_notMem_tsupport hf hH hρR hαR hzρ).symm)
    have e : logVariation x (h - σ) + (sectionVariation fun w ↦ exp (ν w) * H w) =
        logVariation x h + c := by
      rw [logVariation_sub x (hh.differentiable (by simp)) (hσ.differentiable (by simp))]
      simp only [c]
      abel
    rw [e]
    exact (memLp_logVariation_of_mem_realSobolevFunctions
      (memLp_top_apply hx.continuous hlim (by simp)) (memLp_top_apply hx.continuous hlim (by simp))
      (hh.of_le (by simp)) hh₁ hh₂).add (hc.memLp_of_hasCompactSupport hcc)
  · rw [sectionValue_add, sectionValue_logVariation, sectionValue_sectionVariation]

/-- **Every principal part is realized by a kernel element.** Under the hypotheses of
`TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_and_sectionValue_eq_mul_add_exp_mul`, let `n` be
the zero multiplicities of `α`. For every entire `H` there is a smooth square-integrable `y` in the
kernel of `L_x` whose principal-part data at each `z` are the derivatives `H⁽ʲ⁾(z)`, `j < n z`. -/
theorem exists_gaugeFixedOperator_eq_zero_and_principalPart_eq
    (hx : ContDiff ℝ ∞ x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {n : ℂ → ℕ} (hα : IsZeroMultiplicity (sectionValue x) n) {ν : ℂ → ℂ} (hν : ContDiff ℝ ∞ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y ∧ MemLp y 2 volume ∧
      (∀ z, gaugeFixedOperator x y z = 0) ∧
        ∀ z, ∀ j < n z, principalPart x ν y z j = iteratedDeriv j H z := by
  obtain ⟨y, hy, hy₂, hker, G, hG, hyG⟩ :=
    exists_gaugeFixedOperator_eq_zero_and_sectionValue_eq_mul_add_exp_mul hx hhol hlim hν hνeq hH
  exact ⟨y, hy, hy₂, hker, fun z j hj ↦
    principalPart_eq_iteratedDeriv hα hν.continuous hG.continuous hH hyG hj⟩

/-! ### `2 m` independent kernel elements at a framed vortex -/

/-- **`2 m` independent kernel elements at a framed vortex.** Let `x` be a smooth field satisfying
the holomorphicity rows of the vortex equation, with the degree-`m` end framing
`α(z) (z / |z|)⁻ᵐ → 1`. Then there are `2 m` real-linearly independent smooth square-integrable
variations in the kernel of the gauge-fixed operator `L_x`. They are indexed by `Fin m × Fin 2`
and realize the holomorphic parts `H = z ^ j` and `H = i z ^ j`, `j < m`. Their number is the real
dimension of the tangent space of the divisor space `Sym^m ℂ`. -/
theorem exists_linearIndependent_gaugeFixedOperator_eq_zero {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ y : Fin m × Fin 2 → ℂ → EuclideanSpace ℝ (Fin 4), LinearIndependent ℝ y ∧
      ∀ i, ContDiff ℝ ∞ (y i) ∧ MemLp (y i) 2 volume ∧ ∀ z, gaugeFixedOperator x (y i) z = 0 := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.mp hx i
  have hdi (i : Fin 4) : Differentiable ℝ (fun z ↦ x z i) := (hxi i).differentiable (by simp)
  have hlim := tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe
  obtain ⟨ν, hν, hνeq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eq (n := ⊤) le_top
    (contDiff_connectionCoeff (hxi 0) (hxi 1))
  obtain ⟨D, hD⟩ := exists_sym_sectionValue_eq_pow_count_mul (k := ⊤) le_top (hxi 0) (hxi 1)
    (hdi 2) (hdi 3) hhol hframe
  have hα : IsZeroMultiplicity (sectionValue x) fun z ↦ Multiset.count z (D : Multiset ℂ) :=
    isZeroMultiplicity_iff.2 fun z ↦ by
      obtain ⟨v, hv, hv₀, hvf⟩ := hD z
      exact ⟨v, hv.continuousAt, hv₀, hvf⟩
  -- Kernel elements realizing `H = c z ^ j`, `c ∈ {1, i}`, `j < m`.
  set c : Fin 2 → ℂ := ![1, I]
  have hH (i : Fin m × Fin 2) : Differentiable ℂ fun z : ℂ ↦ c i.2 * z ^ (i.1 : ℕ) := by fun_prop
  choose y hy hy₂ hker G hG hyG using fun i ↦
    exists_gaugeFixedOperator_eq_zero_and_sectionValue_eq_mul_add_exp_mul hx hhol hlim hν hνeq
      (hH i)
  refine ⟨y, Fintype.linearIndependent_iff.2 fun t ht i ↦ ?_, fun i ↦ ⟨hy i, hy₂ i, hker i⟩⟩
  -- The section of `∑ t i • y i = 0` is `α ∑ t i G i + e^ν q`, with `q = ∑ t i c z ^ j`.
  set q : Polynomial ℂ := ∑ i, Polynomial.C ((t i : ℂ) * c i.2) * Polynomial.X ^ (i.1 : ℕ)
  have hqeval (z : ℂ) : q.eval z = ∑ i, (t i : ℂ) * (c i.2 * z ^ (i.1 : ℕ)) := by
    simp [q, Polynomial.eval_finsetSum, mul_assoc]
  let L (z : ℂ) : (ℂ → EuclideanSpace ℝ (Fin 4)) →ₗ[ℝ] ℂ :=
    { toFun := fun v ↦ sectionValue v z
      map_add' := fun a b ↦ sectionValue_add a b z
      map_smul' := fun r a ↦ by simp [Complex.real_smul] }
  have hsec (z : ℂ) : sectionValue x z * ∑ i, (t i : ℂ) * G i z + exp (ν z) * q.eval z = 0 := by
    have h := congrArg (L z) ht
    simp only [map_sum, map_smul, map_zero] at h
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, hyG, Complex.real_smul] at h
    rw [hqeval, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← h]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  -- So the derivatives of `q` below the multiplicities of `D` vanish, and `q = 0`.
  have hq0 : q = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_isRoot_iterate_derivative (D := D)
      ?_ fun a j hj ↦ ?_
    · have hm : 0 < m := i.1.pos
      rw [Sym.card_coe]
      refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := m - 1)
        fun k _ ↦ (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)) (by omega)
    · rw [Polynomial.IsRoot, ← congrFun (Polynomial.iteratedDeriv q j) a]
      simpa using hα.iteratedDeriv_eq_of_eventually_mul_add_mul_eq
        (G₁ := fun z ↦ ∑ i, (t i : ℂ) * G i z) (H₁ := fun z ↦ q.eval z) (H₂ := 0) (G₂ := 0)
        hν.continuous.cexp.continuousAt (exp_ne_zero _)
        (continuous_finsetSum _ fun k _ ↦ continuous_const.mul (hG k).continuous).continuousAt
        continuousAt_const ((Polynomial.differentiable q).analyticAt a) analyticAt_const
        (Eventually.of_forall fun w ↦ by simpa using hsec w) hj
  -- The polynomials `c X ^ j` are real-linearly independent, as part of the basis
  -- `{X ^ j, i X ^ j}` of `ℂ[X]` over `ℝ`.
  have hli : LinearIndependent ℝ fun i : Fin m × Fin 2 ↦
      c i.2 • (Polynomial.X : Polynomial ℂ) ^ (i.1 : ℕ) := by
    convert (Complex.basisOneI.smulTower' (Polynomial.basisMonomials ℂ)).linearIndependent.comp
      (fun i : Fin m × Fin 2 ↦ ((i.1 : ℕ), i.2))
      (fun i k h ↦ Prod.ext (Fin.ext (Prod.ext_iff.1 h).1) (Prod.ext_iff.1 h).2) using 1
    funext i
    simp [Module.Basis.smulTower'_apply, c, Polynomial.monomial_one_right_eq_X_pow]
  refine Fintype.linearIndependent_iff.1 hli t ?_ i
  rw [← hq0]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← smul_assoc, Complex.real_smul, Polynomial.smul_eq_C_mul]

end TauCeti.Vortex

end
