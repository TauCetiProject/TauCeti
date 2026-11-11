/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Distribution.TestFunction.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.LaplacianResolvent
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Integral
import TauCeti.Analysis.InnerProductSpace.WeakSolution
import TauCeti.Analysis.Sobolev.Poincare.Schrodinger
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The stationary Schrödinger equation with a potential positive at infinity

Let `E` be a finite-dimensional real inner product space and `P` a bounded measurable potential on
`E` which is nonnegative and bounded below by a constant `a > 0` outside a ball. This file solves
the stationary Schrödinger equation

`-Δh + P h = g`

on the whole space, for every `g ∈ L²(E)`, with a solution `h` in the Sobolev space `H²(E)`.

* **Weak solutions.** By the Poincaré inequality for Schrödinger forms
  (`TauCeti.exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq`)
  and Green's identity, the quadratic form of `-Δ + P` is bounded below on test functions,
  `c ∫ φ² ≤ ∫ φ (-Δφ + P φ)`, so `c ‖φ‖₂ ≤ ‖-Δφ + P φ‖₂`. Since `-Δ + P` is formally
  self-adjoint, the abstract weak right inverse
  (`LinearMap.exists_continuousLinearMap_inner_apply_eq_of_mul_norm_le`) gives a bounded operator
  `Q` on `L²(E)` of norm at most `c⁻¹` such that `Q g` is a weak solution:
  `∫ (Q g) (-Δφ + P φ) = ∫ g φ` for every compactly supported `C²` function `φ`
  (`TauCeti.exists_continuousLinearMap_integral_mul_neg_laplacian_add_mul_eq`).
* **Regularity.** A weak `L²` solution of `-Δh + P h = g` with `g ∈ L²` satisfies
  `-Δh + h = g + (1 - P) h` in the sense of tempered distributions, and the right side lies in
  `L²` because `P` is bounded. Elliptic regularity of `-Δ + 1`
  (`TemperedDistribution.memSobolev_add_two_iff_neg_laplacian_add_smul`) puts `h` in `H²(E)`
  (`TauCeti.mem_realSobolevFunctions_two_of_integral_mul_neg_laplacian_add_mul_eq`). Only the
  boundedness of `P` is used here.

Together, every `g ∈ L²(E)` has a weak solution `h ∈ H²(E)`
(`TauCeti.exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq`). Solving
for the real and imaginary parts of a complex right-hand side separately gives a complex weak
solution (`TauCeti.integrable_and_integral_mul_neg_laplacian_add_mul_eq_of_re_im`).

The potential may vanish on a large set inside the ball, so `-Δ + P` need not be bounded below
by a positive constant pointwise. A potential of this kind is `P = |α|² / 4` for the section `α`
of a plane vortex, which vanishes at the zeros of `α` and tends to `1 / 4` at infinity; the
equation `Δη = P η` for `η = δα / α` describes the infinitesimal deformations of the vortex.

## Main results

* `TauCeti.exists_continuousLinearMap_integral_mul_neg_laplacian_add_mul_eq`: the bounded weak
  solution operator of `-Δ + P` on `L²(E)`.
* `TauCeti.mem_realSobolevFunctions_two_of_integral_mul_neg_laplacian_add_mul_eq`: weak `L²`
  solutions lie in `H²(E)`.
* `TauCeti.exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq`: existence of
  an `H²` weak solution for every `L²` right-hand side.
* `TauCeti.integrable_and_integral_mul_neg_laplacian_add_mul_eq_of_re_im`: real weak solutions
  for the real and imaginary parts combine into a complex weak solution.
* `TauCeti.memLp_neg_laplacian_add_mul`: the Schrödinger operator with a bounded potential maps
  compactly supported `C²` functions into `L²`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 8 (weak solutions and their regularity).
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  Section XIII.1 (Schrödinger operators with potentials bounded below).
-/

public section

namespace TauCeti

open MeasureTheory Filter Metric TemperedDistribution
open scoped Laplacian ContDiff Gradient InnerProductSpace RealInnerProductSpace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The weak solution operator -/

section Weak

/-- The compactly supported `C²` real test functions on `E`. -/
private abbrev TestFn (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  TestFunction (⊤ : TopologicalSpace.Opens E) ℝ 2

/-- The image `-Δφ + P φ` of a compactly supported `C²` function under the Schrödinger operator
with a bounded potential `P` is square integrable. -/
theorem memLp_neg_laplacian_add_mul {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {P : E → ℝ}
    (hP : MemLp P ⊤ μ) {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    MemLp (fun z ↦ -Δ φ z + P z * φ z) 2 μ := by
  have hφ2 : MemLp φ 2 μ := hφ.continuous.memLp_of_hasCompactSupport hφc
  refine MemLp.add ?_ ?_
  · exact (hφ.continuous_laplacian.memLp_of_hasCompactSupport hφc.laplacian).neg
  · exact hP.mul hφ2

/-- The Schrödinger operator `-Δ + P` on test functions, with values in `L²`. -/
private noncomputable def schrodingerToLp {P : E → ℝ} (hP : MemLp P ⊤ volume) :
    TestFn E →ₗ[ℝ] Lp ℝ 2 (volume : Measure E) where
  toFun φ := (memLp_neg_laplacian_add_mul hP φ.contDiff φ.hasCompactSupport).toLp _
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun z ↦ ?_)
    simp only [FunLike.coe_add, Pi.add_apply,
      (φ.contDiff.contDiffAt).laplacian_add ψ.contDiff.contDiffAt]
    ring
  map_smul' t φ := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun z ↦ ?_)
    simp only [FunLike.coe_smul, Pi.smul_apply,
      InnerProductSpace.laplacian_smul t φ.contDiff.contDiffAt, smul_eq_mul]
    ring

/-- **The weak solution operator of the stationary Schrödinger equation.** Let `P` be a bounded
measurable potential on `E`, almost everywhere nonnegative and almost everywhere at least `a > 0`
outside the closed ball of radius `R`. Then there are `c > 0` and a bounded operator `Q` on
`L²(E)` with `‖Q‖ ≤ c⁻¹` such that `Q g` is a weak solution of `-Δh + P h = g` for every
`g ∈ L²(E)`: `∫ (Q g) (-Δφ + P φ) = ∫ g φ` for every compactly supported `C²` function `φ`. -/
theorem exists_continuousLinearMap_integral_mul_neg_laplacian_add_mul_eq [Nontrivial E]
    {P : E → ℝ} (hP : MemLp P ⊤ volume) (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z) :
    ∃ c > 0, ∃ Q : Lp ℝ 2 (volume : Measure E) →L[ℝ] Lp ℝ 2 (volume : Measure E),
      ‖Q‖ ≤ c⁻¹ ∧ ∀ (g : Lp ℝ 2 (volume : Measure E)) (φ : E → ℝ), ContDiff ℝ 2 φ →
        HasCompactSupport φ → ∫ z, Q g z * (-Δ φ z + P z * φ z) = ∫ z, g z * φ z := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq
      (μ := volume) (F := ℝ) (hP.locallyIntegrable le_top) hP₀ ha hPa
  -- The `L²` inner product with, and the norm of, a square-integrable function.
  have inner_toLp_eq_integral (u : Lp ℝ 2 (volume : Measure E)) {f : E → ℝ}
      (hf : MemLp f 2 volume) : ⟪u, hf.toLp f⟫ = ∫ z, u z * f z := by
    rw [L2.inner_toLp]
    simp only [inner]
    exact integral_congr_ae (ae_of_all _ fun z ↦ mul_comm _ _)
  have norm_toLp_sq {f : E → ℝ} (hf : MemLp f 2 volume) : ‖hf.toLp f‖ ^ 2 = ∫ z, f z ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using hf.norm_toLp_sq
  set S := schrodingerToLp hP
  set ι :=
    (TestFunction.ambientToLp 2 volume : TestFn E →L[ℝ] Lp ℝ 2 (volume : Measure E)).toLinearMap
  have hSφ (φ : TestFn E) : S φ =
      (memLp_neg_laplacian_add_mul hP φ.contDiff φ.hasCompactSupport).toLp _ := rfl
  have hιφ (φ : TestFn E) : ι φ =
      (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ :=
    TestFunction.ambientToLp_apply φ
  -- The quadratic form of `-Δ + P` is bounded below:
  -- `c ‖φ‖₂² ≤ ⟪(-Δ + P) φ, φ⟫ ≤ ‖(-Δ + P) φ‖₂ ‖φ‖₂`.
  have hbound (φ : TestFn E) : c * ‖ι φ‖ ≤ ‖S φ‖ := by
    have hφ2 : MemLp φ 2 volume := φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
    have hDc : Continuous fun z ↦ ‖fderiv ℝ φ z‖ ^ 2 :=
      (φ.contDiff.continuous_fderiv (by norm_num)).norm.pow 2
    have hD : Integrable (fun z ↦ ‖fderiv ℝ φ z‖ ^ 2) volume :=
      hDc.integrable_of_hasCompactSupport
        ((φ.hasCompactSupport.fderiv (𝕜 := ℝ)).comp_left (g := fun L ↦ ‖L‖ ^ 2) (by simp))
    have hPφ : Integrable (fun z ↦ P z * φ z ^ 2) volume :=
      ((hP.mul hφ2 : MemLp (fun z ↦ P z * φ z) 2 volume).integrable_mul hφ2).congr
        (ae_of_all _ fun z ↦ by simp only [Pi.mul_apply]; ring)
    have hΔφ : Integrable (fun z ↦ φ z * -Δ (φ : E → ℝ) z) volume :=
      (φ.continuous.mul φ.contDiff.continuous_laplacian.neg).integrable_of_hasCompactSupport
        φ.hasCompactSupport.mul_right
    have hinner : ⟪S φ, ι φ⟫ = (∫ z, ‖fderiv ℝ φ z‖ ^ 2) + ∫ z, P z * φ z ^ 2 := by
      rw [real_inner_comm, hιφ, hSφ, inner_toLp_eq_integral]
      calc ∫ z, hφ2.toLp φ z * (-Δ (φ : E → ℝ) z + P z * φ z)
          = ∫ z, (φ z * -Δ (φ : E → ℝ) z + P z * φ z ^ 2) := by
            refine integral_congr_ae ?_
            filter_upwards [hφ2.coeFn_toLp] with z hz
            rw [hz]
            ring
        _ = _ := by
            -- Green's identity `∫ φ (-Δφ) = ∫ ‖Dφ‖²`.
            have hG := integral_inner_gradient_eq_neg_integral_mul_laplacian (μ := volume)
              φ.contDiff (φ.contDiff.of_le (by norm_num)) φ.hasCompactSupport
            simp only [real_inner_self_eq_norm_sq, norm_gradient_eq_norm_fderiv] at hG
            rw [integral_add hΔφ hPφ]
            simp only [mul_neg, integral_neg, hG]
    have hlow : c * ‖ι φ‖ ^ 2 ≤ ‖S φ‖ * ‖ι φ‖ := by
      rw [hιφ, norm_toLp_sq, ← hιφ]
      calc c * ∫ z, φ z ^ 2 ≤ (∫ z, ‖fderiv ℝ φ z‖ ^ 2) + ∫ z, P z * φ z ^ 2 := by
            simpa only [Real.norm_eq_abs, sq_abs] using
              hgap φ (φ.contDiff.of_le (by norm_num)) φ.hasCompactSupport
        _ = ⟪S φ, ι φ⟫ := hinner.symm
        _ ≤ ‖S φ‖ * ‖ι φ‖ := real_inner_le_norm _ _
    rcases (norm_nonneg (ι φ)).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      exact norm_nonneg _
    · nlinarith
  obtain ⟨Q, hQn, -, hQ⟩ := LinearMap.exists_continuousLinearMap_inner_apply_eq_of_mul_norm_le
    S ι hc hbound
  refine ⟨c, hc, Q, hQn, fun g φ hφ hφc ↦ ?_⟩
  have h := hQ g ⟨φ, hφ, hφc, by simp⟩
  rwa [hSφ, hιφ, inner_toLp_eq_integral, inner_toLp_eq_integral] at h

end Weak

/-! ### Regularity of weak solutions -/

section Regularity

/-- **Weak solutions of the stationary Schrödinger equation lie in `H²`.** Let `P` be a bounded
measurable potential, and let `h`, `g ∈ L²(E)` satisfy `-Δh + P h = g` weakly:
`∫ h (-Δφ + P φ) = ∫ g φ` for every smooth compactly supported function `φ`. Then `h ∈ H²(E)`. -/
theorem mem_realSobolevFunctions_two_of_integral_mul_neg_laplacian_add_mul_eq {P : E → ℝ}
    (hP : MemLp P ⊤ volume) {h g : E → ℝ} (hh : MemLp h 2 volume) (hg : MemLp g 2 volume)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, h z * (-Δ (φ : E → ℝ) z + P z * φ z) = ∫ z, g z * φ z) :
    h ∈ realSobolevFunctions E 2 2 := by
  set u := hh.toLp h
  -- The right side of `-Δh + h = g + (1 - P) h`.
  have hf : MemLp (fun z ↦ g z + (1 - P z) * h z) 2 volume :=
    hg.add ((memLp_top_const 1).sub hP |>.mul hh)
  set v := hf.toLp _
  set U := Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)
  -- In the sense of tempered distributions, `-Δh + h = g + (1 - P) h`.
  have hU : -Δ U + (1 : ℝ) • U = Lp.toTemperedDistribution (Complex.ofRealCLM.compLp v) := by
    refine TemperedDistribution.ext_real fun φ hφc ↦ ?_
    have hφ : ContDiff ℝ ∞ φ := φ.smooth ⊤
    have hΔ : (Δ (φ.postcompCLM Complex.ofRealCLM) : 𝓢(E, ℂ)) =
        (Δ φ).postcompCLM Complex.ofRealCLM := by
      have hcoe : ⇑(φ.postcompCLM Complex.ofRealCLM) = Complex.ofRealCLM ∘ φ :=
        funext fun z ↦ SchwartzMap.postcompCLM_apply _ _ z
      ext z
      rw [SchwartzMap.laplacian_apply, SchwartzMap.postcompCLM_apply, hcoe,
        SchwartzMap.laplacian_apply,
        (hφ.contDiffAt.of_le (by simp)).laplacian_CLM_comp_left]
      rfl
    have hφ2 : MemLp φ 2 volume := φ.continuous.memLp_of_hasCompactSupport hφc
    have hΔ2 : MemLp (Δ φ : 𝓢(E, ℝ)) 2 volume := (Δ φ).memLp 2
    have hi₁ : Integrable (fun z ↦ (Δ φ : 𝓢(E, ℝ)) z * u z) volume :=
      hΔ2.integrable_mul (Lp.memLp u)
    have hi₂ : Integrable (fun z ↦ φ z * u z) volume := hφ2.integrable_mul (Lp.memLp u)
    have hi₃ : Integrable (fun z ↦ h z * (-Δ (φ : E → ℝ) z + P z * φ z)) volume :=
      hh.integrable_mul (memLp_neg_laplacian_add_mul hP (hφ.of_le (by simp)) hφc)
    have hi₄ : Integrable (fun z ↦ h z * ((1 - P z) * φ z)) volume :=
      hh.integrable_mul
        ((memLp_top_const 1).sub hP |>.mul hφ2 : MemLp (fun z ↦ (1 - P z) * φ z) 2 volume)
    have hi₅ : Integrable (fun z ↦ g z * φ z) volume := hg.integrable_mul hφ2
    simp only [add_apply, neg_apply, TemperedDistribution.laplacian_apply_apply, smul_apply, hΔ]
    rw [Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
      Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
      Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM, Complex.real_smul,
      Complex.ofReal_one, one_mul, ← Complex.ofReal_neg, ← Complex.ofReal_add, ← integral_neg]
    congr 1
    rw [← integral_add (f := fun z ↦ -((Δ φ : 𝓢(E, ℝ)) z * u z)) hi₁.neg hi₂]
    -- Both sides are `∫ h (-Δφ + φ)`, using the weak equation for the part `-Δφ + P φ`.
    have hw := hweak φ hφ hφc
    calc ∫ z, (-((Δ φ : 𝓢(E, ℝ)) z * u z) + φ z * u z)
        = ∫ z, (h z * (-Δ (φ : E → ℝ) z + P z * φ z) + h z * ((1 - P z) * φ z)) := by
          refine integral_congr_ae ?_
          filter_upwards [hh.coeFn_toLp] with z hz
          rw [hz, SchwartzMap.laplacian_apply]
          ring
      _ = ∫ z, (g z * φ z + h z * ((1 - P z) * φ z)) := by
          rw [integral_add hi₃ hi₄, integral_add hi₅ hi₄, hw]
      _ = ∫ z, φ z * v z := by
          refine integral_congr_ae ?_
          filter_upwards [hf.coeFn_toLp] with z hz
          rw [hz]
          ring
  have hv : MemSobolev 0 2 (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp v)) :=
    memSobolev_zero_iff.2 ⟨_, rfl⟩
  have hU2 : MemSobolev 2 2 U := by
    have := (memSobolev_add_two_iff_neg_laplacian_add_smul (s := 0) (F := ℂ) one_pos).2
      (hU ▸ hv)
    simpa using this
  exact mem_realSobolevFunctions.2 ⟨u, hh.coeFn_toLp, hU2⟩

end Regularity

/-- **Solvability of the stationary Schrödinger equation in `H²`.** Let `P` be a bounded
measurable potential on `E`, almost everywhere nonnegative and almost everywhere at least `a > 0`
outside the closed ball of radius `R`. Then for every `g ∈ L²(E)` there is `h ∈ H²(E)` with
`-Δh + P h = g` weakly: `∫ h (-Δφ + P φ) = ∫ g φ` for every compactly supported `C²`
function `φ`. -/
theorem exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq [Nontrivial E]
    {P : E → ℝ} (hP : MemLp P ⊤ volume) (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z) {g : E → ℝ} (hg : MemLp g 2 volume) :
    ∃ h ∈ realSobolevFunctions E 2 2, ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∫ z, h z * (-Δ φ z + P z * φ z) = ∫ z, g z * φ z := by
  obtain ⟨-, -, Q, -, hQ⟩ :=
    exists_continuousLinearMap_integral_mul_neg_laplacian_add_mul_eq hP hP₀ ha hPa
  -- The weak equation for `Q g` only sees `g` through its values almost everywhere.
  have hweak (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
      ∫ z, Q (hg.toLp g) z * (-Δ φ z + P z * φ z) = ∫ z, g z * φ z := by
    rw [hQ _ φ hφ hφc]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with z hz
    rw [hz]
  refine ⟨Q (hg.toLp g), ?_, hweak⟩
  exact mem_realSobolevFunctions_two_of_integral_mul_neg_laplacian_add_mul_eq hP
    (Lp.memLp _) hg fun φ hφ hφc ↦ hweak φ (hφ.of_le (by simp)) hφc


/-! ### Complex-valued weak solutions -/

/-- **Complex weak solutions from real ones.** Let `P` be a bounded potential and `g ∈ L²(E; ℂ)`.
If `h₁`, `h₂ ∈ L²(E)` are weak solutions of `-Δh + P h = Re g` and `-Δh + P h = Im g`, then
`h = h₁ + i h₂` is a weak solution of `-Δh + P h = g`: for every compactly supported `C²` real
function `φ`, the integrand `h (-Δφ + P φ)` is integrable and `∫ h (-Δφ + P φ) = ∫ g φ`. -/
theorem integrable_and_integral_mul_neg_laplacian_add_mul_eq_of_re_im {P : E → ℝ}
    (hP : MemLp P ⊤ volume) {g : E → ℂ} (hg : MemLp g 2 volume) {h₁ h₂ : E → ℝ}
    (hh₁ : MemLp h₁ 2 volume) (hh₂ : MemLp h₂ 2 volume)
    (hw₁ : ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∫ z, h₁ z * (-Δ φ z + P z * φ z) = ∫ z, (g z).re * φ z)
    (hw₂ : ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∫ z, h₂ z * (-Δ φ z + P z * φ z) = ∫ z, (g z).im * φ z)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z ↦ (h₁ z + h₂ z * Complex.I) * ((-Δ φ z + P z * φ z : ℝ) : ℂ)) volume ∧
      ∫ z, (h₁ z + h₂ z * Complex.I) * ((-Δ φ z + P z * φ z : ℝ) : ℂ) =
        ∫ z, g z * (φ z : ℂ) := by
  set L : E → ℝ := fun z ↦ -Δ φ z + P z * φ z with hLdef
  have hL2 : MemLp L 2 volume := memLp_neg_laplacian_add_mul hP hφ hφc
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hφc
  have j₁ : Integrable (fun z ↦ h₁ z * L z) volume := hh₁.integrable_mul hL2
  have j₂ : Integrable (fun z ↦ h₂ z * L z) volume := hh₂.integrable_mul hL2
  have j₃ : Integrable (fun z ↦ (g z).re * φ z) volume := hg.re.integrable_mul hφ2
  have j₄ : Integrable (fun z ↦ (g z).im * φ z) volume := hg.im.integrable_mul hφ2
  -- Integrals of `u + i v` for real integrable `u`, `v`.
  have hsplit (u v : E → ℝ) (hu : Integrable u volume) (hv : Integrable v volume) :
      ∫ z, ((u z : ℂ) + Complex.I * (v z : ℂ)) =
        (∫ z, u z : ℝ) + Complex.I * (∫ z, v z : ℝ) := by
    rw [integral_add (f := fun z ↦ (u z : ℂ)) (g := fun z ↦ Complex.I * (v z : ℂ)) hu.ofReal
      (hv.ofReal.const_mul Complex.I), integral_const_mul,
      integral_complex_ofReal, integral_complex_ofReal]
  refine ⟨(Integrable.add (f := fun z ↦ ((h₁ z * L z : ℝ) : ℂ))
      (g := fun z ↦ Complex.I * ((h₂ z * L z : ℝ) : ℂ)) j₁.ofReal
        (j₂.ofReal.const_mul Complex.I)).congr (ae_of_all _ fun z ↦ ?_), ?_⟩
  · simp only [Pi.add_apply, hLdef]
    push_cast
    ring
  have hl : ∫ z, (h₁ z + h₂ z * Complex.I) * (L z : ℂ) =
      ∫ z, (((h₁ z * L z : ℝ) : ℂ) + Complex.I * ((h₂ z * L z : ℝ) : ℂ)) :=
    integral_congr_ae (ae_of_all _ fun z ↦ by simp only [hLdef]; push_cast; ring)
  have hr : ∫ z, g z * (φ z : ℂ) =
      ∫ z, ((((g z).re * φ z : ℝ) : ℂ) + Complex.I * (((g z).im * φ z : ℝ) : ℂ)) := by
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    dsimp only
    conv_lhs => rw [← Complex.re_add_im (g z)]
    push_cast
    ring
  rw [hl, hr, hsplit _ _ j₁ j₂, hsplit _ _ j₃ j₄, hw₁ φ hφ hφc, hw₂ φ hφ hφc]

end TauCeti
