/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Sobolev.W1p.Basic
import Mathlib.MeasureTheory.Function.Holder
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.TestFunction.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.LaplacianResolvent
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Integral
import TauCeti.Analysis.InnerProductSpace.WeakSolution
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.Sobolev.Poincare.Schrodinger
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The stationary Schrödinger equation with a potential positive at infinity

Let `E` be a finite-dimensional real inner product space and `P` a bounded measurable potential on
`E` which is nonnegative and bounded below by a constant `a > 0` outside a ball. This file solves
the stationary Schrödinger equation

`-Δh + P h = g`

on the whole space, for every `g ∈ L²(E)`, with a solution `h` in the Sobolev space `H²(E)`
which is unique among weak solutions in `L²(E)`.

* **Weak solutions.** By the Poincaré inequality for Schrödinger forms
  (`TauCeti.exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq`)
  and Green's identity, the quadratic form of `-Δ + P` is bounded below on test functions,
  `c ∫ φ² ≤ ∫ φ (-Δφ + P φ)`, so `c ‖φ‖₂ ≤ ‖-Δφ + P φ‖₂`. Since `-Δ + P` is formally
  self-adjoint, the abstract weak right inverse
  (`LinearMap.exists_continuousLinearMap_inner_apply_eq_of_mul_norm_le`) gives a bounded operator
  `Q` on `L²(E)` of norm at most `c⁻¹` such that `Q g` is a weak solution:
  `∫ (Q g) (-Δφ + P φ) = ∫ g φ` for every compactly supported `C²` function `φ`
  (`TauCeti.exists_continuousLinearMap_integral_mul_neg_laplacian_add_mul_eq`).
* **Regularity.** A weak solution of `-Δh + P h = g` satisfies `-Δh + h = g + h - P h` in the
  sense of tempered distributions. If `h`, `P h` and `g` lie in `H^s(E)`, elliptic regularity of
  `-Δ + 1` (`TemperedDistribution.memSobolev_add_two_iff_neg_laplacian_add_smul`) puts `h` in
  `H^(s+2)(E)`
  (`TauCeti.mem_realSobolevFunctions_add_two_of_integral_mul_neg_laplacian_add_mul_eq`); this
  uses no sign or bound on `P`, and iterating it gives higher regularity whenever multiplication
  by `P` preserves the Sobolev scale. At `s = 0`, boundedness of `P` suffices, so a weak `L²`
  solution with `g ∈ L²` lies in `H²(E)`
  (`TauCeti.mem_realSobolevFunctions_two_of_integral_mul_neg_laplacian_add_mul_eq`).
* **Uniqueness.** Passing from test functions to all of `H¹(E) = W^{1,2}(E)` by density
  (`TauCeti.W1p.denseRange_ofTestFunctionₗ_top`), the form `∫ ⟪∇u, ∇v⟫ + ∫ P u v` is coercive on
  `H¹(E)`
  (`TauCeti.exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq`). A weak `L²`
  solution of `-Δh + P h = 0` lies in `H²(E) ⊆ H¹(E)` and is orthogonal to `H¹(E)` for this
  form, so it vanishes; two weak `L²` solutions for the same `g` thus agree almost everywhere
  (`TauCeti.ae_eq_of_integral_mul_neg_laplacian_add_mul_eq`).

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
* `TauCeti.mem_realSobolevFunctions_add_two_of_integral_mul_neg_laplacian_add_mul_eq`: a weak
  solution gains two derivatives over `h`, `P h` and `g`.
* `TauCeti.mem_realSobolevFunctions_two_of_integral_mul_neg_laplacian_add_mul_eq`: weak `L²`
  solutions lie in `H²(E)`.
* `TauCeti.exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq`: existence of
  an `H²` weak solution for every `L²` right-hand side.
* `TauCeti.exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq`: coercivity of
  the Schrödinger form, `c ‖u‖²_{H¹} ≤ ‖∇u‖₂² + ∫ P u²`.
* `TauCeti.ae_eq_of_integral_mul_neg_laplacian_add_mul_eq`: two weak `L²` solutions agree almost
  everywhere.
* `TauCeti.integrable_and_integral_mul_neg_laplacian_add_mul_eq_of_re_im`: real weak solutions
  for the real and imaginary parts combine into a complex weak solution.
* `TauCeti.memLp_neg_laplacian_add_mul`: the Schrödinger operator with a bounded potential maps
  compactly supported `C²` functions into `L²`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 8 (weak solutions, the energy method, and regularity).
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
  -- The `L²` inner product with a square-integrable function.
  have inner_toLp_eq_integral (u : Lp ℝ 2 (volume : Measure E)) {f : E → ℝ}
      (hf : MemLp f 2 volume) : ⟪u, hf.toLp f⟫ = ∫ z, u z * f z := by
    rw [L2.inner_toLp]
    simp only [inner]
    exact integral_congr_ae (ae_of_all _ fun z ↦ mul_comm _ _)
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
    have _ : Integrable (fun z ↦ ‖fderiv ℝ φ z‖ ^ 2) volume :=
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
      rw [show ‖ι φ‖ ^ 2 = ∫ z, ‖φ z‖ ^ 2 from TestFunction.norm_ambientToLp_sq φ]
      calc c * ∫ z, ‖φ z‖ ^ 2 ≤ (∫ z, ‖fderiv ℝ φ z‖ ^ 2) + ∫ z, P z * φ z ^ 2 := by
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
  rw [hSφ, inner_toLp_eq_integral, ContinuousLinearMap.coe_coe, TestFunction.inner_ambientToLp] at h
  simp only [Real.inner_apply] at h
  exact h

end Weak

/-! ### Regularity of weak solutions -/

section Regularity

/-- The distributional form of a weak solution: if `h` is a weak solution of `-Δh + P h = g`,
with `h`, `P h` and `g` square integrable, then `-Δh + h = g + h - P h` as tempered
distributions. -/
private theorem neg_laplacian_add_eq {P h g : E → ℝ} (hh : MemLp h 2 volume)
    (hPh : MemLp (fun z ↦ P z * h z) 2 volume) (hg : MemLp g 2 volume)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, h z * (-Δ (φ : E → ℝ) z + P z * φ z) = ∫ z, g z * φ z)
    {uh uR : Lp ℝ 2 (volume : Measure E)} (huh : uh =ᵐ[volume] h)
    (huR : uR =ᵐ[volume] g + h - fun z ↦ P z * h z) :
    -Δ (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp uh) : 𝓢'(E, ℂ)) +
        (1 : ℝ) • (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp uh) : 𝓢'(E, ℂ)) =
      Lp.toTemperedDistribution (Complex.ofRealCLM.compLp uR) := by
  refine ext_real fun φ hφ ↦ ?_
  have hφ2 := φ.memLp 2 (μ := volume)
  have hΔ2 : MemLp (Δ (φ : E → ℝ)) 2 volume := by
    convert (Δ φ).memLp 2 (μ := volume) using 1
    exact funext fun z ↦ (SchwartzMap.laplacian_apply φ z).symm
  -- Both sides as real integrals against `h`, `g` and `P h`.
  rw [add_apply, neg_apply, smul_apply, laplacian_apply_apply, laplacian_postcompCLM,
    Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
    Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
    Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM, one_smul]
  have hA : ∫ z, (Δ φ) z * uh z = ∫ z, h z * Δ (φ : E → ℝ) z :=
    integral_congr_ae (huh.mono fun z hz ↦ by simp only [hz, SchwartzMap.laplacian_apply, mul_comm])
  have hB : ∫ z, φ z * uh z = ∫ z, φ z * h z :=
    integral_congr_ae (huh.mono fun z hz ↦ by simp only [hz])
  have hC : ∫ z, φ z * uR z = ∫ z, φ z * (g + h - fun z ↦ P z * h z) z :=
    integral_congr_ae (huR.mono fun z hz ↦ by simp only [hz])
  rw [hA, hB, hC]
  -- Split the integrals of the weak equation and of the right-hand side.
  have hw := hweak φ (φ.smooth ⊤) hφ
  have i1 : Integrable (fun z ↦ h z * Δ (φ : E → ℝ) z) := hh.integrable_mul hΔ2
  have i2 : Integrable (fun z ↦ φ z * (P z * h z)) := hφ2.integrable_mul hPh
  have i3 : Integrable (fun z ↦ φ z * g z) := hφ2.integrable_mul hg
  have i4 : Integrable (fun z ↦ φ z * h z) := hφ2.integrable_mul hh
  have e1 : ∫ z, h z * (-Δ (φ : E → ℝ) z + P z * φ z) =
      -(∫ z, h z * Δ (φ : E → ℝ) z) + ∫ z, φ z * (P z * h z) := by
    rw [← integral_neg, ← integral_add (f := fun z ↦ -(h z * Δ (φ : E → ℝ) z)) i1.neg i2]
    exact integral_congr_ae (Eventually.of_forall fun z ↦ by ring)
  have e2 : ∫ z, φ z * (g + h - fun z ↦ P z * h z) z =
      (∫ z, φ z * g z) + (∫ z, φ z * h z) - ∫ z, φ z * (P z * h z) := by
    rw [← integral_add (f := fun z ↦ φ z * g z) (g := fun z ↦ φ z * h z) i3 i4,
      ← integral_sub (f := fun z ↦ φ z * g z + φ z * h z) (i3.add i4) i2]
    exact integral_congr_ae (Eventually.of_forall fun z ↦ by
      simp only [Pi.add_apply, Pi.sub_apply]; ring)
  have e3 : ∫ z, g z * φ z = ∫ z, φ z * g z :=
    integral_congr_ae (Eventually.of_forall fun z ↦ mul_comm _ _)
  rw [e2]
  rw [e1, e3] at hw
  push_cast
  rw [← Complex.ofReal_neg, ← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_sub]
  congr 1
  linarith

/-- **Weak solutions of the stationary Schrödinger equation gain two derivatives.** If `h`, `P h`
and `g` lie in `H^s(E)` and `-Δh + P h = g` weakly, that is `∫ h (-Δφ + P φ) = ∫ g φ` for every
smooth compactly supported function `φ`, then `h ∈ H^(s+2)(E)`. No sign or bound on `P` is
assumed. -/
theorem mem_realSobolevFunctions_add_two_of_integral_mul_neg_laplacian_add_mul_eq {s : ℝ}
    {P h g : E → ℝ} (hh : h ∈ realSobolevFunctions E s 2)
    (hPh : (fun z ↦ P z * h z) ∈ realSobolevFunctions E s 2)
    (hg : g ∈ realSobolevFunctions E s 2)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, h z * (-Δ (φ : E → ℝ) z + P z * φ z) = ∫ z, g z * φ z) :
    h ∈ realSobolevFunctions E (s + 2) 2 := by
  obtain ⟨uh, huh, -⟩ := mem_realSobolevFunctions.1 hh
  obtain ⟨uR, huR, hRs⟩ := mem_realSobolevFunctions.1 (sub_mem (add_mem hg hh) hPh)
  have hT := neg_laplacian_add_eq (memLp_of_mem_realSobolevFunctions hh)
    (memLp_of_mem_realSobolevFunctions hPh) (memLp_of_mem_realSobolevFunctions hg) hweak huh huR
  exact mem_realSobolevFunctions.2 ⟨uh, huh,
    (memSobolev_add_two_iff_neg_laplacian_add_smul one_pos).2 (by rw [hT]; exact hRs)⟩

/-- **Weak solutions of the stationary Schrödinger equation lie in `H²`.** Let `P` be a bounded
measurable potential, and let `h`, `g ∈ L²(E)` satisfy `-Δh + P h = g` weakly:
`∫ h (-Δφ + P φ) = ∫ g φ` for every smooth compactly supported function `φ`. Then `h ∈ H²(E)`. -/
theorem mem_realSobolevFunctions_two_of_integral_mul_neg_laplacian_add_mul_eq {P : E → ℝ}
    (hP : MemLp P ⊤ volume) {h g : E → ℝ} (hh : MemLp h 2 volume) (hg : MemLp g 2 volume)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, h z * (-Δ (φ : E → ℝ) z + P z * φ z) = ∫ z, g z * φ z) :
    h ∈ realSobolevFunctions E 2 2 := by
  simpa only [zero_add] using
    mem_realSobolevFunctions_add_two_of_integral_mul_neg_laplacian_add_mul_eq (s := 0)
      (mem_realSobolevFunctions_zero_iff.2 hh) (mem_realSobolevFunctions_zero_iff.2 (hP.fun_mul hh))
      (mem_realSobolevFunctions_zero_iff.2 hg) hweak

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

/-! ### Uniqueness of weak solutions -/

section Uniqueness

open TopologicalSpace
open scoped Distributions

variable {P : E → ℝ}

/-- Multiplication by an essentially bounded potential, as a bounded operator on `L²(E)`. -/
private noncomputable def potentialMul (hP : MemLp P ⊤ (volume : Measure E)) :
    Lp ℝ 2 ((volume : Measure E).restrict (⊤ : Opens E)) →L[ℝ]
      Lp ℝ 2 ((volume : Measure E).restrict (⊤ : Opens E)) :=
  (ContinuousLinearMap.lsmul ℝ ℝ).holderL _ ⊤ 2 2 ((hP.restrict _).toLp P)

private theorem potentialMul_ae (hP : MemLp P ⊤ (volume : Measure E))
    (f : Lp ℝ 2 ((volume : Measure E).restrict (⊤ : Opens E))) :
    potentialMul hP f =ᵐ[volume] fun z ↦ P z * f z := by
  have h := (ContinuousLinearMap.lsmul ℝ ℝ).coeFn_holder (r := 2) ((hP.restrict _).toLp P) f
  have h' := (hP.restrict ((⊤ : Opens E) : Set E)).coeFn_toLp
  simp only [Opens.coe_top, Measure.restrict_univ] at h h'
  filter_upwards [h, h'] with z hz hz'
  simp only [potentialMul, ContinuousLinearMap.holderL_apply_apply, hz, hz',
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- The Schrödinger form `(u, v) ↦ ⟪∇u, ∇v⟫ + ⟪u, P v⟫` on `H¹(E)`. -/
private noncomputable def schrodingerForm (hP : MemLp P ⊤ (volume : Measure E)) :
    W1p (volume : Measure E) ⊤ 2 →L[ℝ] W1p (volume : Measure E) ⊤ 2 →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun u v ↦ ⟪W1p.gradient u, W1p.gradient v⟫ +
        ⟪W1p.value u, potentialMul hP (W1p.value v)⟫)
      (fun u u' v ↦ by
        simp only [← W1p.gradientL_apply, ← W1p.valueL_apply, map_add, inner_add_left]; ring)
      (fun c u v ↦ by
        simp only [← W1p.gradientL_apply, ← W1p.valueL_apply, map_smul, real_inner_smul_left,
          smul_eq_mul]; ring)
      (fun u v v' ↦ by
        simp only [← W1p.gradientL_apply, ← W1p.valueL_apply, map_add, inner_add_right]; ring)
      (fun c u v ↦ by
        simp only [← W1p.gradientL_apply, ← W1p.valueL_apply, map_smul, real_inner_smul_right,
          smul_eq_mul]; ring))
    (1 + ‖potentialMul hP‖) fun u v ↦ by
      simp only [LinearMap.mk₂_apply]
      have h1 := abs_real_inner_le_norm (W1p.gradient u) (W1p.gradient v)
      have h2 := abs_real_inner_le_norm (W1p.value u) (potentialMul hP (W1p.value v))
      have h3 := (potentialMul hP).le_opNorm (W1p.value v)
      have hgu := W1p.norm_gradient_le u
      have hgv := W1p.norm_gradient_le v
      have hvu := W1p.norm_value_le u
      have hvv := W1p.norm_value_le v
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans ?_
      have _ := norm_nonneg (potentialMul hP)
      calc _ ≤ ‖W1p.gradient u‖ * ‖W1p.gradient v‖ +
            ‖W1p.value u‖ * (‖potentialMul hP‖ * ‖W1p.value v‖) := by
            gcongr
            exact h2.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
        _ ≤ ‖u‖ * ‖v‖ + ‖u‖ * (‖potentialMul hP‖ * ‖v‖) := by gcongr
        _ = (1 + ‖potentialMul hP‖) * ‖u‖ * ‖v‖ := by ring

private theorem schrodingerForm_apply (hP : MemLp P ⊤ (volume : Measure E))
    (u v : W1p (volume : Measure E) ⊤ 2) :
    schrodingerForm hP u v = (∫ z, ⟪W1p.gradient u z, W1p.gradient v z⟫) +
      ∫ z, P z * (W1p.value u z * W1p.value v z) := by
  simp only [schrodingerForm, LinearMap.mkContinuous₂_apply, LinearMap.mk₂_apply, L2.inner_def,
    Opens.coe_top, Measure.restrict_univ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [potentialMul_ae hP (W1p.value v)] with z hz
  rw [hz, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
  ring

private theorem schrodingerForm_self (hP : MemLp P ⊤ (volume : Measure E))
    (u : W1p (volume : Measure E) ⊤ 2) :
    schrodingerForm hP u u = ‖W1p.gradient u‖ ^ 2 + ∫ z, P z * W1p.value u z ^ 2 := by
  rw [schrodingerForm_apply, ← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
  simp only [Opens.coe_top, Measure.restrict_univ, real_inner_self_eq_norm_sq, sq]

/-- The Poincaré inequality for the Schrödinger form, extended from test functions to all of
`H¹(E)` by density. -/
private theorem mul_norm_value_sq_le_schrodingerForm [Nontrivial E]
    (hP : MemLp P ⊤ (volume : Measure E)) (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z) :
    ∃ c > 0, ∀ u : W1p (volume : Measure E) ⊤ 2,
      c * ‖W1p.value u‖ ^ 2 ≤ schrodingerForm hP u u := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq
      (μ := volume) (F := ℝ) (hP.locallyIntegrable le_top) hP₀ ha hPa
  refine ⟨c, hc, fun u ↦ ?_⟩
  refine (W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 2) (by norm_num)).induction_on
    u (isClosed_le (continuous_const.mul
      (((W1p.valueL (mu := volume) (Omega := ⊤) (p := 2)).continuous.congr
        W1p.valueL_apply).norm.pow 2))
      ((schrodingerForm hP).continuous₂.comp
      (continuous_id.prodMk continuous_id))) fun φ ↦ ?_
  have hv := W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ
  rw [schrodingerForm_self, W1p.norm_value_ofTestFunctionₗ_top_sq,
    W1p.norm_gradient_ofTestFunctionₗ_top_sq]
  have h := hgap φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
  simp only [Real.norm_eq_abs, sq_abs] at h
  convert h using 2
  exact integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])

/-- **Coercivity of the Schrödinger form on `H¹(E)`.** Let `P` be essentially bounded, almost
everywhere nonnegative, and almost everywhere at least `a > 0` outside the closed ball of radius
`R`. Then there is `c > 0` with `c ‖u‖²_{H¹} ≤ ‖∇u‖₂² + ∫ P u²` for every `u ∈ H¹(E)`. -/
theorem exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq [Nontrivial E]
    (hP : MemLp P ⊤ (volume : Measure E)) (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z) :
    ∃ c > 0, ∀ u : W1p (volume : Measure E) ⊤ 2,
      c * ‖u‖ ^ 2 ≤ ‖W1p.gradient u‖ ^ 2 + ∫ z, P z * W1p.value u z ^ 2 := by
  obtain ⟨c, hc, hgap⟩ := mul_norm_value_sq_le_schrodingerForm hP hP₀ ha hPa
  refine ⟨min 1 c / 2, by positivity, fun u ↦ ?_⟩
  have hgap := hgap u
  rw [schrodingerForm_self] at hgap
  have hpot : 0 ≤ ∫ z, P z * W1p.value u z ^ 2 :=
    integral_nonneg_of_ae (hP₀.mono fun z hz ↦ by positivity)
  have h1 : min 1 c ≤ 1 := min_le_left _ _
  have h2 : min 1 c ≤ c := min_le_right _ _
  have _ : 0 ≤ min 1 c := le_min zero_le_one hc.le
  rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
  nlinarith [sq_nonneg ‖W1p.value u‖, sq_nonneg ‖W1p.gradient u‖,
    mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖W1p.value u‖),
    mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖W1p.gradient u‖)]

/-- For `u ∈ H¹(E)`, testing `u` against `-Δφ + P φ` is the Schrödinger form of `u` and `φ`. -/
private theorem integral_value_mul_eq_schrodingerForm (hP : MemLp P ⊤ (volume : Measure E))
    (u : W1p (volume : Measure E) ⊤ 2) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    ∫ z, W1p.value u z * (-Δ (φ : E → ℝ) z + P z * φ z) =
      schrodingerForm hP u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) := by
  have hu : MemLp (W1p.value u : E → ℝ) 2 volume := W1p.memLp_value u
  have hφ2 : MemLp (φ : E → ℝ) 2 volume :=
    φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hΔ2 : MemLp (Δ (φ : E → ℝ)) 2 volume :=
    (φ.contDiff.of_le (by simp)).continuous_laplacian.memLp_of_hasCompactSupport
      φ.hasCompactSupport.laplacian
  have hibp := (W1p.hasWeakFDerivOn u).integral_laplacian_smul_eq_neg_integral_inner φ
  simp only [smul_eq_mul] at hibp
  have hv := W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ
  have hg := W1p.gradient_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ
  rw [schrodingerForm_apply]
  have e1 : ∫ z, W1p.value u z * (-Δ (φ : E → ℝ) z + P z * φ z) =
      -(∫ z, Δ (φ : E → ℝ) z * W1p.value u z) + ∫ z, P z * (W1p.value u z * φ z) := by
    rw [← integral_neg, ← integral_add (f := fun z ↦ -(Δ (φ : E → ℝ) z * W1p.value u z))
      (hΔ2.integrable_mul hu).neg
        (memLp_one_iff_integrable.1 (hP.fun_mul (hu.fun_mul hφ2 : MemLp _ 1 volume)))]
    exact integral_congr_ae (Eventually.of_forall fun z ↦ by ring)
  rw [e1, hibp, neg_neg]
  congr 1
  · refine integral_congr_ae (hg.mono fun z hz ↦ ?_)
    simp only [hz, real_inner_comm]
  · exact integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])

/-- An `H¹` function which is a weak solution of `-Δh + P h = 0` is orthogonal to all of `H¹(E)`
for the Schrödinger form. -/
private theorem schrodingerForm_eq_zero (hP : MemLp P ⊤ (volume : Measure E))
    {u : W1p (volume : Measure E) ⊤ 2}
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, W1p.value u z * (-Δ (φ : E → ℝ) z + P z * φ z) = 0)
    (v : W1p (volume : Measure E) ⊤ 2) :
    schrodingerForm hP u v = 0 := by
  refine (W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 2) (by norm_num)).induction_on
    v (isClosed_eq (schrodingerForm hP u).continuous continuous_const) fun φ ↦ ?_
  rw [← integral_value_mul_eq_schrodingerForm hP]
  exact hweak φ φ.contDiff φ.hasCompactSupport

/-- **Uniqueness of weak solutions of the stationary Schrödinger equation.** Let `P` be
essentially bounded, almost everywhere nonnegative, and almost everywhere at least `a > 0` outside
the closed ball of radius `R`. If `h₁, h₂ ∈ L²(E)` both satisfy `-Δh + P h = g` weakly, that is
`∫ h (-Δφ + P φ) = ∫ g φ` for every smooth compactly supported function `φ`, then `h₁ = h₂`
almost everywhere. -/
theorem ae_eq_of_integral_mul_neg_laplacian_add_mul_eq [Nontrivial E]
    (hP : MemLp P ⊤ (volume : Measure E)) (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z) {h₁ h₂ g : E → ℝ} (hh₁ : MemLp h₁ 2 volume)
    (hh₂ : MemLp h₂ 2 volume)
    (hw₁ : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, h₁ z * (-Δ (φ : E → ℝ) z + P z * φ z) = ∫ z, g z * φ z)
    (hw₂ : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, h₂ z * (-Δ (φ : E → ℝ) z + P z * φ z) = ∫ z, g z * φ z) :
    h₁ =ᵐ[volume] h₂ := by
  -- The difference is a weak solution with zero right-hand side.
  have hd (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
      ∫ z, (h₁ - h₂) z * (-Δ (φ : E → ℝ) z + P z * φ z) = 0 := by
    have hT := memLp_neg_laplacian_add_mul (μ := volume) hP (hφ.of_le (by simp)) hc
    simp only [Pi.sub_apply, sub_mul]
    rw [integral_sub (f := fun z ↦ h₁ z * (-Δ φ z + P z * φ z))
      (g := fun z ↦ h₂ z * (-Δ φ z + P z * φ z)) (hh₁.integrable_mul hT)
      (hh₂.integrable_mul hT), hw₁ φ hφ hc, hw₂ φ hφ hc, sub_self]
  -- It lies in `H²(E) ⊆ H¹(E)`, so it is the value of some `w ∈ W^{1,2}(E)`.
  have h2 := mem_realSobolevFunctions_two_of_integral_mul_neg_laplacian_add_mul_eq hP
    (hh₁.sub hh₂) (MemLp.zero : MemLp (0 : E → ℝ) 2 volume) fun φ hφ hc ↦ by
      simpa only [Pi.zero_apply, zero_mul, integral_zero] using hd φ hφ hc
  obtain ⟨w, hw⟩ :=
    exists_w1p_value_ae_eq_of_mem_realSobolevFunctions (by norm_num) (by norm_num) (by norm_num) h2
  -- The Poincaré inequality forces the value of `w` to vanish.
  have hw0 : schrodingerForm hP w w = 0 := schrodingerForm_eq_zero hP (fun φ hφ hc ↦ by
    rw [← hd φ hφ hc]
    exact integral_congr_ae (hw.mono fun z hz ↦ by simp only [hz])) w
  obtain ⟨c, hc, hgap⟩ := mul_norm_value_sq_le_schrodingerForm hP hP₀ ha hPa
  have hn : W1p.value w = 0 := by
    have := hgap w
    rw [hw0] at this
    have hsq : ‖W1p.value w‖ ^ 2 = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right this hc) (sq_nonneg _)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)
  have h0 : (W1p.value w : E → ℝ) =ᵐ[volume] 0 := by
    rw [hn]
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.coeFn_zero ℝ 2 ((volume : Measure E).restrict (⊤ : Opens E))
  filter_upwards [hw.symm.trans h0] with z hz
  simpa [sub_eq_zero] using hz

end Uniqueness


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
