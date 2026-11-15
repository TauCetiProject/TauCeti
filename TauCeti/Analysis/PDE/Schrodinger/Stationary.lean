/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.TestFunction.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.LaplacianResolvent
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Integral
import TauCeti.Analysis.InnerProductSpace.WeakSolution
import TauCeti.Analysis.PDE.Regularity.PlanarPoisson
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.Poincare.Schrodinger
import TauCeti.Analysis.Sobolev.W1p.Density
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
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
* **Uniqueness.** The Schrödinger form `TauCeti.schrodingerForm`, `∫ ⟪∇u, ∇v⟫ + ∫ P u v`, is
  coercive on `H¹(E) = W^{1,2}(E)`
  (`TauCeti.exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq`). A weak `L²`
  solution of `-Δh + P h = 0` lies in `H²(E) ⊆ H¹(E)` and, by density of test functions
  (`TauCeti.W1p.denseRange_ofTestFunctionₗ_top`), is orthogonal to `H¹(E)` for this form, so it
  vanishes; two weak `L²` solutions for the same `g` thus agree almost everywhere
  (`TauCeti.ae_eq_of_integral_mul_neg_laplacian_add_mul_eq`).

Together, every `g ∈ L²(E)` has a weak solution `h ∈ H²(E)`
(`TauCeti.exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq`). Solving
for the real and imaginary parts of a complex right-hand side separately gives a complex weak
solution (`TauCeti.integrable_and_integral_mul_neg_laplacian_add_mul_eq_of_re_im`).

In the plane, `H²` embeds in the continuous functions vanishing at infinity, and the planar
Poisson bootstrap (`TauCeti.contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp`) makes the
continuous representative of the weak solution classical: for a `Cᵏ` bounded potential and a
`Cᵏ` square-integrable source `g`, `k ≥ 1`, the equation `Δu = P u + g` has a `Cᵏ⁺¹` solution
with `u`, `Du ∈ L²` and `u → 0` at infinity (`TauCeti.exists_contDiff_laplacian_eq_mul_add`).

In the plane, a smooth potential and a smooth right-hand side give a smooth solution: the
`H²` solution has a continuous representative by the Sobolev embedding
(`TemperedDistribution.MemSobolev.exists_contDiff_ae_eq`), interior regularity for the
semilinear Poisson equation `Δh = P h - g`
(`TauCeti.contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp`) makes it smooth, and it then
solves the equation pointwise (`TauCeti.eqOn_laplacian_of_forall_integral_laplacian_mul_eq_comp`,
`TauCeti.exists_contDiff_mem_realSobolevFunctions_two_neg_laplacian_add_mul_eq`). Solving for the
real and imaginary parts separately gives the complex version
(`TauCeti.exists_contDiff_re_im_mem_realSobolevFunctions_two_neg_laplacian_add_mul_eq`).

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
* `TauCeti.ae_eq_of_integral_mul_neg_laplacian_add_mul_eq`: two weak `L²` solutions agree almost
  everywhere.
* `TauCeti.integrable_and_integral_mul_neg_laplacian_add_mul_eq_of_re_im`: real weak solutions
  for the real and imaginary parts combine into a complex weak solution.
* `TauCeti.memLp_neg_laplacian_add_mul`: the Schrödinger operator with a bounded potential maps
  compactly supported `C²` functions into `L²`.
* `TauCeti.exists_contDiff_laplacian_eq_mul_add`: classical solutions of `Δu = P u + g` in the
  plane, square integrable with square-integrable derivative and vanishing at infinity.

* `TauCeti.exists_contDiff_mem_realSobolevFunctions_two_neg_laplacian_add_mul_eq`: in the plane,
  a smooth `H²` solution solving the equation pointwise, for smooth `P` and `g`.
* `TauCeti.exists_contDiff_re_im_mem_realSobolevFunctions_two_neg_laplacian_add_mul_eq`: the same
  for a complex right-hand side.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 8 (weak solutions, the energy method, and regularity).
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  Section XIII.1 (Schrödinger operators with potentials bounded below).
-/

public section

namespace TauCeti

open MeasureTheory Filter Metric TemperedDistribution
open scoped Laplacian ContDiff Gradient InnerProductSpace RealInnerProductSpace SchwartzMap Topology
  ZeroAtInfty Distributions

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
  exact_mod_cast (by linarith : -(∫ z, h z * Δ (φ : E → ℝ) z) + ∫ z, φ z * h z =
    (∫ z, φ z * g z) + (∫ z, φ z * h z) - ∫ z, φ z * (P z * h z))

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
  -- The Poincaré inequality on `H¹(E)` forces `w` to vanish.
  have hw0 : schrodingerForm hP w w = 0 := schrodingerForm_eq_zero hP (fun φ hφ hc ↦ by
    rw [← hd φ hφ hc]
    exact integral_congr_ae (hw.mono fun z hz ↦ by simp only [hz])) w
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq hP hP₀ ha hPa
  have hn : W1p.value w = 0 := by
    have := hgap w
    rw [← schrodingerForm_self hP, hw0] at this
    have hsq : ‖w‖ ^ 2 = 0 := le_antisymm (nonpos_of_mul_nonpos_right this hc) (sq_nonneg _)
    rw [← W1p.valueL_apply, norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq), map_zero]
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

/-! ### Classical solutions in the plane -/

section Plane

variable {P g : ℂ → ℝ}

/-- The weak equation `∫ Δφ h = ∫ φ (P h + g)` satisfied by an `L²` weak solution of
`-Δh + P h = -g`. -/
private theorem integral_laplacian_mul_eq_of_integral_mul_neg_laplacian_add_mul_eq
    (hP : Continuous P) (hg2 : MemLp g 2 volume) {h : ℂ → ℝ} (hh : MemLp h 2 volume)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hw : ∫ z, h z * (-Δ φ z + P z * φ z) = ∫ z, (-g) z * φ z) :
    ∫ z, Δ φ z * h z = ∫ z, φ z * (P z * h z + g z) := by
  have hΔ : Integrable (fun z ↦ Δ φ z * h z) volume :=
    hh.integrable_mul ((hφ.continuous_laplacian).memLp_of_hasCompactSupport (p := 2)
      hφc.laplacian) |>.congr (ae_of_all _ fun z ↦ mul_comm _ _)
  have hPφ : Integrable (fun z ↦ P z * φ z * h z) volume :=
    hh.integrable_mul ((hP.mul hφ.continuous).memLp_of_hasCompactSupport (p := 2)
      hφc.mul_left) |>.congr (ae_of_all _ fun z ↦ mul_comm _ _)
  have hφg : Integrable (fun z ↦ φ z * g z) volume :=
    (hφ.continuous.memLp_of_hasCompactSupport (p := 2) hφc).integrable_mul hg2
  have hgφ : ∫ z, (-g) z * φ z = -∫ z, φ z * g z := by
    rw [← integral_neg]
    exact integral_congr_ae (ae_of_all _ fun z ↦ by simp only [Pi.neg_apply]; ring)
  have hsplit : ∫ z, h z * (-Δ φ z + P z * φ z) =
      (∫ z, P z * φ z * h z) - ∫ z, Δ φ z * h z :=
    (integral_congr_ae (ae_of_all _ fun z ↦ by ring)).trans (integral_sub hPφ hΔ)
  have hsplit' : ∫ z, φ z * (P z * h z + g z) =
      (∫ z, P z * φ z * h z) + ∫ z, φ z * g z :=
    (integral_congr_ae (ae_of_all _ fun z ↦ by ring)).trans (integral_add hPφ hφg)
  rw [hsplit']
  linear_combination hsplit - hw.trans hgφ

/-- **The stationary Schrödinger equation in the plane.** Let `P` be a `Cᵏ` potential, `k ≥ 1`,
which is bounded, nonnegative, and at least `a > 0` outside a ball, and let `g` be a `Cᵏ`
square-integrable source. Then `Δu = P u + g` has a `Cᵏ⁺¹` solution `u` on the plane such that
`u` and its derivative are square integrable and `u → 0` at infinity. -/
theorem exists_contDiff_laplacian_eq_mul_add {k : ℕ∞} (hk : 1 ≤ k) (hP : ContDiff ℝ k P)
    (hP₀ : ∀ z, 0 ≤ P z) {C : ℝ} (hPC : ∀ z, P z ≤ C) {a R : ℝ} (ha : 0 < a)
    (haP : ∀ z, R < ‖z‖ → a ≤ P z) (hg : ContDiff ℝ k g) (hg2 : MemLp g 2) :
    ∃ u : ℂ → ℝ, ContDiff ℝ ((k : ℕ∞ω) + 1) u ∧ MemLp u 2 ∧ MemLp (fderiv ℝ u) 2 ∧
      Tendsto u (cocompact ℂ) (𝓝 0) ∧ ∀ z, Δ u z = P z * u z + g z := by
  have hPc : Continuous P := hP.continuous
  have hPtop : MemLp P ⊤ volume := memLp_top_of_bound hPc.aestronglyMeasurable C
    (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hP₀ z)]; exact hPC z)
  obtain ⟨h, hh, hw⟩ := exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq
    hPtop (ae_of_all _ hP₀) ha (ae_of_all _ haP) hg2.neg
  obtain ⟨u, hu, hU⟩ := mem_realSobolevFunctions.1 hh
  obtain ⟨W, hW⟩ := (Lp.memSobolev_natCast_iff_exists_wkp_value_eq (by norm_num) (by norm_num) 2
    u).1 (by simpa only [Nat.cast_ofNat] using hU)
  have hdim : Module.finrank ℝ ℂ < 2 * 2 := by rw [Complex.finrank_real_complex]; norm_num
  set v := Wkp.toZeroAtInfty hdim W
  have hhv : h =ᵐ[volume] v :=
    hu.symm.trans (hW.symm.trans (Wkp.value_ae_eq_toZeroAtInfty hdim W))
  have hh2 : MemLp h 2 volume := (Lp.memLp u).ae_eq hu
  -- The continuous representative is a distributional solution, hence `Cᵏ⁺¹` and classical.
  set F : ℂ × ℝ → ℝ := fun p ↦ P p.1 * p.2 + g p.1
  have hF : ContDiff ℝ k F := (hP.comp contDiff_fst).mul contDiff_snd |>.add (hg.comp contDiff_fst)
  have hv (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℝ)) :
      ∫ x, Δ (φ : ℂ → ℝ) x * v x = ∫ x, φ x * F (x, v x) := by
    have hφ : ContDiff ℝ 2 (φ : ℂ → ℝ) := φ.contDiff.of_le (by norm_cast)
    have e := integral_laplacian_mul_eq_of_integral_mul_neg_laplacian_add_mul_eq hPc hg2 hh2 hφ
      φ.hasCompactSupport (hw φ hφ φ.hasCompactSupport)
    have e₁ : ∫ z, Δ (φ : ℂ → ℝ) z * h z = ∫ z, Δ (φ : ℂ → ℝ) z * v z :=
      integral_congr_ae (hhv.mono fun z hz ↦ by simp only [hz])
    have e₂ : ∫ z, φ z * (P z * h z + g z) = ∫ z, φ z * F (z, v z) :=
      integral_congr_ae (hhv.mono fun z hz ↦ by simp only [hz, F])
    rwa [e₁, e₂] at e
  have hvc : ContinuousOn (v : ℂ → ℝ) (⊤ : TopologicalSpace.Opens ℂ) :=
    v.continuous.continuousOn
  have hsmooth := contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp hF.contDiffOn hvc hv
  have heq := eqOn_laplacian_of_forall_integral_laplacian_mul_eq_comp
    ((hF.of_le (by exact_mod_cast hk)).contDiffOn) hvc hv
  simp only [TopologicalSpace.Opens.coe_top] at hsmooth heq
  have hv1 : ContDiff ℝ 1 (v : ℂ → ℝ) := (contDiffOn_univ.1 hsmooth).of_le (by
    calc (1 : ℕ∞ω) ≤ (k : ℕ∞ω) := by exact_mod_cast hk
      _ ≤ (k : ℕ∞ω) + 1 := le_self_add)
  have hdv := W1p.memLp_fderiv_of_contDiffOn (Wkp.firstOrder 1 W) hv1.contDiffOn
    (by rw [Wkp.value_firstOrder]; exact ae_restrict_of_ae (Wkp.value_ae_eq_toZeroAtInfty hdim W))
  rw [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at hdv
  exact ⟨v, contDiffOn_univ.1 hsmooth, hh2.ae_eq hhv, hdv,
    ZeroAtInftyContinuousMap.zero_at_infty' v, fun z ↦ heq (Set.mem_univ z)⟩

end Plane

/-! ### Smooth solutions in the plane -/

/-- The weak form `∫ h (-f + P φ) = ∫ g φ` of `-Δh + P h = g`, with `f = Δφ`, rearranged into the
weak form `∫ f h = ∫ φ (P h - g)` of `Δh = P h - g`. -/
private theorem integral_mul_eq_integral_mul_sub_of_integral_mul_neg_add_mul_eq {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {f φ P h g : α → ℝ}
    (i₁ : Integrable (fun z ↦ f z * h z) μ) (i₂ : Integrable (fun z ↦ φ z * (P z * h z)) μ)
    (i₃ : Integrable (fun z ↦ φ z * g z) μ)
    (e : ∫ z, h z * (-f z + P z * φ z) ∂μ = ∫ z, g z * φ z ∂μ) :
    ∫ z, f z * h z ∂μ = ∫ z, φ z * (P z * h z - g z) ∂μ := by
  have e₁ : ∫ z, h z * (-f z + P z * φ z) ∂μ =
      -∫ z, f z * h z ∂μ + ∫ z, φ z * (P z * h z) ∂μ := by
    rw [← integral_neg, ← integral_add (f := fun z ↦ -(f z * h z)) i₁.neg i₂]
    exact integral_congr_ae (ae_of_all _ fun z ↦ by ring)
  have e₂ : ∫ z, φ z * (P z * h z - g z) ∂μ =
      ∫ z, φ z * (P z * h z) ∂μ - ∫ z, g z * φ z ∂μ := by
    rw [← integral_sub i₂ (i₃.congr (ae_of_all _ fun z ↦ mul_comm _ _))]
    exact integral_congr_ae (ae_of_all _ fun z ↦ by ring)
  rw [e₂, ← e, e₁]
  ring

/-- **Smooth solutions in the plane.** Let `P` be a smooth bounded potential on `ℂ`, almost
everywhere nonnegative and almost everywhere at least `a > 0` outside the closed ball of radius
`R`, and let `g` be a smooth function in `L²(ℂ)`. Then `-Δh + P h = g` has a smooth solution
`h ∈ H²(ℂ)`, which solves the equation at every point. -/
theorem exists_contDiff_mem_realSobolevFunctions_two_neg_laplacian_add_mul_eq {P : ℂ → ℝ}
    (hPs : ContDiff ℝ ∞ P) (hP : MemLp P ⊤ volume) (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ}
    (ha : 0 < a) (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z) {g : ℂ → ℝ} (hgs : ContDiff ℝ ∞ g)
    (hg : MemLp g 2 volume) :
    ∃ h : ℂ → ℝ, ContDiff ℝ ∞ h ∧ h ∈ realSobolevFunctions ℂ 2 2 ∧
      ∀ z, -Δ h z + P z * h z = g z := by
  obtain ⟨h₀, hh₀, hw₀⟩ :=
    exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq hP hP₀ ha hPa hg
  -- `H²(ℂ)` embeds into the continuous functions: pass to the continuous representative `h`.
  obtain ⟨u, hu, hS⟩ := mem_realSobolevFunctions.1 hh₀
  obtain ⟨c, hc, huc⟩ :=
    hS.exists_contDiff_ae_eq (k := 0) (by norm_num [Complex.finrank_real_complex])
  set h : ℂ → ℝ := fun z ↦ (c z).re with hdef
  have hae : h₀ =ᵐ[volume] h := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume) u, hu, huc]
      with z h₁ h₂ h₃
    simp [hdef, ← h₃, h₁, h₂]
  have hh : h ∈ realSobolevFunctions ℂ 2 2 := mem_realSobolevFunctions_of_ae_eq hh₀ hae
  have hcont : Continuous h := Complex.continuous_re.comp hc.continuous
  have hh2 : MemLp h 2 volume := memLp_of_mem_realSobolevFunctions hh
  -- The weak form of `Δh = P h - g` against test functions.
  have hweak (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℝ)) :
      ∫ z, Δ (φ : ℂ → ℝ) z * h z = ∫ z, φ z * (P z * h z - g z) := by
    have hφ : ContDiff ℝ 2 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
    have hφ2 : MemLp (φ : ℂ → ℝ) 2 volume :=
      hφ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
    have hΔ2 : MemLp (Δ (φ : ℂ → ℝ)) 2 volume :=
      hφ.continuous_laplacian.memLp_of_hasCompactSupport φ.hasCompactSupport.laplacian
    have i₁ : Integrable (fun z ↦ Δ (φ : ℂ → ℝ) z * h z) volume := hΔ2.integrable_mul hh2
    have hPh : MemLp (fun z ↦ P z * h z) 2 volume := hP.mul hh2
    have i₂ : Integrable (fun z ↦ φ z * (P z * h z)) volume := hφ2.integrable_mul hPh
    have i₃ : Integrable (fun z ↦ φ z * g z) volume := hφ2.integrable_mul hg
    have e := hw₀ φ hφ φ.hasCompactSupport
    rw [integral_congr_ae (hae.mono fun z hz ↦ by rw [hz])] at e
    exact integral_mul_eq_integral_mul_sub_of_integral_mul_neg_add_mul_eq i₁ i₂ i₃ e
  -- Interior regularity for `Δh = P h - g` makes `h` smooth and the equation pointwise.
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℂ × ℝ ↦ P p.1 * p.2 - g p.1)
      ((⊤ : TopologicalSpace.Opens ℂ) ×ˢ Set.univ) :=
    (((hPs.comp contDiff_fst).mul contDiff_snd).sub (hgs.comp contDiff_fst)).contDiffOn
  have hreg := contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp (U := ⊤) (w := h) hF
    hcont.continuousOn hweak
  have heq := eqOn_laplacian_of_forall_integral_laplacian_mul_eq_comp (U := ⊤)
    (hF.of_le (by simp)) hcont.continuousOn hweak
  refine ⟨h, by simpa [contDiffOn_univ] using hreg.of_le le_self_add, hh, fun z ↦ ?_⟩
  have := heq (Set.mem_univ z)
  simp only at this
  linarith

/-- **Smooth complex solutions in the plane.** Let `P` be a smooth bounded potential on `ℂ`,
almost everywhere nonnegative and almost everywhere at least `a > 0` outside the closed ball of
radius `R`, and let `g` be a smooth function in `L²(ℂ; ℂ)`. Then `-Δh + P h = g` has a smooth
solution `h ∈ H²(ℂ; ℂ)`, which solves the equation at every point: solve for the real and
imaginary parts separately. -/
theorem exists_contDiff_re_im_mem_realSobolevFunctions_two_neg_laplacian_add_mul_eq
    {P : ℂ → ℝ} (hPs : ContDiff ℝ ∞ P) (hP : MemLp P ⊤ volume) (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z)
    {a R : ℝ} (ha : 0 < a) (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z) {g : ℂ → ℂ}
    (hgs : ContDiff ℝ ∞ g) (hg : MemLp g 2 volume) :
    ∃ h : ℂ → ℂ, ContDiff ℝ ∞ h ∧ (fun z ↦ (h z).re) ∈ realSobolevFunctions ℂ 2 2 ∧
      (fun z ↦ (h z).im) ∈ realSobolevFunctions ℂ 2 2 ∧
      ∀ z, -Δ h z + (P z : ℂ) * h z = g z := by
  obtain ⟨h₁, hh₁s, hh₁, he₁⟩ :=
    exists_contDiff_mem_realSobolevFunctions_two_neg_laplacian_add_mul_eq hPs hP hP₀ ha hPa
      (Complex.reCLM.contDiff.comp hgs) hg.re
  obtain ⟨h₂, hh₂s, hh₂, he₂⟩ :=
    exists_contDiff_mem_realSobolevFunctions_two_neg_laplacian_add_mul_eq hPs hP hP₀ ha hPa
      (Complex.imCLM.contDiff.comp hgs) hg.im
  set h : ℂ → ℂ := fun z ↦ (h₁ z : ℂ) + h₂ z * Complex.I with hdef
  have hhs : ContDiff ℝ ∞ h := (Complex.ofRealCLM.contDiff.comp hh₁s).add
    ((Complex.ofRealCLM.contDiff.comp hh₂s).mul contDiff_const)
  have hre : (fun z ↦ (h z).re) = h₁ := funext fun z ↦ by simp [hdef]
  have him : (fun z ↦ (h z).im) = h₂ := funext fun z ↦ by simp [hdef]
  refine ⟨h, hhs, hre ▸ hh₁, him ▸ hh₂, fun z ↦ ?_⟩
  have hc : ContDiffAt ℝ 2 h z := (hhs.of_le (by simp) : ContDiff ℝ 2 h).contDiffAt
  have hΔre : (Δ h z).re = Δ h₁ z := by
    rw [← hre]; exact (hc.laplacian_CLM_comp_left (l := Complex.reCLM)).symm
  have hΔim : (Δ h z).im = Δ h₂ z := by
    rw [← him]; exact (hc.laplacian_CLM_comp_left (l := Complex.imCLM)).symm
  have e₁ := he₁ z
  have e₂ := he₂ z
  simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply] at e₁ e₂
  apply Complex.ext
  · rw [Complex.add_re, Complex.neg_re, Complex.re_ofReal_mul, hΔre, congrFun hre z]
    exact e₁
  · rw [Complex.add_im, Complex.neg_im, Complex.im_ofReal_mul, hΔim, congrFun him z]
    exact e₂

end TauCeti
