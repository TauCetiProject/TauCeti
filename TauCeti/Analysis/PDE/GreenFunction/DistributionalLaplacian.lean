/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.GreenFunction.Ball
public import Mathlib.Analysis.Distribution.TestFunction
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.DistributionalLaplacian
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Distribution

/-!
# Distributional Laplacian of the Green kernel of the unit ball

For a pole in the open unit ball, the Green kernel is the Newtonian fundamental solution
minus a correction harmonic throughout the ball. Thus its distributional negative Laplacian
is the Dirac mass at the pole. This is the interior equation for the Dirichlet Green
function; its zero boundary values are proved with the kernel construction.

The argument is the fundamental-solution identity and Green's second identity against
test functions, as in Evans, *Partial Differential Equations*, Section 2.2.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Metric Set TopologicalSpace
open scoped Distributions RealInnerProductSpace

variable {n : ℕ}

/-- The reflected-pole corrector is harmonic throughout the open unit ball whenever the
pole lies inside it. -/
theorem harmonicOnNhd_ballGreenCorrector {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ < 1) : HarmonicOnNhd (ballGreenCorrector n x)
      (⟨ball 0 1, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin n))) := by
  intro y hy
  have hy' : ‖y‖ < 1 := by simpa using hy
  exact harmonicAt_ballGreenCorrector
    (norm_sq_mul_norm_sq_sub_two_mul_inner_add_one_pos
      ((mul_le_of_le_one_right (norm_nonneg x) hy'.le).trans_lt hx).ne)

/-- The unit-ball Green kernel has distributional negative Laplacian equal to a Dirac mass
at its pole. The test function is supported strictly inside the ball, so no boundary term
appears. -/
theorem integral_laplacian_mul_ballGreenKernel (hn : 3 ≤ n)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1)
    (φ : 𝓓((⟨ball 0 1, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    ∫ y, Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ) y * ballGreenKernel n x y =
      -(φ : EuclideanSpace ℝ (Fin n) → ℝ) x := by
  let ψ := LineDeriv.laplacianCLM ℝ (EuclideanSpace ℝ (Fin n)) _ φ
  have hψ : ∀ y, (ψ : EuclideanSpace ℝ (Fin n) → ℝ) y = Δ (φ : _ → ℝ) y :=
    fun y => TestFunction.laplacianCLM_apply φ y
  have hc : LocallyIntegrableOn (ballGreenCorrector n x)
      (⟨ball 0 1, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin n))) volume :=
    (harmonicOnNhd_ballGreenCorrector hx).contDiffOn.continuousOn.locallyIntegrableOn
      (⟨ball 0 1, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin n))).isOpen.measurableSet
  have hcint : Integrable (fun y => Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ) y *
      ballGreenCorrector n x y) volume := by
    simpa only [← hψ, smul_eq_mul] using integrable_smul_of_locallyIntegrableOn hc ψ
  have hni : Integrable (fun y => Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ) y *
      newtonianKernel n (y - x)) volume := by
    let g : EuclideanSpace ℝ (Fin n) → ℝ := fun y => Δ (φ : _ → ℝ) (y + x)
    have hgcont : Continuous g := by
      have hψcont : Continuous (ψ : EuclideanSpace ℝ (Fin n) → ℝ) := ψ.contDiff.continuous
      have hgeq : g = (ψ : EuclideanSpace ℝ (Fin n) → ℝ) ∘ (fun y => y + x) :=
        funext fun y => (hψ (y + x)).symm
      rw [hgeq]
      exact hψcont.comp (continuous_id.add continuous_const)
    have hgcpt : HasCompactSupport g := by
      have hψcpt : HasCompactSupport (ψ : EuclideanSpace ℝ (Fin n) → ℝ) := ψ.hasCompactSupport
      have hgeq : g = (ψ : EuclideanSpace ℝ (Fin n) → ℝ) ∘ (Homeomorph.addRight x) :=
        funext fun y => (hψ (y + x)).symm
      rw [hgeq]
      exact hψcpt.comp_homeomorph (Homeomorph.addRight x)
    have hgi : Integrable (fun y => newtonianKernel n y * g y) volume :=
      (locallyIntegrable_newtonianKernel n).integrable_smul_right_of_hasCompactSupport
        hgcont hgcpt
    have hgi' : Integrable (fun y => newtonianKernel n (y - x) * g (y - x)) volume :=
      hgi.comp_sub_right x
    simpa only [g, sub_add_cancel, mul_comm] using hgi'
  have hcorrector : ∫ y, Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ) y *
      ballGreenCorrector n x y = 0 := by
    simpa only [smul_eq_mul] using
      (harmonicOnNhd_ballGreenCorrector hx).integral_laplacian_smul_eq_zero (μ := volume) φ
  rw [show (fun y => Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ) y * ballGreenKernel n x y) =
      (fun y => Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ) y * newtonianKernel n (y - x) -
        Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ) y * ballGreenCorrector n x y) by
        funext y; rw [ballGreenKernel_def]; ring]
  rw [integral_sub hni hcint, hcorrector, sub_zero]
  exact integral_laplacian_mul_newtonianKernel_sub hn (φ.contDiff.of_le (by norm_num))
    φ.hasCompactSupport x

end TauCeti

end
