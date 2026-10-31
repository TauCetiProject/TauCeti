/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Deformation
public import TauCeti.Analysis.Complex.Wirtinger.Similarity
import Mathlib.Topology.DiscreteSubset

/-!
# Isolated zeros and local multiplicities of plane vortex sections

For the section `α = 2(p + i q)`, the two holomorphicity rows of the plane vortex equation
give `bar∂ α = (b₂ - i b₁) α / 2`. The smooth scalar similarity principle therefore factors
every nontrivial section locally as `(w - z)^n v(w)`, with `v` smooth and nonzero at `z`.
In particular the zeros are isolated. If `|α| → 1` at infinity, the zero set is finite.
These conclusions supply the local zero multiplicities and finiteness needed to associate
an effective divisor to a framed plane vortex; no prescribed-divisor existence or flux
identity is asserted here.

Only the holomorphicity rows are used. The curvature equation is unnecessary, and the
section components need only be real differentiable when the connection is smooth.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public noncomputable section

open Complex Filter Set Topology
open scoped ContDiff

namespace TauCeti.Vortex

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The two holomorphicity rows give the scalar Cauchy–Riemann equation for `α = 2(p + i q)`. -/
theorem conjWirtingerDeriv_section {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0) :
    conjWirtingerDeriv (fun w ↦ 2 * ((x w 2 : ℂ) + I * x w 3)) z 1 =
      ((x z 1 : ℂ) - I * x z 0) / 2 * (2 * ((x z 2 : ℂ) + I * x z 3)) := by
  have hP := Complex.ofRealCLM.hasFDerivAt.comp z hp.hasFDerivAt
  have hQ := Complex.ofRealCLM.hasFDerivAt.comp z hq.hasFDerivAt
  have hA := (hP.fun_add (hQ.const_mul I)).const_mul (2 : ℂ)
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at hA
  rw [conjWirtingerDeriv_apply, hA.fderiv]
  rw [equation_apply_one] at h₁
  rw [equation_apply_two] at h₂
  apply Complex.ext <;>
    simp [smul_eq_mul, Complex.ofRealCLM_apply] <;> linarith

variable (hb₁ : ContDiff ℝ ∞ (fun w ↦ x w 0))
  (hb₂ : ContDiff ℝ ∞ (fun w ↦ x w 1))
  (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
  (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)

include hb₁ hb₂ hp hq hhol

/-- A nontrivial plane vortex section factors locally as a nonnegative integral power
times a smooth nonvanishing factor, including at repeated zeros. -/
theorem exists_contDiffAt_section_eq_pow_mul
    (hne : ∃ w, (x w 2 : ℂ) + I * x w 3 ≠ 0) (z : ℂ) :
    ∃ (n : ℕ) (v : ℂ → ℂ), ContDiffAt ℝ ∞ v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, 2 * ((x w 2 : ℂ) + I * x w 3) = (w - z) ^ n * v w := by
  have ha : ContDiff ℝ ∞ (fun w ↦ ((x w 1 : ℂ) - I * x w 0) / 2) := by
    exact ((Complex.ofRealCLM.contDiff.comp hb₂).sub
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hb₁))).div_const 2
  have hα : Differentiable ℝ (fun w ↦ 2 * ((x w 2 : ℂ) + I * x w 3)) := by
    fun_prop
  apply exists_contDiffAt_pow_mul_of_conjWirtingerDeriv_eq_mul ha hα
    (fun w ↦ conjWirtingerDeriv_section (hp w) (hq w) (hhol w).1 (hhol w).2)
  simpa only [mul_ne_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, true_and] using hne

/-- A plane vortex section approaching unit modulus has finitely many zeros. -/
theorem finite_section_zeroSet
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    {w | (x w 2 : ℂ) + I * x w 3 = 0}.Finite := by
  let α := fun w ↦ 2 * ((x w 2 : ℂ) + I * x w 3)
  have ha : ContDiff ℝ ∞ (fun w ↦ ((x w 1 : ℂ) - I * x w 0) / 2) := by
    exact ((Complex.ofRealCLM.contDiff.comp hb₂).sub
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hb₁))).div_const 2
  have hα : Differentiable ℝ α := by dsimp [α]; fun_prop
  have htail : ∀ᶠ w in cocompact ℂ, α w ≠ 0 := by
    filter_upwards [hlim.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with w hw
    intro hz
    have hr := congrArg Complex.re hz
    have hi := congrArg Complex.im hz
    simp [α] at hr hi
    simp [hr, hi] at hw
  have hne : ∃ w, α w ≠ 0 := htail.exists
  have hdis : IsDiscrete {w | α w = 0} := by
    apply isDiscrete_iff_nhdsNE.mpr
    intro z _
    have hz := eventually_ne_zero_of_conjWirtingerDeriv_eq_mul ha hα
      (fun w ↦ conjWirtingerDeriv_section (hp w) (hq w) (hhol w).1 (hhol w).2) hne z
    rw [← disjoint_iff, Filter.disjoint_principal_right]
    exact hz
  obtain ⟨K, hK, hsub⟩ := Filter.mem_cocompact'.mp htail
  simp only [Set.compl_ofPred, not_not] at hsub
  have hc : IsCompact {w | α w = 0} := hK.of_isClosed_subset
    (isClosed_eq hα.continuous continuous_const) (by simpa using hsub)
  simpa [α] using hc.finite hdis

end TauCeti.Vortex
