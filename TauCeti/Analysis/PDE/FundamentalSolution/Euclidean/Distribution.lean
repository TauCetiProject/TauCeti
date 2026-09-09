/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
public import Mathlib.Analysis.Distribution.Distribution
-- Used only by the local-integrability proofs below.
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# The distribution induced by the Euclidean Newtonian kernel

The totalized `n`-dimensional Newtonian kernel and its Fréchet derivative are locally integrable
in every dimension: the kernel and derivative are zero in dimensions zero and two, the
one-dimensional kernel is continuous, and the higher-dimensional singularities are integrable.
This file packages that fact with Mathlib's canonical distribution induced by a locally
integrable function.  The resulting distribution is the object to which the distributional
identity `-Δ Gₙ = δ₀` will apply.

The normalization and decay estimate are the standard ones from Evans, *Partial Differential
Equations*, Section 2.2.  The kernel and its derivative have locally integrable singularities;
their induced distribution and test-function pairing provide the input for the later proof of
the distributional identity `-Δ Gₙ = δ₀`.

## Main declarations

* `TauCeti.locallyIntegrable_newtonianKernel`: local integrability of `Gₙ`.
* `TauCeti.newtonianKernelDistribution`: the distribution induced by `Gₙ` on all of Euclidean
  space in dimensions `n ≥ 3`.
* `TauCeti.newtonianKernelDistribution_apply`: its test-function pairing.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric TopologicalSpace

open scoped Distributions

private lemma newtonianKernel_norm_le_rpow (n : ℕ) (hn : 3 ≤ n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖newtonianKernel n x‖ ≤
      ((n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        ‖x‖ ^ (-((n : ℝ) - 2)) := by
  have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hcoef : 0 < ((n : ℝ) * ((n : ℝ) - 2) *
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ := by
    apply inv_pos.mpr
    exact mul_pos (mul_pos (by positivity) (by linarith))
      (volume_real_unitBall_pos n)
  rw [newtonianKernel_def]
  by_cases hx : x = 0
  · subst x
    simp [Real.zero_rpow (by linarith : (2 : ℝ) - n ≠ 0)]
  · rw [Real.norm_of_nonneg (mul_nonneg hcoef.le (Real.rpow_nonneg (norm_nonneg x) _))]
    -- Put both powers in the exponent form used by the radial integrability criterion.
    rw [show (2 : ℝ) - n = -((n : ℝ) - 2) by ring]

private lemma newtonianKernel_zero_function : newtonianKernel 0 = 0 := by
  funext x
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx]
  exact newtonianKernel_zero 0

/-- The Newtonian kernel is locally integrable in every dimension.

In dimensions zero and two it is identically zero; in dimension one the totalized kernel is
continuous, and in dimensions at least three its radial singularity has order `n - 2`, strictly
below the ambient dimension. -/
theorem locallyIntegrable_newtonianKernel (n : ℕ) :
    LocallyIntegrable (newtonianKernel n) := by
  by_cases h : n = 0 ∨ n = 2
  · rcases h with rfl | rfl
    · rw [newtonianKernel_zero_function]
      exact locallyIntegrable_zero
    · have hzero : newtonianKernel 2 = 0 := by
        funext x
        rw [newtonianKernel_def]
        norm_num
      rw [hzero]
      exact locallyIntegrable_zero
  · have hn : n = 1 ∨ 3 ≤ n := by omega
    rcases hn with rfl | hn
    · have hcont : Continuous (newtonianKernel 1) := by
        rw [show newtonianKernel 1 = (fun x : EuclideanSpace ℝ (Fin 1) ↦
          ((1 : ℝ) * ((1 : ℝ) - 2) *
            volume.real (ball (0 : EuclideanSpace ℝ (Fin 1)) 1))⁻¹ *
            ‖x‖ ^ (2 - (1 : ℝ))) by
          -- Rewrite the opaque kernel definition so `fun_prop` can recognize the radial formula.
          funext x
          simpa using newtonianKernel_def 1 x]
        norm_num
        fun_prop
      exact hcont.locallyIntegrable
    · let C : ℝ := ((n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹
      refine locallyIntegrable_of_norm_le_rpow (μ := volume)
        (E := EuclideanSpace ℝ (Fin n))
        (F := ℝ) (f := newtonianKernel n) (α := (n : ℝ) - 2) (C := C) ?_ ?_ ?_ ?_
      · have hn1 : 1 ≤ n := le_trans (by norm_num) hn
        simpa [finrank_euclideanSpace, Fintype.card_fin] using hn1
      · have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn
        rw [finrank_euclideanSpace_fin]
        linarith
      · refine Filter.Eventually.of_forall ?_
        intro x
        dsimp [C]
        exact newtonianKernel_norm_le_rpow n hn x
      · rw [show newtonianKernel n = (fun x : EuclideanSpace ℝ (Fin n) ↦
            ((n : ℝ) * ((n : ℝ) - 2) *
              volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
              ‖x‖ ^ (2 - (n : ℝ))) by
          -- Lift the pointwise defining equation so that measurability can see the radial formula.
          funext x
          exact newtonianKernel_def n x]
        apply AEMeasurable.aestronglyMeasurable
        measurability

/-- The Fréchet derivative of the Newtonian kernel is locally integrable in every dimension.

In dimensions zero and two it is identically zero; in dimensions one and at least three its
radial order is `1 - n`, strictly below the ambient dimension. -/
theorem locallyIntegrable_fderiv_newtonianKernel (n : ℕ) :
    LocallyIntegrable (fun x => fderiv ℝ (newtonianKernel n) x) := by
  by_cases h : n = 0 ∨ n = 2
  · rcases h with rfl | rfl
    · rw [newtonianKernel_zero_function]
      simp only [fderiv_zero]
      simpa only [Pi.zero_apply] using
        (locallyIntegrable_const (μ := volume)
          (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ))
    · have hzero : newtonianKernel 2 = 0 := by
        funext x
        rw [newtonianKernel_def]
        norm_num
      rw [hzero]
      simp only [fderiv_zero]
      simpa only [Pi.zero_apply] using
        (locallyIntegrable_const (μ := volume)
          (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ))
  · have hn : n = 1 ∨ 3 ≤ n := by omega
    have hn1 : 1 ≤ n := by omega
    have hn2 : n ≠ 2 := by omega
    have hnontrivial : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
      apply Module.nontrivial_of_finrank_pos (R := ℝ)
      rw [finrank_euclideanSpace_fin]
      exact_mod_cast hn1
    have hae : ∀ᵐ x : EuclideanSpace ℝ (Fin n) ∂volume, x ≠ 0 :=
      letI := hnontrivial
      volume.ae_ne 0
    let C : ℝ := ((n : ℝ) *
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹
    refine locallyIntegrable_of_norm_le_rpow (μ := volume)
      (E := EuclideanSpace ℝ (Fin n))
      (F := EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (f := fun x => fderiv ℝ (newtonianKernel n) x)
      (α := (n : ℝ) - 1) (C := C) ?_ ?_ ?_ ?_
    · simpa [finrank_euclideanSpace, Fintype.card_fin] using hn1
    · rw [finrank_euclideanSpace_fin]
      have hnℝ : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith
    · filter_upwards [hae] with x hx
      rw [norm_fderiv_newtonianKernel n hn2 hx]
      dsimp [C]
      -- Match the derivative decay exponent with the radial-power criterion.
      rw [show 1 - (n : ℝ) = -((n : ℝ) - 1) by ring]
    · let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fun x ↦
        (-(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹) *
          ‖x‖ ^ (-(n : ℝ))) • innerSL ℝ x
      have hg : Measurable g := by
        dsimp [g]
        fun_prop
      have hfg : (fun x => fderiv ℝ (newtonianKernel n) x) =ᵐ[volume] g := by
        filter_upwards [hae] with x hx
        exact fderiv_newtonianKernel n hn2 hx
      exact hg.aestronglyMeasurable.congr hfg.symm

/-- The distribution induced by the Newtonian kernel on all of Euclidean space in dimensions
`n ≥ 3`.  The dimension hypothesis reserves this name for the higher-dimensional fundamental
solution, since the totalized kernel formula is defined in every dimension. -/
noncomputable def newtonianKernelDistribution (n : ℕ) (_hn : 3 ≤ n) :
    𝓓'((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  Distribution.ofFun (⊤ : Opens (EuclideanSpace ℝ (Fin n)))
    (newtonianKernel n) volume ⊤

/-- Evaluation of the Newtonian-kernel distribution on a smooth compactly supported
test function. -/
@[simp] theorem newtonianKernelDistribution_apply (n : ℕ) (hn : 3 ≤ n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    newtonianKernelDistribution n hn φ =
      ∫ x, φ x • newtonianKernel n x := by
  rw [newtonianKernelDistribution, Distribution.ofFun_apply]
  exact (locallyIntegrable_newtonianKernel n).locallyIntegrableOn _

end TauCeti

end
