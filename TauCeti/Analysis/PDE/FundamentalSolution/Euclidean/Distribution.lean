/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# The distribution induced by the Euclidean Newtonian kernel

The singularity of the `n`-dimensional Newtonian kernel is locally integrable for `n ≥ 3`.
This file packages that fact with Mathlib's canonical distribution induced by a locally
integrable function.  The resulting distribution is the object to which the distributional
identity `-Δ Gₙ = δ₀` will apply.

The decay estimate is the standard one from Evans, *Partial Differential Equations*, Section 2.2.
The local-integrability argument uses Mathlib's general radial-power criterion
`MeasureTheory.locallyIntegrable_of_norm_le_rpow`.  A search of the local LeanPool archive found
related three-dimensional potential estimates in
`LeanPool/Clawristotle/NewtonianPotential.lean`, but no distributional Newtonian identity; no
LeanPool code is copied here.

## Main declarations

* `TauCeti.locallyIntegrable_newtonianKernel`: local integrability of `Gₙ`.
* `TauCeti.newtonianKernelDistribution`: the distribution induced by `Gₙ` on all of Euclidean
  space.
* `TauCeti.newtonianKernelDistribution_apply`: its test-function pairing.

The distributional Laplacian identity and its flux-to-test-function proof remain to be formalized.
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

/-- The Newtonian kernel is locally integrable in every dimension `n ≥ 3`.

The exponent `n - 2` is strictly smaller than the ambient dimension `n`, so the radial
singularity is covered by Mathlib's general `rpow` integrability theorem. -/
theorem locallyIntegrable_newtonianKernel (n : ℕ) (hn : 3 ≤ n) :
    LocallyIntegrable (newtonianKernel n) := by
  let C : ℝ := ((n : ℝ) * ((n : ℝ) - 2) *
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

/-- The Fréchet derivative of the Newtonian kernel is locally integrable away from its pole.

Its norm has the radial singularity `‖x‖^(1-n)`, whose exponent is still below the ambient
dimension.  This is the integrability input for the punctured-domain integration-by-parts step
in the distributional fundamental-solution proof. -/
theorem locallyIntegrable_fderiv_newtonianKernel (n : ℕ) (hn : 3 ≤ n) :
    LocallyIntegrable (fun x => fderiv ℝ (newtonianKernel n) x) := by
  have hnontrivial : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [finrank_euclideanSpace_fin]
    omega
  -- The derivative formula is needed only off the pole; its exceptional singleton is
  -- null for Euclidean volume in these nontrivial dimensions.
  have hpunct : NeBot (nhdsWithin (0 : EuclideanSpace ℝ (Fin n))
      ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ) :=
    @Real.punctured_nhds_module_neBot (EuclideanSpace ℝ (Fin n)) _ _ _ hnontrivial _ _ 0
  have hnull : NullSingletonClass (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    @Measure.IsAddHaarMeasure.nullSingletonClass (EuclideanSpace ℝ (Fin n))
      _ _ _ _ _ _ _ hpunct volume inferInstance
  have hae : ∀ᵐ x : EuclideanSpace ℝ (Fin n) ∂volume, x ≠ 0 :=
    @Measure.ae_ne (EuclideanSpace ℝ (Fin n)) _ volume hnull 0
  let C : ℝ := ((n : ℝ) *
    volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹
  refine locallyIntegrable_of_norm_le_rpow (μ := volume)
    (E := EuclideanSpace ℝ (Fin n))
    (F := EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (f := fun x => fderiv ℝ (newtonianKernel n) x)
    (α := (n : ℝ) - 1) (C := C) ?_ ?_ ?_ ?_
  · have hn1 : 1 ≤ n := le_trans (by norm_num) hn
    simpa [finrank_euclideanSpace, Fintype.card_fin] using hn1
  · rw [finrank_euclideanSpace_fin]
    linarith
  · filter_upwards [hae] with x hx
    rw [norm_fderiv_newtonianKernel n (by omega) hx]
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
      exact fderiv_newtonianKernel n (by omega) hx
    exact hg.aestronglyMeasurable.congr hfg.symm

/-- The distribution induced by the Newtonian kernel on all of Euclidean space. -/
noncomputable def newtonianKernelDistribution (n : ℕ) :
    𝓓'((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  Distribution.ofFun (⊤ : Opens (EuclideanSpace ℝ (Fin n)))
    (newtonianKernel n) volume ⊤

/-- Evaluation of the Newtonian-kernel distribution on a smooth compactly supported
test function. -/
theorem newtonianKernelDistribution_apply (n : ℕ) (hn : 3 ≤ n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    newtonianKernelDistribution n φ =
      ∫ x, φ x • newtonianKernel n x := by
  rw [newtonianKernelDistribution, Distribution.ofFun_apply]
  exact (locallyIntegrable_newtonianKernel n hn).locallyIntegrableOn _

end TauCeti

end
