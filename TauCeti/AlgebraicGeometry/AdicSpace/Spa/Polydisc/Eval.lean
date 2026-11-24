/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm

import TauCeti.RingTheory.Huber.Restricted.Comparison

/-!
# Evaluation bounds and Lipschitz continuity on the closed polydisc

Evaluating a restricted power series `f ∈ R⟨T₁, …, Tₖ⟩` on the unit polydisc `(R°)ᵏ` over a
complete ultrametric normed commutative ring is bounded by, and Lipschitz with constant, the unit
Gauss norm of `f`.

## Main results

* `TauCeti.ValuationSpectrum.norm_evalAtHom_le`: evaluation of a restricted series on `(R°)ᵏ` is
  bounded by its unit Gauss norm.
* `TauCeti.ValuationSpectrum.norm_evalAtHom_sub_evalAtHom_le`: evaluation of a restricted series on
  `(R°)ᵏ` is Lipschitz with constant its unit Gauss norm.
* `TauCeti.ValuationSpectrum.lipschitzWith_evalAtHom_apply` and
  `TauCeti.ValuationSpectrum.continuous_evalAtHom_apply`: evaluation of a fixed series is Lipschitz
  and continuous in `a ∈ (K°)ᵏ`.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber Filter Topology
open scoped NNReal

section EvalLipschitz

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- **Evaluation of a restricted power series is bounded on the closed unit polydisc** by its unit
Gauss norm. -/
theorem norm_evalAtHom_le {a : Fin k → R}
    (ha : ∀ i, IsPowerBounded (a i)) (ha₁ : ∀ i, ‖a i‖ ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    ‖evalAtHom a ha f‖ ≤
      MvPowerSeries.gaussNorm norm (fun _ : Fin k ↦ (1 : ℝ)) (f : MvPowerSeries (Fin k) R) := by
  rw [evalAtHom_def, ← coe_restrictedMvPowerSeriesGaussEquiv f, ← MvPowerSeries.norm_eq_gaussNorm]
  simpa only [one_mul] using norm_weightedEvalHom_le continuousAt_id (C := 1)
    (fun r ↦ by simp) ha₁ _ f

/-- **Evaluation of a restricted power series is Lipschitz on the closed unit polydisc**, with
Lipschitz constant its unit Gauss norm. -/
theorem norm_evalAtHom_sub_evalAtHom_le {a b : Fin k → R}
    (ha : ∀ i, IsPowerBounded (a i)) (hb : ∀ i, IsPowerBounded (b i))
    (ha₁ : ∀ i, ‖a i‖ ≤ 1) (hb₁ : ∀ i, ‖b i‖ ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    ‖evalAtHom a ha f - evalAtHom b hb f‖ ≤
      MvPowerSeries.gaussNorm norm (fun _ : Fin k ↦ (1 : ℝ)) (f : MvPowerSeries (Fin k) R) *
        ‖a - b‖ := by
  rw [evalAtHom_def, evalAtHom_def, ← coe_restrictedMvPowerSeriesGaussEquiv f,
    ← MvPowerSeries.norm_eq_gaussNorm]
  simpa only [one_mul] using norm_weightedEvalHom_sub_weightedEvalHom_le continuousAt_id (C := 1)
    (fun r ↦ by simp) ha₁ _ hb₁ _ f

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- For a fixed restricted power series `f ∈ K⟨T₁, …, Tₖ⟩`, evaluation `a ↦ f(a)` is Lipschitz on
`(K°)ᵏ` with constant the unit Gauss norm of `f`. -/
theorem lipschitzWith_evalAtHom_apply
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    LipschitzWith
      (Real.toNNReal (MvPowerSeries.gaussNorm norm (fun _ : Fin k ↦ (1 : ℝ))
        (f : MvPowerSeries (Fin k) K)))
      fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦ evalAtHom a.val a.property f := by
  refine LipschitzWith.of_dist_le_mul fun a b ↦ ?_
  have hnonneg : 0 ≤ MvPowerSeries.gaussNorm norm (fun _ : Fin k ↦ (1 : ℝ))
      (f : MvPowerSeries (Fin k) K) := by
    rw [← coe_restrictedMvPowerSeriesGaussEquiv f, ← MvPowerSeries.norm_eq_gaussNorm]
    exact norm_nonneg _
  rw [Real.coe_toNNReal _ hnonneg, dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
  exact norm_evalAtHom_sub_evalAtHom_le a.property b.property
    (fun i ↦ isPowerBounded_iff_norm_le_one.mp (a.property i))
    (fun i ↦ isPowerBounded_iff_norm_le_one.mp (b.property i)) f

/-- For a fixed restricted power series `f ∈ K⟨T₁, …, Tₖ⟩`, evaluation `a ↦ f(a)` is continuous on
`(K°)ᵏ`. -/
theorem continuous_evalAtHom_apply
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    Continuous fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      evalAtHom a.val a.property f :=
  (lipschitzWith_evalAtHom_apply f).continuous

end EvalLipschitz

end TauCeti.ValuationSpectrum
