/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.RingTheory.Huber.Restricted.Comparison.Eval

/-!
# Normed evaluation on the closed polydisc

This file compares Wedhorn's evaluation homomorphism `TauCeti.ValuationSpectrum.evalAtHom` on the
unit Tate algebra `A⟨T₁, …, Tₖ⟩` with the normed restricted evaluation
`MvPowerSeries.restrictedEval₂` by specializing the Huber evaluation comparison in
`TauCeti.RingTheory.Huber.Restricted.Comparison.Eval`, and transfers the Gauss-norm bound,
Lipschitz continuity, and continuity in the evaluation argument to `evalAtHom`.

## Main results

* `TauCeti.ValuationSpectrum.evalAtHom_eq_restrictedEval₂`: comparison of `evalAtHom` with
  `MvPowerSeries.restrictedEval₂` via `restrictedMvPowerSeriesGaussEquiv`.
* `TauCeti.ValuationSpectrum.norm_evalAtHom_le`: Gauss-norm bound for `evalAtHom`.
* `TauCeti.ValuationSpectrum.norm_evalAtHom_sub_evalAtHom_le`: evaluation of a restricted series on
  `(A°)ᵏ` is Lipschitz with constant its unit Gauss norm.
* `TauCeti.ValuationSpectrum.lipschitzWith_evalAtHom_apply` and
  `TauCeti.ValuationSpectrum.continuous_evalAtHom_arg`: for fixed `f`, `a ↦ evalAtHom a.1 a.2 f`
  is Lipschitz and continuous on `(K°)ᵏ`.

## References

* S. Howe and C. Klevdal, *Admissible pairs and p-adic Hodge structures II: the bi-analytic
  Ax–Lindemann theorem*, arXiv:2308.11064v2, proof of Lemma 9.3.5, p. 60.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

section NormedCommRing

variable {k : ℕ} {A : Type*} [NormedCommRing A] [IsUltrametricDist A] [CompleteSpace A]

/-- **Comparison of `evalAtHom` with normed restricted evaluation.** Through the Gauss-norm
comparison `restrictedMvPowerSeriesGaussEquiv`, Wedhorn's evaluation `evalAtHom a ha` agrees with
`MvPowerSeries.restrictedEval₂` along the identity of `A`. -/
theorem evalAtHom_eq_restrictedEval₂ (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i))
    (ha' : ∀ i, ‖a i‖ ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    evalAtHom a ha f =
      MvPowerSeries.restrictedEval₂ (RingHom.id A) a (fun _ ↦ le_rfl) ha'
        (restrictedMvPowerSeriesGaussEquiv f) := by
  rw [evalAtHom_eq_weightedEvalHom,
    weightedEvalHom_eq_restrictedEval₂OfBound (C := 1) continuousAt_id (fun r ↦ by simp) ha',
    RingHom.restrictedEval₂OfBound_eq_restrictedEval₂]

/-- **Gauss-norm bound on evaluation.** Evaluating `f ∈ A⟨T⟩` at a point `a` with `‖a i‖ ≤ 1`
produces an element of norm at most the unit Gauss norm of `f`. -/
theorem norm_evalAtHom_le (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i))
    (ha' : ∀ i, ‖a i‖ ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    ‖evalAtHom a ha f‖ ≤ ‖restrictedMvPowerSeriesGaussEquiv f‖ := by
  rw [evalAtHom_eq_restrictedEval₂ a ha ha' f]
  exact MvPowerSeries.norm_restrictedEval₂_le (RingHom.id A) a (fun _ ↦ le_rfl) ha' _

/-- **Evaluation of a restricted power series is Lipschitz on the closed unit polydisc**, with
Lipschitz constant its unit Gauss norm. -/
theorem norm_evalAtHom_sub_evalAtHom_le {a b : Fin k → A}
    (ha : ∀ i, IsPowerBounded (a i)) (hb : ∀ i, IsPowerBounded (b i))
    (ha₁ : ∀ i, ‖a i‖ ≤ 1) (hb₁ : ∀ i, ‖b i‖ ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    ‖evalAtHom a ha f - evalAtHom b hb f‖ ≤
      ‖restrictedMvPowerSeriesGaussEquiv f‖ * ‖a - b‖ := by
  rw [evalAtHom_eq_restrictedEval₂ a ha ha₁ f, evalAtHom_eq_restrictedEval₂ b hb hb₁ f]
  simpa only [mul_comm ‖a - b‖] using
    MvPowerSeries.norm_restrictedEval₂_sub_le (RingHom.id A) (fun _ ↦ le_rfl) ha₁ hb₁
      (norm_nonneg (a - b))
      (fun i ↦ by simpa only [mul_one, Pi.sub_apply] using norm_le_pi_norm (a - b) i)
      (restrictedMvPowerSeriesGaussEquiv f)

end NormedCommRing

section NormedField

variable {k : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- For a fixed restricted power series `f ∈ K⟨T₁, …, Tₖ⟩`, evaluation `a ↦ f(a)` is Lipschitz on
`(K°)ᵏ` with constant the unit Gauss norm of `f`. -/
theorem lipschitzWith_evalAtHom_apply
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    LipschitzWith ‖restrictedMvPowerSeriesGaussEquiv f‖₊
      fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦ evalAtHom a.val a.property f := by
  refine LipschitzWith.of_dist_le_mul fun a b ↦ ?_
  rw [coe_nnNorm, dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
  exact norm_evalAtHom_sub_evalAtHom_le a.property b.property
    (fun i ↦ isPowerBounded_iff_norm_le_one.mp (a.property i))
    (fun i ↦ isPowerBounded_iff_norm_le_one.mp (b.property i)) f

/-- **Evaluation of a fixed restricted series is continuous in its argument** on `(K°)ᵏ`. -/
theorem continuous_evalAtHom_arg
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    Continuous fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      evalAtHom a.val a.property f :=
  (lipschitzWith_evalAtHom_apply f).continuous

end NormedField

end TauCeti.ValuationSpectrum
