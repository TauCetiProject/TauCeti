/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.RingTheory.Huber.Restricted.Gauss.Norm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval

/-!
# Normed evaluation on the closed polydisc

This file compares Wedhorn's evaluation homomorphism `TauCeti.ValuationSpectrum.evalAtHom` on the
unit Tate algebra `A⟨T₁, …, Tₖ⟩` with the normed restricted evaluation
`MvPowerSeries.restrictedEval₂` through the Gauss comparison
`TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv`, and transfers the Gauss-norm bound,
ultrametric Lipschitz estimate, and continuity in the evaluation argument to `evalAtHom`.

## Main results

* `TauCeti.ValuationSpectrum.evalAtHom_eq_restrictedEval₂`: comparison of `evalAtHom` with
  `MvPowerSeries.restrictedEval₂` via `restrictedMvPowerSeriesGaussEquiv`.
* `TauCeti.ValuationSpectrum.norm_evalAtHom_le` and
  `TauCeti.ValuationSpectrum.norm_evalAtHom_sub_le`: Gauss-norm bound and Lipschitz bound for
  `evalAtHom` in its evaluation point.
* `TauCeti.ValuationSpectrum.continuous_evalAtHom_arg`: for fixed `f`, `a ↦ evalAtHom a.1 a.2 f`
  is continuous on `(K°)ᵏ`.

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
  have heq : (evalAtHom a ha).comp restrictedMvPowerSeriesGaussEquiv.symm.toRingHom =
      MvPowerSeries.restrictedEval₂ (RingHom.id A) a (fun _ ↦ le_rfl) ha' := by
    refine MvPowerSeries.eq_restrictedEval₂ (RingHom.id A) a (fun _ ↦ le_rfl) ha' _
      ((continuous_evalAtHom a ha).comp continuous_restrictedMvPowerSeriesGaussEquiv_symm)
      (fun r ↦ ?_) fun i ↦ ?_
    · have hC : restrictedMvPowerSeriesGaussEquiv.symm
          (algebraMap A (MvPowerSeries.IsRestricted.subring (R := A) (fun _ : Fin k ↦ 1)) r) =
          weightedC _ isWeightFamily_one_weight r :=
        restrictedMvPowerSeriesGaussEquiv.injective (by simp)
      simp [hC]
    · have hX : restrictedMvPowerSeriesGaussEquiv.symm
          ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_monomial _ (Finsupp.single i 1) 1⟩ =
          weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i :=
        restrictedMvPowerSeriesGaussEquiv.injective (by simp)
      simp [hX]
  simpa using RingHom.congr_fun heq (restrictedMvPowerSeriesGaussEquiv f)

/-- **Gauss-norm bound on evaluation.** Evaluating `f ∈ A⟨T⟩` at a point `a` with `‖a i‖ ≤ 1`
produces an element of norm at most the unit Gauss norm of `f`. -/
theorem norm_evalAtHom_le (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i))
    (ha' : ∀ i, ‖a i‖ ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    ‖evalAtHom a ha f‖ ≤ ‖restrictedMvPowerSeriesGaussEquiv f‖ := by
  rw [evalAtHom_eq_restrictedEval₂ a ha ha' f]
  exact MvPowerSeries.norm_restrictedEval₂_le (RingHom.id A) a (fun _ ↦ le_rfl) ha' _

/-- **Ultrametric Lipschitz bound for `evalAtHom` in its argument.** If `a` and `b` lie in the
closed unit polydisc and satisfy `‖a i - b i‖ ≤ δ` for every `i`, then
`‖f(a) - f(b)‖ ≤ δ * ‖f‖`. -/
theorem norm_evalAtHom_sub_le {a b : Fin k → A} (ha : ∀ i, IsPowerBounded (a i))
    (ha' : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, IsPowerBounded (b i)) (hb' : ∀ i, ‖b i‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hab : ∀ i, ‖a i - b i‖ ≤ δ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    ‖evalAtHom a ha f - evalAtHom b hb f‖ ≤ δ * ‖restrictedMvPowerSeriesGaussEquiv f‖ := by
  rw [evalAtHom_eq_restrictedEval₂ a ha ha' f, evalAtHom_eq_restrictedEval₂ b hb hb' f]
  exact MvPowerSeries.norm_restrictedEval₂_sub_le (RingHom.id A) (fun _ ↦ le_rfl) ha' hb' hδ
    (fun i ↦ by simpa using hab i) (restrictedMvPowerSeriesGaussEquiv f)

end NormedCommRing

section NormedField

variable {k : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Evaluation of a fixed restricted series is continuous in its argument** on `(K°)ᵏ`. -/
theorem continuous_evalAtHom_arg
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    Continuous fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      evalAtHom a.val a.property f := by
  let e : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} →
      {a : Fin k → K // ∀ i, ‖a i‖ ≤ (1 : ℝ)} :=
    fun a ↦ ⟨a.val, fun i ↦ isPowerBounded_iff_norm_le_one.mp (a.property i)⟩
  have he : Continuous e := continuous_subtypeVal.subtype_mk _
  have hfun : (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
        evalAtHom a.val a.property f) =
      (fun a : {a : Fin k → K // ∀ i, ‖a i‖ ≤ (1 : ℝ)} ↦
        MvPowerSeries.restrictedEval₂ (RingHom.id K) a.val (fun _ ↦ le_rfl) a.property
          (restrictedMvPowerSeriesGaussEquiv f)) ∘ e :=
    funext fun a ↦ evalAtHom_eq_restrictedEval₂ a.val a.property (fun i ↦
      isPowerBounded_iff_norm_le_one.mp (a.property i)) f
  rw [hfun]
  exact (MvPowerSeries.continuous_restrictedEval₂_arg (RingHom.id K) (fun _ ↦ le_rfl)
    (restrictedMvPowerSeriesGaussEquiv f)).comp he

end NormedField

end TauCeti.ValuationSpectrum
