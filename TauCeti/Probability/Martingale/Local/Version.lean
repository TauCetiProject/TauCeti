/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Local.Congruence
public import TauCeti.Probability.Process.LocalProperty
public import TauCeti.Probability.Process.Predictable.Basic

/-!
# Predictable versions of local martingales

A native local martingale with almost-surely left-continuous paths has a predictable,
indistinguishable version which is again a native local martingale on the original
filtration. In particular, this applies to almost-surely continuous local martingales.
It supplies representatives suitable for stopped evaluation and stochastic integration
without completing or enlarging the filtration.

Native locality alone does not imply adaptation of the original process: its stopped
stages can hide arbitrary changes on exceptional sample points. We first use
`ProbabilityTheory.Locally.exists_stronglyAdapted_ae_eq` to recover an adapted
representative from those stages. The predictable-version theorem for adapted
left-continuous processes then applies, and progressive congruence preserves locality.
All comparisons hold simultaneously in time outside one common null set, rather than
only almost surely at each deterministic time.

No moment assumption on the initial value, finiteness assumption on the measure,
completeness, or right continuity of the filtration is required. The selected version
need not have left-continuous paths on the exceptional null set.

For almost-surely continuous local martingales, the predictable version is also almost-surely
continuous, and cross-brackets or quadratic brackets relative to strongly predictable processes
transfer to it (`TauCeti.Probability.exists_isStronglyPredictable_indist_prod_sub_initialValue_sub`
and `ProbabilityTheory.Locally.exists_isStronglyPredictable_indist_sq_sub_initialValue_sub`).

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §5.
-/

public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.Locally

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}

/-- An almost-surely left-continuous native local martingale has a predictable
indistinguishable version which remains a native local martingale for the same measure
and filtration. Literal adaptation of the original process is not assumed. -/
theorem exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P)
    (hc : ∀ᵐ ω ∂P, IsLeftContinuous (fun t ↦ X t ω)) :
    ∃ Y : ℝ≥0 → Ω → E, IsStronglyPredictable ℱ Y ∧ Y ≡ᵐ[P] X ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ Y P := by
  obtain ⟨Z, hZ, hZX⟩ := hX.exists_stronglyAdapted_ae_eq fun _ h ↦ h.stronglyAdapted
  have hcZ : ∀ᵐ ω ∂P, IsLeftContinuous (fun t ↦ Z t ω) := by
    filter_upwards [hc, hZX] with ω hω heq
    simpa only [funext heq] using hω
  obtain ⟨Y, hY, hYZ⟩ :=
    hZ.exists_isStronglyPredictable_indist_of_ae_isLeftContinuous hcZ
  have hYX : Y ≡ᵐ[P] X := hYZ.trans hZX
  exact ⟨Y, hY, hYX, hY.isStronglyProgressive.locally_martingale_of_indist hX hYX.symm⟩

/-- An almost-surely continuous native local martingale has an almost-surely continuous
predictable indistinguishable version which remains a native local martingale. -/
theorem exists_isStronglyPredictable_indist_locally_martingale_of_ae_continuous
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P) (hc : ∀ᵐ ω ∂P, Continuous (X · ω)) :
    ∃ Y : ℝ≥0 → Ω → E, IsStronglyPredictable ℱ Y ∧ (∀ᵐ ω ∂P, Continuous (Y · ω)) ∧
      Y ≡ᵐ[P] X ∧ Locally (fun U ↦ Martingale U ℱ P) ℱ Y P :=
  let ⟨Y, hY, hYX, hYl⟩ :=
    hX.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hc.mono fun _ h ↦ h.isLeftContinuous)
  ⟨Y, hY, hc.mp (hYX.mono fun _ heq hω ↦ hω.congr fun t ↦ (heq t).symm), hYX, hYl⟩

end ProbabilityTheory.Locally

/-- A family of almost-surely continuous real native local martingales with local-martingale
cross-brackets matching `M i t * M j t - M i 0 * M j 0 - A i j t` (for strongly predictable
`A i j`) admits almost-surely continuous, strongly predictable indistinguishable versions `Y i`
that remain local martingales and have strongly predictable local-martingale cross-brackets
`Y i t * Y j t - Y i 0 * Y j 0 - A i j t`. -/
theorem TauCeti.Probability.exists_isStronglyPredictable_indist_prod_sub_initialValue_sub
    {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    {M : ι → ℝ≥0 → Ω → ℝ} {A Q : ι → ι → ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, ProbabilityTheory.Locally (fun U ↦ Martingale U ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, ProbabilityTheory.Locally (fun U ↦ Martingale U ℱ P) ℱ (Q i j) P)
    (hA : ∀ i j, IsStronglyPredictable ℱ (A i j)) (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω))
    (hQM : ∀ i j, ∀ᵐ ω ∂P, ∀ t, M i t ω * M j t ω - M i 0 ω * M j 0 ω - A i j t ω = Q i j t ω) :
    ∃ Y : ι → ℝ≥0 → Ω → ℝ, (∀ i, IsStronglyPredictable ℱ (Y i)) ∧
      (∀ i, Y i ≡ᵐ[P] M i) ∧ (∀ i, ∀ᵐ ω ∂P, Continuous (Y i · ω)) ∧
      (∀ i, ProbabilityTheory.Locally (fun U ↦ Martingale U ℱ P) ℱ (Y i) P) ∧
      (∀ i j, IsStronglyPredictable ℱ
        (fun t ω ↦ Y i t ω * Y j t ω - Y i 0 ω * Y j 0 ω - A i j t ω)) ∧
      (∀ i j, ProbabilityTheory.Locally (fun U ↦ Martingale U ℱ P) ℱ
        (fun t ω ↦ Y i t ω * Y j t ω - Y i 0 ω * Y j 0 ω - A i j t ω) P) := by
  choose Y hYp hYc hYM hYl using fun i ↦
    (hM i).exists_isStronglyPredictable_indist_locally_martingale_of_ae_continuous (hcont i)
  have hY0 i : StronglyMeasurable[ℱ ⊥] (Y i 0) := by
    simpa only [bot_eq_zero] using (hYp i).isStronglyProgressive.stronglyAdapted 0
  have hQp i j : IsStronglyPredictable ℱ
      (fun t ω ↦ Y i t ω * Y j t ω - Y i 0 ω * Y j 0 ω - A i j t ω) :=
    StronglyMeasurable.sub (StronglyMeasurable.sub ((hYp i).mul (hYp j))
      ((hY0 i).mul (hY0 j)).isStronglyPredictable_snd) (hA i j)
  exact ⟨Y, hYp, hYM, hYc, hYl, hQp, fun i j ↦
    (hQp i j).isStronglyProgressive.locally_martingale_of_indist (hQ i j) <|
      (hYM i).mp <| (hYM j).mp <| (hQM i j).mono fun _ hq hj hi t ↦ by
        simpa [hi t, hj t, hi 0, hj 0] using (hq t).symm⟩

/-- An almost-surely continuous real native local martingale `M` whose quadratic bracket
`M t ^ 2 - M 0 ^ 2 - A t` (for strongly predictable `A`) is indistinguishable from a local
martingale `Q` admits an almost-surely continuous, strongly predictable indistinguishable version
`Y` that remains a local martingale with `Y t ^ 2 - Y 0 ^ 2 - A t` strongly predictable and a
local martingale. -/
theorem ProbabilityTheory.Locally.exists_isStronglyPredictable_indist_sq_sub_initialValue_sub
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    {M A Q : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun U ↦ Martingale U ℱ P) ℱ M P) (hQ : Locally (fun U ↦ Martingale U ℱ P) ℱ Q P)
    (hA : IsStronglyPredictable ℱ A) (hcont : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hQM : ∀ᵐ ω ∂P, ∀ t, M t ω ^ 2 - M 0 ω ^ 2 - A t ω = Q t ω) :
    ∃ Y : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ Y ∧ Y ≡ᵐ[P] M ∧ (∀ᵐ ω ∂P, Continuous (Y · ω)) ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ Y P ∧
      IsStronglyPredictable ℱ (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2 - A t ω) ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2 - A t ω) P := by
  obtain ⟨Y, hYp, hYM, hYc, hYl, hQp, hQY⟩ :=
    TauCeti.Probability.exists_isStronglyPredictable_indist_prod_sub_initialValue_sub
      (ι := Unit) (M := fun _ ↦ M) (A := fun _ _ ↦ A) (Q := fun _ _ ↦ Q)
      (fun _ ↦ hM) (fun _ _ ↦ hQ) (fun _ _ ↦ hA) (fun _ ↦ hcont)
      (fun _ _ ↦ by simpa only [sq] using hQM)
  exact ⟨Y (), hYp (), hYM (), hYc (), hYl (), by simpa only [sq] using hQp () (),
    by simpa only [sq] using hQY () ()⟩
