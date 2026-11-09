/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.ConditionalExpectation.WithDensity
public import TauCeti.Probability.Martingale.Basic

/-!
# Martingales under a change of measure

Let `Q = μ.withDensity w` be finite, and write `Z_t = E_μ[w.toReal | ℱ_t]` for its
conditional density. An adapted process `X`, integrable at each time under `Q`, is a
`Q`-martingale exactly when `Z X` is a `μ`-martingale. This is the measure-theoretic
step in transferring martingale representations: one first represents the weighted
process under the original measure, then transforms its integrand.

The theorem permits vanishing densities; equivalence of the measures is unnecessary.
It makes no assertion about stochastic integrals, path regularity or representation.
A second form accepts any strongly adapted fixed-time version of the conditional
density, allowing a continuous density martingale to be used without identifying its
representative pointwise with conditional expectations. Neither form upgrades
fixed-time agreement to indistinguishability.

The proof uses the conditional-density set-integral identity from
`MeasureTheory.StronglyMeasurable.setIntegral_condExp_toReal_smul` and the native
conditional-expectation characterization of martingales.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.5.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Preorder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ι mΩ} [SigmaFiniteFiltration μ ℱ]
  {w : Ω → ℝ≥0∞} {X : ι → Ω → E}

/-- An adapted process integrable under a finite density change is a martingale
under that measure exactly when its conditional-density-weighted process is a
martingale under the original measure. The density need not be strictly positive. -/
theorem StronglyAdapted.martingale_withDensity_iff (hX : StronglyAdapted ℱ X)
    (hw : AEMeasurable w μ) [IsFiniteMeasure (μ.withDensity w)]
    (hint : ∀ t, Integrable (X t) (μ.withDensity w)) :
    Martingale X ℱ (μ.withDensity w) ↔
      Martingale (fun t ω ↦ μ[fun x ↦ (w x).toReal | ℱ t] ω • X t ω) ℱ μ := by
  have hadapt : StronglyAdapted ℱ
      (fun t ω ↦ μ[fun x ↦ (w x).toReal | ℱ t] ω • X t ω) :=
    fun t ↦ stronglyMeasurable_condExp.smul (hX t)
  have hint' := fun t ↦ (hX t).integrable_condExp_toReal_smul hw (hint t)
  rw [hX.martingale_iff_setIntegral_eq hint, hadapt.martingale_iff_setIntegral_eq hint']
  refine forall_congr' fun s ↦ forall_congr' fun t ↦ imp_congr_right fun hst ↦ ?_
  refine forall_congr' fun A ↦ imp_congr_right fun hA ↦ ?_
  rw [(hX s).setIntegral_condExp_toReal_smul (ℱ.le s) hw (hint s) hA,
    (hX t).setIntegral_condExp_toReal_smul (ℱ.le t) hw (hint t) (ℱ.mono hst A hA)]

/-- The martingale change-of-measure criterion with any strongly adapted version
`Z` of the conditional density, such as a selected continuous density process.
Only fixed-time almost-sure agreement is required. -/
theorem StronglyAdapted.martingale_withDensity_iff_of_ae_eq_condExp
    (hX : StronglyAdapted ℱ X) (hw : AEMeasurable w μ)
    [IsFiniteMeasure (μ.withDensity w)] (hint : ∀ t, Integrable (X t) (μ.withDensity w))
    {Z : ι → Ω → ℝ} (hZ : StronglyAdapted ℱ Z)
    (hZeq : ∀ t, Z t =ᵐ[μ] μ[fun x ↦ (w x).toReal | ℱ t]) :
    Martingale X ℱ (μ.withDensity w) ↔ Martingale (fun t ω ↦ Z t ω • X t ω) ℱ μ := by
  rw [hX.martingale_withDensity_iff hw hint]
  have heq : ∀ t, (fun ω ↦ Z t ω • X t ω) =ᵐ[μ]
      (fun ω ↦ μ[fun x ↦ (w x).toReal | ℱ t] ω • X t ω) := fun t ↦
    (hZeq t).mono fun ω hω ↦ congrArg (· • X t ω) hω
  exact ⟨fun h ↦ h.congr (fun t ↦ (hZ t).smul (hX t)) (fun t ↦ (heq t).symm),
    fun h ↦ h.congr (fun t ↦ stronglyMeasurable_condExp.smul (hX t)) heq⟩

end MeasureTheory
