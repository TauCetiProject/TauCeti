/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Extension
public import TauCeti.Analysis.Distribution.Rectifiable.Mass
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The mass measure and Borel restrictions of the current of an oriented set

Let `V` be a finite-dimensional real inner product space, `Ω` an open subset, `θ : V → ℝ` a
multiplicity locally integrable on `Ω` for `μHE[k]`, and `τ : V → Fin k → V` measurable orientation
frames, orthonormal wherever `θ` does not vanish, with frame current
`T = Distribution.frameCurrent θ τ`.

The **mass measure** of `T` is `|θ| μHE[k]` on `Ω` (`Distribution.massMeasure_frameCurrent`): as a
measure on `Ω`, `‖T‖ = ((μHE[k]).withDensity |θ|).comap (↑)`. This measure is locally finite since
`θ` is locally integrable
(`MeasureTheory.LocallyIntegrableOn.isLocallyFiniteMeasure_comap_withDensity`), hence outer
regular, and it has the value
`∫_{U ∩ Ω} |θ| dμHE[k]` on `Ω ∩ U` for every open `U`, which is the local mass of `T` on `U`
(`Distribution.localMass_frameCurrent`); the mass measure is the only outer regular measure with
these values (`Distribution.eq_massMeasure_of_preimage_coe`).

The **Borel restriction** of `T` to a Borel set `A` is the frame current of the multiplicity
`1_A θ` (`Distribution.massRestrict_frameCurrent`); in Simon's notation,
`τ(M, θ, ξ) ⌞ A = τ(M ∩ A, θ, ξ)`. The current `R` of `1_A θ` has mass measure `‖T‖ ⌞ A`, the
current `R'` of `1_{Aᶜ} θ` has mass measure `‖T‖ ⌞ Aᶜ`, and `T = R + R'`; such a splitting
identifies `R` as `T ⌞ A` (`Distribution.massRestrict_eq_of_massMeasure_eq`).

## Main declarations

* `Distribution.massMeasure_frameCurrent`: `‖T‖ = |θ| μHE[k]` on `Ω`, and
  `Distribution.massMeasure_frameCurrent_indicator`: the current of `1_A θ` has mass measure
  `‖T‖ ⌞ A`.
* `Distribution.massRestrict_frameCurrent`: the Borel restriction of `T` to `A` is the frame
  current of `1_A θ`.

## References

* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §3 (integer multiplicity
  rectifiable currents `τ(M, θ, ξ)` and their mass).
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction MeasureTheory exteriorPower
open scoped Distributions ENNReal RealInnerProductSpace Topology

namespace Distribution

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {Ω : Opens V} {n : ℕ∞} {k : ℕ} {θ : V → ℝ}
  {τ : V → Fin k → V}

/-- **The mass measure of a frame current** is `|θ| μHE[k]` on `Ω`, for a multiplicity `θ`
locally integrable on `Ω` and measurable frames `τ`, orthonormal where `θ` does not vanish. -/
theorem massMeasure_frameCurrent (hθ : LocallyIntegrableOn θ Ω μHE[k]) (hτ : Measurable τ)
    (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) :
    massMeasure (frameCurrent θ τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      (μHE[k].withDensity fun x ↦ ‖θ x‖ₑ).comap ((↑) : Ω → V) := by
  have hemb : MeasurableEmbedding ((↑) : Ω → V) := .subtypeVal Ω.isOpen.measurableSet
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  have := hθ.isLocallyFiniteMeasure_comap_withDensity Ω.isOpen.measurableSet
  refine (eq_massMeasure_of_preimage_coe (hasLocallyFiniteMass_frameCurrent hθ hτo) _
    fun U hU ↦ ?_).symm
  rw [hemb.comap_preimage, withDensity_apply _ (hU.measurableSet.inter hemb.measurableSet_range),
    localMass_frameCurrent hθ hτ hτo hU, Subtype.range_val_subtype, SetLike.setOfPred_mem_eq]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem orthonormal_of_indicator_ne_zero (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x))
    (A : Set V) (x : V) (hx : A.indicator θ x ≠ 0) : Orthonormal ℝ (τ x) := by
  by_cases hxA : x ∈ A
  · exact hτo x (by simpa [hxA] using hx)
  · simp [hxA] at hx

/-- The mass measure of the frame current of `1_A θ` is the mass measure of the frame current of
`θ` restricted to `A`. -/
theorem massMeasure_frameCurrent_indicator (hθ : LocallyIntegrableOn θ Ω μHE[k])
    (hτ : Measurable τ) (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) {A : Set V}
    (hA : MeasurableSet A) :
    massMeasure (frameCurrent (A.indicator θ) τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      (massMeasure (frameCurrent θ τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)).restrict
        ((↑) ⁻¹' A) := by
  rw [massMeasure_frameCurrent
      ((hθ.mono_set inter_subset_left).indicator_of_closure hA.nullMeasurableSet) hτ
      (orthonormal_of_indicator_ne_zero hτo A),
    massMeasure_frameCurrent hθ hτ hτo]
  simp_rw [eNorm_indicator_eq_indicator_eNorm]
  rw [withDensity_indicator hA, ← restrict_withDensity hA]
  exact (MeasurableEmbedding.subtypeVal Ω.isOpen.measurableSet).comap_restrict _ _

/-- **Borel restriction of a frame current.** For a multiplicity `θ` locally integrable on `Ω`,
measurable frames `τ`, orthonormal where `θ` does not vanish, and a measurable set `A`, the
restriction `T ⌞ A` of the frame current `T` of `(θ, τ)` is the frame current of `(1_A θ, τ)`. -/
theorem massRestrict_frameCurrent (hθ : LocallyIntegrableOn θ Ω μHE[k]) (hτ : Measurable τ)
    (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) {A : Set V} (hA : MeasurableSet A) :
    massRestrict (frameCurrent θ τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
        (hA.preimage measurable_subtypeVal) =
      frameCurrent (A.indicator θ) τ := by
  have hθA := (hθ.mono_set inter_subset_left).indicator_of_closure hA.nullMeasurableSet
  have hθAc := (hθ.mono_set inter_subset_left).indicator_of_closure hA.compl.nullMeasurableSet
  exact massRestrict_eq_of_massMeasure_eq
    (hasLocallyFiniteMass_frameCurrent hθA (orthonormal_of_indicator_ne_zero hτo A))
    (hasLocallyFiniteMass_frameCurrent hθAc (orthonormal_of_indicator_ne_zero hτo Aᶜ))
    (frameCurrent_eq_add_of_ae hθ hτ hτo hθA hτ (orthonormal_of_indicator_ne_zero hτo A) hθAc hτ
      (orthonormal_of_indicator_ne_zero hτo Aᶜ) (ae_of_all _ fun x _ ω ↦ by
        by_cases hx : x ∈ A <;> simp [hx]))
    _ (massMeasure_frameCurrent_indicator hθ hτ hτo hA)
    (massMeasure_frameCurrent_indicator hθ hτ hτo hA.compl)

end Distribution
