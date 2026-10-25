/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.TotalVariation

/-!
# The perimeter of a set in an open set

The **perimeter** of a set `s` in an open set `Ω` of a finite-dimensional real inner product space
is the total variation of its indicator on `Ω` (`TauCeti.perimeter`). For a measurable `s` this is
De Giorgi's extended perimeter

`P(s; Ω) = ⨆ { ∫_s div φ | φ ∈ 𝓓(Ω, E), ‖φ x‖ ≤ 1 for all x }`

(`TauCeti.perimeter_eq_iSup`), defined without any regularity of its topological boundary. It is
the measure-theoretic notion of boundary area: a measurable set has finite perimeter in `Ω`
exactly when `P(s; Ω) < ∞`, which does not require `s` to have finite volume. The perimeter is
meaningful when `s ∩ Ω` is null-measurable; otherwise the integrals in the supremum may be
Mathlib's junk value `0` for non-integrable functions, and the perimeter may then be a junk value
carrying no geometric meaning.

The perimeter only sees `s` up to null sets (`TauCeti.perimeter_congr_ae`), so topological
frontier and perimeter can differ. Against an additive Haar measure, complements have the same
perimeter (`TauCeti.perimeter_compl`), since their indicators differ by a constant. Lower
semicontinuity under local convergence in measure (`TauCeti.perimeter_le_liminf`) supplies
the semicontinuity half of the direct method for perimeter problems.

## Main declarations

* `TauCeti.perimeter μ Ω s`: the perimeter of `s` in `Ω`.
* `TauCeti.perimeter_eq_iSup`: the perimeter of a null-measurable set as a supremum of `∫_s div φ`.
* `TauCeti.perimeter_congr_ae`, `TauCeti.perimeter_mono` and `TauCeti.perimeter_iSup`: invariance
  under null modification inside `Ω`, and monotonicity and inner continuity in `Ω`.
* `TauCeti.perimeter_compl`, `TauCeti.perimeter_empty` and `TauCeti.perimeter_univ`.
* `TauCeti.perimeter_le_liminf`: lower semicontinuity of the perimeter.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1 and
  Proposition 12.15.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Filter TestFunction Set
open scoped ENNReal Distributions Topology symmDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {μ : Measure E} {Ω Ω' : Opens E} {s t : Set E}

/-- The **perimeter** of a set `s` in the open set `Ω`, relative to the measure `μ`: the total
variation of the indicator of `s` on `Ω`. For a null-measurable `s` it is the extended supremum
of `∫_s div φ ∂μ` over test vector fields `φ ∈ 𝓓(Ω, E)` with `‖φ x‖ ≤ 1` everywhere
(`TauCeti.perimeter_eq_iSup`). -/
def perimeter (μ : Measure E) (Ω : Opens E) (s : Set E) : ℝ≥0∞ :=
  totalVariationOn μ Ω (s.indicator 1)

/-- The perimeter is the total variation of the indicator. -/
theorem perimeter_def : perimeter μ Ω s = totalVariationOn μ Ω (s.indicator 1) :=
  (rfl)

/-- **The perimeter by duality.** For a null-measurable set `s`,
`P(s; Ω) = ⨆ { ∫_s div φ ∂μ | φ ∈ 𝓓(Ω, E), ‖φ‖ ≤ 1 }`. -/
theorem perimeter_eq_iSup (hs : NullMeasurableSet s μ) : perimeter μ Ω s =
    ⨆ (φ : 𝓓(Ω, E)) (_ : ∀ x, ‖φ x‖ ≤ 1), ENNReal.ofReal (∫ x in s, divergenceCLM φ x ∂μ) := by
  rw [perimeter_def, totalVariationOn_def]
  refine iSup_congr fun φ => iSup_congr fun _ => congrArg ENNReal.ofReal ?_
  rw [← integral_indicator₀ hs]
  congr 1 with x
  by_cases hx : x ∈ s <;> simp [hx]

/-- **Locality.** Modifying a set by a null set inside `Ω` does not change its perimeter in
`Ω`. -/
theorem perimeter_congr_ae (h : s =ᵐ[μ.restrict Ω] t) : perimeter μ Ω s = perimeter μ Ω t :=
  totalVariationOn_congr_ae (indicator_ae_eq_of_ae_eq_set h)

/-- The perimeter grows with the open set. -/
theorem perimeter_mono (h : Ω' ≤ Ω) : perimeter μ Ω' s ≤ perimeter μ Ω s :=
  totalVariationOn_mono h

/-- **Inner continuity in the open set.** The perimeter in the union of a directed family of open
sets is the supremum of the perimeters in its members. -/
theorem perimeter_iSup {ι : Type*} [Nonempty ι] {Ω : ι → Opens E} (hΩ : Directed (· ≤ ·) Ω) :
    perimeter μ (⨆ i, Ω i) s = ⨆ i, perimeter μ (Ω i) s :=
  totalVariationOn_iSup hΩ

/-- The empty set has perimeter zero. -/
@[simp]
theorem perimeter_empty : perimeter μ Ω ∅ = 0 := by
  rw [perimeter_def, indicator_empty]
  exact totalVariationOn_zero

section Haar

variable [BorelSpace E] [μ.IsAddHaarMeasure]

/-- **Complements have the same perimeter**, against an additive Haar measure. No measurability
of `s` is needed: the indicators of `s` and `sᶜ` differ by a constant up to sign. -/
@[simp]
theorem perimeter_compl : perimeter μ Ω sᶜ = perimeter μ Ω s := by
  have h : sᶜ.indicator (1 : E → ℝ) = fun x => (-s.indicator 1) x + 1 := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [perimeter_def, perimeter_def, h, totalVariationOn_add_const, totalVariationOn_neg]

/-- The whole space has perimeter zero, against an additive Haar measure. -/
@[simp]
theorem perimeter_univ : perimeter μ Ω univ = 0 := by
  rw [← compl_empty, perimeter_compl, perimeter_empty]

end Haar

/-! ### Lower semicontinuity -/

/-- **Lower semicontinuity of the perimeter.** If the sets `s i` converge to `s₀` locally in
measure in `Ω`, that is `μ ((s i ∆ s₀) ∩ K) → 0` for every compact `K ⊆ Ω`, then
`P(s₀; Ω) ≤ liminf P(s i; Ω)`. -/
theorem perimeter_le_liminf [OpensMeasurableSpace E] [IsLocallyFiniteMeasure μ] {ι : Type*}
    {l : Filter ι} [l.NeBot] {s : ι → Set E} {s₀ : Set E}
    (hs : ∀ᶠ i in l, NullMeasurableSet (s i) μ) (hs₀ : NullMeasurableSet s₀ μ)
    (h : ∀ K, IsCompact K → K ⊆ Ω → Tendsto (fun i => μ ((s i ∆ s₀) ∩ K)) l (𝓝 0)) :
    perimeter μ Ω s₀ ≤ liminf (fun i => perimeter μ Ω (s i)) l := by
  -- The indicator of a null-measurable set is locally integrable.
  have hli {t : Set E} (ht : NullMeasurableSet t μ) :
      LocallyIntegrableOn (t.indicator (1 : E → ℝ)) Ω μ :=
    (((locallyIntegrable_const 1).indicator (measurableSet_toMeasurable μ t)).congr
      (indicator_ae_eq_of_ae_eq_set ht.toMeasurable_ae_eq)).locallyIntegrableOn _
  refine totalVariationOn_le_liminf (hs.mono fun i hi => hli hi) (hli hs₀) fun K hK hKΩ => ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h K hK hKΩ)
    (fun _ => zero_le) fun i => ?_
  have hpt : ∀ x, ‖(s i).indicator (1 : E → ℝ) x - s₀.indicator 1 x‖ₑ =
      (s i ∆ s₀).indicator 1 x := fun x => by
    by_cases h₁ : x ∈ s i <;> by_cases h₂ : x ∈ s₀ <;> simp [mem_symmDiff, h₁, h₂]
  simp_rw [hpt]
  exact (lintegral_indicator_one_le _).trans
    (Measure.restrict_apply' hK.isClosed.measurableSet).le

end TauCeti
