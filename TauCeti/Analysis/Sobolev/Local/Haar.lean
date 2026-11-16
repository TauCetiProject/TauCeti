/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Sobolev.WeakDeriv.Haar
import TauCeti.Analysis.Sobolev.WeakDeriv.Translation

/-!
# Haar-measure independence and linear/affine invariance of local Sobolev classes

On a locally compact second-countable real normed space `E`, any two additive Haar measures differ
by a positive finite constant (`MeasureTheory.Measure.isAddLeftInvariant_eq_smul`). Because scaling
the ambient measure by a positive finite scalar preserves and reflects `Lᵖ` membership on compact
sets as well as weak differentiability (`TauCeti.hasWeakFDerivOn_smul_measure_iff`), both
`TauCeti.MemLpLoc` and `TauCeti.MemWkpLoc` are independent of the choice of additive Haar measure
(`TauCeti.memLpLoc_iff_of_isAddHaarMeasure`, `TauCeti.memWkpLoc_iff_of_isAddHaarMeasure`, and their
`MeasureSpace`-comparison forms `TauCeti.memLpLoc_congr_measureSpace` and
`TauCeti.memWkpLoc_congr_measureSpace`).

Consequently, any continuous linear equivalence `e : E ≃L[ℝ] E₁` between spaces carrying
arbitrary Borel additive Haar measures preserves and reflects `MemLpLoc` (for locally compact
second-countable spaces) and `MemWkpLoc` at every order (for finite-dimensional real normed spaces;
see `TauCeti.MemLpLoc.comp_continuousLinearEquiv`, `ContinuousLinearEquiv.memLpLoc_comp_iff`,
`TauCeti.MemWkpLoc.comp_continuousLinearEquiv`, `ContinuousLinearEquiv.memWkpLoc_comp_iff`).
Combined with translation invariance (`TauCeti.MemLpLoc.comp_add_right`,
`TauCeti.MemWkpLoc.comp_add_right`), this yields affine invariance
(`TauCeti.MemLpLoc.comp_continuousLinearEquiv_add`,
`TauCeti.MemWkpLoc.comp_continuousLinearEquiv_add`) across arbitrary finite-dimensional real normed
spaces, independent of inner products or canonical volume normalizations.

## Main declarations

* `TauCeti.memLpLoc_smul_measure_iff`, `TauCeti.memWkpLoc_smul_measure_iff`: invariance under
  positive finite scaling of the ambient measure.
* `TauCeti.memLpLoc_iff_of_isAddHaarMeasure`, `TauCeti.memWkpLoc_iff_of_isAddHaarMeasure`:
  independence of the choice of additive Haar measure.
* `TauCeti.memLpLoc_congr_measureSpace`, `TauCeti.memWkpLoc_congr_measureSpace`: independence of
  the `MeasureSpace` instance among Borel additive Haar measures.
* `TauCeti.MemLpLoc.comp_add_right`, `TauCeti.MemWkpLoc.comp_add_right`: translation invariance.
* `TauCeti.MemLpLoc.comp_continuousLinearEquiv`, `ContinuousLinearEquiv.memLpLoc_comp_iff`:
  linear invariance of local `Lᵖ` classes.
* `TauCeti.MemWkpLoc.comp_continuousLinearEquiv`, `ContinuousLinearEquiv.memWkpLoc_comp_iff`:
  linear invariance of local Sobolev classes of every order.
* `TauCeti.MemLpLoc.comp_continuousLinearEquiv_add`,
  `TauCeti.MemWkpLoc.comp_continuousLinearEquiv_add`: affine invariance of local `Lᵖ` and local
  Sobolev classes of every order.

## References

* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §4.2.
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), §2.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

universe u u₁ v

section SmulMeasure

/-- Scaling the ambient measure by a positive finite constant preserves and reflects local `Lᵖ`
membership. -/
theorem memLpLoc_smul_measure_iff {E : Type u} {F : Type v}
    [TopologicalSpace E] [MeasurableSpace E] [NormedAddCommGroup F]
    {μ : Measure E} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞)
    {p : ENNReal} {U : Set E} {f : E → F} :
    @MemLpLoc E F _ ⟨c • μ⟩ _ p U f ↔ @MemLpLoc E F _ ⟨μ⟩ _ p U f := by
  refine ⟨fun h => (@memLpLoc_iff E F _ ⟨μ⟩ _ _ _ _).2 fun K hKU hK => ?_,
    fun h => (@memLpLoc_iff E F _ ⟨c • μ⟩ _ _ _ _).2 fun K hKU hK => ?_⟩
  · have h' := ((@memLpLoc_iff E F _ ⟨c • μ⟩ _ _ _ _).1 h K hKU hK).smul_measure
      (ENNReal.inv_ne_top.2 hc0)
    change MemLp f p (c⁻¹ • (c • μ).restrict K) at h'
    rwa [Measure.restrict_smul, smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul] at h'
  · change MemLp f p ((c • μ).restrict K)
    rw [Measure.restrict_smul]
    exact ((@memLpLoc_iff E F _ ⟨μ⟩ _ _ _ _).1 h K hKU hK).smul_measure hc

/-- Scaling the ambient measure by a positive finite constant preserves and reflects local Sobolev
membership at every order. -/
theorem memWkpLoc_smul_measure_iff {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞)
    {p : ENNReal} {U : Set E} {k : ℕ} {f : E → F} :
    @MemWkpLoc E _ _ ⟨c • μ⟩ p U k F _ _ f ↔ @MemWkpLoc E _ _ ⟨μ⟩ p U k F _ _ f := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : E → F},
      @MemWkpLoc E _ _ ⟨c • μ⟩ p U k F _ _ f ↔
        @MemWkpLoc E _ _ ⟨μ⟩ p U k F _ _ f := by
    intro k
    induction k with
    | zero =>
      intro F _ _ f
      simp only [@memWkpLoc_zero_iff E F _ _ ⟨c • μ⟩, @memWkpLoc_zero_iff E F _ _ ⟨μ⟩]
      exact memLpLoc_smul_measure_iff hc0 hc
    | succ k ih =>
      intro F _ _ f
      simp only [@memWkpLoc_succ_iff E F _ _ ⟨c • μ⟩, @memWkpLoc_succ_iff E F _ _ ⟨μ⟩]
      exact and_congr (memLpLoc_smul_measure_iff hc0 hc) <| exists_congr fun D =>
        and_congr (hasWeakFDerivOn_smul_measure_iff (μ := μ) (D := D) hc0 hc) ih
  cases k with
  | zero =>
    simp only [@memWkpLoc_zero_iff E F _ _ ⟨c • μ⟩, @memWkpLoc_zero_iff E F _ _ ⟨μ⟩]
    exact memLpLoc_smul_measure_iff hc0 hc
  | succ k =>
    simp only [@memWkpLoc_succ_iff E F _ _ ⟨c • μ⟩, @memWkpLoc_succ_iff E F _ _ ⟨μ⟩]
    exact and_congr (memLpLoc_smul_measure_iff hc0 hc) <| exists_congr fun D =>
      and_congr (hasWeakFDerivOn_smul_measure_iff (μ := μ) (D := D) hc0 hc) (aux k)

end SmulMeasure

section HaarIndependence

/-- Local `Lᵖ` membership on a locally compact second-countable topological additive group is
independent of the choice of additive Haar measure. -/
theorem memLpLoc_iff_of_isAddHaarMeasure {E : Type u} {F : Type v}
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [LocallyCompactSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] {μ ν : Measure E} [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {p : ENNReal} {U : Set E} {f : E → F} :
    @MemLpLoc E F _ ⟨μ⟩ _ p U f ↔ @MemLpLoc E F _ ⟨ν⟩ _ p U f := by
  rw [Measure.isAddLeftInvariant_eq_smul μ ν, ← Measure.coe_nnreal_smul]
  exact memLpLoc_smul_measure_iff
    (ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne')
    ENNReal.coe_ne_top

/-- Local `Lᵖ` membership is independent of the `MeasureSpace` instance among Borel additive Haar
measures. -/
theorem memLpLoc_congr_measureSpace {E : Type u} {F : Type v}
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [LocallyCompactSpace E] [SecondCountableTopology E] [NormedAddCommGroup F]
    (m₁ m₂ : MeasureSpace E)
    [hB₁ : @BorelSpace E _ m₁.toMeasurableSpace]
    [hB₂ : @BorelSpace E _ m₂.toMeasurableSpace]
    [@Measure.IsAddHaarMeasure E _ _ m₁.toMeasurableSpace m₁.volume]
    [@Measure.IsAddHaarMeasure E _ _ m₂.toMeasurableSpace m₂.volume]
    {p : ENNReal} {U : Set E} {f : E → F} :
    @MemLpLoc E F _ m₁ _ p U f ↔ @MemLpLoc E F _ m₂ _ p U f := by
  rcases m₁ with @⟨m₁, μ⟩
  rcases m₂ with @⟨m₂, ν⟩
  have hm : m₁ = m₂ := hB₁.measurable_eq.trans hB₂.measurable_eq.symm
  subst hm
  exact memLpLoc_iff_of_isAddHaarMeasure

/-- Local Sobolev membership at every order is independent of the choice of additive Haar
measure. -/
theorem memWkpLoc_iff_of_isAddHaarMeasure {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ ν : Measure E} [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {p : ENNReal} {U : Set E} {k : ℕ} {f : E → F} :
    @MemWkpLoc E _ _ ⟨μ⟩ p U k F _ _ f ↔ @MemWkpLoc E _ _ ⟨ν⟩ p U k F _ _ f := by
  rw [Measure.isAddLeftInvariant_eq_smul μ ν, ← Measure.coe_nnreal_smul]
  exact memWkpLoc_smul_measure_iff
    (ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne')
    ENNReal.coe_ne_top

/-- Local Sobolev membership at every order is independent of the `MeasureSpace` instance among
Borel additive Haar measures. -/
theorem memWkpLoc_congr_measureSpace {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m₁ m₂ : MeasureSpace E)
    [hB₁ : @BorelSpace E _ m₁.toMeasurableSpace]
    [hB₂ : @BorelSpace E _ m₂.toMeasurableSpace]
    [@Measure.IsAddHaarMeasure E _ _ m₁.toMeasurableSpace m₁.volume]
    [@Measure.IsAddHaarMeasure E _ _ m₂.toMeasurableSpace m₂.volume]
    {p : ENNReal} {U : Set E} {k : ℕ} {f : E → F} :
    @MemWkpLoc E _ _ m₁ p U k F _ _ f ↔ @MemWkpLoc E _ _ m₂ p U k F _ _ f := by
  rcases m₁ with @⟨m₁, μ⟩
  rcases m₂ with @⟨m₂, ν⟩
  have hm : m₁ = m₂ := hB₁.measurable_eq.trans hB₂.measurable_eq.symm
  subst hm
  exact memWkpLoc_iff_of_isAddHaarMeasure

end HaarIndependence

section Translation

/-- Right translation preserves local `Lᵖ` membership under any right-invariant Borel measure. -/
theorem MemLpLoc.comp_add_right {E : Type u} {F : Type v}
    [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddRightInvariant]
    [NormedAddCommGroup F] {p : ENNReal} {U V : Set E} {u : E → F}
    (hu : MemLpLoc p V u) (b : E) (hmaps : MapsTo (· + b) U V) :
    MemLpLoc p U (fun x => u (x + b)) := by
  have hcont : Continuous (· + b) := continuous_id.add continuous_const
  refine memLpLoc_iff.2 fun K hKU hK => ?_
  have hK' : IsCompact ((· + b) '' K) := hK.image hcont
  have hu' : MemLp u p (volume.restrict ((· + b) '' K)) :=
    memLpLoc_iff.1 hu _ ((image_mono hKU).trans hmaps.image_subset) hK'
  have hmap : ((volume : Measure E).restrict K).map (· + b) = volume.restrict ((· + b) '' K) := by
    conv_rhs => rw [← (measurePreserving_add_right (volume : Measure E) b).map_eq]
    rw [Measure.restrict_map hcont.measurable hK'.isClosed.measurableSet,
      preimage_image_eq K (add_left_injective b)]
  exact hu'.comp_measurePreserving ⟨hcont.measurable, hmap⟩

/-- Right translation preserves and reflects local `Lᵖ` membership. -/
theorem memLpLoc_comp_add_right_iff {E : Type u} {F : Type v}
    [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddRightInvariant]
    [NormedAddCommGroup F] {p : ENNReal} {V : Set E} {u : E → F} (b : E) :
    MemLpLoc p ((· + b) ⁻¹' V) (fun x => u (x + b)) ↔ MemLpLoc p V u := by
  refine ⟨fun h => ?_, fun h => h.comp_add_right b (mapsTo_preimage (· + b) V)⟩
  simpa only [add_assoc, neg_add_cancel, add_zero] using
    h.comp_add_right (-b) fun x hx => by
      simpa [mem_preimage, add_assoc, neg_add_cancel, add_zero] using hx

/-- Right translation preserves local Sobolev membership at every order. -/
theorem MemWkpLoc.comp_add_right {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ENNReal} {U V : Set E} {k : ℕ} {u : E → F}
    (hu : MemWkpLoc p V k u) (b : E) (hmaps : MapsTo (· + b) U V) :
    MemWkpLoc p U k (fun x => u (x + b)) := by
  have hint : MapsTo (· + b) (interior U) (interior V) := by
    intro x hx
    have hmem : x + b ∈ (Homeomorph.addRight b) '' interior U := ⟨x, hx, rfl⟩
    rw [(Homeomorph.addRight b).image_interior] at hmem
    exact interior_mono hmaps.image_subset hmem
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {u : E → F}, MemWkpLoc p V k u → MemWkpLoc p U k (fun x => u (x + b)) := by
    intro k
    induction k with
    | zero =>
      intro F _ _ u hu
      exact memWkpLoc_zero_iff.2 ((memWkpLoc_zero_iff.1 hu).comp_add_right b hmaps)
    | succ k ih =>
      intro F _ _ u hu
      obtain ⟨hLp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hu
      exact memWkpLoc_succ_iff.2
        ⟨hLp.comp_add_right b hmaps, fun x => D (x + b),
          hD.comp_add_right (V := Opens.interior U) (by simpa using hint), ih hk⟩
  cases k with
  | zero => exact memWkpLoc_zero_iff.2 ((memWkpLoc_zero_iff.1 hu).comp_add_right b hmaps)
  | succ k =>
    obtain ⟨hLp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hu
    exact memWkpLoc_succ_iff.2
      ⟨hLp.comp_add_right b hmaps, fun x => D (x + b),
        hD.comp_add_right (V := Opens.interior U) (by simpa using hint), aux k hk⟩

/-- Right translation preserves and reflects local Sobolev membership at every order. -/
theorem memWkpLoc_comp_add_right_iff {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ENNReal} {V : Set E} {k : ℕ} {u : E → F} (b : E) :
    MemWkpLoc p ((· + b) ⁻¹' V) k (fun x => u (x + b)) ↔ MemWkpLoc p V k u := by
  refine ⟨fun h => ?_, fun h => h.comp_add_right b (mapsTo_preimage (· + b) V)⟩
  simpa only [add_assoc, neg_add_cancel, add_zero] using
    h.comp_add_right (-b) fun x hx => by
      simpa [mem_preimage, add_assoc, neg_add_cancel, add_zero] using hx

end Translation

section LinearAndAffineLp

variable {E : Type u} {E₁ : Type u₁} {F : Type v}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁]
  [T2Space E₁] [LocallyCompactSpace E₁] [SecondCountableTopology E₁]
  [MeasureSpace E₁] [BorelSpace E₁] [(volume : Measure E₁).IsAddHaarMeasure]
  [NormedAddCommGroup F]

/-- Precomposition with a continuous linear equivalence between spaces carrying arbitrary Borel
additive Haar measures preserves local `Lᵖ` membership. -/
theorem MemLpLoc.comp_continuousLinearEquiv {p : ENNReal} {U : Set E} {V : Set E₁}
    {u : E₁ → F} (hu : MemLpLoc p V u) (e : E ≃L[ℝ] E₁) (hmaps : MapsTo e U V) :
    MemLpLoc p U (u ∘ e) := by
  have : ((volume : Measure E).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  have hu' : @MemLpLoc E₁ F _ ⟨(volume : Measure E).map e⟩ _ p V u :=
    (memLpLoc_iff_of_isAddHaarMeasure (μ := (volume : Measure E).map e) (ν := volume)).2 hu
  refine memLpLoc_iff.2 fun K hKU hK => ?_
  have hK' : IsCompact (e '' K) := hK.image e.continuous
  have hmem : MemLp u p (((volume : Measure E).map e).restrict (e '' K)) :=
    (@memLpLoc_iff E₁ F _ ⟨(volume : Measure E).map e⟩ _ _ _ _).1 hu' _
      ((image_mono hKU).trans hmaps.image_subset) hK'
  have hmap : ((volume : Measure E).restrict K).map e =
      ((volume : Measure E).map e).restrict (e '' K) := by
    rw [Measure.restrict_map e.continuous.measurable hK'.isClosed.measurableSet,
      preimage_image_eq K e.injective]
  exact hmem.comp_measurePreserving ⟨e.continuous.measurable, hmap⟩

/-- Precomposition with a continuous linear equivalence preserves and reflects local `Lᵖ`
membership. -/
theorem _root_.ContinuousLinearEquiv.memLpLoc_comp_iff [T2Space E] [LocallyCompactSpace E]
    [SecondCountableTopology E] {p : ENNReal} {V : Set E₁} {u : E₁ → F}
    (e : E ≃L[ℝ] E₁) :
    MemLpLoc p (e ⁻¹' V) (u ∘ e) ↔ MemLpLoc p V u := by
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv e (mapsTo_preimage e V)⟩
  simpa [Function.comp_def] using
    h.comp_continuousLinearEquiv e.symm fun y hy => by simpa [mem_preimage] using hy

/-- Real-affine changes of variables between spaces carrying arbitrary Borel additive Haar measures
preserve local `Lᵖ` membership. -/
theorem MemLpLoc.comp_continuousLinearEquiv_add {p : ENNReal} {U : Set E} {V : Set E₁}
    {u : E₁ → F} (hu : MemLpLoc p V u) (A : E ≃L[ℝ] E₁) (b : E₁)
    (hmaps : MapsTo (fun x => A x + b) U V) :
    MemLpLoc p U (fun x => u (A x + b)) :=
  (hu.comp_add_right b (mapsTo_preimage (· + b) V)).comp_continuousLinearEquiv A hmaps

end LinearAndAffineLp

section LinearAndAffineWkp

variable {E : Type u} {E₁ : Type u₁} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [MeasureSpace E₁] [BorelSpace E₁] [(volume : Measure E₁).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Linear invariance of local Sobolev classes.** Precomposition with any continuous linear
equivalence `e : E ≃L[ℝ] E₁` between finite-dimensional real normed spaces (carrying arbitrary
Borel additive Haar measures) preserves local Sobolev membership at every order. -/
theorem MemWkpLoc.comp_continuousLinearEquiv {p : ENNReal} {U : Set E}
    {V : Set E₁} {k : ℕ} {u : E₁ → F}
    (hu : MemWkpLoc p V k u) (e : E ≃L[ℝ] E₁) (hmaps : MapsTo e U V) :
    MemWkpLoc p U k (u ∘ e) := by
  have hint : MapsTo e (interior U) (interior V) := by
    intro x hx
    have hmem : e x ∈ e.toHomeomorph '' interior U := ⟨x, hx, rfl⟩
    rw [e.toHomeomorph.image_interior] at hmem
    exact interior_mono hmaps.image_subset hmem
  have aux : ∀ (k : ℕ) {F : Type (max u₁ v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {u : E₁ → F}, MemWkpLoc p V k u → MemWkpLoc p U k (u ∘ e) := by
    intro k
    induction k with
    | zero =>
      intro F _ _ u hu
      exact memWkpLoc_zero_iff.2 ((memWkpLoc_zero_iff.1 hu).comp_continuousLinearEquiv e hmaps)
    | succ k ih =>
      intro F _ _ u hu
      obtain ⟨hLp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hu
      have := hD.completeSpace
      refine memWkpLoc_succ_iff.2
        ⟨hLp.comp_continuousLinearEquiv e hmaps,
          fun x =>
            ((ContinuousLinearMap.compL ℝ E E₁ F).flip (e : E →L[ℝ] E₁)) (D (e x)),
          ?_, (ih hk).clm_comp _⟩
      simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply] using
        hD.comp_continuousLinearEquiv_of_isAddHaarMeasure (U := Opens.interior U) e
          (by simpa using hint)
  cases k with
  | zero =>
    exact memWkpLoc_zero_iff.2 ((memWkpLoc_zero_iff.1 hu).comp_continuousLinearEquiv e hmaps)
  | succ k =>
    obtain ⟨hLp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hu
    have := hD.completeSpace
    refine memWkpLoc_succ_iff.2
      ⟨hLp.comp_continuousLinearEquiv e hmaps,
        fun x =>
          ((ContinuousLinearMap.compL ℝ E E₁ F).flip (e : E →L[ℝ] E₁)) (D (e x)),
        ?_, (aux k hk).clm_comp _⟩
    simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply] using
      hD.comp_continuousLinearEquiv_of_isAddHaarMeasure (U := Opens.interior U) e
        (by simpa using hint)

/-- Precomposition with a continuous linear equivalence preserves and reflects local Sobolev
membership at every order. -/
theorem _root_.ContinuousLinearEquiv.memWkpLoc_comp_iff {p : ENNReal}
    {V : Set E₁} {k : ℕ} {u : E₁ → F} (e : E ≃L[ℝ] E₁) :
    MemWkpLoc p (e ⁻¹' V) k (u ∘ e) ↔ MemWkpLoc p V k u := by
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv e (mapsTo_preimage e V)⟩
  simpa [Function.comp_def] using
    h.comp_continuousLinearEquiv e.symm fun y hy => by simpa [mem_preimage] using hy

/-- **Real-affine changes of variables preserve every order.** For `A : E ≃L[ℝ] E₁`,
`b : E₁`, and `x ↦ A x + b` mapping `U` into `V`, precomposition maps `MemWkpLoc p V k` into
`MemWkpLoc p U k` for arbitrary finite-dimensional real normed spaces carrying Borel additive
Haar measures. -/
theorem MemWkpLoc.comp_continuousLinearEquiv_add {p : ENNReal} {U : Set E}
    {V : Set E₁} {k : ℕ} {u : E₁ → F}
    (hu : MemWkpLoc p V k u) (A : E ≃L[ℝ] E₁) (b : E₁)
    (hmaps : MapsTo (fun x => A x + b) U V) :
    MemWkpLoc p U k (fun x => u (A x + b)) :=
  (hu.comp_add_right b (mapsTo_preimage (· + b) V)).comp_continuousLinearEquiv A hmaps

end LinearAndAffineWkp

end TauCeti
