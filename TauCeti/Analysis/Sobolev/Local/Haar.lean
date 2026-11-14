/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar-measure and linear-coordinate invariance of local Lebesgue and Sobolev classes

On a locally compact topological additive group, any two additive Haar measures agree up to a
positive finite scalar factor on sets of compact closure. Scaling a measure by a nonzero finite
constant preserves both `Lᵖ` membership on compact sets and weak integration by parts, so the
predicates `MemLpLoc` and `MemWkpLoc` are independent of the choice of additive Haar measure.

Consequently, for any continuous linear equivalence `e : E ≃L[ℝ] E'` between finite-dimensional
real normed spaces equipped with additive Haar measures, precomposition with `e` preserves and
reflects both `MemLpLoc` and `MemWkpLoc` of every order, without assuming `e` to be
measure-preserving or either space to carry an inner product. In particular, identifying
`EuclideanSpace ℝ ι` (`ℓ²` norm) with `ι → ℝ` (`ℓ∞` norm) via `EuclideanSpace.equiv` preserves
and reflects `MemWkpLoc`.

## Main declarations

* `TauCeti.MemLpLoc.smul_measure`, `TauCeti.memLpLoc_smul_measure_iff`: rescaling the reference
  measure by a finite (respectively nonzero finite) constant on `MemLpLoc`.
* `TauCeti.MemLpLoc.of_isAddHaarMeasure`, `TauCeti.memLpLoc_isAddHaarMeasure_iff`: invariance of
  `MemLpLoc` under changing the additive Haar measure on any locally compact Hausdorff additive
  group.
* `TauCeti.MemWkpLoc.smul_measure`, `TauCeti.memWkpLoc_smul_measure_iff`: rescaling the reference
  measure on `MemWkpLoc` of any order `k`.
* `TauCeti.MemWkpLoc.of_isAddHaarMeasure`, `TauCeti.memWkpLoc_isAddHaarMeasure_iff`,
  `TauCeti.memWkpLoc_two_smul_volume_iff`: invariance of `MemWkpLoc` across additive Haar measures
  and positive scalar multiples of `volume`.
* `TauCeti.MemLpLoc.comp_continuousLinearEquiv`, `ContinuousLinearEquiv.memLpLoc_comp_iff`:
  pullback and equivalence of `MemLpLoc` along an arbitrary continuous linear equivalence.
* `TauCeti.MemWkpLoc.comp_continuousLinearEquiv`, `ContinuousLinearEquiv.memWkpLoc_comp_iff`:
  pullback and equivalence of `MemWkpLoc` of any order along an arbitrary continuous linear
  equivalence.
* `TauCeti.memWkpLoc_comp_euclideanSpace_equiv_iff`: equivalence of `MemWkpLoc` between `ι → ℝ`
  (supremum norm) and `EuclideanSpace ℝ ι` (`ℓ²` norm).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.
* W. P. Ziemer, *Weakly Differentiable Functions*, §2.1–2.2.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

/-! ### Measure scaling and additive Haar invariance for `MemLpLoc` -/

section MemLpLocMeasure

/-- Scaling the ambient measure by a finite constant preserves local `Lᵖ` membership. -/
theorem MemLpLoc.smul_measure {E F : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [NormedAddCommGroup F] {μ : Measure E} {p : ℝ≥0∞} {U : Set E} {f : E → F}
    (hf : @MemLpLoc E _ { volume := μ } F _ p U f) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    @MemLpLoc E _ { volume := c • μ } F _ p U f :=
  (@memLpLoc_iff E _ { volume := c • μ } F _ p U f).2 fun K hKU hK => by
    change MemLp f p ((c • μ).restrict K)
    rw [Measure.restrict_smul]
    exact ((@memLpLoc_iff E _ { volume := μ } F _ p U f).1 hf K hKU hK).smul_measure hc

/-- Scaling the ambient measure by a nonzero finite constant preserves and reflects local `Lᵖ`
membership. -/
theorem memLpLoc_smul_measure_iff {E F : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [NormedAddCommGroup F] {μ : Measure E} {p : ℝ≥0∞} {U : Set E} {f : E → F}
    {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞) :
    @MemLpLoc E _ { volume := c • μ } F _ p U f ↔
      @MemLpLoc E _ { volume := μ } F _ p U f := by
  refine ⟨fun h => ?_, fun h => h.smul_measure hc⟩
  have h' := h.smul_measure (ENNReal.inv_ne_top.2 hc₀)
  have heq : c⁻¹ • c • μ = μ := by rw [smul_smul, ENNReal.inv_mul_cancel hc₀ hc, one_smul]
  rwa [heq] at h'

/-- On a locally compact Hausdorff topological additive group, `MemLpLoc` does not depend on the
choice of additive Haar measure: any two additive Haar measures differ on every compact subset by
the finite constant `Measure.addHaarScalarFactor`. -/
theorem MemLpLoc.of_isAddHaarMeasure {E F : Type*} [AddGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [LocallyCompactSpace E] [T2Space E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] {μ : Measure E} [μ.IsAddHaarMeasure] (ν : Measure E)
    [ν.IsAddHaarMeasure] {p : ℝ≥0∞} {U : Set E} {f : E → F}
    (hf : @MemLpLoc E _ { volume := μ } F _ p U f) :
    @MemLpLoc E _ { volume := ν } F _ p U f :=
  (@memLpLoc_iff E _ { volume := ν } F _ p U f).2 fun K hKU hK => by
    change MemLp f p (ν.restrict K)
    have hrestrict : ν.restrict K = Measure.addHaarScalarFactor ν μ • μ.restrict K := by
      ext s hs
      rw [Measure.restrict_apply hs, smul_apply, Measure.restrict_apply hs,
        ENNReal.smul_def]
      exact Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure_of_measurableSet ν μ
        (hs.inter hK.isClosed.measurableSet) (hK.closure_of_subset inter_subset_right)
    rw [hrestrict]
    exact ((@memLpLoc_iff E _ { volume := μ } F _ p U f).1 hf K hKU hK).smul_measure_nnreal

/-- Equivalence of `MemLpLoc` for any two additive Haar measures on a locally compact Hausdorff
topological additive group. -/
theorem memLpLoc_isAddHaarMeasure_iff {E F : Type*} [AddGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [LocallyCompactSpace E] [T2Space E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] (μ ν : Measure E) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {p : ℝ≥0∞} {U : Set E} {f : E → F} :
    @MemLpLoc E _ { volume := μ } F _ p U f ↔
      @MemLpLoc E _ { volume := ν } F _ p U f :=
  ⟨fun h => h.of_isAddHaarMeasure ν, fun h => h.of_isAddHaarMeasure μ⟩

end MemLpLocMeasure

/-! ### Measure scaling and additive Haar invariance for `MemWkpLoc` -/

section MemWkpLocMeasure

universe u v

private theorem memWkpLoc_smul_measure_aux {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {μ : Measure E} {p : ℝ≥0∞} {U : Set E} {c : ℝ≥0∞} (hc : c ≠ ∞) :
    ∀ {k : ℕ} {F' : Type (max u v)} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {f : E → F'},
      @MemWkpLoc E _ _ { volume := μ } p U k F' _ _ f →
        @MemWkpLoc E _ _ { volume := c • μ } p U k F' _ _ f
  | 0, F', _, _, f, hf =>
    (@memWkpLoc_zero_iff E _ _ { volume := c • μ } F' _ _ p U f).2
      (((@memWkpLoc_zero_iff E _ _ { volume := μ } F' _ _ p U f).1 hf).smul_measure hc)
  | k + 1, F', _, _, f, hf => by
    obtain ⟨hf₀, D, hD_weak, hD_wkp⟩ :=
      (@memWkpLoc_succ_iff E _ _ { volume := μ } F' _ _ p U f k).1 hf
    exact (@memWkpLoc_succ_iff E _ _ { volume := c • μ } F' _ _ p U f k).2
      ⟨hf₀.smul_measure hc, D, hD_weak.smul_measure hc, memWkpLoc_smul_measure_aux hc hD_wkp⟩

/-- Scaling the ambient measure by a finite constant preserves `MemWkpLoc` of every order. -/
theorem MemWkpLoc.smul_measure {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E}
    {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f : E → F}
    (hf : @MemWkpLoc E _ _ { volume := μ } p U k F _ _ f) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    @MemWkpLoc E _ _ { volume := c • μ } p U k F _ _ f := by
  cases k with
  | zero =>
    exact (@memWkpLoc_zero_iff E _ _ { volume := c • μ } F _ _ p U f).2
      (((@memWkpLoc_zero_iff E _ _ { volume := μ } F _ _ p U f).1 hf).smul_measure hc)
  | succ k =>
    obtain ⟨hf₀, D, hD_weak, hD_wkp⟩ :=
      (@memWkpLoc_succ_iff E _ _ { volume := μ } F _ _ p U f k).1 hf
    exact (@memWkpLoc_succ_iff E _ _ { volume := c • μ } F _ _ p U f k).2
      ⟨hf₀.smul_measure hc, D, hD_weak.smul_measure hc, memWkpLoc_smul_measure_aux hc hD_wkp⟩

/-- Scaling the ambient measure by a nonzero finite constant preserves and reflects `MemWkpLoc`
of every order. -/
theorem memWkpLoc_smul_measure_iff {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f : E → F}
    {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞) :
    @MemWkpLoc E _ _ { volume := c • μ } p U k F _ _ f ↔
      @MemWkpLoc E _ _ { volume := μ } p U k F _ _ f := by
  refine ⟨fun h => ?_, fun h => h.smul_measure hc⟩
  have h' := h.smul_measure (ENNReal.inv_ne_top.2 hc₀)
  have heq : c⁻¹ • c • μ = μ := by rw [smul_smul, ENNReal.inv_mul_cancel hc₀ hc, one_smul]
  rwa [heq] at h'

/-- On a finite-dimensional real normed space, `MemWkpLoc` does not depend on the choice of
additive Haar measure. -/
theorem MemWkpLoc.of_isAddHaarMeasure {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E} [μ.IsAddHaarMeasure]
    (ν : Measure E) [ν.IsAddHaarMeasure] {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f : E → F}
    (hf : @MemWkpLoc E _ _ { volume := μ } p U k F _ _ f) :
    @MemWkpLoc E _ _ { volume := ν } p U k F _ _ f := by
  rw [Measure.isAddLeftInvariant_eq_smul ν μ]
  exact hf.smul_measure ENNReal.coe_ne_top

/-- Equivalence of `MemWkpLoc` for any two additive Haar measures on a finite-dimensional real
normed space. -/
theorem memWkpLoc_isAddHaarMeasure_iff {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (μ ν : Measure E) [μ.IsAddHaarMeasure]
    [ν.IsAddHaarMeasure] {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f : E → F} :
    @MemWkpLoc E _ _ { volume := μ } p U k F _ _ f ↔
      @MemWkpLoc E _ _ { volume := ν } p U k F _ _ f :=
  ⟨fun h => h.of_isAddHaarMeasure ν, fun h => h.of_isAddHaarMeasure μ⟩

/-- Doubling the canonical volume on `E` leaves `MemWkpLoc` unchanged for every exponent `p`,
domain `U`, and order `k`. -/
theorem memWkpLoc_two_smul_volume_iff {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasureSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f : E → F} :
    @MemWkpLoc E _ _ { volume := (2 : ℝ≥0∞) • (volume : Measure E) } p U k F _ _ f ↔
      MemWkpLoc p U k f :=
  memWkpLoc_smul_measure_iff two_ne_zero ENNReal.ofNat_ne_top

end MemWkpLocMeasure

/-! ### Source continuous linear equivalences -/

section ContinuousLinearEquiv

universe u u' v

/-- **Pullback of `MemLpLoc` along an arbitrary continuous linear equivalence.** Between
locally compact real normed Borel spaces carrying additive Haar measures, precomposing with any
continuous linear equivalence `e : E ≃L[ℝ] E'` preserves `MemLpLoc`, without assuming `e` to be
measure-preserving. -/
theorem MemLpLoc.comp_continuousLinearEquiv {E : Type u} {E' : Type u'} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [LocallyCompactSpace E'] [MeasureSpace E']
    [BorelSpace E'] [(volume : Measure E').IsAddHaarMeasure]
    [NormedAddCommGroup F] {p : ℝ≥0∞} {U : Set E} {U' : Set E'} {f : E' → F}
    (hf : MemLpLoc p U' f) (e : E ≃L[ℝ] E') (hU : U ⊆ e ⁻¹' U') :
    MemLpLoc p U (f ∘ e) := by
  let μ : Measure E := volume
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hf_map : @MemLpLoc E' _ { volume := μ.map e } F _ p U' f :=
    hf.of_isAddHaarMeasure (μ.map e)
  refine memLpLoc_iff.2 fun K hKU hK => ?_
  let eₘ : E ≃ᵐ E' := e.toHomeomorph.toMeasurableEquiv
  have hK' : e '' K ⊆ U' := image_subset_iff.2 (hKU.trans hU)
  have hmem : MemLp f p ((μ.map eₘ).restrict (e '' K)) :=
    (@memLpLoc_iff E' _ { volume := μ.map e } F _ p U' f).1 hf_map
      (e '' K) hK' (hK.image e.continuous)
  have hrest : (μ.restrict K).map eₘ = (μ.map eₘ).restrict (e '' K) := by
    simpa only [eₘ, Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph,
      preimage_image_eq K e.injective] using (eₘ.restrict_map μ (e '' K)).symm
  rw [← hrest] at hmem
  exact eₘ.memLp_map_measure_iff.1 hmem

/-- **Equivalence of `MemLpLoc` under an arbitrary continuous linear equivalence.** -/
theorem _root_.ContinuousLinearEquiv.memLpLoc_comp_iff {E : Type u} {E' : Type u'} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [LocallyCompactSpace E'] [MeasureSpace E']
    [BorelSpace E'] [(volume : Measure E').IsAddHaarMeasure]
    [NormedAddCommGroup F] {p : ℝ≥0∞} {U' : Set E'} {f : E' → F} (e : E ≃L[ℝ] E') :
    MemLpLoc p (e ⁻¹' U') (f ∘ e) ↔ MemLpLoc p U' f := by
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv e subset_rfl⟩
  have hVU : U' ⊆ e.symm ⁻¹' (e ⁻¹' U') := fun y hy => by simpa using hy
  simpa only [Function.comp_def, e.apply_symm_apply] using h.comp_continuousLinearEquiv e.symm hVU

private theorem memWkpLoc_comp_continuousLinearEquiv_aux {E : Type u} {E' : Type u'}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [MeasureSpace E']
    [BorelSpace E'] [(volume : Measure E').IsAddHaarMeasure]
    {p : ℝ≥0∞} {U : Set E} {U' : Set E'} (e : E ≃L[ℝ] E') (hU : U ⊆ e ⁻¹' U') :
    ∀ {k : ℕ} {F' : Type (max u (max u' v))} [NormedAddCommGroup F'] [NormedSpace ℝ F']
      {f : E' → F'}, MemWkpLoc p U' k f → MemWkpLoc p U k (f ∘ e)
  | 0, _, _, _, _, hf =>
    memWkpLoc_zero_iff.2 ((memWkpLoc_zero_iff.1 hf).comp_continuousLinearEquiv e hU)
  | k + 1, F', _, _, f, hf => by
    obtain ⟨hf₀, D, hD_weak, hD_wkp⟩ := memWkpLoc_succ_iff.mp hf
    have : CompleteSpace F' := hD_weak.completeSpace
    have hmaps : MapsTo e (Opens.interior U) (Opens.interior U') := fun x hx =>
      interior_maximal (image_subset_iff.2 (interior_subset.trans hU))
        (e.toHomeomorph.isOpenMap _ isOpen_interior) (mem_image_of_mem e hx)
    have hweak : HasWeakFDerivOn volume (Opens.interior U) (f ∘ e)
        (fun x => (D (e x)).comp (e : E →L[ℝ] E')) :=
      hD_weak.comp_continuousLinearEquiv_of_isAddHaarMeasure e hmaps
    have hDe : MemWkpLoc p U k (D ∘ e) :=
      memWkpLoc_comp_continuousLinearEquiv_aux e hU hD_wkp
    have hDcomp : MemWkpLoc p U k (fun x => (D (e x)).comp (e : E →L[ℝ] E')) :=
      hDe.clm_comp ((ContinuousLinearMap.compL ℝ E E' F').flip (e : E →L[ℝ] E'))
    exact memWkpLoc_succ_iff.mpr ⟨hf₀.comp_continuousLinearEquiv e hU, _, hweak, hDcomp⟩

/-- **Pullback of `MemWkpLoc` along an arbitrary continuous linear equivalence.** Between
finite-dimensional real normed spaces equipped with additive Haar measures, precomposition with any
continuous linear equivalence `e : E ≃L[ℝ] E'` preserves `MemWkpLoc` of every order `k`, with no
inner-product or measure-preservation assumption on `e`. -/
theorem MemWkpLoc.comp_continuousLinearEquiv {E : Type u} {E' : Type u'} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [MeasureSpace E']
    [BorelSpace E'] [(volume : Measure E').IsAddHaarMeasure]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U : Set E} {U' : Set E'} {k : ℕ}
    {f : E' → F} (hf : MemWkpLoc p U' k f) (e : E ≃L[ℝ] E') (hU : U ⊆ e ⁻¹' U') :
    MemWkpLoc p U k (f ∘ e) := by
  let L : F ≃L[ℝ] ULift.{max u u'} F :=
    (ContinuousLinearEquiv.ulift : ULift.{max u u'} F ≃L[ℝ] F).symm
  exact L.comp_memWkpLoc_iff.mp
    (memWkpLoc_comp_continuousLinearEquiv_aux.{u, u', v} e hU (L.comp_memWkpLoc_iff.mpr hf))

/-- **Equivalence of `MemWkpLoc` under an arbitrary continuous linear equivalence.** -/
theorem _root_.ContinuousLinearEquiv.memWkpLoc_comp_iff {E : Type u} {E' : Type u'} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [MeasureSpace E']
    [BorelSpace E'] [(volume : Measure E').IsAddHaarMeasure]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U' : Set E'} {k : ℕ} {f : E' → F}
    (e : E ≃L[ℝ] E') :
    MemWkpLoc p (e ⁻¹' U') k (f ∘ e) ↔ MemWkpLoc p U' k f := by
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv e subset_rfl⟩
  have hVU : U' ⊆ e.symm ⁻¹' (e ⁻¹' U') := fun y hy => by simpa using hy
  simpa only [Function.comp_def, e.apply_symm_apply] using h.comp_continuousLinearEquiv e.symm hVU

/-- **Invariance of `MemWkpLoc` between `ℓ²` and `ℓ∞` norms on finite products.** Pulling a map on
`ι → ℝ` (with the supremum norm, which is not induced by an inner product for `#ι ≥ 2`) back to
`EuclideanSpace ℝ ι` (with the `ℓ²` norm) via `EuclideanSpace.equiv ι ℝ` preserves and reflects
`MemWkpLoc` of every order. -/
theorem memWkpLoc_comp_euclideanSpace_equiv_iff {ι : Type*} [Fintype ι] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U : Set (ι → ℝ)} {k : ℕ}
    {f : (ι → ℝ) → F} :
    MemWkpLoc p ((EuclideanSpace.equiv ι ℝ) ⁻¹' U) k (f ∘ EuclideanSpace.equiv ι ℝ) ↔
      MemWkpLoc p U k f :=
  (EuclideanSpace.equiv ι ℝ).memWkpLoc_comp_iff

end ContinuousLinearEquiv

end TauCeti
