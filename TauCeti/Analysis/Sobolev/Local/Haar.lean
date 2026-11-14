/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving

/-!
# Haar-measure invariance and linear changes of variables for `MemLpLoc` and `MemW1pLoc`

On a second-countable locally compact topological additive group `G` with its Borel σ-algebra, any
two additive Haar measures differ by a positive finite scalar factor
(`MeasureTheory.Measure.isAddLeftInvariant_eq_smul`). Consequently:

* They have the same null sets (`MeasureTheory.Measure.ae_eq_of_isAddHaarMeasure`,
  `MeasureTheory.Measure.ae_restrict_eq_of_isAddHaarMeasure`) and the same `Lᵖ` spaces on every
  subset (`MeasureTheory.memLp_addHaar_iff`, `MeasureTheory.memLp_restrict_addHaar_iff`); in
  particular `2 • volume` has the same null sets
  (`MeasureTheory.Measure.ae_ennreal_smul_measure_eq`) and `Lᵖ(K)` functions
  (`MeasureTheory.memLp_smul_measure_iff`) as `volume`.
* Replacing `volume` by a positive finite multiple or by any other additive Haar measure leaves both
  `TauCeti.MemLpLoc` and `TauCeti.MemW1pLoc` unchanged (`TauCeti.memLpLoc_smul_volume_iff`,
  `TauCeti.memW1pLoc_smul_volume_iff`, `TauCeti.memLpLoc_addHaar_iff`,
  `TauCeti.memW1pLoc_addHaar_iff`).
* Every continuous linear equivalence `e : E ≃L[ℝ] E₁` between finite-dimensional real normed spaces
  carrying additive Haar measures transports `MemLpLoc` and `MemW1pLoc`
  (`TauCeti.MemLpLoc.comp_continuousLinearEquiv`, `ContinuousLinearEquiv.memLpLoc_comp_iff`,
  `TauCeti.MemW1pLoc.comp_continuousLinearEquiv`, `ContinuousLinearEquiv.memW1pLoc_comp_iff`), with
  no measure-preservation hypothesis on `e`.
* In particular, `ℝ × ℝ` with its `max` norm `‖(y₁, y₂)‖ = max |y₁| |y₂|` (which fails the
  parallelogram law and so comes from no inner product) and product Lebesgue measure has the exact
  same `MemLpLoc` and `MemW1pLoc` classes as `EuclideanSpace ℝ (Fin 2)` through the coordinate
  equivalence `TauCeti.euclideanFinTwoEquivProd`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), 275–299, §2.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace MeasureTheory

/-- Rescaling a measure by a positive finite constant leaves `MemLp` unchanged (for instance for
`2 • volume` alongside `MeasureTheory.Measure.ae_ennreal_smul_measure_eq`). -/
theorem memLp_smul_measure_iff {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞) {p : ℝ≥0∞} {f : α → F} :
    MemLp f p (c • μ) ↔ MemLp f p μ :=
  ⟨fun h => by
    simpa only [smul_smul, ENNReal.inv_mul_cancel hc₀ hc, one_smul] using
      h.smul_measure (ENNReal.inv_ne_top.2 hc₀),
   fun h => h.smul_measure hc⟩

section AddHaar

variable {G F : Type*} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup F]

/-- Any two additive Haar measures on a second-countable locally compact topological additive group
have the same restricted almost-everywhere filter on every set `s`. -/
theorem Measure.ae_restrict_eq_of_isAddHaarMeasure (μ₁ μ₂ : Measure G)
    [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure] (s : Set G) :
    ae (μ₁.restrict s) = ae (μ₂.restrict s) := by
  refine le_antisymm ?_ ?_
  · rw [Measure.isAddLeftInvariant_eq_smul μ₁ μ₂, Measure.restrict_smul]
    exact Measure.ae_smul_measure_le _
  · rw [Measure.isAddLeftInvariant_eq_smul μ₂ μ₁, Measure.restrict_smul]
    exact Measure.ae_smul_measure_le _

/-- Any two additive Haar measures on a second-countable locally compact topological additive group
have the same almost-everywhere filter, hence the same null sets. -/
theorem Measure.ae_eq_of_isAddHaarMeasure (μ₁ μ₂ : Measure G)
    [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure] :
    ae μ₁ = ae μ₂ := by
  simpa using Measure.ae_restrict_eq_of_isAddHaarMeasure μ₁ μ₂ univ

/-- `MemLp` on any subset `s` of a second-countable locally compact topological additive group does
not depend on the choice of additive Haar measure. -/
theorem memLp_restrict_addHaar_iff (μ₁ μ₂ : Measure G)
    [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure] {p : ℝ≥0∞} {s : Set G} {u : G → F} :
    MemLp u p (μ₁.restrict s) ↔ MemLp u p (μ₂.restrict s) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Measure.isAddLeftInvariant_eq_smul μ₂ μ₁, Measure.restrict_smul]
    exact h.smul_measure_nnreal
  · rw [Measure.isAddLeftInvariant_eq_smul μ₁ μ₂, Measure.restrict_smul]
    exact h.smul_measure_nnreal

/-- `MemLp` on a second-countable locally compact topological additive group does not depend on the
choice of additive Haar measure. -/
theorem memLp_addHaar_iff (μ₁ μ₂ : Measure G) [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure]
    {p : ℝ≥0∞} {u : G → F} :
    MemLp u p μ₁ ↔ MemLp u p μ₂ := by
  simpa using memLp_restrict_addHaar_iff μ₁ μ₂ (s := univ)

end AddHaar

end MeasureTheory

namespace TauCeti

/-! ### Measure rescaling and Haar independence of `MemLpLoc` and `MemW1pLoc` -/

/-- Rescaling `volume` by a positive finite constant leaves `MemLpLoc` unchanged. -/
theorem memLpLoc_smul_volume_iff {E F : Type*} [TopologicalSpace E] [MeasureSpace E]
    [NormedAddCommGroup F] {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞)
    {p : ℝ≥0∞} {U : Set E} {u : E → F} :
    @MemLpLoc E F _ { volume := c • volume } _ p U u ↔ MemLpLoc p U u := by
  simp only [@memLpLoc_iff E F _ { volume := c • volume } _, memLpLoc_iff, Measure.restrict_smul,
    memLp_smul_measure_iff hc₀ hc]

/-- Rescaling `volume` by a positive finite constant leaves `MemW1pLoc` unchanged. -/
theorem memW1pLoc_smul_volume_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞) {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} :
    @MemW1pLoc E F _ _ { volume := c • volume } _ _ p Ω u ↔ MemW1pLoc p Ω u := by
  simp only [@memW1pLoc_iff E F _ _ { volume := c • volume } _ _, memW1pLoc_iff,
    memLpLoc_smul_volume_iff hc₀ hc, hasWeakFDerivOn_smul_measure_iff hc₀ hc]

/-- `MemLpLoc` on a second-countable locally compact topological additive group does not depend on
the choice of additive Haar measure. -/
theorem memLpLoc_addHaar_iff {G F : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup F]
    (μ₁ μ₂ : Measure G) [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure]
    {p : ℝ≥0∞} {U : Set G} {u : G → F} :
    @MemLpLoc G F _ { volume := μ₁ } _ p U u ↔ @MemLpLoc G F _ { volume := μ₂ } _ p U u := by
  simp only [@memLpLoc_iff G F _ { volume := μ₁ } _, @memLpLoc_iff G F _ { volume := μ₂ } _,
    memLp_restrict_addHaar_iff μ₁ μ₂]

/-- `MemW1pLoc` on a finite-dimensional real normed space does not depend on the choice of additive
Haar measure. -/
theorem memW1pLoc_addHaar_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ₁ μ₂ : Measure E) [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure]
    {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} :
    @MemW1pLoc E F _ _ { volume := μ₁ } _ _ p Ω u ↔
      @MemW1pLoc E F _ _ { volume := μ₂ } _ _ p Ω u := by
  simp only [@memW1pLoc_iff E F _ _ { volume := μ₁ } _ _,
    @memW1pLoc_iff E F _ _ { volume := μ₂ } _ _,
    memLpLoc_addHaar_iff μ₁ μ₂, hasWeakFDerivOn_addHaar_iff μ₁ μ₂]

/-! ### Transport under continuous linear equivalences -/

section ContinuousLinearEquiv

variable {E E₁ F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [MeasureSpace E₁] [BorelSpace E₁] [(volume : Measure E₁).IsAddHaarMeasure]
  [NormedAddCommGroup F]

/-- Precomposition with a continuous linear equivalence between finite-dimensional real normed
spaces carrying additive Haar measures preserves `MemLpLoc`. -/
theorem MemLpLoc.comp_continuousLinearEquiv {p : ℝ≥0∞} {U : Set E} {V : Set E₁} {u : E₁ → F}
    (hu : MemLpLoc p V u) (e : E ≃L[ℝ] E₁) (hUV : MapsTo e U V) :
    MemLpLoc p U (u ∘ e) := by
  have : FiniteDimensional ℝ E₁ := Module.Finite.equiv e.toLinearEquiv
  have : ((volume : Measure E).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  refine memLpLoc_iff.2 fun K hKU hK => ?_
  have hKe : MemLp u p ((volume : Measure E₁).restrict (e '' K)) :=
    memLpLoc_iff.1 hu (e '' K) ((image_mono hKU).trans hUV.image_subset) (hK.image e.continuous)
  have hmap : MemLp u p (((volume : Measure E).map e).restrict (e '' K)) :=
    (memLp_restrict_addHaar_iff _ _).2 hKe
  rw [he.restrict_map, e.injective.preimage_image] at hmap
  exact he.memLp_map_measure_iff.1 hmap

/-- `MemLpLoc` is invariant under precomposition with any continuous linear equivalence between
finite-dimensional real normed spaces carrying additive Haar measures. -/
theorem _root_.ContinuousLinearEquiv.memLpLoc_comp_iff (e : E ≃L[ℝ] E₁)
    {p : ℝ≥0∞} {V : Set E₁} {u : E₁ → F} :
    MemLpLoc p (e ⁻¹' V) (u ∘ e) ↔ MemLpLoc p V u := by
  have : FiniteDimensional ℝ E₁ := Module.Finite.equiv e.toLinearEquiv
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv e (mapsTo_preimage e V)⟩
  simpa only [Function.comp_def, e.apply_symm_apply] using
    h.comp_continuousLinearEquiv e.symm fun y hy => by simpa using hy

variable [NormedSpace ℝ F]

/-- Precomposition with a continuous linear equivalence between finite-dimensional real normed
spaces carrying additive Haar measures preserves `MemW1pLoc`, with weak derivative
`x ↦ Du (e x) ∘L e`. -/
theorem MemW1pLoc.comp_continuousLinearEquiv {p : ℝ≥0∞} {Ω : Opens E} {Ω' : Opens E₁}
    {u : E₁ → F} (hu : MemW1pLoc p Ω' u) (e : E ≃L[ℝ] E₁) (hΩ : MapsTo e Ω Ω') :
    MemW1pLoc p Ω (u ∘ e) := by
  obtain ⟨huLp, Du, hDu, hDuLp⟩ := memW1pLoc_iff.1 hu
  exact memW1pLoc_iff.2 ⟨huLp.comp_continuousLinearEquiv e hΩ,
    fun x => (Du (e x)).comp (e : E →L[ℝ] E₁),
    hDu.comp_continuousLinearEquiv e hΩ,
    (hDuLp.comp_continuousLinearEquiv e hΩ).clm_comp
      ((ContinuousLinearMap.compL ℝ E E₁ F).flip (e : E →L[ℝ] E₁))⟩

/-- `MemW1pLoc` is invariant under precomposition with any continuous linear equivalence between
finite-dimensional real normed spaces carrying additive Haar measures. -/
theorem _root_.ContinuousLinearEquiv.memW1pLoc_comp_iff (e : E ≃L[ℝ] E₁)
    {p : ℝ≥0∞} {Ω' : Opens E₁} {u : E₁ → F} :
    MemW1pLoc p (Ω'.comap ⟨e, e.continuous⟩) (u ∘ e) ↔ MemW1pLoc p Ω' u := by
  have : FiniteDimensional ℝ E₁ := Module.Finite.equiv e.toLinearEquiv
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv e (mapsTo_preimage e Ω')⟩
  simpa only [Function.comp_def, e.apply_symm_apply] using
    h.comp_continuousLinearEquiv e.symm fun y hy => by simpa using hy

end ContinuousLinearEquiv

/-! ### Non-inner-product model check: `ℝ × ℝ` with the `max` norm -/

/-- The `max` norm `‖(y₁, y₂)‖ = max |y₁| |y₂|` on `ℝ × ℝ` fails the parallelogram law, hence is
not induced by any real inner product. -/
theorem prod_real_parallelogram_law_false :
    ‖((1 : ℝ), (0 : ℝ)) + (0, 1)‖ ^ 2 + ‖((1 : ℝ), (0 : ℝ)) - (0, 1)‖ ^ 2 ≠
      2 * (‖((1 : ℝ), (0 : ℝ))‖ ^ 2 + ‖((0 : ℝ), (1 : ℝ))‖ ^ 2) := by
  simp [Prod.norm_def]

/-- The coordinate continuous linear equivalence `x ↦ (x 0, x 1)` between
`EuclideanSpace ℝ (Fin 2)` (with the `ℓ²` inner-product norm) and `ℝ × ℝ` (with the `max` norm
`max |y₁| |y₂|` and product Lebesgue measure). -/
def euclideanFinTwoEquivProd : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin 2 => ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

@[simp]
theorem euclideanFinTwoEquivProd_apply (x : EuclideanSpace ℝ (Fin 2)) :
    euclideanFinTwoEquivProd x = (x 0, x 1) := by
  simp [euclideanFinTwoEquivProd]

/-- `ℝ × ℝ` with its `max` norm and product Lebesgue measure has the exact same `MemLpLoc` classes
as `EuclideanSpace ℝ (Fin 2)` through `TauCeti.euclideanFinTwoEquivProd`. -/
theorem memLpLoc_prod_iff_euclideanFinTwo {F : Type*} [NormedAddCommGroup F]
    {p : ℝ≥0∞} {V : Set (ℝ × ℝ)} {u : ℝ × ℝ → F} :
    MemLpLoc p V u ↔
      MemLpLoc p (euclideanFinTwoEquivProd ⁻¹' V) (u ∘ euclideanFinTwoEquivProd) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  exact euclideanFinTwoEquivProd.memLpLoc_comp_iff.symm

/-- `ℝ × ℝ` with its `max` norm and product Lebesgue measure has the exact same `MemW1pLoc` classes
as `EuclideanSpace ℝ (Fin 2)` through `TauCeti.euclideanFinTwoEquivProd`. -/
theorem memW1pLoc_prod_iff_euclideanFinTwo {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} {Ω : Opens (ℝ × ℝ)} {u : ℝ × ℝ → F} :
    MemW1pLoc p Ω u ↔
      MemW1pLoc p (Ω.comap ⟨euclideanFinTwoEquivProd, euclideanFinTwoEquivProd.continuous⟩)
        (u ∘ euclideanFinTwoEquivProd) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  exact euclideanFinTwoEquivProd.memW1pLoc_comp_iff.symm

end TauCeti
