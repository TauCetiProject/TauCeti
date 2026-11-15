/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Total
import Mathlib.Order.Disjointed
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# Integrating functions against the Riemannian volume form

On an oriented Riemannian manifold `M`, a function `f : M → ℝ` is integrated as the top form
`f vol`, where `vol = TauCeti.riemannianVolumeForm o` is the Riemannian volume form of the
orientation `o`: `∫_M f vol = integralTopForm o (fun x ↦ f x • vol x)`. This file records the
basic properties of this integral that pointwise estimates need: it is nonnegative on nonnegative
functions, it commutes with constant factors, and on a compact manifold it is additive and
monotone on continuous functions. Thus a pointwise inequality `f ≤ g` between continuous functions
integrates to `∫_M f vol ≤ ∫_M g vol`.

In every dimension `m : ℕ` (including `m = 0`), the integral of `vol` itself is nonnegative, forces
compactness of `M` when integrable, agrees on compact `M` with `TauCeti.riemannianTotalVolume I M`,
is strictly positive on nonempty compact `M`, and is independent of the choice of orientation `o`.

## Main results

* `TauCeti.compactSpace_of_integrableTopForm_riemannianVolumeForm` and
  `TauCeti.integrableTopForm_riemannianVolumeForm_iff_compactSpace`: integrability of `vol`
  characterizes compactness of `M`.
* `TauCeti.integralTopForm_riemannianVolumeForm_eq_riemannianTotalVolume`: on a compact manifold,
  `∫_M vol = riemannianTotalVolume I M`.
* `TauCeti.integralTopForm_riemannianVolumeForm_nonneg`,
  `TauCeti.integralTopForm_riemannianVolumeForm_pos`, and
  `TauCeti.integralTopForm_riemannianVolumeForm_congr`: nonnegativity, strict positivity on
  nonempty compact manifolds, and orientation independence of `∫_M vol` in all dimensions.
* `TauCeti.integralTopForm_smul_riemannianVolumeForm_nonneg`: `0 ≤ f` gives `0 ≤ ∫_M f vol`.
* `TauCeti.integralTopForm_mul_smul_riemannianVolumeForm`: `∫_M c f vol = c ∫_M f vol`.
* `TauCeti.isSmoothForm_smul_riemannianVolumeForm`: `f vol` is a continuous top form when `f`
  is continuous.
* `TauCeti.integralTopForm_add_smul_riemannianVolumeForm`: on a compact manifold,
  `∫_M (f + g) vol = ∫_M f vol + ∫_M g vol` for continuous `f` and `g`.
* `TauCeti.integralTopForm_smul_riemannianVolumeForm_mono`: on a compact manifold, `f ≤ g`
  gives `∫_M f vol ≤ ∫_M g vol` for continuous `f` and `g`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 16.6 and Proposition 15.29.
-/

public section

noncomputable section

open Bundle Function MeasureTheory Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {m : ℕ} (o : Manifold.Orientation I M (Fin m))

open scoped Classical in
/-- Against an orientation lift whose model orientation is that of the reindexed standard basis
`b = (Module.finBasis ℝ E).reindex σ`, the signed coordinate coefficient of the Riemannian volume
form at `y` is the chart volume density on the chart target and `0` outside it, independent of the
lift and in every dimension `m`. -/
private theorem signedInChartAt_riemannianVolumeForm_eq
    (σ : Fin (Module.finrank ℝ E) ≃ Fin m) (l : Manifold.OrientationLift I M (Fin m))
    (hl : l.modelOrientation = ((Module.finBasis ℝ E).reindex σ).orientation)
    (α : M) (y : E) :
    (riemannianVolumeForm (Manifold.Orientation.mk l)).signedInChartAt
        ((Module.finBasis ℝ E).reindex σ) α (fun z ↦ l.signAt α z) y =
      if y ∈ (extChartAt I α).target then
        chartVolumeDensity (I := I) α ((extChartAt I α).symm y)
      else 0 := by
  set b := (Module.finBasis ℝ E).reindex σ
  by_cases hy : y ∈ (extChartAt I α).target
  · set x := (extChartAt I α).symm y
    have hx : x ∈ (extChartAt I α).source := (extChartAt I α).map_target hy
    have hxy : extChartAt I α x = y := (extChartAt I α).right_inv hy
    have hα : x ∈ (chartAt H α).source := by simpa only [extChartAt_source] using hx
    have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet] using hα
    have heval :
        ((riemannianVolumeForm (Manifold.Orientation.mk l)).inChartAt α (extChartAt I α x)) b =
          riemannianVolumeForm (Manifold.Orientation.mk l) x
            ((trivializationAt E (TangentSpace I) α).basisAt b hbase) := by
      rw [RoughForm.inChartAt_apply, ← TangentBundle.symmL_trivializationAt hα,
        (extChartAt I α).left_inv hx]
      congr 1
      ext i
      exact (TauCeti.Manifold.basisAt_apply b hbase i).symm
    rw [ite_eq_left hy, ← hxy, RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ hx,
      heval, riemannianVolumeForm_basisAt (Manifold.Orientation.mk l) σ hbase,
      Manifold.Orientation.orientationAt_mk, l.mapOrientation_orientationAt hα,
      l.chartOrientation_eq_ite α ⟨x, hα⟩, l.signAt_of_mem hα, hl]
    rcases Int.units_eq_one_or (l.sign α ⟨x, hα⟩) with hs | hs
    · simp [hs, b]
    · have hne :
          ((Module.finBasis ℝ E).reindex σ).orientation ≠
            -((Module.finBasis ℝ E).reindex σ).orientation :=
        Module.Ray.ne_neg_self _
      have hne1 : (-1 : ℤˣ) ≠ 1 := by decide
      simp [hs, b, hne, hne1]
  · rw [RoughForm.signedInChartAt_apply, dite_eq_right hy, ite_eq_right hy]

/-- Because `riemannianVolumeForm o` vanishes nowhere, its integrability forces compactness of the
manifold. -/
theorem compactSpace_of_integrableTopForm_riemannianVolumeForm
    (h : IntegrableTopForm (riemannianVolumeForm o)) : CompactSpace M :=
  ⟨by simpa using h.isCompact⟩

/-- On a noncompact manifold, `riemannianVolumeForm o` is not compactly supported, so its
`integralTopForm` evaluates to `0`. -/
theorem integralTopForm_riemannianVolumeForm_eq_zero_of_not_compactSpace
    (h : ¬ CompactSpace M) :
    integralTopForm o (riemannianVolumeForm o) = 0 :=
  integralTopForm_eq_zero_of_not_integrable o _ fun hi ↦
    h (compactSpace_of_integrableTopForm_riemannianVolumeForm o hi)

/-- In every dimension `m : ℕ` (including `m = 0`), the integral of the Riemannian volume form is
nonnegative. -/
theorem integralTopForm_riemannianVolumeForm_nonneg :
    0 ≤ integralTopForm o (riemannianVolumeForm o) := by
  classical
  by_cases hi : IntegrableTopForm (riemannianVolumeForm o)
  · have : CompactSpace M := compactSpace_of_integrableTopForm_riemannianVolumeForm o hi
    let : MeasurableSpace E := borel E
    have : BorelSpace E := ⟨rfl⟩
    let σ : Fin (Module.finrank ℝ E) ≃ Fin m := finCongr (by simpa using o.card_eq.symm)
    let b := (Module.finBasis ℝ E).reindex σ
    obtain ⟨l, rfl, hl⟩ := o.exists_lift_modelOrientation_eq b.orientation
    obtain ⟨_, α, s, _, _, _, _, hform⟩ := exists_chart_partition_integralTopForm l b
    rw [hform _ hi, hl, _root_.Orientation.signBasis_orientation, Units.val_one, Int.cast_one,
      one_mul]
    refine Finset.sum_nonneg fun i _ ↦ integral_nonneg fun y ↦ ?_
    rw [signedInChartAt_riemannianVolumeForm_eq σ l hl]
    split_ifs
    · exact chartVolumeDensity_nonneg _ _
    · exact le_rfl
  · rw [integralTopForm_eq_zero_of_not_integrable _ _ hi]

section ContinuousMetric

variable [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- For a continuous Riemannian metric, `riemannianVolumeForm o` is integrable if and only if the
manifold is compact. -/
theorem integrableTopForm_riemannianVolumeForm_iff_compactSpace :
    IntegrableTopForm (riemannianVolumeForm o) ↔ CompactSpace M := by
  refine ⟨compactSpace_of_integrableTopForm_riemannianVolumeForm o, fun h ↦ ?_⟩
  have : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    Bundle.IsContinuousRiemannianBundle.toIsContMDiffZero
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  exact (isSmoothForm_riemannianVolumeForm (n := 0) o).integrableTopForm
    (by simp [h.isCompact_univ])
    (Module.finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm))

/-- For an orientation lift `l` whose model orientation agrees with the reindexed standard basis
`b = (Module.finBasis ℝ E).reindex σ`, integrating the signed coordinate coefficient of
`riemannianVolumeForm (Orientation.mk l)` over the chart image of any measurable subset `s` of the
preferred chart source at `α` recovers `(riemannianVolume I M).real s`. -/
private theorem setIntegral_signedInChartAt_riemannianVolumeForm
    [LindelofSpace M] [MeasurableSpace M] [BorelSpace M] [MeasurableSpace E] [BorelSpace E]
    (σ : Fin (Module.finrank ℝ E) ≃ Fin m) (l : Manifold.OrientationLift I M (Fin m))
    (hl : l.modelOrientation = ((Module.finBasis ℝ E).reindex σ).orientation)
    {α : M} {s : Set M} (hs : s ⊆ (extChartAt I α).source) (hs_meas : MeasurableSet s) :
    ∫ y in (extChartAt I α) '' s,
      (riemannianVolumeForm (Manifold.Orientation.mk l)).signedInChartAt
        ((Module.finBasis ℝ E).reindex σ) α (fun x ↦ l.signAt α x) y
        ∂((Module.finBasis ℝ E).reindex σ).addHaar =
      (riemannianVolume I M).real s := by
  have hm : ‹MeasurableSpace E› = borel E := BorelSpace.measurable_eq
  cases hm
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hs_chart : s ⊆ (chartAt H α).source := by rwa [← extChartAt_source (I := I)]
  calc ∫ y in (extChartAt I α) '' s,
        (riemannianVolumeForm (Manifold.Orientation.mk l)).signedInChartAt
          ((Module.finBasis ℝ E).reindex σ) α (fun x ↦ l.signAt α x) y
          ∂((Module.finBasis ℝ E).reindex σ).addHaar
      = ∫ y in (extChartAt I α) '' s,
          chartVolumeDensity (I := I) α ((extChartAt I α).symm y) • (1 : ℝ)
            ∂(Module.finBasis ℝ E).addHaar := by
        rw [Module.Basis.addHaar_reindex]
        refine setIntegral_congr_fun (hs_meas.image_extChartAt α hs) fun y hy ↦ ?_
        rcases hy with ⟨x, hx, rfl⟩
        rw [signedInChartAt_riemannianVolumeForm_eq σ l hl,
          ite_eq_left ((extChartAt I α).map_source (hs hx)), smul_eq_mul, mul_one]
    _ = ∫ _ in s, (1 : ℝ) ∂riemannianVolume I M :=
        (setIntegral_riemannianVolume_of_subset hs_chart hs_meas (fun _ : M ↦ (1 : ℝ))).symm
    _ = (riemannianVolume I M).real s := by
        rw [setIntegral_const, smul_eq_mul, mul_one]

/-- **The integral of the Riemannian volume form equals the total Riemannian volume** on a compact
oriented Riemannian manifold, in every dimension `m : ℕ`. -/
theorem integralTopForm_riemannianVolumeForm_eq_riemannianTotalVolume
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M] :
    integralTopForm o (riemannianVolumeForm o) = riemannianTotalVolume I M := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let σ : Fin (Module.finrank ℝ E) ≃ Fin m := finCongr (by simpa using o.card_eq.symm)
  let b := (Module.finBasis ℝ E).reindex σ
  obtain ⟨l, rfl, hl⟩ := o.exists_lift_modelOrientation_eq b.orientation
  have hi : IntegrableTopForm (riemannianVolumeForm (Manifold.Orientation.mk l)) :=
    (integrableTopForm_riemannianVolumeForm_iff_compactSpace _).2 inferInstance
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M ↦ (extChartAt I x).source) (fun x ↦ isOpen_extChartAt_source x)
    (fun x _ ↦ mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩)
  let e : Fin t.card ≃ t := t.equivFin.symm
  let α : Fin t.card → M := fun i ↦ (e i : M)
  let u : Fin t.card → Set M := fun i ↦ (extChartAt I (α i)).source
  have hu : ∀ i, IsOpen (u i) := fun i ↦ isOpen_extChartAt_source (α i)
  have hs : ∀ i, u i ⊆ (extChartAt I (α i)).source := fun _ ↦ Subset.rfl
  have hcov : (univ : Set M) ⊆ ⋃ i, u i := fun x hx ↦ by
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨e.symm ⟨z, hz⟩, by simpa [u, α] using hxz⟩
  rw [integralTopForm_eq_sum_disjointed_chart_integrals l _ hi b α u hu hs
      ((subset_univ _).trans hcov),
    hl, _root_.Orientation.signBasis_orientation, Units.val_one, Int.cast_one, one_mul]
  have hs_meas : ∀ i, MeasurableSet (disjointed u i) := fun i ↦ by
    rw [disjointed_apply]
    have ho : IsOpen ((Finset.Iio i).sup u) := by
      rw [Finset.sup_set_eq_biUnion]
      exact isOpen_biUnion fun j _ ↦ hu j
    exact (hu i).measurableSet.diff ho.measurableSet
  rw [Finset.sum_congr rfl fun i _ ↦ setIntegral_signedInChartAt_riemannianVolumeForm σ l hl
    ((disjointed_subset u i).trans (hs i)) (hs_meas i),
    ← measureReal_iUnion_fintype (disjoint_disjointed u) hs_meas, iUnion_disjointed,
    Subset.antisymm (subset_univ _) hcov, riemannianTotalVolume_def]

/-- On a nonempty compact oriented Riemannian manifold of any dimension `m : ℕ`, the integral of the
Riemannian volume form is strictly positive. -/
theorem integralTopForm_riemannianVolumeForm_pos [CompactSpace M] [Nonempty M] :
    0 < integralTopForm o (riemannianVolumeForm o) := by
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  rw [integralTopForm_riemannianVolumeForm_eq_riemannianTotalVolume o]
  exact riemannianTotalVolume_pos

/-- For a continuous Riemannian metric, the integral of the Riemannian volume form does not depend
on the choice of orientation (even across disconnected components or noncompact manifolds). -/
theorem integralTopForm_riemannianVolumeForm_congr
    (o₁ o₂ : Manifold.Orientation I M (Fin m)) :
    integralTopForm o₁ (riemannianVolumeForm o₁) =
      integralTopForm o₂ (riemannianVolumeForm o₂) := by
  by_cases hc : CompactSpace M
  · let : MeasurableSpace M := borel M
    have : BorelSpace M := ⟨rfl⟩
    rw [integralTopForm_riemannianVolumeForm_eq_riemannianTotalVolume o₁,
      integralTopForm_riemannianVolumeForm_eq_riemannianTotalVolume o₂]
  · rw [integralTopForm_riemannianVolumeForm_eq_zero_of_not_compactSpace o₁ hc,
      integralTopForm_riemannianVolumeForm_eq_zero_of_not_compactSpace o₂ hc]

end ContinuousMetric

/-- The integral `∫_M f vol` of a nonnegative function against the Riemannian volume form is
nonnegative, on an oriented Riemannian manifold of positive dimension. -/
theorem integralTopForm_smul_riemannianVolumeForm_nonneg [NeZero m] {f : M → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) :=
  integralTopForm_nonneg o fun x c hc ↦ by
    let := o.fact_finrank_tangentSpace x
    rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, riemannianVolumeForm_apply]
    exact mul_nonneg (hf x) (Orientation.volumeForm_apply_pos_iff.2 hc).le

/-- Constant factors come out of the integral against the Riemannian volume form:
`∫_M c f vol = c ∫_M f vol`. -/
theorem integralTopForm_mul_smul_riemannianVolumeForm (c : ℝ) (f : M → ℝ) :
    integralTopForm o (fun x ↦ (c * f x) • riemannianVolumeForm o x) =
      c * integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) := by
  rw [← integralTopForm_smul]
  congr 1
  funext x
  rw [Pi.smul_apply, mul_smul]

section Continuous

variable [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]

/-- For a continuous function `f`, the top form `f vol` is continuous. -/
theorem isSmoothForm_smul_riemannianVolumeForm {f : M → ℝ} (hf : Continuous f) :
    IsSmoothForm I 0 (fun x ↦ f x • riemannianVolumeForm o x) := by
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  exact (isSmoothForm_riemannianVolumeForm o).fun_smul (contMDiff_zero_iff.2 hf)

variable [CompactSpace M]

/-- On a compact oriented Riemannian manifold, the integral against the Riemannian volume form is
additive on continuous functions: `∫_M (f + g) vol = ∫_M f vol + ∫_M g vol`. -/
theorem integralTopForm_add_smul_riemannianVolumeForm {f g : M → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    integralTopForm o (fun x ↦ (f x + g x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) +
        integralTopForm o (fun x ↦ g x • riemannianVolumeForm o x) := by
  rw [← integralTopForm_add_of_compactSpace o (isSmoothForm_smul_riemannianVolumeForm o hf)
    (isSmoothForm_smul_riemannianVolumeForm o hg)]
  congr 1
  funext x
  rw [Pi.add_apply, add_smul]

/-- **Monotonicity of the integral against the Riemannian volume form**: on a compact oriented
Riemannian manifold of positive dimension, continuous functions with `f ≤ g` satisfy
`∫_M f vol ≤ ∫_M g vol`. -/
theorem integralTopForm_smul_riemannianVolumeForm_mono [NeZero m] {f g : M → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, f x ≤ g x) :
    integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) ≤
      integralTopForm o (fun x ↦ g x • riemannianVolumeForm o x) := by
  have h :=
    integralTopForm_add_smul_riemannianVolumeForm o (g := fun x ↦ g x - f x) hf (hg.sub hf)
  simp only [add_sub_cancel] at h
  rw [h, le_add_iff_nonneg_right]
  exact integralTopForm_smul_riemannianVolumeForm_nonneg o fun x ↦ sub_nonneg.2 (hfg x)

end Continuous

end TauCeti
