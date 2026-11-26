/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Function.Jacobian
public import TauCeti.MeasureTheory.Function.Coarea.Eilenberg
import TauCeti.MeasureTheory.Integral.Measurable
import TauCeti.MeasureTheory.Measure.Hausdorff
import TauCeti.MeasureTheory.Measure.Regular
import TauCeti.MeasureTheory.Measure.Restrict
import TauCeti.Topology.EMetricSpace.Lipschitz

/-!
# Measurability of fiber measures, fiber integrals, and ambient-to-fiber descent

The coarea formula integrates the Hausdorff measures `y ↦ μH[t] (A ∩ f ⁻¹' {y})`, weighted
Lebesgue integrals `y ↦ ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]`, and Bochner integrals
`y ↦ ∫ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]` along the fibers of a map `f`. This file proves that these
fiber quantities depend almost everywhere (strongly) measurably on `y`, and that ambient
almost-everywhere properties on `A` descend to `μHE[k]`-almost-everywhere properties on almost
every fiber `A ∩ f ⁻¹' {y}`.

Fiber measures on compact and σ-compact sets (and on sets σ-compact up to a fiberwise-null
remainder) are measurable by `IsCompact.measurable_hausdorffMeasure_inter_preimage`,
`IsSigmaCompact.measurable_hausdorffMeasure_inter_preimage`, and
`TauCeti.aemeasurable_hausdorffMeasure_inter_preimage_of_ae_eq_zero` in
`TauCeti.MeasureTheory.Measure.Hausdorff`. This file extends them to measurable sets,
almost-everywhere measurable weights, and almost-everywhere strongly measurable Banach-valued
integrands via Eilenberg's inequality.

If `f` is Lipschitz (or locally Lipschitz) on `A` with values in a real normed space `Y` with
additive Haar measure `μ`, and `A` is σ-compact up to a `μH[finrank ℝ Y + t]`-null set, then
`y ↦ μH[t] (A ∩ f ⁻¹' {y})` is `μ`-almost everywhere measurable: the fibers of the null part are
null for almost every `y` by Eilenberg's inequality. When `A` is a subset of an `n`-dimensional
real inner product space `E` and `n ≤ finrank ℝ Y + k`, any condition holding
`volume.restrict A`-almost everywhere holds `μHE[k].restrict (A ∩ f ⁻¹' {y})`-almost everywhere for
`μ`-almost every `y`: enclosing the exceptional set in a Borel null hull of `volume.restrict A`
produces a subset of `A` of Lebesgue measure zero, hence `μHE[finrank ℝ Y + k]`-null, whose fibers
are `μHE[k]`-null almost everywhere by Eilenberg's inequality. Neither measurability nor openness of
`A` is needed for this descent. When `A` is Lebesgue measurable, measure-family integration
measurability (`TauCeti.MeasureTheory.Integral.Measurable`) combined with almost-everywhere descent
shows that `y ↦ ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]` is `μ`-almost everywhere measurable for every
`volume.restrict A`-almost everywhere measurable weight `g`, and
`y ↦ ∫ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]` is `μ`-almost everywhere strongly measurable for every
`volume.restrict A`-almost everywhere strongly measurable function `g` without any integrability
assumption.

Using Mathlib's countable Lipschitz decomposition of maps with within-set derivatives, the same
ambient-to-fiber descent and weighted/Bochner fiber-integral almost-everywhere (strong)
measurability extend to any map with a within-set derivative at each point of `s`, in the
complementary dimension `k = n - m`. Neither surjectivity of the derivative nor integrability of
the integrand is required.

## Main declarations

* `LipschitzOnWith.aemeasurable_hausdorffMeasure_inter_preimage`,
  `LocallyLipschitzOn.aemeasurable_hausdorffMeasure_inter_preimage`: fiber measures of a Lipschitz
  (or locally Lipschitz) map are almost everywhere measurable on a set that is σ-compact up to a
  null set.
* `LocallyLipschitzOn.ae_ae_restrict_preimage_of_ae_restrict`,
  `LocallyLipschitzOn.ae_ae_eq_restrict_preimage`,
  `LocallyLipschitzOn.ae_nullMeasurableSet_restrict_preimage`,
  `LocallyLipschitzOn.ae_aemeasurable_restrict_preimage`,
  `LocallyLipschitzOn.ae_aestronglyMeasurable_restrict_preimage`: ambient almost-everywhere
  predicates, equalities, null-measurable sets, and almost-everywhere (strongly) measurable
  functions descend along locally Lipschitz maps to `μHE[k]` on almost every fiber whenever
  `dim E ≤ finrank ℝ Y + k`.
* `LocallyLipschitzOn.aemeasurable_euclideanHausdorffMeasure_inter_preimage`,
  `LocallyLipschitzOn.aemeasurable_setLIntegral_euclideanHausdorffMeasure_inter_preimage`,
  `LocallyLipschitzOn.aestronglyMeasurable_setIntegral_euclideanHausdorffMeasure_inter_preimage`
  (and counterparts in `LipschitzOnWith`, `LocallyLipschitz`, and `LipschitzWith`):
  almost-everywhere measurability of normalized fiber measures and weighted fiber integrals, and
  almost-everywhere strong measurability of Bochner fiber integrals.
* `MeasureTheory.ae_ae_restrict_preimage_of_hasFDerivWithinAt`,
  `MeasureTheory.ae_ae_eq_restrict_preimage_of_hasFDerivWithinAt`,
  `MeasureTheory.aemeasurable_euclideanHausdorffMeasure_inter_preimage_of_hasFDerivWithinAt`,
  `MeasureTheory.aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt`,
  `MeasureTheory.aestronglyMeasurable_setIntegral_fiber_of_hasFDerivWithinAt`: ambient-to-fiber
  descent and fiber almost-everywhere (strong) measurability for maps with within-set derivatives.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4.1 (measurability of the fiber measures in the coarea formula).
* H. Federer, *Geometric Measure Theory*, §3.2.11–3.2.12.
-/

public section

open MeasureTheory Measure Set Filter Module
open scoped ENNReal NNReal

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

section FiberMeasurability

variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure Y) [μ.IsAddHaarMeasure] {K : ℝ≥0} {t : ℝ}

/-- **Fiber measures of a Lipschitz map are almost everywhere measurable.** Let `f` be Lipschitz
on `A`, with values in a real normed space `Y` with additive Haar measure `μ`, and let `t` be
real. If `A` contains a σ-compact set `S` with `μH[finrank ℝ Y + t] (A \ S) = 0`, then
`y ↦ μH[t] (A ∩ f ⁻¹' {y})` is `μ`-almost everywhere measurable. -/
theorem LipschitzOnWith.aemeasurable_hausdorffMeasure_inter_preimage {f : X → Y} {A S : Set X}
    (hf : LipschitzOnWith K f A) (hSA : S ⊆ A) (hS : IsSigmaCompact S)
    (hAS : μH[finrank ℝ Y + t] (A \ S) = 0) :
    AEMeasurable (fun y ↦ μH[t] (A ∩ f ⁻¹' {y})) μ :=
  TauCeti.aemeasurable_hausdorffMeasure_inter_preimage_of_ae_eq_zero hSA hS
    (hf.continuousOn.mono hSA)
    ((hf.mono sdiff_subset).ae_hausdorffMeasure_inter_preimage_eq_zero μ hAS)

/-- **Fiber measures of a locally Lipschitz map are almost everywhere measurable.** Let `f` be
locally Lipschitz on `A`, with values in a real normed space `Y` with additive Haar measure `μ`,
and let `t` be real. If `A` contains a σ-compact set `S` with `μH[finrank ℝ Y + t] (A \ S) = 0`,
then `y ↦ μH[t] (A ∩ f ⁻¹' {y})` is `μ`-almost everywhere measurable. The null set `A \ S` is
separable, so countably many Lipschitz pieces cover it. -/
theorem LocallyLipschitzOn.aemeasurable_hausdorffMeasure_inter_preimage
    {f : X → Y} {A S : Set X}
    (hf : LocallyLipschitzOn A f) (hSA : S ⊆ A) (hS : IsSigmaCompact S)
    (hAS : μH[finrank ℝ Y + t] (A \ S) = 0) :
    AEMeasurable (fun y ↦ μH[t] (A ∩ f ⁻¹' {y})) μ :=
  TauCeti.aemeasurable_hausdorffMeasure_inter_preimage_of_ae_eq_zero hSA hS
    (hf.continuousOn.mono hSA)
    ((hf.mono sdiff_subset).ae_hausdorffMeasure_inter_preimage_eq_zero μ hAS)

end FiberMeasurability

section EuclideanFiberDescent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [μ.IsAddHaarMeasure]

namespace LocallyLipschitzOn

variable {f : E → Y} {A : Set E} {k : ℕ}

/-- If `f` is locally Lipschitz on a Lebesgue-null subset `A` of `E` and `dim E ≤ finrank ℝ Y + k`,
then `A ∩ f ⁻¹' {y}` is `μHE[k]`-null for `μ`-almost every `y`. No measurability of `A` is
needed. -/
theorem ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_volume_eq_zero
    (hf : LocallyLipschitzOn A f) (hA : volume A = 0)
    (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    ∀ᵐ y ∂μ, μHE[k] (A ∩ f ⁻¹' {y}) = 0 :=
  hf.ae_euclideanHausdorffMeasure_inter_preimage_eq_zero μ
    (TauCeti.euclideanHausdorffMeasure_eq_zero_of_volume_eq_zero hA hk)

/-- **Ambient-to-fiber almost-everywhere descent for locally Lipschitz maps.** If `f` is locally
Lipschitz on `A ⊆ E`, `p` holds `volume.restrict A`-almost everywhere, and
`dim E ≤ finrank ℝ Y + k`, then `p` holds `μHE[k]`-almost everywhere on `A ∩ f ⁻¹' {y}` for
`μ`-almost every `y`. Neither `A` nor `p` need be measurable. -/
theorem ae_ae_restrict_preimage_of_ae_restrict (hf : LocallyLipschitzOn A f) {p : E → Prop}
    (hp : ∀ᵐ x ∂volume.restrict A, p x) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    ∀ᵐ y ∂μ, ∀ᵐ x ∂μHE[k].restrict (A ∩ f ⁻¹' {y}), p x := by
  set T := toMeasurable (volume.restrict A) {x | ¬p x}
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hTA : volume (T ∩ A) = 0 :=
    measure_inter_eq_zero_of_restrict ((measure_toMeasurable _).trans (ae_iff.1 hp))
  have hfib := (hf.mono inter_subset_right)
    |>.ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_volume_eq_zero μ hTA hk
  filter_upwards [hfib] with y hy
  refine ae_iff.2 (nonpos_iff_eq_zero.1 ?_)
  calc (μHE[k].restrict (A ∩ f ⁻¹' {y})) {x | ¬p x}
      ≤ (μHE[k].restrict (A ∩ f ⁻¹' {y})) T := measure_mono (subset_toMeasurable _ _)
    _ = μHE[k] ((T ∩ A) ∩ f ⁻¹' {y}) := by rw [Measure.restrict_apply hTm, inter_assoc]
    _ = 0 := hy

/-- Ambient almost-everywhere equality on `A` descends along a locally Lipschitz map to
`μHE[k]`-almost-everywhere equality on almost every fiber `A ∩ f ⁻¹' {y}` when
`dim E ≤ finrank ℝ Y + k`. -/
theorem ae_ae_eq_restrict_preimage (hf : LocallyLipschitzOn A f) {Z : Type*} {g₁ g₂ : E → Z}
    (hg : g₁ =ᵐ[volume.restrict A] g₂) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    ∀ᵐ y ∂μ, g₁ =ᵐ[μHE[k].restrict (A ∩ f ⁻¹' {y})] g₂ :=
  hf.ae_ae_restrict_preimage_of_ae_restrict μ hg hk

/-- A `volume.restrict A`-null-measurable set is `μHE[k]`-null-measurable on almost every fiber
`A ∩ f ⁻¹' {y}` of a map locally Lipschitz on `A` when `dim E ≤ finrank ℝ Y + k`. -/
theorem ae_nullMeasurableSet_restrict_preimage (hf : LocallyLipschitzOn A f) {t : Set E}
    (ht : NullMeasurableSet t (volume.restrict A)) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    ∀ᵐ y ∂μ, NullMeasurableSet t (μHE[k].restrict (A ∩ f ⁻¹' {y})) := by
  filter_upwards [hf.ae_ae_eq_restrict_preimage μ
    (g₁ := (· ∈ toMeasurable (volume.restrict A) t)) (g₂ := (· ∈ t))
    (ht.toMeasurable_ae_eq.mono fun _ h ↦ propext h) hk] with y hy
  exact (measurableSet_toMeasurable _ _).nullMeasurableSet.congr
    (hy.mono fun _ h ↦ Iff.of_eq h)

/-- An almost-everywhere measurable function on `A` is `μHE[k]`-almost everywhere measurable on
almost every fiber `A ∩ f ⁻¹' {y}` of a map locally Lipschitz on `A` when
`dim E ≤ finrank ℝ Y + k`. -/
theorem ae_aemeasurable_restrict_preimage {Z : Type*} [MeasurableSpace Z]
    (hf : LocallyLipschitzOn A f) {g : E → Z} (hg : AEMeasurable g (volume.restrict A))
    (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    ∀ᵐ y ∂μ, AEMeasurable g (μHE[k].restrict (A ∩ f ⁻¹' {y})) := by
  filter_upwards [hf.ae_ae_eq_restrict_preimage μ hg.ae_eq_mk hk] with y hy
  exact hg.measurable_mk.aemeasurable.congr hy.symm

/-- An almost-everywhere strongly measurable function on `A` is `μHE[k]`-almost everywhere
strongly measurable on almost every fiber `A ∩ f ⁻¹' {y}` of a map locally Lipschitz on `A` when
`dim E ≤ finrank ℝ Y + k`. -/
theorem ae_aestronglyMeasurable_restrict_preimage {Z : Type*} [TopologicalSpace Z]
    (hf : LocallyLipschitzOn A f) {g : E → Z} (hg : AEStronglyMeasurable g (volume.restrict A))
    (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    ∀ᵐ y ∂μ, AEStronglyMeasurable g (μHE[k].restrict (A ∩ f ⁻¹' {y})) := by
  obtain ⟨g₀, hg₀, hgg₀⟩ := hg
  filter_upwards [hf.ae_ae_eq_restrict_preimage μ hgg₀ hk] with y hy
  exact hg₀.aestronglyMeasurable.congr hy.symm

/-- Volume-almost-everywhere equal sets `A₁ =ᵐ[volume] A₂` on whose union `f` is locally Lipschitz
induce identical restricted fiber measures `μHE[k].restrict (Aᵢ ∩ f ⁻¹' {y})` for `μ`-almost every
`y` when `dim E ≤ finrank ℝ Y + k`. -/
theorem ae_restrict_euclideanHausdorffMeasure_preimage_congr {A₁ A₂ : Set E}
    (hf : LocallyLipschitzOn (A₁ ∪ A₂) f) (hA : A₁ =ᵐ[volume] A₂)
    (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    ∀ᵐ y ∂μ, μHE[k].restrict (A₁ ∩ f ⁻¹' {y}) = μHE[k].restrict (A₂ ∩ f ⁻¹' {y}) := by
  have h12 := (hf.mono (sdiff_subset.trans subset_union_left))
    |>.ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_volume_eq_zero μ
      (ae_eq_set.1 hA).1 hk
  have h21 := (hf.mono (sdiff_subset.trans subset_union_right))
    |>.ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_volume_eq_zero μ
      (ae_eq_set.1 hA).2 hk
  filter_upwards [h12, h21] with y hy12 hy21
  exact Measure.restrict_congr_set ((ae_eq_set (s := A₁ ∩ f ⁻¹' {y}) (t := A₂ ∩ f ⁻¹' {y})).2
    ⟨measure_mono_null (by intro x; simp; tauto) hy12,
      measure_mono_null (by intro x; simp; tauto) hy21⟩)

/-- **Normalized fiber measures of a locally Lipschitz map on a Lebesgue measurable set are almost
everywhere measurable.** Let `f` be locally Lipschitz on a Lebesgue measurable subset `A` of an
`n`-dimensional real inner product space, with values in a real normed space `Y` with additive
Haar measure `μ`. If `n ≤ finrank ℝ Y + k`, then `y ↦ μHE[k] (A ∩ f ⁻¹' {y})` is `μ`-almost
everywhere measurable. Neither openness of `A` nor a global Lipschitz bound is needed. This
applies to the coarea dimension `k = n - finrank ℝ Y`, for which `n ≤ finrank ℝ Y + k` is
`le_add_tsub`. -/
theorem aemeasurable_euclideanHausdorffMeasure_inter_preimage (hf : LocallyLipschitzOn A f)
    (hA : NullMeasurableSet A) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ μHE[k] (A ∩ f ⁻¹' {y})) μ := by
  obtain ⟨S, hSA, hS, hSA'⟩ := hA.exists_isSigmaCompact_subset_ae_eq
  -- The null part `A \ S` is null for the `n`-dimensional, hence `(finrank ℝ Y + k)`-dimensional,
  -- Hausdorff measure.
  have hnull : μH[finrank ℝ Y + (k : ℝ)] (A \ S) = 0 :=
    TauCeti.hausdorffMeasure_eq_zero_of_volume_eq_zero (ae_eq_set.1 hSA').2 (by exact_mod_cast hk)
  simp only [euclideanHausdorffMeasure_def, _root_.smul_apply]
  exact (hf.aemeasurable_hausdorffMeasure_inter_preimage μ hSA hS hnull).const_smul _

private theorem aemeasurable_restrict_euclideanHausdorffMeasure_inter_preimage
    (hf : LocallyLipschitzOn A f) (hA : NullMeasurableSet A) (hk : finrank ℝ E ≤ finrank ℝ Y + k)
    (t : Set E) (ht : MeasurableSet t) :
    AEMeasurable (fun y ↦ (μHE[k].restrict (A ∩ f ⁻¹' {y})) t) μ := by
  simp_rw [Measure.restrict_inter_apply _ _ _ ht]
  exact (hf.mono inter_subset_left).aemeasurable_euclideanHausdorffMeasure_inter_preimage μ
    (hA.inter ht.nullMeasurableSet) hk

/-- **Weighted fiber integrals of a locally Lipschitz map are almost everywhere measurable.** Let
`f` be locally Lipschitz on a Lebesgue-measurable set `A ⊆ E` and let `g : E → ℝ≥0∞` be
`volume.restrict A`-almost everywhere measurable. Whenever `dim E ≤ finrank ℝ Y + k`, the
fiber-integral map `y ↦ ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]` is `μ`-almost everywhere measurable. -/
theorem aemeasurable_setLIntegral_euclideanHausdorffMeasure_inter_preimage
    (hf : LocallyLipschitzOn A f) (hA : NullMeasurableSet A) {g : E → ℝ≥0∞}
    (hg : AEMeasurable g (volume.restrict A)) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]) μ := by
  refine (hg.measurable_mk.aemeasurable_lintegral_of_aemeasurable_measure
    (hf.aemeasurable_restrict_euclideanHausdorffMeasure_inter_preimage μ hA hk)).congr ?_
  filter_upwards [hf.ae_ae_eq_restrict_preimage μ hg.ae_eq_mk hk] with y hy
  exact (lintegral_congr_ae hy).symm

/-- **Bochner fiber integrals of a locally Lipschitz map are almost everywhere strongly
measurable.** Let `f` be locally Lipschitz on a Lebesgue-measurable set `A ⊆ E` and let `g : E → V`
be `volume.restrict A`-almost everywhere strongly measurable. Whenever `dim E ≤ finrank ℝ Y + k`,
the fiber-integral map `y ↦ ∫ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]` is `μ`-almost everywhere strongly
measurable. No integrability assumption on `g` is needed. -/
theorem aestronglyMeasurable_setIntegral_euclideanHausdorffMeasure_inter_preimage
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hf : LocallyLipschitzOn A f) (hA : NullMeasurableSet A) {g : E → V}
    (hg : AEStronglyMeasurable g (volume.restrict A)) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEStronglyMeasurable (fun y ↦ ∫ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]) μ := by
  refine (hg.stronglyMeasurable_mk.aestronglyMeasurable_integral_of_aemeasurable_measure
    (hf.aemeasurable_restrict_euclideanHausdorffMeasure_inter_preimage μ hA hk)).congr ?_
  filter_upwards [hf.ae_ae_eq_restrict_preimage μ hg.ae_eq_mk hk] with y hy
  exact (integral_congr_ae hy).symm

end LocallyLipschitzOn

namespace LipschitzOnWith

variable {K : ℝ≥0} {f : E → Y} {A : Set E} {k : ℕ}

/-- Normalized fiber measures `y ↦ μHE[k] (A ∩ f ⁻¹' {y})` of a Lipschitz-on-`A` map on a Lebesgue
measurable set `A` are `μ`-almost everywhere measurable when `dim E ≤ dim Y + k`. -/
theorem aemeasurable_euclideanHausdorffMeasure_inter_preimage (hf : LipschitzOnWith K f A)
    (hA : NullMeasurableSet A) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ μHE[k] (A ∩ f ⁻¹' {y})) μ :=
  hf.locallyLipschitzOn.aemeasurable_euclideanHausdorffMeasure_inter_preimage μ hA hk

/-- Weighted fiber integrals `y ↦ ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]` of a Lipschitz-on-`A` map on
a Lebesgue measurable set `A` are `μ`-almost everywhere measurable when `dim E ≤ dim Y + k`. -/
theorem aemeasurable_setLIntegral_euclideanHausdorffMeasure_inter_preimage
    (hf : LipschitzOnWith K f A) (hA : NullMeasurableSet A) {g : E → ℝ≥0∞}
    (hg : AEMeasurable g (volume.restrict A)) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]) μ :=
  hf.locallyLipschitzOn.aemeasurable_setLIntegral_euclideanHausdorffMeasure_inter_preimage μ hA hg
    hk

/-- Bochner fiber integrals `y ↦ ∫ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]` of a Lipschitz-on-`A` map on a
Lebesgue measurable set `A` are `μ`-almost everywhere strongly measurable when
`dim E ≤ dim Y + k`. -/
theorem aestronglyMeasurable_setIntegral_euclideanHausdorffMeasure_inter_preimage
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hf : LipschitzOnWith K f A) (hA : NullMeasurableSet A) {g : E → V}
    (hg : AEStronglyMeasurable g (volume.restrict A)) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEStronglyMeasurable (fun y ↦ ∫ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]) μ :=
  hf.locallyLipschitzOn.aestronglyMeasurable_setIntegral_euclideanHausdorffMeasure_inter_preimage
    μ hA hg hk

end LipschitzOnWith

namespace LocallyLipschitz

variable {f : E → Y} {A : Set E} {k : ℕ}

/-- Ambient almost-everywhere predicates on `E` descend along a locally Lipschitz map to
`μHE[k]`-almost-everywhere predicates on `f ⁻¹' {y}` for `μ`-almost every `y` when
`dim E ≤ dim Y + k`. -/
theorem ae_ae_restrict_preimage_of_ae (hf : LocallyLipschitz f) {p : E → Prop} (hp : ∀ᵐ x : E, p x)
    (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    ∀ᵐ y ∂μ, ∀ᵐ x ∂μHE[k].restrict (f ⁻¹' {y}), p x := by
  simpa only [univ_inter] using
    (hf.locallyLipschitzOn (s := univ)).ae_ae_restrict_preimage_of_ae_restrict μ
      (by simpa only [Measure.restrict_univ] using hp) hk

/-- Ambient almost-everywhere equality on `E` descends along a locally Lipschitz map to
`μHE[k]`-almost-everywhere equality on almost every fiber `f ⁻¹' {y}` when `dim E ≤ dim Y + k`. -/
theorem ae_ae_eq_restrict_preimage (hf : LocallyLipschitz f) {Z : Type*} {g₁ g₂ : E → Z}
    (hg : g₁ =ᵐ[volume] g₂) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    ∀ᵐ y ∂μ, g₁ =ᵐ[μHE[k].restrict (f ⁻¹' {y})] g₂ :=
  hf.ae_ae_restrict_preimage_of_ae μ hg hk

/-- Normalized fiber measures `y ↦ μHE[k] (A ∩ f ⁻¹' {y})` of a locally Lipschitz map on a Lebesgue
measurable set `A` are `μ`-almost everywhere measurable when `dim E ≤ dim Y + k`. -/
theorem aemeasurable_euclideanHausdorffMeasure_inter_preimage (hf : LocallyLipschitz f)
    (hA : NullMeasurableSet A) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ μHE[k] (A ∩ f ⁻¹' {y})) μ :=
  (hf.locallyLipschitzOn (s := A)).aemeasurable_euclideanHausdorffMeasure_inter_preimage μ hA hk

/-- Normalized global fiber measures `y ↦ μHE[k] (f ⁻¹' {y})` of a locally Lipschitz map are
`μ`-almost everywhere measurable when `dim E ≤ dim Y + k`. -/
theorem aemeasurable_euclideanHausdorffMeasure_preimage (hf : LocallyLipschitz f)
    (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ μHE[k] (f ⁻¹' {y})) μ := by
  simpa only [univ_inter] using
    hf.aemeasurable_euclideanHausdorffMeasure_inter_preimage μ MeasurableSet.univ.nullMeasurableSet
      hk

/-- Weighted fiber integrals `y ↦ ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]` of a locally Lipschitz map
on a Lebesgue-measurable set `A` are `μ`-almost everywhere measurable when `dim E ≤ dim Y + k`. -/
theorem aemeasurable_setLIntegral_euclideanHausdorffMeasure_inter_preimage (hf : LocallyLipschitz f)
    (hA : NullMeasurableSet A) {g : E → ℝ≥0∞} (hg : AEMeasurable g (volume.restrict A))
    (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]) μ :=
  (hf.locallyLipschitzOn (s := A))
    |>.aemeasurable_setLIntegral_euclideanHausdorffMeasure_inter_preimage μ hA hg hk

/-- Weighted global fiber integrals `y ↦ ∫⁻ x in f ⁻¹' {y}, g x ∂μHE[k]` of a locally Lipschitz map
are `μ`-almost everywhere measurable for every Lebesgue almost-everywhere measurable weight `g`
when `dim E ≤ dim Y + k`. -/
theorem aemeasurable_setLIntegral_euclideanHausdorffMeasure_preimage (hf : LocallyLipschitz f)
    {g : E → ℝ≥0∞} (hg : AEMeasurable g) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ ∫⁻ x in f ⁻¹' {y}, g x ∂μHE[k]) μ := by
  simpa only [univ_inter] using
    hf.aemeasurable_setLIntegral_euclideanHausdorffMeasure_inter_preimage μ
      MeasurableSet.univ.nullMeasurableSet (by simpa only [Measure.restrict_univ] using hg) hk

/-- Bochner fiber integrals `y ↦ ∫ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]` of a locally Lipschitz map on a
Lebesgue-measurable set `A` are `μ`-almost everywhere strongly measurable when
`dim E ≤ dim Y + k`. -/
theorem aestronglyMeasurable_setIntegral_euclideanHausdorffMeasure_inter_preimage
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (hf : LocallyLipschitz f)
    (hA : NullMeasurableSet A) {g : E → V} (hg : AEStronglyMeasurable g (volume.restrict A))
    (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEStronglyMeasurable (fun y ↦ ∫ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]) μ :=
  (hf.locallyLipschitzOn (s := A))
    |>.aestronglyMeasurable_setIntegral_euclideanHausdorffMeasure_inter_preimage μ hA hg hk

/-- Global Bochner fiber integrals `y ↦ ∫ x in f ⁻¹' {y}, g x ∂μHE[k]` of a locally Lipschitz map
are `μ`-almost everywhere strongly measurable for every Lebesgue almost-everywhere strongly
measurable function `g` when `dim E ≤ dim Y + k`. -/
theorem aestronglyMeasurable_setIntegral_euclideanHausdorffMeasure_preimage
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (hf : LocallyLipschitz f)
    {g : E → V} (hg : AEStronglyMeasurable g) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEStronglyMeasurable (fun y ↦ ∫ x in f ⁻¹' {y}, g x ∂μHE[k]) μ := by
  simpa only [univ_inter] using
    hf.aestronglyMeasurable_setIntegral_euclideanHausdorffMeasure_inter_preimage μ
      MeasurableSet.univ.nullMeasurableSet (by simpa only [Measure.restrict_univ] using hg) hk

end LocallyLipschitz

namespace LipschitzWith

variable {K : ℝ≥0} {f : E → Y} {A : Set E} {k : ℕ}

/-- Ambient almost-everywhere predicates on `E` descend along a Lipschitz map to
`μHE[k]`-almost-everywhere predicates on `f ⁻¹' {y}` for `μ`-almost every `y` when
`dim E ≤ dim Y + k`. -/
theorem ae_ae_restrict_preimage_of_ae (hf : LipschitzWith K f) {p : E → Prop} (hp : ∀ᵐ x : E, p x)
    (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    ∀ᵐ y ∂μ, ∀ᵐ x ∂μHE[k].restrict (f ⁻¹' {y}), p x :=
  hf.locallyLipschitz.ae_ae_restrict_preimage_of_ae μ hp hk

/-- Ambient almost-everywhere equality on `E` descends along a Lipschitz map to
`μHE[k]`-almost-everywhere equality on almost every fiber `f ⁻¹' {y}` when `dim E ≤ dim Y + k`. -/
theorem ae_ae_eq_restrict_preimage (hf : LipschitzWith K f) {Z : Type*} {g₁ g₂ : E → Z}
    (hg : g₁ =ᵐ[volume] g₂) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    ∀ᵐ y ∂μ, g₁ =ᵐ[μHE[k].restrict (f ⁻¹' {y})] g₂ :=
  hf.locallyLipschitz.ae_ae_eq_restrict_preimage μ hg hk

/-- Normalized fiber measures `y ↦ μHE[k] (A ∩ f ⁻¹' {y})` of a Lipschitz map on a Lebesgue
measurable set `A` are `μ`-almost everywhere measurable when `dim E ≤ dim Y + k`. -/
theorem aemeasurable_euclideanHausdorffMeasure_inter_preimage (hf : LipschitzWith K f)
    (hA : NullMeasurableSet A) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ μHE[k] (A ∩ f ⁻¹' {y})) μ :=
  hf.locallyLipschitz.aemeasurable_euclideanHausdorffMeasure_inter_preimage μ hA hk

/-- Normalized global fiber measures `y ↦ μHE[k] (f ⁻¹' {y})` of a Lipschitz map are `μ`-almost
everywhere measurable when `dim E ≤ dim Y + k`. -/
theorem aemeasurable_euclideanHausdorffMeasure_preimage (hf : LipschitzWith K f)
    (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ μHE[k] (f ⁻¹' {y})) μ :=
  hf.locallyLipschitz.aemeasurable_euclideanHausdorffMeasure_preimage μ hk

/-- Weighted fiber integrals `y ↦ ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]` of a Lipschitz map on a
Lebesgue-measurable set `A` are `μ`-almost everywhere measurable when `dim E ≤ dim Y + k`. -/
theorem aemeasurable_setLIntegral_euclideanHausdorffMeasure_inter_preimage (hf : LipschitzWith K f)
    (hA : NullMeasurableSet A) {g : E → ℝ≥0∞} (hg : AEMeasurable g (volume.restrict A))
    (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ ∫⁻ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]) μ :=
  hf.locallyLipschitz.aemeasurable_setLIntegral_euclideanHausdorffMeasure_inter_preimage μ hA hg hk

/-- Weighted global fiber integrals `y ↦ ∫⁻ x in f ⁻¹' {y}, g x ∂μHE[k]` of a Lipschitz map are
`μ`-almost everywhere measurable for every Lebesgue almost-everywhere measurable weight `g` when
`dim E ≤ dim Y + k`. -/
theorem aemeasurable_setLIntegral_euclideanHausdorffMeasure_preimage (hf : LipschitzWith K f)
    {g : E → ℝ≥0∞} (hg : AEMeasurable g) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ ∫⁻ x in f ⁻¹' {y}, g x ∂μHE[k]) μ :=
  hf.locallyLipschitz.aemeasurable_setLIntegral_euclideanHausdorffMeasure_preimage μ hg hk

/-- Bochner fiber integrals `y ↦ ∫ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]` of a Lipschitz map on a
Lebesgue-measurable set `A` are `μ`-almost everywhere strongly measurable when
`dim E ≤ dim Y + k`. -/
theorem aestronglyMeasurable_setIntegral_euclideanHausdorffMeasure_inter_preimage
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (hf : LipschitzWith K f)
    (hA : NullMeasurableSet A) {g : E → V} (hg : AEStronglyMeasurable g (volume.restrict A))
    (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEStronglyMeasurable (fun y ↦ ∫ x in A ∩ f ⁻¹' {y}, g x ∂μHE[k]) μ :=
  hf.locallyLipschitz.aestronglyMeasurable_setIntegral_euclideanHausdorffMeasure_inter_preimage
    μ hA hg hk

/-- Global Bochner fiber integrals `y ↦ ∫ x in f ⁻¹' {y}, g x ∂μHE[k]` of a Lipschitz map are
`μ`-almost everywhere strongly measurable for every Lebesgue almost-everywhere strongly measurable
function `g` when `dim E ≤ dim Y + k`. -/
theorem aestronglyMeasurable_setIntegral_euclideanHausdorffMeasure_preimage
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (hf : LipschitzWith K f)
    {g : E → V} (hg : AEStronglyMeasurable g) (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEStronglyMeasurable (fun y ↦ ∫ x in f ⁻¹' {y}, g x ∂μHE[k]) μ :=
  hf.locallyLipschitz.aestronglyMeasurable_setIntegral_euclideanHausdorffMeasure_preimage μ hg hk

end LipschitzWith

end EuclideanFiberDescent

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {f : E → F} {s : Set E}
  (μ : Measure F) [μ.IsAddHaarMeasure]

/-- **Ambient-to-fiber descent for maps with within-set derivatives.** If `f` has a derivative
within `s` at every point of `s` and `p` holds `volume.restrict s`-almost everywhere, then `p`
holds `μHE[dim E - dim F]`-almost everywhere on `s ∩ f ⁻¹' {y}` for `μ`-almost every `y`. Neither
`s` nor `p` need be measurable. -/
theorem ae_ae_restrict_preimage_of_hasFDerivWithinAt {f' : E → E →L[ℝ] F}
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) {p : E → Prop}
    (hp : ∀ᵐ x ∂volume.restrict s, p x) :
    ∀ᵐ y ∂μ, ∀ᵐ x ∂μHE[finrank ℝ E - finrank ℝ F].restrict (s ∩ f ⁻¹' {y}), p x := by
  obtain ⟨t, A, -, -, hcover, happrox, -⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hd
      (fun _ ↦ 1) fun _ ↦ one_ne_zero
  have hpiece : ∀ᵐ y ∂μ, ∀ n,
      ∀ᵐ x ∂μHE[finrank ℝ E - finrank ℝ F].restrict ((s ∩ t n) ∩ f ⁻¹' {y}), p x :=
    ae_all_iff.2 fun n ↦
      (lipschitzOnWith_iff_restrict.2 (happrox n).lipschitzWith).locallyLipschitzOn
        |>.ae_ae_restrict_preimage_of_ae_restrict μ
          (ae_restrict_of_ae_restrict_of_subset inter_subset_left hp) le_add_tsub
  filter_upwards [hpiece] with y hy
  have hset : s ∩ f ⁻¹' {y} = ⋃ n, (s ∩ t n) ∩ f ⁻¹' {y} := by
    ext x; have := @hcover x; simp at this ⊢; aesop
  rw [hset, ae_restrict_iUnion_iff]
  exact hy

/-- Ambient almost-everywhere equality on `s` descends along a map with within-set derivatives to
`μHE[dim E - dim F]`-almost-everywhere equality on almost every fiber `s ∩ f ⁻¹' {y}`. -/
theorem ae_ae_eq_restrict_preimage_of_hasFDerivWithinAt {f' : E → E →L[ℝ] F}
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) {Z : Type*} {g₁ g₂ : E → Z}
    (hg : g₁ =ᵐ[volume.restrict s] g₂) :
    ∀ᵐ y ∂μ, g₁ =ᵐ[μHE[finrank ℝ E - finrank ℝ F].restrict (s ∩ f ⁻¹' {y})] g₂ :=
  ae_ae_restrict_preimage_of_hasFDerivWithinAt μ hd hg

/-- An almost-everywhere measurable function on `s` descends along a map with within-set
derivatives to a `μHE[dim E - dim F]`-almost everywhere measurable function on almost every fiber
`s ∩ f ⁻¹' {y}`. -/
theorem ae_aemeasurable_restrict_preimage_of_hasFDerivWithinAt {Z : Type*} [MeasurableSpace Z]
    {f' : E → E →L[ℝ] F} (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    {g : E → Z} (hg : AEMeasurable g (volume.restrict s)) :
    ∀ᵐ y ∂μ, AEMeasurable g (μHE[finrank ℝ E - finrank ℝ F].restrict (s ∩ f ⁻¹' {y})) := by
  filter_upwards [ae_ae_eq_restrict_preimage_of_hasFDerivWithinAt μ hd hg.ae_eq_mk] with y hy
  exact hg.measurable_mk.aemeasurable.congr hy.symm

/-- An almost-everywhere strongly measurable function on `s` descends along a map with within-set
derivatives to a `μHE[dim E - dim F]`-almost everywhere strongly measurable function on almost every
fiber `s ∩ f ⁻¹' {y}`. -/
theorem ae_aestronglyMeasurable_restrict_preimage_of_hasFDerivWithinAt {Z : Type*}
    [TopologicalSpace Z] {f' : E → E →L[ℝ] F} (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    {g : E → Z} (hg : AEStronglyMeasurable g (volume.restrict s)) :
    ∀ᵐ y ∂μ, AEStronglyMeasurable g
      (μHE[finrank ℝ E - finrank ℝ F].restrict (s ∩ f ⁻¹' {y})) := by
  obtain ⟨g₀, hg₀, hgg₀⟩ := hg
  filter_upwards [ae_ae_eq_restrict_preimage_of_hasFDerivWithinAt μ hd hgg₀] with y hy
  exact hg₀.aestronglyMeasurable.congr hy.symm

/-- Weighted fiber integrals of an almost-everywhere measurable weight along a map with a
within-set derivative on a Lebesgue-measurable set are almost everywhere measurable. Neither
surjectivity of the derivative nor integrability of the weight is required. -/
theorem aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt
    (hs : NullMeasurableSet s volume) {f' : E → E →L[ℝ] F}
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    {g : E → ℝ≥0∞} (hg : AEMeasurable g (volume.restrict s)) :
    AEMeasurable (fun y ↦ ∫⁻ x in s ∩ f ⁻¹' {y}, g x
      ∂μHE[finrank ℝ E - finrank ℝ F]) μ := by
  obtain ⟨t, A, hdisj, htm, hcover, happrox, -⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hd
      (fun _ ↦ 1) fun _ ↦ one_ne_zero
  have hmeas (n : ℕ) : AEMeasurable
      (fun y ↦ ∫⁻ x in (s ∩ t n) ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) μ :=
    (lipschitzOnWith_iff_restrict.2 (happrox n).lipschitzWith).locallyLipschitzOn
      |>.aemeasurable_setLIntegral_euclideanHausdorffMeasure_inter_preimage μ
        (hs.inter (htm n).nullMeasurableSet) (hg.mono_set inter_subset_left) le_add_tsub
  have heq (y : F) : (∫⁻ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) =
      ∑' n, ∫⁻ x in (s ∩ t n) ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
    have hset : (⋃ n, t n) ∩ (s ∩ f ⁻¹' {y}) = s ∩ f ⁻¹' {y} :=
      inter_eq_right.mpr (inter_subset_left.trans hcover)
    calc (∫⁻ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F])
        = ∫⁻ x in ⋃ n, t n, g x
            ∂(μHE[finrank ℝ E - finrank ℝ F].restrict (s ∩ f ⁻¹' {y})) := by
          rw [Measure.restrict_restrict (MeasurableSet.iUnion htm), hset]
      _ = ∑' n, ∫⁻ x in (s ∩ t n) ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
          rw [lintegral_iUnion htm hdisj]
          exact tsum_congr fun n ↦ by rw [Measure.restrict_inter_restrict _ _ _ (htm n)]
  exact (AEMeasurable.tsum hmeas).congr (Eventually.of_forall fun y ↦ (heq y).symm)

/-- Fiber measures of a map with a within-set derivative on a Lebesgue-measurable set are
almost everywhere measurable in the complementary dimension for any target Haar measure. -/
theorem aemeasurable_euclideanHausdorffMeasure_inter_preimage_of_hasFDerivWithinAt
    (hs : NullMeasurableSet s volume) {f' : E → E →L[ℝ] F}
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    AEMeasurable (fun y ↦ μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y})) μ := by
  simpa only [lintegral_one, Measure.restrict_apply_univ] using
    aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt μ hs hd aemeasurable_one

private theorem
    aemeasurable_restrict_euclideanHausdorffMeasure_inter_preimage_of_hasFDerivWithinAt
    (hs : NullMeasurableSet s volume) {f' : E → E →L[ℝ] F}
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (t : Set E) (ht : MeasurableSet t) :
    AEMeasurable
      (fun y ↦ (μHE[finrank ℝ E - finrank ℝ F].restrict (s ∩ f ⁻¹' {y})) t) μ := by
  simp_rw [Measure.restrict_inter_apply _ _ _ ht]
  exact aemeasurable_euclideanHausdorffMeasure_inter_preimage_of_hasFDerivWithinAt μ
    (hs.inter ht.nullMeasurableSet) fun x hx ↦ (hd x hx.1).mono inter_subset_left

/-- Bochner fiber integrals of an almost-everywhere strongly measurable function along a map with a
within-set derivative on a Lebesgue-measurable set are almost everywhere strongly measurable.
Neither surjectivity of the derivative nor integrability of `g` is required. -/
theorem aestronglyMeasurable_setIntegral_fiber_of_hasFDerivWithinAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hs : NullMeasurableSet s volume) {f' : E → E →L[ℝ] F}
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    {g : E → V} (hg : AEStronglyMeasurable g (volume.restrict s)) :
    AEStronglyMeasurable (fun y ↦ ∫ x in s ∩ f ⁻¹' {y}, g x
      ∂μHE[finrank ℝ E - finrank ℝ F]) μ := by
  refine (hg.stronglyMeasurable_mk.aestronglyMeasurable_integral_of_aemeasurable_measure
    (aemeasurable_restrict_euclideanHausdorffMeasure_inter_preimage_of_hasFDerivWithinAt μ hs
      hd)).congr ?_
  filter_upwards [ae_ae_eq_restrict_preimage_of_hasFDerivWithinAt μ hd hg.ae_eq_mk] with y hy
  exact (integral_congr_ae hy).symm

end MeasureTheory
