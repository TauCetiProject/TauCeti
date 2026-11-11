/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Function.Jacobian
public import TauCeti.MeasureTheory.Function.Coarea.Eilenberg
import TauCeti.MeasureTheory.Measure.Hausdorff
import TauCeti.MeasureTheory.Measure.Regular
import TauCeti.Topology.EMetricSpace.Lipschitz

/-!
# Measurability of the fiber measures of a map

The coarea formula integrates the Hausdorff measures `y ↦ μH[t] (A ∩ f ⁻¹' {y})` of the fibers of
a map `f`. This file shows that this integrand is measurable, so that the formula is an identity
between genuine integrals, and so that it can be summed over a countable partition of `A`.

Fiber measures on compact and σ-compact sets (and on sets σ-compact up to a fiberwise-null
remainder) are measurable by `IsCompact.measurable_hausdorffMeasure_inter_preimage`,
`IsSigmaCompact.measurable_hausdorffMeasure_inter_preimage`, and
`TauCeti.aemeasurable_hausdorffMeasure_inter_preimage_of_ae_eq_zero` in
`TauCeti.MeasureTheory.Measure.Hausdorff`. This file extends them to measurable sets via
Eilenberg's inequality.

If `f` is Lipschitz (or, in a second-countable domain, locally Lipschitz) on `A` with values in a
finite-dimensional real normed space with additive Haar measure `μ`, and `A` is σ-compact up to a
`μH[m + t]`-null set, where `m` is the dimension of the target, then
`y ↦ μH[t] (A ∩ f ⁻¹' {y})` is `μ`-almost everywhere measurable: the fibers of the null part are
null for almost every `y` by Eilenberg's inequality. In particular this holds for any map locally
Lipschitz on a Lebesgue measurable subset `A` of a finite-dimensional real inner product space of
dimension `n` and the normalized Hausdorff measures `μHE[k]` with `n ≤ m + k`, which include the
coarea dimension `k = n - m`.

We extend the complementary-dimensional result to maps with within-set derivatives using
Mathlib's countable partition into Lipschitz pieces. Measurable-function induction then gives
almost-everywhere measurability of weighted fiber integrals. Neither surjectivity of the
derivative nor integrability of the weight is required.

## Main declarations

* `LipschitzOnWith.aemeasurable_hausdorffMeasure_inter_preimage`,
  `LocallyLipschitzOn.aemeasurable_hausdorffMeasure_inter_preimage`: fiber measures of a Lipschitz
  (or, on a second-countable domain, locally Lipschitz) map are almost everywhere measurable on a
  set that is σ-compact up to a null set.
* `LocallyLipschitzOn.aemeasurable_euclideanHausdorffMeasure_inter_preimage`: the normalized fiber
  measures `μHE[k]` of a map locally Lipschitz on a Lebesgue measurable subset of an
  `n`-dimensional real inner product space into an `m`-dimensional real normed space are almost
  everywhere measurable when `n ≤ m + k`.
* `MeasureTheory.aemeasurable_euclideanHausdorffMeasure_inter_preimage_of_hasFDerivWithinAt`,
  `MeasureTheory.aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt`: almost-everywhere
  measurability of complementary-dimensional fiber measures and weighted fiber integrals for maps
  with within-set derivatives.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4.1 (measurability of the fiber measures in the coarea formula).
-/

public section

open MeasureTheory Measure Set Filter Module
open scoped ENNReal NNReal

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

section FiberMeasurability

variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y]
  [BorelSpace Y] (μ : Measure Y) [μ.IsAddHaarMeasure] {K : ℝ≥0} {t : ℝ}

/-- **Fiber measures of a Lipschitz map are almost everywhere measurable.** Let `f` be Lipschitz
on `A`, with values in an `m`-dimensional real normed space with additive Haar measure `μ`, and
let `t` be real. If `A` contains a σ-compact set `S` with `μH[m + t] (A \ S) = 0`, then
`y ↦ μH[t] (A ∩ f ⁻¹' {y})` is `μ`-almost everywhere measurable. -/
theorem LipschitzOnWith.aemeasurable_hausdorffMeasure_inter_preimage {f : X → Y} {A S : Set X}
    (hf : LipschitzOnWith K f A) (hSA : S ⊆ A) (hS : IsSigmaCompact S)
    (hAS : μH[finrank ℝ Y + t] (A \ S) = 0) :
    AEMeasurable (fun y ↦ μH[t] (A ∩ f ⁻¹' {y})) μ :=
  TauCeti.aemeasurable_hausdorffMeasure_inter_preimage_of_ae_eq_zero hSA hS
    (hf.continuousOn.mono hSA)
    ((hf.mono sdiff_subset).ae_hausdorffMeasure_inter_preimage_eq_zero μ hAS)

/-- **Fiber measures of a locally Lipschitz map on a second-countable domain are almost everywhere
measurable.** Let `f` be locally Lipschitz on `A`, with values in an `m`-dimensional real normed
space with additive Haar measure `μ`, and let `t` be real. If `A` contains a σ-compact set `S` with
`μH[m + t] (A \ S) = 0`, then `y ↦ μH[t] (A ∩ f ⁻¹' {y})` is `μ`-almost everywhere measurable.
Unlike `LipschitzOnWith.aemeasurable_hausdorffMeasure_inter_preimage`, this assumes
`[SecondCountableTopology X]` to cover `A \ S` by countably many Lipschitz pieces. -/
theorem LocallyLipschitzOn.aemeasurable_hausdorffMeasure_inter_preimage
    [SecondCountableTopology X] {f : X → Y} {A S : Set X}
    (hf : LocallyLipschitzOn A f) (hSA : S ⊆ A) (hS : IsSigmaCompact S)
    (hAS : μH[finrank ℝ Y + t] (A \ S) = 0) :
    AEMeasurable (fun y ↦ μH[t] (A ∩ f ⁻¹' {y})) μ :=
  TauCeti.aemeasurable_hausdorffMeasure_inter_preimage_of_ae_eq_zero hSA hS
    (hf.continuousOn.mono hSA)
    ((hf.mono sdiff_subset).ae_hausdorffMeasure_inter_preimage_eq_zero μ hAS)

/-- **Normalized fiber measures of a locally Lipschitz map on a Lebesgue measurable set are almost
everywhere measurable.** Let `f` be locally Lipschitz on a Lebesgue measurable subset `A` of an
`n`-dimensional real inner product space, with values in an `m`-dimensional real normed space
with additive Haar measure `μ`. If `n ≤ m + k`, then `y ↦ μHE[k] (A ∩ f ⁻¹' {y})` is
`μ`-almost everywhere measurable. Neither openness of `A` nor a global Lipschitz bound is needed.
This applies to the coarea dimension `k = n - m`, for which `n ≤ m + k` is `le_add_tsub`. -/
theorem LocallyLipschitzOn.aemeasurable_euclideanHausdorffMeasure_inter_preimage {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {f : E → Y} {A : Set E} (hf : LocallyLipschitzOn A f)
    (hA : NullMeasurableSet A) {k : ℕ} (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ μHE[k] (A ∩ f ⁻¹' {y})) μ := by
  obtain ⟨S, hSA, hS, hSA'⟩ := hA.exists_isSigmaCompact_subset_ae_eq
  -- The null part `A \ S` is null for the `n`-dimensional, hence the `(m + k)`-dimensional,
  -- Hausdorff measure.
  have hnull : μH[finrank ℝ Y + (k : ℝ)] (A \ S) = 0 :=
    TauCeti.hausdorffMeasure_eq_zero_of_volume_eq_zero (ae_eq_set.1 hSA').2 (by exact_mod_cast hk)
  simp only [euclideanHausdorffMeasure_def, _root_.smul_apply]
  exact (hf.aemeasurable_hausdorffMeasure_inter_preimage μ hSA hS hnull).const_smul _

end FiberMeasurability

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {f : E → F} {s : Set E}
  (μ : Measure F) [μ.IsAddHaarMeasure]

/-- Fiber measures of a map with a within-set derivative on a Lebesgue-measurable set are
almost everywhere measurable in the complementary dimension for any target Haar measure. -/
theorem aemeasurable_euclideanHausdorffMeasure_inter_preimage_of_hasFDerivWithinAt
    (hs : NullMeasurableSet s volume) {f' : E → E →L[ℝ] F}
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    AEMeasurable (fun y ↦ μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y})) μ := by
  obtain ⟨t, A, hdisj, htm, hcover, happrox, -⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hd
      (fun _ ↦ 1) fun _ ↦ one_ne_zero
  have hmeas (n : ℕ) : AEMeasurable
      (fun y ↦ μHE[finrank ℝ E - finrank ℝ F] ((s ∩ t n) ∩ f ⁻¹' {y})) μ := by
    have hlip := lipschitzOnWith_iff_restrict.2 (happrox n).lipschitzWith
    exact hlip.locallyLipschitzOn.aemeasurable_euclideanHausdorffMeasure_inter_preimage μ
      (hs.inter (htm n).nullMeasurableSet) le_add_tsub
  have heq (y : F) : μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) =
      ∑' n, μHE[finrank ℝ E - finrank ℝ F] ((s ∩ t n) ∩ f ⁻¹' {y}) := by
    have hset : (⋃ n, t n) ∩ (s ∩ f ⁻¹' {y}) = s ∩ f ⁻¹' {y} :=
      inter_eq_right.mpr (inter_subset_left.trans hcover)
    calc
      μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) =
          ((μHE[finrank ℝ E - finrank ℝ F]).restrict (s ∩ f ⁻¹' {y})) (⋃ n, t n) := by
        rw [Measure.restrict_apply (MeasurableSet.iUnion htm), hset]
      _ = ∑' n, μHE[finrank ℝ E - finrank ℝ F] ((s ∩ t n) ∩ f ⁻¹' {y}) := by
        rw [measure_iUnion hdisj htm]
        apply tsum_congr
        intro n
        rw [Measure.restrict_apply (htm n)]
        congr 1
        ac_rfl
  exact (AEMeasurable.tsum hmeas).congr (Eventually.of_forall fun y ↦ (heq y).symm)

/-- Weighted fiber integrals of a map with a within-set derivative on a Lebesgue-measurable
set are almost everywhere measurable. No full-rank or integrability hypothesis is required. -/
theorem aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt
    (hs : NullMeasurableSet s volume) {f' : E → E →L[ℝ] F}
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    AEMeasurable (fun y ↦ ∫⁻ x in s ∩ f ⁻¹' {y}, g x
      ∂μHE[finrank ℝ E - finrank ℝ F]) μ := by
  refine Measurable.ennreal_induction ?_ ?_ ?_ hg
  · intro c t ht
    simp_rw [lintegral_indicator ht, Measure.restrict_restrict ht, lintegral_const,
      Measure.restrict_apply_univ]
    have hset (y : F) : t ∩ (s ∩ f ⁻¹' {y}) = (s ∩ t) ∩ f ⁻¹' {y} := by ac_rfl
    simp_rw [hset]
    exact (aemeasurable_euclideanHausdorffMeasure_inter_preimage_of_hasFDerivWithinAt μ
      (hs.inter ht.nullMeasurableSet)
      (fun x hx ↦ (hd x hx.1).mono inter_subset_left)).const_mul c
  · intro g h hdisj hg hh ihg ihh
    simp_rw [Pi.add_apply, lintegral_add_left hg]
    exact ihg.add ihh
  · intro g hg hmono ih
    have heq (y : F) : (∫⁻ x in s ∩ f ⁻¹' {y}, ⨆ n, _ ∂μHE[finrank ℝ E - finrank ℝ F]) =
        ⨆ n, ∫⁻ x in s ∩ f ⁻¹' {y}, _ ∂μHE[finrank ℝ E - finrank ℝ F] :=
      lintegral_iSup hg hmono
    simp_rw [heq]
    exact AEMeasurable.iSup ih

end MeasureTheory
