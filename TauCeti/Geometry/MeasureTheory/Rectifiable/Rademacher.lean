/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.TangentialFDeriv
import TauCeti.Geometry.MeasureTheory.Rectifiable.Bilipschitz
import TauCeti.Geometry.MeasureTheory.Rectifiable.Density
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz
import TauCeti.Topology.EMetricSpace.Lipschitz

/-!
# Rademacher's theorem and measurability for tangential derivatives on rectifiable sets

On a null-measurable, countably `k`-rectifiable subset `E` of a finite-dimensional real inner
product space `V` with locally finite `μHE[k]` measure, every map `g : V → W` into a
finite-dimensional real normed space `W` that is locally Lipschitz on `E` is tangentially
differentiable `μHE[k]`-almost everywhere on `E`, with `μHE[k].restrict E`-almost everywhere
measurable tangential derivative and tangential Jacobian.

When `g` is `K`-Lipschitz on `E`, we first extend `g|_E` to a globally Lipschitz map `gExt : V → W`
via `LipschitzOnWith.extend_finite_dimension`, cover `E` up to a `μHE[k]`-null set by pairwise
disjoint Borel bi-Lipschitz patches `f n '' B n ⊆ E`, and apply Euclidean Rademacher's theorem to
both `f n` and `gExt ∘ f n` together with Besicovitch Lebesgue density on `B n` and zero `k`-density
of `E \ f n '' B n` on `f n '' B n`. The parametrization chain rule in
`TauCeti.Geometry.MeasureTheory.Rectifiable.TangentialFDeriv` then gives both almost-everywhere
tangential differentiability, the sharp bounds `‖tangentialFDeriv k E g x‖ ≤ K` and
`tangentialJacobian k E g x ≤ K ^ k`, and `μHE[k].restrict E`-a.e. measurability. Covering `E` by
countably many open sets (`LocallyLipschitzOn.exists_open_cover_lipschitzOnWith`) extends
differentiability and measurability to `LocallyLipschitzOn E g`.

## Main results

* `TauCeti.ae_regular_and_density_on_patch`: on any Borel bi-Lipschitz patch `f '' B ⊆ E`,
  `volume`-almost every parameter `u ∈ B` is a Lebesgue density-one regular point whose image has
  `(E \ f '' B)`-density zero.
* `LipschitzOnWith.ae_hasTangentialFDerivAt_and_norm_le`,
  `LipschitzOnWith.ae_hasTangentialFDerivAt`, `LipschitzOnWith.ae_norm_tangentialFDeriv_le`,
  `LipschitzOnWith.ae_tangentialJacobian_le`, `LipschitzOnWith.aemeasurable_tangentialFDeriv`,
  `LipschitzOnWith.aemeasurable_tangentialJacobian`.
* `LocallyLipschitzOn.ae_hasTangentialFDerivAt`,
  `LocallyLipschitzOn.aemeasurable_tangentialFDeriv`,
  `LocallyLipschitzOn.aemeasurable_tangentialJacobian`, together with `LipschitzWith` and
  `LocallyLipschitz` specializations.

## References

* H. Federer, *Geometric Measure Theory*, 3.2.19.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 2.90.
-/

public section

open Filter Function Metric MeasureTheory Measure Module Set
open scoped ENNReal NNReal Topology symmDiff

namespace TauCeti

/-- `Ring.inverse` on the Banach algebra `U →L[ℝ] U` (for finite-dimensional `U`) is Borel
measurable. -/
private lemma measurable_ringInverse_clm {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] :
    Measurable (@Ring.inverse (U →L[ℝ] U) _) := by
  classical
  have hopen : IsOpen {G : U →L[ℝ] U | IsUnit G} := Units.isOpen
  have hcont : ContinuousOn (@Ring.inverse (U →L[ℝ] U) _) {G | IsUnit G} :=
    (differentiableOn_inverse (𝕜 := ℝ) (R := U →L[ℝ] U)).continuousOn
  have hpiece : ({G : U →L[ℝ] U | IsUnit G}.piecewise (@Ring.inverse (U →L[ℝ] U) _) 0) =
      @Ring.inverse (U →L[ℝ] U) _ := by
    ext G
    by_cases hG : IsUnit G <;> simp [Set.piecewise, hG, Ring.inverse_non_unit]
  rw [← hpiece]
  exact hcont.measurable_piecewise continuousOn_const hopen.measurableSet

/-- On a Borel bi-Lipschitz patch `f '' B ⊆ E` of a null-measurable set `E` with locally finite
`μHE[k]` measure, `volume`-almost every parameter `u ∈ B` is a Lebesgue density-one regular point
whose image `f u` has `(E \ f '' B)`-density zero. -/
theorem ae_regular_and_density_on_patch {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {k : ℕ} {E : Set V} (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    {B : Set (EuclideanSpace ℝ (Fin k))} {f : EuclideanSpace ℝ (Fin k) → V} {K_f L_f : ℝ≥0}
    (hBm : MeasurableSet B) (hf_lip : LipschitzWith K_f f)
    (hf_anti : AntilipschitzWith L_f (B.domRestrict f)) :
    ∀ᵐ u ∂volume, u ∈ B →
      DifferentiableAt ℝ f u ∧ Injective (fderiv ℝ f u) ∧
      Tendsto (fun r => volume (B ∩ closedBall u r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun r => μHE[k] ((E \ f '' B) ∩ closedBall (f u) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
  have hTm : MeasurableSet (f '' B) :=
    hBm.image_of_continuousOn_injOn hf_lip.continuous.continuousOn
      (injOn_iff_injective.mpr hf_anti.injective)
  have : IsLocallyFiniteMeasure (μHE[k].restrict (E \ f '' B)) := by
    rw [Set.sdiff_eq, inter_comm, ← Measure.restrict_restrict hTm.compl]
    infer_instance
  have hzero_target :=
    ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div_of_isLocallyFiniteMeasure k
      (hEm.diff hTm.nullMeasurableSet)
  let badT := {u ∈ B | ¬ Tendsto (fun r =>
      μHE[k] ((E \ f '' B) ∩ closedBall (f u) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)}
  have hbadT_vol : volume badT = 0 := by
    have himg0 : μHE[k] (f '' badT) = 0 := by
      refine measure_mono_null ?_ (ae_iff.mp hzero_target)
      rintro _ ⟨u, ⟨huB, hnot⟩, rfl⟩
      exact fun h => hnot (h fun hmem => hmem.2 (mem_image_of_mem f huB))
    have hle := volume_le_mul_euclideanHausdorffMeasure_image_of_antilipschitzWith hf_anti
      (fun _ hu => hu.1 : badT ⊆ B)
    simpa only [finrank_euclideanSpace_fin, himg0, mul_zero, nonpos_iff_eq_zero] using hle
  let S := {u | ¬ Tendsto (fun r => volume (B ∩ closedBall u r) /
    volume (closedBall u r)) (𝓝[>] 0) (𝓝 1)}
  have hS_vol : volume (S ∩ B) = 0 :=
    nonpos_iff_eq_zero.mp ((le_restrict_apply B S).trans_eq
      (ae_iff.mp (Besicovitch.ae_tendsto_measure_inter_div volume B)))
  let badJ := {u ∈ B | (fderiv ℝ f u).toLinearMap.normDet = 0}
  have hbadJ_vol : volume badJ = 0 := by
    have himg0 : μHE[k] (f '' badJ) = 0 := by
      refine measure_mono_null ?_
        (by simpa only [finrank_euclideanSpace_fin] using
          hf_lip.euclideanHausdorffMeasure_image_setOf_normDet_fderiv_eq_zero)
      rintro _ ⟨u, ⟨_, h0⟩, rfl⟩
      exact ⟨u, h0, rfl⟩
    have hle := volume_le_mul_euclideanHausdorffMeasure_image_of_antilipschitzWith hf_anti
      (fun _ hu => hu.1 : badJ ⊆ B)
    simpa only [finrank_euclideanSpace_fin, himg0, mul_zero, nonpos_iff_eq_zero] using hle
  filter_upwards [hf_lip.ae_differentiableAt, measure_eq_zero_iff_ae_notMem.mp hbadJ_vol,
    measure_eq_zero_iff_ae_notMem.mp hS_vol,
    measure_eq_zero_iff_ae_notMem.mp hbadT_vol] with u hdiff hJ hD hT huB
  have hnorm_ne : (fderiv ℝ f u).toLinearMap.normDet ≠ 0 := fun h0 => hJ ⟨huB, h0⟩
  have hdens : Tendsto (fun r => volume (B ∩ closedBall u r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [addHaar_closedBall_center] using (not_not.mp fun h => hD ⟨h, huB⟩)
  exact ⟨hdiff, ((fderiv ℝ f u).toLinearMap.normDet_ne_zero_tfae.out 1 5).mp hnorm_ne,
    hdens, not_not.mp fun h => hT ⟨huB, h⟩⟩

end TauCeti

namespace LipschitzOnWith

open TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {k : ℕ} {E : Set V} {g : V → W} {K : ℝ≥0}

section NormedTarget

variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- Shared patch-level helper: for a Lipschitz extension `gExt` agreeing with `g` on `E` and a Borel
bi-Lipschitz patch `f '' B ⊆ E`, `μHE[k]`-almost every `x ∈ f '' B` is the image of a regular
density-one parameter `u ∈ B` where `HasTangentialFDerivAt` holds with explicit formula and norm
bound `≤ K`. -/
private lemma ae_patch_tangential (hg : LipschitzOnWith K g E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    {gExt : V → W} {KExt : ℝ≥0} (hgExt_lip : LipschitzWith KExt gExt) (hgExt_eq : EqOn g gExt E)
    {B : Set (EuclideanSpace ℝ (Fin k))} {f : EuclideanSpace ℝ (Fin k) → V}
    {K_f L_f : ℝ≥0} (hBm : MeasurableSet B) (hf_lip : LipschitzWith K_f f)
    (hf_anti : AntilipschitzWith L_f (B.domRestrict f)) (hsub : f '' B ⊆ E) :
    ∀ᵐ x ∂μHE[k], x ∈ f '' B → ∃ u ∈ B, f u = x ∧
      Injective (fderiv ℝ f u) ∧
      HasFDerivWithinAt f (fderiv ℝ f u) B u ∧
      HasFDerivWithinAt (g ∘ f) (fderiv ℝ (gExt ∘ f) u) B u ∧
      HasTangentialFDerivAt k E g
        (fderiv ℝ (gExt ∘ f) u ∘L
          Ring.inverse ((fderiv ℝ f u).adjoint ∘L fderiv ℝ f u) ∘L (fderiv ℝ f u).adjoint)
        (f u) ∧
      ‖tangentialFDeriv k E g (f u)‖ ≤ K ∧
      Tendsto (fun r => volume (B ∩ closedBall u r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun r => μHE[k] ((E \ f '' B) ∩ closedBall (f u) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
  let U := EuclideanSpace ℝ (Fin k)
  have hae_u := (ae_regular_and_density_on_patch hEm hBm hf_lip hf_anti).and
    (hgExt_lip.comp hf_lip).ae_differentiableAt
  let badU := {u ∈ B | ¬ ((DifferentiableAt ℝ f u ∧ Injective (fderiv ℝ f u) ∧
    Tendsto (fun r => volume (B ∩ closedBall u r) /
      volume (closedBall (0 : U) r)) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun r => μHE[k] ((E \ f '' B) ∩ closedBall (f u) r) /
      volume (closedBall (0 : U) r)) (𝓝[>] 0) (𝓝 0)) ∧
    DifferentiableAt ℝ (gExt ∘ f) u)}
  have hbadU_vol : volume badU = 0 := by
    refine measure_mono_null ?_ (ae_iff.mp hae_u)
    exact fun u ⟨huB, hnot⟩ h => hnot ⟨h.1 huB, h.2⟩
  have hbadU_img : μHE[k] (f '' badU) = 0 := by
    have hle := hf_lip.lipschitzOnWith.euclideanHausdorffMeasure_image_le k (s := badU)
    simpa only [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hbadU_vol, mul_zero,
      nonpos_iff_eq_zero] using hle
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hbadU_img] with x hx_good
  rintro ⟨u, huB, rfl⟩
  obtain ⟨⟨hf_diff, hinj, hdens, hdiff⟩, hgf_diff⟩ :=
    not_not.mp fun h => hx_good ⟨u, ⟨huB, h⟩, rfl⟩
  have hgf_within : HasFDerivWithinAt (g ∘ f) (fderiv ℝ (gExt ∘ f) u) B u :=
    hgf_diff.hasFDerivAt.hasFDerivWithinAt.congr
      (fun v hv => hgExt_eq (hsub (mem_image_of_mem f hv)))
      (hgExt_eq (hsub (mem_image_of_mem f huB)))
  have hdiff' : Tendsto (fun r =>
      μHE[finrank ℝ U] ((E \ f '' B) ∩ closedBall (f u) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [U, finrank_euclideanSpace_fin,
      ← volume_closedBall_eq_euclidean (0 : EuclideanSpace ℝ (Fin k))] using hdiff
  have htan := hf_diff.hasFDerivAt.hasFDerivWithinAt.hasTangentialFDerivAt_of_comp hinj
    hf_anti huB hsub hdens hdiff' hgf_within
  have hnorm := hf_diff.hasFDerivAt.hasFDerivWithinAt.norm_tangentialFDeriv_le_of_lipschitzOnWith
    hinj hf_anti huB hsub hdens hdiff' hgf_within hg
  exact ⟨u, huB, rfl, hinj, hf_diff.hasFDerivAt.hasFDerivWithinAt, hgf_within,
    by simpa only [U, finrank_euclideanSpace_fin] using htan,
    by simpa only [U, finrank_euclideanSpace_fin] using hnorm, hdens, hdiff⟩

/-- **Tangential Rademacher theorem for `LipschitzOnWith`.** On a null-measurable, countably
`k`-rectifiable set `E` with locally finite `μHE[k]` measure, every `K`-Lipschitz map `g : V → W`
on `E` into a finite-dimensional real normed space `W` is tangentially differentiable with
`‖tangentialFDeriv k E g x‖ ≤ K` at `μHE[k]`-almost every `x ∈ E`. -/
theorem ae_hasTangentialFDerivAt_and_norm_le (hg : LipschitzOnWith K g E)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E →
      HasTangentialFDerivAt k E g (tangentialFDeriv k E g x) x ∧
        ‖tangentialFDeriv k E g x‖ ≤ K := by
  obtain ⟨gExt, hgExt_lip, hgExt_eq⟩ := hg.extend_finite_dimension
  obtain ⟨B, f, K_f, L_f, hBm, _, hbi, _, hsubE, hcover_ae⟩ :=
    hE.exists_disjoint_measurable_bilipschitz_cover hEm
  have hpatch (n : ℕ) := hg.ae_patch_tangential hEm hgExt_lip hgExt_eq (hBm n) (hbi n).1 (hbi n).2
    ((subset_iUnion (fun m => f m '' B m) n).trans hsubE)
  have hnull : μHE[k] (E \ ⋃ n, f n '' B n) = 0 :=
    measure_mono_null (fun _ ⟨hxE, hxU⟩ => Or.inr ⟨hxE, hxU⟩)
      (measure_symmDiff_eq_zero_iff.mpr hcover_ae)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull, ae_all_iff.mpr hpatch] with x hcov hp hxE
  obtain ⟨n, hxn⟩ := mem_iUnion.mp (not_not.mp fun h => hcov ⟨hxE, h⟩)
  obtain ⟨u, _, rfl, _, _, _, htan, hnorm, _, _⟩ := hp n hxn
  exact ⟨hasTangentialFDerivAt_tangentialFDeriv ⟨_, htan⟩, hnorm⟩

/-- Almost-everywhere approximate tangential differentiability for `LipschitzOnWith`. -/
theorem ae_hasTangentialFDerivAt (hg : LipschitzOnWith K g E)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → HasTangentialFDerivAt k E g (tangentialFDeriv k E g x) x :=
  (hg.ae_hasTangentialFDerivAt_and_norm_le hE hEm).mono fun _ hx hxE => (hx hxE).1

/-- Almost-everywhere sharp bound `‖tangentialFDeriv k E g x‖ ≤ K` on a countably
`k`-rectifiable set `E`. -/
theorem ae_norm_tangentialFDeriv_le (hg : LipschitzOnWith K g E)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → ‖tangentialFDeriv k E g x‖ ≤ K :=
  (hg.ae_hasTangentialFDerivAt_and_norm_le hE hEm).mono fun _ hx hxE => (hx hxE).2

/-- **Measurability of `tangentialFDeriv` for `LipschitzOnWith`.** -/
theorem aemeasurable_tangentialFDeriv (hg : LipschitzOnWith K g E)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    AEMeasurable (tangentialFDeriv k E g) (μHE[k].restrict E) := by
  obtain ⟨gExt, hgExt_lip, hgExt_eq⟩ := hg.extend_finite_dimension
  obtain ⟨B, f, K_f, L_f, hBm, hTm, hbi, _, hsubE, hcover_ae⟩ :=
    hE.exists_disjoint_measurable_bilipschitz_cover hEm
  rw [← Measure.restrict_congr_set hcover_ae]
  refine AEMeasurable.iUnion fun n => ?_
  let U := EuclideanSpace ℝ (Fin k)
  have he : MeasurableEmbedding ((B n).domRestrict (f n)) :=
    (hbi n).1.continuous.continuousOn.measurableEmbedding (hBm n)
      (injOn_iff_injective.mpr (hbi n).2.injective)
  let M : U → V →L[ℝ] W := fun u => fderiv ℝ (gExt ∘ f n) u ∘L
    Ring.inverse ((fderiv ℝ (f n) u).adjoint ∘L fderiv ℝ (f n) u) ∘L
    (fderiv ℝ (f n) u).adjoint
  have hMm : Measurable M := by
    have hm_f := measurable_fderiv ℝ (f n)
    have hm_adj : Measurable fun u : U => (fderiv ℝ (f n) u).adjoint :=
      ContinuousLinearMap.adjoint.continuous.measurable.comp hm_f
    have hm_inv : Measurable fun u : U =>
        Ring.inverse ((fderiv ℝ (f n) u).adjoint ∘L fderiv ℝ (f n) u) :=
      measurable_ringInverse_clm.comp
        ((continuous_fst.clm_comp continuous_snd).measurable.comp (hm_adj.prodMk hm_f))
    exact (continuous_fst.clm_comp continuous_snd).measurable.comp
      ((measurable_fderiv ℝ (gExt ∘ f n)).prodMk
        ((continuous_fst.clm_comp continuous_snd).measurable.comp (hm_inv.prodMk hm_adj)))
  obtain ⟨Φ, hΦm, hΦ⟩ := he.exists_measurable_extend (g := fun u : B n => M u)
    (hMm.comp measurable_subtype_coe) (fun _ => ⟨0⟩)
  refine hΦm.aemeasurable.congr ?_
  rw [EventuallyEq, ae_restrict_iff' (hTm n)]
  filter_upwards [hg.ae_patch_tangential hEm hgExt_lip hgExt_eq (hBm n) (hbi n).1 (hbi n).2
    ((subset_iUnion (fun m => f m '' B m) n).trans hsubE)] with x hx hxB
  obtain ⟨u, huB, rfl, _, _, _, htan, _, _, _⟩ := hx hxB
  exact (congrFun hΦ ⟨u, huB⟩).trans htan.tangentialFDeriv_eq.symm

end NormedTarget

section InnerProductTarget

variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- Almost-everywhere sharp bound `tangentialJacobian k E g x ≤ K ^ k` on a countably
`k`-rectifiable set `E`. -/
theorem ae_tangentialJacobian_le (hg : LipschitzOnWith K g E)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → tangentialJacobian k E g x ≤ (K : ℝ) ^ k := by
  filter_upwards [hg.ae_hasTangentialFDerivAt_and_norm_le hE hEm] with x hx hxE
  obtain ⟨htan, hnorm⟩ := hx hxE
  exact htan.tangentialJacobian_le_opNorm_pow.trans (pow_le_pow_left₀ (norm_nonneg _) hnorm _)

/-- **Measurability of `tangentialJacobian` for `LipschitzOnWith`.** -/
theorem aemeasurable_tangentialJacobian (hg : LipschitzOnWith K g E)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    AEMeasurable (tangentialJacobian k E g) (μHE[k].restrict E) := by
  obtain ⟨gExt, hgExt_lip, hgExt_eq⟩ := hg.extend_finite_dimension
  obtain ⟨B, f, K_f, L_f, hBm, hTm, hbi, _, hsubE, hcover_ae⟩ :=
    hE.exists_disjoint_measurable_bilipschitz_cover hEm
  rw [← Measure.restrict_congr_set hcover_ae]
  refine AEMeasurable.iUnion fun n => ?_
  let U := EuclideanSpace ℝ (Fin k)
  have he : MeasurableEmbedding ((B n).domRestrict (f n)) :=
    (hbi n).1.continuous.continuousOn.measurableEmbedding (hBm n)
      (injOn_iff_injective.mpr (hbi n).2.injective)
  let J : U → ℝ := fun u =>
    (fderiv ℝ (gExt ∘ f n) u).toLinearMap.normDet / (fderiv ℝ (f n) u).toLinearMap.normDet
  have hJm : Measurable J :=
    (ContinuousLinearMap.continuous_normDet.measurable.comp
      (measurable_fderiv ℝ (gExt ∘ f n))).div
      (ContinuousLinearMap.continuous_normDet.measurable.comp (measurable_fderiv ℝ (f n)))
  obtain ⟨Ψ, hΨm, hΨ⟩ := he.exists_measurable_extend (g := fun u : B n => J u)
    (hJm.comp measurable_subtype_coe) (fun _ => ⟨0⟩)
  refine hΨm.aemeasurable.congr ?_
  have hsub_n := (subset_iUnion (fun m => f m '' B m) n).trans hsubE
  rw [EventuallyEq, ae_restrict_iff' (hTm n)]
  filter_upwards [hg.ae_patch_tangential hEm hgExt_lip hgExt_eq (hBm n) (hbi n).1 (hbi n).2
    hsub_n] with x hx hxB
  obtain ⟨u, huB, rfl, hinj, hf_w, hgf_w, _, _, hdens, hdiff⟩ := hx hxB
  have hdiff' : Tendsto (fun r =>
      μHE[finrank ℝ U] ((E \ f n '' B n) ∩ closedBall (f n u) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [U, finrank_euclideanSpace_fin,
      ← volume_closedBall_eq_euclidean (0 : EuclideanSpace ℝ (Fin k))] using hdiff
  have hmul : tangentialJacobian k E g (f n u) * (fderiv ℝ (f n) u).toLinearMap.normDet =
      (fderiv ℝ (gExt ∘ f n) u).toLinearMap.normDet := by
    simpa only [U, finrank_euclideanSpace_fin] using
      hf_w.tangentialJacobian_mul_normDet hinj (hbi n).2 huB hsub_n hdens hdiff' hgf_w
  have hdet_ne := ((fderiv ℝ (f n) u).toLinearMap.normDet_ne_zero_tfae.out 5 1).mp hinj
  exact (congrFun hΨ ⟨u, huB⟩).trans (eq_div_of_mul_eq hdet_ne hmul).symm

end InnerProductTarget

end LipschitzOnWith

namespace LocallyLipschitzOn

open TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {k : ℕ} {E : Set V} {g : V → W}

/-- **Tangential Rademacher theorem for `LocallyLipschitzOn`.** Every map locally Lipschitz on a
null-measurable, countably `k`-rectifiable set `E` with locally finite `μHE[k]` measure into a
finite-dimensional real normed space `W` is tangentially differentiable `μHE[k]`-almost everywhere
on `E`. -/
theorem ae_hasTangentialFDerivAt [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → HasTangentialFDerivAt k E g (tangentialFDeriv k E g x) x := by
  obtain ⟨O, K, hO, hcov, hLip⟩ := hg.exists_open_cover_lipschitzOnWith
  have hpiece (n : ℕ) : ∀ᵐ x ∂μHE[k], x ∈ E ∩ O n →
      HasTangentialFDerivAt k E g (tangentialFDeriv k E g x) x := by
    have : IsLocallyFiniteMeasure (μHE[k].restrict (E ∩ O n)) := by
      rw [inter_comm, ← Measure.restrict_restrict (hO n).measurableSet]
      infer_instance
    filter_upwards [(hLip n).ae_hasTangentialFDerivAt (hE.mono inter_subset_left)
      (hEm.inter (hO n).measurableSet.nullMeasurableSet)] with x hx hxEO
    have hnhds : (E ∩ O n : Set V) =ᶠ[𝓝 x] E := by
      filter_upwards [(hO n).mem_nhds hxEO.2] with z hz
      simp [hz]
    rw [← tangentialFDeriv_congr_nhds_set hnhds]
    exact (HasTangentialFDerivAt.congr_nhds_set hnhds).mp (hx hxEO)
  filter_upwards [ae_all_iff.mpr hpiece] with x hx hxE
  obtain ⟨n, hxn⟩ := mem_iUnion.mp (hcov hxE)
  exact hx n ⟨hxE, hxn⟩

/-- **Measurability of `tangentialFDeriv` for `LocallyLipschitzOn`.** -/
theorem aemeasurable_tangentialFDeriv [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    AEMeasurable (tangentialFDeriv k E g) (μHE[k].restrict E) := by
  obtain ⟨O, K, hO, hcov, hLip⟩ := hg.exists_open_cover_lipschitzOnWith
  have hE_eq : E = ⋃ n, E ∩ O n := by
    rw [← inter_iUnion, inter_eq_self_of_subset_left hcov]
  nth_rw 2 [hE_eq]
  refine AEMeasurable.iUnion fun n => ?_
  have : IsLocallyFiniteMeasure (μHE[k].restrict (E ∩ O n)) := by
    rw [inter_comm, ← Measure.restrict_restrict (hO n).measurableSet]
    infer_instance
  refine ((hLip n).aemeasurable_tangentialFDeriv (hE.mono inter_subset_left)
    (hEm.inter (hO n).measurableSet.nullMeasurableSet)).congr ?_
  rw [EventuallyEq, ae_restrict_iff'₀ (hEm.inter (hO n).measurableSet.nullMeasurableSet)]
  refine Eventually.of_forall fun x hxEO => tangentialFDeriv_congr_nhds_set ?_ g
  filter_upwards [(hO n).mem_nhds hxEO.2] with z hz
  simp [hz]

/-- **Measurability of `tangentialJacobian` for `LocallyLipschitzOn`.** -/
theorem aemeasurable_tangentialJacobian [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    AEMeasurable (tangentialJacobian k E g) (μHE[k].restrict E) := by
  obtain ⟨O, K, hO, hcov, hLip⟩ := hg.exists_open_cover_lipschitzOnWith
  have hE_eq : E = ⋃ n, E ∩ O n := by
    rw [← inter_iUnion, inter_eq_self_of_subset_left hcov]
  nth_rw 2 [hE_eq]
  refine AEMeasurable.iUnion fun n => ?_
  have : IsLocallyFiniteMeasure (μHE[k].restrict (E ∩ O n)) := by
    rw [inter_comm, ← Measure.restrict_restrict (hO n).measurableSet]
    infer_instance
  refine ((hLip n).aemeasurable_tangentialJacobian (hE.mono inter_subset_left)
    (hEm.inter (hO n).measurableSet.nullMeasurableSet)).congr ?_
  rw [EventuallyEq, ae_restrict_iff'₀ (hEm.inter (hO n).measurableSet.nullMeasurableSet)]
  refine Eventually.of_forall fun x hxEO => tangentialJacobian_congr_nhds_set ?_ g
  filter_upwards [(hO n).mem_nhds hxEO.2] with z hz
  simp [hz]

end LocallyLipschitzOn

namespace LipschitzWith

open TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E : Set V} {g : V → W} {K : ℝ≥0}

/-- Almost-everywhere approximate tangential differentiability for globally `K`-Lipschitz maps. -/
theorem ae_hasTangentialFDerivAt [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (hg : LipschitzWith K g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → HasTangentialFDerivAt k E g (tangentialFDeriv k E g x) x :=
  hg.lipschitzOnWith.ae_hasTangentialFDerivAt hE hEm

/-- Almost-everywhere sharp bound `‖tangentialFDeriv k E g x‖ ≤ K` for `K`-Lipschitz maps. -/
theorem ae_norm_tangentialFDeriv_le [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (hg : LipschitzWith K g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → ‖tangentialFDeriv k E g x‖ ≤ K :=
  hg.lipschitzOnWith.ae_norm_tangentialFDeriv_le hE hEm

/-- Almost-everywhere sharp bound `tangentialJacobian k E g x ≤ K ^ k` for `K`-Lipschitz maps. -/
theorem ae_tangentialJacobian_le [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (hg : LipschitzWith K g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → tangentialJacobian k E g x ≤ (K : ℝ) ^ k :=
  hg.lipschitzOnWith.ae_tangentialJacobian_le hE hEm

/-- Measurability of `tangentialFDeriv` for globally `K`-Lipschitz maps. -/
theorem aemeasurable_tangentialFDeriv [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (hg : LipschitzWith K g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    AEMeasurable (tangentialFDeriv k E g) (μHE[k].restrict E) :=
  hg.lipschitzOnWith.aemeasurable_tangentialFDeriv hE hEm

/-- Measurability of `tangentialJacobian` for globally `K`-Lipschitz maps. -/
theorem aemeasurable_tangentialJacobian [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (hg : LipschitzWith K g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    AEMeasurable (tangentialJacobian k E g) (μHE[k].restrict E) :=
  hg.lipschitzOnWith.aemeasurable_tangentialJacobian hE hEm

end LipschitzWith

namespace LocallyLipschitz

open TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E : Set V} {g : V → W}

/-- Almost-everywhere approximate tangential differentiability for locally Lipschitz maps. -/
theorem ae_hasTangentialFDerivAt [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (hg : LocallyLipschitz g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → HasTangentialFDerivAt k E g (tangentialFDeriv k E g x) x :=
  (hg.comp_locallyLipschitzOn (LipschitzWith.id.lipschitzOnWith.locallyLipschitzOn (s := E)))
    |>.ae_hasTangentialFDerivAt hE hEm

/-- Measurability of `tangentialFDeriv` for locally Lipschitz maps. -/
theorem aemeasurable_tangentialFDeriv [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (hg : LocallyLipschitz g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    AEMeasurable (tangentialFDeriv k E g) (μHE[k].restrict E) :=
  (hg.comp_locallyLipschitzOn (LipschitzWith.id.lipschitzOnWith.locallyLipschitzOn (s := E)))
    |>.aemeasurable_tangentialFDeriv hE hEm

/-- Measurability of `tangentialJacobian` for locally Lipschitz maps. -/
theorem aemeasurable_tangentialJacobian [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (hg : LocallyLipschitz g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    AEMeasurable (tangentialJacobian k E g) (μHE[k].restrict E) :=
  (hg.comp_locallyLipschitzOn (LipschitzWith.id.lipschitzOnWith.locallyLipschitzOn (s := E)))
    |>.aemeasurable_tangentialJacobian hE hEm

end LocallyLipschitz
