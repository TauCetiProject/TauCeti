/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.TangentialFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import TauCeti.Analysis.Calculus.TangentCone.Haar
import TauCeti.Geometry.Euclidean.Volume.Density
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
import TauCeti.Topology.EMetricSpace.Lipschitz

/-!
# Rademacher's theorem and measurability for tangential derivatives on rectifiable sets

Every locally Lipschitz map `g : V → W` into a finite-dimensional real normed space on a countably
`k`-rectifiable, `μHE[k]`-null-measurable set `E` with locally finite restricted measure
`μHE[k].restrict E` is tangentially differentiable at `μHE[k]`-almost every point of `E`, and both
`tangentialFDeriv k E g` and `tangentialJacobian k E g` are `μHE[k].restrict E`-a.e. measurable.

The proof refines a disjoint Borel bi-Lipschitz cover of `E` so that `g` extends globally as a
Lipschitz map `gExt n` on each patch
(`LocallyLipschitzOn.exists_disjoint_measurable_bilipschitz_extension_cover`). Classical
Rademacher's theorem on `EuclideanSpace ℝ (Fin k)` combined with Lebesgue density and the
patchwise chain rule (`Rectifiable.TangentialFDeriv`) then yields a.e. tangential
differentiability (hence `μHE[k].restrict E`-a.e. additivity and subtraction of `tangentialFDeriv`,
complementing unconditional `tangentialFDeriv_const_smul` and `tangentialFDeriv_neg`) and patchwise
measurable formulas (via `ContinuousLinearMap.measurable_gramLeftInverse`) enabling integration of
the tangential Jacobian in `Rectifiable.AreaFormula`. The sharp operator-norm and Jacobian bounds
`‖D x‖ ≤ K` and `J x ≤ K ^ k` for `LipschitzOnWith K g E` hold without finite-dimensionality of the
codomain `W`.

## References

* H. Federer, *Geometric Measure Theory*, 3.2.19 (Rademacher's theorem on rectifiable sets).
* L. Simon, *Lectures on Geometric Measure Theory*, §12.
-/

public section

open Filter Function Metric MeasureTheory Measure Module Set
open scoped ENNReal NNReal Topology symmDiff
local notation "ω[" d "](" r ")" => volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) r)
local notation "Euc[" d "]" => EuclideanSpace ℝ (Fin d)
namespace TauCeti
/-- Almost every parameter `u ∈ B` of a Borel bi-Lipschitz patch `f '' B ⊆ E` is a Lebesgue
density-one regular point whose image has `(E \ f '' B)`-density zero. -/
theorem ae_regular_and_density_on_patch {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E : Set V} (hEm :
    NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)] {B : Set (Euc[k])} {f :
    Euc[k] → V} {K_f L_f : ℝ≥0} (hBm : MeasurableSet B) (hf_lip : LipschitzWith K_f f) (hf_anti :
    AntilipschitzWith L_f (B.domRestrict f)) : ∀ᵐ u ∂volume, u ∈ B → DifferentiableAt ℝ f u ∧
    Injective (fderiv ℝ f u) ∧ Tendsto (fun r => volume (B ∩ closedBall u r) / ω[k](r)) (𝓝[>] 0) (𝓝
    1) ∧ Tendsto (fun r => μHE[k] ((E \ f '' B) ∩ closedBall (f u) r) / ω[k](r)) (𝓝[>] 0) (𝓝 0) :=
    by
  have hTm : MeasurableSet (f '' B) := hBm.image_of_continuousOn_injOn
    hf_lip.continuous.continuousOn (injOn_iff_injective.mpr hf_anti.injective)
  have : IsLocallyFiniteMeasure (μHE[k].restrict (E \ f '' B)) := by
    rw [Set.sdiff_eq, inter_comm, ← Measure.restrict_restrict hTm.compl]; infer_instance
  have hvol0 {S : Set (Euc[k])} (hSB : S ⊆ B) (h0 : μHE[k] (f '' S) = 0) : volume S = 0 := by
    simpa only [finrank_euclideanSpace_fin, h0, mul_zero, nonpos_iff_eq_zero] using
      volume_le_mul_euclideanHausdorffMeasure_image_of_antilipschitzWith hf_anti hSB
  have hbadT : volume {u ∈ B | ¬ Tendsto (fun r => μHE[k] ((E \ f '' B) ∩ closedBall (f u) r) /
    ω[k](r)) (𝓝[>] 0) (𝓝 0)} = 0 := hvol0 (sep_subset _ _) <| measure_mono_null
      (by rintro _ ⟨u, ⟨huB, hnot⟩, rfl⟩ h; exact hnot (h fun hm => hm.2 (mem_image_of_mem f huB)))
    (ae_iff.mp (ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div_of_isLocallyFiniteMeasure
      k (hEm.diff hTm.nullMeasurableSet)))
  have hS_vol : volume ({u | ¬ Tendsto (fun r => volume (B ∩ closedBall u r) /
    volume (closedBall u r)) (𝓝[>] 0) (𝓝 1)} ∩ B) = 0 := nonpos_iff_eq_zero.mp <|
    (le_restrict_apply B _).trans_eq (ae_iff.mp (Besicovitch.ae_tendsto_measure_inter_div volume B))
  filter_upwards [hf_lip.ae_differentiableAt,
    measure_eq_zero_iff_ae_notMem.mp hS_vol, measure_eq_zero_iff_ae_notMem.mp hbadT] with u hdiff
    hD hT huB
  have hdens1 : Tendsto (fun r => volume (B ∩ closedBall u r) / volume (closedBall u r))
      (𝓝[>] 0) (𝓝 1) := not_not.mp fun h => hD ⟨h, huB⟩
  exact ⟨hdiff,
    hdiff.hasFDerivAt.hasFDerivWithinAt.injective_of_tendsto_inter_closedBall_div volume huB
      hf_anti hdens1,
    by simpa only [addHaar_closedBall_center] using hdens1,
    not_not.mp fun h => hT ⟨huB, h⟩⟩
private lemma ae_patch_tangential {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W] {k : ℕ} {E : Set V} {g gExt : V → W}
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)] {KExt : ℝ≥0}
    (hgExt_lip : LipschitzWith KExt gExt) {B : Set (Euc[k])} {f : Euc[k] → V}
    (hgExt_eq : EqOn g gExt (f '' B)) {K_f L_f : ℝ≥0} (hBm : MeasurableSet B)
    (hf_lip : LipschitzWith K_f f) (hf_anti : AntilipschitzWith L_f (B.domRestrict f))
    (hsub : f '' B ⊆ E) :
    ∀ᵐ x ∂μHE[k], x ∈ f '' B → ∃ u ∈ B, f u = x ∧ Injective (fderiv ℝ f u) ∧
      HasFDerivWithinAt f (fderiv ℝ f u) B u ∧
      HasFDerivWithinAt (g ∘ f) (fderiv ℝ (gExt ∘ f) u) B u ∧
      HasTangentialFDerivAt k E g
        (fderiv ℝ (gExt ∘ f) u ∘L (fderiv ℝ f u).gramLeftInverse) (f u) ∧
      Tendsto (fun r => volume (B ∩ closedBall u r) / ω[k](r)) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun r => μHE[finrank ℝ (Euc[k])] ((E \ f '' B) ∩ closedBall (f u) r) /
        ω[finrank ℝ (Euc[k])](r)) (𝓝[>] 0) (𝓝 0) := by
  let U := Euc[k]
  have hae := ((ae_regular_and_density_on_patch hEm hBm hf_lip hf_anti).and
    (hgExt_lip.comp hf_lip).ae_differentiableAt).mono fun _ h (huB : _ ∈ B) =>
      And.intro (h.1 huB) h.2
  have himg :=
    (hf_lip.lipschitzOnWith (s := B)).ae_euclideanHausdorffMeasure_exists_of_addHaar volume hae
  rw [finrank_euclideanSpace_fin] at himg
  filter_upwards [himg] with x hx hxB
  obtain ⟨u, huB, rfl, ⟨hf_diff, hinj, hdens, hdiff⟩, hgf_diff⟩ := hx hxB
  have hgf_w := hgf_diff.hasFDerivAt.hasFDerivWithinAt.congr
    (fun _ hv => hgExt_eq (mem_image_of_mem f hv)) (hgExt_eq (mem_image_of_mem f huB))
  have hdiff' : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' B) ∩ closedBall (f u) r) /
      ω[finrank ℝ U](r)) (𝓝[>] 0) (𝓝 0) := by
    dsimp only [U]; rwa [finrank_euclideanSpace_fin]
  exact ⟨u, huB, rfl, hinj, hf_diff.hasFDerivAt.hasFDerivWithinAt, hgf_w,
    by simpa only [U, finrank_euclideanSpace_fin] using
      hf_diff.hasFDerivAt.hasFDerivWithinAt.hasTangentialFDerivAt_of_comp hf_anti huB hsub
        hdens hdiff' hgf_w, hdens, hdiff'⟩
end TauCeti
section RectifiableRademacher
open TauCeti
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] {k : ℕ} {E : Set V} {g : V → W}
local notation "D" => TauCeti.tangentialFDeriv k E g
local notation "J" => TauCeti.tangentialJacobian k E g
namespace LocallyLipschitzOn
variable (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k])
include hg hE hEm
private lemma aemeasurable_of_extension_cover [NormedSpace ℝ W] [FiniteDimensional ℝ W] {α : Type*}
    [MeasurableSpace α] [Nonempty α] {F : V → α} (hpatch : ∀ {B : Set (Euc[k])} {f : Euc[k] → V}
    {gExt : V → W} {K_f L_f K_g : ℝ≥0}, MeasurableSet B → LipschitzWith K_f f → AntilipschitzWith
    L_f (B.domRestrict f) → LipschitzWith K_g gExt → EqOn g gExt (f '' B) → f '' B ⊆ E → ∃ M :
    Euc[k] → α, Measurable M ∧ ∀ᵐ x ∂μHE[k], x ∈ f '' B → ∃ u ∈ B, f u = x ∧ F x = M u) :
    AEMeasurable F (μHE[k].restrict E) := by
  obtain ⟨B, f, gExt, _, _, _, hBm, hTm, hbi, hgExt, _, hsubE, hcover_ae⟩ :=
    hg.exists_disjoint_measurable_bilipschitz_extension_cover hE hEm
  rw [← Measure.restrict_congr_set hcover_ae]; refine AEMeasurable.iUnion fun n => ?_
  obtain ⟨M, hMm, hae⟩ := hpatch (hBm n) (hbi n).1 (hbi n).2 (hgExt n).1 (hgExt n).2 (hsubE n)
  obtain ⟨Φ, hΦm, hΦ⟩ := ((hbi n).1.continuous.continuousOn.measurableEmbedding (hBm n)
    (injOn_iff_injective.mpr (hbi n).2.injective)).exists_measurable_extend (g := fun u : B n => M
    u) (hMm.comp measurable_subtypeVal) (fun _ => ‹Nonempty α›)
  refine hΦm.aemeasurable.congr ((ae_restrict_iff' (hTm n)).mpr ?_)
  filter_upwards [hae] with x hx hxB
  obtain ⟨u, huB, rfl, hFM⟩ := hx hxB; exact (congrFun hΦ ⟨u, huB⟩).trans hFM.symm
variable [IsLocallyFiniteMeasure (μHE[k].restrict E)]
/-- Tangential Rademacher theorem for `LocallyLipschitzOn`. -/
theorem ae_hasTangentialFDerivAt [NormedSpace ℝ W] [FiniteDimensional ℝ W] : ∀ᵐ x ∂μHE[k], x ∈ E →
    HasTangentialFDerivAt k E g (D x) x := by
  obtain ⟨B, f, gExt, _, _, _, hBm, _, hbi, hgExt, _, hsubE, hcover_ae⟩ :=
    hg.exists_disjoint_measurable_bilipschitz_extension_cover hE hEm
  filter_upwards [hcover_ae.symm.subset, ae_all_iff.mpr fun n =>
    ae_patch_tangential hEm (hgExt n).1 (hgExt n).2 (hBm n) (hbi n).1 (hbi n).2
      (hsubE n)] with x hcov hp hxE
  obtain ⟨n, hxn⟩ := mem_iUnion.mp (hcov hxE)
  obtain ⟨_, _, rfl, _, _, _, htan, _, _⟩ := hp n hxn
  exact hasTangentialFDerivAt_tangentialFDeriv ⟨_, htan⟩
/-- Measurability of `tangentialFDeriv` for `LocallyLipschitzOn`. -/
theorem aemeasurable_tangentialFDeriv [NormedSpace ℝ W] [FiniteDimensional ℝ W] :
    AEMeasurable (D) (μHE[k].restrict E) := by
  refine aemeasurable_of_extension_cover hg hE hEm fun {_ f gExt _ _ _} hBm hf_lip hf_anti hgExt_lip
    hgExt_eq hsub => ?_
  refine ⟨fun u => fderiv ℝ (gExt ∘ f) u ∘L (fderiv ℝ f u).gramLeftInverse,
    (continuous_fst.clm_comp continuous_snd).measurable.comp
      ((measurable_fderiv ℝ (gExt ∘ f)).prodMk
        (ContinuousLinearMap.measurable_gramLeftInverse.comp (measurable_fderiv ℝ f))), ?_⟩
  filter_upwards [ae_patch_tangential hEm hgExt_lip hgExt_eq hBm hf_lip hf_anti hsub]
    with x hx hxB
  obtain ⟨u, huB, rfl, _, _, _, htan, _, _⟩ := hx hxB
  exact ⟨u, huB, rfl, htan.tangentialFDeriv_eq⟩
/-- Measurability of `tangentialJacobian` for `LocallyLipschitzOn`. -/
theorem aemeasurable_tangentialJacobian [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] :
    AEMeasurable (J) (μHE[k].restrict E) := by
  refine aemeasurable_of_extension_cover hg hE hEm fun {_ f gExt _ _ _} hBm hf_lip hf_anti hgExt_lip
    hgExt_eq hsub => ?_
  refine ⟨fun u => (fderiv ℝ (gExt ∘ f) u).toLinearMap.normDet / (fderiv ℝ f u).toLinearMap.normDet,
    (ContinuousLinearMap.continuous_normDet.measurable.comp (measurable_fderiv ℝ (gExt ∘ f))).div
    (ContinuousLinearMap.continuous_normDet.measurable.comp (measurable_fderiv ℝ f)), ?_⟩
  filter_upwards [ae_patch_tangential hEm hgExt_lip hgExt_eq hBm hf_lip hf_anti hsub] with x hx hxB
  obtain ⟨u, huB, rfl, hinj, hf_w, hgf_w, _, hdens, hdiff'⟩ := hx hxB
  refine ⟨u, huB, rfl, eq_div_of_mul_eq
    (((fderiv ℝ f u).toLinearMap.normDet_ne_zero_tfae.out 5 1).mp hinj) ?_⟩
  simpa only [finrank_euclideanSpace_fin] using
    hf_w.tangentialJacobian_mul_normDet hf_anti huB hsub hdens hdiff' hgf_w
omit hg in
/-- Almost-everywhere additivity of `tangentialFDeriv` for locally Lipschitz maps on `E`. -/
theorem tangentialFDeriv_add_ae_eq [NormedSpace ℝ W] [FiniteDimensional ℝ W] {g₁ g₂ : V → W}
    (hg₁ : LocallyLipschitzOn E g₁) (hg₂ : LocallyLipschitzOn E g₂) :
    tangentialFDeriv k E (g₁ + g₂) =ᵐ[μHE[k].restrict E]
      tangentialFDeriv k E g₁ + tangentialFDeriv k E g₂ := by
  refine (ae_restrict_iff'₀ hEm).mpr ?_
  filter_upwards [hg₁.ae_hasTangentialFDerivAt hE hEm,
    hg₂.ae_hasTangentialFDerivAt hE hEm] with x hx₁ hx₂ hxE
  exact tangentialFDeriv_add ⟨_, hx₁ hxE⟩ ⟨_, hx₂ hxE⟩
omit hg in
/-- Almost-everywhere subtraction rule for `tangentialFDeriv` of locally Lipschitz maps on `E`. -/
theorem tangentialFDeriv_sub_ae_eq [NormedSpace ℝ W] [FiniteDimensional ℝ W] {g₁ g₂ : V → W}
    (hg₁ : LocallyLipschitzOn E g₁) (hg₂ : LocallyLipschitzOn E g₂) :
    tangentialFDeriv k E (g₁ - g₂) =ᵐ[μHE[k].restrict E]
      tangentialFDeriv k E g₁ - tangentialFDeriv k E g₂ := by
  refine (ae_restrict_iff'₀ hEm).mpr ?_
  filter_upwards [hg₁.ae_hasTangentialFDerivAt hE hEm,
    hg₂.ae_hasTangentialFDerivAt hE hEm] with x hx₁ hx₂ hxE
  exact tangentialFDeriv_sub ⟨_, hx₁ hxE⟩ ⟨_, hx₂ hxE⟩
end LocallyLipschitzOn
namespace LipschitzOnWith
variable {K : ℝ≥0} (hg : LipschitzOnWith K g E) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
include hg hE hEm
/-- Almost-everywhere sharp bound `‖tangentialFDeriv k E g x‖ ≤ K` for `LipschitzOnWith` into any
real normed space `W` (without requiring `W` to be finite-dimensional). -/
theorem ae_norm_tangentialFDeriv_le [NormedSpace ℝ W] :
    ∀ᵐ x ∂μHE[k], x ∈ E → ‖D x‖ ≤ K := by
  refine hE.ae_of_forall_bilipschitz_patch hEm fun {B f _ _} hBm hsub hf_lip hf_anti => ?_
  have himg := (hf_lip.lipschitzOnWith (s := B)).ae_euclideanHausdorffMeasure_exists_of_addHaar
    volume (ae_regular_and_density_on_patch hEm hBm hf_lip hf_anti)
  rw [finrank_euclideanSpace_fin] at himg
  filter_upwards [himg] with x hx hxB
  obtain ⟨u, huB, rfl, hf_diff, -, hdens, -⟩ := hx hxB
  simpa only [finrank_euclideanSpace_fin] using
    hf_diff.hasFDerivAt.hasFDerivWithinAt.norm_tangentialFDeriv_le_of_lipschitzOnWith
      hf_anti huB hsub hdens hg
/-- Almost-everywhere tangential differentiability for `LipschitzOnWith`. -/
theorem ae_hasTangentialFDerivAt [NormedSpace ℝ W] [FiniteDimensional ℝ W] : ∀ᵐ x ∂μHE[k], x ∈ E →
    HasTangentialFDerivAt k E g (D x) x := hg.locallyLipschitzOn.ae_hasTangentialFDerivAt hE hEm
/-- Measurability of `tangentialFDeriv` for `LipschitzOnWith`. -/
theorem aemeasurable_tangentialFDeriv [NormedSpace ℝ W] [FiniteDimensional ℝ W] :
    AEMeasurable (D) (μHE[k].restrict E) :=
  hg.locallyLipschitzOn.aemeasurable_tangentialFDeriv hE hEm
/-- Almost-everywhere sharp bound `tangentialJacobian k E g x ≤ K ^ k` for `LipschitzOnWith` into
any real inner product space `W` (without requiring `W` to be finite-dimensional). -/
theorem ae_tangentialJacobian_le [InnerProductSpace ℝ W] : ∀ᵐ x ∂μHE[k],
    x ∈ E → J x ≤ (K : ℝ) ^ k :=
  (hg.ae_norm_tangentialFDeriv_le hE hEm).mono fun _ h hx =>
    (tangentialJacobian_le_norm_tangentialFDeriv_pow k E g _).trans
      (pow_le_pow_left₀ (norm_nonneg _) (h hx) _)
/-- Measurability of `tangentialJacobian` for `LipschitzOnWith`. -/
theorem aemeasurable_tangentialJacobian [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] :
    AEMeasurable (J) (μHE[k].restrict E) :=
  hg.locallyLipschitzOn.aemeasurable_tangentialJacobian hE hEm
end LipschitzOnWith
namespace LipschitzWith
variable {K : ℝ≥0} (hg : LipschitzWith K g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
include hg hE hEm
/-- Almost-everywhere tangential differentiability for `K`-Lipschitz maps. -/
theorem ae_hasTangentialFDerivAt [NormedSpace ℝ W] [FiniteDimensional ℝ W] : ∀ᵐ x ∂μHE[k], x ∈ E →
    HasTangentialFDerivAt k E g (D x) x := hg.lipschitzOnWith.ae_hasTangentialFDerivAt hE hEm
/-- Almost-everywhere sharp bound `‖tangentialFDeriv k E g x‖ ≤ K` for `K`-Lipschitz maps into any
real normed space `W`. -/
theorem ae_norm_tangentialFDeriv_le [NormedSpace ℝ W] : ∀ᵐ x ∂μHE[k],
    x ∈ E → ‖D x‖ ≤ K := hg.lipschitzOnWith.ae_norm_tangentialFDeriv_le hE hEm
/-- Almost-everywhere sharp bound `tangentialJacobian k E g x ≤ K ^ k` for `K`-Lipschitz maps into
any real inner product space `W`. -/
theorem ae_tangentialJacobian_le [InnerProductSpace ℝ W] : ∀ᵐ x ∂μHE[k],
    x ∈ E → J x ≤ (K : ℝ) ^ k := hg.lipschitzOnWith.ae_tangentialJacobian_le hE hEm
/-- Measurability of `tangentialFDeriv` for `K`-Lipschitz maps. -/
theorem aemeasurable_tangentialFDeriv [NormedSpace ℝ W] [FiniteDimensional ℝ W] :
    AEMeasurable (D) (μHE[k].restrict E) := hg.lipschitzOnWith.aemeasurable_tangentialFDeriv hE hEm
/-- Measurability of `tangentialJacobian` for `K`-Lipschitz maps. -/
theorem aemeasurable_tangentialJacobian [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] :
    AEMeasurable (J) (μHE[k].restrict E) :=
  hg.lipschitzOnWith.aemeasurable_tangentialJacobian hE hEm
end LipschitzWith
namespace LocallyLipschitz
variable (hg : LocallyLipschitz g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
include hg hE hEm
/-- Almost-everywhere tangential differentiability for locally Lipschitz maps. -/
theorem ae_hasTangentialFDerivAt [NormedSpace ℝ W] [FiniteDimensional ℝ W] : ∀ᵐ x ∂μHE[k], x ∈ E →
    HasTangentialFDerivAt k E g (D x) x := hg.locallyLipschitzOn.ae_hasTangentialFDerivAt hE hEm
/-- Measurability of `tangentialFDeriv` for locally Lipschitz maps. -/
theorem aemeasurable_tangentialFDeriv [NormedSpace ℝ W] [FiniteDimensional ℝ W] :
    AEMeasurable (D) (μHE[k].restrict E) :=
  hg.locallyLipschitzOn.aemeasurable_tangentialFDeriv hE hEm
/-- Measurability of `tangentialJacobian` for locally Lipschitz maps. -/
theorem aemeasurable_tangentialJacobian [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] :
    AEMeasurable (J) (μHE[k].restrict E) :=
  hg.locallyLipschitzOn.aemeasurable_tangentialJacobian hE hEm
end LocallyLipschitz
end RectifiableRademacher
