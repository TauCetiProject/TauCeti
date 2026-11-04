/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Real
public import TauCeti.Analysis.Calculus.Rademacher
public import TauCeti.MeasureTheory.Function.Coarea.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import TauCeti.Analysis.Calculus.Sard.LowDimension
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Function.Coarea.Measurability
import TauCeti.MeasureTheory.Measure.Hausdorff
import TauCeti.MeasureTheory.Measure.Regular

/-!
# Critical-rank fibre nullity and the coarea formula for Lipschitz maps

Let `E` and `F` be finite-dimensional real inner product spaces of dimensions `n` and `m`, and let
`J f x = (fderiv ℝ f x)†.normDet` be the coarea Jacobian of `f : E → F`. Together with the regular
coarea formula in `TauCeti.MeasureTheory.Function.Coarea.Basic`, this file removes the full-rank
differentiability hypothesis for Lipschitz and locally Lipschitz maps:

* **Critical-rank points have almost everywhere null fibres.** If `f` is differentiable at every
  point of `s` and `J f = 0` on `s` (equivalently, `fderiv ℝ f x` is not surjective), then for
  almost every `y : F` the fibre `s ∩ f ⁻¹' {y}` is null for `μHE[n - m]`. Neither measurability of
  `s`, nor a Lipschitz bound, nor `m ≤ n` is needed.
* **The coarea formula for locally Lipschitz and Lipschitz maps.** If `f` is locally Lipschitz on
  an open neighbourhood of a Lebesgue-measurable set `s` (in particular, if `f` is locally Lipschitz
  or Lipschitz on `E`), then
  `∫⁻ y, μHE[n - m] (s ∩ f ⁻¹' {y}) = ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x)†.normDet`.
* **Finiteness and real-valued integration.** When `x ↦ (fderiv ℝ f x)†.normDet` is integrable on
  `s`, almost every fibre `s ∩ f ⁻¹' {y}` has finite `μHE[n - m]`-measure, the real-valued fibre
  measure `y ↦ μHE[n - m].real (s ∩ f ⁻¹' {y})` is integrable, and its Bochner integral equals
  `∫ x in s, (fderiv ℝ f x)†.normDet`.

## The argument

When `n < m`, `f` sends `s` to a Lebesgue-null set by
`DifferentiableOn.addHaar_image_eq_zero_of_finrank_lt_finrank`, so almost every fibre of `s` is
empty. When `m ≤ n`, `s` is covered by Borel pieces on which `f` is Lipschitz with bounded
derivative, and inner regularity plus Eilenberg's inequality reduces to compact sets `K`. Over a
compact `K`, consider `p ε (x, z) = f x + ε • z` on `S = K × B(0, 1)` inside the Euclidean product
`E ×₂ F`. For `ε ≠ 0`, `p ε` has surjective derivative on `S`, so the regular coarea formula equates
`∫⁻ y, μHE[n] (S ∩ p ε ⁻¹' {y})` with `∫⁻ w in S, J (p ε) w`. Slicing each `p ε`-fibre by the
`1`-Lipschitz projection `(x, z) ↦ z`, Eilenberg's inequality, Tonelli's theorem, and translation
invariance on `F` bound `volume (B(0, 1)) * ∫⁻ u, μH[n - m] (K ∩ f ⁻¹' {u})` above by a constant
multiple of `∫⁻ w in S, J (p ε) w`. As `ε → 0`, the derivative of `p ε` tends to `(v, u) ↦ D f x v`,
which is not surjective on `K`, so dominated convergence sends the upper bound to zero.

For a map locally Lipschitz on an open set `U`, Rademacher's theorem
(`LocallyLipschitzOn.ae_differentiableAt_of_mem`) makes the nondifferentiability locus in `U`
Lebesgue-null, hence fibrewise null almost everywhere by a countable Eilenberg cover, while the
critical-rank theorem handles the differentiable points with nonsurjective derivative. The remaining
points form the Borel regular locus where `Coarea.Basic` applies.

## Main declarations

* `TauCeti.ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_normDet_adjoint_fderiv_eq_zero`,
  `TauCeti.ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_not_surjective_fderiv`:
  critical-rank points have almost everywhere null fibres.
* `LocallyLipschitzOn.aemeasurable_euclideanHausdorffMeasure_inter_preimage`: almost-everywhere
  measurability of normalized fibre measures for maps locally Lipschitz on a Lebesgue-measurable
  set.
* `LocallyLipschitzOn.ae_restrict_inter_setOf_regular_preimage_eq`,
  `LipschitzWith.ae_restrict_inter_setOf_regular_preimage_eq`: on almost every fibre, restricting
  `μHE[n - m]` to the fibre agrees with restricting to its regular part.
* `ae_euclideanHausdorffMeasure_setOf_normDet_adjoint_fderiv_eq_zero_inter_preimage_eq_zero` (in
  `LipschitzWith`): the coarea Sard lemma for Lipschitz maps.
* `lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv` (in
  `LocallyLipschitzOn`, `LocallyLipschitz`, and `LipschitzWith`): the unweighted coarea formula.
* `LipschitzOnWith.integrableOn_normDet_adjoint_fderiv`,
  `LipschitzWith.integrableOn_normDet_adjoint_fderiv`,
  `LocallyLipschitzOn.integrableOn_normDet_adjoint_fderiv_of_isCompact`: integrability of the
  coarea Jacobian on finite-measure or compact sets.
* `ae_euclideanHausdorffMeasure_inter_preimage_lt_top_of_integrableOn`,
  `integrable_euclideanHausdorffMeasure_real_inter_preimage`, and
  `integral_euclideanHausdorffMeasure_real_inter_preimage_eq_integral_normDet_adjoint_fderiv` (in
  `LocallyLipschitzOn`, `LocallyLipschitz`, and `LipschitzWith`): fibre finiteness and the
  real-valued coarea formula.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4.2–3.4.3 (the coarea formula for Lipschitz maps, proved via the perturbation `f x + ε z`).
* H. Federer, *Geometric Measure Theory*, Theorem 3.2.11 (the coarea formula).
-/

public section

open Filter Function MeasureTheory Measure Metric Module Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {f : E → F} {s : Set E}

omit [MeasurableSpace F] [BorelSpace F] in
/-- The set of differentiability points with nonzero coarea Jacobian is Borel measurable. -/
theorem measurableSet_setOf_differentiableAt_normDet_adjoint_ne_zero (f : E → F) :
    MeasurableSet {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).adjoint.normDet ≠ 0} :=
  (measurableSet_of_differentiableAt ℝ f).inter
    (measurableSet_eq_fun ((ContinuousLinearMap.continuous_normDet.comp
      ContinuousLinearMap.adjoint.continuous).measurable.comp (measurable_fderiv ℝ f))
      measurable_const).compl

omit [MeasurableSpace F] [BorelSpace F] in
/-- The regular coarea locus, where `f` is differentiable with surjective derivative, is Borel
measurable. -/
theorem measurableSet_setOf_differentiableAt_surjective_fderiv (f : E → F) :
    MeasurableSet {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)} := by
  convert measurableSet_setOf_differentiableAt_normDet_adjoint_ne_zero f using 1
  ext x
  exact and_congr_right' (by
    rw [← ContinuousLinearMap.coe_coe, ← LinearMap.normDet_adjoint_ne_zero_iff,
      ContinuousLinearMap.adjoint_toLinearMap])

/-- Critical-rank fibre nullity on a compact set `K` where `fderiv ℝ f` is bounded and
`dim F ≤ dim E`, proved by perturbing `f` to `(x, z) ↦ f x + ε • z` on `K × ball 0 1`. -/
private theorem ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_isCompact
    {K : Set E} (hK : IsCompact K) (R : ℝ) (hdim : finrank ℝ F ≤ finrank ℝ E)
    (hd : ∀ x ∈ K, DifferentiableAt ℝ f x)
    (h0 : ∀ x ∈ K, (fderiv ℝ f x).adjoint.normDet = 0)
    (hR' : ∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ R) :
    ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F] (K ∩ f ⁻¹' {y}) = 0 := by
  let W := WithLp 2 (E × F)
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E F
  let π₁ : W →L[ℝ] E := ContinuousLinearMap.fst ℝ E F ∘L (e : W →L[ℝ] E × F)
  let π₂ : W →L[ℝ] F := ContinuousLinearMap.snd ℝ E F ∘L (e : W →L[ℝ] E × F)
  have hdimW : finrank ℝ W - finrank ℝ F = finrank ℝ E := by
    have hW : finrank ℝ W = finrank ℝ E + finrank ℝ F := by
      rw [e.toLinearEquiv.finrank_eq, Module.finrank_prod]
    omega
  let B : Set F := ball 0 1
  let S : Set W := {w : W | w.fst ∈ K ∧ w.snd ∈ B}
  have hSm : MeasurableSet S :=
    (hK.isClosed.measurableSet.preimage π₁.continuous.measurable).inter
      (isOpen_ball.measurableSet.preimage π₂.continuous.measurable)
  have hSfin : volume S ≠ ∞ := by
    have hSbdd : Bornology.IsBounded S :=
      (e.symm.toContinuousLinearMap.lipschitzWith.isBounded_image
        (hK.isBounded.prod (isBounded_ball (x := (0 : F)) (r := 1)))).subset
        fun w hw ↦ ⟨e w, hw, e.symm_apply_apply w⟩
    exact hSbdd.measure_lt_top.ne
  let p (ε : ℝ) (w : W) : F := f w.fst + ε • w.snd
  let D (ε : ℝ) (A : E →L[ℝ] F) : W →L[ℝ] F := A ∘L π₁ + ε • π₂
  have hp_deriv (ε : ℝ) {w : W} (hw : w ∈ S) :
      HasFDerivAt (p ε) (D ε (fderiv ℝ f w.fst)) w :=
    ((hd w.fst hw.1).hasFDerivAt.comp w π₁.hasFDerivAt).add (π₂.hasFDerivAt.const_smul ε)
  have hD_surj {ε : ℝ} (hε : ε ≠ 0) (A : E →L[ℝ] F) : Surjective (D ε A) := fun v ↦
    ⟨e.symm (0, ε⁻¹ • v), by simp [D, π₁, π₂, smul_inv_smul₀ hε]⟩
  -- For `ε ≠ 0`, `p ε` has surjective derivative on `S`, so the regular coarea formula applies.
  have hco {ε : ℝ} (hε : ε ≠ 0) :
      ∫⁻ y : F, μHE[finrank ℝ E] (S ∩ p ε ⁻¹' {y}) =
        ∫⁻ w in S, ENNReal.ofReal (D ε (fderiv ℝ f w.fst)).adjoint.normDet := by
    rw [← hdimW,
      lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
        hSm.nullMeasurableSet (fun w hw ↦ (hp_deriv ε hw).differentiableAt)
        (fun w hw ↦ by rw [(hp_deriv ε hw).fderiv]; exact hD_surj hε _)]
    exact setLIntegral_congr_fun hSm fun w hw ↦ by rw [(hp_deriv ε hw).fderiv]
  -- Slice each `p ε`-fibre along the `1`-Lipschitz second projection `w ↦ w.snd`.
  set k := finrank ℝ E - finrank ℝ F
  let ϕ : F → ℝ≥0∞ := fun u ↦ μH[(k : ℝ)] (K ∩ f ⁻¹' {u})
  have hϕm : Measurable ϕ :=
    hK.measurable_hausdorffMeasure_inter_preimage
      (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt) (k : ℝ)
  have hι (z : F) : Isometry (fun x : E ↦ WithLp.toLp 2 (x, z)) := by
    refine Isometry.of_dist_eq fun x₁ x₂ ↦ ?_
    rw [dist_eq_norm, dist_eq_norm]
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    have hsub : WithLp.toLp 2 (x₁, z) - WithLp.toLp 2 (x₂, z) = WithLp.toLp 2 (x₁ - x₂, 0) :=
      e.injective (by ext <;> simp [e])
    rw [hsub, WithLp.prod_norm_sq_eq_of_L2]
    simp
  have hslice (ε : ℝ) (y : F) {z : F} (hz : z ∈ B) :
      (S ∩ p ε ⁻¹' {y}) ∩ (fun w : W ↦ w.snd) ⁻¹' {z} =
        (fun x : E ↦ WithLp.toLp 2 (x, z)) '' (K ∩ f ⁻¹' {y - ε • z}) := by
    ext w
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_image, S, p]
    constructor
    · rintro ⟨⟨⟨hwK, -⟩, hpw⟩, rfl⟩
      refine ⟨w.fst, ⟨hwK, eq_sub_of_add_eq hpw⟩, ?_⟩
      exact e.injective (by ext <;> simp [e])
    · rintro ⟨x, ⟨hxK, hfx⟩, rfl⟩
      simp [hxK, hz, hfx]
  have hsnd_lip : LipschitzWith 1 (fun w : W ↦ w.snd) := by
    refine LipschitzWith.of_dist_le_mul fun w₁ w₂ ↦ ?_
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    have hsub : (w₁ - w₂).snd = w₁.snd - w₂.snd := rfl
    rw [← hsub, WithLp.prod_norm_sq_eq_of_L2]
    nlinarith [sq_nonneg ‖(w₁ - w₂).fst‖]
  have hdim_add : (finrank ℝ F : ℝ) + (k : ℝ) = (finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.add_sub_of_le hdim
  let c := addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin (finrank ℝ E))))
    μH[(finrank ℝ E : ℝ)]
  have hlow {ε : ℝ} (hε : ε ≠ 0) :
      (c : ℝ≥0∞) * (volume B * ∫⁻ u : F, ϕ u) ≤
        volume B * ∫⁻ w in S, ENNReal.ofReal (D ε (fderiv ℝ f w.fst)).adjoint.normDet := by
    have hfib (y : F) : ∫⁻ z in B, ϕ (y - ε • z) ≤
        volume B * μH[(finrank ℝ E : ℝ)] (S ∩ p ε ⁻¹' {y}) := by
      have hBeq : ∫⁻ z in B, ϕ (y - ε • z) =
          ∫⁻ z in B, μH[(k : ℝ)] ((S ∩ p ε ⁻¹' {y}) ∩ (fun w : W ↦ w.snd) ⁻¹' {z}) := by
        refine setLIntegral_congr_fun isOpen_ball.measurableSet fun z hz ↦ ?_
        rw [hslice ε y hz, (hι z).hausdorffMeasure_image (Or.inl k.cast_nonneg)]
      calc ∫⁻ z in B, ϕ (y - ε • z)
          ≤ ∫⁻ z : F, μH[(k : ℝ)] ((S ∩ p ε ⁻¹' {y}) ∩ (fun w : W ↦ w.snd) ⁻¹' {z}) := by
            rw [hBeq]
            exact setLIntegral_le_lintegral B _
        _ ≤ volume B * 1 ^ finrank ℝ F *
              μH[(finrank ℝ F : ℝ) + (k : ℝ)] (S ∩ p ε ⁻¹' {y}) :=
            hsnd_lip.lipschitzOnWith.lintegral_hausdorffMeasure_inter_preimage_le volume
              k.cast_nonneg
        _ = volume B * μH[(finrank ℝ E : ℝ)] (S ∩ p ε ⁻¹' {y}) := by simp [hdim_add]
    have hswap : ∫⁻ y : F, ∫⁻ z in B, ϕ (y - ε • z) = volume B * ∫⁻ u : F, ϕ u := by
      have hm : AEMeasurable (fun q : F × F ↦ ϕ (q.1 - ε • q.2))
          (volume.prod (volume.restrict B)) :=
        (hϕm.comp (continuous_fst.sub
          (continuous_const.smul continuous_snd)).measurable).aemeasurable
      rw [lintegral_lintegral_swap hm]
      simp_rw [lintegral_sub_right_eq_self ϕ]
      rw [setLIntegral_const, mul_comm]
    calc (c : ℝ≥0∞) * (volume B * ∫⁻ u : F, ϕ u)
        = (c : ℝ≥0∞) * ∫⁻ y : F, ∫⁻ z in B, ϕ (y - ε • z) := by rw [hswap]
      _ ≤ (c : ℝ≥0∞) * ∫⁻ y : F, volume B * μH[(finrank ℝ E : ℝ)] (S ∩ p ε ⁻¹' {y}) := by
          gcongr with y
          exact hfib y
      _ = volume B * ∫⁻ y : F, μHE[finrank ℝ E] (S ∩ p ε ⁻¹' {y}) := by
          rw [lintegral_const_mul' _ _ measure_ball_lt_top.ne, ← mul_assoc, mul_comm (c : ℝ≥0∞),
            mul_assoc, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
          congr 1
          refine lintegral_congr fun y ↦ ?_
          rw [euclideanHausdorffMeasure_def, smul_apply, ENNReal.smul_def, smul_eq_mul]
      _ = volume B * ∫⁻ w in S, ENNReal.ofReal (D ε (fderiv ℝ f w.fst)).adjoint.normDet := by
          rw [hco hε]
  -- Dominated convergence sends the upper bound to `0` as `ε → 0`.
  have hcont : Continuous fun L : W →L[ℝ] F ↦ L.adjoint.normDet :=
    ContinuousLinearMap.continuous_normDet.comp ContinuousLinearMap.adjoint.continuous
  have hDcont : Continuous fun q : ℝ × (E →L[ℝ] F) ↦ D q.1 q.2 :=
    (continuous_snd.clm_comp continuous_const).add (continuous_fst.smul continuous_const)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod
    (isCompact_closedBall (0 : E →L[ℝ] F) R)
    |>.exists_bound_of_continuousOn (hcont.comp hDcont).continuousOn
  have hlim : Tendsto
      (fun ε : ℝ ↦ ∫⁻ w in S, ENNReal.ofReal (D ε (fderiv ℝ f w.fst)).adjoint.normDet) (𝓝 0)
      (𝓝 (∫⁻ w in S, ENNReal.ofReal (D 0 (fderiv ℝ f w.fst)).adjoint.normDet)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ ↦ ENNReal.ofReal M)
      (Eventually.of_forall fun ε ↦ ?_) ?_ ?_ (Eventually.of_forall fun w ↦ ?_)
    · exact ENNReal.measurable_ofReal.comp ((hcont.comp ((continuous_id.clm_comp
        continuous_const).add continuous_const)).measurable.comp
        ((measurable_fderiv ℝ f).comp π₁.continuous.measurable))
    · filter_upwards [Icc_mem_nhds (neg_one_lt_zero : (-1 : ℝ) < 0) zero_lt_one] with ε hε
      refine (ae_restrict_iff' hSm).2 (Eventually.of_forall fun w hw ↦ ?_)
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
        (hM (ε, fderiv ℝ f w.fst) ⟨hε, mem_closedBall_zero_iff.2 (hR' w.fst hw.1)⟩))
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSfin
    · exact (ENNReal.continuous_ofReal.comp (hcont.comp
        (hDcont.comp (continuous_id.prodMk continuous_const)))).tendsto 0
  have hzero : ∫⁻ w in S, ENNReal.ofReal (D 0 (fderiv ℝ f w.fst)).adjoint.normDet = 0 := by
    refine (setLIntegral_congr_fun hSm fun w hw ↦ ?_).trans lintegral_zero
    have hns : ¬Surjective (D 0 (fderiv ℝ f w.fst) : W →ₗ[ℝ] F) := by
      have hns0 : ¬Surjective (fderiv ℝ f w.fst : E →ₗ[ℝ] F) := by
        rw [← LinearMap.normDet_adjoint_eq_zero_iff, ContinuousLinearMap.adjoint_toLinearMap]
        exact h0 w.fst hw.1
      intro hsurj
      refine hns0 fun v ↦ ?_
      obtain ⟨u, hu⟩ := hsurj v
      exact ⟨π₁ u, by simpa [D] using hu⟩
    rw [← ContinuousLinearMap.adjoint_toLinearMap, LinearMap.normDet_adjoint_eq_zero_iff.2 hns,
      ENNReal.ofReal_zero]
  rw [hzero] at hlim
  have hlim' : Tendsto
      (fun ε : ℝ ↦ volume B * ∫⁻ w in S, ENNReal.ofReal (D ε (fderiv ℝ f w.fst)).adjoint.normDet)
      (𝓝[≠] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (hlim.mono_left nhdsWithin_le_nhds)
      (Or.inr measure_ball_lt_top.ne)
  have hprod0 : (c : ℝ≥0∞) * (volume B * ∫⁻ u : F, ϕ u) = 0 :=
    nonpos_iff_eq_zero.1 (ge_of_tendsto hlim' (eventually_nhdsWithin_of_forall fun ε hε ↦ hlow hε))
  have hc0 : (c : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (finrank ℝ E))
  have hB0 : volume B ≠ 0 := (measure_ball_pos volume (0 : F) one_pos).ne'
  have hint0 : ∫⁻ u : F, ϕ u = 0 := by
    rcases mul_eq_zero.1 hprod0 with hc | hBint
    · exact (hc0 hc).elim
    rcases mul_eq_zero.1 hBint with hB | hint
    · exact (hB0 hB).elim
    exact hint
  filter_upwards [(lintegral_eq_zero_iff hϕm).1 hint0] with y hy
  exact euclideanHausdorffMeasure_eq_zero_iff.2 hy

/-- **Critical-rank points have almost everywhere null fibres.** Let `E` and `F` be
finite-dimensional real inner product spaces. If `f : E → F` is differentiable at every point of `s`
and its coarea Jacobian `(fderiv ℝ f x)†.normDet` vanishes on `s`, then almost every fibre
`s ∩ f ⁻¹' {y}` is null for `μHE[dim E - dim F]`. Neither measurability of `s`, nor a Lipschitz
hypothesis, nor `dim F ≤ dim E` is required. -/
theorem ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_normDet_adjoint_fderiv_eq_zero
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (h0 : ∀ x ∈ s, (fderiv ℝ f x).adjoint.normDet = 0) :
    ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) = 0 := by
  by_cases hEF : finrank ℝ E < finrank ℝ F
  · have himg : volume (f '' s) = 0 :=
      (DifferentiableOn.addHaar_image_eq_zero_of_finrank_lt_finrank volume
        (fun x hx ↦ (hd x hx).differentiableWithinAt) hEF)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 himg] with y hy
    have hemp : s ∩ f ⁻¹' {y} = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hy ⟨x, hx.1, hx.2⟩
    simp [hemp]
  replace hEF : finrank ℝ F ≤ finrank ℝ E := not_lt.1 hEF
  -- Cover `s` by Borel pieces on which `fderiv ℝ f` is bounded and `f` is Lipschitz.
  let T : ℕ → Set E := fun r ↦
    ({x | DifferentiableAt ℝ f x} ∩ {x | (fderiv ℝ f x).adjoint.normDet = 0}) ∩
      {x | ‖fderiv ℝ f x‖ ≤ r}
  have hTm (r : ℕ) : MeasurableSet (T r) :=
    (((measurableSet_of_differentiableAt ℝ f).inter
      (measurableSet_eq_fun ((ContinuousLinearMap.continuous_normDet.comp
        ContinuousLinearMap.adjoint.continuous).measurable.comp (measurable_fderiv ℝ f))
        measurable_const)).inter
      (measurableSet_le (measurable_fderiv ℝ f).norm measurable_const))
  choose t A _ ht_meas ht_cover ht_approx _ using fun r ↦
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f (T r) (fderiv ℝ f)
      (fun x hx ↦ hx.1.1.hasFDerivAt.hasFDerivWithinAt) (fun _ ↦ 1) (fun _ ↦ one_ne_zero)
  let P (p : ℕ × ℕ) : Set E := T p.1 ∩ t p.1 p.2
  have hPnull (p : ℕ × ℕ) : ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F] (P p ∩ f ⁻¹' {y}) = 0 := by
    have hPm : MeasurableSet (P p) := (hTm p.1).inter (ht_meas p.1 p.2)
    have hPlip : LipschitzOnWith _ f (P p) :=
      lipschitzOnWith_iff_restrict.2 (ht_approx p.1 p.2).lipschitzWith
    obtain ⟨S, hSP, hSsig, hSP_ae⟩ :=
      (hPm.nullMeasurableSet (μ := volume)).exists_isSigmaCompact_subset_ae_eq
    obtain ⟨K, hKc, rfl⟩ := hSsig
    -- On the null remainder `P p \ ⋃ m, K m`, Eilenberg's inequality gives null fibres a.e.
    have hrem : ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F] ((P p \ ⋃ m, K m) ∩ f ⁻¹' {y}) = 0 := by
      have hvol : μHE[finrank ℝ F + (finrank ℝ E - finrank ℝ F)] (P p \ ⋃ m, K m) = 0 := by
        rw [Nat.add_sub_of_le hEF, InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
        exact (ae_eq_set.1 hSP_ae).2
      exact (hPlip.mono sdiff_subset).ae_euclideanHausdorffMeasure_inter_preimage_eq_zero
        volume hvol
    -- On each compact piece `K m`, the compact critical-rank lemma gives null fibres a.e.
    have hcomp : ∀ᵐ y : F, ∀ m, μHE[finrank ℝ E - finrank ℝ F] (K m ∩ f ⁻¹' {y}) = 0 :=
      ae_all_iff.2 fun m ↦
        ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_isCompact (hKc m) p.1 hEF
          (fun x hx ↦ (hSP (subset_iUnion K m hx)).1.1.1)
          (fun x hx ↦ (hSP (subset_iUnion K m hx)).1.1.2)
          (fun x hx ↦ (hSP (subset_iUnion K m hx)).1.2)
    filter_upwards [hrem, hcomp] with y hy_rem hy_comp
    have hsub : P p ∩ f ⁻¹' {y} ⊆ ((P p \ ⋃ m, K m) ∩ f ⁻¹' {y}) ∪ ⋃ m, K m ∩ f ⁻¹' {y} := by
      intro x ⟨hxP, hxy⟩
      by_cases hxK : x ∈ ⋃ m, K m
      · obtain ⟨m, hxm⟩ := mem_iUnion.1 hxK
        exact Or.inr (mem_iUnion.2 ⟨m, hxm, hxy⟩)
      · exact Or.inl ⟨⟨hxP, hxK⟩, hxy⟩
    exact measure_mono_null hsub (measure_union_null hy_rem (measure_iUnion_null hy_comp))
  filter_upwards [ae_all_iff.2 hPnull] with y hy
  refine measure_mono_null (t := ⋃ p, P p ∩ f ⁻¹' {y}) (fun x ⟨hxs, hxy⟩ ↦ ?_)
    (measure_iUnion_null hy)
  obtain ⟨r, hr⟩ := exists_nat_ge ‖fderiv ℝ f x‖
  have hxT : x ∈ T r := ⟨⟨hd x hxs, h0 x hxs⟩, hr⟩
  obtain ⟨j, hj⟩ := mem_iUnion.1 (ht_cover r hxT)
  exact mem_iUnion.2 ⟨(r, j), ⟨hxT, hj⟩, hxy⟩

/-- If `f` is differentiable at every point of `s` with nonsurjective derivative, then almost every
fibre `s ∩ f ⁻¹' {y}` is null for `μHE[dim E - dim F]`. -/
theorem ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_not_surjective_fderiv
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hns : ∀ x ∈ s, ¬Surjective (fderiv ℝ f x)) :
    ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) = 0 :=
  ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_normDet_adjoint_fderiv_eq_zero hd
    fun x hx ↦ by
      rw [← ContinuousLinearMap.adjoint_toLinearMap, LinearMap.normDet_adjoint_eq_zero_iff]
      exact hns x hx

end TauCeti

private alias lintegral_coarea_surj :=
  lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv

/-! ### Locally Lipschitz maps -/

namespace LocallyLipschitzOn

open TauCeti

section NormedTarget

/-- If `f` is locally Lipschitz on `A` with values in an `m`-dimensional real normed space and
`μH[m + t] A = 0`, then almost every fibre `A ∩ f ⁻¹' {y}` is `μH[t]`-null. -/
theorem ae_hausdorffMeasure_inter_preimage_eq_zero {X Y : Type*} [EMetricSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [μ.IsAddHaarMeasure]
    {A : Set X} {f : X → Y} {t : ℝ}
    (hf : LocallyLipschitzOn A f) (ht : 0 ≤ t) (hA : μH[finrank ℝ Y + t] A = 0) :
    ∀ᵐ y ∂μ, μH[t] (A ∩ f ⁻¹' {y}) = 0 := by
  have hloc : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ ∃ K, LipschitzOnWith K f (A ∩ U) := by
    intro x hx
    obtain ⟨K, u, hu, hK⟩ := hf hx
    obtain ⟨U, hU, hxU, hUu⟩ := mem_nhdsWithin.1 hu
    exact ⟨U, hU, hxU, K, hK.mono ((inter_comm A U).subset.trans hUu)⟩
  choose! U hU hxU K hK using hloc
  obtain ⟨c, hcA, hc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x ↦ A ∩ U x) fun x hx ↦ inter_mem_nhdsWithin A ((hU x hx).mem_nhds (hxU x hx))
  have hae := (ae_ball_iff hc).2 fun x hx ↦
    (hK x (hcA hx)).ae_hausdorffMeasure_inter_preimage_eq_zero μ ht
      (measure_mono_null inter_subset_left hA)
  filter_upwards [hae] with y hy
  have : Countable c := hc.to_subtype
  refine measure_mono_null (t := ⋃ x : c, (A ∩ U x) ∩ f ⁻¹' {y}) (fun z ⟨hzA, hzy⟩ ↦ ?_)
    (measure_iUnion_null fun x ↦ hy x x.2)
  obtain ⟨x, hxc, hzx⟩ := mem_iUnion₂.1 (hcov hzA)
  exact mem_iUnion.2 ⟨⟨x, hxc⟩, hzx, hzy⟩

/-- **Normalized fibre measures of a locally Lipschitz map on a Lebesgue-measurable set are almost
everywhere measurable.** Neither openness of `A` nor a global Lipschitz bound is required. -/
theorem aemeasurable_euclideanHausdorffMeasure_inter_preimage {E Y : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [μ.IsAddHaarMeasure]
    {A : Set E} {f : E → Y} (hf : LocallyLipschitzOn A f) (hA : NullMeasurableSet A) {k : ℕ}
    (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ μHE[k] (A ∩ f ⁻¹' {y})) μ := by
  obtain ⟨S, hSA, hS, hSA'⟩ := hA.exists_isSigmaCompact_subset_ae_eq
  have hnull : μH[finrank ℝ Y + (k : ℝ)] (A \ S) = 0 := by
    have h := (ae_eq_set.1 hSA').2
    rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      euclideanHausdorffMeasure_eq_zero_iff] at h
    exact nonpos_iff_eq_zero.1 ((hausdorffMeasure_mono (by exact_mod_cast hk) _).trans h.le)
  have hae : (fun y ↦ μH[(k : ℝ)] (A ∩ f ⁻¹' {y})) =ᵐ[μ]
      fun y ↦ μH[(k : ℝ)] (S ∩ f ⁻¹' {y}) := by
    filter_upwards [(hf.mono sdiff_subset).ae_hausdorffMeasure_inter_preimage_eq_zero μ
      k.cast_nonneg hnull] with y hy
    exact (measure_eq_measure_of_null_sdiff (inter_subset_inter_left _ hSA)
      (by rwa [← inter_sdiff_distrib_right])).symm
  simp only [euclideanHausdorffMeasure_def, _root_.smul_apply]
  exact ((hS.measurable_hausdorffMeasure_inter_preimage (hf.continuousOn.mono hSA)
    (k : ℝ)).aemeasurable.congr hae.symm).const_smul _

end NormedTarget

section Coarea

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {U s : Set E} {f : E → F}

/-- On an open set `U` where `f` is locally Lipschitz, the points of `U` outside the regular coarea
locus have null `(dim E - dim F)`-dimensional fibre measure for almost every `y : F`. -/
theorem ae_euclideanHausdorffMeasure_sdiff_setOf_regular_inter_preimage_eq_zero
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) :
    ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F]
      ((U \ {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}) ∩ f ⁻¹' {y}) = 0 := by
  let N := {x ∈ U | ¬DifferentiableAt ℝ f x}
  let C := {x ∈ U | DifferentiableAt ℝ f x ∧ ¬Surjective (fderiv ℝ f x)}
  have hN_vol : μH[finrank ℝ F + ((finrank ℝ E - finrank ℝ F : ℕ) : ℝ)] N = 0 := by
    have hvol : volume N = 0 := by
      have hae : ∀ᵐ x : E, x ∉ N := by
        filter_upwards [hf.ae_differentiableAt_of_mem hU] with x hx hxN
        exact hxN.2 (hx hxN.1)
      exact measure_eq_zero_iff_ae_notMem.2 hae
    rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      euclideanHausdorffMeasure_eq_zero_iff] at hvol
    exact nonpos_iff_eq_zero.1
      ((hausdorffMeasure_mono (by exact_mod_cast le_add_tsub) _).trans hvol.le)
  have hN_fib : ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F] (N ∩ f ⁻¹' {y}) = 0 := by
    filter_upwards [(hf.mono fun _ (hx : _ ∈ N) ↦ hx.1).ae_hausdorffMeasure_inter_preimage_eq_zero
      volume (Nat.cast_nonneg _) hN_vol] with y hy
    exact euclideanHausdorffMeasure_eq_zero_iff.2 hy
  have hC_fib : ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F] (C ∩ f ⁻¹' {y}) = 0 :=
    ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_not_surjective_fderiv
      (fun _ hx ↦ hx.2.1) (fun _ hx ↦ hx.2.2)
  filter_upwards [hN_fib, hC_fib] with y hyN hyC
  refine measure_mono_null (t := (N ∩ f ⁻¹' {y}) ∪ (C ∩ f ⁻¹' {y}))
    (fun x ⟨⟨hxU, hxG⟩, hxy⟩ ↦ ?_) (measure_union_null hyN hyC)
  by_cases hd : DifferentiableAt ℝ f x
  · exact Or.inr ⟨⟨hxU, hd, fun hs ↦ hxG ⟨hd, hs⟩⟩, hxy⟩
  · exact Or.inl ⟨⟨hxU, hd⟩, hxy⟩

/-- For `s ⊆ U` with `U` open and `f` locally Lipschitz on `U`, restricting
`μHE[dim E - dim F]` to the fibre `s ∩ f ⁻¹' {y}` agrees for almost every `y : F` with restricting
to its regular part `(s ∩ {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}) ∩ f ⁻¹' {y}`. -/
theorem ae_restrict_inter_setOf_regular_preimage_eq
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U) :
    ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F].restrict (s ∩ f ⁻¹' {y}) =
      μHE[finrank ℝ E - finrank ℝ F].restrict
        ((s ∩ {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}) ∩ f ⁻¹' {y}) := by
  set G := {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}
  filter_upwards [hf.ae_euclideanHausdorffMeasure_sdiff_setOf_regular_inter_preimage_eq_zero hU]
    with y hy
  refine Measure.restrict_congr_set (ae_eq_set.2
    ⟨?_, measure_mono_null (fun x ⟨⟨⟨hxs, _⟩, hxy⟩, hx⟩ ↦ (hx ⟨hxs, hxy⟩).elim) measure_empty⟩)
  refine measure_mono_null (fun x ⟨⟨hxs, hxy⟩, hx⟩ ↦ ?_) hy
  exact ⟨⟨hsU hxs, fun hxG ↦ hx ⟨⟨hxs, hxG⟩, hxy⟩⟩, hxy⟩

/-- **The coarea formula for locally Lipschitz maps on open sets.** If `f : E → F` is locally
Lipschitz on an open set `U` containing a Lebesgue-measurable set `s`, then the integral over `F` of
the `(dim E - dim F)`-dimensional Euclidean Hausdorff measures of `s ∩ f ⁻¹' {y}` equals the
integral over `s` of the coarea Jacobian `(fderiv ℝ f x)†.normDet`. -/
theorem lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s) :
    ∫⁻ y : F, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet := by
  set G := {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}
  have hGm : MeasurableSet G := measurableSet_setOf_differentiableAt_surjective_fderiv f
  have hfib : ∫⁻ y : F, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) =
      ∫⁻ y : F, μHE[finrank ℝ E - finrank ℝ F] ((s ∩ G) ∩ f ⁻¹' {y}) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hf.ae_restrict_inter_setOf_regular_preimage_eq hU hsU] with y hy
    simpa only [Measure.restrict_apply_univ] using congrArg (fun μ ↦ μ univ) hy
  have hzero : ∫⁻ x in s \ G, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet = 0 := by
    refine nonpos_iff_eq_zero.1 ((lintegral_mono_set (sdiff_le_sdiff_right hsU)).trans_eq ?_)
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_restrict_of_ae (hf.ae_differentiableAt_of_mem (μ := volume) hU),
      ae_restrict_mem (MeasurableSet.diff hU.measurableSet hGm)] with x hx hxUG
    have hd : DifferentiableAt ℝ f x := hx hxUG.1
    have hns : ¬Surjective (fderiv ℝ f x : E →ₗ[ℝ] F) := fun hsurj ↦ hxUG.2 ⟨hd, hsurj⟩
    rw [← ContinuousLinearMap.adjoint_toLinearMap, LinearMap.normDet_adjoint_eq_zero_iff.2 hns,
      ENNReal.ofReal_zero]
  rw [hfib,
    lintegral_coarea_surj (hs.inter hGm.nullMeasurableSet) (fun _ hx ↦ hx.2.1) (fun _ hx ↦ hx.2.2),
    ← lintegral_inter_add_sdiff _ s hGm, hzero, add_zero]

/-- If `f` is locally Lipschitz on an open neighbourhood `U` of a Lebesgue-measurable set `s` and
the coarea Jacobian is integrable on `s`, then almost every fibre `s ∩ f ⁻¹' {y}` has finite
`μHE[dim E - dim F]`-measure. -/
theorem ae_euclideanHausdorffMeasure_inter_preimage_lt_top_of_integrableOn
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet) s) :
    ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) < ∞ := by
  have hm := (hf.mono hsU).aemeasurable_euclideanHausdorffMeasure_inter_preimage volume hs
    le_add_tsub
  refine ae_lt_top' hm ?_
  rw [hf.lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
    hU hsU hs]
  exact hint.lintegral_lt_top.ne

/-- If `f` is locally Lipschitz on an open neighbourhood `U` of a Lebesgue-measurable set `s` and
the coarea Jacobian is integrable on `s`, then the real-valued fibre measure
`y ↦ μHE[dim E - dim F].real (s ∩ f ⁻¹' {y})` is integrable on `F`. -/
theorem integrable_euclideanHausdorffMeasure_real_inter_preimage
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet) s) :
    Integrable (fun y : F ↦ μHE[finrank ℝ E - finrank ℝ F].real (s ∩ f ⁻¹' {y})) := by
  have hm := (hf.mono hsU).aemeasurable_euclideanHausdorffMeasure_inter_preimage volume hs
    le_add_tsub
  have hne : ∫⁻ y : F, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) ≠ ∞ := by
    rw [hf.lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
      hU hsU hs]
    exact hint.lintegral_lt_top.ne
  exact integrable_toReal_of_lintegral_ne_top hm hne

/-- **The real-valued coarea formula for locally Lipschitz maps on open sets.** When the coarea
Jacobian `(fderiv ℝ f x)†.normDet` is integrable on `s`, the Bochner integral of the real-valued
fibre measure equals the Bochner integral of the coarea Jacobian over `s`. -/
theorem integral_euclideanHausdorffMeasure_real_inter_preimage_eq_integral_normDet_adjoint_fderiv
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet) s) :
    ∫ y : F, μHE[finrank ℝ E - finrank ℝ F].real (s ∩ f ⁻¹' {y}) =
      ∫ x in s, (fderiv ℝ f x).adjoint.normDet := by
  have hm := (hf.mono hsU).aemeasurable_euclideanHausdorffMeasure_inter_preimage volume hs
    le_add_tsub
  have hfin := hf.ae_euclideanHausdorffMeasure_inter_preimage_lt_top_of_integrableOn hU hsU hs hint
  simp only [measureReal_def]
  rw [integral_toReal hm hfin,
    hf.lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
      hU hsU hs,
    ← integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x ↦ LinearMap.normDet_nonneg _) hint.aestronglyMeasurable]

end Coarea

end LocallyLipschitzOn

/-! ### Integrability of the coarea Jacobian -/

namespace LipschitzOnWith

/-- If `f` is `K`-Lipschitz on an open set `U` containing a finite-measure set `s`, then the coarea
Jacobian `x ↦ (fderiv ℝ f x)†.normDet` is integrable on `s`. Neither measurability of `s` nor
`dim F ≤ dim E` is required. -/
theorem integrableOn_normDet_adjoint_fderiv {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    {U s : Set E} {f : E → F} {K : ℝ≥0} (hf : LipschitzOnWith K f U) (hU : IsOpen U)
    (hsU : s ⊆ U) (hs : volume s ≠ ∞) :
    IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet) s := by
  by_cases hEF : finrank ℝ E < finrank ℝ F
  · have h0 : (fun x : E ↦ (fderiv ℝ f x).adjoint.normDet) = 0 := by
      ext x
      have hns : ¬Surjective (fderiv ℝ f x : E →ₗ[ℝ] F) :=
        fun h ↦ hEF.not_ge (LinearMap.finrank_le_finrank_of_surjective h)
      rw [Pi.zero_apply, ← ContinuousLinearMap.adjoint_toLinearMap,
        LinearMap.normDet_adjoint_eq_zero_iff.2 hns]
    rw [h0]
    exact integrableOn_zero
  replace hEF : finrank ℝ F ≤ finrank ℝ E := not_lt.1 hEF
  let t : Set E := toMeasurable volume s ∩ U
  have htm : MeasurableSet t := (measurableSet_toMeasurable volume s).inter hU.measurableSet
  have ht_fin : volume t < ∞ :=
    ((measure_mono inter_subset_left).trans_eq (measure_toMeasurable s)).trans_lt hs.lt_top
  have hJm : Measurable fun x : E ↦ (fderiv ℝ f x).adjoint.normDet :=
    (ContinuousLinearMap.continuous_normDet.comp
      ContinuousLinearMap.adjoint.continuous).measurable.comp (measurable_fderiv ℝ f)
  have hfU : LocallyLipschitzOn U f := fun _ _ ↦ ⟨K, U, self_mem_nhdsWithin, hf⟩
  have ht_int : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet) t := by
    refine (lintegral_ofReal_ne_top_iff_integrable hJm.aestronglyMeasurable.restrict
      (Eventually.of_forall fun _ ↦ LinearMap.normDet_nonneg _)).1 ?_
    rw [← hfU.lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
      hU inter_subset_right htm.nullMeasurableSet]
    set k := finrank ℝ E - finrank ℝ F
    let c := addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin k))) μH[(k : ℝ)]
    have hc : ∫⁻ y : F, μHE[k] (t ∩ f ⁻¹' {y}) =
        (c : ℝ≥0∞) * ∫⁻ y : F, μH[(k : ℝ)] (t ∩ f ⁻¹' {y}) := by
      rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      refine lintegral_congr fun y ↦ ?_
      rw [euclideanHausdorffMeasure_def, smul_apply, ENNReal.smul_def, smul_eq_mul]
    have htH : μH[finrank ℝ F + (k : ℝ)] t < ∞ := by
      have hdim : finrank ℝ F + (k : ℝ) = (finrank ℝ E : ℝ) := by
        exact_mod_cast Nat.add_sub_of_le hEF
      rw [hdim, ← euclideanHausdorffMeasure_lt_top_iff,
        InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
      exact ht_fin
    rw [hc]
    refine ENNReal.mul_ne_top ENNReal.coe_ne_top ?_
    refine ((hf.mono inter_subset_right).lintegral_hausdorffMeasure_inter_preimage_le volume
      k.cast_nonneg).trans_lt ?_ |>.ne
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top measure_ball_lt_top (ENNReal.pow_ne_top ENNReal.coe_ne_top).lt_top) htH
  exact ht_int.mono_set (subset_inter (subset_toMeasurable volume s) hsU)

end LipschitzOnWith

namespace LocallyLipschitzOn

/-- On a compact subset `s` of an open set `U` where `f` is locally Lipschitz, the coarea Jacobian
`x ↦ (fderiv ℝ f x)†.normDet` is integrable on `s`. -/
theorem integrableOn_normDet_adjoint_fderiv_of_isCompact {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    {U s : Set E} {f : E → F} (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U)
    (hs : IsCompact s) :
    IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet) s := by
  have hloc : ∀ x ∈ s, ∃ r > 0, ∃ K, LipschitzOnWith K f (ball x r) := by
    intro x hx
    obtain ⟨K, t, ht, hKt⟩ := hf (hsU hx)
    rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds (hsU hx))] at ht
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 ht
    exact ⟨r, hr, K, hKt.mono hrt⟩
  choose! r hr K hK using hloc
  obtain ⟨I, hIs, hcov⟩ := hs.elim_nhds_subcover (fun x ↦ ball x (r x))
    fun x hx ↦ ball_mem_nhds x (hr x hx)
  refine (integrableOn_finset_iUnion.2 fun x hx ↦ ?_).mono_set hcov
  exact (hK x (hIs x hx)).integrableOn_normDet_adjoint_fderiv isOpen_ball Subset.rfl
    measure_ball_lt_top.ne

end LocallyLipschitzOn

/-! ### Globally locally Lipschitz maps -/

namespace LocallyLipschitz

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {s : Set E} {f : E → F}

/-- For a locally Lipschitz map `f : E → F`, the complement of the regular coarea locus has null
`(dim E - dim F)`-dimensional fibre measure for almost every `y : F`. -/
theorem ae_euclideanHausdorffMeasure_compl_setOf_regular_inter_preimage_eq_zero
    (hf : LocallyLipschitz f) :
    ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F]
      ({x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}ᶜ ∩ f ⁻¹' {y}) = 0 := by
  let hfU := hf.locallyLipschitzOn (s := univ)
  simpa only [compl_eq_univ_sdiff] using
    hfU.ae_euclideanHausdorffMeasure_sdiff_setOf_regular_inter_preimage_eq_zero isOpen_univ

/-- For a locally Lipschitz map `f : E → F` and any set `s`, restricting `μHE[dim E - dim F]` to
`s ∩ f ⁻¹' {y}` agrees for almost every `y : F` with restricting to its regular part. -/
theorem ae_restrict_inter_setOf_regular_preimage_eq (hf : LocallyLipschitz f) (s : Set E) :
    ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F].restrict (s ∩ f ⁻¹' {y}) =
      μHE[finrank ℝ E - finrank ℝ F].restrict
        ((s ∩ {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}) ∩ f ⁻¹' {y}) :=
  (hf.locallyLipschitzOn (s := univ)).ae_restrict_inter_setOf_regular_preimage_eq isOpen_univ
    (subset_univ s)

/-- **The coarea formula for locally Lipschitz maps.** -/
theorem lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
    (hf : LocallyLipschitz f) (hs : NullMeasurableSet s) :
    ∫⁻ y : F, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet := by
  let hfU := hf.locallyLipschitzOn (s := univ)
  exact hfU.lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
    isOpen_univ (subset_univ s) hs

/-- For a locally Lipschitz map, the coarea Jacobian is integrable on every compact set. -/
theorem integrableOn_normDet_adjoint_fderiv_of_isCompact (hf : LocallyLipschitz f)
    (hs : IsCompact s) :
    IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet) s :=
  (hf.locallyLipschitzOn (s := univ)).integrableOn_normDet_adjoint_fderiv_of_isCompact isOpen_univ
    (subset_univ s) hs

/-- Almost-everywhere fibre finiteness for a locally Lipschitz map when the coarea Jacobian is
integrable on `s`. -/
theorem ae_euclideanHausdorffMeasure_inter_preimage_lt_top_of_integrableOn
    (hf : LocallyLipschitz f) (hs : NullMeasurableSet s)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet) s) :
    ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) < ∞ := by
  let hfU := hf.locallyLipschitzOn (s := univ)
  exact hfU.ae_euclideanHausdorffMeasure_inter_preimage_lt_top_of_integrableOn
    isOpen_univ (subset_univ s) hs hint

/-- Integrability of the real-valued fibre measure for a locally Lipschitz map when the coarea
Jacobian is integrable on `s`. -/
theorem integrable_euclideanHausdorffMeasure_real_inter_preimage
    (hf : LocallyLipschitz f) (hs : NullMeasurableSet s)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet) s) :
    Integrable (fun y : F ↦ μHE[finrank ℝ E - finrank ℝ F].real (s ∩ f ⁻¹' {y})) :=
  (hf.locallyLipschitzOn (s := univ)).integrable_euclideanHausdorffMeasure_real_inter_preimage
    isOpen_univ (subset_univ s) hs hint

/-- **The real-valued coarea formula for locally Lipschitz maps.** -/
theorem integral_euclideanHausdorffMeasure_real_inter_preimage_eq_integral_normDet_adjoint_fderiv
    (hf : LocallyLipschitz f) (hs : NullMeasurableSet s)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet) s) :
    ∫ y : F, μHE[finrank ℝ E - finrank ℝ F].real (s ∩ f ⁻¹' {y}) =
      ∫ x in s, (fderiv ℝ f x).adjoint.normDet :=
  (hf.locallyLipschitzOn (s := univ))
    |>.integral_euclideanHausdorffMeasure_real_inter_preimage_eq_integral_normDet_adjoint_fderiv
      isOpen_univ (subset_univ s) hs hint

end LocallyLipschitz

/-! ### Lipschitz maps -/

namespace LipschitzWith

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {s : Set E} {f : E → F} {K : ℝ≥0}

/-- For a Lipschitz map `f : E → F`, the complement of its regular coarea locus has null
`(dim E - dim F)`-dimensional fibre measure for almost every `y : F`. -/
theorem ae_euclideanHausdorffMeasure_compl_setOf_regular_inter_preimage_eq_zero
    (hf : LipschitzWith K f) :
    ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F]
      ({x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}ᶜ ∩ f ⁻¹' {y}) = 0 :=
  hf.locallyLipschitz.ae_euclideanHausdorffMeasure_compl_setOf_regular_inter_preimage_eq_zero

/-- **Coarea Sard lemma for Lipschitz maps.** The set where the coarea Jacobian
`(fderiv ℝ f x)†.normDet` vanishes (including points where `f` is not differentiable) meets almost
every fibre in a `μHE[dim E - dim F]`-null set. -/
theorem ae_euclideanHausdorffMeasure_setOf_normDet_adjoint_fderiv_eq_zero_inter_preimage_eq_zero
    (hf : LipschitzWith K f) :
    ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F]
      ({x | (fderiv ℝ f x).adjoint.normDet = 0} ∩ f ⁻¹' {y}) = 0 := by
  filter_upwards [hf.ae_euclideanHausdorffMeasure_compl_setOf_regular_inter_preimage_eq_zero]
    with y hy
  refine measure_mono_null
    (t := {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}ᶜ ∩ f ⁻¹' {y})
    (fun x ⟨hx, hxy⟩ ↦ ⟨fun hreg ↦ ?_, hxy⟩) hy
  exact (LinearMap.normDet_adjoint_ne_zero_iff.2 hreg.2)
    (by simpa [ContinuousLinearMap.adjoint_toLinearMap] using hx)

/-- For a Lipschitz map `f : E → F` and any set `s`, restricting `μHE[dim E - dim F]` to the fibre
`s ∩ f ⁻¹' {y}` agrees for almost every `y : F` with restricting to its regular part. -/
theorem ae_restrict_inter_setOf_regular_preimage_eq (hf : LipschitzWith K f) (s : Set E) :
    ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F].restrict (s ∩ f ⁻¹' {y}) =
      μHE[finrank ℝ E - finrank ℝ F].restrict
        ((s ∩ {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}) ∩ f ⁻¹' {y}) :=
  hf.locallyLipschitz.ae_restrict_inter_setOf_regular_preimage_eq s

/-- **The coarea formula for Lipschitz maps** on a Lebesgue-measurable set `s`:
`∫⁻ y, μHE[dim E - dim F] (s ∩ f ⁻¹' {y}) = ∫⁻ x in s, (fderiv ℝ f x)†.normDet`. -/
theorem lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s) :
    ∫⁻ y : F, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet := by
  let hfL := hf.locallyLipschitz
  exact hfL.lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
    hs

/-- **The global coarea formula for Lipschitz maps**:
`∫⁻ y, μHE[dim E - dim F] (f ⁻¹' {y}) = ∫⁻ x, (fderiv ℝ f x)†.normDet`. -/
theorem lintegral_euclideanHausdorffMeasure_preimage_eq_lintegral_normDet_adjoint_fderiv
    (hf : LipschitzWith K f) :
    ∫⁻ y : F, μHE[finrank ℝ E - finrank ℝ F] (f ⁻¹' {y}) =
      ∫⁻ x : E, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet := by
  simpa using
    hf.lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
      MeasurableSet.univ.nullMeasurableSet

/-- For a Lipschitz map, the coarea Jacobian is integrable on every set of finite Lebesgue
measure. -/
theorem integrableOn_normDet_adjoint_fderiv (hf : LipschitzWith K f) (hs : volume s ≠ ∞) :
    IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet) s :=
  hf.lipschitzOnWith.integrableOn_normDet_adjoint_fderiv isOpen_univ (subset_univ s) hs

/-- Almost-everywhere fibre finiteness for a Lipschitz map when the coarea Jacobian is integrable on
`s`. -/
theorem ae_euclideanHausdorffMeasure_inter_preimage_lt_top_of_integrableOn
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet) s) :
    ∀ᵐ y : F, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) < ∞ :=
  hf.locallyLipschitz.ae_euclideanHausdorffMeasure_inter_preimage_lt_top_of_integrableOn hs hint

/-- Integrability of the real-valued fibre measure for a Lipschitz map when the coarea Jacobian is
integrable on `s`. -/
theorem integrable_euclideanHausdorffMeasure_real_inter_preimage
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet) s) :
    Integrable (fun y : F ↦ μHE[finrank ℝ E - finrank ℝ F].real (s ∩ f ⁻¹' {y})) :=
  hf.locallyLipschitz.integrable_euclideanHausdorffMeasure_real_inter_preimage hs hint

/-- **The real-valued coarea formula for Lipschitz maps.** When the coarea Jacobian is integrable on
`s`, the integral of the real-valued fibre measure equals the integral of `(fderiv ℝ f x)†.normDet`
over `s`. -/
theorem integral_euclideanHausdorffMeasure_real_inter_preimage_eq_integral_normDet_adjoint_fderiv
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet) s) :
    ∫ y : F, μHE[finrank ℝ E - finrank ℝ F].real (s ∩ f ⁻¹' {y}) =
      ∫ x in s, (fderiv ℝ f x).adjoint.normDet :=
  hf.locallyLipschitz
    |>.integral_euclideanHausdorffMeasure_real_inter_preimage_eq_integral_normDet_adjoint_fderiv
      hs hint

/-- **The global real-valued coarea formula for Lipschitz maps.** -/
theorem integral_euclideanHausdorffMeasure_real_preimage_eq_integral_normDet_adjoint_fderiv
    (hf : LipschitzWith K f) (hint : Integrable fun x : E ↦ (fderiv ℝ f x).adjoint.normDet) :
    ∫ y : F, μHE[finrank ℝ E - finrank ℝ F].real (f ⁻¹' {y}) =
      ∫ x : E, (fderiv ℝ f x).adjoint.normDet := by
  simpa using
    hf.integral_euclideanHausdorffMeasure_real_inter_preimage_eq_integral_normDet_adjoint_fderiv
      MeasurableSet.univ.nullMeasurableSet hint.integrableOn

end LipschitzWith

end
