/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.GroupConvolution
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.CompleteOfCompleteLp
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
import TauCeti.MeasureTheory.Group.Convolution.OpenSubgroup
import TauCeti.MeasureTheory.Group.OpenSubgroup
import TauCeti.MeasureTheory.Group.Prod
import TauCeti.MeasureTheory.Group.SigmaCompactSupport

/-!
# Pointwise representation and Fubini theory for group convolution

On a locally compact Hausdorff group `G` that is not assumed second countable, `borel (G × G)` can
be strictly larger than the product σ-algebra `borel G × borel G`, so `G` need not satisfy
`MeasurableMul₂ G`. When `G` is also not assumed σ-compact, its Haar measure `μ` is not σ-finite
either.

Combining the Haar product strong-measurability theorems of `TauCeti.MeasureTheory.Group.Prod` with
σ-compact open-subgroup reduction, this file identifies the operator convolution
`MeasureTheory.Lp.convolutionL μ p hp h f` (`1 ≤ p < ∞`) almost everywhere with the classical
pointwise Bochner integral `x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ` for any regular Haar measure `μ` on an
arbitrary locally compact Hausdorff group `G`:

1. **Local Fubini and pointwise representation on σ-compact groups:** Bounding
   `∫ x in s, ‖f (y⁻¹ * x)‖` uniformly in `y` via `Set.LpToL1RestrictCLM` and `Lp.leftTranslation`
   shows that `(x, y) ↦ h y • f (y⁻¹ * x)` is integrable on `(μ.restrict s).prod μ` whenever
   `μ s < ∞` (and on all of `μ.prod μ` when `f` is integrable). Testing against `Set.setIntegralLp`
   and applying Fubini's theorem yields
   `Lp.convolutionL μ p hp h f =ᵐ[μ] fun x => ∫ y, h y • f (y⁻¹ * x) ∂μ` on σ-compact groups.
2. **Reduction to σ-compact open subgroups on arbitrary locally compact Hausdorff groups:** For
   `1 ≤ p < ∞`, an integrable kernel `h` and an `Lᵖ` function `f` vanish almost everywhere outside
   one σ-compact open subgroup `H`
   (`MeasureTheory.exists_openSubgroup_isSigmaCompact_forall_ae_eq_zero`).
   Outside `H`, invariance of `Hᶜ` under left multiplication by `H` and
   `Measure.quasiMeasurePreserving_inv_mul_of_regular` make `y ↦ h y • f (y⁻¹ * x)` almost
   everywhere zero at *every* `x ∉ H` (`OpenSubgroup.ae_smul_inv_mul_eq_zero_of_notMem`). Inside
   `H`, both the operator convolution and the pointwise integral reduce to `(H, μ.comap (↑))`
   (`Lp.extendByZeroComapₗᵢ_convolutionL`,
   `integral_convolution_eq_comap_of_ae_restrict_compl_eq_zero`), transferring almost-everywhere
   integrability (`1 ≤ p ≤ ∞`, using `MemLp.comp_quasiMeasurePreserving_top` when `p = ∞`) and the
   pointwise formula to arbitrary locally compact Hausdorff groups.

## Main results

* `MeasureTheory.Integrable.smul_comp_inv_mul_restrict` and
  `MeasureTheory.Integrable.smul_comp_inv_mul_prod`: product integrability of the convolution
  integrand on `(μ.restrict s).prod μ` (`μ s < ∞`, `1 ≤ p ≤ ∞`) and on `μ.prod μ` (`p = 1`) on
  σ-compact locally compact Hausdorff groups.
* `MeasureTheory.Integrable.ae_integrable_smul_comp_inv_mul` and
  `MeasureTheory.Lp.ae_integrable_smul_comp_inv_mul`: on any locally compact Hausdorff group with a
  regular Haar measure `μ` and `1 ≤ p ≤ ∞`, `y ↦ h y • f (y⁻¹ * x)` is `μ`-integrable for
  `μ`-almost every `x : G`.
* `MeasureTheory.Lp.convolutionL_ae_eq`, `MeasureTheory.Lp.convolutionL_toLp_ae_eq`, and
  `MeasureTheory.Integrable.convolutionL_toL1_ae_eq`:
  `convolutionL μ p hp h f =ᵐ[μ] fun x => ∫ y, h y • f (y⁻¹ * x) ∂μ` for a regular Haar measure `μ`
  on any locally compact Hausdorff group (`1 ≤ p < ∞`).
* `MeasureTheory.Integrable.memLp_integral_smul_comp_inv_mul`,
  `MeasureTheory.Integrable.integral_smul_comp_inv_mul`, and
  `MeasureTheory.integral_integral_smul_comp_inv_mul`: `Lᵖ` membership, integrability, and integral
  product formula for `x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ` with respect to a regular Haar measure `μ` on
  any locally compact Hausdorff group.

## Provenance

The finite-measure `Lᵖ → L¹` restriction and `Set.setIntegralLp` Fubini argument in the σ-compact
case (`MeasureTheory.Integrable.smul_comp_inv_mul_restrict` and the σ-compact step of
`MeasureTheory.Lp.convolutionL_ae_eq`) is adapted from the finite-dimensional additive proofs of
`TauCeti.integrable_convolution_integrand_restrict` and `TauCeti.convolutionLp_ae_eq_convolution` in
`TauCeti/MeasureTheory/Function/Lp/Convolution.lean`.

## References

* D. H. Fremlin, *Measure Theory*, Vol. 4, Torres Fremlin (2003), §443M.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §2.5.
* B. Bekka, P. de la Harpe, and A. Valette, *Kazhdan's Property (T)*, Cambridge University Press
  (2008), proof of Theorem G.3.1.
-/

public section

noncomputable section

open Filter Function Set
open scoped ENNReal

namespace MeasureTheory

/-! ### Local Fubini and pointwise convolution on σ-compact groups -/

section SigmaCompactFubini

variable {G 𝕜 E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]
  [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SigmaCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
private theorem integral_norm_smul_le {ν : Measure G} (c : 𝕜) {g : G → E} (hg : Integrable g ν) :
    ∫ x, ‖c • g x‖ ∂ν ≤ ‖c‖ * ∫ x, ‖g x‖ ∂ν :=
  (integral_mono (hg.smul c).norm (hg.norm.const_mul ‖c‖) fun _ => norm_smul_le _ _).trans_eq
    (integral_const_mul _ _)

/-- On a σ-compact locally compact Hausdorff group with a regular Haar measure `μ`, the convolution
integrand `(x, y) ↦ h y • f (y⁻¹ * x)` of an integrable kernel `h` and `f ∈ Lᵖ(G, μ)` (`1 ≤ p ≤ ∞`)
is integrable on `(μ.restrict s).prod μ` for every set `s` of finite measure. -/
theorem Integrable.smul_comp_inv_mul_restrict {p : ℝ≥0∞} [Fact (1 ≤ p)] {h : G → 𝕜}
    (hh : Integrable h μ) {f : G → E} (hf : MemLp f p μ) {s : Set G} (hμs : μ s < ∞) :
    Integrable (fun q : G × G => h q.2 • f (q.2⁻¹ * q.1)) ((μ.restrict s).prod μ) := by
  have _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
  have hmeas : AEStronglyMeasurable (fun q : G × G => h q.2 • f (q.2⁻¹ * q.1))
      ((μ.restrict s).prod μ) :=
    (hh.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).smul
      hf.aestronglyMeasurable.comp_inv_mul_prod
  -- Bound `∫ x in s, ‖f (y⁻¹ * x)‖ ∂μ` uniformly in `y` via `Lᵖ → L¹(s)` restriction on `‖f ·‖`.
  let R := Set.LpToL1RestrictCLM (𝕜 := ℝ) (F := ℝ) (p := p) s hμs
  let fn : Lp ℝ p μ := hf.norm.toLp fun x => ‖f x‖
  have hbound (y : G) : ∫ x in s, ‖f (y⁻¹ * x)‖ ∂μ ≤ ‖R‖ * ‖fn‖ := by
    calc ∫ x in s, ‖f (y⁻¹ * x)‖ ∂μ
        = ‖R (Lp.leftTranslation μ p ℝ y fn)‖ := by
          rw [L1.norm_eq_integral_norm]
          refine integral_congr_ae ?_
          filter_upwards [Set.LpToL1RestrictCLM_coeFn (𝕜 := ℝ) s hμs
              (Lp.leftTranslation μ p ℝ y fn),
            ae_restrict_of_ae (Lp.coeFn_leftTranslation (𝕜 := ℝ) y fn),
            ae_restrict_of_ae ((measurePreserving_mul_left μ y⁻¹).quasiMeasurePreserving.ae
              hf.norm.coeFn_toLp)] with x hx₁ hx₂ hx₃
          rw [hx₁, hx₂, hx₃, Real.norm_of_nonneg (norm_nonneg _)]
      _ ≤ ‖R‖ * ‖fn‖ := by
          rw [← LinearIsometryEquiv.norm_map (Lp.leftTranslation μ p ℝ y) fn]
          exact R.le_opNorm _
  have hfy (y : G) : Integrable (fun x => f (y⁻¹ * x)) (μ.restrict s) :=
    ((hf.comp_measurePreserving (measurePreserving_mul_left μ y⁻¹)).restrict s).integrable Fact.out
  refine (integrable_prod_iff' hmeas).2 ⟨.of_forall fun y => (hfy y).smul (h y), ?_⟩
  refine (hh.norm.mul_const (‖R‖ * ‖fn‖)).mono' hmeas.prod_swap.norm.integral_prod_right'
    (.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  exact (integral_norm_smul_le (h y) (hfy y)).trans
    (mul_le_mul_of_nonneg_left (hbound y) (norm_nonneg _))

/-- On a σ-compact locally compact Hausdorff group with a regular Haar measure `μ`, the convolution
integrand `(x, y) ↦ h y • f (y⁻¹ * x)` of two integrable functions is integrable on `μ.prod μ`. -/
theorem Integrable.smul_comp_inv_mul_prod {h : G → 𝕜} (hh : Integrable h μ) {f : G → E}
    (hf : Integrable f μ) :
    Integrable (fun q : G × G => h q.2 • f (q.2⁻¹ * q.1)) (μ.prod μ) := by
  have hmeas : AEStronglyMeasurable (fun q : G × G => h q.2 • f (q.2⁻¹ * q.1)) (μ.prod μ) :=
    (hh.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).smul
      hf.aestronglyMeasurable.comp_inv_mul_prod
  have hfy_int (y : G) : Integrable (fun x => f (y⁻¹ * x)) μ := hf.comp_mul_left y⁻¹
  refine (integrable_prod_iff' hmeas).2 ⟨.of_forall fun y => (hfy_int y).smul (h y), ?_⟩
  refine (hh.norm.mul_const (∫ x, ‖f x‖ ∂μ)).mono' hmeas.prod_swap.norm.integral_prod_right'
    (.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  exact (integral_norm_smul_le (h y) (hfy_int y)).trans_eq
    (by rw [integral_mul_left_eq_self (fun x => ‖f x‖) y⁻¹])

private theorem ae_integrable_smul_comp_inv_mul_of_sigmaCompact {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {h : G → 𝕜} (hh : Integrable h μ) {f : G → E} (hf : MemLp f p μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => h y • f (y⁻¹ * x)) μ := by
  have hspan (n : ℕ) : ∀ᵐ x ∂μ, x ∈ spanningSets μ n →
      Integrable (fun y => h y • f (y⁻¹ * x)) μ :=
    (ae_restrict_iff' (measurableSet_spanningSets μ n)).1
      (hh.smul_comp_inv_mul_restrict hf (measure_spanningSets_lt_top μ n)).prod_right_ae
  filter_upwards [ae_all_iff.2 hspan] with x hx
  obtain ⟨n, hn⟩ := mem_iUnion.1 ((iUnion_spanningSets μ).symm ▸ mem_univ x)
  exact hx n hn

end SigmaCompactFubini

section SigmaCompactConvolutionL

variable {G 𝕜 E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [SMulCommClass ℝ 𝕜 E] [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem convolutionL_ae_eq_of_sigmaCompact (hp : p ≠ ∞) (h : Lp 𝕜 1 μ) (f : Lp E p μ) :
    Lp.convolutionL μ p hp h f =ᵐ[μ] fun x => ∫ y, h y • f (y⁻¹ * x) ∂μ := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ hμs => ?_) (fun s _ hμs => ?_) fun s _ hμs => ?_
  · have _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
    exact ((Lp.memLp _).restrict s).integrable Fact.out
  · exact ((L1.integrable_coeFn h).smul_comp_inv_mul_restrict (Lp.memLp f) hμs).integral_prod_left
  · let S := Set.setIntegralLp (𝕜 := ℝ) (F := E) (p := p) s hμs
    have hint := Lp.integrable_smul_leftTranslation hp (L1.integrable_coeFn h) f
    calc ∫ x in s, Lp.convolutionL μ p hp h f x ∂μ
        = S (Lp.convolutionL μ p hp h f) := (Set.setIntegralLp_apply s hμs _).symm
      _ = ∫ y, ∫ x in s, h y • f (y⁻¹ * x) ∂μ ∂μ := by
          rw [Lp.convolutionL_apply, ← S.integral_comp_comm hint]
          refine integral_congr_ae (.of_forall fun y => ?_)
          dsimp only
          rw [Set.setIntegralLp_apply]
          refine integral_congr_ae (ae_restrict_of_ae ?_)
          filter_upwards [Lp.coeFn_smul (h y) (Lp.leftTranslation μ p 𝕜 y f),
            Lp.coeFn_leftTranslation (𝕜 := 𝕜) y f] with x hx₁ hx₂
          rw [hx₁, Pi.smul_apply, hx₂]
      _ = ∫ x in s, (∫ y, h y • f (y⁻¹ * x) ∂μ) ∂μ :=
          (integral_integral_swap
            ((L1.integrable_coeFn h).smul_comp_inv_mul_restrict (Lp.memLp f) hμs)).symm

end SigmaCompactConvolutionL

/-! ### Arbitrary locally compact Hausdorff groups via σ-compact open subgroups -/

section LocallyCompact

variable {G 𝕜 E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]

omit [μ.IsHaarMeasure] in
/-- Simultaneously enclose an integrable function `h` and an `Lᵖ` function `f` (`1 ≤ p < ∞`) inside
a single σ-compact open subgroup outside which both vanish `μ`-almost everywhere. -/
private theorem exists_openSubgroup_isSigmaCompact_ae_eq_zero_pair
    [NormedAddCommGroup 𝕜] [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {h : G → 𝕜} (hh : Integrable h μ) {f : G → E} (hf : MemLp f p μ) :
    ∃ H : OpenSubgroup G, IsSigmaCompact (H : Set G) ∧
      h =ᵐ[μ.restrict (H : Set G)ᶜ] 0 ∧ f =ᵐ[μ.restrict (H : Set G)ᶜ] 0 := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  let F : Bool → G → ℝ := fun b => if b then (fun x => ‖h x‖) else (fun x => ‖f x‖)
  have hF (b : Bool) : AEFinStronglyMeasurable (F b) μ := by
    cases b
    · exact hf.norm.aefinStronglyMeasurable hp₀ hp
    · exact hh.norm.aefinStronglyMeasurable
  obtain ⟨H, hH, hFH⟩ := exists_openSubgroup_isSigmaCompact_forall_ae_eq_zero hF
  refine ⟨H, hH, ?_, ?_⟩
  · filter_upwards [hFH true] with x hx
    exact norm_eq_zero.1 hx
  · filter_upwards [hFH false] with x hx
    exact norm_eq_zero.1 hx

/-- **Almost-everywhere integrability of the pointwise convolution integrand.** On any locally
compact Hausdorff group with a regular Haar measure `μ` (without σ-compactness or second
countability), if `h` is integrable and `f ∈ Lᵖ(G, μ)` (`1 ≤ p ≤ ∞`), then for `μ`-almost every
`x : G` the function `y ↦ h y • f (y⁻¹ * x)` is `μ`-integrable. -/
theorem Integrable.ae_integrable_smul_comp_inv_mul [NormedRing 𝕜] [NormedAddCommGroup E]
    [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {h : G → 𝕜} (hh : Integrable h μ) {f : G → E} (hf : MemLp f p μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => h y • f (y⁻¹ * x)) μ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · exact .of_forall fun x => hh.smul_of_top_left
      (hf.comp_quasiMeasurePreserving_top (Measure.quasiMeasurePreserving_inv_mul_of_regular μ x))
  obtain ⟨H, hH, hh_off, hf_off⟩ := exists_openSubgroup_isSigmaCompact_ae_eq_zero_pair hp hh hf
  have hH_meas : MeasurableSet (H : Set G) := H.isOpen.measurableSet
  have _ : SigmaCompactSpace H := isSigmaCompact_iff_sigmaCompactSpace.1 hH
  let ν : Measure H := μ.comap ((↑) : H → G)
  have hh₀ : Integrable (fun u : H => h u) ν :=
    (integrable_iff_comap_subtypeVal_of_ae_eq_zero hH_meas hh_off).1 hh
  have hf₀ : MemLp (fun u : H => f u) p ν :=
    (memLp_iff_comap_subtypeVal_of_ae_eq_zero hH_meas hf_off).1 hf
  refine ae_of_ae_restrict_of_ae_restrict_compl (H : Set G) ?_ ?_
  · refine (ae_restrict_iff_subtype hH_meas).2 ?_
    filter_upwards [ae_integrable_smul_comp_inv_mul_of_sigmaCompact hh₀ hf₀] with u hu
    exact (integrable_iff_comap_subtypeVal_of_ae_eq_zero hH_meas
      (H.ae_restrict_compl_smul_inv_mul_eq_zero hh_off f (u : G))).2 hu
  · refine (ae_restrict_iff' hH_meas.compl).2 (.of_forall fun x hx => ?_)
    exact (integrable_zero G E μ).congr (H.ae_smul_inv_mul_eq_zero_of_notMem hh_off hf_off hx).symm

namespace Lp

section PointwiseConvolutionL

/-- On a locally compact Hausdorff group `G` with a regular Haar measure `μ`, for
`h ∈ L¹(G, μ; 𝕜)` and `f ∈ Lᵖ(G, μ; E)` (`1 ≤ p ≤ ∞`), the convolution integrand
`y ↦ h y • f (y⁻¹ * x)` is `μ`-integrable for `μ`-almost every `x : G`. -/
theorem ae_integrable_smul_comp_inv_mul [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (h : Lp 𝕜 1 μ) (f : Lp E p μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => h y • f (y⁻¹ * x)) μ :=
  (L1.integrable_coeFn h).ae_integrable_smul_comp_inv_mul (Lp.memLp f)

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [SMulCommClass ℝ 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Pointwise representation of `Lp.convolutionL` on arbitrary locally compact Hausdorff groups.**
On a locally compact Hausdorff group `G` with a regular Haar measure `μ` (without σ-compactness or
second countability), for `1 ≤ p < ∞`, `h ∈ L¹(G, μ; 𝕜)`, and `f ∈ Lᵖ(G, μ; E)`, the operator
convolution `convolutionL μ p hp h f` agrees `μ`-almost everywhere with the pointwise Bochner
integral `x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ`. -/
theorem convolutionL_ae_eq {hp : p ≠ ∞} (h : Lp 𝕜 1 μ) (f : Lp E p μ) :
    convolutionL μ p hp h f =ᵐ[μ] fun x => ∫ y, h y • f (y⁻¹ * x) ∂μ := by
  by_cases hE : CompleteSpace E
  swap
  · have hzero : convolutionL μ p hp h f = 0 := by
      rcases subsingleton_or_nontrivial (Lp E p μ) with _ | _
      · exact Subsingleton.elim _ _
      · have hLp : ¬CompleteSpace (Lp E p μ) :=
          fun _ => hE (completeSpace_of_completeSpace_Lp E p μ)
        rw [convolutionL_apply, integral_of_not_completeSpace hLp]
    simpa only [hzero, integral_of_not_completeSpace hE, Pi.zero_def] using Lp.coeFn_zero E p μ
  obtain ⟨H, hH, hh_off, hf_off⟩ :=
    exists_openSubgroup_isSigmaCompact_ae_eq_zero_pair hp (L1.integrable_coeFn h) (Lp.memLp f)
  have hH_meas : MeasurableSet (H : Set G) := H.isOpen.measurableSet
  have _ : SigmaCompactSpace H := isSigmaCompact_iff_sigmaCompactSpace.1 hH
  let ν : Measure H := μ.comap ((↑) : H → G)
  let h₀ : Lp 𝕜 1 ν := restrictComapCLM 𝕜 μ 1 hH_meas h
  let f₀ : Lp E p ν := restrictComapCLM 𝕜 μ p hH_meas f
  have hconv_ext : convolutionL μ p hp h f =
      extendByZeroComapₗᵢ 𝕜 μ hH_meas (convolutionL ν p hp h₀ f₀) := by
    rw [extendByZeroComapₗᵢ_convolutionL,
      extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero hH_meas hh_off,
      extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero hH_meas hf_off]
  rw [hconv_ext]
  refine ae_of_ae_restrict_of_ae_restrict_compl (H : Set G) ?_ ?_
  · refine (ae_restrict_iff_subtype hH_meas).2 ?_
    filter_upwards [coeFn_extendByZeroComapₗᵢ_comp_subtype (𝕜 := 𝕜) hH_meas
        (convolutionL ν p hp h₀ f₀),
      convolutionL_ae_eq_of_sigmaCompact hp h₀ f₀] with u hu₁ hu₂
    rw [Function.comp_apply] at hu₁
    rw [hu₁, hu₂,
      integral_convolution_eq_comap_of_ae_restrict_compl_eq_zero hH_meas hh_off (⇑f) (u : G)]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_restrictComapCLM (𝕜 := 𝕜) hH_meas h,
      (Measure.quasiMeasurePreserving_inv_mul_of_regular ν u).ae
        (coeFn_restrictComapCLM (𝕜 := 𝕜) hH_meas f)] with v hv_h hv_f
    simp only [Function.comp_apply] at hv_h hv_f
    rw [hv_h, hv_f, MulMemClass.coe_mul, InvMemClass.coe_inv]
  · filter_upwards [coeFn_extendByZeroComapₗᵢ_restrict_compl (𝕜 := 𝕜) hH_meas
        (convolutionL ν p hp h₀ f₀),
      ae_restrict_mem hH_meas.compl] with x hx₁ hxH
    rw [hx₁, Pi.zero_apply, H.integral_smul_inv_mul_eq_zero_of_notMem hh_off hf_off hxH]

/-- On a locally compact Hausdorff group `G` with a regular Haar measure `μ`, `Lp.convolutionL`
applied to `(hh.toL1 h)` and `(hf.toLp f)` for an integrable function `h` and an `Lᵖ` function `f`
(`1 ≤ p < ∞`) is represented `μ`-almost everywhere by `x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ`. -/
theorem convolutionL_toLp_ae_eq {hp : p ≠ ∞} {h : G → 𝕜} (hh : Integrable h μ) {f : G → E}
    (hf : MemLp f p μ) :
    convolutionL μ p hp (hh.toL1 h) (hf.toLp f) =ᵐ[μ] fun x => ∫ y, h y • f (y⁻¹ * x) ∂μ := by
  filter_upwards [convolutionL_ae_eq (hp := hp) (hh.toL1 h) (hf.toLp f)] with x hx
  refine hx.trans (integral_congr_ae ?_)
  filter_upwards [hh.coeFn_toL1,
    (Measure.quasiMeasurePreserving_inv_mul_of_regular μ x).ae hf.coeFn_toLp] with y hy_h hy_f
  rw [hy_h, hy_f]

end PointwiseConvolutionL

end Lp

section FunctionConsequences

/-- On a locally compact Hausdorff group `G` with a regular Haar measure `μ`, `Lp.convolutionL`
applied to `(hh.toL1 h)` and `(hf.toL1 f)` agrees `μ`-almost everywhere with
`x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ` for any two `μ`-integrable functions `h` and `f`, trading the
continuity and compact-support hypotheses of `MeasureTheory.Lp.convolutionL_toL1_ae_eq` for local
compactness, Hausdorffness, and a regular Haar measure. -/
theorem Integrable.convolutionL_toL1_ae_eq [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]
    {h : G → 𝕜} (hh : Integrable h μ) {f : G → E} (hf : Integrable f μ) :
    Lp.convolutionL μ 1 ENNReal.one_ne_top (hh.toL1 h) (hf.toL1 f) =ᵐ[μ]
      fun x => ∫ y, h y • f (y⁻¹ * x) ∂μ := by
  have htoLp : (memLp_one_iff_integrable.2 hf).toLp f = hf.toL1 f :=
    Lp.ext <| (MemLp.coeFn_toLp _).trans hf.coeFn_toL1.symm
  exact htoLp ▸ Lp.convolutionL_toLp_ae_eq hh (memLp_one_iff_integrable.2 hf)

/-- On a locally compact Hausdorff group with a regular Haar measure `μ`, the pointwise group
convolution `x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ` of `h ∈ L¹(G, μ; 𝕜)` and `f ∈ Lᵖ(G, μ; E)` (`1 ≤ p < ∞`)
belongs to `Lᵖ(G, μ; E)`. -/
theorem Integrable.memLp_integral_smul_comp_inv_mul [NormedRing 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {h : G → 𝕜} (hh : Integrable h μ) {f : G → E} (hf : MemLp f p μ) :
    MemLp (fun x => ∫ y, h y • f (y⁻¹ * x) ∂μ) p μ := by
  by_cases hE : CompleteSpace E
  swap
  · simp [integral_of_not_completeSpace hE]
  obtain ⟨H, hH, hh_off, hf_off⟩ := exists_openSubgroup_isSigmaCompact_ae_eq_zero_pair hp hh hf
  have hH_meas : MeasurableSet (H : Set G) := H.isOpen.measurableSet
  have _ : SigmaCompactSpace H := isSigmaCompact_iff_sigmaCompactSpace.1 hH
  let ν : Measure H := μ.comap ((↑) : H → G)
  have hh₀ : Integrable (fun u : H => h u) ν :=
    (integrable_iff_comap_subtypeVal_of_ae_eq_zero hH_meas hh_off).1 hh
  have hf₀ : MemLp (fun u : H => f u) p ν :=
    (memLp_iff_comap_subtypeVal_of_ae_eq_zero hH_meas hf_off).1 hf
  have hmeas_H : AEStronglyMeasurable (fun u : H => ∫ y, h y • f (y⁻¹ * (u : G)) ∂μ) ν := by
    simp_rw [H.integral_smul_inv_mul_coe_eq_comap hh_off f]
    exact ((hh₀.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd).smul
        hf₀.aestronglyMeasurable.comp_inv_mul_prod).integral_prod_right'
  have hmeas : AEStronglyMeasurable (fun x => ∫ y, h y • f (y⁻¹ * x) ∂μ) μ :=
    (aestronglyMeasurable_iff_comap_subtypeVal_of_ae_eq_zero hH_meas
      (H.ae_restrict_compl_integral_smul_inv_mul_eq_zero hh_off hf_off)).2 hmeas_H
  have hreal : MemLp (fun x => ∫ y, ‖h y‖ * ‖f (y⁻¹ * x)‖ ∂μ) p μ :=
    (Lp.memLp (Lp.convolutionL μ p hp (hh.norm.toL1 _) (hf.norm.toLp _))).ae_eq
      (Lp.convolutionL_toLp_ae_eq (𝕜 := ℝ) (E := ℝ) hh.norm hf.norm)
  refine hreal.mono' hmeas ?_
  filter_upwards [hh.norm.ae_integrable_smul_comp_inv_mul hf.norm] with x hxint
  exact norm_integral_le_of_norm_le hxint (.of_forall fun _ => norm_smul_le _ _)

/-- On a locally compact Hausdorff group with a regular Haar measure `μ`, the pointwise group
convolution `x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ` of two integrable functions is integrable. -/
theorem Integrable.integral_smul_comp_inv_mul [NormedRing 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    {h : G → 𝕜} (hh : Integrable h μ) {f : G → E} (hf : Integrable f μ) :
    Integrable (fun x => ∫ y, h y • f (y⁻¹ * x) ∂μ) μ :=
  memLp_one_iff_integrable.1 <| hh.memLp_integral_smul_comp_inv_mul ENNReal.one_ne_top
    (memLp_one_iff_integrable.2 hf)

/-- **Integral of a pointwise group convolution.** On any locally compact Hausdorff group with a
regular Haar measure `μ`, `∫ x, (∫ y, h y • f (y⁻¹ * x) ∂μ) ∂μ = (∫ x, h x ∂μ) • ∫ x, f x ∂μ` for
integrable `h` and `f`. -/
theorem integral_integral_smul_comp_inv_mul [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E] {h : G → 𝕜} (hh : Integrable h μ)
    {f : G → E} (hf : Integrable f μ) :
    ∫ x, (∫ y, h y • f (y⁻¹ * x) ∂μ) ∂μ = (∫ x, h x ∂μ) • ∫ x, f x ∂μ := by
  rw [← integral_congr_ae (hh.convolutionL_toL1_ae_eq hf), Lp.integral_convolutionL,
    integral_congr_ae hh.coeFn_toL1, integral_congr_ae hf.coeFn_toL1]

end FunctionConsequences

end LocallyCompact

end MeasureTheory
