/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1

/-!
# Conditional expectation on `L¹` for arbitrary measures

Mathlib's conditional expectation `MeasureTheory.condExpL1CLM` on `L¹(μ)` with respect to a
sub-σ-algebra `m` requires the trimmed measure `μ.trim hm` to be σ-finite. This file constructs the
conditional expectation `TauCeti.condExpL1Proj G hm μ` on `L¹(μ; G)` for an arbitrary measure
`μ` and an arbitrary sub-σ-algebra `m ≤ m0`, with values in a real Banach space `G`.

The starting point is the orthogonal projection `MeasureTheory.condExpL2` of `L²(μ)` onto the
`m`-measurable classes. Mathlib bounds its `L¹` norm on every `m`-measurable set of finite measure.
An `m`-measurable class in `L²(μ)` vanishes off an `m`-measurable set on which the trimmed measure
is σ-finite, so these local bounds give the global contraction
`∫⁻ ‖condExpL2 f‖ₑ ≤ ∫⁻ ‖f‖ₑ` (`TauCeti.lintegral_eNorm_condExpL2_le`). In particular the projection
of the indicator of a set of finite measure is integrable, with `L¹` norm at most the measure of the
set. As in Mathlib's construction of `condExpL1CLM`, the projection of indicators then extends by
`MeasureTheory.L1.setToL1` to a contraction of `L¹(μ; G)`.

The result is the unique continuous linear map of `L¹(μ; G)` that takes values in `m`-measurable
classes and preserves integrals over `m`-measurable sets of *finite measure*
(`TauCeti.condExpL1Proj_eq_iff`). Integrals over `m`-measurable sets of infinite measure need not be
preserved: for Lebesgue measure on `ℝ` and the trivial σ-algebra, the only integrable constant is
zero, so the projection vanishes (`TauCeti.condExpL1Proj_bot`), although the integral of the
indicator of `[0, 1]` over `ℝ` is one. When `μ.trim hm` is σ-finite the projection is Mathlib's
`condExpL1CLM` (`TauCeti.condExpL1Proj_eq_condExpL1CLM`), and on real classes in `L¹ ∩ L²` it agrees
with the `L²` projection (`TauCeti.condExpL1Proj_toL1_ae_eq_condExpL2`).

## Main definitions

* `TauCeti.condExpL1Proj G hm μ`: the conditional expectation `L¹(μ; G) →L[ℝ] L¹(μ; G)` with
  respect to `m ≤ m0`, for an arbitrary measure `μ`.

## Main results

* `TauCeti.lintegral_eNorm_condExpL2_le`: the `L²` projection contracts the `L¹` seminorm.
* `TauCeti.norm_condExpL1Proj_le`: the conditional expectation is a contraction.
* `TauCeti.setIntegral_condExpL1Proj` and `TauCeti.aestronglyMeasurable_condExpL1Proj`: it preserves
  integrals over `m`-measurable sets of finite measure and takes values in `m`-measurable classes.
* `TauCeti.condExpL1Proj_eq_iff`: these two properties characterize it.
* `TauCeti.condExpL1Proj_of_aestronglyMeasurable`, `TauCeti.condExpL1Proj_condExpL1Proj` and
  `TauCeti.range_condExpL1Proj`: it is a projection onto the `m`-measurable classes.
* `TauCeti.condExpL1Proj_nonneg`, `TauCeti.condExpL1Proj_mono` and `TauCeti.abs_condExpL1Proj_le`:
  positivity and the modulus inequality for real classes.
* `TauCeti.condExpL1Proj_condExpL1Proj_of_le`: the tower property for nested σ-algebras.
* `TauCeti.condExpL1Proj_eq_condExpL1CLM`: agreement with Mathlib's conditional expectation when the
  trimmed measure is σ-finite.
* `TauCeti.condExpL1Proj_toL1_ae_eq_condExpL2`: agreement with the `L²` projection on `L¹ ∩ L²`.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Springer, 2016, §1.3, pp. 50–51 (conditional expectations on arbitrary measure spaces).
* The extension from indicators follows Mathlib's construction of `MeasureTheory.condExpL1CLM` in
  `Mathlib/MeasureTheory/Function/ConditionalExpectation/CondexpL1.lean`.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}

section Contraction

/-- If a function is finitely strongly measurable for the trimmed measure `μ.trim hm` and its
lower `L¹` integrals over the `m`-measurable sets of finite `μ`-measure are bounded by `C`, then
its lower `L¹` integral over the whole space is bounded by `C`. The trimmed measure need not be
σ-finite. -/
theorem lintegral_eNorm_le_of_forall_fin_meas_trim_le {E : Type*} [NormedAddCommGroup E]
    (hm : m ≤ m0) {g : α → E} (hg : FinStronglyMeasurable g (μ.trim hm)) (C : ℝ≥0∞)
    (hC : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, ‖g x‖ₑ ∂μ ≤ C) :
    ∫⁻ x, ‖g x‖ₑ ∂μ ≤ C := by
  obtain ⟨t, ht, hgt, htμ⟩ := hg.exists_set_sigmaFinite
  have : SigmaFinite ((μ.restrict t).trim hm) := by rwa [← restrict_trim hm μ ht]
  rw [← setLIntegral_eq_of_support_subset (s := t) fun x hx => by_contra fun hxt => hx (by
    simp [hgt x hxt])]
  refine lintegral_le_of_forall_fin_meas_trim_le hm C fun s hs hμs => ?_
  rw [Measure.restrict_restrict (hm s hs)]
  rw [Measure.restrict_apply (hm s hs)] at hμs
  exact hC _ (hs.inter ht) hμs

/-- **The `L²` conditional expectation contracts the `L¹` seminorm**, for an arbitrary measure and
an arbitrary sub-σ-algebra. This is the global form of Mathlib's
`MeasureTheory.lintegral_nnNorm_condExpL2_le` on `m`-measurable sets of finite measure. -/
theorem lintegral_eNorm_condExpL2_le (hm : m ≤ m0) (f : Lp ℝ 2 μ) :
    ∫⁻ x, ‖(condExpL2 ℝ ℝ hm f : α → ℝ) x‖ₑ ∂μ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := by
  obtain ⟨g, hg, hfg⟩ :=
    lpMeas.ae_fin_strongly_measurable' hm (condExpL2 ℝ ℝ hm f) two_ne_zero ENNReal.ofNat_ne_top
  have hfg' : (fun x => ‖(condExpL2 ℝ ℝ hm f : α → ℝ) x‖ₑ) =ᵐ[μ] fun x => ‖g x‖ₑ :=
    hfg.mono fun x hx => by simp only [hx]
  rw [lintegral_congr_ae hfg']
  refine lintegral_eNorm_le_of_forall_fin_meas_trim_le hm hg _ fun s hs hμs => ?_
  calc ∫⁻ x in s, ‖g x‖ₑ ∂μ = ∫⁻ x in s, ‖(condExpL2 ℝ ℝ hm f : α → ℝ) x‖ₑ ∂μ :=
        (lintegral_congr_ae (ae_restrict_of_ae hfg')).symm
    _ ≤ ∫⁻ x in s, ‖f x‖ₑ ∂μ := by
        simpa only [eNorm_eq_nnNorm] using lintegral_nnNorm_condExpL2_le hs hμs f
    _ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := setLIntegral_le_lintegral _ _

/-- The `L²` conditional expectation of an integrable class in `L²(μ)` is integrable, for an
arbitrary measure and an arbitrary sub-σ-algebra. -/
theorem integrable_condExpL2_of_integrable (hm : m ≤ m0) {f : Lp ℝ 2 μ} (hf : Integrable f μ) :
    Integrable (condExpL2 ℝ ℝ hm f : α → ℝ) μ :=
  ⟨Lp.aestronglyMeasurable _, (lintegral_eNorm_condExpL2_le hm f).trans_lt hf.2⟩

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The `L²` conditional expectation of the indicator `𝟙_s x` of a measurable set of finite measure
has `L¹` seminorm at most `μ s * ‖x‖ₑ`, for an arbitrary measure and an arbitrary sub-σ-algebra. -/
theorem lintegral_eNorm_condExpIndSMul_le (hm : m ≤ m0) {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : G) :
    ∫⁻ a, ‖condExpIndSMul hm hs hμs x a‖ₑ ∂μ ≤ μ s * ‖x‖ₑ := by
  have hind : ∫⁻ a, ‖indicatorConstLp 2 hs hμs (1 : ℝ) a‖ₑ ∂μ = μ s := by
    rw [lintegral_congr_ae ((indicatorConstLp_coeFn (p := 2)).mono fun a ha => by rw [ha])]
    simp [eNorm_indicator_eq_indicator_eNorm, lintegral_indicator hs]
  calc ∫⁻ a, ‖condExpIndSMul hm hs hμs x a‖ₑ ∂μ
      = ∫⁻ a, ‖(condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a‖ₑ * ‖x‖ₑ ∂μ :=
        lintegral_congr_ae ((condExpIndSMul_ae_eq_smul hm hs hμs x).mono fun a ha => by
          simp only [ha, eNorm_smul])
    _ = (∫⁻ a, ‖(condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a‖ₑ ∂μ) * ‖x‖ₑ :=
        lintegral_mul_const' _ _ eNorm_ne_top
    _ ≤ μ s * ‖x‖ₑ := by grw [lintegral_eNorm_condExpL2_le hm, hind]

end Contraction

section Uniqueness

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Two integrable `m`-measurable functions with the same integrals over all `m`-measurable sets of
finite measure agree almost everywhere. The trimmed measure `μ.trim hm` need not be σ-finite. -/
theorem ae_eq_of_forall_setIntegral_eq_of_aestronglyMeasurable (hm : m ≤ m0) {f g : α → G}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfm : AEStronglyMeasurable[m] f μ)
    (hgm : AEStronglyMeasurable[m] g μ)
    (hfg : ∀ s, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
    f =ᵐ[μ] g := by
  have hf' := (hf.congr hfm.ae_eq_mk).trim hm hfm.stronglyMeasurable_mk
  have hg' := (hg.congr hgm.ae_eq_mk).trim hm hgm.stronglyMeasurable_mk
  refine hfm.ae_eq_mk.trans ((ae_eq_of_ae_eq_trim (Integrable.ae_eq_of_forall_setIntegral_eq _ _
    hf' hg' fun s hs hμs => ?_)).trans hgm.ae_eq_mk.symm)
  rw [trim_measurableSet_eq hm hs] at hμs
  rw [← setIntegral_trim hm hfm.stronglyMeasurable_mk hs,
    ← setIntegral_trim hm hgm.stronglyMeasurable_mk hs,
    ← setIntegral_congr_ae (hm s hs) (hfm.ae_eq_mk.mono fun x hx _ => hx),
    ← setIntegral_congr_ae (hm s hs) (hgm.ae_eq_mk.mono fun x hx _ => hx), hfg s hs hμs]

end Uniqueness

section Indicator

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The `L²` conditional expectation of the indicator `𝟙_s x` of a measurable set of finite measure
is integrable, for an arbitrary measure and an arbitrary sub-σ-algebra. -/
theorem integrable_condExpIndSMul_of_le (hm : m ≤ m0) {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : G) : Integrable (condExpIndSMul hm hs hμs x) μ :=
  ⟨Lp.aestronglyMeasurable _,
    (lintegral_eNorm_condExpIndSMul_le hm hs hμs x).trans_lt (by finiteness)⟩

/-- The conditional expectation of `𝟙_s x`, as a continuous linear map of `x` into `L¹`, for a
measurable set `s` of finite measure. -/
private def condExpL1ProjIndFin (hm : m ≤ m0) {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) : G →L[ℝ] α →₁[μ] G :=
  LinearMap.mkContinuous
    { toFun x := (integrable_condExpIndSMul_of_le hm hs hμs x).toL1 _
      map_add' x y := by
        rw [← Integrable.toL1_add, Integrable.toL1_eq_toL1_iff, condExpIndSMul_add]
        exact Lp.coeFn_add _ _
      map_smul' c x := by
        rw [RingHom.id_apply, ← Integrable.toL1_smul', Integrable.toL1_eq_toL1_iff,
          condExpIndSMul_smul]
        exact Lp.coeFn_smul _ _ }
    (μ.real s) fun x => by
      rw [LinearMap.coe_mk, AddHom.coe_mk, Integrable.norm_toL1, measureReal_def,
        ← toReal_eNorm, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (by finiteness) <| by
        simpa only [edist_zero_right] using lintegral_eNorm_condExpIndSMul_le hm hs hμs x

private theorem condExpL1ProjIndFin_ae_eq (hm : m ≤ m0) {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : G) :
    condExpL1ProjIndFin hm hs hμs x =ᵐ[μ] condExpIndSMul hm hs hμs x :=
  (integrable_condExpIndSMul_of_le hm hs hμs x).coeFn_toL1

open scoped Classical in
/-- The conditional expectation of indicators, as a set function with values in continuous linear
maps into `L¹`. Its value on sets that are not measurable or have infinite measure is zero. -/
private def condExpL1ProjInd (hm : m ≤ m0) (μ : Measure α) (s : Set α) : G →L[ℝ] α →₁[μ] G :=
  if hs : MeasurableSet s ∧ μ s ≠ ∞ then condExpL1ProjIndFin hm hs.1 hs.2 else 0

private theorem condExpL1ProjInd_ae_eq (hm : m ≤ m0) {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : G) :
    condExpL1ProjInd hm μ s x =ᵐ[μ] condExpIndSMul hm hs hμs x := by
  simpa [condExpL1ProjInd, hs, hμs] using condExpL1ProjIndFin_ae_eq hm hs hμs x

private theorem dominatedFinMeasAdditive_condExpL1ProjInd (hm : m ≤ m0) (μ : Measure α) :
    DominatedFinMeasAdditive μ (condExpL1ProjInd (G := G) hm μ) 1 := by
  refine ⟨fun s t hs ht hμs hμt hst => ?_, fun s hs hμs => ?_⟩
  · have hμst : μ (s ∪ t) ≠ ∞ := measure_union_ne_top hμs hμt
    ext1 x
    refine Lp.ext ?_
    grw [add_apply, Lp.coeFn_add, condExpL1ProjInd_ae_eq hm hs hμs,
      condExpL1ProjInd_ae_eq hm ht hμt, condExpL1ProjInd_ae_eq hm (hs.union ht) hμst]
    rw [condExpIndSMul, condExpIndSMul, condExpIndSMul,
      indicatorConstLp_disjoint_union hs ht hμs hμt hst (1 : ℝ), map_add, Submodule.coe_add,
      map_add]
    exact Lp.coeFn_add _ _
  · simp only [one_mul, condExpL1ProjInd, hs, hμs.ne, ne_eq, not_false_eq_true, and_self,
      ↓reduceDIte]
    exact LinearMap.mkContinuous_norm_le _ measureReal_nonneg _

end Indicator

section Projection

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

variable (G) in
/-- The **conditional expectation on `L¹(μ; G)`** with respect to a sub-σ-algebra `m ≤ m0`, for an
arbitrary measure `μ`. It is the unique continuous linear map that takes values in `m`-measurable
classes and preserves integrals over `m`-measurable sets of finite measure
(`TauCeti.condExpL1Proj_eq_iff`). When `μ.trim hm` is σ-finite it is Mathlib's
`MeasureTheory.condExpL1CLM` (`TauCeti.condExpL1Proj_eq_condExpL1CLM`). -/
def condExpL1Proj (hm : m ≤ m0) (μ : Measure α) : (α →₁[μ] G) →L[ℝ] α →₁[μ] G :=
  L1.setToL1 (dominatedFinMeasAdditive_condExpL1ProjInd hm μ)

variable {hm : m ≤ m0}

/-- The conditional expectation of the indicator `𝟙_s x` of a measurable set of finite measure is
the `L²` conditional expectation of the indicator of `s`, multiplied by `x`. -/
theorem condExpL1Proj_indicatorConstLp {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) :
    condExpL1Proj G hm μ (indicatorConstLp 1 hs hμs x) =ᵐ[μ] condExpIndSMul hm hs hμs x := by
  rw [condExpL1Proj, L1.setToL1_indicatorConstLp]
  exact condExpL1ProjInd_ae_eq hm hs hμs x

/-- The conditional expectation on `L¹` is a contraction. -/
theorem norm_condExpL1Proj_le : ‖condExpL1Proj G hm μ‖ ≤ 1 :=
  L1.norm_setToL1_le _ zero_le_one

/-- The conditional expectation on `L¹` does not increase the norm. -/
theorem norm_condExpL1Proj_apply_le (f : α →₁[μ] G) : ‖condExpL1Proj G hm μ f‖ ≤ ‖f‖ :=
  ((condExpL1Proj G hm μ).le_opNorm f).trans
    (mul_le_of_le_one_left (norm_nonneg f) norm_condExpL1Proj_le)

/-- The conditional expectation on `L¹` takes values in `m`-measurable classes. -/
theorem aestronglyMeasurable_condExpL1Proj (f : α →₁[μ] G) :
    AEStronglyMeasurable[m] (condExpL1Proj G hm μ f) μ := by
  induction f using Lp.induction ENNReal.one_ne_top with
  | indicatorConst c hs hμs =>
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact (aestronglyMeasurable_condExpIndSMul hm hs hμs.ne c).congr
      (condExpL1Proj_indicatorConstLp hs hμs.ne c).symm
  | add hf hg _ hfm hgm =>
    rw [(condExpL1Proj G hm μ).map_add]
    exact (hfm.add hgm).congr (Lp.coeFn_add ..).symm
  | isClosed =>
    exact (isClosed_aestronglyMeasurable hm).preimage (condExpL1Proj G hm μ).continuous

/-- The conditional expectation on `L¹` preserves integrals over `m`-measurable sets of finite
measure. Integrals over `m`-measurable sets of infinite measure need not be preserved; see
`TauCeti.condExpL1Proj_bot`. -/
theorem setIntegral_condExpL1Proj (f : α →₁[μ] G) {s : Set α} (hs : MeasurableSet[m] s)
    (hμs : μ s ≠ ∞) : ∫ x in s, condExpL1Proj G hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  induction f using Lp.induction ENNReal.one_ne_top with
  | indicatorConst c ht hμt =>
    rw [Lp.simpleFunc.coe_indicatorConst, setIntegral_indicatorConstLp (hm s hs),
      setIntegral_congr_ae (hm s hs)
        ((condExpL1Proj_indicatorConstLp ht hμt.ne c).mono fun x hx _ => hx)]
    exact setIntegral_condExpIndSMul hs ht hμs hμt.ne c
  | add hf hg _ hfP hgP =>
    rw [(condExpL1Proj G hm μ).map_add,
      setIntegral_congr_ae (hm s hs) ((Lp.coeFn_add _ _).mono fun x hx _ => hx),
      setIntegral_congr_ae (hm s hs) ((Lp.coeFn_add _ _).mono fun x hx _ => hx), Pi.add_def,
      Pi.add_def, integral_add (L1.integrable_coeFn _).integrableOn
        (L1.integrable_coeFn _).integrableOn,
      integral_add (L1.integrable_coeFn _).integrableOn (L1.integrable_coeFn _).integrableOn,
      hfP, hgP]
  | isClosed =>
    exact isClosed_eq ((continuous_setIntegral s).comp (condExpL1Proj G hm μ).continuous)
      (continuous_setIntegral s)

/-- **Characterization of the conditional expectation on `L¹`**: `condExpL1Proj G hm μ f = g` if
and only if `g` is `m`-measurable and has the same integrals as `f` over all `m`-measurable sets of
finite measure. -/
theorem condExpL1Proj_eq_iff {f g : α →₁[μ] G} :
    condExpL1Proj G hm μ f = g ↔ AEStronglyMeasurable[m] g μ ∧
      ∀ s, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ := by
  refine ⟨?_, fun ⟨hg, hgf⟩ => Lp.ext ?_⟩
  · rintro rfl
    exact ⟨aestronglyMeasurable_condExpL1Proj f, fun s hs hμs =>
      setIntegral_condExpL1Proj f hs hμs.ne⟩
  · refine ae_eq_of_forall_setIntegral_eq_of_aestronglyMeasurable hm (L1.integrable_coeFn _)
      (L1.integrable_coeFn _) (aestronglyMeasurable_condExpL1Proj f) hg fun s hs hμs => ?_
    rw [setIntegral_condExpL1Proj f hs hμs.ne, hgf s hs hμs]

/-- The conditional expectation on `L¹` fixes the `m`-measurable classes. -/
theorem condExpL1Proj_of_aestronglyMeasurable {f : α →₁[μ] G}
    (hf : AEStronglyMeasurable[m] f μ) : condExpL1Proj G hm μ f = f :=
  condExpL1Proj_eq_iff.2 ⟨hf, fun _ _ _ => rfl⟩

/-- The conditional expectation on `L¹` is idempotent. -/
@[simp]
theorem condExpL1Proj_condExpL1Proj (f : α →₁[μ] G) :
    condExpL1Proj G hm μ (condExpL1Proj G hm μ f) = condExpL1Proj G hm μ f :=
  condExpL1Proj_of_aestronglyMeasurable (aestronglyMeasurable_condExpL1Proj f)

/-- The range of the conditional expectation on `L¹` is the closed subspace of `m`-measurable
classes. -/
theorem range_condExpL1Proj :
    LinearMap.range (condExpL1Proj G hm μ : (α →₁[μ] G) →ₗ[ℝ] α →₁[μ] G) = lpMeas G ℝ m 1 μ := by
  ext f
  refine ⟨?_, fun hf => ⟨f, condExpL1Proj_of_aestronglyMeasurable hf⟩⟩
  rintro ⟨g, rfl⟩
  exact aestronglyMeasurable_condExpL1Proj g

/-- The conditional expectation on `L¹` commutes with multiplication by scalars of any normed
division ring acting on `G` compatibly with the real scalars. -/
theorem condExpL1Proj_smul {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 G] [NormSMulClass 𝕜 G]
    [SMulCommClass ℝ 𝕜 G] (c : 𝕜) (f : α →₁[μ] G) :
    condExpL1Proj G hm μ (c • f) = c • condExpL1Proj G hm μ f := by
  refine condExpL1Proj_eq_iff.2 ⟨((aestronglyMeasurable_condExpL1Proj f).const_smul c).congr
    (Lp.coeFn_smul _ _).symm, fun s hs hμs => ?_⟩
  rw [setIntegral_congr_ae (hm s hs) ((Lp.coeFn_smul _ _).mono fun x hx _ => hx),
    setIntegral_congr_ae (hm s hs) ((Lp.coeFn_smul _ _).mono fun x hx _ => hx), Pi.smul_def,
    Pi.smul_def, integral_smul, integral_smul, setIntegral_condExpL1Proj f hs hμs.ne]

/-- **Tower property**: conditioning first on `m₂` and then on a smaller `m₁` is conditioning on
`m₁`. -/
theorem condExpL1Proj_condExpL1Proj_of_le {m₁ m₂ : MeasurableSpace α} (hm₁₂ : m₁ ≤ m₂)
    (hm₂ : m₂ ≤ m0) (f : α →₁[μ] G) :
    condExpL1Proj G (hm₁₂.trans hm₂) μ (condExpL1Proj G hm₂ μ f) =
      condExpL1Proj G (hm₁₂.trans hm₂) μ f := by
  refine condExpL1Proj_eq_iff.2 ⟨aestronglyMeasurable_condExpL1Proj f, fun s hs hμs => ?_⟩
  rw [setIntegral_condExpL1Proj f hs hμs.ne, setIntegral_condExpL1Proj f (hm₁₂ s hs) hμs.ne]

/-- When the trimmed measure `μ.trim hm` is σ-finite, the conditional expectation on `L¹` is
Mathlib's `MeasureTheory.condExpL1CLM`. -/
theorem condExpL1Proj_eq_condExpL1CLM [SigmaFinite (μ.trim hm)] :
    condExpL1Proj G hm μ = condExpL1CLM G hm μ := by
  ext1 f
  exact condExpL1Proj_eq_iff.2 ⟨aestronglyMeasurable_condExpL1CLM f, fun s hs _ =>
    setIntegral_condExpL1CLM f hs⟩

/-- For the trivial σ-algebra and a measure of infinite total mass, the conditional expectation on
`L¹` vanishes: the only integrable constant is zero. -/
theorem condExpL1Proj_bot (hμ : μ univ = ∞) : condExpL1Proj G bot_le μ = 0 := by
  ext1 f
  refine condExpL1Proj_eq_iff.2 ⟨?_, fun s hs hμs => ?_⟩
  · exact aestronglyMeasurable_const.congr (Lp.coeFn_zero ..).symm
  · rcases MeasurableSpace.measurableSet_bot_iff.1 hs with rfl | rfl
    · simp
    · exact absurd hμs (by simp [hμ])

end Projection

section Real

variable {hm : m ≤ m0}

/-- The conditional expectation on `L¹` agrees with the `L²` conditional expectation on real
classes in `L¹ ∩ L²`, for an arbitrary measure. -/
theorem condExpL1Proj_toL1_ae_eq_condExpL2 {f : Lp ℝ 2 μ} (hf : Integrable f μ) :
    condExpL1Proj ℝ hm μ (hf.toL1 f) =ᵐ[μ] condExpL2 ℝ ℝ hm f := by
  have hg := integrable_condExpL2_of_integrable hm hf
  have h : condExpL1Proj ℝ hm μ (hf.toL1 f) = hg.toL1 _ := by
    refine condExpL1Proj_eq_iff.2 ⟨(aestronglyMeasurable_condExpL2 hm f).congr
      hg.coeFn_toL1.symm, fun s hs hμs => ?_⟩
    rw [setIntegral_congr_ae (hm s hs) (hg.coeFn_toL1.mono fun x hx _ => hx),
      setIntegral_congr_ae (hm s hs) (hf.coeFn_toL1.mono fun x hx _ => hx)]
    exact integral_condExpL2_eq_of_fin_meas_real f hs hμs.ne
  rw [h]
  exact hg.coeFn_toL1

/-- The conditional expectation on real `L¹` is positive. -/
theorem condExpL1Proj_nonneg {f : α →₁[μ] ℝ} (hf : 0 ≤ f) : 0 ≤ condExpL1Proj ℝ hm μ f := by
  rw [← Lp.coeFn_nonneg] at hf ⊢
  obtain ⟨g, hg, hPg⟩ := aestronglyMeasurable_condExpL1Proj (hm := hm) f
  have hgi : Integrable g (μ.trim hm) := ((L1.integrable_coeFn _).congr hPg).trim hm hg
  refine (ae_le_of_ae_le_trim (ae_nonneg_of_forall_setIntegral_nonneg hgi fun s hs hμs => ?_)).trans
    hPg.symm.le
  rw [trim_measurableSet_eq hm hs] at hμs
  rw [← setIntegral_trim hm hg hs, ← setIntegral_congr_ae (hm s hs) (hPg.mono fun x hx _ => hx),
    setIntegral_condExpL1Proj f hs hμs.ne]
  exact setIntegral_nonneg_of_ae_restrict (ae_restrict_of_ae hf)

/-- The conditional expectation on real `L¹` is monotone. -/
theorem condExpL1Proj_mono {f g : α →₁[μ] ℝ} (hfg : f ≤ g) :
    condExpL1Proj ℝ hm μ f ≤ condExpL1Proj ℝ hm μ g := by
  rw [← sub_nonneg, ← map_sub]
  exact condExpL1Proj_nonneg (sub_nonneg.2 hfg)

/-- **Modulus inequality** for the conditional expectation on real `L¹`. -/
theorem abs_condExpL1Proj_le (f : α →₁[μ] ℝ) :
    |condExpL1Proj ℝ hm μ f| ≤ condExpL1Proj ℝ hm μ |f| :=
  abs_le'.2 ⟨condExpL1Proj_mono (le_abs_self f), by
    rw [← map_neg]; exact condExpL1Proj_mono (neg_le_abs f)⟩

end Real

end TauCeti
