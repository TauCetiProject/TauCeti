/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.KFunctional
public import TauCeti.Analysis.Normed.Interpolation.Lebesgue
public import TauCeti.MeasureTheory.Function.DecreasingRearrangement
public import TauCeti.MeasureTheory.Function.Lp.L1AddLinfty

/-!
# The `K`-functional of the couple `(L¹, L^∞)`

For the compatible couple `(L¹(μ; E), L^∞(μ; E))` (`TauCeti.CompatibleCouple.l1Linfty`) and
`t ≥ 0`, Peetre's `K`-functional of an element `u` of `L¹ + L^∞` represented by a function `f` is
the integral of the decreasing rearrangement of `‖f‖` over `(0, t]`:

`K(t, u) = ∫₀ᵗ ‖f‖*`

(`TauCeti.CompatibleCouple.ofReal_kFunctional_l1Linfty`,
`TauCeti.CompatibleCouple.kFunctional_l1Linfty`). This is the formula
`MeasureTheory.Measure.lintegral_decreasingRearrangement_enorm_eq_iInf_eLpNorm`, which is stated
for arbitrary splittings `f = f₀ + f₁` measured by `Lᵖ` seminorms, transported to the
decompositions of `u` in the sum space of the couple. The integral `∫₀ᵗ ‖f‖*` is finite for every
`f` in `L¹ + L^∞`; conversely, for `t > 0`, an almost everywhere strongly measurable function with
`∫₀ᵗ ‖f‖* < ∞` represents an element of `L¹ + L^∞`
(`TauCeti.L1AddLinfty.exists_toAEEqFun_ae_eq_iff_lintegral_decreasingRearrangement_lt_top`).

The ambient space of `l1Linfty` carries the indiscrete topology, so the normed real interpolation
spaces `(L¹, L^∞)_{θ,q}` are those of the Lebesgue couple `TauCeti.CompatibleCouple.lebesgue` at
the exponents `1` and `∞`, whose ambient space is the normed space `L¹ + L^∞`. Both couples have
the same decompositions, so the embedding of the sum space of the Lebesgue couple into `L¹ + L^∞`,
a surjective isometry (`TauCeti.CompatibleCouple.norm_lebesgue_one_top_sumSpaceEmbed`), preserves
the `K`-functional (`TauCeti.CompatibleCouple.kFunctional_l1Linfty_sumSpaceEmbed`). The formula
holds for the Lebesgue couple as well
(`TauCeti.CompatibleCouple.ofReal_kFunctional_lebesgue_one_top`,
`TauCeti.CompatibleCouple.kFunctional_lebesgue_one_top`).

As a check, the `K`-functional of `c 1_A` is `‖c‖ min (t, μ A)`
(`TauCeti.CompatibleCouple.ofReal_kFunctional_l1Linfty_indicator`): the decomposition
`c 1_A = 0 + c 1_A` costs at most `t ‖c‖`, when `μ A < ∞` the decomposition `c 1_A = c 1_A + 0`
costs `‖c‖ μ A`, and no decomposition does better.

The radial retraction attaining the infimum in
`MeasureTheory.Measure.lintegral_decreasingRearrangement_enorm_eq_iInf_eLpNorm` scales vectors by
real numbers, so for the exact formula `E` is assumed to be a real normed space in addition to a
normed space over the scalar field `𝕜` of the couple. Without `NormedSpace ℝ E`, truncating `f` by
the indicator of `{‖f‖ > ‖f‖* t}` still gives the two-sided comparison
`∫₀ᵗ ‖f‖* ≤ K(t, u) ≤ 2 ∫₀ᵗ ‖f‖*`
(`TauCeti.CompatibleCouple.lintegral_decreasingRearrangement_le_ofReal_kFunctional_l1Linfty`,
`TauCeti.CompatibleCouple.ofReal_kFunctional_l1Linfty_le_two_mul`).

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.2 (Theorem 5.2.1).
* T. Fack and H. Kosaki, *Generalized s-numbers of τ-measurable operators*, Pacific J. Math.
  **123** (1986), 269–300, the formula following Theorem 4.4.
-/

public noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti.CompatibleCouple

variable {𝕜 E : Type*} {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {t : ℝ}

/-- The cost `‖g‖ + t ‖h‖` of a pair of `Lᵖ` functions, in terms of `eLpNorm`. -/
private theorem ofReal_norm_add_mul_norm {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (g : Lp E p μ) (h : Lp E q μ) (ht : 0 ≤ t) :
    ENNReal.ofReal (‖g‖ + t * ‖h‖) = eLpNorm g p μ + ENNReal.ofReal t * eLpNorm h q μ := by
  rw [ENNReal.ofReal_add (norm_nonneg _) (by positivity), ENNReal.ofReal_mul ht, Lp.norm_def,
    Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g),
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top h)]

/-- A splitting of finite cost `‖f₀‖₁ + t ‖f₁‖_∞`, with `t > 0`, is a pair of `L¹` and `L^∞`
functions. -/
private theorem memLp_of_eLpNorm_add_mul_ne_top {f₀ f₁ : α → E} (ht : 0 < t)
    (hfin : eLpNorm f₀ 1 μ + ENNReal.ofReal t * eLpNorm f₁ ∞ μ ≠ ∞) :
    MemLp f₀ 1 μ ∧ MemLp f₁ ∞ μ := by
  obtain ⟨hfin₀, hfin₁⟩ := ENNReal.add_ne_top.1 hfin
  refine ⟨memLp_iff.2 hfin₀.lt_top, memLp_iff.2 (lt_top_iff_ne_top.2 fun htop => hfin₁ ?_)⟩
  rw [htop, ENNReal.mul_top (by simpa using ht)]

/-- The Lebesgue couple `(L¹, L^∞)` and `l1Linfty` have the same decompositions, hence the same
`K`-functional, read through the embedding of the sum space of the former into `L¹ + L^∞`. -/
theorem kFunctional_l1Linfty_sumSpaceEmbed (ht : 0 ≤ t) (v : (lebesgue 𝕜 E μ 1 ∞).SumSpace) :
    (l1Linfty 𝕜 E μ).kFunctional t ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v) =
      (lebesgue 𝕜 E μ 1 ∞).kFunctional t v := by
  refine le_antisymm ((le_kFunctional_iff ht).2 fun g h hgh => kFunctional_le ht ?_)
    ((le_kFunctional_iff ht).2 fun g h hgh =>
      kFunctional_le ht ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed_injective ?_))
  · rw [← hgh, lebesgue_one_top_sumSpaceEmbed_fstToSum_add_sndToSum]
  · rw [lebesgue_one_top_sumSpaceEmbed_fstToSum_add_sndToSum, hgh]

/-- Every decomposition `u = g + h` bounds `∫₀ᵗ ‖f‖*` by `‖g‖₁ + t ‖h‖_∞`, so `∫₀ᵗ ‖f‖*` is at most
`K(t, u)`. No real normed space structure on `E` is needed. -/
theorem lintegral_decreasingRearrangement_le_ofReal_kFunctional_l1Linfty
    {u : L1AddLinfty 𝕜 E μ} {f : α → E} (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) (ht : 0 ≤ t) :
    ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s ≤
      ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hu
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨g, h, hgh, hlt⟩ := (kFunctional_lt_iff ht).1
    (lt_add_of_pos_right ((l1Linfty 𝕜 E μ).kFunctional t u) (NNReal.coe_pos.2 hε))
  have hgh' : ⇑g + ⇑h =ᵐ[μ] f := (L1AddLinfty.fstToSum_add_sndToSum_eq_iff.1 hgh).trans hu
  calc ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s
      ≤ ∫⁻ y, ‖g y‖ₑ ∂μ + ENNReal.ofReal t * essSup (‖h ·‖ₑ) μ :=
        μ.lintegral_decreasingRearrangement_le_lintegral_add_mul_essSup hf.eNorm t
          (hgh'.mono fun y hy => by
            simp only [Pi.add_apply] at hy ⊢
            rw [← hy]
            exact eNorm_add_le (g y) (h y))
    _ = ENNReal.ofReal (‖g‖ + t * ‖h‖) := by
        rw [ofReal_norm_add_mul_norm _ _ ht,
          eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable g),
          eLpNorm_exponent_top (Lp.aestronglyMeasurable h),
          eLpNormEssSup_eq_essSup_eNorm]
    _ ≤ ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u + ε) :=
        ENNReal.ofReal_le_ofReal hlt.le
    _ = ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) + ε := by
        rw [ENNReal.ofReal_add (kFunctional_nonneg ht) ε.coe_nonneg,
          ENNReal.ofReal_coe_nnreal]

/-- Lower bound `∫₀ᵗ ‖f‖* ≤ K(t, v)` for the Lebesgue couple `(L¹, L^∞)`, without requiring a real
normed space structure on `E`. -/
theorem lintegral_decreasingRearrangement_le_ofReal_kFunctional_lebesgue_one_top
    {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    (ht : 0 ≤ t) :
    ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s ≤
      ENNReal.ofReal ((lebesgue 𝕜 E μ 1 ∞).kFunctional t v) := by
  rw [← kFunctional_l1Linfty_sumSpaceEmbed ht]
  exact lintegral_decreasingRearrangement_le_ofReal_kFunctional_l1Linfty hv ht

/-- Indicator truncation at height `‖f‖* t` bounds `K(t, u)` by `2 ∫₀ᵗ ‖f‖*` for `t > 0`, without
requiring a real normed space structure on `E`. -/
private theorem ofReal_kFunctional_l1Linfty_le_two_mul_of_pos {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) (ht : 0 < t) :
    ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) ≤
      2 * ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hu
  have hfin : ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s < ∞ :=
    (lintegral_decreasingRearrangement_le_ofReal_kFunctional_l1Linfty hu ht.le).trans_lt
      ENNReal.ofReal_lt_top
  have hsub := μ.lintegral_decreasingRearrangement_eq_lintegral_sub hf.eNorm t
  set c := μ.decreasingRearrangement (‖f ·‖ₑ) t
  obtain ⟨_, hfin₁⟩ := ENNReal.add_lt_top.1 (hsub ▸ hfin)
  have hc : c ≠ ∞ := fun hc => by
    rw [hc, ENNReal.mul_top (by simpa using ht)] at hfin₁
    exact lt_irrefl _ hfin₁
  set S := {y | c < ‖f y‖ₑ}
  have hS : NullMeasurableSet S μ := nullMeasurableSet_lt aemeasurable_const hf.eNorm
  have hμS : μ S ≤ ENNReal.ofReal t := μ.measure_setOf_decreasingRearrangement_lt_le _ t
  have hest₀ :
      eLpNorm (S.indicator f) 1 μ ≤ ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := by
    rw [eLpNorm_one_eq_lintegral_eNorm (hf.indicator₀ hS), hsub]
    calc ∫⁻ y, ‖S.indicator f y‖ₑ ∂μ
        ≤ ∫⁻ y, (‖f y‖ₑ - c) + S.indicator (fun _ => c) y ∂μ := lintegral_mono fun y => by
          by_cases hy : y ∈ S
          · simpa [hy] using le_tsub_add
          · simp [hy]
      _ ≤ ∫⁻ y, (‖f y‖ₑ - c) ∂μ + ENNReal.ofReal t * c := by
          rw [lintegral_add_left' (hf.eNorm.sub_const c)]
          gcongr
          exact (lintegral_indicator_const_le S c).trans (by rw [mul_comm]; gcongr)
  have hest₁ : eLpNorm (Sᶜ.indicator f) ∞ μ ≤ c := by
    rw [eLpNorm_exponent_top (hf.indicator₀ hS.compl)]
    refine eLpNormEssSup_le_of_ae_eNorm_bound (ae_of_all _ fun y => ?_)
    by_cases hy : y ∈ S
    · simp [hy]
    · rw [Set.indicator_of_mem ((Set.mem_compl_iff S y).2 hy)]
      exact not_lt.1 hy
  have h₀ : MemLp (S.indicator f) 1 μ := memLp_iff.2 (hest₀.trans_lt hfin)
  have h₁ : MemLp (Sᶜ.indicator f) ∞ μ := memLp_iff.2 (hest₁.trans_lt hc.lt_top)
  have hdec : (l1Linfty 𝕜 E μ).fstToSum (h₀.toLp _) + (l1Linfty 𝕜 E μ).sndToSum (h₁.toLp _) =
      u := by
    refine L1AddLinfty.fstToSum_add_sndToSum_eq_iff.2 ?_
    filter_upwards [h₀.coeFn_toLp, h₁.coeFn_toLp, hu] with y hy₀ hy₁ hy
    rw [Pi.add_apply, hy₀, hy₁, hy, Set.indicator_self_add_compl_apply]
  calc ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u)
      ≤ ENNReal.ofReal (‖h₀.toLp _‖ + t * ‖h₁.toLp _‖) :=
        ENNReal.ofReal_le_ofReal (kFunctional_le ht.le hdec)
    _ = eLpNorm (S.indicator f) 1 μ + ENNReal.ofReal t * eLpNorm (Sᶜ.indicator f) ∞ μ := by
        rw [ofReal_norm_add_mul_norm _ _ ht.le, eLpNorm_congr_ae h₀.coeFn_toLp,
          eLpNorm_congr_ae h₁.coeFn_toLp]
    _ ≤ (∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s) +
          (∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s) := by
        gcongr
        exact (mul_le_mul_right hest₁ _).trans (hsub ▸ le_add_self)
    _ = 2 * ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := (two_mul _).symm

/-- Indicator truncation bounds `K(t, u)` by `2 ∫₀ᵗ ‖f‖*` for `t ≥ 0`, over any normed field `𝕜`
without requiring `NormedSpace ℝ E`. -/
theorem ofReal_kFunctional_l1Linfty_le_two_mul {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) (ht : 0 ≤ t) :
    ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) ≤
      2 * ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := by
  obtain rfl | ht := ht.eq_or_lt
  · rw [Ioc_self, Measure.restrict_empty, lintegral_zero_measure, mul_zero]
    have hfin : ∫⁻ s, μ.decreasingRearrangement (‖f ·‖ₑ) s ∂volume.restrict (Ioc 0 1) ≠ ∞ :=
      ((lintegral_decreasingRearrangement_le_ofReal_kFunctional_l1Linfty hu zero_le_one).trans_lt
        ENNReal.ofReal_lt_top).ne
    have hvol : Tendsto (volume.restrict (Ioc (0 : ℝ) 1) ∘ Ioc 0) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => bot_le)
        fun s => Measure.restrict_apply_le _ _
      simpa [Real.volume_Ioc] using
        (ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))).mono_left nhdsWithin_le_nhds
    have hlim : Tendsto (fun s => 2 * ∫⁻ r in Ioc 0 s, μ.decreasingRearrangement (‖f ·‖ₑ) r
        ∂volume.restrict (Ioc 0 1)) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (tendsto_setLIntegral_zero hfin hvol) (Or.inr (by simp))
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with s ⟨hs, hs₁⟩
    rw [Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc, max_self, min_eq_left hs₁]
    exact (ENNReal.ofReal_le_ofReal (kFunctional_mono le_rfl hs.le u)).trans
      (ofReal_kFunctional_l1Linfty_le_two_mul_of_pos hu hs)
  · exact ofReal_kFunctional_l1Linfty_le_two_mul_of_pos hu ht

/-- Upper bound `K(t, v) ≤ 2 ∫₀ᵗ ‖f‖*` for the Lebesgue couple `(L¹, L^∞)`, without requiring a
real normed space structure on `E`. -/
theorem ofReal_kFunctional_lebesgue_one_top_le_two_mul {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace}
    {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    (ht : 0 ≤ t) :
    ENNReal.ofReal ((lebesgue 𝕜 E μ 1 ∞).kFunctional t v) ≤
      2 * ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := by
  rw [← kFunctional_l1Linfty_sumSpaceEmbed ht]
  exact ofReal_kFunctional_l1Linfty_le_two_mul hv ht

variable [NormedSpace ℝ E]

/-- The `K`-functional of `(L¹, L^∞)` for `t > 0`. -/
private theorem ofReal_kFunctional_l1Linfty_of_pos {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) (ht : 0 < t) :
    ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) =
      ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hu
  refine le_antisymm ?_
    (lintegral_decreasingRearrangement_le_ofReal_kFunctional_l1Linfty hu ht.le)
  -- A splitting `f = f₀ + f₁` of finite cost gives a decomposition of `u` of the same cost.
  rw [μ.lintegral_decreasingRearrangement_enorm_eq_iInf_eLpNorm hf]
  refine le_iInf fun f₀ => le_iInf fun f₁ => le_iInf fun hsum => ?_
  by_cases hfin : eLpNorm f₀ 1 μ + ENNReal.ofReal t * eLpNorm f₁ ∞ μ = ∞
  · rw [hfin]
    exact le_top
  obtain ⟨h₀, h₁⟩ := memLp_of_eLpNorm_add_mul_ne_top ht hfin
  have hdec : (l1Linfty 𝕜 E μ).fstToSum (h₀.toLp f₀) + (l1Linfty 𝕜 E μ).sndToSum (h₁.toLp f₁) =
      u := by
    refine L1AddLinfty.fstToSum_add_sndToSum_eq_iff.2 ?_
    filter_upwards [h₀.coeFn_toLp, h₁.coeFn_toLp, hu] with y hy₀ hy₁ hy
    rw [Pi.add_apply, hy₀, hy₁, hy, ← Pi.add_apply, hsum]
  calc ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u)
      ≤ ENNReal.ofReal (‖h₀.toLp f₀‖ + t * ‖h₁.toLp f₁‖) :=
        ENNReal.ofReal_le_ofReal (kFunctional_le ht.le hdec)
    _ = eLpNorm f₀ 1 μ + ENNReal.ofReal t * eLpNorm f₁ ∞ μ := by
        rw [ofReal_norm_add_mul_norm _ _ ht.le, eLpNorm_congr_ae h₀.coeFn_toLp,
          eLpNorm_congr_ae h₁.coeFn_toLp]

/-- **The `K`-functional of `(L¹, L^∞)`.** For `t ≥ 0` and an element `u` of `L¹ + L^∞`
represented by `f`, `K(t, u) = ∫₀ᵗ ‖f‖*`. -/
theorem ofReal_kFunctional_l1Linfty {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) (ht : 0 ≤ t) :
    ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) =
      ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := by
  obtain rfl | ht := ht.eq_or_lt
  · -- `K(0, u) ≤ K(s, u) = ∫₀ˢ ‖f‖*`, which tends to `0` as `s ↓ 0` since `∫₀¹ ‖f‖*` is finite.
    rw [Ioc_self, Measure.restrict_empty, lintegral_zero_measure]
    have hfin : ∫⁻ s, μ.decreasingRearrangement (‖f ·‖ₑ) s ∂volume.restrict (Ioc 0 1) ≠ ∞ := by
      rw [← ofReal_kFunctional_l1Linfty_of_pos hu one_pos]
      exact ENNReal.ofReal_ne_top
    have hvol : Tendsto (volume.restrict (Ioc (0 : ℝ) 1) ∘ Ioc 0) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => bot_le)
        fun s => Measure.restrict_apply_le _ _
      simpa [Real.volume_Ioc] using
        (ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))).mono_left nhdsWithin_le_nhds
    refine le_antisymm (ge_of_tendsto (tendsto_setLIntegral_zero hfin hvol) ?_) bot_le
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with s ⟨hs, hs₁⟩
    rw [Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc, max_self, min_eq_left hs₁,
      ← ofReal_kFunctional_l1Linfty_of_pos hu hs]
    exact ENNReal.ofReal_le_ofReal (kFunctional_mono le_rfl hs.le u)
  · exact ofReal_kFunctional_l1Linfty_of_pos hu ht

/-- **The `K`-functional of `(L¹, L^∞)`**, real form: for `t ≥ 0` and an element `u` of
`L¹ + L^∞` represented by `f`, `K(t, u) = ∫₀ᵗ ‖f‖*`. -/
theorem kFunctional_l1Linfty {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) (ht : 0 ≤ t) :
    (l1Linfty 𝕜 E μ).kFunctional t u =
      (∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s).toReal := by
  rw [← ofReal_kFunctional_l1Linfty hu ht, ENNReal.toReal_ofReal (kFunctional_nonneg ht)]

/-- **The `K`-functional of the Lebesgue couple `(L¹, L^∞)`.** For `t ≥ 0` and an element `v` of
its sum space represented by `f`, `K(t, v) = ∫₀ᵗ ‖f‖*`. -/
theorem ofReal_kFunctional_lebesgue_one_top {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    (ht : 0 ≤ t) :
    ENNReal.ofReal ((lebesgue 𝕜 E μ 1 ∞).kFunctional t v) =
      ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := by
  rw [← kFunctional_l1Linfty_sumSpaceEmbed ht, ofReal_kFunctional_l1Linfty hv ht]

/-- **The `K`-functional of the Lebesgue couple `(L¹, L^∞)`**, real form: for `t ≥ 0` and an
element `v` of its sum space represented by `f`, `K(t, v) = ∫₀ᵗ ‖f‖*`. -/
theorem kFunctional_lebesgue_one_top {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    (ht : 0 ≤ t) :
    (lebesgue 𝕜 E μ 1 ∞).kFunctional t v =
      (∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s).toReal := by
  rw [← kFunctional_l1Linfty_sumSpaceEmbed ht, kFunctional_l1Linfty hv ht]

/-- The `K`-functional of `c 1_A` in `L¹ + L^∞` is `‖c‖ min (t, μ A)`, for `t ≥ 0`. -/
theorem ofReal_kFunctional_l1Linfty_indicator {u : L1AddLinfty 𝕜 E μ} {A : Set α}
    {c : E} (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] A.indicator fun _ => c)
    (ht : 0 ≤ t) :
    ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) = ‖c‖ₑ * min (ENNReal.ofReal t) (μ A) := by
  rw [ofReal_kFunctional_l1Linfty hu ht]
  simp_rw [eNorm_indicator_eq_indicator_eNorm]
  exact μ.lintegral_decreasingRearrangement_indicator A ‖c‖ₑ t

end TauCeti.CompatibleCouple

namespace TauCeti.L1AddLinfty

variable {𝕜 E : Type*} {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {t : ℝ}

/-- For `t > 0`, a function represents an element of `L¹ + L^∞` exactly when it is almost
everywhere strongly measurable and `∫₀ᵗ ‖f‖*` is finite. -/
theorem exists_toAEEqFun_ae_eq_iff_lintegral_decreasingRearrangement_lt_top {f : α → E}
    (ht : 0 < t) :
    (∃ u : L1AddLinfty 𝕜 E μ, ⇑(toAEEqFun 𝕜 u) =ᵐ[μ] f) ↔
      AEStronglyMeasurable f μ ∧ ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s < ∞ := by
  refine ⟨fun ⟨u, hu⟩ => ⟨(AEEqFun.aestronglyMeasurable _).congr hu,
    (CompatibleCouple.lintegral_decreasingRearrangement_le_ofReal_kFunctional_l1Linfty hu
      ht.le).trans_lt ENNReal.ofReal_lt_top⟩, fun ⟨hf, hfin⟩ => exists_toAEEqFun_ae_eq_iff.2 ?_⟩
  -- Truncate `f` at the level `c = ‖f‖* t`: the part above `c` is integrable, since
  -- `{‖f‖ > c}` has measure at most `t`, and the part below is bounded by `c`.
  rw [μ.lintegral_decreasingRearrangement_eq_lintegral_sub hf.eNorm t] at hfin
  set c := μ.decreasingRearrangement (‖f ·‖ₑ) t
  obtain ⟨hfin₀, hfin₁⟩ := ENNReal.add_lt_top.1 hfin
  have hc : c ≠ ∞ := fun hc => by
    rw [hc, ENNReal.mul_top (by simpa using ht)] at hfin₁
    exact lt_irrefl _ hfin₁
  set S := {y | c < ‖f y‖ₑ}
  have hS : NullMeasurableSet S μ := nullMeasurableSet_lt aemeasurable_const hf.eNorm
  have hμS : μ S ≤ ENNReal.ofReal t := μ.measure_setOf_decreasingRearrangement_lt_le _ t
  have h₀ : MemLp (S.indicator f) 1 μ := by
    rw [memLp_iff, eLpNorm_one_eq_lintegral_eNorm (hf.indicator₀ hS)]
    calc ∫⁻ y, ‖S.indicator f y‖ₑ ∂μ
        ≤ ∫⁻ y, (‖f y‖ₑ - c) + S.indicator (fun _ => c) y ∂μ := lintegral_mono fun y => by
          by_cases hy : y ∈ S
          · simpa [hy] using le_tsub_add
          · simp [hy]
      _ ≤ ∫⁻ y, (‖f y‖ₑ - c) ∂μ + c * μ S := by
          rw [lintegral_add_left' (hf.eNorm.sub_const c)]
          gcongr
          exact lintegral_indicator_const_le S c
      _ < ∞ := ENNReal.add_lt_top.2 ⟨hfin₀,
          ENNReal.mul_lt_top hc.lt_top (hμS.trans_lt ENNReal.ofReal_lt_top)⟩
  have h₁ : MemLp (Sᶜ.indicator f) ∞ μ := by
    rw [memLp_iff, eLpNorm_exponent_top (hf.indicator₀ hS.compl)]
    refine (eLpNormEssSup_le_of_ae_eNorm_bound (ae_of_all _ fun y => ?_)).trans_lt hc.lt_top
    by_cases hy : y ∈ S
    · simp [hy]
    · rw [Set.indicator_of_mem ((Set.mem_compl_iff S y).2 hy)]
      exact not_lt.1 hy
  refine ⟨h₀.toLp _, h₁.toLp _, ?_⟩
  filter_upwards [h₀.coeFn_toLp, h₁.coeFn_toLp] with y hy₀ hy₁
  rw [Pi.add_apply, hy₀, hy₁, Set.indicator_self_add_compl_apply]

end TauCeti.L1AddLinfty
