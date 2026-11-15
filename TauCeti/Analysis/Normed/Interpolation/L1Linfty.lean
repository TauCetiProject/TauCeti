/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.KFunctional
public import TauCeti.Analysis.Normed.Interpolation.Lebesgue
public import TauCeti.Analysis.Normed.Interpolation.RealMethod
public import TauCeti.MeasureTheory.Function.DecreasingRearrangement
public import TauCeti.MeasureTheory.Function.LorentzSeminorm
public import TauCeti.MeasureTheory.Function.Lp.L1AddLinfty
-- Proof-only: the weighted Hardy inequality and rpow lintegral bounding the K-method and Lorentz
-- integrals.
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.MeasureTheory.Integral.Hardy

/-!
# The `K`-functional and real interpolation spaces of `(L¹, L^∞)`

For the compatible couple `(L¹(μ; E), L^∞(μ; E))` (`TauCeti.CompatibleCouple.l1Linfty`) and
`t ≥ 0`, Peetre's `K`-functional of an element `u` of `L¹ + L^∞` represented by a function `f` is
the integral of the decreasing rearrangement of `‖f‖` over `(0, t]`:

`K(t, u) = ∫₀ᵗ ‖f‖*`

(`TauCeti.CompatibleCouple.ofReal_kFunctional_l1Linfty`,
`TauCeti.CompatibleCouple.kFunctional_l1Linfty`). This is the formula
`MeasureTheory.Measure.lintegral_decreasingRearrangement_enorm_eq_iInf_eLpNorm`, which is stated
for arbitrary splittings `f = f₀ + f₁` measured by `Lᵖ` seminorms, transported to the
decompositions of `u` in the sum space of the couple. Without assuming that `E` is a real normed
space, indicator truncation at `‖f‖* t` still yields the two-sided bound
`∫₀ᵗ ‖f‖* ≤ K(t, u) ≤ 2 ∫₀ᵗ ‖f‖*`
(`TauCeti.CompatibleCouple.ofReal_kFunctional_l1Linfty_le_two_mul`). The integral `∫₀ᵗ ‖f‖*` is
finite for every `f` in `L¹ + L^∞`; conversely, for `t > 0`, an almost everywhere strongly
measurable function with `∫₀ᵗ ‖f‖* < ∞` represents an element of `L¹ + L^∞`
(`TauCeti.L1AddLinfty.exists_toAEEqFun_ae_eq_iff_lintegral_decreasingRearrangement_lt_top`).

Applying the real interpolation method (`TauCeti.CompatibleCouple.kMethodENorm`,
`TauCeti.CompatibleCouple.KMethodSpace`) for `0 < θ < 1`, `1 ≤ q ≤ ∞`, and `1 / p = 1 - θ`
identifies `(L¹, L^∞)_{θ,q}` with the Lorentz space `L^{p,q}` (`TauCeti.eLorentzNorm`,
`TauCeti.MemLorentz`):

* Monotonicity `t ‖f‖* t ≤ ∫₀ᵗ ‖f‖* ≤ K(t, u)` gives the lower bound
  `‖f‖_{p,q} ≤ ‖u‖_{θ,q}` (`TauCeti.CompatibleCouple.eLorentzNorm_le_kMethodENorm_l1Linfty`,
  `TauCeti.CompatibleCouple.eLorentzNorm_le_kMethodENorm_lebesgue_one_top`).
* Hardy's inequality on `(0, ∞)` (`TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le`) gives the
  upper bound `‖u‖_{θ,q} ≤ 2 θ⁻¹ ‖f‖_{p,q}` over any normed field `𝕜`
  (`TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_le_two_mul_eLorentzNorm`), sharpened to
  `‖u‖_{θ,q} ≤ θ⁻¹ ‖f‖_{p,q}` when `E` is also a real normed space
  (`TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_le_eLorentzNorm`).
* Membership in `(L¹, L^∞)_{θ,q}` is equivalent to `MemLorentz f p q μ`, and every Lorentz
  function with `1 < p < ∞` and `q ≠ 0` represents an element of `L¹ + L^∞`
  (`TauCeti.CompatibleCouple.mem_kMethod_lebesgue_one_top_iff_memLorentz`,
  `TauCeti.L1AddLinfty.exists_toAEEqFun_ae_eq_of_memLorentz`,
  `TauCeti.CompatibleCouple.exists_mem_kMethod_lebesgue_one_top_iff_memLorentz`).
* On the diagonal `q = p`, where `eLorentzNorm f p p μ = eLpNorm f p μ`, this yields the
  Banach-space isomorphism `(L¹, L^∞)_{θ,p} ≃L[𝕜] L^p(μ; E)`
  (`TauCeti.CompatibleCouple.lebesgueOneTopKMethodEquivLp`).

The ambient space of `l1Linfty` carries the indiscrete topology, so the normed real interpolation
spaces `(L¹, L^∞)_{θ,q}` are those of the Lebesgue couple `TauCeti.CompatibleCouple.lebesgue` at
the exponents `1` and `∞`, whose ambient space is the normed space `L¹ + L^∞`. Both couples have
the same decompositions, so the embedding of the sum space of the Lebesgue couple into `L¹ + L^∞`,
a surjective isometry (`TauCeti.CompatibleCouple.norm_lebesgue_one_top_sumSpaceEmbed`), preserves
both the `K`-functional (`TauCeti.CompatibleCouple.kFunctional_l1Linfty_sumSpaceEmbed`) and the
`K`-method norm (`TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_sumSpaceEmbed`).

As a check, for `[NormedSpace ℝ E]` the `K`-functional of `c 1_A` is `‖c‖ min (t, μ A)`
(`TauCeti.CompatibleCouple.ofReal_kFunctional_l1Linfty_indicator`), and for `0 < θ < 1` its
`K`-method norm is `c_{θ,q} ‖c‖ μ A ^ (1 - θ)`
(`TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_indicator`).

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.2 (Theorems 5.2.1 and 5.2.4).
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

/-- The Lebesgue couple `(L¹, L^∞)` and `l1Linfty` have the same `K`-method norm, read through the
embedding of the sum space of the former into `L¹ + L^∞`. -/
theorem kMethodENorm_l1Linfty_sumSpaceEmbed (θ : ℝ) (q : ℝ≥0∞)
    (v : (lebesgue 𝕜 E μ 1 ∞).SumSpace) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v) =
      (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v := by
  rw [kMethodENorm_def, kMethodENorm_def]
  refine eLpNorm_congr_ae ?_
  filter_upwards [ae_pos_multHaar] with t ht
  rw [kFunctional_l1Linfty_sumSpaceEmbed ht.le]

/-- Every decomposition `u = g + h` bounds `∫₀ᵗ ‖f‖*` by `‖g‖₁ + t ‖h‖_∞`, so `∫₀ᵗ ‖f‖*` is at most
`K(t, u)`. -/
private theorem lintegral_decreasingRearrangement_le_ofReal_kFunctional_l1Linfty
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

/-- Indicator truncation at `c = ‖f‖* t` bounds `K(t, u)` by `2 ∫₀ᵗ ‖f‖*` for `t > 0` without
requiring a real scalar action on `E`. -/
private theorem ofReal_kFunctional_l1Linfty_le_two_mul_of_pos {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) (ht : 0 < t) :
    ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) ≤
      2 * ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hu
  set I := ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s
  set c := μ.decreasingRearrangement (‖f ·‖ₑ) t
  have hI_lt : I < ∞ :=
    (lintegral_decreasingRearrangement_le_ofReal_kFunctional_l1Linfty hu ht.le).trans_lt
      ENNReal.ofReal_lt_top
  have hI_eq : I = (∫⁻ y, (‖f y‖ₑ - c) ∂μ) + ENNReal.ofReal t * c :=
    μ.lintegral_decreasingRearrangement_eq_lintegral_sub hf.eNorm t
  have htc_le : ENNReal.ofReal t * c ≤ I := hI_eq ▸ le_add_self
  have hc_lt : c < ∞ := lt_top_iff_ne_top.2 fun hc => by
    rw [hc, ENNReal.mul_top (by simpa using ht), top_le_iff] at htc_le
    exact hI_lt.ne htc_le
  set S := {y | c < ‖f y‖ₑ}
  have hS : NullMeasurableSet S μ := nullMeasurableSet_lt aemeasurable_const hf.eNorm
  have he₀ : eLpNorm (S.indicator f) 1 μ ≤ I := by
    rw [eLpNorm_one_eq_lintegral_eNorm (hf.indicator₀ hS), hI_eq]
    calc ∫⁻ y, ‖S.indicator f y‖ₑ ∂μ
        ≤ ∫⁻ y, (‖f y‖ₑ - c) + S.indicator (fun _ => c) y ∂μ := lintegral_mono fun y => by
          by_cases hy : y ∈ S
          · simpa [hy] using le_tsub_add
          · simp [hy]
      _ ≤ (∫⁻ y, (‖f y‖ₑ - c) ∂μ) + c * μ S := by
          rw [lintegral_add_left' (hf.eNorm.sub_const c)]
          gcongr
          exact lintegral_indicator_const_le S c
      _ ≤ (∫⁻ y, (‖f y‖ₑ - c) ∂μ) + ENNReal.ofReal t * c := by
          rw [mul_comm (ENNReal.ofReal t) c]
          gcongr
          exact μ.measure_setOf_decreasingRearrangement_lt_le _ t
  have he₁ : eLpNorm (Sᶜ.indicator f) ∞ μ ≤ c := by
    rw [eLpNorm_exponent_top (hf.indicator₀ hS.compl)]
    refine eLpNormEssSup_le_of_ae_eNorm_bound (ae_of_all _ fun y => ?_)
    by_cases hy : y ∈ S
    · simp [hy]
    · rw [Set.indicator_of_mem ((Set.mem_compl_iff S y).2 hy)]
      exact not_lt.1 hy
  have h₀ : MemLp (S.indicator f) 1 μ := memLp_iff.2 (he₀.trans_lt hI_lt)
  have h₁ : MemLp (Sᶜ.indicator f) ∞ μ := memLp_iff.2 (he₁.trans_lt hc_lt)
  have hdec :
      (l1Linfty 𝕜 E μ).fstToSum (h₀.toLp _) + (l1Linfty 𝕜 E μ).sndToSum (h₁.toLp _) = u := by
    refine L1AddLinfty.fstToSum_add_sndToSum_eq_iff.2 ?_
    filter_upwards [h₀.coeFn_toLp, h₁.coeFn_toLp, hu] with y hy₀ hy₁ hy
    rw [Pi.add_apply, hy₀, hy₁, hy, Set.indicator_self_add_compl_apply]
  calc ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u)
      ≤ eLpNorm (S.indicator f) 1 μ + ENNReal.ofReal t * eLpNorm (Sᶜ.indicator f) ∞ μ := by
        refine (ENNReal.ofReal_le_ofReal (kFunctional_le ht.le hdec)).trans_eq ?_
        rw [ofReal_norm_add_mul_norm _ _ ht.le, eLpNorm_congr_ae h₀.coeFn_toLp,
          eLpNorm_congr_ae h₁.coeFn_toLp]
    _ ≤ I + I := add_le_add he₀ ((mul_le_mul_right he₁ _).trans htc_le)
    _ = 2 * I := (two_mul I).symm

/-- At `t = 0`, the `K`-functional of `(L¹, L^∞)` vanishes. -/
@[simp]
theorem kFunctional_zero_left_l1Linfty (u : L1AddLinfty 𝕜 E μ) :
    (l1Linfty 𝕜 E μ).kFunctional 0 u = 0 := by
  set f : α → E := ⇑(L1AddLinfty.toAEEqFun 𝕜 u)
  have hfin : ∫⁻ s, μ.decreasingRearrangement (‖f ·‖ₑ) s ∂volume.restrict (Ioc 0 1) ≠ ∞ :=
    ((lintegral_decreasingRearrangement_le_ofReal_kFunctional_l1Linfty EventuallyEq.rfl
      zero_le_one).trans_lt ENNReal.ofReal_lt_top).ne
  have hvol : Tendsto (volume.restrict (Ioc (0 : ℝ) 1) ∘ Ioc 0) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => bot_le)
      fun s => Measure.restrict_apply_le _ _
    simpa [Real.volume_Ioc] using
      (ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))).mono_left nhdsWithin_le_nhds
  have htend : Tendsto (fun s : ℝ =>
      2 * ∫⁻ r in Ioc 0 s, μ.decreasingRearrangement (‖f ·‖ₑ) r ∂volume.restrict (Ioc 0 1))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul (tendsto_setLIntegral_zero hfin hvol) (Or.inr (by norm_num))
  have h0 : ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional 0 u) = 0 := by
    refine le_antisymm (ge_of_tendsto htend ?_) bot_le
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with s ⟨hs, hs₁⟩
    rw [Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc, max_self, min_eq_left hs₁]
    exact (ENNReal.ofReal_le_ofReal (kFunctional_mono le_rfl hs.le u)).trans
      (ofReal_kFunctional_l1Linfty_le_two_mul_of_pos EventuallyEq.rfl hs)
  exact le_antisymm (ENNReal.ofReal_eq_zero.1 h0) (kFunctional_nonneg le_rfl)

/-- Over any normed field `𝕜`, Peetre's `K`-functional of `(L¹, L^∞)` is at most `2 ∫₀ᵗ ‖f‖*` for
`t ≥ 0`. When `E` is also a real normed space, the factor `2` drops to `1`
(`ofReal_kFunctional_l1Linfty`). -/
theorem ofReal_kFunctional_l1Linfty_le_two_mul {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) (ht : 0 ≤ t) :
    ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) ≤
      2 * ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := by
  obtain rfl | ht := ht.eq_or_lt
  · simp
  · exact ofReal_kFunctional_l1Linfty_le_two_mul_of_pos hu ht

/-! ### Norm equivalence between `(L¹, L^∞)_{θ,q}` and `L^{p,q}` -/

/-- For `0 < θ < 1` and `p.toReal⁻¹ = 1 - θ`, the exponent `p` satisfies `1 < p < ∞`. -/
private theorem one_lt_and_ne_top_of_toReal_inv_eq {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p : ℝ≥0∞}
    (hp : p.toReal⁻¹ = 1 - θ) : 1 < p ∧ p ≠ ∞ := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  have hp_top : p ≠ ∞ := by
    rintro rfl
    simp only [ENNReal.toReal_top, inv_zero] at hp
    exact h1θ.ne hp
  have hp_pos : 0 < p.toReal := inv_pos.1 (hp ▸ h1θ)
  have hp_gt : 1 < p.toReal := by nlinarith [inv_mul_cancel₀ hp_pos.ne', hp, hθ.1, hp_pos]
  exact ⟨(ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).1 (by simpa using hp_gt), hp_top⟩

/-- **Lower bound of the `(L¹, L^∞)` real interpolation formula.** For `p ≠ 0` and
`1 / p = 1 - θ`, every `u` in `L¹ + L^∞` represented by `f` satisfies
`eLorentzNorm f p q μ ≤ (l1Linfty 𝕜 E μ).kMethodENorm θ q u`. -/
theorem eLorentzNorm_le_kMethodENorm_l1Linfty {θ : ℝ} {p q : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p.toReal⁻¹ = 1 - θ) {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) :
    eLorentzNorm f p q μ ≤ (l1Linfty 𝕜 E μ).kMethodENorm θ q u := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hu
  rw [eLorentzNorm_eq_eLpNorm hp0 hf, kMethodENorm_def]
  refine eLpNorm_mono_eNorm_ae
    ((ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
      (μ.measurable_decreasingRearrangement _)).aestronglyMeasurable ?_
  filter_upwards [ae_pos_multHaar] with t ht
  simp only [eNorm_eq_self]
  rw [hp, Real.eNorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le)),
    ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  have hpow : ENNReal.ofReal (t ^ (1 - θ)) = ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal t := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add_one ht.ne',
      show -θ + 1 = 1 - θ by ring]
  have hmono : ENNReal.ofReal t * μ.decreasingRearrangement (‖f ·‖ₑ) t ≤
      ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := by
    have hconst : ENNReal.ofReal t * μ.decreasingRearrangement (‖f ·‖ₑ) t =
        ∫⁻ _ in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) t := by
      rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
    rw [hconst]
    exact setLIntegral_mono' measurableSet_Ioc fun s hs =>
      μ.antitone_decreasingRearrangement _ hs.2
  rw [hpow, mul_assoc]
  exact mul_le_mul_right
    (hmono.trans (lintegral_decreasingRearrangement_le_ofReal_kFunctional_l1Linfty hu ht.le)) _

/-- **Lower bound of the `(L¹, L^∞)` real interpolation formula** for the Lebesgue couple. -/
theorem eLorentzNorm_le_kMethodENorm_lebesgue_one_top {θ : ℝ} {p q : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p.toReal⁻¹ = 1 - θ) {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f) :
    eLorentzNorm f p q μ ≤ (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed]
  exact eLorentzNorm_le_kMethodENorm_l1Linfty hp0 hp hv

/-- **Upper bound of the `(L¹, L^∞)` real interpolation formula** over an arbitrary normed field:
for `0 < θ < 1`, `1 ≤ q`, and `1 / p = 1 - θ`, every `u` in `L¹ + L^∞` represented by `f` satisfies
`‖u‖_{θ,q} ≤ 2 θ⁻¹ ‖f‖_{p,q}`. -/
theorem kMethodENorm_l1Linfty_le_two_mul_eLorentzNorm {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p q : ℝ≥0∞}
    (hq : 1 ≤ q) (hp : p.toReal⁻¹ = 1 - θ) {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u ≤ ENNReal.ofReal (2 * θ⁻¹) * eLorentzNorm f p q μ := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hu
  obtain ⟨hp1, _⟩ := one_lt_and_ne_top_of_toReal_inv_eq hθ hp
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  set g : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s
  have hg : AEStronglyMeasurable g multHaar := by
    refine aestronglyMeasurable_iff_aemeasurable.2 ((ENNReal.measurable_ofReal.comp
      (measurable_id.pow_const _)).aemeasurable.mul ?_)
    exact (Monotone.measurable (f := fun t : ℝ =>
      ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s)
      fun _ _ hab => lintegral_mono_set (Ioc_subset_Ioc_right hab)).aemeasurable
  rw [kMethodENorm_def, eLorentzNorm_eq_eLpNorm hp0 hf, hp, ENNReal.ofReal_mul zero_le_two,
    ENNReal.ofReal_ofNat, mul_assoc]
  calc eLpNorm (fun t => t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u) q multHaar
      ≤ eLpNorm (fun t => 2 * g t) q multHaar := by
        refine eLpNorm_mono_eNorm_ae (aestronglyMeasurable_rpow_neg_mul_kFunctional θ u) ?_
        filter_upwards [ae_pos_multHaar] with t ht
        rw [eNorm_eq_self, Real.eNorm_of_nonneg
          (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le)),
          ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
        exact (mul_le_mul_right (ofReal_kFunctional_l1Linfty_le_two_mul hu ht.le) _).trans_eq
          (mul_left_comm _ _ _)
    _ = 2 * eLpNorm g q multHaar := eLpNorm_const_mul_ennreal hg
    _ ≤ 2 * (ENNReal.ofReal θ⁻¹ * eLpNorm (fun t : ℝ =>
          ENNReal.ofReal (t ^ (1 - θ)) * μ.decreasingRearrangement (‖f ·‖ₑ) t) q multHaar) := by
        gcongr
        exact TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le hθ.1 hq _

/-- **Upper bound of the `(L¹, L^∞)` real interpolation formula** for the Lebesgue couple over an
arbitrary normed field. -/
theorem kMethodENorm_lebesgue_one_top_le_two_mul_eLorentzNorm {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    {p q : ℝ≥0∞} (hq : 1 ≤ q) (hp : p.toReal⁻¹ = 1 - θ) {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace}
    {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v ≤
      ENNReal.ofReal (2 * θ⁻¹) * eLorentzNorm f p q μ := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed]
  exact kMethodENorm_l1Linfty_le_two_mul_eLorentzNorm hθ hq hp hv

/-- **Membership in `(L¹, L^∞)_{θ,q}` via the Lorentz gauge.** For `0 < θ < 1`, `1 ≤ q`, and
`1 / p = 1 - θ`, an element `u` of `L¹ + L^∞` represented by `f` lies in `(l1Linfty 𝕜 E μ).kMethod`
if and only if `MemLorentz f p q μ`. -/
theorem mem_kMethod_l1Linfty_iff_memLorentz {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p q : ℝ≥0∞} (hq : 1 ≤ q)
    (hp : p.toReal⁻¹ = 1 - θ) {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) :
    u ∈ (l1Linfty 𝕜 E μ).kMethod θ q ↔ MemLorentz f p q μ := by
  obtain ⟨hp1, _⟩ := one_lt_and_ne_top_of_toReal_inv_eq hθ hp
  rw [mem_kMethod_iff, memLorentz_iff]
  refine ⟨(eLorentzNorm_le_kMethodENorm_l1Linfty (zero_lt_one.trans hp1).ne' hp hu).trans_lt,
    fun hf => (kMethodENorm_l1Linfty_le_two_mul_eLorentzNorm hθ hq hp hu).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)⟩

/-- **Membership in `(L¹, L^∞)_{θ,q}`** for the Lebesgue couple: for `0 < θ < 1`, `1 ≤ q`, and
`1 / p = 1 - θ`, an element `v` of the sum space represented by `f` lies in
`(lebesgue 𝕜 E μ 1 ∞).kMethod θ q` if and only if `MemLorentz f p q μ`. -/
theorem mem_kMethod_lebesgue_one_top_iff_memLorentz {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p q : ℝ≥0∞}
    (hq : 1 ≤ q) (hp : p.toReal⁻¹ = 1 - θ) {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f) :
    v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q ↔ MemLorentz f p q μ := by
  rw [mem_kMethod_iff, ← kMethodENorm_l1Linfty_sumSpaceEmbed, ← mem_kMethod_iff]
  exact mem_kMethod_l1Linfty_iff_memLorentz hθ hq hp hv

section RealNormedSpace

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
  · simp
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

/-- **Sharp upper bound of the `(L¹, L^∞)` real interpolation formula.** When `E` is also a real
normed space, Hardy's inequality and `K(t, u) = ∫₀ᵗ ‖f‖*` bound the `K`-method norm by
`θ⁻¹ ‖f‖_{p,q}` for `0 < θ < 1`, `1 ≤ q`, and `1 / p = 1 - θ`. -/
theorem kMethodENorm_l1Linfty_le_eLorentzNorm {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p q : ℝ≥0∞}
    (hq : 1 ≤ q) (hp : p.toReal⁻¹ = 1 - θ) {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u ≤ ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hu
  obtain ⟨hp1, _⟩ := one_lt_and_ne_top_of_toReal_inv_eq hθ hp
  rw [kMethodENorm_def, eLorentzNorm_eq_eLpNorm (zero_lt_one.trans hp1).ne' hf, hp]
  refine (eLpNorm_mono_eNorm_ae (aestronglyMeasurable_rpow_neg_mul_kFunctional θ u) ?_).trans
    (TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le hθ.1 hq _)
  filter_upwards [ae_pos_multHaar] with t ht
  rw [eNorm_eq_self, Real.eNorm_of_nonneg
    (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le)),
    ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ofReal_kFunctional_l1Linfty hu ht.le]

/-- **Sharp upper bound of the `(L¹, L^∞)` real interpolation formula** for the Lebesgue couple when
`E` is also a real normed space. -/
theorem kMethodENorm_lebesgue_one_top_le_eLorentzNorm {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p q : ℝ≥0∞}
    (hq : 1 ≤ q) (hp : p.toReal⁻¹ = 1 - θ) {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v ≤ ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed]
  exact kMethodENorm_l1Linfty_le_eLorentzNorm hθ hq hp hv

/-- The `K`-functional of `c 1_A` in `L¹ + L^∞` is `‖c‖ min (t, μ A)`, for `t ≥ 0`. -/
theorem ofReal_kFunctional_l1Linfty_indicator {u : L1AddLinfty 𝕜 E μ} {A : Set α}
    {c : E} (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] A.indicator fun _ => c)
    (ht : 0 ≤ t) :
    ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) = ‖c‖ₑ * min (ENNReal.ofReal t) (μ A) := by
  rw [ofReal_kFunctional_l1Linfty hu ht]
  simp_rw [eNorm_indicator_eq_indicator_eNorm]
  exact μ.lintegral_decreasingRearrangement_indicator A ‖c‖ₑ t

private theorem eLpNorm_rpow_neg_mul_min_const (θ : ℝ) (q : ℝ≥0∞) {m : ℝ} (hm : 0 < m) :
    eLpNorm (fun t : ℝ => t ^ (-θ) * min t m) q multHaar =
      ENNReal.ofReal (m ^ (1 - θ)) * kMethodConst θ q := by
  have hmp : MeasurePreserving (m * ·) multHaar multHaar :=
    ⟨measurable_const_mul m, map_multHaar_mul_left hm⟩
  have hf : AEStronglyMeasurable (fun t : ℝ => t ^ (-θ) * min t m) multHaar :=
    ((continuousOn_id.rpow_const fun _ ht => Or.inl (ne_of_gt ht)).mul
      (continuous_id.min continuous_const).continuousOn).aestronglyMeasurable_multHaar
  have hae : ((fun t : ℝ => t ^ (-θ) * min t m) ∘ (m * ·)) =ᵐ[multHaar]
      m ^ (1 - θ) • fun s : ℝ => s ^ (-θ) * min 1 s := by
    filter_upwards [ae_pos_multHaar] with s hs
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    have hmin : min (m * s) m = m * min 1 s := by
      rw [show min (m * s) m = min (m * s) (m * 1) by rw [mul_one],
        ← mul_min_of_nonneg _ _ hm.le, min_comm]
    rw [Real.mul_rpow hm.le hs.le, hmin,
      show m ^ (-θ) * s ^ (-θ) * (m * min 1 s) = (m ^ (-θ) * m) * (s ^ (-θ) * min 1 s) by ring,
      ← Real.rpow_add_one hm.ne', show -θ + 1 = 1 - θ by ring]
  rw [← eLpNorm_comp_measurePreserving hf hmp, eLpNorm_congr_ae hae, eLpNorm_const_smul,
    Real.eNorm_of_nonneg (Real.rpow_nonneg hm.le _), ← kMethodConst_def]

private theorem kMethodENorm_l1Linfty_indicator_eq_top_of_measure_eq_top {θ : ℝ}
    (hθ : θ ∈ Ioo 0 1) {q : ℝ≥0∞} (hq0 : q ≠ 0) {u : L1AddLinfty 𝕜 E μ} {A : Set α} {c : E}
    (hc : c ≠ 0) (hA : μ A = ∞)
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] A.indicator fun _ => c) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u = ∞ := by
  have ha : ‖c‖ₑ * kMethodConst θ q ≠ 0 :=
    mul_ne_zero (eNorm_ne_zero.2 hc) (kMethodConst_ne_zero θ hq0)
  have hlim : Tendsto (fun n : ℕ => (‖c‖ₑ * kMethodConst θ q) * n) atTop (𝓝 ∞) := by
    have h := ENNReal.Tendsto.const_mul (a := ‖c‖ₑ * kMethodConst θ q)
      ENNReal.tendsto_nat_nhds_top (Or.inl ENNReal.top_ne_zero)
    rwa [ENNReal.mul_top ha] at h
  refine top_le_iff.1 (le_of_tendsto' hlim fun n : ℕ => ?_)
  set m : ℝ := ((n : ℝ) + 1) ^ (1 - θ)⁻¹
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  have hm : 0 < m := Real.rpow_pos_of_pos (by positivity) _
  have hpow : (n : ℝ≥0∞) ≤ ENNReal.ofReal (m ^ (1 - θ)) := by
    rw [← Real.rpow_mul (by positivity), inv_mul_cancel₀ h1θ.ne', Real.rpow_one]
    exact (ENNReal.ofReal_natCast n).symm.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  calc ‖c‖ₑ * kMethodConst θ q * (n : ℝ≥0∞)
      ≤ ‖c‖ₑ * (ENNReal.ofReal (m ^ (1 - θ)) * kMethodConst θ q) := by
        rw [mul_assoc, mul_comm (kMethodConst θ q)]
        gcongr
    _ = eLpNorm (‖c‖ • fun t : ℝ => t ^ (-θ) * min t m) q multHaar := by
        rw [eLpNorm_const_smul, eNorm_norm, eLpNorm_rpow_neg_mul_min_const θ q hm]
    _ ≤ (l1Linfty 𝕜 E μ).kMethodENorm θ q u := by
        have hcont : ContinuousOn (fun t : ℝ => t ^ (-θ) * min t m) (Ioi 0) :=
          (continuousOn_id.rpow_const fun _ ht => Or.inl (ne_of_gt ht)).mul
            (continuous_id.min continuous_const).continuousOn
        rw [kMethodENorm_def]
        refine eLpNorm_mono_ae_real (hcont.aestronglyMeasurable_multHaar.const_smul _) ?_
        filter_upwards [ae_pos_multHaar] with t ht
        have hk : (l1Linfty 𝕜 E μ).kFunctional t u = ‖c‖ * t := by
          have h := ofReal_kFunctional_l1Linfty_indicator hu ht.le
          rw [hA, min_top_right, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg c)] at h
          exact (ENNReal.ofReal_eq_ofReal_iff (kFunctional_nonneg ht.le) (by positivity)).1 h
        rw [Pi.smul_apply, smul_eq_mul, hk,
          Real.norm_of_nonneg (mul_nonneg (norm_nonneg c)
            (mul_nonneg (Real.rpow_nonneg ht.le _) (le_min ht.le hm.le))),
          show ‖c‖ * (t ^ (-θ) * min t m) = t ^ (-θ) * (‖c‖ * min t m) by ring]
        gcongr
        exact min_le_left t m

/-- **The `K`-method norm of an indicator function.** For `0 < θ < 1` and an element `u` of
`L¹ + L^∞` represented by `c 1_A`,
`‖u‖_{θ,q} = c_{θ,q} ‖c‖ μ A ^ (1 - θ)`.
Comparing `c_{θ,q} = (θ (1 - θ) q) ^ (-1 / q)` (`kMethodConst_eq`) with the Lorentz indicator
constant `(p / q) ^ (1 / q) = ((1 - θ) q) ^ (-1 / q)` (`eLorentzNorm_indicator_const₀` at
`1 / p = 1 - θ`) exhibits the exact factor `θ ^ (-1 / q)` (equal to `1` at `q = ∞`). -/
theorem kMethodENorm_l1Linfty_indicator {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (q : ℝ≥0∞)
    {u : L1AddLinfty 𝕜 E μ} {A : Set α} {c : E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] A.indicator fun _ => c) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u = kMethodConst θ q * ‖c‖ₑ * μ A ^ (1 - θ) := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  have h0_ae : ⇑(L1AddLinfty.toAEEqFun 𝕜 (0 : L1AddLinfty 𝕜 E μ)) =ᵐ[μ] (0 : α → E) := by
    rw [map_zero]
    exact AEEqFun.coeFn_zero
  rcases eq_or_ne q 0 with rfl | hq0
  · have hcont : ContinuousOn (fun t : ℝ => t ^ (-θ) * min 1 t) (Ioi 0) :=
      (continuousOn_id.rpow_const fun _ ht => Or.inl (ne_of_gt ht)).mul
        (continuous_const.min continuous_id).continuousOn
    rw [kMethodENorm_def, eLpNorm_exponent_zero
      (aestronglyMeasurable_rpow_neg_mul_kFunctional θ u), kMethodConst_def,
      eLpNorm_exponent_zero hcont.aestronglyMeasurable_multHaar]
    simp
  rcases eq_or_ne c 0 with rfl | hc
  · have hzero : (A.indicator fun _ : α => (0 : E)) = 0 := by ext; simp
    have hu0 : u = 0 :=
      L1AddLinfty.toAEEqFun_injective <| AEEqFun.ext ((hzero ▸ hu).trans h0_ae.symm)
    simp [hu0]
  rcases eq_or_ne (μ A) 0 with hA0 | hA0
  · have hu0 : u = 0 := L1AddLinfty.toAEEqFun_injective <| AEEqFun.ext <|
      (hu.trans (indicator_ae_eq_zero.2 (measure_mono_null inter_subset_left hA0))).trans h0_ae.symm
    simp [hu0, hA0, ENNReal.zero_rpow_of_pos h1θ]
  rcases eq_or_ne (μ A) ∞ with hAtop | hAfin
  · rw [kMethodENorm_l1Linfty_indicator_eq_top_of_measure_eq_top hθ hq0 hc hAtop hu, hAtop,
      ENNReal.top_rpow_of_pos h1θ,
      ENNReal.mul_top (mul_ne_zero (kMethodConst_ne_zero θ hq0) (eNorm_ne_zero.2 hc))]
  · set m : ℝ := (μ A).toReal
    have hm : 0 < m := ENNReal.toReal_pos hA0 hAfin
    have hae : (fun t : ℝ => t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u) =ᵐ[multHaar]
        ‖c‖ • fun t : ℝ => t ^ (-θ) * min t m := by
      filter_upwards [ae_pos_multHaar] with t ht
      have hk := ofReal_kFunctional_l1Linfty_indicator hu ht.le
      rw [← ENNReal.ofReal_toReal hAfin, ← ENNReal.ofReal_min, ← ofReal_norm,
        ← ENNReal.ofReal_mul (norm_nonneg c)] at hk
      rw [(ENNReal.ofReal_eq_ofReal_iff (kFunctional_nonneg ht.le)
        (mul_nonneg (norm_nonneg c) (le_min ht.le hm.le))).1 hk, Pi.smul_apply, smul_eq_mul]
      ring
    rw [kMethodENorm_def, eLpNorm_congr_ae hae, eLpNorm_const_smul, eNorm_norm,
      eLpNorm_rpow_neg_mul_min_const θ q hm, ← ENNReal.ofReal_rpow_of_pos hm,
      ENNReal.ofReal_toReal hAfin]
    ring

end RealNormedSpace

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

/-- Every Lorentz function with `1 < p < ∞` and `q ≠ 0` represents an element of `L¹ + L^∞`:
weak-`L^p` control `‖f‖* s ≤ ‖f‖_{p,∞} s ^ (-1 / p)` is integrable on `(0, 1]` because
`1 / p < 1`. -/
theorem exists_toAEEqFun_ae_eq_of_memLorentz {p q : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞)
    (hq0 : q ≠ 0) {f : α → E} (hf : MemLorentz f p q μ) :
    ∃ u : L1AddLinfty 𝕜 E μ, ⇑(toAEEqFun 𝕜 u) =ᵐ[μ] f := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hp_gt : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).2 hp1
  have hinv_lt : p.toReal⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp_gt
  have hf_top : MemLorentz f p ∞ μ := hf.mono_exponent hq0 le_top
  refine (exists_toAEEqFun_ae_eq_iff_lintegral_decreasingRearrangement_lt_top (𝕜 := 𝕜) one_pos).2
    ⟨hf.aestronglyMeasurable, ?_⟩
  rw [← restrict_Ioo_eq_restrict_Ioc]
  calc ∫⁻ s in Ioo 0 1, μ.decreasingRearrangement (‖f ·‖ₑ) s
      ≤ ∫⁻ s in Ioo 0 1, eLorentzNorm f p ∞ μ * ENNReal.ofReal (s ^ (-p.toReal⁻¹)) := by
        refine setLIntegral_mono' measurableSet_Ioo fun s ⟨hs, _⟩ => ?_
        have hle := ofReal_mul_decreasingRearrangement_le_eLorentzNorm (μ := μ) hp0 hp
          ENNReal.top_ne_zero hs f
        simp only [ENNReal.toReal_top, div_zero, inv_zero, Real.rpow_zero, one_mul] at hle
        calc μ.decreasingRearrangement (‖f ·‖ₑ) s
            = (ENNReal.ofReal (s ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) s) *
                ENNReal.ofReal (s ^ (-p.toReal⁻¹)) := by
              rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hs,
                add_neg_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
          _ ≤ eLorentzNorm f p ∞ μ * ENNReal.ofReal (s ^ (-p.toReal⁻¹)) := by gcongr
    _ = eLorentzNorm f p ∞ μ * ∫⁻ s in Ioo 0 1, ENNReal.ofReal (s ^ (-p.toReal⁻¹)) :=
        lintegral_const_mul'' _ (by fun_prop)
    _ < ∞ := by
        rw [TauCeti.lintegral_ofReal_rpow_Ioo (by linarith) zero_le_one]
        exact ENNReal.mul_lt_top hf_top.eLorentzNorm_lt_top ENNReal.ofReal_lt_top

end TauCeti.L1AddLinfty

namespace TauCeti.CompatibleCouple

variable {𝕜 E : Type*} {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Function-level characterization of `(L¹, L^∞)_{θ,q}`.** For `0 < θ < 1`, `1 ≤ q`, and
`1 / p = 1 - θ`, a function `f : α → E` represents an element of `(lebesgue 𝕜 E μ 1 ∞).kMethod θ q`
if and only if `MemLorentz f p q μ`. -/
theorem exists_mem_kMethod_lebesgue_one_top_iff_memLorentz {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    {p q : ℝ≥0∞} (hq : 1 ≤ q) (hp : p.toReal⁻¹ = 1 - θ) {f : α → E} :
    (∃ v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q,
        ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f) ↔
      MemLorentz f p q μ := by
  refine ⟨fun ⟨v, hv_mem, hv_ae⟩ =>
    (mem_kMethod_lebesgue_one_top_iff_memLorentz hθ hq hp hv_ae).1 hv_mem, fun hf => ?_⟩
  obtain ⟨hp1, hp_top⟩ := one_lt_and_ne_top_of_toReal_inv_eq hθ hp
  obtain ⟨u, hu⟩ := L1AddLinfty.exists_toAEEqFun_ae_eq_of_memLorentz (𝕜 := 𝕜) hp1 hp_top
    (zero_lt_one.trans_le hq).ne' hf
  obtain ⟨v, rfl⟩ := lebesgue_one_top_sumSpaceEmbed_surjective u
  exact ⟨v, (mem_kMethod_lebesgue_one_top_iff_memLorentz hθ hq hp hu).2 hf, hu⟩

/-! ### Diagonal isomorphism `(L¹, L^∞)_{θ,p} ≃L[𝕜] L^p` -/

section Equiv

variable {θ : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

open KMethodSpace

variable (𝕜 E μ) in
private def lebesgueOneTopKMethodToLpₗ (hθ : θ ∈ Ioo 0 1) (hp : p.toReal⁻¹ = 1 - θ) :
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p →ₗ[𝕜] Lp E p μ where
  toFun u := ⟨L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (toSumₗ u)),
    Lp.mem_Lp_iff_memLp.2 <| memLorentz_self_iff.1 <|
      (mem_kMethod_lebesgue_one_top_iff_memLorentz hθ (Fact.out : 1 ≤ p) hp EventuallyEq.rfl).1
        (toSumₗ_mem u)⟩
  map_add' _ _ := Subtype.ext (by simp only [map_add]; rfl)
  map_smul' _ _ := Subtype.ext (by simp only [RingHom.id_apply, map_smul]; rfl)

private theorem coe_lebesgueOneTopKMethodToLpₗ (hθ : θ ∈ Ioo 0 1) (hp : p.toReal⁻¹ = 1 - θ)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    (lebesgueOneTopKMethodToLpₗ 𝕜 E μ hθ hp u : α →ₘ[μ] E) =
      L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (toSumₗ u)) :=
  (rfl)

variable (𝕜 E μ) in
private def lpToLebesgueOneTopKMethodₗ (hθ : θ ∈ Ioo 0 1) (hp : p.toReal⁻¹ = 1 - θ) :
    Lp E p μ →ₗ[𝕜] (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p where
  toFun f := KMethodSpace.mk (lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f) <|
    (mem_kMethod_lebesgue_one_top_iff_memLorentz hθ (Fact.out : 1 ≤ p) hp
      (by simp)).2 (memLorentz_self_iff.2 (Lp.memLp f))
  map_add' _ _ := KMethodSpace.ext (by simp)
  map_smul' _ _ := KMethodSpace.ext (by simp)

private theorem toSumₗ_lpToLebesgueOneTopKMethodₗ (hθ : θ ∈ Ioo 0 1) (hp : p.toReal⁻¹ = 1 - θ)
    (f : Lp E p μ) :
    toSumₗ (lpToLebesgueOneTopKMethodₗ 𝕜 E μ hθ hp f) =
      lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f :=
  toSumₗ_mk _ _

private theorem norm_lebesgueOneTopKMethodToLpₗ_le (hθ : θ ∈ Ioo 0 1) (hp : p.toReal⁻¹ = 1 - θ)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    ‖lebesgueOneTopKMethodToLpₗ 𝕜 E μ hθ hp u‖ ≤ ‖u‖ := by
  obtain ⟨hp1, _⟩ := one_lt_and_ne_top_of_toReal_inv_eq hθ hp
  have h := eLorentzNorm_le_kMethodENorm_lebesgue_one_top (q := p) (zero_lt_one.trans hp1).ne' hp
    (v := toSumₗ u) (f := ⇑(lebesgueOneTopKMethodToLpₗ 𝕜 E μ hθ hp u)) EventuallyEq.rfl
  rw [eLorentzNorm_self, ← Lp.eNorm_def, ← _root_.ofReal_norm, ← KMethodSpace.ofReal_norm u] at h
  exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg u)).1 h

private theorem norm_lpToLebesgueOneTopKMethodₗ_le (hθ : θ ∈ Ioo 0 1) (hp : p.toReal⁻¹ = 1 - θ)
    (f : Lp E p μ) :
    ‖lpToLebesgueOneTopKMethodₗ 𝕜 E μ hθ hp f‖ ≤ 2 * θ⁻¹ * ‖f‖ := by
  have h := kMethodENorm_lebesgue_one_top_le_two_mul_eLorentzNorm (𝕜 := 𝕜) hθ (Fact.out : 1 ≤ p)
    hp (v := lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f) (f := ⇑f) (by simp)
  have h0 : 0 ≤ 2 * θ⁻¹ * ‖f‖ := by
    have := hθ.1
    positivity
  rw [eLorentzNorm_self, ← Lp.eNorm_def, ← _root_.ofReal_norm,
    ← ENNReal.ofReal_mul (by have := hθ.1; positivity),
    ← toSumₗ_lpToLebesgueOneTopKMethodₗ (𝕜 := 𝕜) hθ hp f,
    ← KMethodSpace.ofReal_norm (lpToLebesgueOneTopKMethodₗ 𝕜 E μ hθ hp f)] at h
  exact (ENNReal.ofReal_le_ofReal_iff h0).1 h

variable (𝕜 E μ) in
private def lebesgueOneTopKMethodToLp (hθ : θ ∈ Ioo 0 1) (hp : p.toReal⁻¹ = 1 - θ) :
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous (lebesgueOneTopKMethodToLpₗ 𝕜 E μ hθ hp) 1 fun u => by
    simpa only [one_mul] using norm_lebesgueOneTopKMethodToLpₗ_le hθ hp u

variable (𝕜 E μ) in
private def lpToLebesgueOneTopKMethod (hθ : θ ∈ Ioo 0 1) (hp : p.toReal⁻¹ = 1 - θ) :
    Lp E p μ →L[𝕜] (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p :=
  LinearMap.mkContinuous (lpToLebesgueOneTopKMethodₗ 𝕜 E μ hθ hp) (2 * θ⁻¹)
    (norm_lpToLebesgueOneTopKMethodₗ_le hθ hp)

private theorem leftInverse_lpToLebesgueOneTopKMethod (hθ : θ ∈ Ioo 0 1)
    (hp : p.toReal⁻¹ = 1 - θ) :
    Function.LeftInverse (lpToLebesgueOneTopKMethod 𝕜 E μ hθ hp)
      (lebesgueOneTopKMethodToLp 𝕜 E μ hθ hp) := fun u => by
  apply KMethodSpace.ext
  apply (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed_injective
  apply L1AddLinfty.toAEEqFun_injective
  change L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed
      (toSumₗ (lpToLebesgueOneTopKMethodₗ 𝕜 E μ hθ hp
        (lebesgueOneTopKMethodToLpₗ 𝕜 E μ hθ hp u)))) =
    L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (toSumₗ u))
  rw [toSumₗ_lpToLebesgueOneTopKMethodₗ, sumSpaceEmbed_lpToLebesgueSum,
    L1AddLinfty.toAEEqFun_ofLp, coe_lebesgueOneTopKMethodToLpₗ]

private theorem rightInverse_lpToLebesgueOneTopKMethod (hθ : θ ∈ Ioo 0 1)
    (hp : p.toReal⁻¹ = 1 - θ) :
    Function.RightInverse (lpToLebesgueOneTopKMethod 𝕜 E μ hθ hp)
      (lebesgueOneTopKMethodToLp 𝕜 E μ hθ hp) := fun f => by
  apply Subtype.ext
  change (lebesgueOneTopKMethodToLpₗ 𝕜 E μ hθ hp
    (lpToLebesgueOneTopKMethodₗ 𝕜 E μ hθ hp f) : α →ₘ[μ] E) = f
  rw [coe_lebesgueOneTopKMethodToLpₗ, toSumₗ_lpToLebesgueOneTopKMethodₗ,
    sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp]

variable (𝕜 E μ) in
/-- **Diagonal real interpolation of `(L¹, L^∞)`.** For `0 < θ < 1` and `1 / p = 1 - θ`, the real
interpolation space `(L¹(μ; E), L^∞(μ; E))_{θ,p}` is continuously linearly isomorphic to
`L^p(μ; E)`, with forward norm at most `1` and inverse norm at most `2 θ⁻¹` (sharpened to `θ⁻¹`
when `E` is also a real normed space, `norm_lebesgueOneTopKMethodEquivLp_symm_le`). -/
def lebesgueOneTopKMethodEquivLp (hθ : θ ∈ Ioo 0 1) (hp : p.toReal⁻¹ = 1 - θ) :
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p ≃L[𝕜] Lp E p μ :=
  ContinuousLinearEquiv.equivOfInverse
    (lebesgueOneTopKMethodToLp 𝕜 E μ hθ hp)
    (lpToLebesgueOneTopKMethod 𝕜 E μ hθ hp)
    (leftInverse_lpToLebesgueOneTopKMethod hθ hp)
    (rightInverse_lpToLebesgueOneTopKMethod hθ hp)

@[simp]
theorem coe_lebesgueOneTopKMethodEquivLp (hθ : θ ∈ Ioo 0 1) (hp : p.toReal⁻¹ = 1 - θ)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    (lebesgueOneTopKMethodEquivLp 𝕜 E μ hθ hp u : α →ₘ[μ] E) =
      L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (toSumₗ u)) :=
  (rfl)

@[simp]
theorem toSumₗ_lebesgueOneTopKMethodEquivLp_symm (hθ : θ ∈ Ioo 0 1) (hp : p.toReal⁻¹ = 1 - θ)
    (f : Lp E p μ) :
    toSumₗ ((lebesgueOneTopKMethodEquivLp 𝕜 E μ hθ hp).symm f) =
      lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f :=
  toSumₗ_mk _ _

theorem norm_lebesgueOneTopKMethodEquivLp_le (hθ : θ ∈ Ioo 0 1) (hp : p.toReal⁻¹ = 1 - θ)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    ‖lebesgueOneTopKMethodEquivLp 𝕜 E μ hθ hp u‖ ≤ ‖u‖ :=
  norm_lebesgueOneTopKMethodToLpₗ_le hθ hp u

theorem norm_lebesgueOneTopKMethodEquivLp_symm_le_two_mul (hθ : θ ∈ Ioo 0 1)
    (hp : p.toReal⁻¹ = 1 - θ) (f : Lp E p μ) :
    ‖(lebesgueOneTopKMethodEquivLp 𝕜 E μ hθ hp).symm f‖ ≤ 2 * θ⁻¹ * ‖f‖ :=
  norm_lpToLebesgueOneTopKMethodₗ_le hθ hp f

theorem norm_lebesgueOneTopKMethodEquivLp_symm_le [NormedSpace ℝ E] (hθ : θ ∈ Ioo 0 1)
    (hp : p.toReal⁻¹ = 1 - θ) (f : Lp E p μ) :
    ‖(lebesgueOneTopKMethodEquivLp 𝕜 E μ hθ hp).symm f‖ ≤ θ⁻¹ * ‖f‖ := by
  have h := kMethodENorm_lebesgue_one_top_le_eLorentzNorm (𝕜 := 𝕜) hθ (Fact.out : 1 ≤ p) hp
    (v := toSumₗ ((lebesgueOneTopKMethodEquivLp 𝕜 E μ hθ hp).symm f)) (f := ⇑f) (by simp)
  have hθ0 : 0 ≤ θ⁻¹ := inv_nonneg.2 hθ.1.le
  rw [eLorentzNorm_self, ← Lp.eNorm_def, ← _root_.ofReal_norm, ← ENNReal.ofReal_mul hθ0,
    ← KMethodSpace.ofReal_norm] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hθ0 (norm_nonneg f))).1 h

end Equiv

end TauCeti.CompatibleCouple
