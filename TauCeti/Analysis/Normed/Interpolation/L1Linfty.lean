/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.KFunctional
public import TauCeti.MeasureTheory.Function.DecreasingRearrangement
public import TauCeti.MeasureTheory.Function.Lp.L1AddLinfty

/-!
# The `K`-functional of the couple `(L¹, L^∞)`

For the compatible couple `(L¹(μ; E), L^∞(μ; E))` (`TauCeti.CompatibleCouple.l1Linfty`) and
`t > 0`, Peetre's `K`-functional of an element `u` of `L¹ + L^∞` represented by a function `f` is
the integral of the decreasing rearrangement of `‖f‖` over `(0, t]`:

`K(t, u) = ∫₀ᵗ ‖f‖*`

(`TauCeti.CompatibleCouple.ofReal_kFunctional_l1Linfty`,
`TauCeti.CompatibleCouple.kFunctional_l1Linfty`). This is the formula
`MeasureTheory.Measure.lintegral_decreasingRearrangement_enorm_eq_iInf_eLpNorm`, which is stated
for arbitrary splittings `f = f₀ + f₁` measured by `Lᵖ` seminorms, transported to the
decompositions of `u` in the sum space of the couple, on which the real interpolation spaces
`(L¹, L^∞)_{θ,q}` are built. Since `K(t, u)` is a real number, the equation shows in particular
that `∫₀ᵗ ‖f‖*` is finite for every `f` in `L¹ + L^∞`.

As a check, the `K`-functional of `c 1_A` is `‖c‖ min (t, μ A)`
(`TauCeti.CompatibleCouple.ofReal_kFunctional_l1Linfty_indicator`): the decompositions
`c 1_A = c 1_A + 0` and `c 1_A = 0 + c 1_A` cost `‖c‖ μ A` and `t ‖c‖`, and no decomposition does
better.

The radial retraction attaining the infimum in the scalar formula scales vectors by real numbers,
so `E` is assumed to be a real normed space in addition to a normed space over the scalar field
`𝕜` of the couple.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.2 (Theorem 5.2.1).
* T. Fack and H. Kosaki, *Generalized s-numbers of τ-measurable operators*, Pacific J. Math.
  **123** (1986), 269–300, the formula following Theorem 4.4.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.CompatibleCouple

variable {𝕜 E : Type*} {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] {t : ℝ}

/-- **The `K`-functional of `(L¹, L^∞)`.** For `t > 0` and an element `u` of `L¹ + L^∞`
represented by `f`, `K(t, u) = ∫₀ᵗ ‖f‖*`. -/
theorem ofReal_kFunctional_l1Linfty {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) (ht : 0 < t) :
    ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) =
      ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hu
  refine le_antisymm ?_ (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
  · -- A splitting `f = f₀ + f₁` of finite cost gives a decomposition of `u` of the same cost.
    rw [μ.lintegral_decreasingRearrangement_enorm_eq_iInf_eLpNorm hf]
    refine le_iInf fun f₀ => le_iInf fun f₁ => le_iInf fun hsum => ?_
    by_cases hfin : eLpNorm f₀ 1 μ + ENNReal.ofReal t * eLpNorm f₁ ∞ μ = ∞
    · rw [hfin]
      exact le_top
    obtain ⟨hfin₀, hfin₁⟩ := ENNReal.add_ne_top.1 hfin
    have hfin₁' : eLpNorm f₁ ∞ μ ≠ ∞ := fun htop => hfin₁ <| by
      rw [htop, ENNReal.mul_top (by simpa using ht)]
    have h₀ : MemLp f₀ 1 μ := memLp_iff.2 hfin₀.lt_top
    have h₁ : MemLp f₁ ∞ μ := memLp_iff.2 hfin₁'.lt_top
    have hdec : (l1Linfty 𝕜 E μ).fstToSum (h₀.toLp f₀) + (l1Linfty 𝕜 E μ).sndToSum (h₁.toLp f₁) =
        u := by
      refine L1AddLinfty.fstToSum_add_sndToSum_eq_iff.2 ?_
      filter_upwards [h₀.coeFn_toLp, h₁.coeFn_toLp, hu] with y hy₀ hy₁ hy
      rw [Pi.add_apply, hy₀, hy₁, hy, ← Pi.add_apply, hsum]
    calc ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u)
        ≤ ENNReal.ofReal (‖h₀.toLp f₀‖ + t * ‖h₁.toLp f₁‖) :=
          ENNReal.ofReal_le_ofReal (kFunctional_le ht.le hdec)
      _ = eLpNorm f₀ 1 μ + ENNReal.ofReal t * eLpNorm f₁ ∞ μ := by
          rw [ENNReal.ofReal_add (norm_nonneg _) (by positivity), ENNReal.ofReal_mul ht.le,
            Lp.norm_toLp, Lp.norm_toLp, ENNReal.ofReal_toReal h₀.eLpNorm_ne_top,
            ENNReal.ofReal_toReal h₁.eLpNorm_ne_top]
  · -- Every decomposition `u = g + h` bounds `∫₀ᵗ ‖f‖*` by `‖g‖₁ + t ‖h‖_∞`.
    obtain ⟨g, h, hgh, hlt⟩ := (kFunctional_lt_iff ht.le).1
      (lt_add_of_pos_right ((l1Linfty 𝕜 E μ).kFunctional t u) (NNReal.coe_pos.2 hε))
    have hgh' : ⇑g + ⇑h =ᵐ[μ] f := (L1AddLinfty.fstToSum_add_sndToSum_eq_iff.1 hgh).trans hu
    calc ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s
        ≤ ∫⁻ y, ‖g y‖ₑ ∂μ + ENNReal.ofReal t * essSup (‖h ·‖ₑ) μ :=
          μ.lintegral_decreasingRearrangement_le_lintegral_add_mul_essSup hf.enorm t
            (hgh'.mono fun y hy => by
              simp only [Pi.add_apply] at hy ⊢
              rw [← hy]
              exact enorm_add_le (g y) (h y))
      _ = ENNReal.ofReal (‖g‖ + t * ‖h‖) := by
          rw [ENNReal.ofReal_add (norm_nonneg _) (by positivity), ENNReal.ofReal_mul ht.le,
            Lp.norm_def, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g),
            ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top h),
            eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable g),
            eLpNorm_exponent_top (Lp.aestronglyMeasurable h),
            eLpNormEssSup_eq_essSup_enorm]
      _ ≤ ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u + ε) :=
          ENNReal.ofReal_le_ofReal hlt.le
      _ = ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) + ε := by
          rw [ENNReal.ofReal_add (kFunctional_nonneg ht.le) ε.coe_nonneg,
            ENNReal.ofReal_coe_nnreal]

/-- **The `K`-functional of `(L¹, L^∞)`**, real form: for `t > 0` and an element `u` of
`L¹ + L^∞` represented by `f`, `K(t, u) = ∫₀ᵗ ‖f‖*`. -/
theorem kFunctional_l1Linfty {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) (ht : 0 < t) :
    (l1Linfty 𝕜 E μ).kFunctional t u =
      (∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s).toReal := by
  rw [← ofReal_kFunctional_l1Linfty hu ht, ENNReal.toReal_ofReal (kFunctional_nonneg ht.le)]

/-- The `K`-functional of `c 1_A` in `L¹ + L^∞` is `‖c‖ min (t, μ A)`, for `t > 0`. -/
theorem ofReal_kFunctional_l1Linfty_indicator {u : L1AddLinfty 𝕜 E μ} {A : Set α}
    {c : E} (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] A.indicator fun _ => c)
    (ht : 0 < t) :
    ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) = ‖c‖ₑ * min (ENNReal.ofReal t) (μ A) := by
  rw [ofReal_kFunctional_l1Linfty hu ht]
  simp_rw [enorm_indicator_eq_indicator_enorm, μ.decreasingRearrangement_indicator]
  have hS : MeasurableSet {s : ℝ | ENNReal.ofReal s < μ A} :=
    measurableSet_lt ENNReal.measurable_ofReal measurable_const
  have hind : (fun s : ℝ => if ENNReal.ofReal s < μ A then ‖c‖ₑ else 0) =
      {s : ℝ | ENNReal.ofReal s < μ A}.indicator fun _ => ‖c‖ₑ := by
    ext s
    simp [Set.indicator_apply]
  rw [hind, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc, lintegral_indicator_const hS,
    Measure.restrict_apply hS]
  congr 1
  rcases eq_or_ne (μ A) ∞ with hA | hA
  · simp [hA]
  have hset : {s : ℝ | ENNReal.ofReal s < μ A} ∩ Ioo 0 t = Ioo 0 t ∩ Iio (μ A).toReal := by
    ext s
    constructor
    · rintro ⟨hs, hs₀, hst⟩
      exact ⟨⟨hs₀, hst⟩, (ENNReal.ofReal_lt_iff_lt_toReal hs₀.le hA).1 hs⟩
    · rintro ⟨⟨hs₀, hst⟩, hs⟩
      exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal hs₀.le hA).2 hs, hs₀, hst⟩
  rw [hset, Ioo_inter_Iio, Real.volume_Ioo, sub_zero, ENNReal.ofReal_min,
    ENNReal.ofReal_toReal hA]

end TauCeti.CompatibleCouple
