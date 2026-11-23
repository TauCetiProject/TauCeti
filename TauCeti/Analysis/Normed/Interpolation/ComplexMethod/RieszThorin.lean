/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.ToLp
import TauCeti.MeasureTheory.Function.SimpleFunc.Dense

/-!
# The Riesz–Thorin theorem for maps of Lebesgue couples

Let `1 ≤ p₀, p₁, q₀, q₁ ≤ ∞`, and let `T₀ : L^{p₀}(μ; E) → L^{q₀}(ν; F)` and
`T₁ : L^{p₁}(μ; E) → L^{q₁}(ν; F)` be bounded complex-linear operators, for a complex Banach space
`E` and a complex inner product space `F`, that agree on common elements: `T₀ f₀ = T₁ f₁` almost
everywhere whenever `f₀ = f₁` almost everywhere. Together they define one operator `T` on the sum
`L^{p₀} + L^{p₁}`, with values in `L^{q₀} + L^{q₁}`, by `T (f₀ + f₁) = T₀ f₀ + T₁ f₁`. For
`0 < θ < 1` put

`1 / p = (1 - θ) / p₀ + θ / p₁` and `1 / q = (1 - θ) / q₀ + θ / q₁`,

and suppose `p, q < ∞` and that `ν` is σ-finite. The **Riesz–Thorin theorem** says that `T` maps
`Lᵖ` into `L^q` with norm at most `‖T₀‖ ^ (1 - θ) ‖T₁‖ ^ θ`. This file constructs that operator,
`TauCeti.CompatibleCouple.lebesgueMap`, as a continuous linear map `Lᵖ → L^q`, and proves:

* `TauCeti.CompatibleCouple.coeFn_lebesgueMap_of_ae_eq_add`: it is the restriction of `T`: if
  `f = f₀ + f₁` almost everywhere with `fⱼ ∈ L^{pⱼ}`, then `T f = T₀ f₀ + T₁ f₁` almost
  everywhere. In particular it agrees with `T₀` on `Lᵖ ∩ L^{p₀}` and with `T₁` on `Lᵖ ∩ L^{p₁}`
  (`coeFn_lebesgueMap_of_ae_eq_fst`, `coeFn_lebesgueMap_of_ae_eq_snd`).
* `TauCeti.CompatibleCouple.norm_lebesgueMap_le` and `opNorm_lebesgueMap_le_opNorm`: the bound
  `‖T f‖_q ≤ M₀ ^ (1 - θ) M₁ ^ θ ‖f‖_p` whenever `M₀` and `M₁` bound `T₀` and `T₁`.
* `TauCeti.CompatibleCouple.coeFn_lebesgueMap_ae_eq_lebesgueMap`: the operators obtained at two
  parameters `θ` and `θ'` agree on `L^{p_θ} ∩ L^{p_θ'}`, since both are restrictions of `T`.
* `TauCeti.CompatibleCouple.eq_lebesgueMap_of_fst`: it is the only bounded operator `Lᵖ → L^q`
  that agrees with `T₀` on `Lᵖ ∩ L^{p₀}`, because the simple functions of `Lᵖ` lie in `L^{p₀}` and
  are dense in `Lᵖ`. Likewise it is the only one that agrees with `T₁` on `Lᵖ ∩ L^{p₁}`
  (`eq_lebesgueMap_of_snd`).

The endpoint exponents may be infinite; only the interpolated exponents `p` and `q` must be
finite. The scalar form of the theorem for operators defined on simple functions, which allows
`q = ∞` as well, is `TauCeti.eLpNorm_le_rpow_mul_rpow_mul_eLpNorm`.

## The argument

The pair `(T₀, T₁)` is a map of the Lebesgue couples `(L^{p₀}, L^{p₁}) → (L^{q₀}, L^{q₁})`, so the
complex method gives a map `[L^{p₀}, L^{p₁}]_θ → [L^{q₀}, L^{q₁}]_θ` of norm at most
`‖T₀‖ ^ (1 - θ) ‖T₁‖ ^ θ` lying over `T` (`ComplexMethodSpace.map`; Bergh–Löfström,
Theorem 4.1.2). Calderón's identification of the complex interpolation spaces of the Lebesgue
couples, `[L^{p₀}, L^{p₁}]_θ = Lᵖ` and `[L^{q₀}, L^{q₁}]_θ = L^q` with equal norms
(`lpToLebesgueComplexMethod` and `ComplexMethodSpace.lebesgueToLp`; Bergh–Löfström,
Theorem 5.1.1), turns it into the operator `Lᵖ → L^q`. All of these maps lie over the embeddings
of the spaces into `L¹ + L^∞`, which is how the formula `T (f₀ + f₁) = T₀ f₀ + T₁ f₁` is read
off. That `(T₀, T₁)` is a map of couples is `lebesgue_fstToSum_eq_sndToSum`.

## References

* M. Riesz, *Sur les maxima des formes bilinéaires et sur les fonctionnelles linéaires*,
  Acta Math. 49 (1927).
* G. O. Thorin, *An extension of a convexity theorem due to M. Riesz*, Kungl. Fysiogr. Sällsk.
  i Lund Förh. 8 (1939).
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, Theorem 1.1.1, and §4.1 and §5.1 for the proof by the complex method.
* L. Grafakos, *Classical Fourier Analysis*, Theorem 1.3.4.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.CompatibleCouple

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} {ν : Measure β}
  {p₀ p₁ p q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)] [Fact (1 ≤ q₀)]
  [Fact (1 ≤ q₁)] [Fact (1 ≤ q)]

variable [SigmaFinite ν] (T₀ : Lp E p₀ μ →L[ℂ] Lp F q₀ ν) (T₁ : Lp E p₁ μ →L[ℂ] Lp F q₁ ν)
  (h : ∀ (f₀ : Lp E p₀ μ) (f₁ : Lp E p₁ μ), ⇑f₀ =ᵐ[μ] ⇑f₁ → ⇑(T₀ f₀) =ᵐ[ν] ⇑(T₁ f₁))
  {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
  (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)
  (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) (hq_top : q ≠ ∞)

/-- **The Riesz–Thorin operator.** Let `T₀ : L^{p₀} → L^{q₀}` and `T₁ : L^{p₁} → L^{q₁}` be bounded
operators that agree almost everywhere on functions agreeing almost everywhere, and let
`0 < θ < 1`, `1 / p = (1 - θ) / p₀ + θ / p₁` and `1 / q = (1 - θ) / q₀ + θ / q₁` with `p, q < ∞`.
This is the bounded operator `Lᵖ → L^q` that sends `f = f₀ + f₁`, `fⱼ ∈ L^{pⱼ}`, to
`T₀ f₀ + T₁ f₁` (`coeFn_lebesgueMap_of_ae_eq_add`). Its norm is at most
`‖T₀‖ ^ (1 - θ) ‖T₁‖ ^ θ` (`opNorm_lebesgueMap_le_opNorm`). -/
def lebesgueMap : Lp E p μ →L[ℂ] Lp F q ν :=
  (ComplexMethodSpace.lebesgueToLp hθ hq hq_top).comp
    ((ComplexMethodSpace.map θ T₀ T₁ (lebesgue_fstToSum_eq_sndToSum T₀ T₁ h)).comp
      (lpToLebesgueComplexMethod (Ioo_subset_Icc_self hθ) hp hp_top))

private theorem lebesgueMap_apply (f : Lp E p μ) :
    lebesgueMap T₀ T₁ h hθ hp hp_top hq hq_top f =
      ComplexMethodSpace.lebesgueToLp hθ hq hq_top
        (ComplexMethodSpace.map θ T₀ T₁ (lebesgue_fstToSum_eq_sndToSum T₀ T₁ h)
          (lpToLebesgueComplexMethod (Ioo_subset_Icc_self hθ) hp hp_top f)) :=
  (rfl)

/-- **The Riesz–Thorin operator is the restriction of `T₀ + T₁`.** If `f ∈ Lᵖ` agrees almost
everywhere with `f₀ + f₁` for `f₀ ∈ L^{p₀}` and `f₁ ∈ L^{p₁}`, then
`T f = T₀ f₀ + T₁ f₁` almost everywhere. -/
theorem coeFn_lebesgueMap_of_ae_eq_add {f : Lp E p μ} {f₀ : Lp E p₀ μ} {f₁ : Lp E p₁ μ}
    (hf : ⇑f =ᵐ[μ] ⇑f₀ + ⇑f₁) :
    ⇑(lebesgueMap T₀ T₁ h hθ hp hp_top hq hq_top f) =ᵐ[ν] ⇑(T₀ f₀) + ⇑(T₁ f₁) := by
  -- In `L^{p₀} + L^{p₁}`, the element of `[L^{p₀}, L^{p₁}]_θ` representing `f` is `f₀ + f₁`.
  have hu : ComplexMethodSpace.toSum
      (lpToLebesgueComplexMethod (Ioo_subset_Icc_self hθ) hp hp_top f) =
        (lebesgue ℂ E μ p₀ p₁).fstToSum f₀ + (lebesgue ℂ E μ p₀ p₁).sndToSum f₁ := by
    refine sumSpace_ext _ ?_
    rw [sumSpaceEmbed_toSum_lpToLebesgueComplexMethod]
    exact (lebesgue_sumSpaceEmbed_fstToSum_add_sndToSum_eq_ofLp_iff.2 hf.symm).symm
  refine (lebesgue_sumSpaceEmbed_fstToSum_add_sndToSum_eq_ofLp_iff (𝕜 := ℂ)).1 ?_ |>.symm
  rw [lebesgueMap_apply, ComplexMethodSpace.ofLp_lebesgueToLp]
  congr 1
  rw [ComplexMethodSpace.toSum_map, hu, map_add]
  have hT := lebesgue_fstToSum_eq_sndToSum T₀ T₁ h
  exact congr_arg₂ (· + ·)
    ((lebesgue ℂ E μ p₀ p₁).sumLift_fstToSum ((lebesgue ℂ F ν q₀ q₁).fstToSum.comp T₀)
      ((lebesgue ℂ F ν q₀ q₁).sndToSum.comp T₁) hT f₀).symm
    ((lebesgue ℂ E μ p₀ p₁).sumLift_sndToSum ((lebesgue ℂ F ν q₀ q₁).fstToSum.comp T₀)
      ((lebesgue ℂ F ν q₀ q₁).sndToSum.comp T₁) hT f₁).symm

/-- The Riesz–Thorin operator agrees with `T₀` on `Lᵖ ∩ L^{p₀}`. -/
theorem coeFn_lebesgueMap_of_ae_eq_fst {f : Lp E p μ} {f₀ : Lp E p₀ μ} (hf : ⇑f =ᵐ[μ] ⇑f₀) :
    ⇑(lebesgueMap T₀ T₁ h hθ hp hp_top hq hq_top f) =ᵐ[ν] ⇑(T₀ f₀) := by
  have hf' : ⇑f =ᵐ[μ] ⇑f₀ + ⇑(0 : Lp E p₁ μ) := by
    filter_upwards [hf, Lp.coeFn_zero E p₁ μ] with x hx h0
    rw [Pi.add_apply, hx, h0, Pi.zero_apply, add_zero]
  filter_upwards [coeFn_lebesgueMap_of_ae_eq_add T₀ T₁ h hθ hp hp_top hq hq_top hf',
    Lp.coeFn_zero F q₁ ν] with x hx h0
  rw [hx, Pi.add_apply, map_zero, h0, Pi.zero_apply, add_zero]

/-- The Riesz–Thorin operator agrees with `T₁` on `Lᵖ ∩ L^{p₁}`. -/
theorem coeFn_lebesgueMap_of_ae_eq_snd {f : Lp E p μ} {f₁ : Lp E p₁ μ} (hf : ⇑f =ᵐ[μ] ⇑f₁) :
    ⇑(lebesgueMap T₀ T₁ h hθ hp hp_top hq hq_top f) =ᵐ[ν] ⇑(T₁ f₁) := by
  have hf' : ⇑f =ᵐ[μ] ⇑(0 : Lp E p₀ μ) + ⇑f₁ := by
    filter_upwards [hf, Lp.coeFn_zero E p₀ μ] with x hx h0
    rw [Pi.add_apply, hx, h0, Pi.zero_apply, zero_add]
  filter_upwards [coeFn_lebesgueMap_of_ae_eq_add T₀ T₁ h hθ hp hp_top hq hq_top hf',
    Lp.coeFn_zero F q₀ ν] with x hx h0
  rw [hx, Pi.add_apply, map_zero, h0, Pi.zero_apply, zero_add]

/-- **The Riesz–Thorin theorem.** If `‖T₀ f‖_{q₀} ≤ M₀ ‖f‖_{p₀}` and `‖T₁ f‖_{q₁} ≤ M₁ ‖f‖_{p₁}`,
then `‖T f‖_q ≤ M₀ ^ (1 - θ) M₁ ^ θ ‖f‖_p` on `Lᵖ`. -/
theorem norm_lebesgueMap_le {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ f, ‖T₀ f‖ ≤ M₀ * ‖f‖) (h₁ : ∀ f, ‖T₁ f‖ ≤ M₁ * ‖f‖) (f : Lp E p μ) :
    ‖lebesgueMap T₀ T₁ h hθ hp hp_top hq hq_top f‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖f‖ := by
  rw [lebesgueMap_apply]
  refine (ComplexMethodSpace.norm_lebesgueToLp_le hθ hq hq_top _).trans <|
    (ComplexMethodSpace.norm_map_le T₀ T₁ _ (Ioo_subset_Icc_self hθ) hM₀ hM₁ h₀ h₁ _).trans ?_
  gcongr
  exact norm_lpToLebesgueComplexMethod_le _ hp hp_top f

/-- **The Riesz–Thorin theorem**, in terms of operator norms:
`‖T‖_{Lᵖ → L^q} ≤ ‖T₀‖ ^ (1 - θ) ‖T₁‖ ^ θ`. -/
theorem opNorm_lebesgueMap_le_opNorm :
    ‖lebesgueMap T₀ T₁ h hθ hp hp_top hq hq_top‖ ≤ ‖T₀‖ ^ (1 - θ) * ‖T₁‖ ^ θ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_lebesgueMap_le T₀ T₁ h hθ hp hp_top hq hq_top (norm_nonneg T₀) (norm_nonneg T₁)
      T₀.le_opNorm T₁.le_opNorm)

/-- **Consistency of the Riesz–Thorin operators.** The operators obtained at two parameters `θ`
and `θ'` agree on `L^{p_θ} ∩ L^{p_θ'}`: both send a function to `T₀ f₀ + T₁ f₁` for any
decomposition `f₀ + f₁` of it. -/
theorem coeFn_lebesgueMap_ae_eq_lebesgueMap {p' q' : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ q')]
    {θ' : ℝ} (hθ' : θ' ∈ Ioo (0 : ℝ) 1)
    (hp' : p'⁻¹ = ENNReal.ofReal (1 - θ') * p₀⁻¹ + ENNReal.ofReal θ' * p₁⁻¹) (hp'_top : p' ≠ ∞)
    (hq' : q'⁻¹ = ENNReal.ofReal (1 - θ') * q₀⁻¹ + ENNReal.ofReal θ' * q₁⁻¹) (hq'_top : q' ≠ ∞)
    {f : Lp E p μ} {g : Lp E p' μ} (hfg : ⇑f =ᵐ[μ] ⇑g) :
    ⇑(lebesgueMap T₀ T₁ h hθ hp hp_top hq hq_top f) =ᵐ[ν]
      ⇑(lebesgueMap T₀ T₁ h hθ' hp' hp'_top hq' hq'_top g) := by
  -- Decompose `f` as `f₀ + f₁` through the element of `L^{p₀} + L^{p₁}` it represents.
  obtain ⟨f₀, f₁, hsum⟩ := (lebesgue ℂ E μ p₀ p₁).exists_fstToSum_add_sndToSum_eq
    (ComplexMethodSpace.toSum (lpToLebesgueComplexMethod (Ioo_subset_Icc_self hθ) hp hp_top f))
  have hf : ⇑f =ᵐ[μ] ⇑f₀ + ⇑f₁ := by
    refine (lebesgue_sumSpaceEmbed_fstToSum_add_sndToSum_eq_ofLp_iff (𝕜 := ℂ)).1 ?_ |>.symm
    rw [hsum, sumSpaceEmbed_toSum_lpToLebesgueComplexMethod]
  exact (coeFn_lebesgueMap_of_ae_eq_add T₀ T₁ h hθ hp hp_top hq hq_top hf).trans
    (coeFn_lebesgueMap_of_ae_eq_add T₀ T₁ h hθ' hp' hp'_top hq' hq'_top (hfg.symm.trans hf)).symm

/-- **Uniqueness of the Riesz–Thorin operator.** A bounded operator `S : Lᵖ → L^q` that agrees
with `T₀` on `Lᵖ ∩ L^{p₀}` is the Riesz–Thorin operator. -/
theorem eq_lebesgueMap_of_fst {S : Lp E p μ →L[ℂ] Lp F q ν}
    (hS : ∀ (f : Lp E p μ) (f₀ : Lp E p₀ μ), ⇑f =ᵐ[μ] ⇑f₀ → ⇑(S f) =ᵐ[ν] ⇑(T₀ f₀)) :
    S = lebesgueMap T₀ T₁ h hθ hp hp_top hq hq_top :=
  Lp.continuousLinearMap_ext_of_memLp hp_top fun _ hf =>
    Lp.ext ((hS _ _ hf.coeFn_toLp.symm).trans
      (coeFn_lebesgueMap_of_ae_eq_fst T₀ T₁ h hθ hp hp_top hq hq_top hf.coeFn_toLp.symm).symm)

/-- **Uniqueness of the Riesz–Thorin operator.** A bounded operator `S : Lᵖ → L^q` that agrees
with `T₁` on `Lᵖ ∩ L^{p₁}` is the Riesz–Thorin operator. -/
theorem eq_lebesgueMap_of_snd {S : Lp E p μ →L[ℂ] Lp F q ν}
    (hS : ∀ (f : Lp E p μ) (f₁ : Lp E p₁ μ), ⇑f =ᵐ[μ] ⇑f₁ → ⇑(S f) =ᵐ[ν] ⇑(T₁ f₁)) :
    S = lebesgueMap T₀ T₁ h hθ hp hp_top hq hq_top :=
  Lp.continuousLinearMap_ext_of_memLp hp_top fun _ hf =>
    Lp.ext ((hS _ _ hf.coeFn_toLp.symm).trans
      (coeFn_lebesgueMap_of_ae_eq_snd T₀ T₁ h hθ hp hp_top hq hq_top hf.coeFn_toLp.symm).symm)

end TauCeti.CompatibleCouple
