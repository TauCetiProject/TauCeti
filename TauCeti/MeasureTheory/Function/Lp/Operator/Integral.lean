/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Integral operators with operator-valued kernels on `Lᵖ`

Let `K : α → β → (F →L[𝕜] G)` be an a.e. strongly measurable kernel on `μ.prod ν` whose
operator-norm row integrals `∫⁻ y, ‖K x y‖ₑ ∂ν` are at most `A` for almost every `x` and whose
column integrals `∫⁻ x, ‖K x y‖ₑ ∂μ` are at most `B` for almost every `y`. Then for every
`1 ≤ p ≤ ∞` the integral operator

`u ↦ (x ↦ ∫ y, K x y (u y) ∂ν)`

is a bounded operator `TauCeti.integralOperatorLp K p hK hA hB : Lp F p ν →L[𝕜] Lp G p μ` of
norm at most `A ^ (1 - 1/p) * B ^ (1/p)`, hence at most `max A B`. For `p = ∞` the exponent
`1/p` is `0`, so the bound is `A`.

This is the vector-valued form of Schur's test: for finite `p` it follows from the scalar
estimate `TauCeti.lintegral_rpow_lintegral_mul_le` applied to the norm kernel `‖K x y‖ₑ` and the
input `‖u y‖ₑ`, together with `‖∫ y, K x y (u y) ∂ν‖ₑ ≤ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν`; for `p = ∞`
only the row bound is used. Typical applications are Littlewood–Paley block estimates, where the
kernels of the localized operators between dyadic blocks have uniform `L¹` bounds in each
variable, and matrix-valued kernels acting on sections of a trivial finite-rank bundle.

## Main declarations

* `TauCeti.ae_integrable_apply_of_memLp`: for `u ∈ Lᵖ` the integrand `y ↦ K x y (u y)` is
  integrable for almost every `x`.
* `TauCeti.eLpNorm_integral_apply_le`: the `Lᵖ` bound for the integral operator on functions.
* `TauCeti.integralOperatorLp`: the integral operator as a bounded operator on `Lᵖ`.
* `TauCeti.norm_integralOperatorLp_le`, `TauCeti.norm_integralOperatorLp_le_max`: its norm
  bounds.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Theorem 6.18.
-/

public section

noncomputable section

open MeasureTheory Function
open scoped ENNReal NNReal

namespace TauCeti

variable {α β 𝕜 F G : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {K : α → β → F →L[𝕜] G} {u : β → F} {p : ℝ≥0∞}

/-- For `1 ≤ p ≤ ∞` the exponent `1 - 1/p` is nonnegative; for `p = ∞` it is `1`, as
`ENNReal.toReal ∞ = 0`. -/
private theorem one_sub_toReal_inv_nonneg (hp : 1 ≤ p) : 0 ≤ 1 - p.toReal⁻¹ := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · simp
  · exact sub_nonneg.2 (inv_le_one_of_one_le₀ (by simpa using ENNReal.toReal_mono hp_top hp))

omit [SFinite μ] in
/-- The pointwise estimate behind the `p = ∞` case: if the row integrals of `‖K‖ₑ` are at most
`A`, then `∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν ≤ A * ‖u‖_∞` for almost every `x`. -/
private theorem ae_lintegral_enorm_mul_le_mul_eLpNormEssSup
    (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν)) {A : ℝ≥0∞}
    (hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A) :
    ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν ≤ A * eLpNormEssSup u ν := by
  filter_upwards [hA, hK.prodMk_left] with x hx hKx
  calc ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν ≤ ∫⁻ y, ‖K x y‖ₑ * eLpNormEssSup u ν ∂ν :=
        lintegral_mono_ae <| by
          filter_upwards [ae_le_eLpNormEssSup (f := u) (μ := ν)] with y hy
          gcongr
    _ = (∫⁻ y, ‖K x y‖ₑ ∂ν) * eLpNormEssSup u ν := lintegral_mul_const'' _ hKx.enorm
    _ ≤ A * eLpNormEssSup u ν := by gcongr

/-- Schur's test for the norm kernel `‖K x y‖ₑ` of an a.e. strongly measurable operator-valued
kernel, together with the a.e. measurability of `x ↦ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν`. The
scalar Schur test needs a measurable kernel, so it is applied to a strongly measurable
modification of `K`, which agrees with `K` on almost every row and on almost every column. -/
private theorem lintegral_rpow_lintegral_enorm_mul_le
    (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν)) (hu : AEStronglyMeasurable u ν)
    {r : ℝ} (hr : 1 ≤ r) {A B : ℝ≥0∞} (hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B) :
    AEMeasurable (fun x ↦ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν) μ ∧
      ∫⁻ x, (∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν) ^ r ∂μ ≤
        A ^ (r - 1) * B * ∫⁻ y, ‖u y‖ₑ ^ r ∂ν := by
  set K' := hK.mk (uncurry K)
  have hrow : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, K x y = K' (x, y) := Measure.ae_ae_of_ae_prod hK.ae_eq_mk
  have hcol : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, K x y = K' (x, y) := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hK.ae_eq_mk)
  have hrow' : (fun x ↦ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν) =ᵐ[μ]
      fun x ↦ ∫⁻ y, ‖K' (x, y)‖ₑ * ‖u y‖ₑ ∂ν := by
    filter_upwards [hrow] with x hx
    exact lintegral_congr_ae <| hx.mono fun y hy ↦ by simp only [hy]
  have hk : Measurable (uncurry fun x y ↦ ‖K' (x, y)‖ₑ) := hK.stronglyMeasurable_mk.enorm
  refine ⟨(hk.aemeasurable.mul hu.enorm.comp_snd).lintegral_prod_right'.congr hrow'.symm, ?_⟩
  rw [lintegral_congr_ae (hrow'.mono fun x hx ↦ congrArg (· ^ r) hx)]
  refine lintegral_rpow_lintegral_mul_le hk hu.enorm hr ?_ ?_
  · filter_upwards [hA, hrow] with x hx hx'
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hx
    filter_upwards [hx'] with y hy
    simp [hy]
  · filter_upwards [hB, hcol] with y hy hy'
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hy
    filter_upwards [hy'] with x hx
    simp [hx]

/-- The `Lᵖ` bound for the dominating function `x ↦ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν`, from which both
the integrability and the norm bound of the integral operator follow. -/
private theorem eLpNorm_lintegral_enorm_mul_le
    (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν)) (hu : AEStronglyMeasurable u ν)
    (hp : 1 ≤ p) {A B : ℝ≥0∞} (hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B) :
    eLpNorm (fun x ↦ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν) p μ ≤
      A ^ (1 - p.toReal⁻¹) * B ^ p.toReal⁻¹ * eLpNorm u p ν := by
  have hr : 1 ≤ p.toReal ∨ p = ∞ := by
    rcases eq_or_ne p ∞ with rfl | hp_top
    · exact .inr rfl
    · exact .inl (by simpa using ENNReal.toReal_mono hp_top hp)
  obtain ⟨hmeas, -⟩ := lintegral_rpow_lintegral_enorm_mul_le hK hu le_rfl hA hB
  rcases eq_or_ne p ∞ with rfl | hp_top
  · simp only [eLpNorm_exponent_top hmeas.aestronglyMeasurable, eLpNorm_exponent_top hu,
      ENNReal.toReal_top, inv_zero, sub_zero, ENNReal.rpow_one, ENNReal.rpow_zero, mul_one]
    refine eLpNormEssSup_le_of_ae_enorm_bound ?_
    simpa only [enorm_eq_self] using ae_lintegral_enorm_mul_le_mul_eLpNormEssSup (u := u) hK hA
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hr : 1 ≤ p.toReal := hr.resolve_right hp_top
  have hr0 : 0 < p.toReal := zero_lt_one.trans_le hr
  obtain ⟨-, hS⟩ := lintegral_rpow_lintegral_enorm_mul_le hK hu hr hA hB
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hmeas.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hu]
  simp only [enorm_eq_self]
  calc (∫⁻ x, (∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν) ^ p.toReal ∂μ) ^ (1 / p.toReal)
      ≤ (A ^ (p.toReal - 1) * B * ∫⁻ y, ‖u y‖ₑ ^ p.toReal ∂ν) ^ (1 / p.toReal) := by
        gcongr
    _ = A ^ (1 - p.toReal⁻¹) * B ^ p.toReal⁻¹ *
          (∫⁻ y, ‖u y‖ₑ ^ p.toReal ∂ν) ^ (1 / p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, one_div,
          show (p.toReal - 1) * p.toReal⁻¹ = 1 - p.toReal⁻¹ by field_simp]

/-- The constant `A ^ (1 - 1/p) * B ^ (1/p)` of Schur's test is finite for finite `A` and `B`. -/
private theorem schur_const_lt_top (hp : 1 ≤ p) (A B : ℝ≥0) :
    (A : ℝ≥0∞) ^ (1 - p.toReal⁻¹) * (B : ℝ≥0∞) ^ p.toReal⁻¹ < ∞ :=
  ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (one_sub_toReal_inv_nonneg hp)
    ENNReal.coe_ne_top) (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top)

/-- For `u ∈ Lᵖ(ν)` the dominating function `x ↦ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν` is finite almost
everywhere. -/
private theorem ae_lintegral_enorm_mul_lt_top
    (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν)) (hu : MemLp u p ν) (hp : 1 ≤ p)
    {A B : ℝ≥0} (hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B) :
    ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν < ∞ := by
  obtain ⟨hmeas, -⟩ := lintegral_rpow_lintegral_enorm_mul_le hK hu.aestronglyMeasurable le_rfl
    hA hB
  have hfin : eLpNorm (fun x ↦ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν) p μ < ∞ :=
    (eLpNorm_lintegral_enorm_mul_le hK hu.aestronglyMeasurable hp hA hB).trans_lt
      (ENNReal.mul_lt_top (schur_const_lt_top hp A B) hu.eLpNorm_lt_top)
  rcases eq_or_ne p ∞ with rfl | hp_top
  · filter_upwards [ae_le_eLpNormEssSup (f := fun x ↦ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν) (μ := μ)]
      with x hx
    rw [enorm_eq_self] at hx
    exact hx.trans_lt (eLpNormEssSup_le_eLpNorm_top.trans_lt hfin)
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hr0 : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hlt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp_top hfin
  simp only [enorm_eq_self] at hlt
  filter_upwards [ae_lt_top' (hmeas.pow_const _) hlt.ne] with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos hr0).1 hx

/-- For `u ∈ Lᵖ(ν)`, `1 ≤ p ≤ ∞`, and a kernel whose operator-norm row and column integrals are
bounded, the integrand `y ↦ K x y (u y)` is integrable for almost every `x`. -/
theorem ae_integrable_apply_of_memLp (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν))
    (hu : MemLp u p ν) (hp : 1 ≤ p) {A B : ℝ≥0} (hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ K x y (u y)) ν := by
  filter_upwards [ae_lintegral_enorm_mul_lt_top hK hu hp hA hB,
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hK
      hu.aestronglyMeasurable.comp_snd).prodMk_left] with x hx hx'
  exact ⟨hx', (lintegral_mono fun y ↦ (K x y).le_opENorm (u y)).trans_lt hx⟩

variable [NormedSpace ℝ G]

omit [SFinite μ] in
/-- The integral operator with kernel `K` is a.e. strongly measurable on a.e. strongly
measurable inputs. -/
theorem aestronglyMeasurable_integral_apply (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν))
    (hu : AEStronglyMeasurable u ν) :
    AEStronglyMeasurable (fun x ↦ ∫ y, K x y (u y) ∂ν) μ :=
  (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hK
    hu.comp_snd).integral_prod_right'

/-- **Schur's test** for an operator-valued kernel: if the operator-norm row integrals of `K` are
a.e. at most `A` and its column integrals are a.e. at most `B`, then for `1 ≤ p ≤ ∞`,
`‖x ↦ ∫ y, K x y (u y) ∂ν‖_p ≤ A ^ (1 - 1/p) * B ^ (1/p) * ‖u‖_p`. -/
theorem eLpNorm_integral_apply_le (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν))
    (hu : AEStronglyMeasurable u ν) (hp : 1 ≤ p) {A B : ℝ≥0∞}
    (hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A) (hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B) :
    eLpNorm (fun x ↦ ∫ y, K x y (u y) ∂ν) p μ ≤
      A ^ (1 - p.toReal⁻¹) * B ^ p.toReal⁻¹ * eLpNorm u p ν :=
  (eLpNorm_mono_enorm (aestronglyMeasurable_integral_apply hK hu) fun x ↦
      (enorm_integral_le_lintegral_enorm _).trans <|
        (lintegral_mono fun y ↦ (K x y).le_opENorm (u y)).trans_eq (enorm_eq_self _).symm).trans
    (eLpNorm_lintegral_enorm_mul_le hK hu hp hA hB)

/-- The integral operator with kernel `K` maps `Lᵖ(ν)` to `Lᵖ(μ)` when the operator-norm row
and column integrals of `K` are bounded. -/
theorem memLp_integral_apply (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν))
    (hu : MemLp u p ν) (hp : 1 ≤ p) {A B : ℝ≥0} (hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B) :
    MemLp (fun x ↦ ∫ y, K x y (u y) ∂ν) p μ :=
  (eLpNorm_integral_apply_le hK hu.aestronglyMeasurable hp hA hB).trans_lt
    (ENNReal.mul_lt_top (schur_const_lt_top hp A B) hu.eLpNorm_lt_top)

variable [SMulCommClass ℝ 𝕜 G]

/-- The integral operator `u ↦ (x ↦ ∫ y, K x y (u y) ∂ν)` with an a.e. strongly measurable kernel
`K : α → β → (F →L[𝕜] G)`, as a bounded operator from `Lᵖ(ν; F)` to `Lᵖ(μ; G)` for
`1 ≤ p ≤ ∞`, when the operator-norm row integrals of `K` are a.e. at most `A` and its column
integrals are a.e. at most `B`. Its norm is at most `A ^ (1 - 1/p) * B ^ (1/p)`
(`TauCeti.norm_integralOperatorLp_le`). -/
def integralOperatorLp (K : α → β → F →L[𝕜] G) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν)) {A B : ℝ≥0}
    (hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A) (hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B) :
    Lp F p ν →L[𝕜] Lp G p μ :=
  LinearMap.mkContinuous
    { toFun u := (memLp_integral_apply hK (Lp.memLp u) Fact.out hA hB).toLp
      map_add' u v := by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [ae_integrable_apply_of_memLp hK (Lp.memLp u) Fact.out hA hB,
          ae_integrable_apply_of_memLp hK (Lp.memLp v) Fact.out hA hB] with x hu hv
        rw [Pi.add_apply, ← integral_add hu hv]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add u v] with y hy
        rw [hy, Pi.add_apply, map_add]
      map_smul' c u := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (.of_forall fun x ↦ ?_)
        rw [Pi.smul_apply, ← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c u] with y hy
        rw [hy, Pi.smul_apply, map_smul] }
    (A ^ (1 - p.toReal⁻¹) * B ^ p.toReal⁻¹ : ℝ≥0) fun u ↦ by
      have hle := eLpNorm_integral_apply_le hK (Lp.memLp u).aestronglyMeasurable
        (Fact.out : 1 ≤ p) hA hB
      rw [← ENNReal.coe_rpow_of_nonneg _ (one_sub_toReal_inv_nonneg (Fact.out : 1 ≤ p)),
        ← ENNReal.coe_rpow_of_nonneg _ (by positivity), ← ENNReal.coe_mul] at hle
      rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, Lp.norm_def, ← ENNReal.coe_toReal,
        ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_ne_top u)) hle

section integralOperatorLp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hK : AEStronglyMeasurable (uncurry K) (μ.prod ν)}
  {A B : ℝ≥0} {hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A} {hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B}

/-- The integral operator acts by `x ↦ ∫ y, K x y (u y) ∂ν` almost everywhere. -/
theorem coeFn_integralOperatorLp (u : Lp F p ν) :
    integralOperatorLp K p hK hA hB u =ᵐ[μ] fun x ↦ ∫ y, K x y (u y) ∂ν :=
  MemLp.coeFn_toLp (memLp_integral_apply hK (Lp.memLp u) Fact.out hA hB)

/-- An `Lᵖ` class equal almost everywhere to `x ↦ ∫ y, K x y (u y) ∂ν` is the image of `u` under
the integral operator. -/
theorem integralOperatorLp_eq_iff {u : Lp F p ν} {v : Lp G p μ} :
    integralOperatorLp K p hK hA hB u = v ↔ (fun x ↦ ∫ y, K x y (u y) ∂ν) =ᵐ[μ] v :=
  ⟨fun h ↦ h ▸ (coeFn_integralOperatorLp u).symm,
    fun h ↦ Lp.ext ((coeFn_integralOperatorLp u).trans h)⟩

/-- **Schur's test** on `Lᵖ`: the integral operator has norm at most `A ^ (1 - 1/p) * B ^ (1/p)`,
where `A` bounds the row integrals and `B` the column integrals of `‖K‖`. For `p = ∞` the bound
is `A`. -/
theorem norm_integralOperatorLp_le :
    ‖integralOperatorLp K p hK hA hB‖ ≤ ((A ^ (1 - p.toReal⁻¹) * B ^ p.toReal⁻¹ : ℝ≥0) : ℝ) :=
  LinearMap.mkContinuous_norm_le _ (NNReal.coe_nonneg _) _

/-- The integral operator has norm at most the larger of the bounds on the row and column
integrals of `‖K‖`. In particular, a common bound `A` on both gives norm at most `A`. -/
theorem norm_integralOperatorLp_le_max : ‖integralOperatorLp K p hK hA hB‖ ≤ max A B := by
  refine norm_integralOperatorLp_le.trans ?_
  have h₀ := one_sub_toReal_inv_nonneg (Fact.out : 1 ≤ p)
  have h₁ : 0 ≤ p.toReal⁻¹ := by positivity
  rw [NNReal.coe_le_coe]
  calc A ^ (1 - p.toReal⁻¹) * B ^ p.toReal⁻¹
      ≤ max A B ^ (1 - p.toReal⁻¹) * max A B ^ p.toReal⁻¹ := by
        gcongr
        exacts [le_max_left A B, le_max_right A B]
    _ = max A B := by
        rw [← NNReal.rpow_add' (by simp), sub_add_cancel, NNReal.rpow_one]

end integralOperatorLp

end TauCeti
