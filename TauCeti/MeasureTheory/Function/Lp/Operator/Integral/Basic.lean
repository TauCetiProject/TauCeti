/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
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

This is the vector-valued form of Schur's test: it follows from the scalar `Lᵖ` estimate
`TauCeti.eLpNorm_lintegral_mul_le` applied to the norm kernel `‖K x y‖ₑ` and the input `‖u y‖ₑ`,
together with `‖∫ y, K x y (u y) ∂ν‖ₑ ≤ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν`; for `p = ∞` only the row
bound is used. Typical applications are Littlewood–Paley block estimates, where the
kernels of the localized operators between dyadic blocks have uniform `L¹` bounds in each
variable, and matrix-valued kernels acting on sections of a trivial finite-rank bundle.

## Main declarations

* `TauCeti.ae_integrable_apply_of_memLp`: for `u ∈ Lᵖ` the integrand `y ↦ K x y (u y)` is
  integrable for almost every `x`.
* `TauCeti.eLpNorm_integral_apply_le`: the `Lᵖ` bound for the integral operator on functions.
* `TauCeti.integralOperatorLp`: the integral operator as a bounded operator on `Lᵖ`.
* `TauCeti.norm_integralOperatorLp_le`, `TauCeti.norm_integralOperatorLp_le_max`: its norm
  bounds.
* `TauCeti.integralOperatorLp_sub`: the integral operator of `K₁ - K₂` is the difference of the
  integral operators of `K₁` and `K₂`.
* `TauCeti.lintegral_enorm_row_le_of_le_indicator`,
  `TauCeti.lintegral_enorm_column_le_of_le_indicator`: the row and column bounds `c * ν t` and
  `c * μ s` for a kernel bounded by `c` on `s ×ˢ t` and zero outside it.

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

/-- The `Lᵖ` bound for the dominating function `x ↦ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν`, from which both
the integrability and the norm bound of the integral operator follow: Schur's test
`TauCeti.eLpNorm_lintegral_mul_le` for the norm kernel `‖K x y‖ₑ`. -/
private theorem eLpNorm_lintegral_enorm_mul_le
    (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν)) (hu : AEStronglyMeasurable u ν)
    (hp : 1 ≤ p) {A B : ℝ≥0∞} (hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B) :
    eLpNorm (fun x ↦ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν) p μ ≤
      A ^ (1 - p.toReal⁻¹) * B ^ p.toReal⁻¹ * eLpNorm u p ν :=
  (eLpNorm_lintegral_mul_le (k := fun x y ↦ ‖K x y‖ₑ) hK.enorm hu.enorm hp hA hB).trans_eq
    (by rw [eLpNorm_enorm _ hu])

/-- For `u ∈ Lᵖ(ν)` the dominating function `x ↦ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν` is finite almost
everywhere. -/
private theorem ae_lintegral_enorm_mul_lt_top
    (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν)) (hu : MemLp u p ν) (hp : 1 ≤ p)
    {A B : ℝ≥0} (hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B) :
    ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν < ∞ := by
  have hfin : MemLp (fun x ↦ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν) p μ :=
    memLp_lintegral_mul (k := fun x y ↦ ‖K x y‖ₑ) hK.enorm hu.enorm hp hA hB
  simpa only [enorm_eq_self] using hfin.ae_enorm_lt_top (zero_lt_one.trans_le hp).ne'

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

omit [MeasurableSpace α] [SFinite ν] in
/-- A kernel bounded by `c` on `s ×ˢ t` and zero outside it has row integrals at most `c * ν t`. -/
theorem lintegral_enorm_row_le_of_le_indicator {s : Set α} {t : Set β} (ht : MeasurableSet t)
    {c : ℝ≥0∞} (hK : ∀ x y, ‖K x y‖ₑ ≤ s.indicator (fun _ ↦ t.indicator (fun _ ↦ c) y) x)
    (x : α) : ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ c * ν t := by
  calc ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ ∫⁻ y, t.indicator (fun _ ↦ c) y ∂ν := by
        refine lintegral_mono fun y ↦ (hK x y).trans ?_
        by_cases hx : x ∈ s <;> simp [hx]
    _ = c * ν t := lintegral_indicator_const ht c

omit [MeasurableSpace β] [SFinite μ] in
/-- A kernel bounded by `c` on `s ×ˢ t` and zero outside it has column integrals at most
`c * μ s`. -/
theorem lintegral_enorm_column_le_of_le_indicator {s : Set α} {t : Set β} (hs : MeasurableSet s)
    {c : ℝ≥0∞} (hK : ∀ x y, ‖K x y‖ₑ ≤ s.indicator (fun _ ↦ t.indicator (fun _ ↦ c) y) x)
    (y : β) : ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ c * μ s := by
  calc ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ ∫⁻ x, s.indicator (fun _ ↦ c) x ∂μ := by
        refine lintegral_mono fun x ↦ (hK x y).trans ?_
        by_cases hx : x ∈ s <;> by_cases hy : y ∈ t <;> simp [hx, hy]
    _ = c * μ s := lintegral_indicator_const hs c

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
    (ENNReal.mul_lt_top (rpow_one_sub_toReal_inv_mul_rpow_toReal_inv_lt_top hp A B)
      hu.eLpNorm_lt_top)

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
      refine (Lp.norm_toLp _ (memLp_integral_apply hK (Lp.memLp u) Fact.out hA hB)).trans_le
        (ENNReal.toReal_le_of_le_ofReal (by positivity) ?_)
      rw [ENNReal.ofReal_mul NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal,
        ofReal_norm, Lp.enorm_def, coe_rpow_one_sub_toReal_inv_mul_rpow_toReal_inv Fact.out]
      exact eLpNorm_integral_apply_le hK (Lp.memLp u).aestronglyMeasurable Fact.out hA hB

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

/-- The integral operator of the difference of two kernels is the difference of their integral
operators. -/
theorem integralOperatorLp_sub {K₁ K₂ : α → β → F →L[𝕜] G}
    {hK₁ : AEStronglyMeasurable (uncurry K₁) (μ.prod ν)} {A₁ B₁ : ℝ≥0}
    {hA₁ : ∀ᵐ x ∂μ, ∫⁻ y, ‖K₁ x y‖ₑ ∂ν ≤ A₁} {hB₁ : ∀ᵐ y ∂ν, ∫⁻ x, ‖K₁ x y‖ₑ ∂μ ≤ B₁}
    {hK₂ : AEStronglyMeasurable (uncurry K₂) (μ.prod ν)} {A₂ B₂ : ℝ≥0}
    {hA₂ : ∀ᵐ x ∂μ, ∫⁻ y, ‖K₂ x y‖ₑ ∂ν ≤ A₂} {hB₂ : ∀ᵐ y ∂ν, ∫⁻ x, ‖K₂ x y‖ₑ ∂μ ≤ B₂}
    {hK : AEStronglyMeasurable (uncurry fun x y ↦ K₁ x y - K₂ x y) (μ.prod ν)} {A B : ℝ≥0}
    {hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K₁ x y - K₂ x y‖ₑ ∂ν ≤ A}
    {hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K₁ x y - K₂ x y‖ₑ ∂μ ≤ B} :
    integralOperatorLp K₁ p hK₁ hA₁ hB₁ - integralOperatorLp K₂ p hK₂ hA₂ hB₂ =
      integralOperatorLp (fun x y ↦ K₁ x y - K₂ x y) p hK hA hB := by
  refine ContinuousLinearMap.ext fun u ↦ (integralOperatorLp_eq_iff.2 ?_).symm
  filter_upwards [ae_integrable_apply_of_memLp hK₁ (Lp.memLp u) Fact.out hA₁ hB₁,
    ae_integrable_apply_of_memLp hK₂ (Lp.memLp u) Fact.out hA₂ hB₂,
    coeFn_integralOperatorLp (hK := hK₁) (hA := hA₁) (hB := hB₁) u,
    coeFn_integralOperatorLp (hK := hK₂) (hA := hA₂) (hB := hB₂) u,
    Lp.coeFn_sub (integralOperatorLp K₁ p hK₁ hA₁ hB₁ u)
      (integralOperatorLp K₂ p hK₂ hA₂ hB₂ u)] with x h₁ h₂ e₁ e₂ e
  rw [sub_apply, e, Pi.sub_apply, e₁, e₂, ← integral_sub h₁ h₂]
  simp only [sub_apply]

end integralOperatorLp

end TauCeti
