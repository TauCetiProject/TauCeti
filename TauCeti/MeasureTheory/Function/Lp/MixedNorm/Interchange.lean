/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.Lp.Indicator
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral

/-!
# Minkowski's inequality for mixed norms and the interchange of Bochner spaces

For a function `F` of two variables and exponents `p ≤ q < ∞`, **Minkowski's inequality for mixed
norms** says that taking the `Lᵖ` norm in the first variable before the `L^q` norm in the second
gives at most the norm taken in the opposite order:

`‖t ↦ ‖F (·, t)‖_{Lᵖ(μ)}‖_{L^q(ν)} ≤ ‖s ↦ ‖F (s, ·)‖_{L^q(ν)}‖_{Lᵖ(μ)}`.

For s-finite measures this is `TauCeti.eLpNorm_eLpNorm_swap_le`, a consequence of Minkowski's
integral inequality `TauCeti.lintegral_Lp_lintegral_le` applied to `‖F‖ ^ p` with exponent `q / p`.
For arbitrary measures it holds for strongly measurable functions supported in a product of two
sets on which the measures are s-finite (`TauCeti.eLpNorm_eLpNorm_swap_le_of_support_subset`).

Applied to finite sums of rectangle tensors, this inequality gives, for `1 ≤ p ≤ q < ∞`, arbitrary
measure spaces `(S, μ)`, `(T, ν)` and a Banach space `X`, the continuous linear contraction

`TauCeti.minkowskiContraction 𝕜 X μ ν p q : Lᵖ(μ; L^q(ν; X)) →L[𝕜] L^q(ν; Lᵖ(μ; X))`

interchanging the two variables: for measurable sets `A ⊆ S` and `B ⊆ T` of finite measure and
`x : X` it sends the rectangle tensor `𝟙_A (𝟙_B x)` to `𝟙_B (𝟙_A x)`
(`TauCeti.minkowskiContraction_indicatorConstLp`). The rectangle tensors span a dense subspace
(`TauCeti.dense_span_indicatorConstLp_indicatorConstLp`), so two continuous linear maps agreeing
on them are equal (`TauCeti.continuousLinearMap_ext_indicatorConstLp_indicatorConstLp`); in
particular the contraction is the unique continuous linear map with this rectangle formula, and it
commutes with bounded linear maps of `X` (`TauCeti.minkowskiContraction_comp_compLpL`). For `p = q`
the two interchanges are mutually inverse, which gives the linear isometric equivalence
`TauCeti.lpLpComm 𝕜 X μ ν p : Lᵖ(μ; Lᵖ(ν; X)) ≃ₗᵢ[𝕜] Lᵖ(ν; Lᵖ(μ; X))`.

No σ-finiteness is assumed: a finite sum of rectangle tensors is supported in a product of two
sets of finite measure, where the mixed-norm inequality applies.

## Main declarations

* `TauCeti.eLpNorm_eLpNorm_swap_le`: Minkowski's inequality for mixed norms.
* `TauCeti.minkowskiContraction`: the interchange `Lᵖ(μ; L^q(ν; X)) → L^q(ν; Lᵖ(μ; X))`.
* `TauCeti.minkowskiContraction_indicatorConstLp`: its value on rectangle tensors.
* `TauCeti.norm_minkowskiContraction_le`: it is a contraction.
* `TauCeti.lpLpComm`: the isometric interchange for equal exponents.

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces*, Vol. I,
  Springer, 2016, Proposition 1.2.22 and Corollary 1.2.23.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace TauCeti

section MixedNorm

variable {α β ε : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  {ν : Measure β} [TopologicalSpace ε] {p q : ℝ≥0∞}

/-- Minkowski's inequality for mixed norms of a strongly measurable function. -/
private theorem eLpNorm_eLpNorm_swap_le_of_stronglyMeasurable [ContinuousENorm ε] [SFinite μ]
    [SFinite ν] {F : α × β → ε} (hF : StronglyMeasurable F) (hpq : p ≤ q) (hq : q ≠ ∞) :
    eLpNorm (fun y ↦ eLpNorm (fun x ↦ F (x, y)) p μ) q ν ≤
      eLpNorm (fun x ↦ eLpNorm (fun y ↦ F (x, y)) q ν) p μ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · have h0 (y : β) : eLpNorm (fun x ↦ F (x, y)) 0 μ = 0 :=
      eLpNorm_exponent_zero (hF.comp_measurable measurable_prodMk_right).aestronglyMeasurable
    simp [h0]
  have hq0 : q ≠ 0 := ne_bot_of_le_ne_bot hp0 hpq
  have hp : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hlm : AEStronglyMeasurable (fun y ↦ eLpNorm (fun x ↦ F (x, y)) p μ) ν :=
    hF.prod_swap.aestronglyMeasurable.eLpNorm_prod_right (μ := ν) (ν := μ)
  have hrm : AEStronglyMeasurable (fun x ↦ eLpNorm (fun y ↦ F (x, y)) q ν) μ :=
    hF.aestronglyMeasurable.eLpNorm_prod_right (μ := μ) (ν := ν)
  have hl (y : β) : eLpNorm (fun x ↦ F (x, y)) p μ =
      (∫⁻ x, ‖F (x, y)‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) :=
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp
      (hF.comp_measurable measurable_prodMk_right).aestronglyMeasurable
  have hr (x : α) : eLpNorm (fun y ↦ F (x, y)) q ν =
      (∫⁻ y, ‖F (x, y)‖ₑ ^ q.toReal ∂ν) ^ (1 / q.toReal) :=
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq
      (hF.comp_measurable measurable_prodMk_left).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq hlm,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hrm]
  simp only [hl, hr, eNorm_eq_self]
  set a := p.toReal
  set b := q.toReal
  have ha : 0 < a := ENNReal.toReal_pos hp0 hp
  have hab : a ≤ b := ENNReal.toReal_mono hq hpq
  have hb : 0 < b := ha.trans_le hab
  -- Minkowski's integral inequality for `‖F‖ ^ a` with exponent `b / a ≥ 1`.
  have key := lintegral_Lp_lintegral_le (μ := ν) (ν := μ) (f := fun y x ↦ ‖F (x, y)‖ₑ ^ a)
    (hF.prod_swap.aestronglyMeasurable.eNorm.pow_const a) ((one_le_div ha).2 hab)
  have e₁ (z : ℝ≥0∞) : (z ^ a) ^ (b / a) = z ^ b := by
    rw [← ENNReal.rpow_mul, mul_div_cancel₀ _ ha.ne']
  have e₂ (z : ℝ≥0∞) : (z ^ (1 / a)) ^ b = z ^ (b / a) := by
    rw [← ENNReal.rpow_mul, one_div_mul_eq_div]
  have e₃ (z : ℝ≥0∞) : (z ^ (1 / b)) ^ a = z ^ (1 / (b / a)) := by
    rw [← ENNReal.rpow_mul, one_div_div, one_div_mul_eq_div]
  have e₄ (z : ℝ≥0∞) : z ^ (1 / b) = (z ^ (1 / (b / a))) ^ (1 / a) := by
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
  simp only [e₁] at key
  simp only [e₂, e₃]
  rw [e₄]
  exact ENNReal.rpow_le_rpow key (by positivity)

/-- **Minkowski's inequality for mixed norms.** For `p ≤ q < ∞` and an almost everywhere
strongly measurable function `F` on a product of s-finite measure spaces, the `L^q(ν)` norm of the
`Lᵖ(μ)` norms of the sections `F (·, y)` is at most the `Lᵖ(μ)` norm of the `L^q(ν)` norms of the
sections `F (x, ·)`. -/
theorem eLpNorm_eLpNorm_swap_le [ContinuousENorm ε] [SFinite μ] [SFinite ν] {F : α × β → ε}
    (hF : AEStronglyMeasurable F (μ.prod ν)) (hpq : p ≤ q) (hq : q ≠ ∞) :
    eLpNorm (fun y ↦ eLpNorm (fun x ↦ F (x, y)) p μ) q ν ≤
      eLpNorm (fun x ↦ eLpNorm (fun y ↦ F (x, y)) q ν) p μ := by
  set G := hF.mk F
  have hG : StronglyMeasurable G := hF.stronglyMeasurable_mk
  -- Almost every section of `F` agrees almost everywhere with the corresponding section of `G`.
  have hx : ∀ᵐ x ∂μ, (fun y ↦ F (x, y)) =ᵐ[ν] fun y ↦ G (x, y) :=
    Measure.ae_ae_of_ae_prod hF.ae_eq_mk
  have hy : ∀ᵐ y ∂ν, (fun x ↦ F (x, y)) =ᵐ[μ] fun x ↦ G (x, y) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae_eq_comp
        hF.ae_eq_mk)
  calc eLpNorm (fun y ↦ eLpNorm (fun x ↦ F (x, y)) p μ) q ν
      = eLpNorm (fun y ↦ eLpNorm (fun x ↦ G (x, y)) p μ) q ν :=
        eLpNorm_congr_ae (hy.mono fun y hy ↦ eLpNorm_congr_ae hy)
    _ ≤ eLpNorm (fun x ↦ eLpNorm (fun y ↦ G (x, y)) q ν) p μ :=
        eLpNorm_eLpNorm_swap_le_of_stronglyMeasurable hG hpq hq
    _ = eLpNorm (fun x ↦ eLpNorm (fun y ↦ F (x, y)) q ν) p μ :=
        eLpNorm_congr_ae (hx.mono fun x hx ↦ (eLpNorm_congr_ae hx).symm)

/-- **Minkowski's inequality for mixed norms**, for arbitrary measures: it holds for a strongly
measurable function supported in a product `A ×ˢ B` of sets on which `μ` and `ν` restrict to
s-finite measures, for instance sets of finite measure. -/
theorem eLpNorm_eLpNorm_swap_le_of_support_subset [ENormedAddMonoid ε] {F : α × β → ε}
    (hF : StronglyMeasurable F)
    {A : Set α} {B : Set β} [SFinite (μ.restrict A)] [SFinite (ν.restrict B)]
    (hFAB : Function.support F ⊆ A ×ˢ B) (hpq : p ≤ q) (hq : q ≠ ∞) :
    eLpNorm (fun y ↦ eLpNorm (fun x ↦ F (x, y)) p μ) q ν ≤
      eLpNorm (fun x ↦ eLpNorm (fun y ↦ F (x, y)) q ν) p μ := by
  have hzero (x : α) (y : β) (h : x ∉ A ∨ y ∉ B) : F (x, y) = 0 := by
    by_contra hne
    have := hFAB hne
    simp only [mem_prod] at this
    tauto
  -- Each section only sees the set carrying the support.
  have hsx (y : β) : eLpNorm (fun x ↦ F (x, y)) p μ = eLpNorm (fun x ↦ F (x, y)) p (μ.restrict A) :=
    (eLpNorm_restrict_eq_of_support_subset
      (hF.comp_measurable measurable_prodMk_right).aestronglyMeasurable
      fun x hx ↦ by_contra fun h ↦ hx (hzero x y (Or.inl h))).symm
  have hsy (x : α) : eLpNorm (fun y ↦ F (x, y)) q ν = eLpNorm (fun y ↦ F (x, y)) q (ν.restrict B) :=
    (eLpNorm_restrict_eq_of_support_subset
      (hF.comp_measurable measurable_prodMk_left).aestronglyMeasurable
      fun y hy ↦ by_contra fun h ↦ hy (hzero x y (Or.inr h))).symm
  simp only [hsx, hsy]
  -- The outer functions are supported in `B` and in `A`.
  have hlm : AEStronglyMeasurable (fun y ↦ eLpNorm (fun x ↦ F (x, y)) p (μ.restrict A)) ν :=
    hF.prod_swap.aestronglyMeasurable.eLpNorm_prod_right (μ := ν) (ν := μ.restrict A)
  have hrm : AEStronglyMeasurable (fun x ↦ eLpNorm (fun y ↦ F (x, y)) q (ν.restrict B)) μ :=
    hF.aestronglyMeasurable.eLpNorm_prod_right (μ := μ) (ν := ν.restrict B)
  rw [← eLpNorm_restrict_eq_of_support_subset (s := B) hlm
      fun y hy ↦ by_contra fun h ↦ hy (by simp [hzero _ y (Or.inr h)]),
    ← eLpNorm_restrict_eq_of_support_subset (s := A) hrm
      fun x hx ↦ by_contra fun h ↦ hx (by simp [hzero x _ (Or.inl h)])]
  exact eLpNorm_eLpNorm_swap_le_of_stronglyMeasurable hF hpq hq

end MixedNorm

section Interchange

variable {S T 𝕜 X : Type*} [MeasurableSpace S] [MeasurableSpace T] {μ : Measure S}
  {ν : Measure T} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

omit [Fact (1 ≤ p)] in
/-- A finite linear combination of rectangle tensors `𝟙_{A i} (𝟙_{B i} (x i))` is represented,
in almost every first variable, by the corresponding linear combination of functions on the
product. -/
private theorem ae_ae_linearCombination_indicatorConstLp {ι : Type*} {A : ι → Set S}
    {B : ι → Set T} (x : ι → X) (hA : ∀ i, MeasurableSet (A i)) (hμA : ∀ i, μ (A i) ≠ ∞)
    (hB : ∀ i, MeasurableSet (B i)) (hνB : ∀ i, ν (B i) ≠ ∞) (c : ι →₀ 𝕜) :
    ∀ᵐ s ∂μ, ⇑(Finsupp.linearCombination 𝕜
        (fun i ↦ indicatorConstLp p (hA i) (hμA i) (indicatorConstLp q (hB i) (hνB i) (x i))) c
          s) =ᵐ[ν] fun t ↦
        Finsupp.linearCombination 𝕜 (fun i ↦ (A i ×ˢ B i).indicator fun _ ↦ x i) c (s, t) := by
  set v : ι → Lp (Lp X q ν) p μ :=
    fun i ↦ indicatorConstLp p (hA i) (hμA i) (indicatorConstLp q (hB i) (hνB i) (x i))
  induction c using Finsupp.induction_linear with
  | zero =>
    filter_upwards [Lp.coeFn_zero (Lp X q ν) p μ] with s hs
    simp only [map_zero, hs, Pi.zero_apply]
    filter_upwards [Lp.coeFn_zero X q ν] with t ht
    rw [ht, Pi.zero_apply]
  | add f g hf hg =>
    simp only [map_add]
    filter_upwards [Lp.coeFn_add (Finsupp.linearCombination 𝕜 v f)
      (Finsupp.linearCombination 𝕜 v g), hf, hg] with s hs h₁ h₂
    rw [hs, Pi.add_apply]
    filter_upwards [Lp.coeFn_add (Finsupp.linearCombination 𝕜 v f s)
      (Finsupp.linearCombination 𝕜 v g s), h₁, h₂] with t ht ht₁ ht₂
    rw [ht, Pi.add_apply, ht₁, ht₂, Pi.add_apply]
  | single i a =>
    simp only [Finsupp.linearCombination_single, v]
    filter_upwards [Lp.coeFn_smul a (v i), indicatorConstLp_coeFn (p := p) (hs := hA i)
      (hμs := hμA i) (c := indicatorConstLp q (hB i) (hνB i) (x i))] with s h₁ h₂
    rw [h₁, Pi.smul_apply, h₂]
    by_cases hs : s ∈ A i
    · rw [indicator_of_mem hs]
      filter_upwards [Lp.coeFn_smul a (indicatorConstLp q (hB i) (hνB i) (x i)),
        indicatorConstLp_coeFn (p := q) (hs := hB i) (hμs := hνB i) (c := x i)] with t h₃ h₄
      rw [h₃, Pi.smul_apply, h₄]
      by_cases ht : t ∈ B i <;> simp [hs, ht]
    · rw [indicator_of_notMem hs, smul_zero]
      filter_upwards [Lp.coeFn_zero X q ν] with t ht
      rw [ht, Pi.zero_apply]
      simp [hs]

/-- The norm of a finite linear combination of rectangle tensors is the mixed norm of the
corresponding function on the product. -/
private theorem eNorm_linearCombination_indicatorConstLp {ι : Type*} {A : ι → Set S}
    {B : ι → Set T} (x : ι → X) (hA : ∀ i, MeasurableSet (A i)) (hμA : ∀ i, μ (A i) ≠ ∞)
    (hB : ∀ i, MeasurableSet (B i)) (hνB : ∀ i, ν (B i) ≠ ∞) (c : ι →₀ 𝕜) :
    ‖Finsupp.linearCombination 𝕜
        (fun i ↦ indicatorConstLp p (hA i) (hμA i) (indicatorConstLp q (hB i) (hνB i) (x i))) c‖ₑ =
      eLpNorm (fun s ↦ eLpNorm (fun t ↦ Finsupp.linearCombination 𝕜
        (fun i ↦ (A i ×ˢ B i).indicator fun _ ↦ x i) c (s, t)) q ν) p μ := by
  set Φ : Lp (Lp X q ν) p μ := Finsupp.linearCombination 𝕜
    (fun i ↦ indicatorConstLp p (hA i) (hμA i) (indicatorConstLp q (hB i) (hνB i) (x i))) c
  have h : (fun s ↦ ‖Φ s‖ₑ) =ᵐ[μ] fun s ↦ eLpNorm (fun t ↦ Finsupp.linearCombination 𝕜
      (fun i ↦ (A i ×ˢ B i).indicator fun _ ↦ x i) c (s, t)) q ν := by
    filter_upwards [ae_ae_linearCombination_indicatorConstLp (p := p) (q := q) x hA hμA hB hνB c]
      with s hs
    rw [Lp.eNorm_def]
    exact eLpNorm_congr_ae hs
  rw [Lp.eNorm_def, ← eLpNorm_eNorm _ (Lp.aestronglyMeasurable Φ), eLpNorm_congr_ae h]

/-- A finite linear combination of functions `𝟙_{A i ×ˢ B i} (x i)` is strongly measurable and is
supported in a product of two sets of finite measure. -/
private theorem exists_support_linearCombination_indicator_subset {ι : Type*} {A : ι → Set S}
    {B : ι → Set T} (x : ι → X) (hA : ∀ i, MeasurableSet (A i)) (hμA : ∀ i, μ (A i) ≠ ∞)
    (hB : ∀ i, MeasurableSet (B i)) (hνB : ∀ i, ν (B i) ≠ ∞) (c : ι →₀ 𝕜) :
    StronglyMeasurable (Finsupp.linearCombination 𝕜 (fun i ↦ (A i ×ˢ B i).indicator fun _ ↦ x i) c)
      ∧ ∃ A' B', μ A' ≠ ∞ ∧ ν B' ≠ ∞ ∧ Function.support
        (Finsupp.linearCombination 𝕜 (fun i ↦ (A i ×ˢ B i).indicator fun _ ↦ x i) c) ⊆
          A' ×ˢ B' := by
  have hsum : Finsupp.linearCombination 𝕜 (fun i ↦ (A i ×ˢ B i).indicator fun _ ↦ x i) c =
      ∑ i ∈ c.support, c i • (A i ×ˢ B i).indicator fun _ ↦ x i :=
    Finsupp.linearCombination_apply 𝕜 c
  rw [hsum]
  refine ⟨Finset.stronglyMeasurable_sum _ fun i _ ↦
      (stronglyMeasurable_const.indicator ((hA i).prod (hB i))).const_smul _,
    ⋃ i ∈ c.support, A i, ⋃ i ∈ c.support, B i,
    (measure_biUnion_lt_top c.support.finite_toSet fun i _ ↦ (hμA i).lt_top).ne,
    (measure_biUnion_lt_top c.support.finite_toSet fun i _ ↦ (hνB i).lt_top).ne, ?_⟩
  intro z hz
  rw [Function.mem_support, Finset.sum_apply] at hz
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hmem : z ∈ A i ×ˢ B i := by
    by_contra h
    simp [indicator_of_notMem h] at hne
  exact ⟨mem_biUnion hi hmem.1, mem_biUnion hi hmem.2⟩

/-- The norm inequality behind the interchange: interchanging the variables of a finite linear
combination of rectangle tensors does not increase its norm. -/
private theorem norm_linearCombination_indicatorConstLp_swap_le {ι : Type*} {A : ι → Set S}
    {B : ι → Set T} (x : ι → X) (hA : ∀ i, MeasurableSet (A i)) (hμA : ∀ i, μ (A i) ≠ ∞)
    (hB : ∀ i, MeasurableSet (B i)) (hνB : ∀ i, ν (B i) ≠ ∞) (hpq : p ≤ q) (hq : q ≠ ∞)
    (c : ι →₀ 𝕜) :
    ‖Finsupp.linearCombination 𝕜
        (fun i ↦ indicatorConstLp q (hB i) (hνB i) (indicatorConstLp p (hA i) (hμA i) (x i))) c‖ ≤
      ‖Finsupp.linearCombination 𝕜
        (fun i ↦ indicatorConstLp p (hA i) (hμA i) (indicatorConstLp q (hB i) (hνB i) (x i)))
          c‖ := by
  set F := Finsupp.linearCombination 𝕜 (fun i ↦ (A i ×ˢ B i).indicator fun _ ↦ x i) c
  have hswap (t : T) (s : S) : Finsupp.linearCombination 𝕜
      (fun i ↦ (B i ×ˢ A i).indicator fun _ ↦ x i) c (t, s) = F (s, t) := by
    simp only [F, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hs : s ∈ A i <;> by_cases ht : t ∈ B i <;> simp [hs, ht]
  obtain ⟨hF, A', B', hA', hB', hsupp⟩ :=
    exists_support_linearCombination_indicator_subset x hA hμA hB hνB c
  have : IsFiniteMeasure (μ.restrict A') := isFiniteMeasure_restrict.2 hA'
  have : IsFiniteMeasure (ν.restrict B') := isFiniteMeasure_restrict.2 hB'
  have key : ‖Finsupp.linearCombination 𝕜
        (fun i ↦ indicatorConstLp q (hB i) (hνB i) (indicatorConstLp p (hA i) (hμA i) (x i))) c‖ₑ ≤
      ‖Finsupp.linearCombination 𝕜
        (fun i ↦ indicatorConstLp p (hA i) (hμA i) (indicatorConstLp q (hB i) (hνB i) (x i))) c‖ₑ
      := by
    rw [eNorm_linearCombination_indicatorConstLp (p := q) (q := p) x hB hνB hA hμA c,
      eNorm_linearCombination_indicatorConstLp (p := p) (q := q) x hA hμA hB hνB c]
    simp only [hswap]
    exact eLpNorm_eLpNorm_swap_le_of_support_subset hF hsupp hpq hq
  rw [← toReal_eNorm, ← toReal_eNorm]
  exact ENNReal.toReal_mono eNorm_ne_top key

/-- The data of a rectangle tensor: two measurable sets of finite measure and a vector. -/
private structure Rectangle (μ : Measure S) (ν : Measure T) (X : Type*) where
  /-- The set in the first variable. -/
  A : Set S
  /-- The set in the second variable. -/
  B : Set T
  /-- The vector. -/
  x : X
  hA : MeasurableSet A
  hμA : μ A ≠ ∞
  hB : MeasurableSet B
  hνB : ν B ≠ ∞

/-- The rectangle tensor `𝟙_A (𝟙_B x)` in `Lᵖ(μ; L^q(ν; X))`. -/
private def rectangleLeft (p q : ℝ≥0∞) [Fact (1 ≤ q)] (r : Rectangle μ ν X) :
    Lp (Lp X q ν) p μ :=
  indicatorConstLp p r.hA r.hμA (indicatorConstLp q r.hB r.hνB r.x)

/-- The interchanged rectangle tensor `𝟙_B (𝟙_A x)` in `L^q(ν; Lᵖ(μ; X))`. -/
private def rectangleRight (p q : ℝ≥0∞) [Fact (1 ≤ p)] (r : Rectangle μ ν X) :
    Lp (Lp X p μ) q ν :=
  indicatorConstLp q r.hB r.hνB (indicatorConstLp p r.hA r.hμA r.x)

/-- For finite exponents the rectangle tensors `𝟙_A (𝟙_B x)`, for measurable sets `A ⊆ S` and
`B ⊆ T` of finite measure and `x : X`, span a dense subspace of `Lᵖ(μ; L^q(ν; X))`. -/
theorem dense_span_indicatorConstLp_indicatorConstLp (hp : p ≠ ∞) (hq : q ≠ ∞) :
    Dense (Submodule.span 𝕜 {Φ : Lp (Lp X q ν) p μ | ∃ (A : Set S) (B : Set T)
      (hA : MeasurableSet A) (hB : MeasurableSet B) (hμA : μ A ≠ ∞) (hνB : ν B ≠ ∞) (x : X),
        indicatorConstLp p hA hμA (indicatorConstLp q hB hνB x) = Φ} :
      Set (Lp (Lp X q ν) p μ)) := by
  set K := (Submodule.span 𝕜 {Φ : Lp (Lp X q ν) p μ | ∃ (A : Set S) (B : Set T)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hμA : μ A ≠ ∞) (hνB : ν B ≠ ∞) (x : X),
      indicatorConstLp p hA hμA (indicatorConstLp q hB hνB x) = Φ}).topologicalClosure
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.eq_top_iff']
  have hK : IsClosed (K : Set (Lp (Lp X q ν) p μ)) := Submodule.isClosed_topologicalClosure _
  refine Lp.induction hp (motive := (· ∈ K)) ?_ (fun _ _ _ _ _ h₁ h₂ ↦ K.add_mem h₁ h₂) hK
  intro c A hA hμA
  rw [Lp.simpleFunc.coe_indicatorConst]
  -- For a fixed outer set `A`, the constants `c` with `𝟙_A c ∈ K` form a closed subspace
  -- containing the indicator classes `𝟙_B x`.
  refine Lp.induction hq (motive := fun c ↦ indicatorConstLp p hA hμA.ne c ∈ K) ?_ ?_ ?_ c
  · intro x B hB hνB
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨A, B, hA, hB, hμA.ne, hνB.ne, x, rfl⟩)
  · intro f g _ _ _ h₁ h₂
    rw [← indicatorConstLp_add]
    exact K.add_mem h₁ h₂
  · simpa only [preimage, indicatorConstLpL_apply, SetLike.mem_coe] using
      hK.preimage (indicatorConstLpL 𝕜 p hA hμA.ne : Lp X q ν →L[𝕜] _).continuous

/-- Two continuous linear maps out of `Lᵖ(μ; L^q(ν; X))`, `p, q < ∞`, that agree on all rectangle
tensors `𝟙_A (𝟙_B x)` are equal. -/
theorem continuousLinearMap_ext_indicatorConstLp_indicatorConstLp {F : Type*}
    [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜 F] [T2Space F] (hp : p ≠ ∞) (hq : q ≠ ∞)
    {f g : Lp (Lp X q ν) p μ →L[𝕜] F}
    (h : ∀ (A : Set S) (B : Set T) (hA : MeasurableSet A) (hB : MeasurableSet B)
      (hμA : μ A ≠ ∞) (hνB : ν B ≠ ∞) (x : X),
      f (indicatorConstLp p hA hμA (indicatorConstLp q hB hνB x)) =
        g (indicatorConstLp p hA hμA (indicatorConstLp q hB hνB x))) :
    f = g :=
  ContinuousLinearMap.ext_on (dense_span_indicatorConstLp_indicatorConstLp hp hq) <| by
    rintro _ ⟨A, B, hA, hB, hμA, hνB, x, rfl⟩
    exact h A B hA hB hμA hνB x

private theorem denseRange_linearCombination_rectangleLeft (hp : p ≠ ∞) (hq : q ≠ ∞) :
    DenseRange (Finsupp.linearCombination 𝕜 (rectangleLeft (μ := μ) (ν := ν) (X := X) p q)) := by
  rw [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination]
  refine (dense_span_indicatorConstLp_indicatorConstLp hp hq).mono
    (SetLike.coe_subset_coe.2 (Submodule.span_mono ?_))
  rintro _ ⟨A, B, hA, hB, hμA, hνB, x, rfl⟩
  exact ⟨⟨A, B, x, hA, hμA, hB, hνB⟩, rfl⟩

private theorem norm_linearCombination_rectangleRight_le (hpq : p ≤ q) (hq : q ≠ ∞)
    (c : Rectangle μ ν X →₀ 𝕜) :
    ‖Finsupp.linearCombination 𝕜 (rectangleRight p q) c‖ ≤
      1 * ‖Finsupp.linearCombination 𝕜 (rectangleLeft p q) c‖ := by
  rw [one_mul]
  exact norm_linearCombination_indicatorConstLp_swap_le Rectangle.x Rectangle.hA Rectangle.hμA
    Rectangle.hB Rectangle.hνB hpq hq c

variable [CompleteSpace X]

variable (𝕜 X μ ν p q) in
/-- **Minkowski's contraction.** For `1 ≤ p ≤ q < ∞` and arbitrary measure spaces, the continuous
linear map `Lᵖ(μ; L^q(ν; X)) → L^q(ν; Lᵖ(μ; X))` interchanging the two variables: it sends each
rectangle tensor `𝟙_A (𝟙_B x)` to `𝟙_B (𝟙_A x)` (`TauCeti.minkowskiContraction_indicatorConstLp`)
and has norm at most one (`TauCeti.norm_minkowskiContraction_le`). For other exponents its value
is unspecified. -/
def minkowskiContraction : Lp (Lp X q ν) p μ →L[𝕜] Lp (Lp X p μ) q ν :=
  (Finsupp.linearCombination 𝕜 (rectangleRight (μ := μ) (ν := ν) (X := X) p q)).extendOfNorm
    (Finsupp.linearCombination 𝕜 (rectangleLeft p q))

/-- Minkowski's contraction sends the rectangle tensor `𝟙_A (𝟙_B x)` to `𝟙_B (𝟙_A x)`. -/
@[simp]
theorem minkowskiContraction_indicatorConstLp (hpq : p ≤ q) (hq : q ≠ ∞) {A : Set S} {B : Set T}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hμA : μ A ≠ ∞) (hνB : ν B ≠ ∞) (x : X) :
    minkowskiContraction 𝕜 X μ ν p q (indicatorConstLp p hA hμA (indicatorConstLp q hB hνB x)) =
      indicatorConstLp q hB hνB (indicatorConstLp p hA hμA x) := by
  have h := LinearMap.extendOfNorm_eq
    (f := Finsupp.linearCombination 𝕜 (rectangleRight (μ := μ) (ν := ν) (X := X) p q))
    (e := Finsupp.linearCombination 𝕜 (rectangleLeft (μ := μ) (ν := ν) (X := X) p q))
    (denseRange_linearCombination_rectangleLeft (𝕜 := 𝕜) (ne_top_of_le_ne_top hq hpq) hq)
    ⟨1, norm_linearCombination_rectangleRight_le hpq hq⟩
    (Finsupp.single ⟨A, B, x, hA, hμA, hB, hνB⟩ 1)
  rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, one_smul,
    one_smul] at h
  exact h

/-- Minkowski's contraction does not increase norms. -/
theorem norm_minkowskiContraction_apply_le (hpq : p ≤ q) (hq : q ≠ ∞)
    (Φ : Lp (Lp X q ν) p μ) : ‖minkowskiContraction 𝕜 X μ ν p q Φ‖ ≤ ‖Φ‖ := by
  have h := LinearMap.norm_extendOfNorm_apply_le
    (f := Finsupp.linearCombination 𝕜 (rectangleRight (μ := μ) (ν := ν) (X := X) p q))
    (e := Finsupp.linearCombination 𝕜 (rectangleLeft (μ := μ) (ν := ν) (X := X) p q))
    (denseRange_linearCombination_rectangleLeft (𝕜 := 𝕜) (ne_top_of_le_ne_top hq hpq) hq) 1
    (norm_linearCombination_rectangleRight_le hpq hq) Φ
  rw [one_mul] at h
  exact h

/-- Minkowski's contraction has operator norm at most one. -/
theorem norm_minkowskiContraction_le (hpq : p ≤ q) (hq : q ≠ ∞) :
    ‖minkowskiContraction 𝕜 X μ ν p q‖ ≤ 1 :=
  LinearMap.opNorm_extendOfNorm_le
    (f := Finsupp.linearCombination 𝕜 (rectangleRight (μ := μ) (ν := ν) (X := X) p q))
    (e := Finsupp.linearCombination 𝕜 (rectangleLeft (μ := μ) (ν := ν) (X := X) p q))
    (denseRange_linearCombination_rectangleLeft (𝕜 := 𝕜) (ne_top_of_le_ne_top hq hpq) hq)
    zero_le_one (norm_linearCombination_rectangleRight_le hpq hq)

/-- Minkowski's contraction commutes with a bounded linear map `L : X →L[𝕜] Y` applied to the
values. -/
theorem minkowskiContraction_comp_compLpL {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [CompleteSpace Y] (hpq : p ≤ q) (hq : q ≠ ∞) (L : X →L[𝕜] Y) :
    (minkowskiContraction 𝕜 Y μ ν p q).comp ((L.compLpL q ν).compLpL p μ) =
      ((L.compLpL p μ).compLpL q ν).comp (minkowskiContraction 𝕜 X μ ν p q) := by
  refine continuousLinearMap_ext_indicatorConstLp_indicatorConstLp
    (ne_top_of_le_ne_top hq hpq) hq fun A B hA hB hμA hνB x ↦ ?_
  simp [minkowskiContraction_indicatorConstLp hpq hq]

/-- For equal finite exponents, interchanging the variables twice is the identity. -/
theorem minkowskiContraction_comp_minkowskiContraction (hp : p ≠ ∞) :
    (minkowskiContraction 𝕜 X ν μ p p).comp (minkowskiContraction 𝕜 X μ ν p p) =
      ContinuousLinearMap.id 𝕜 _ := by
  refine continuousLinearMap_ext_indicatorConstLp_indicatorConstLp hp hp
    fun A B hA hB hμA hνB x ↦ ?_
  simp [minkowskiContraction_indicatorConstLp le_rfl hp]

variable (𝕜 X μ ν p) in
/-- For a finite exponent `p ≥ 1` and arbitrary measure spaces, interchanging the variables is a
linear isometric equivalence `Lᵖ(μ; Lᵖ(ν; X)) ≃ₗᵢ[𝕜] Lᵖ(ν; Lᵖ(μ; X))`. It is Minkowski's
contraction (`TauCeti.lpLpComm_apply`), with inverse the interchange in the other order
(`TauCeti.lpLpComm_symm`). -/
def lpLpComm (hp : p ≠ ∞) : Lp (Lp X p ν) p μ ≃ₗᵢ[𝕜] Lp (Lp X p μ) p ν where
  toLinearEquiv := LinearEquiv.ofLinearMap (minkowskiContraction 𝕜 X μ ν p p).toLinearMap
    (minkowskiContraction 𝕜 X ν μ p p).toLinearMap
    (congrArg ContinuousLinearMap.toLinearMap
      (minkowskiContraction_comp_minkowskiContraction (μ := ν) (ν := μ) hp))
    (congrArg ContinuousLinearMap.toLinearMap (minkowskiContraction_comp_minkowskiContraction hp))
  norm_map' Φ := by
    refine le_antisymm (norm_minkowskiContraction_apply_le le_rfl hp Φ) ?_
    conv_lhs => rw [← ContinuousLinearMap.id_apply (R₁ := 𝕜) Φ,
      ← minkowskiContraction_comp_minkowskiContraction (μ := μ) (ν := ν) hp]
    exact norm_minkowskiContraction_apply_le le_rfl hp _

@[simp]
theorem lpLpComm_apply (hp : p ≠ ∞) (Φ : Lp (Lp X p ν) p μ) :
    lpLpComm 𝕜 X μ ν p hp Φ = minkowskiContraction 𝕜 X μ ν p p Φ :=
  (rfl)

@[simp]
theorem lpLpComm_symm (hp : p ≠ ∞) :
    (lpLpComm 𝕜 X μ ν p hp).symm = lpLpComm 𝕜 X ν μ p hp :=
  (rfl)

end Interchange

end TauCeti
