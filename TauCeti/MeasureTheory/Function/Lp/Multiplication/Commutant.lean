/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Multiplication
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Operators that preserve supports are multiplication operators

Let `μ` be a sigma-finite measure, let `1 ≤ p < ∞`, and let `S` be a bounded operator on the scalar
space `Lᵖ(μ)`. This file proves that `S` is multiplication by an essentially bounded function
`a ∈ L∞(μ)` (`MeasureTheory.Lp.multiplicationOperator`) exactly when it does not enlarge supports:
for every measurable set `s` of finite measure, `S 1_s` vanishes almost everywhere off `s`
(`MeasureTheory.Lp.exists_eq_multiplicationOperator_iff`). Equivalently, `S` commutes with every
multiplication operator (`MeasureTheory.Lp.forall_commute_multiplicationOperator_iff`):
the commutant of `L∞(μ)` acting on `Lᵖ(μ)` is `L∞(μ)` itself. The operator norm of
multiplication by `a` is `‖a‖` (`MeasureTheory.Lp.norm_multiplicationOperator`), so the multiplier
has `L∞` norm `‖S‖`.

On a topological space whose measure is inner regular for compact sets, compact sets suffice
(`MeasureTheory.Lp.exists_eq_multiplicationOperator_of_isCompact`): if `S f` vanishes almost
everywhere off every compact set off which `f` vanishes, then `S` is a multiplication operator.
This is the form that applies to singular integral operators, which are only known through their
action away from the support of their argument.

The scalar field matters. On `Lᵖ(μ; E)` with `E` of dimension at least two, applying a fixed
linear map of `E` at every point does not enlarge supports, and it is not multiplication by a
scalar function unless that map is a multiple of the identity.

## The argument

Cutting `1_t` into `1_s + 1_{t \ s}` for `s ⊆ t` shows that `S 1_s` is `S 1_t` cut off to `s`. So
the images `gₙ = S 1_{Sₙ}` of the indicators of the spanning sets `Sₙ` of `μ` agree on their
overlaps, and glue to a function `a` with `S 1_s = a 1_s` for every `s` of finite measure. Testing
`S` on the indicator of `{x ∈ s | r < ‖a x‖}` for `r > ‖S‖` shows that this set is null, so `a` is
essentially bounded. Then `S` and multiplication by `a` agree on the indicators, which span a dense
subspace of `Lᵖ(μ)` for `p < ∞`.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Section IX.6 (the multiplication
  algebra `L∞(μ)` on `L²(μ)` is maximal abelian).
-/

public section

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace MeasureTheory.Lp

variable {α 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α} [NontriviallyNormedField 𝕜]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {S : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ}

/-- If `S` does not enlarge the supports of indicators, then for `s ⊆ t` the image of `1_s` is the
image of `1_t` cut off to `s`. -/
private theorem apply_indicatorConstLp_ae_eq_indicator
    (hS : ∀ (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      ∀ᵐ x ∂μ, x ∉ s → S (indicatorConstLp p hs hμs (1 : 𝕜)) x = 0)
    {s t : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (ht : MeasurableSet t) (hμt : μ t ≠ ∞)
    (hst : s ⊆ t) :
    S (indicatorConstLp p hs hμs 1) =ᵐ[μ] s.indicator (S (indicatorConstLp p ht hμt 1)) := by
  have hd : MeasurableSet (t \ s) := ht.diff hs
  have hμd : μ (t \ s) ≠ ∞ := measure_ne_top_of_subset sdiff_subset hμt
  have hsum : indicatorConstLp p ht hμt (1 : 𝕜) =
      indicatorConstLp p hs hμs 1 + indicatorConstLp p hd hμd 1 := by
    refine Lp.ext ?_
    filter_upwards [indicatorConstLp_coeFn (p := p) (hs := ht) (hμs := hμt) (c := (1 : 𝕜)),
      indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := (1 : 𝕜)),
      indicatorConstLp_coeFn (p := p) (hs := hd) (hμs := hμd) (c := (1 : 𝕜)),
      Lp.coeFn_add (indicatorConstLp p hs hμs (1 : 𝕜)) (indicatorConstLp p hd hμd 1)]
      with x h₁ h₂ h₃ hadd
    rw [hadd, Pi.add_apply, h₁, h₂, h₃]
    by_cases hxs : x ∈ s
    · simp [hxs, hst hxs]
    · by_cases hxt : x ∈ t <;> simp [hxs, hxt]
  filter_upwards [hS s hs hμs, hS _ hd hμd,
    Lp.coeFn_add (S (indicatorConstLp p hs hμs 1)) (S (indicatorConstLp p hd hμd 1))]
    with x h₁ h₂ hadd
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs, hsum, map_add, hadd, Pi.add_apply, h₂ fun h ↦ h.2 hxs, add_zero]
  · rw [indicator_of_notMem hxs, h₁ hxs]

/-- If `S` does not enlarge the supports of indicators, then on a set `s` of finite measure the
image of `1_s` is bounded by any `r > ‖S‖`. -/
private theorem ae_norm_apply_indicatorConstLp_le
    (hS : ∀ (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      ∀ᵐ x ∂μ, x ∉ s → S (indicatorConstLp p hs hμs (1 : 𝕜)) x = 0)
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) {r : ℝ} (hr : ‖S‖ < r) :
    ∀ᵐ x ∂μ, x ∈ s → ‖S (indicatorConstLp p hs hμs (1 : 𝕜)) x‖ ≤ r := by
  set g := S (indicatorConstLp p hs hμs (1 : 𝕜))
  have hg := Lp.aestronglyMeasurable g
  set B := s ∩ {x | r < ‖hg.mk g x‖}
  have hB : MeasurableSet B :=
    hs.inter (measurableSet_lt measurable_const hg.stronglyMeasurable_mk.norm.measurable)
  have hμB : μ B ≠ ∞ := measure_ne_top_of_subset inter_subset_left hμs
  have hr₀ : 0 < r := (norm_nonneg S).trans_lt hr
  -- `S 1_B` is `g` on `B`, where `‖g‖ > r`, so `r ‖1_B‖ ≤ ‖S 1_B‖ ≤ ‖S‖ ‖1_B‖`
  have hle : ‖indicatorConstLp p hB hμB (1 : 𝕜)‖ ≤
      r⁻¹ * ‖S (indicatorConstLp p hB hμB (1 : 𝕜))‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [apply_indicatorConstLp_ae_eq_indicator hS hB hμB hs hμs inter_subset_left,
      indicatorConstLp_coeFn (p := p) (hs := hB) (hμs := hμB) (c := (1 : 𝕜)), hg.ae_eq_mk]
      with x h₁ h₂ h₃
    rw [h₁, h₂]
    by_cases hxB : x ∈ B
    · rw [indicator_of_mem hxB, indicator_of_mem hxB, norm_one, h₃]
      exact (le_inv_mul_iff₀ hr₀).2 (by simpa using hxB.2.le)
    · simp [indicator_of_notMem hxB]
  have hzero : ‖indicatorConstLp p hB hμB (1 : 𝕜)‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    by_contra! hpos
    have h₁ := hle.trans (mul_le_mul_of_nonneg_left (S.le_opNorm _) (inv_nonneg.2 hr₀.le))
    have h₂ : r⁻¹ * (‖S‖ * ‖indicatorConstLp p hB hμB (1 : 𝕜)‖) <
        ‖indicatorConstLp p hB hμB (1 : 𝕜)‖ := by
      calc r⁻¹ * (‖S‖ * ‖indicatorConstLp p hB hμB (1 : 𝕜)‖)
          < r⁻¹ * (r * ‖indicatorConstLp p hB hμB (1 : 𝕜)‖) :=
            mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hr hpos) (inv_pos.2 hr₀)
        _ = ‖indicatorConstLp p hB hμB (1 : 𝕜)‖ := by field_simp
    exact h₂.not_ge h₁
  have hμB₀ : μ B = 0 := by simpa using norm_eq_zero.1 hzero
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμB₀, hg.ae_eq_mk] with x hxB hx hxs
  rw [hx]
  by_contra! hlt
  exact hxB ⟨hxs, hlt⟩

/-- If `S` does not enlarge the supports of indicators, then the images of the indicators of the
spanning sets of `μ` glue to an essentially bounded function `a₀` with `S 1_s = a₀ 1_s` for every
set `s` of finite measure. -/
private theorem exists_memLp_top_forall_ae_eq_indicator [SigmaFinite μ]
    (hS : ∀ (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      ∀ᵐ x ∂μ, x ∉ s → S (indicatorConstLp p hs hμs (1 : 𝕜)) x = 0) :
    ∃ a₀ : α → 𝕜, MemLp a₀ ∞ μ ∧ ∀ (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      S (indicatorConstLp p hs hμs (1 : 𝕜)) =ᵐ[μ] s.indicator a₀ := by
  -- glue the images `gₙ` of the indicators of the spanning sets along the disjointed pieces
  set g : ℕ → Lp 𝕜 p μ := fun n ↦
    S (indicatorConstLp p (measurableSet_spanningSets μ n) (measure_spanningSets_lt_top μ n).ne 1)
  set a₀ : α → 𝕜 := fun x ↦ g (spanningSetsIndex μ x) x
  have ha₀ : ∀ n, ∀ x ∈ disjointed (spanningSets μ) n, a₀ x = g n x := fun n x hx ↦ by
    simp only [a₀, (spanningSetsIndex_eq_iff μ).2 hx]
  have hmeas : AEStronglyMeasurable a₀ μ := by
    rw [← Measure.restrict_univ (μ := μ), ← iUnion_spanningSets μ, ← iUnion_disjointed,
      aestronglyMeasurable_iUnion_iff]
    exact fun n ↦ (Lp.aestronglyMeasurable (g n)).restrict.congr
      (ae_restrict_of_forall_mem (MeasurableSet.disjointed (measurableSet_spanningSets μ) n)
        fun x hx ↦ (ha₀ n x hx).symm)
  have hbound : ∀ᵐ x ∂μ, ‖a₀ x‖ ≤ ‖S‖ + 1 := by
    have h : ∀ n, ∀ᵐ x ∂μ, x ∈ disjointed (spanningSets μ) n → ‖a₀ x‖ ≤ ‖S‖ + 1 := fun n ↦ by
      filter_upwards [ae_norm_apply_indicatorConstLp_le hS (measurableSet_spanningSets μ n)
        (measure_spanningSets_lt_top μ n).ne (lt_add_one ‖S‖)] with x hx hxn
      rw [ha₀ n x hxn]
      exact hx (disjointed_subset _ _ hxn)
    filter_upwards [ae_all_iff.2 h] with x hx using hx _ (mem_disjointed_spanningSetsIndex μ x)
  refine ⟨a₀, memLp_top_of_bound hmeas _ hbound, fun s hs hμs ↦ ?_⟩
  -- on `s ∩ Sₙ`, both `S 1_s` and `gₙ` are `S 1_{s ∩ Sₙ}`
  have h : ∀ n, ∀ᵐ x ∂μ, x ∈ disjointed (spanningSets μ) n → x ∈ s →
      S (indicatorConstLp p hs hμs (1 : 𝕜)) x = a₀ x := by
    intro n
    have hsn := hs.inter (measurableSet_spanningSets μ n)
    have hμsn : μ (s ∩ spanningSets μ n) ≠ ∞ := measure_ne_top_of_subset inter_subset_left hμs
    filter_upwards [apply_indicatorConstLp_ae_eq_indicator hS hsn hμsn hs hμs inter_subset_left,
      apply_indicatorConstLp_ae_eq_indicator hS hsn hμsn (measurableSet_spanningSets μ n)
        (measure_spanningSets_lt_top μ n).ne inter_subset_right] with x h₁ h₂ hxn hxs
    have hx : x ∈ s ∩ spanningSets μ n := ⟨hxs, disjointed_subset _ _ hxn⟩
    rw [ha₀ n x hxn, ← indicator_of_mem hx (S (indicatorConstLp p hs hμs (1 : 𝕜))), ← h₁, h₂,
      indicator_of_mem hx]
  filter_upwards [ae_all_iff.2 h, hS s hs hμs] with x hx hx'
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs]
    exact hx _ (mem_disjointed_spanningSetsIndex μ x) hxs
  · rw [indicator_of_notMem hxs, hx' hxs]

/-- **Operators that preserve supports are multiplication operators.** On a sigma-finite measure
space and for `p < ∞`, a bounded operator `S` on the scalar space `Lᵖ(μ)` which maps the indicator
of every measurable set `s` of finite measure to a function vanishing almost everywhere off `s` is
multiplication by some `a ∈ L∞(μ)`. -/
theorem exists_eq_multiplicationOperator_of_forall_ae_eq_zero [SigmaFinite μ] (hp : p ≠ ∞)
    (hS : ∀ (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      ∀ᵐ x ∂μ, x ∉ s → S (indicatorConstLp p hs hμs (1 : 𝕜)) x = 0) :
    ∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a := by
  obtain ⟨a₀, ha₀, hind⟩ := exists_memLp_top_forall_ae_eq_indicator hS
  refine ⟨ha₀.toLp a₀, ContinuousLinearMap.ext fun f ↦ ?_⟩
  -- `S` and multiplication by `a₀` agree on indicators, which span a dense subspace
  induction f using Lp.induction hp with
  | @indicatorConst c s hs hμs =>
    have hc : (Lp.simpleFunc.indicatorConst p hs hμs.ne c : Lp 𝕜 p μ) =
        c • indicatorConstLp p hs hμs.ne (1 : 𝕜) := by
      rw [Lp.simpleFunc.coe_indicatorConst]
      refine Lp.ext ?_
      filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs.ne) (c := c),
        Lp.coeFn_smul c (indicatorConstLp p hs hμs.ne (1 : 𝕜)),
        indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs.ne) (c := (1 : 𝕜))]
        with x h₁ h₂ h₃
      rw [h₁, h₂, Pi.smul_apply, h₃]
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hc, map_smul, map_smul]
    congr 1
    refine Lp.ext ?_
    filter_upwards [hind s hs hμs.ne,
      multiplicationOperator_ae (ha₀.toLp a₀) (indicatorConstLp p hs hμs.ne (1 : 𝕜)),
      indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs.ne) (c := (1 : 𝕜)),
      MemLp.coeFn_toLp ha₀] with x h₁ h₂ h₃ h₄
    rw [h₁, h₂, h₃, h₄]
    by_cases hx : x ∈ s <;> simp [hx]
  | add _ _ _ hf hg => rw [map_add, map_add, hf, hg]
  | isClosed => exact isClosed_eq S.continuous (multiplicationOperator _).continuous

/-- **Multiplication operators are the operators that preserve supports.** On a sigma-finite
measure space and for `p < ∞`, a bounded operator `S` on the scalar space `Lᵖ(μ)` is
multiplication by some `a ∈ L∞(μ)` if and only if it maps the indicator of every measurable set
`s` of finite measure to a function vanishing almost everywhere off `s`. -/
theorem exists_eq_multiplicationOperator_iff [SigmaFinite μ] (hp : p ≠ ∞) :
    (∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a) ↔
      ∀ (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
        ∀ᵐ x ∂μ, x ∉ s → S (indicatorConstLp p hs hμs (1 : 𝕜)) x = 0 := by
  refine ⟨?_, exists_eq_multiplicationOperator_of_forall_ae_eq_zero hp⟩
  rintro ⟨a, rfl⟩ s hs hμs
  filter_upwards [multiplicationOperator_ae a (indicatorConstLp p hs hμs (1 : 𝕜)),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := (1 : 𝕜))] with x h₁ h₂ hx
  rw [h₁, h₂, indicator_of_notMem hx, smul_zero]

/-- **The commutant of `L∞`.** On a sigma-finite measure space and for `p < ∞`, a bounded operator
on the scalar space `Lᵖ(μ)` commutes with every multiplication operator if and only if it is
itself a multiplication operator: the multiplication operators form a maximal commutative family
of operators on `Lᵖ(μ)`. -/
theorem forall_commute_multiplicationOperator_iff [SigmaFinite μ] (hp : p ≠ ∞) :
    (∀ b : Lp 𝕜 ∞ μ, Commute S (multiplicationOperator b)) ↔
      ∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a := by
  refine ⟨fun h ↦ ?_, fun ⟨a, ha⟩ b ↦ ha ▸ commute_multiplicationOperator a b⟩
  refine (exists_eq_multiplicationOperator_iff hp).2 fun s hs hμs ↦ ?_
  -- `1_s` is fixed by multiplication by `1_s`, which commutes with `S`
  let b : Lp 𝕜 ∞ μ := indicatorConstLp ∞ hs hμs (1 : 𝕜)
  have hfix : multiplicationOperator b (indicatorConstLp p hs hμs (1 : 𝕜)) =
      indicatorConstLp p hs hμs (1 : 𝕜) := by
    refine Lp.ext ?_
    filter_upwards [multiplicationOperator_ae b (indicatorConstLp p hs hμs (1 : 𝕜)),
      indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := (1 : 𝕜)),
      indicatorConstLp_coeFn (p := ∞) (hs := hs) (hμs := hμs) (c := (1 : 𝕜))] with x h₁ h₂ h₃
    rw [h₁, h₂, h₃]
    by_cases hx : x ∈ s <;> simp [hx]
  have hcomm : S (indicatorConstLp p hs hμs (1 : 𝕜)) =
      multiplicationOperator b (S (indicatorConstLp p hs hμs (1 : 𝕜))) := by
    conv_lhs => rw [← hfix]
    exact congrArg (· (indicatorConstLp p hs hμs (1 : 𝕜))) (h b).eq
  filter_upwards [multiplicationOperator_ae b (S (indicatorConstLp p hs hμs (1 : 𝕜))),
    indicatorConstLp_coeFn (p := ∞) (hs := hs) (hμs := hμs) (c := (1 : 𝕜))] with x h₁ h₂ hx
  rw [hcomm, h₁, h₂, indicator_of_notMem hx, zero_smul]

/-- **Operators that preserve compact supports are multiplication operators.** Let `μ` be a
sigma-finite measure on a topological space, inner regular for compact sets on sets of finite
measure, and let `p < ∞`. A bounded operator `S` on the scalar space `Lᵖ(μ)` such that `S f`
vanishes almost everywhere off every compact set off which `f` vanishes almost everywhere is
multiplication by some `a ∈ L∞(μ)`. -/
theorem exists_eq_multiplicationOperator_of_isCompact [TopologicalSpace α] [R1Space α]
    [BorelSpace α] [SigmaFinite μ] [μ.InnerRegularCompactLTTop] (hp : p ≠ ∞)
    (hS : ∀ (f : Lp 𝕜 p μ) (K : Set α), IsCompact K → (∀ᵐ x ∂μ, x ∉ K → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ K → S f x = 0) :
    ∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a := by
  refine exists_eq_multiplicationOperator_of_forall_ae_eq_zero hp fun s hs hμs ↦ ?_
  -- the classes vanishing off `s` form a closed set
  set Z : Set (Lp 𝕜 p μ) := {g | ∀ᵐ x ∂μ, x ∉ s → g x = 0}
  have hZ : IsClosed Z := by
    have : Z = LpToLpRestrictCLM α 𝕜 𝕜 μ p sᶜ ⁻¹' {0} := by
      ext g
      simp only [Z, mem_ofPred_eq, mem_preimage, mem_singleton_iff, Lp.eq_zero_iff_ae_eq_zero]
      constructor
      · intro h
        filter_upwards [LpToLpRestrictCLM_coeFn 𝕜 sᶜ g, (ae_restrict_iff' hs.compl).2 h]
          with x h₁ h₂
        rw [h₁, h₂, Pi.zero_apply]
      · intro h
        refine (ae_restrict_iff' hs.compl).1 ?_
        filter_upwards [LpToLpRestrictCLM_coeFn 𝕜 sᶜ g, h] with x h₁ h₂
        rw [← h₁, h₂, Pi.zero_apply]
    rw [this]
    exact isClosed_singleton.preimage (ContinuousLinearMap.continuous _)
  -- approximate `1_s` by the indicators of compact subsets `Kₙ`, whose images vanish off `s`
  have hε : ∀ n : ℕ, (n : ℝ≥0∞)⁻¹ ≠ 0 := fun n ↦ ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n)
  choose K hKs hKc hKcl hμK using fun n : ℕ ↦ hs.exists_isCompact_isClosed_lt_add hμs (hε n)
  have hKm : ∀ n, MeasurableSet (K n) := fun n ↦ (hKcl n).measurableSet
  have hμKn : ∀ n, μ (K n) ≠ ∞ := fun n ↦ measure_ne_top_of_subset (hKs n) hμs
  have hlim : Tendsto (fun n ↦ indicatorConstLp p (hKm n) (hμKn n) (1 : 𝕜)) atTop
      (𝓝 (indicatorConstLp p hs hμs 1)) := by
    refine tendsto_indicatorConstLp_set hp ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ zero_le) fun n ↦ ?_
    rw [symmDiff_of_le (hKs n)]
    exact (measure_sdiff_lt_of_lt_add (hKm n).nullMeasurableSet (hKs n) (hμKn n) (hμK n)).le
  refine hZ.mem_of_tendsto ((S.continuous.tendsto _).comp hlim) (Eventually.of_forall fun n ↦ ?_)
  have hvan : ∀ᵐ x ∂μ, x ∉ K n → indicatorConstLp p (hKm n) (hμKn n) (1 : 𝕜) x = 0 := by
    filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hKm n) (hμs := hμKn n) (c := (1 : 𝕜))]
      with x hx hxK
    rw [hx, indicator_of_notMem hxK]
  filter_upwards [hS _ (K n) (hKc n) hvan] with x hx hxs using hx fun h ↦ hxs (hKs n h)

end MeasureTheory.Lp
