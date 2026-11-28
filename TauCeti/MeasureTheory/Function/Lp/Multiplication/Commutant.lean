/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Multiplication.Basic
public import TauCeti.MeasureTheory.Function.Lp.Operator.Local
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# Commutant and support-preserving operators on scalar `Lᵖ`

Let `μ` be a sigma-finite measure, let `1 ≤ p < ∞`, and let `S` be a bounded operator on the scalar
space `Lᵖ(μ)`. This file proves that `S` is multiplication by an essentially bounded function
`a ∈ L∞(μ)` (`MeasureTheory.Lp.multiplicationOperator`) exactly when it is local, that is, does not
enlarge supports: whenever `f` vanishes almost everywhere off a measurable set `s`, so does `S f`
(`MeasureTheory.Lp.exists_eq_multiplicationOperator_iff`). Equivalently, `S` commutes with every
multiplication operator (`MeasureTheory.Lp.forall_commute_multiplicationOperator_iff`):
the commutant of `L∞(μ)` acting on `Lᵖ(μ)` is `L∞(μ)` itself. On a topological space whose measure
is inner regular for compact sets, compact sets suffice
(`MeasureTheory.Lp.exists_eq_multiplicationOperator_of_isCompact`). Both the local and global
multiplier representations in this file are built from the scalar specialization of the
operator-valued locality theorem
`ContinuousLinearMap.exists_forall_ae_eq_apply_of_forall_ae_eq_zero` (applied via
`MeasureTheory.Lp.exists_eq_multiplicationOperator_of_forall_ae_eq_zero`, where the symbol `m x`
on `𝕜` is multiplication by `m x 1`).

On complex scalar `L²`, every bounded operator commuting with measurable-set indicator
multiplications on sets of finite measure is locally multiplication by an `L∞` symbol on each
finite-measure set (`MeasureTheory.Lp.exists_norm_le_and_comp_indicatorMultiplication_eq`),
and globally multiplication by an `L∞` symbol when the measure is `σ`-finite
(`MeasureTheory.Lp.exists_multiplicationOperator_eq_of_forall_commute_indicatorMultiplication` and
`MeasureTheory.Lp.centralizer_range_multiplicationOperator`).

Without any `σ`-finiteness assumption on `μ`, any two bounded operators on `Lp ℂ 2 μ` commuting
with all finite-measure indicator multiplications commute with each other
(`MeasureTheory.Lp.commute_of_forall_commute_indicatorMultiplication`).

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Section IX.6 (the multiplication
  algebra `L∞(μ)` on `L²(μ)` is maximal abelian).
* M. Takesaki, *Theory of Operator Algebras I*, Springer, 2002, Chapter III, §1.
* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  Academic Press, 1983, Example 5.1.6.
-/

public section

noncomputable section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory.Lp

section GeneralLp

open Set

variable {α 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α} [NontriviallyNormedField 𝕜]
  [CompleteSpace 𝕜] [TopologicalSpace.SeparableSpace 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {S : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ}

/-- **Local operators on scalar `Lᵖ` are multiplication operators.** On a sigma-finite measure
space and for `p < ∞`, a bounded operator `S` on the scalar space `Lᵖ(μ)` such that `S f` vanishes
almost everywhere off every measurable set off which `f` vanishes is multiplication by some
`a ∈ L∞(μ)`. -/
theorem exists_eq_multiplicationOperator_of_forall_ae_eq_zero [SigmaFinite μ] (hp : p ≠ ∞)
    (hS : ∀ (f : Lp 𝕜 p μ) (s : Set α), MeasurableSet s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → S f x = 0) :
    ∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a := by
  obtain ⟨m, hm, hbound, hSm⟩ := S.exists_forall_ae_eq_apply_of_forall_ae_eq_zero hp hS
  -- the operator `m x` on `𝕜` is multiplication by `m x 1`
  have ha : MemLp (fun x ↦ m x 1) ∞ μ :=
    memLp_top_of_bound ((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).continuous.comp_stronglyMeasurable
      hm).aestronglyMeasurable ‖S‖ (hbound.mono fun x hx ↦ by
        simpa using ((m x).le_opNorm 1).trans (by simpa using hx))
  refine ⟨ha.toLp _, ContinuousLinearMap.ext fun f ↦ Lp.ext ?_⟩
  filter_upwards [hSm f, multiplicationOperator_ae (ha.toLp _) f, ha.coeFn_toLp] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/-- **Multiplication operators are the local operators.** On a sigma-finite measure space and for
`p < ∞`, a bounded operator `S` on the scalar space `Lᵖ(μ)` is multiplication by some
`a ∈ L∞(μ)` if and only if `S f` vanishes almost everywhere off every measurable set off which `f`
vanishes. -/
theorem exists_eq_multiplicationOperator_iff [SigmaFinite μ] (hp : p ≠ ∞) :
    (∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a) ↔
      ∀ (f : Lp 𝕜 p μ) (s : Set α), MeasurableSet s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
        ∀ᵐ x ∂μ, x ∉ s → S f x = 0 := by
  refine ⟨?_, exists_eq_multiplicationOperator_of_forall_ae_eq_zero hp⟩
  rintro ⟨a, rfl⟩ f s - hf
  filter_upwards [multiplicationOperator_ae a f, hf] with x h₁ h₂ hx
  rw [h₁, h₂ hx, smul_zero]

/-- **The commutant of `L∞`.** On a sigma-finite measure space and for `p < ∞`, a bounded operator
on the scalar space `Lᵖ(μ)` commutes with every multiplication operator if and only if it is
itself a multiplication operator: the multiplication operators form a maximal commutative family
of operators on `Lᵖ(μ)`. -/
theorem forall_commute_multiplicationOperator_iff [SigmaFinite μ] (hp : p ≠ ∞) :
    (∀ b : Lp 𝕜 ∞ μ, Commute S (multiplicationOperator b)) ↔
      ∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a := by
  refine ⟨fun h ↦ (exists_eq_multiplicationOperator_iff hp).2 fun f s hs hf ↦ ?_,
    fun ⟨a, ha⟩ b ↦ ha ▸ commute_multiplicationOperator a b⟩
  -- `f` is fixed by multiplication by `1_s`, which commutes with `S`
  have hb : MemLp (s.indicator fun _ ↦ (1 : 𝕜)) ∞ μ :=
    (memLp_top_const 1).indicator hs.nullMeasurableSet
  have hfix : multiplicationOperator (hb.toLp _) f = f := by
    refine Lp.ext ?_
    filter_upwards [multiplicationOperator_ae (hb.toLp _) f, hb.coeFn_toLp, hf] with x h₁ h₂ h₃
    rw [h₁, h₂]
    by_cases hx : x ∈ s <;> simp [hx, h₃]
  have hcomm : S f = multiplicationOperator (hb.toLp _) (S f) := by
    conv_lhs => rw [← hfix]
    exact congrArg (· f) (h (hb.toLp _)).eq
  filter_upwards [multiplicationOperator_ae (hb.toLp _) (S f), hb.coeFn_toLp] with x h₁ h₂ hx
  rw [hcomm, h₁, h₂, indicator_of_notMem hx, zero_smul]

/-- **Operators that preserve compact supports are multiplication operators.** Let `μ` be a
sigma-finite measure on a Hausdorff space, inner regular for compact sets on sets of finite
measure, and let `p < ∞`. A bounded operator `S` on the scalar space `Lᵖ(μ)` such that `S f`
vanishes almost everywhere off every compact set off which `f` vanishes almost everywhere is
multiplication by some `a ∈ L∞(μ)`. -/
theorem exists_eq_multiplicationOperator_of_isCompact [TopologicalSpace α]
    [OpensMeasurableSpace α] [T2Space α] [SigmaFinite μ] [μ.InnerRegularCompactLTTop]
    (hp : p ≠ ∞)
    (hS : ∀ (f : Lp 𝕜 p μ) (K : Set α), IsCompact K → (∀ᵐ x ∂μ, x ∉ K → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ K → S f x = 0) :
    ∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a :=
  exists_eq_multiplicationOperator_of_forall_ae_eq_zero hp fun f _ hs hf ↦
    S.ae_apply_eq_zero_of_forall_isCompact hp hS f hs hf

end GeneralLp

open ContinuousLinearMap

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}

/-- On a sigma-finite measure space, the indicator multiplications along `spanningSets μ` converge
strongly to the identity on `Lp E 2 μ`. -/
theorem tendsto_indicatorMultiplication_spanningSets [SigmaFinite μ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Lp E 2 μ) :
    Tendsto (fun n ↦ indicatorMultiplication ℂ 2 (measurableSet_spanningSets μ n) f)
      atTop (𝓝 f) := by
  have hmem (n : ℕ) : MemLp ((spanningSets μ n).indicator ⇑f) 2 μ :=
    (Lp.memLp f).indicator (measurableSet_spanningSets μ n).nullMeasurableSet
  have heq (n : ℕ) : indicatorMultiplication ℂ 2 (measurableSet_spanningSets μ n) f =
      (hmem n).toLp _ :=
    Lp.ext <| (indicatorMultiplication_ae (measurableSet_spanningSets μ n) f).trans
      (hmem n).coeFn_toLp.symm
  simp_rw [heq]
  refine TauCeti.tendsto_toLp_of_ae_tendsto_of_norm_le ENNReal.ofNat_ne_top hmem
    EventuallyEq.rfl (fun n ↦ .of_forall fun x ↦ norm_indicator_le_norm_self _ _) ?_
  refine .of_forall fun x ↦ tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_mem_spanningSets μ x] with n hn
  exact (Set.indicator_of_mem hn _).symm

/-- Compressing an operator `T` that commutes with measurable-subset indicators on `s` yields a
local operator on `Lp ℂ 2 (μ.restrict s)`. -/
private theorem isLocal_comp_extendByZero {s : Set α} (hs : MeasurableSet s)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hcomm : ∀ ⦃t : Set α⦄ (ht : MeasurableSet t), t ⊆ s →
      Commute T (indicatorMultiplication ℂ 2 ht))
    (g : Lp ℂ 2 (μ.restrict s)) (t : Set α) (ht : MeasurableSet t)
    (hg : ∀ᵐ x ∂μ.restrict s, x ∉ t → g x = 0) :
    ∀ᵐ x ∂μ.restrict s, x ∉ t →
      ((LpToLpRestrictCLM α ℂ ℂ μ 2 s).comp
        (T.comp ((TauCeti.castLpₗᵢ (𝕜 := ℂ) (E := ℂ) (p := 2)
          Measure.restrict_univ).toLinearIsometry.comp
          (TauCeti.extendByZeroLpₗᵢ ℂ μ hs.nullMeasurableSet
            (Set.subset_univ s))).toContinuousLinearMap)) g x = 0 := by
  set ext₂ : Lp ℂ 2 (μ.restrict s) →ₗᵢ[ℂ] Lp ℂ 2 μ :=
    (TauCeti.castLpₗᵢ Measure.restrict_univ).toLinearIsometry.comp
      (TauCeti.extendByZeroLpₗᵢ ℂ μ hs.nullMeasurableSet (Set.subset_univ s))
  set r := t ∩ s
  have hr : MeasurableSet r := ht.inter hs
  have hι_fix : indicatorMultiplication ℂ 2 hr (ext₂ g) = ext₂ g := by
    refine indicatorMultiplication_eq_self_of_ae_notMem hr ?_
    filter_upwards [TauCeti.coeFn_castLpₗᵢ_extendByZeroLpₗᵢ ℂ hs.nullMeasurableSet g,
      (ae_restrict_iff' hs).mp hg] with x hιx hgx hxr
    change (ext₂ g : α → ℂ) x = _ at hιx
    rw [hιx]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs, hgx hxs fun hxt ↦ hxr ⟨hxt, hxs⟩]
    · rw [Set.indicator_of_notMem hxs]
  have hTι : T (ext₂ g) = indicatorMultiplication ℂ 2 hr (T (ext₂ g)) := by
    rw [← (hcomm hr Set.inter_subset_right).indicatorMultiplication_apply, hι_fix]
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ s (T (ext₂ g)),
    ae_restrict_of_ae ((Lp.ext_iff.mp hTι).trans
      (indicatorMultiplication_ae hr (T (ext₂ g))))] with x hxR hxT hxt
  simp only [comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [hxR, hxT, Set.indicator_of_notMem fun (h : x ∈ r) ↦ hxt h.1]

/-- Gluing on-`s` multiplication representation of the compressed operator and off-`s` vanishing of
`T ∘L P` back into `T ∘L P = multiplicationOperator (ι ∞ b) ∘L P`. -/
private theorem comp_indicatorMultiplication_eq_of_restrict {s : Set α} (hs : MeasurableSet s)
    {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hcomm_s : Commute T (indicatorMultiplication ℂ 2 hs))
    {b : Lp ℂ ∞ (μ.restrict s)}
    (hb_eq : multiplicationOperator (E := ℂ) b =
      (LpToLpRestrictCLM α ℂ ℂ μ 2 s).comp
        (T.comp ((TauCeti.castLpₗᵢ (𝕜 := ℂ) (E := ℂ) (p := 2)
          Measure.restrict_univ).toLinearIsometry.comp
          (TauCeti.extendByZeroLpₗᵢ ℂ μ hs.nullMeasurableSet
            (Set.subset_univ s))).toContinuousLinearMap)) :
    T ∘L indicatorMultiplication ℂ 2 hs =
      multiplicationOperator (TauCeti.castLpₗᵢ (𝕜 := ℂ) Measure.restrict_univ
        (TauCeti.extendByZeroLpₗᵢ ℂ μ hs.nullMeasurableSet (Set.subset_univ s) b)) ∘L
        indicatorMultiplication ℂ 2 hs := by
  refine ContinuousLinearMap.ext fun f ↦ Lp.ext ?_
  simp only [comp_apply]
  set P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := indicatorMultiplication ℂ 2 hs
  have hTP : T (P f) = P (T f) := hcomm_s.indicatorMultiplication_apply f
  have hTf_off : ∀ᵐ x ∂μ, x ∉ s → T (P f) x = 0 := by
    filter_upwards [(Lp.ext_iff.mp hTP).trans (indicatorMultiplication_ae hs (T f))]
      with x hx hxs
    rw [hx, Set.indicator_of_notMem hxs]
  have hTf_on : ⇑(T (P f)) =ᵐ[μ.restrict s] fun x ↦ b x * f x := by
    have hS_apply : multiplicationOperator (E := ℂ) b (LpToLpRestrictCLM α ℂ ℂ μ 2 s f) =
        LpToLpRestrictCLM α ℂ ℂ μ 2 s (T (P f)) := by
      have h := congrArg (fun A : Lp ℂ 2 (μ.restrict s) →L[ℂ] Lp ℂ 2 (μ.restrict s) ↦
        A (LpToLpRestrictCLM α ℂ ℂ μ 2 s f)) hb_eq
      rwa [comp_apply, comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometry.coe_comp, LinearIsometryEquiv.coe_toLinearIsometry,
        Function.comp_apply, TauCeti.castLpₗᵢ_extendByZeroLpₗᵢ_LpToLpRestrictCLM] at h
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ s (T (P f)),
      multiplicationOperator_ae b (LpToLpRestrictCLM α ℂ ℂ μ 2 s f),
      LpToLpRestrictCLM_coeFn ℂ s f] with x hx hmul hR
    rw [← hx, ← hS_apply, hmul, hR, smul_eq_mul]
  filter_upwards [hTf_off, (ae_restrict_iff' hs).mp hTf_on,
    multiplicationOperator_ae (TauCeti.castLpₗᵢ (𝕜 := ℂ) Measure.restrict_univ
      (TauCeti.extendByZeroLpₗᵢ ℂ μ hs.nullMeasurableSet (Set.subset_univ s) b)) (P f),
    indicatorMultiplication_ae (𝕜 := ℂ) hs f,
    TauCeti.coeFn_castLpₗᵢ_extendByZeroLpₗᵢ ℂ hs.nullMeasurableSet b]
    with x hxoff hxon hmul₁ hmul₂ hax
  by_cases hxs : x ∈ s
  · rw [hxon hxs, hmul₁, hmul₂, hax, Set.indicator_of_mem hxs, Set.indicator_of_mem hxs,
      smul_eq_mul]
  · rw [hxoff hxs, hmul₁, hmul₂, Set.indicator_of_notMem hxs, smul_zero]

/-- **Local multiplier representation on a finite-measure set.** On an arbitrary measure space, a
bounded operator on `Lp ℂ 2 μ` that commutes with indicator multiplications on measurable subsets
of a finite-measure measurable set `s` agrees after cutoff to `s` with multiplication by an `L∞`
symbol of norm at most `‖T‖`. -/
theorem exists_norm_le_and_comp_indicatorMultiplication_eq {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hcomm : ∀ ⦃t : Set α⦄ (ht : MeasurableSet t), t ⊆ s →
      Commute T (indicatorMultiplication ℂ 2 ht)) :
    ∃ a : Lp ℂ ∞ μ, ‖a‖ ≤ ‖T‖ ∧
      T ∘L indicatorMultiplication ℂ 2 hs =
        multiplicationOperator a ∘L indicatorMultiplication ℂ 2 hs := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs
  -- Phase 1: Compress `T` to `Lp ℂ 2 (μ.restrict s)` and verify locality.
  let ext₂ : Lp ℂ 2 (μ.restrict s) →ₗᵢ[ℂ] Lp ℂ 2 μ :=
    (TauCeti.castLpₗᵢ Measure.restrict_univ).toLinearIsometry.comp
      (TauCeti.extendByZeroLpₗᵢ ℂ μ hs.nullMeasurableSet (Set.subset_univ s))
  let S : Lp ℂ 2 (μ.restrict s) →L[ℂ] Lp ℂ 2 (μ.restrict s) :=
    (LpToLpRestrictCLM α ℂ ℂ μ 2 s).comp (T.comp ext₂.toContinuousLinearMap)
  have hS_norm : ‖S‖ ≤ ‖T‖ := opNorm_le_bound S (norm_nonneg T) fun g ↦
    calc ‖S g‖ ≤ ‖T (ext₂ g)‖ := norm_Lp_toLp_restrict_le s _
      _ ≤ ‖T‖ * ‖ext₂ g‖ := T.le_opNorm _
      _ = ‖T‖ * ‖g‖ := by rw [ext₂.norm_map]
  -- Phase 2: Represent the compressed operator as multiplication by `b : Lp ℂ ∞ (μ.restrict s)`.
  obtain ⟨b, hb_eq⟩ := exists_eq_multiplicationOperator_of_forall_ae_eq_zero ENNReal.ofNat_ne_top
    (isLocal_comp_extendByZero hs T hcomm)
  have hb_norm : ‖b‖ ≤ ‖S‖ := by
    rw [← norm_multiplicationOperator (E := ℂ) (p := 2) b, ← hb_eq]
  -- Phase 3: Extend `b` by zero to `Lp ℂ ∞ μ` and glue on and off `s`.
  refine ⟨TauCeti.castLpₗᵢ Measure.restrict_univ
      (TauCeti.extendByZeroLpₗᵢ ℂ μ hs.nullMeasurableSet (Set.subset_univ s) b), ?_,
    comp_indicatorMultiplication_eq_of_restrict hs (hcomm hs Set.Subset.rfl) hb_eq.symm⟩
  rw [LinearIsometryEquiv.norm_map, LinearIsometry.norm_map]
  exact hb_norm.trans hS_norm

/-- **Unconditional commutativity of the multiplier commutant.** On an arbitrary measure space —
with no sigma-finiteness assumption — any two bounded operators on `Lp ℂ 2 μ` that commute with
all finite-measure indicator multiplications commute with each other. -/
theorem commute_of_forall_commute_indicatorMultiplication
    {S T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    (hS : ∀ ⦃s : Set α⦄ (hs : MeasurableSet s), μ s ≠ ∞ →
      Commute S (indicatorMultiplication ℂ 2 hs))
    (hT : ∀ ⦃s : Set α⦄ (hs : MeasurableSet s), μ s ≠ ∞ →
      Commute T (indicatorMultiplication ℂ 2 hs)) :
    Commute S T := by
  refine (commute_iff_eq _ _).mpr
    (ContinuousLinearMap.ext_indicatorConstLp ENNReal.ofNat_ne_top fun s hs hμs c ↦ ?_)
  set u := indicatorConstLp 2 hs hμs c
  set P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := indicatorMultiplication ℂ 2 hs
  have hPu : P u = u := indicatorMultiplication_indicatorConstLp_self hs hμs c
  obtain ⟨a, -, ha⟩ := exists_norm_le_and_comp_indicatorMultiplication_eq hs
    hμs S fun t ht hts ↦ hS ht (measure_ne_top_of_subset hts hμs)
  obtain ⟨b, -, hb⟩ := exists_norm_le_and_comp_indicatorMultiplication_eq hs
    hμs T fun t ht hts ↦ hT ht (measure_ne_top_of_subset hts hμs)
  have happly {A B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} {x y : Lp ℂ ∞ μ}
      (hA : A ∘L P = multiplicationOperator x ∘L P)
      (hB : B ∘L P = multiplicationOperator y ∘L P) :
      (A * B) u = multiplicationOperator (x * y) u := by
    have hBu : B u = multiplicationOperator y u := by
      simpa only [comp_apply, hPu] using congrArg (fun R ↦ R u) hB
    have hPBu : P (B u) = B u := by
      have hcomm :=
        (commute_multiplicationOperator_indicatorMultiplication (E := ℂ) (p := 2) y hs)
      rw [hBu, ← hcomm.indicatorMultiplication_apply, hPu]
    calc (A * B) u = (A ∘L P) (B u) := by rw [mul_apply_eq_comp, comp_apply, hPBu]
      _ = multiplicationOperator x (B u) := by rw [hA, comp_apply, hPBu]
      _ = multiplicationOperator (x * y) u := by
        rw [hBu, ← comp_apply, multiplicationOperator_comp_multiplicationOperator]
  rw [happly ha hb, happly hb ha, mul_comm a b]

/-- Any operator in the centralizer of the range of `multiplicationOperator` commutes with every
`multiplicationOperator a`. -/
theorem commute_multiplicationOperator_of_mem_centralizer_range
    {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    (hT : T ∈ (Set.range (multiplicationOperator (E := ℂ) (μ := μ))).centralizer)
    (a : Lp ℂ ∞ μ) :
    Commute T (multiplicationOperator (E := ℂ) a) :=
  (commute_iff_eq _ _).mpr (hT _ ⟨a, rfl⟩).symm

/-- Any operator in the centralizer of the range of `multiplicationOperator` commutes with every
`indicatorMultiplication`. -/
theorem commute_indicatorMultiplication_of_mem_centralizer_range
    {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    (hT : T ∈ (Set.range (multiplicationOperator (E := ℂ) (μ := μ))).centralizer)
    {s : Set α} (hs : MeasurableSet s) :
    Commute T (indicatorMultiplication ℂ 2 hs) := by
  rw [← multiplicationOperator_linftyIndicator hs]
  exact commute_multiplicationOperator_of_mem_centralizer_range hT _

/-- On an arbitrary measure space, any two operators in the centralizer of the range of
`multiplicationOperator` commute with each other. -/
theorem commute_of_mem_centralizer_range_multiplicationOperator {S T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    (hS : S ∈ (Set.range (multiplicationOperator (E := ℂ) (μ := μ))).centralizer)
    (hT : T ∈ (Set.range (multiplicationOperator (E := ℂ) (μ := μ))).centralizer) :
    Commute S T :=
  commute_of_forall_commute_indicatorMultiplication
    (fun _ hs _ ↦ commute_indicatorMultiplication_of_mem_centralizer_range hS hs)
    (fun _ hs _ ↦ commute_indicatorMultiplication_of_mem_centralizer_range hT hs)

/-- **Multiplier commutant theorem on sigma-finite `L²`.** Every bounded operator on `Lp ℂ 2 μ`
that commutes with all finite-measure indicator multiplications is multiplication by an essentially
bounded symbol. -/
theorem exists_multiplicationOperator_eq_of_forall_commute_indicatorMultiplication [SigmaFinite μ]
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hcomm : ∀ ⦃s : Set α⦄ (hs : MeasurableSet s), μ s ≠ ∞ →
      Commute T (indicatorMultiplication ℂ 2 hs)) :
    ∃ a : Lp ℂ ∞ μ, multiplicationOperator (E := ℂ) a = T := by
  have hloc : ∀ (f : Lp ℂ 2 μ) (s : Set α), MeasurableSet s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → T f x = 0 := by
    intro f s hs hf
    set sₙ : ℕ → Set α := fun n ↦ spanningSets μ n ∩ s
    have hsₙ (n : ℕ) : MeasurableSet (sₙ n) := (measurableSet_spanningSets μ n).inter hs
    have hμsₙ (n : ℕ) : μ (sₙ n) ≠ ∞ :=
      ((measure_mono Set.inter_subset_left).trans_lt (measure_spanningSets_lt_top μ n)).ne
    have hfs : indicatorMultiplication ℂ 2 hs f = f :=
      indicatorMultiplication_eq_self_of_ae_notMem hs hf
    let fₙ (n : ℕ) : Lp ℂ 2 μ := indicatorMultiplication ℂ 2 (hsₙ n) f
    have hfₙ (n : ℕ) : fₙ n = indicatorMultiplication ℂ 2 (measurableSet_spanningSets μ n) f := by
      dsimp only [fₙ]
      rw [← indicatorMultiplication_comp_indicatorMultiplication
        (measurableSet_spanningSets μ n) hs, comp_apply, hfs]
    have htend : Tendsto fₙ atTop (𝓝 f) := by
      simpa only [funext hfₙ] using tendsto_indicatorMultiplication_spanningSets f
    refine (Lp.isClosed_setOf_ae_notMem_imp_eq_zero s).mem_of_tendsto
      ((T.continuous.tendsto f).comp htend) (.of_forall fun n ↦ ?_)
    have hTfₙ : T (fₙ n) = indicatorMultiplication ℂ 2 (hsₙ n) (T f) :=
      (hcomm (hsₙ n) (hμsₙ n)).indicatorMultiplication_apply f
    filter_upwards [(Lp.ext_iff.mp hTfₙ).trans (indicatorMultiplication_ae (hsₙ n) (T f))]
      with x hx hxs
    rw [Function.comp_apply, hx, Set.indicator_of_notMem fun (h : x ∈ sₙ n) ↦ hxs h.2]
  exact (exists_eq_multiplicationOperator_of_forall_ae_eq_zero ENNReal.ofNat_ne_top hloc).imp
    fun _ h ↦ h.symm

/-- On a sigma-finite measure space, the centralizer in `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` of the range of
`multiplicationOperator` is that range itself. -/
theorem centralizer_range_multiplicationOperator [SigmaFinite μ] :
    (Set.range (multiplicationOperator (𝕜 := ℂ) (E := ℂ) (p := 2) (μ := μ))).centralizer =
      Set.range (multiplicationOperator (𝕜 := ℂ) (E := ℂ) (p := 2) (μ := μ)) := by
  ext T
  constructor
  · intro hT
    exact exists_multiplicationOperator_eq_of_forall_commute_indicatorMultiplication T
      fun _ hs _ ↦ commute_indicatorMultiplication_of_mem_centralizer_range hT hs
  · rintro ⟨a, rfl⟩ S ⟨b, rfl⟩
    exact (commute_iff_eq _ _).mp (commute_multiplicationOperator b a)

/-- An `L∞` symbol supported on a finite-measure measurable set `s` whose multiplication operator
on `Lp E 2 μ` (for a nontrivial space `E`) vanishes is zero in `Lp ℂ ∞ μ` (with no `SigmaFinite`
hypothesis on `μ`). -/
theorem eq_zero_of_mul_linftyIndicator_eq_self_of_multiplicationOperator_eq_zero
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E]
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) {a : Lp ℂ ∞ μ}
    (hsupp : a * TauCeti.linftyIndicator μ ℂ s hs = a)
    (hzero : multiplicationOperator (E := E) (p := 2) a = 0) : a = 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have happly : multiplicationOperator (E := E) a (indicatorConstLp 2 hs hμs v) = 0 := by
    rw [hzero, zero_apply]
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  filter_upwards [(Lp.ext_iff.mp hsupp.symm).trans (Lp.coeFn_mul a _),
    TauCeti.coeFn_linftyIndicator (μ := μ) (R := ℂ) hs,
    (multiplicationOperator_ae a (indicatorConstLp 2 hs hμs v)).symm.trans
      ((Lp.ext_iff.mp happly).trans (Lp.coeFn_zero E 2 μ)),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := v)]
    with x hmul hsx h0 hind
  by_cases hxs : x ∈ s
  · simp only [hind, Set.indicator_of_mem hxs, Pi.zero_apply, smul_eq_zero] at h0
    exact h0.resolve_right hv
  · rw [hmul, Pi.mul_apply, hsx, Set.indicator_of_notMem hxs, mul_zero, Pi.zero_apply]

end MeasureTheory.Lp

end
