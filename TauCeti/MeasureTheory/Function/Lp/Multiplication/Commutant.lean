/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Multiplication.Basic
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import TauCeti.MeasureTheory.Function.Lp.Operator.Local
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# Commutant and faithfulness of `L²` multiplication operators

On complex scalar `L²`, every bounded operator commuting with measurable-set indicator
multiplications on sets of finite measure is locally multiplication by an `L∞` symbol on each
finite-measure set (`MeasureTheory.Lp.exists_norm_le_and_comp_indicatorMultiplication_eq`),
a local bounded operator on `Lp ℂ 2 ν` is multiplication by an `L∞` symbol
(`MeasureTheory.Lp.exists_norm_le_and_multiplicationOperator_eq_of_forall_ae_eq_zero`),
and globally multiplication by an `L∞` symbol when the measure is `σ`-finite
(`MeasureTheory.Lp.exists_multiplicationOperator_eq_of_forall_commute_indicatorMultiplication` and
`MeasureTheory.Lp.centralizer_range_multiplicationOperator`).

Without any `σ`-finiteness assumption on `μ`, any two bounded operators on `Lp ℂ 2 μ` commuting
with all finite-measure indicator multiplications commute with each other
(`MeasureTheory.Lp.commute_of_forall_commute_indicatorMultiplication`), and indicator
multiplications are faithful on finite-measure measurable sets up to almost-everywhere equality
(`MeasureTheory.Lp.ae_eq_of_indicatorMultiplication_eq`).

## References

* M. Takesaki, *Theory of Operator Algebras I*, Springer, 2002, Chapter III, §1.
* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  Academic Press, 1983, Example 5.1.6.
-/

public section

noncomputable section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory.Lp

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

/-- Scalar specialization of `ContinuousLinearMap.exists_forall_ae_eq_apply_of_forall_ae_eq_zero`:
a local bounded operator on `Lp ℂ 2 ν` (for `σ`-finite `ν`) is multiplication by an `L∞` symbol
of norm at most `‖S‖`. -/
theorem exists_norm_le_and_multiplicationOperator_eq_of_forall_ae_eq_zero
    {ν : Measure α} [SigmaFinite ν] (S : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hS : ∀ (f : Lp ℂ 2 ν) (t : Set α), MeasurableSet t → (∀ᵐ x ∂ν, x ∉ t → f x = 0) →
      ∀ᵐ x ∂ν, x ∉ t → S f x = 0) :
    ∃ a : Lp ℂ ∞ ν, ‖a‖ ≤ ‖S‖ ∧ multiplicationOperator (E := ℂ) a = S := by
  obtain ⟨m, hm_meas, hm_norm, hm_apply⟩ :=
    ContinuousLinearMap.exists_forall_ae_eq_apply_of_forall_ae_eq_zero ENNReal.ofNat_ne_top S hS
  set φ : α → ℂ := fun x ↦ m x 1
  have hφ_meas : StronglyMeasurable φ :=
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).continuous.comp_stronglyMeasurable hm_meas
  have hφ_bdd : ∀ᵐ x ∂ν, ‖φ x‖ ≤ ‖S‖ :=
    hm_norm.mono fun x hx ↦ (ContinuousLinearMap.le_opNorm (m x) 1).trans <| by
      simpa only [norm_one, mul_one] using hx
  have hφ_mem : MemLp φ ∞ ν := memLp_top_of_bound hφ_meas.aestronglyMeasurable ‖S‖ hφ_bdd
  have ha_norm : ‖hφ_mem.toLp φ‖ ≤ ‖S‖ := Lp.norm_le_of_ae_bound_top (norm_nonneg S) <| by
    filter_upwards [hφ_mem.coeFn_toLp, hφ_bdd] with x hx hb
    rwa [hx]
  refine ⟨hφ_mem.toLp φ, ha_norm, ContinuousLinearMap.ext fun f ↦ Lp.ext ?_⟩
  filter_upwards [multiplicationOperator_ae (hφ_mem.toLp φ) f, hφ_mem.coeFn_toLp,
    hm_apply f] with x hmul hφx hSx
  rw [hmul, hφx, hSx]
  have hm1 : m x (f x) = f x * m x 1 := by
    simpa only [smul_eq_mul, mul_one] using map_smul (m x) (f x) (1 : ℂ)
  rw [hm1, smul_eq_mul, mul_comm]

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
  let R : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (μ.restrict s) := LpToLpRestrictCLM α ℂ ℂ μ 2 s
  let ι (p : ℝ≥0∞) [Fact (1 ≤ p)] : Lp ℂ p (μ.restrict s) →ₗᵢ[ℂ] Lp ℂ p μ :=
    (TauCeti.castLpₗᵢ (𝕜 := ℂ) (E := ℂ) (p := p) Measure.restrict_univ).toLinearIsometry.comp
      (TauCeti.extendByZeroLpₗᵢ ℂ μ hs.nullMeasurableSet (Set.subset_univ s))
  have hι_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : Lp ℂ p (μ.restrict s)) :
      (ι p g : α → ℂ) =ᵐ[μ] s.indicator ⇑g :=
    TauCeti.coeFn_castLpₗᵢ_extendByZeroLpₗᵢ ℂ hs.nullMeasurableSet g
  have hιR (f : Lp ℂ 2 μ) : ι 2 (R f) = indicatorMultiplication ℂ 2 hs f := by
    refine Lp.ext ((hι_ae 2 (R f)).trans ?_)
    filter_upwards [(ae_restrict_iff' hs).mp (LpToLpRestrictCLM_coeFn ℂ s f),
      (indicatorMultiplication_ae (𝕜 := ℂ) hs f).symm] with x hxR hind
    rw [← hind]
    by_cases hxs : x ∈ s
    · simp [R, hxs, hxR hxs]
    · simp [hxs]
  let S : Lp ℂ 2 (μ.restrict s) →L[ℂ] Lp ℂ 2 (μ.restrict s) :=
    R.comp (T.comp (ι 2).toContinuousLinearMap)
  have hS_norm : ‖S‖ ≤ ‖T‖ := opNorm_le_bound S (norm_nonneg T) fun g ↦
    calc ‖S g‖ ≤ ‖T (ι 2 g)‖ := norm_Lp_toLp_restrict_le s _
      _ ≤ ‖T‖ * ‖ι 2 g‖ := T.le_opNorm _
      _ = ‖T‖ * ‖g‖ := by rw [(ι 2).norm_map]
  have hS_loc : ∀ (g : Lp ℂ 2 (μ.restrict s)) (t : Set α), MeasurableSet t →
      (∀ᵐ x ∂μ.restrict s, x ∉ t → g x = 0) → ∀ᵐ x ∂μ.restrict s, x ∉ t → S g x = 0 := by
    intro g t ht hg
    set r := t ∩ s
    have hr : MeasurableSet r := ht.inter hs
    have hι_fix : indicatorMultiplication ℂ 2 hr (ι 2 g) = ι 2 g := by
      refine indicatorMultiplication_eq_iff.mpr ?_
      filter_upwards [hι_ae 2 g, (ae_restrict_iff' hs).mp hg] with x hιx hgx
      by_cases hxr : x ∈ r
      · rw [Set.indicator_of_mem hxr]
      · rw [Set.indicator_of_notMem hxr, hιx]
        by_cases hxs : x ∈ s
        · rw [Set.indicator_of_mem hxs, hgx hxs fun hxt ↦ hxr ⟨hxt, hxs⟩]
        · rw [Set.indicator_of_notMem hxs]
    have hTι : T (ι 2 g) = indicatorMultiplication ℂ 2 hr (T (ι 2 g)) := by
      have hc := congrArg (fun A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ ↦ A (ι 2 g))
        ((commute_iff_eq _ _).mp (hcomm hr Set.inter_subset_right))
      simpa only [mul_apply_eq_comp, comp_apply, hι_fix] using hc
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ s (T (ι 2 g)),
      ae_restrict_of_ae ((Lp.ext_iff.mp hTι).trans (indicatorMultiplication_ae hr (T (ι 2 g)))),
      ae_restrict_mem hs] with x hxR hxT _hxs hxt
    change R (T (ι 2 g)) x = 0
    rw [hxR, hxT, Set.indicator_of_notMem fun (h : x ∈ r) ↦ hxt h.1]
  obtain ⟨b, hb_norm, hb_eq⟩ :=
    exists_norm_le_and_multiplicationOperator_eq_of_forall_ae_eq_zero S hS_loc
  refine ⟨ι ∞ b, ((ι ∞).norm_map b).trans_le (hb_norm.trans hS_norm),
    ContinuousLinearMap.ext fun f ↦ Lp.ext ?_⟩
  set P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := indicatorMultiplication ℂ 2 hs
  have hTf_off : ∀ᵐ x ∂μ, x ∉ s → T (P f) x = 0 := by
    have hTP : T (P f) = P (T f) := by
      simpa only [P, mul_apply_eq_comp, comp_apply] using
        congrArg (fun A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ ↦ A f)
          ((commute_iff_eq _ _).mp (hcomm hs Set.Subset.rfl))
    filter_upwards [(Lp.ext_iff.mp hTP).trans (indicatorMultiplication_ae hs (T f))]
      with x hx hxs
    rw [hx, Set.indicator_of_notMem hxs]
  have hTf_on : ⇑(T (P f)) =ᵐ[μ.restrict s] fun x ↦ b x * f x := by
    have h1 : ⇑(T (P f)) =ᵐ[μ.restrict s] ⇑(multiplicationOperator (E := ℂ) b (R f)) := by
      have hS_apply : multiplicationOperator (E := ℂ) b (R f) = R (T (ι 2 (R f))) :=
        congrArg (fun A : Lp ℂ 2 (μ.restrict s) →L[ℂ] Lp ℂ 2 (μ.restrict s) ↦ A (R f)) hb_eq
      filter_upwards [LpToLpRestrictCLM_coeFn ℂ s (T (ι 2 (R f)))] with x hx
      simpa only [hS_apply, hιR] using hx.symm
    filter_upwards [h1, multiplicationOperator_ae b (R f), LpToLpRestrictCLM_coeFn ℂ s f]
      with x hx₁ hmul hR
    rw [hx₁, hmul, hR, smul_eq_mul]
  filter_upwards [hTf_off, (ae_restrict_iff' hs).mp hTf_on,
    multiplicationOperator_ae (ι ∞ b) (P f), indicatorMultiplication_ae (𝕜 := ℂ) hs f,
    hι_ae ∞ b] with x hxoff hxon hmul₁ hmul₂ hax
  change T (P f) x = (multiplicationOperator (ι ∞ b) (P f)) x
  by_cases hxs : x ∈ s
  · rw [hxon hxs, hmul₁, hmul₂, hax, Set.indicator_of_mem hxs, Set.indicator_of_mem hxs,
      smul_eq_mul]
  · rw [hxoff hxs, hmul₁, hmul₂, Set.indicator_of_notMem hxs, smul_zero]

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
    hμs S fun t ht hts ↦ hS ht ((measure_mono hts).trans_lt hμs.lt_top).ne
  obtain ⟨b, -, hb⟩ := exists_norm_le_and_comp_indicatorMultiplication_eq hs
    hμs T fun t ht hts ↦ hT ht ((measure_mono hts).trans_lt hμs.lt_top).ne
  have happly {A B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} {x y : Lp ℂ ∞ μ}
      (hA : A ∘L P = multiplicationOperator x ∘L P)
      (hB : B ∘L P = multiplicationOperator y ∘L P) :
      (A * B) u = multiplicationOperator (x * y) u := by
    have hBu : B u = multiplicationOperator y u := by
      simpa only [comp_apply, hPu] using congrArg (fun R ↦ R u) hB
    have hPBu : P (B u) = B u := by
      dsimp only [P]
      rw [hBu, ← multiplicationOperator_linftyIndicator (𝕜 := ℂ) (E := ℂ) (p := 2) hs,
        ← mul_apply_eq_comp, (commute_iff_eq _ _).mp (commute_multiplicationOperator _ y),
        mul_apply_eq_comp, multiplicationOperator_linftyIndicator]
      exact congrArg (multiplicationOperator y) hPu
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

/-- On an arbitrary measure space, any two operators in the centralizer of the range of
`multiplicationOperator` commute with each other. -/
theorem commute_of_mem_centralizer_range_multiplicationOperator {S T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    (hS : S ∈ (Set.range (multiplicationOperator (E := ℂ) (μ := μ))).centralizer)
    (hT : T ∈ (Set.range (multiplicationOperator (E := ℂ) (μ := μ))).centralizer) :
    Commute S T :=
  commute_of_forall_commute_indicatorMultiplication
    (fun _ hs _ ↦ by
      rw [← multiplicationOperator_linftyIndicator hs]
      exact commute_multiplicationOperator_of_mem_centralizer_range hS _)
    (fun _ hs _ ↦ by
      rw [← multiplicationOperator_linftyIndicator hs]
      exact commute_multiplicationOperator_of_mem_centralizer_range hT _)

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
    have hfs : indicatorMultiplication ℂ 2 hs f = f := by
      refine indicatorMultiplication_eq_iff.mpr ?_
      filter_upwards [hf] with x hfx
      by_cases hxs : x ∈ s
      · rw [Set.indicator_of_mem hxs]
      · rw [Set.indicator_of_notMem hxs, hfx hxs]
    let fₙ (n : ℕ) : Lp ℂ 2 μ := indicatorMultiplication ℂ 2 (hsₙ n) f
    have hfₙ (n : ℕ) : fₙ n = indicatorMultiplication ℂ 2 (measurableSet_spanningSets μ n) f := by
      dsimp only [fₙ]
      rw [← indicatorMultiplication_comp_indicatorMultiplication
        (measurableSet_spanningSets μ n) hs, comp_apply, hfs]
    have htend : Tendsto fₙ atTop (𝓝 f) := by
      simpa only [funext hfₙ] using tendsto_indicatorMultiplication_spanningSets f
    refine (Lp.isClosed_setOf_ae_notMem_imp_eq_zero s).mem_of_tendsto
      ((T.continuous.tendsto f).comp htend) (.of_forall fun n ↦ ?_)
    have hTfₙ : T (fₙ n) = indicatorMultiplication ℂ 2 (hsₙ n) (T f) := by
      have := congrArg (fun A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ ↦ A f)
        ((commute_iff_eq _ _).mp (hcomm (hsₙ n) (hμsₙ n)))
      simpa only [fₙ, mul_apply_eq_comp, comp_apply] using this
    filter_upwards [(Lp.ext_iff.mp hTfₙ).trans (indicatorMultiplication_ae (hsₙ n) (T f))]
      with x hx hxs
    change T (fₙ n) x = 0
    rw [hx, Set.indicator_of_notMem fun (h : x ∈ sₙ n) ↦ hxs h.2]
  exact (exists_norm_le_and_multiplicationOperator_eq_of_forall_ae_eq_zero T hloc).imp fun _ h ↦ h.2

/-- On a sigma-finite measure space, the centralizer in `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` of the range of
`multiplicationOperator` is that range itself. -/
theorem centralizer_range_multiplicationOperator [SigmaFinite μ] :
    (Set.range (multiplicationOperator (𝕜 := ℂ) (E := ℂ) (p := 2) (μ := μ))).centralizer =
      Set.range (multiplicationOperator (𝕜 := ℂ) (E := ℂ) (p := 2) (μ := μ)) := by
  ext T
  constructor
  · intro hT
    exact exists_multiplicationOperator_eq_of_forall_commute_indicatorMultiplication T
      fun _ hs _ ↦ by
        rw [← multiplicationOperator_linftyIndicator hs]
        exact commute_multiplicationOperator_of_mem_centralizer_range hT _
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

/-- If two finite-measure measurable sets induce the same indicator multiplication operator on
`Lp E 2 μ` (for a nontrivial space `E`), then the two sets agree almost everywhere (with no
`SigmaFinite` hypothesis on `μ`). -/
theorem ae_eq_of_indicatorMultiplication_eq
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E]
    {s t : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (ht : MeasurableSet t) (hμt : μ t ≠ ∞)
    (h : indicatorMultiplication (E := E) (μ := μ) ℂ 2 hs =
      indicatorMultiplication (E := E) (μ := μ) ℂ 2 ht) :
    s =ᵐ[μ] t := by
  set es := TauCeti.linftyIndicator μ ℂ s hs
  set et := TauCeti.linftyIndicator μ ℂ t ht
  have hst : es - et = 0 :=
    eq_zero_of_mul_linftyIndicator_eq_self_of_multiplicationOperator_eq_zero (E := E)
      (hs.union ht) (measure_union_lt_top hμs.lt_top hμt.lt_top).ne
      (by
        rw [sub_mul,
          TauCeti.linftyIndicator_mul_linftyIndicator_of_subset_left hs (hs.union ht)
            Set.subset_union_left,
          TauCeti.linftyIndicator_mul_linftyIndicator_of_subset_left ht (hs.union ht)
            Set.subset_union_right])
      (by
        rw [multiplicationOperator_sub, multiplicationOperator_linftyIndicator,
          multiplicationOperator_linftyIndicator, h, sub_self])
  exact (TauCeti.linftyIndicator_inj hs ht).mp (sub_eq_zero.mp hst)

end MeasureTheory.Lp

end
