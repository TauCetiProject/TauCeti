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
finite-measure set
(`MeasureTheory.Lp.exists_norm_le_and_comp_multiplicationOperator_linftyIndicator_eq`),
and globally multiplication by an `L∞` symbol when the measure is `σ`-finite
(`MeasureTheory.Lp.exists_multiplicationOperator_eq_of_forall_commute_linftyIndicator` and
`MeasureTheory.Lp.centralizer_range_multiplicationOperator`).

Without any `σ`-finiteness assumption on `μ`, any two bounded operators on `Lp ℂ 2 μ` commuting
with all finite-measure indicator multiplications commute with each other
(`MeasureTheory.Lp.commute_of_forall_commute_multiplicationOperator_linftyIndicator`), and indicator
multiplications are faithful on finite-measure measurable sets up to almost-everywhere equality
(`MeasureTheory.Lp.ae_eq_of_multiplicationOperator_linftyIndicator_eq`).

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
theorem tendsto_multiplicationOperator_linftyIndicator_spanningSets [SigmaFinite μ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Lp E 2 μ) :
    Tendsto (fun n ↦ multiplicationOperator
      (TauCeti.linftyIndicator μ ℂ (spanningSets μ n) (measurableSet_spanningSets μ n)) f)
      atTop (𝓝 f) := by
  have hmem (n : ℕ) : MemLp ((spanningSets μ n).indicator ⇑f) 2 μ :=
    (Lp.memLp f).indicator (measurableSet_spanningSets μ n).nullMeasurableSet
  have heq (n : ℕ) : multiplicationOperator
      (TauCeti.linftyIndicator μ ℂ (spanningSets μ n) (measurableSet_spanningSets μ n)) f =
      (hmem n).toLp _ := by
    rw [multiplicationOperator_apply, TauCeti.linftyIndicator_smul_eq_toLp]
  simp_rw [heq]
  refine TauCeti.tendsto_toLp_of_ae_tendsto_of_norm_le ENNReal.ofNat_ne_top hmem
    EventuallyEq.rfl (fun n ↦ .of_forall fun x ↦ norm_indicator_le_norm_self _ _) ?_
  refine .of_forall fun x ↦ tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_mem_spanningSets μ x] with n hn
  exact (Set.indicator_of_mem hn _).symm

/-- **Local multiplier representation on a finite-measure set.** On an arbitrary measure space, a
bounded operator on `Lp ℂ 2 μ` that commutes with indicator multiplications on measurable subsets
of a finite-measure measurable set `s` agrees after cutoff to `s` with multiplication by an `L∞`
symbol of norm at most `‖T‖`. -/
theorem exists_norm_le_and_comp_multiplicationOperator_linftyIndicator_eq {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hcomm : ∀ ⦃t : Set α⦄ (ht : MeasurableSet t), t ⊆ s →
      Commute T (multiplicationOperator (TauCeti.linftyIndicator μ ℂ t ht))) :
    ∃ a : Lp ℂ ∞ μ, ‖a‖ ≤ ‖T‖ ∧
      T ∘L multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs) =
        multiplicationOperator a ∘L
          multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs) := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs
  let R : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (μ.restrict s) := LpToLpRestrictCLM α ℂ ℂ μ 2 s
  let ι : Lp ℂ 2 (μ.restrict s) →L[ℂ] Lp ℂ 2 μ :=
    (compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ id
      ⟨measurable_id, by simp⟩).toContinuousLinearMap.comp
      (TauCeti.extendByZeroLpₗᵢ ℂ μ hs.nullMeasurableSet (Set.subset_univ s)).toContinuousLinearMap
  have hι_ae (g : Lp ℂ 2 (μ.restrict s)) : ι g =ᵐ[μ] s.indicator ⇑g := by
    have h1 : (ι g : α → ℂ) =ᵐ[μ]
        ⇑(TauCeti.extendByZeroLpₗᵢ ℂ μ hs.nullMeasurableSet (Set.subset_univ s) g) := by
      simpa only [ι, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        coe_compMeasurePreservingₗᵢ, Function.comp_id] using
        coeFn_compMeasurePreserving
          (TauCeti.extendByZeroLpₗᵢ ℂ μ hs.nullMeasurableSet (Set.subset_univ s) g)
          ⟨measurable_id, by simp⟩
    have h2 : ⇑(TauCeti.extendByZeroLpₗᵢ ℂ μ hs.nullMeasurableSet (Set.subset_univ s) g) =ᵐ[μ]
        s.indicator ⇑g := by
      simpa only [Measure.restrict_univ] using
        TauCeti.coeFn_extendByZeroLpₗᵢ ℂ hs.nullMeasurableSet (Set.subset_univ s) g
    exact h1.trans h2
  have hι_norm (g : Lp ℂ 2 (μ.restrict s)) : ‖ι g‖ = ‖g‖ := by
    simp only [ι, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.norm_map]
  have hιR (f : Lp ℂ 2 μ) :
      ι (R f) = multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs) f := by
    refine Lp.ext ((hι_ae (R f)).trans ?_)
    filter_upwards [(ae_restrict_iff' hs).mp (LpToLpRestrictCLM_coeFn ℂ s f),
      (multiplicationOperator_ae (TauCeti.linftyIndicator μ ℂ s hs) f).symm,
      TauCeti.coeFn_linftyIndicator (μ := μ) (R := ℂ) hs] with x hxR hmul hind
    rw [← hmul]
    by_cases hxs : x ∈ s
    · simp [R, hxs, hxR hxs, hind]
    · simp [hxs, hind]
  let S : Lp ℂ 2 (μ.restrict s) →L[ℂ] Lp ℂ 2 (μ.restrict s) := R.comp (T.comp ι)
  have hS_norm : ‖S‖ ≤ ‖T‖ := by
    refine opNorm_le_bound S (norm_nonneg T) fun g ↦ ?_
    calc ‖S g‖ = ‖R (T (ι g))‖ := rfl
      _ ≤ ‖T (ι g)‖ := norm_Lp_toLp_restrict_le s _
      _ ≤ ‖T‖ * ‖ι g‖ := T.le_opNorm _
      _ = ‖T‖ * ‖g‖ := by rw [hι_norm]
  have hS_loc : ∀ (g : Lp ℂ 2 (μ.restrict s)) (t : Set α), MeasurableSet t →
      (∀ᵐ x ∂μ.restrict s, x ∉ t → g x = 0) → ∀ᵐ x ∂μ.restrict s, x ∉ t → S g x = 0 := by
    intro g t ht hg
    set r := t ∩ s
    have hr : MeasurableSet r := ht.inter hs
    have hι_fix : multiplicationOperator (TauCeti.linftyIndicator μ ℂ r hr) (ι g) = ι g := by
      refine Lp.ext ?_
      filter_upwards [multiplicationOperator_ae (TauCeti.linftyIndicator μ ℂ r hr) (ι g),
        TauCeti.coeFn_linftyIndicator (μ := μ) (R := ℂ) hr, hι_ae g,
        (ae_restrict_iff' hs).mp hg] with x hmul hind hιx hgx
      rw [hmul, hind]
      by_cases hxr : x ∈ r
      · simp [hxr]
      · have hxrg : x ∈ s → g x = 0 := fun hxs ↦ hgx hxs fun hxt ↦ hxr ⟨hxt, hxs⟩
        by_cases hxs : x ∈ s
        · simp [hxr, hιx, hxs, hxrg hxs]
        · simp [hxr, hιx, hxs]
    have hTι : T (ι g) = multiplicationOperator (TauCeti.linftyIndicator μ ℂ r hr) (T (ι g)) := by
      calc T (ι g) = T (multiplicationOperator (TauCeti.linftyIndicator μ ℂ r hr) (ι g)) := by
            rw [hι_fix]
        _ = multiplicationOperator (TauCeti.linftyIndicator μ ℂ r hr) (T (ι g)) := by
            have := congrArg (fun A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ ↦ A (ι g))
              ((commute_iff_eq _ _).mp (hcomm hr Set.inter_subset_right))
            simpa only [mul_apply_eq_comp, comp_apply] using this
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ s (T (ι g)),
      ae_restrict_of_ae ((Lp.ext_iff.mp hTι).trans
        (multiplicationOperator_ae (TauCeti.linftyIndicator μ ℂ r hr) (T (ι g)))),
      ae_restrict_of_ae (TauCeti.coeFn_linftyIndicator (μ := μ) (R := ℂ) hr),
      ae_restrict_mem hs] with x hxR hxT hind _hxs hxt
    have hxr : x ∉ r := fun h ↦ hxt h.1
    change R (T (ι g)) x = 0
    rw [hxR, hxT, hind, Set.indicator_of_notMem hxr, zero_smul]
  obtain ⟨m, hm_meas, hm_norm, hm_apply⟩ :=
    ContinuousLinearMap.exists_forall_ae_eq_apply_of_forall_ae_eq_zero ENNReal.ofNat_ne_top S hS_loc
  set φ : α → ℂ := s.indicator fun x ↦ m x 1
  have hφ_meas : StronglyMeasurable φ :=
    ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).continuous.comp_stronglyMeasurable
      hm_meas).indicator hs
  have hφ_bdd : ∀ᵐ x ∂μ, ‖φ x‖ ≤ ‖T‖ := by
    filter_upwards [(ae_restrict_iff' hs).mp hm_norm] with x hx
    dsimp only [φ]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs]
      exact (ContinuousLinearMap.le_opNorm (m x) 1).trans <| by
        simpa only [norm_one, mul_one] using (hx hxs).trans hS_norm
    · simp [hxs, norm_nonneg]
  have hφ_mem : MemLp φ ∞ μ := memLp_top_of_bound hφ_meas.aestronglyMeasurable ‖T‖ hφ_bdd
  have ha_norm : ‖hφ_mem.toLp φ‖ ≤ ‖T‖ := Lp.norm_le_of_ae_bound_top (norm_nonneg T) <| by
    filter_upwards [hφ_mem.coeFn_toLp, hφ_bdd] with x hx hb
    rwa [hx]
  refine ⟨hφ_mem.toLp φ, ha_norm, ContinuousLinearMap.ext fun f ↦ Lp.ext ?_⟩
  set P := multiplicationOperator (E := ℂ) (p := 2) (TauCeti.linftyIndicator μ ℂ s hs)
  have hTf_off : ∀ᵐ x ∂μ, x ∉ s → T (P f) x = 0 := by
    have hTP : T (P f) = P (T f) := by
      simpa only [P, mul_apply_eq_comp, comp_apply] using
        congrArg (fun A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ ↦ A f)
          ((commute_iff_eq _ _).mp (hcomm hs Set.Subset.rfl))
    filter_upwards [(Lp.ext_iff.mp hTP).trans (multiplicationOperator_ae _ (T f)),
      TauCeti.coeFn_linftyIndicator (μ := μ) (R := ℂ) hs] with x hx hind hxs
    rw [hx, hind, Set.indicator_of_notMem hxs, zero_smul]
  have hTf_on : ⇑(T (P f)) =ᵐ[μ.restrict s] fun x ↦ m x (f x) := by
    have h1 : ⇑(T (P f)) =ᵐ[μ.restrict s] ⇑(S (R f)) := by
      filter_upwards [LpToLpRestrictCLM_coeFn ℂ s (T (ι (R f)))] with x hx
      simpa only [S, comp_apply, hιR] using hx.symm
    have h2 : (fun x ↦ m x (R f x)) =ᵐ[μ.restrict s] fun x ↦ m x (f x) :=
      (LpToLpRestrictCLM_coeFn ℂ s f).mono fun x hx ↦ congrArg (m x) hx
    exact (h1.trans (hm_apply (R f))).trans h2
  filter_upwards [hTf_off, (ae_restrict_iff' hs).mp hTf_on,
    multiplicationOperator_ae (hφ_mem.toLp φ) (P f),
    multiplicationOperator_ae (TauCeti.linftyIndicator μ ℂ s hs) f,
    hφ_mem.coeFn_toLp, TauCeti.coeFn_linftyIndicator (μ := μ) (R := ℂ) hs]
    with x hxoff hxon hmul₁ hmul₂ hφx hind
  change T (P f) x = (multiplicationOperator (hφ_mem.toLp φ) (P f)) x
  by_cases hxs : x ∈ s
  · rw [hxon hxs, hmul₁, hmul₂, hφx, hind]
    simp only [φ, Set.indicator_of_mem hxs, Pi.one_apply, smul_eq_mul, one_mul]
    have hm1 : m x (f x) = f x * m x 1 := by
      simpa only [smul_eq_mul, mul_one] using map_smul (m x) (f x) (1 : ℂ)
    rw [hm1, mul_comm]
  · rw [hxoff hxs, hmul₁, hmul₂, hind, Set.indicator_of_notMem hxs, zero_smul, smul_zero]

/-- **Unconditional commutativity of the multiplier commutant.** On an arbitrary measure space —
with no sigma-finiteness assumption — any two bounded operators on `Lp ℂ 2 μ` that commute with
all finite-measure indicator multiplications commute with each other. -/
theorem commute_of_forall_commute_multiplicationOperator_linftyIndicator
    {S T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    (hS : ∀ ⦃s : Set α⦄ (hs : MeasurableSet s), μ s ≠ ∞ →
      Commute S (multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs)))
    (hT : ∀ ⦃s : Set α⦄ (hs : MeasurableSet s), μ s ≠ ∞ →
      Commute T (multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs))) :
    Commute S T := by
  refine (commute_iff_eq _ _).mpr
    (ContinuousLinearMap.ext_indicatorConstLp ENNReal.ofNat_ne_top fun s hs hμs c ↦ ?_)
  set u := indicatorConstLp 2 hs hμs c
  set P := multiplicationOperator (E := ℂ) (p := 2) (TauCeti.linftyIndicator μ ℂ s hs)
  have hPu : P u = u :=
    multiplicationOperator_linftyIndicator_indicatorConstLp_self hs hμs c
  obtain ⟨a, -, ha⟩ := exists_norm_le_and_comp_multiplicationOperator_linftyIndicator_eq hs
    hμs S fun t ht hts ↦ hS ht ((measure_mono hts).trans_lt hμs.lt_top).ne
  obtain ⟨b, -, hb⟩ := exists_norm_le_and_comp_multiplicationOperator_linftyIndicator_eq hs
    hμs T fun t ht hts ↦ hT ht ((measure_mono hts).trans_lt hμs.lt_top).ne
  have happly {A B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} {x y : Lp ℂ ∞ μ}
      (hA : A ∘L P = multiplicationOperator x ∘L P)
      (hB : B ∘L P = multiplicationOperator y ∘L P) :
      (A * B) u = multiplicationOperator (x * y) u := by
    have hBu : B u = multiplicationOperator y u := by
      simpa only [comp_apply, hPu] using congrArg (fun R ↦ R u) hB
    have hPBu : P (B u) = B u := by
      rw [hBu, ← mul_apply_eq_comp,
        (commute_iff_eq _ _).mp (commute_multiplicationOperator _ y), mul_apply_eq_comp, hPu]
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
  commute_of_forall_commute_multiplicationOperator_linftyIndicator
    (fun _ _ _ ↦ commute_multiplicationOperator_of_mem_centralizer_range hS _)
    (fun _ _ _ ↦ commute_multiplicationOperator_of_mem_centralizer_range hT _)

/-- **Multiplier commutant theorem on sigma-finite `L²`.** Every bounded operator on `Lp ℂ 2 μ`
that commutes with all finite-measure indicator multiplications is multiplication by an essentially
bounded symbol. -/
theorem exists_multiplicationOperator_eq_of_forall_commute_linftyIndicator [SigmaFinite μ]
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hcomm : ∀ ⦃s : Set α⦄ (hs : MeasurableSet s), μ s ≠ ∞ →
      Commute T (multiplicationOperator (TauCeti.linftyIndicator μ ℂ s hs))) :
    ∃ a : Lp ℂ ∞ μ, multiplicationOperator (E := ℂ) a = T := by
  have hloc : ∀ (f : Lp ℂ 2 μ) (s : Set α), MeasurableSet s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → T f x = 0 := by
    intro f s hs hf
    set sₙ : ℕ → Set α := fun n ↦ s ∩ spanningSets μ n
    have hsₙ (n : ℕ) : MeasurableSet (sₙ n) := hs.inter (measurableSet_spanningSets μ n)
    have hμsₙ (n : ℕ) : μ (sₙ n) ≠ ∞ :=
      ((measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
    have hmem (n : ℕ) : MemLp ((sₙ n).indicator ⇑f) 2 μ :=
      (Lp.memLp f).indicator (hsₙ n).nullMeasurableSet
    let fₙ (n : ℕ) : Lp ℂ 2 μ :=
      multiplicationOperator (TauCeti.linftyIndicator μ ℂ (sₙ n) (hsₙ n)) f
    have hfₙ_eq (n : ℕ) : fₙ n = (hmem n).toLp _ := by
      dsimp only [fₙ]
      rw [multiplicationOperator_apply, TauCeti.linftyIndicator_smul_eq_toLp]
    have htend : Tendsto fₙ atTop (𝓝 f) := by
      rw [show fₙ = fun n ↦ (hmem n).toLp _ from funext hfₙ_eq]
      refine TauCeti.tendsto_toLp_of_ae_tendsto_of_norm_le ENNReal.ofNat_ne_top hmem
        EventuallyEq.rfl (fun n ↦ .of_forall fun x ↦ norm_indicator_le_norm_self _ _) ?_
      filter_upwards [hf] with x hfx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_mem_spanningSets μ x] with n hn
      by_cases hxs : x ∈ s
      · exact (Set.indicator_of_mem (show x ∈ sₙ n from ⟨hxs, hn⟩) _).symm
      · rw [hfx hxs]
        exact (Set.indicator_apply_eq_zero.2 fun _ ↦ hfx hxs).symm
    refine (Lp.isClosed_setOf_ae_notMem_imp_eq_zero s).mem_of_tendsto
      ((T.continuous.tendsto f).comp htend) (.of_forall fun n ↦ ?_)
    have hTfₙ : T (fₙ n) =
        multiplicationOperator (TauCeti.linftyIndicator μ ℂ (sₙ n) (hsₙ n)) (T f) := by
      have := congrArg (fun A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ ↦ A f)
        ((commute_iff_eq _ _).mp (hcomm (hsₙ n) (hμsₙ n)))
      simpa only [fₙ, mul_apply_eq_comp, comp_apply] using this
    filter_upwards [(Lp.ext_iff.mp hTfₙ).trans (multiplicationOperator_ae _ (T f)),
      TauCeti.coeFn_linftyIndicator (μ := μ) (R := ℂ) (hsₙ n)] with x hx hind hxs
    change T (fₙ n) x = 0
    rw [hx, hind, Set.indicator_of_notMem fun (h : x ∈ sₙ n) ↦ hxs h.1, zero_smul]
  obtain ⟨m, hm_meas, hm_norm, hm_apply⟩ :=
    ContinuousLinearMap.exists_forall_ae_eq_apply_of_forall_ae_eq_zero ENNReal.ofNat_ne_top T hloc
  set φ : α → ℂ := fun x ↦ m x 1
  have hφ_meas : StronglyMeasurable φ :=
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).continuous.comp_stronglyMeasurable hm_meas
  have hφ_bdd : ∀ᵐ x ∂μ, ‖φ x‖ ≤ ‖T‖ :=
    hm_norm.mono fun x hx ↦ (ContinuousLinearMap.le_opNorm (m x) 1).trans <| by
      simpa only [norm_one, mul_one] using hx
  have hφ_mem : MemLp φ ∞ μ := memLp_top_of_bound hφ_meas.aestronglyMeasurable ‖T‖ hφ_bdd
  refine ⟨hφ_mem.toLp φ, ContinuousLinearMap.ext fun f ↦ Lp.ext ?_⟩
  filter_upwards [multiplicationOperator_ae (hφ_mem.toLp φ) f, hφ_mem.coeFn_toLp,
    hm_apply f] with x hmul hφx hTx
  rw [hmul, hφx, hTx]
  have hm1 : m x (f x) = f x * m x 1 := by
    simpa only [smul_eq_mul, mul_one] using map_smul (m x) (f x) (1 : ℂ)
  rw [hm1, smul_eq_mul, mul_comm]

/-- On a sigma-finite measure space, the centralizer in `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` of the range of
`multiplicationOperator` is that range itself. -/
theorem centralizer_range_multiplicationOperator [SigmaFinite μ] :
    (Set.range (multiplicationOperator (𝕜 := ℂ) (E := ℂ) (p := 2) (μ := μ))).centralizer =
      Set.range (multiplicationOperator (𝕜 := ℂ) (E := ℂ) (p := 2) (μ := μ)) := by
  ext T
  constructor
  · intro hT
    exact exists_multiplicationOperator_eq_of_forall_commute_linftyIndicator T fun _ _ _ ↦
      commute_multiplicationOperator_of_mem_centralizer_range hT _
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

/-- If two finite-measure measurable sets induce the same `L∞` indicator multiplication operator on
`Lp E 2 μ` (for a nontrivial space `E`), then the two sets agree almost everywhere (with no
`SigmaFinite` hypothesis on `μ`). -/
theorem ae_eq_of_multiplicationOperator_linftyIndicator_eq
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E]
    {s t : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (ht : MeasurableSet t) (hμt : μ t ≠ ∞)
    (h : multiplicationOperator (E := E) (p := 2) (TauCeti.linftyIndicator μ ℂ s hs) =
      multiplicationOperator (E := E) (p := 2) (TauCeti.linftyIndicator μ ℂ t ht)) :
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
      (by rw [multiplicationOperator_sub, h, sub_self])
  exact (TauCeti.linftyIndicator_inj hs ht).mp (sub_eq_zero.mp hst)

end MeasureTheory.Lp

end
