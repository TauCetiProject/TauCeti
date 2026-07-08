module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Generic conditional-expectation facts

- `condExp_indicator_eq_of_pair_law_eq`: if `(Y, Z)` and `(Y', Z)` have the same law, then for
  measurable `B` the conditional expectations of `𝟙_B ∘ Y` and `𝟙_B ∘ Y'` given `σ(Z)` agree a.e.
- `condExp_ae_eq_of_forall_condExp_ae_eq_of_tendsto_eLpNorm`: L¹-continuity of conditional
  expectation — if `Xn → Xlim` in L¹ (in `eLpNorm`) and each `μ[Xn n | F]` agrees a.e. with a fixed
  `Y`, then `μ[Xlim | F]` agrees a.e. with `Y`.

Both are generic conditional-expectation facts (no exchangeability/tail/directing-measure
hypotheses), each the bridge for a downstream construction.

Adapted from `cameronfreer/exchangeability` (`Probability/CondExp.lean` and
`Probability/Martingale/Convergence.lean`, pin `e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace TauCeti

namespace MeasureTheory

/-- The L¹ contraction property for real-valued conditional expectation.

This local spelling avoids depending on Mathlib's old deprecated name while remaining compatible
with the pinned Mathlib used by this branch. -/
theorem eLpNorm_condExp_le_eLpNorm_real {Ω : Type*} {m m0 : MeasurableSpace Ω}
    {μ : _root_.MeasureTheory.Measure Ω} (f : Ω → ℝ) :
    eLpNorm (μ[f | m]) 1 μ ≤ eLpNorm f 1 μ := by
  by_cases hf : Integrable f μ
  swap
  · rw [condExp_of_not_integrable hf, eLpNorm_zero]
    exact zero_le
  by_cases hm : m ≤ m0
  swap
  · rw [condExp_of_not_le hm, eLpNorm_zero]
    exact zero_le
  by_cases hsig : SigmaFinite (μ.trim hm)
  swap
  · rw [condExp_of_not_sigmaFinite hm hsig, eLpNorm_zero]
    exact zero_le
  calc
    eLpNorm (μ[f | m]) 1 μ ≤ eLpNorm (μ[(|f|) | m]) 1 μ := by
      refine eLpNorm_mono_ae ?_
      filter_upwards [condExp_mono hf hf.abs
        (ae_of_all μ (fun x => le_abs_self (f x) : ∀ x, f x ≤ |f x|)),
        (condExp_neg ..).symm.le.trans (condExp_mono hf.neg hf.abs
          (ae_of_all μ (fun x => neg_le_abs (f x) : ∀ x, -f x ≤ |f x|)))] with x hx₁ hx₂
      exact abs_le_abs hx₁ hx₂
    _ = eLpNorm f 1 μ := by
      rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm,
        ← ENNReal.toReal_eq_toReal_iff' (hasFiniteIntegral_iff_enorm.mp integrable_condExp.2).ne
          (hasFiniteIntegral_iff_enorm.mp hf.2).ne,
        ← integral_norm_eq_lintegral_enorm
          (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable,
        ← integral_norm_eq_lintegral_enorm hf.1]
      simp_rw [Real.norm_eq_abs]
      rw (config := { occs := .pos [2] }) [← integral_condExp hm]
      refine integral_congr_ae ?_
      have : 0 ≤ᵐ[μ] μ[(|f|) | m] := by
        rw [← condExp_zero]
        exact condExp_mono (integrable_zero _ _ _) hf.abs
          (ae_of_all μ (fun x => abs_nonneg (f x) : ∀ x, 0 ≤ |f x|))
      filter_upwards [this] with x hx
      exact abs_eq_self.2 hx

/-- If a real-valued function is bounded almost everywhere in absolute value by `R`, then so is its
conditional expectation.

This local spelling avoids depending on Mathlib's old deprecated name while remaining compatible
with the pinned Mathlib used by this branch. -/
theorem ae_bdd_abs_condExp_of_ae_bdd_abs_real {Ω : Type*} {m m0 : MeasurableSpace Ω}
    {μ : _root_.MeasureTheory.Measure Ω} {R : NNReal} {f : Ω → ℝ}
    (hbdd : ∀ᵐ x ∂μ, |f x| ≤ R) :
    ∀ᵐ x ∂μ, |(μ[f | m]) x| ≤ R := by
  by_cases hnm : m ≤ m0
  swap
  · simp_rw [condExp_of_not_le hnm, Pi.zero_apply, abs_zero]
    exact Eventually.of_forall fun _ => R.coe_nonneg
  by_cases hfint : Integrable f μ
  swap
  · simp_rw [condExp_of_not_integrable hfint]
    filter_upwards [hbdd] with x hx
    rw [Pi.zero_apply, abs_zero]
    exact (abs_nonneg _).trans hx
  by_contra h
  change μ _ ≠ 0 at h
  simp only [← pos_iff_ne_zero, Set.compl_def, Set.mem_setOf_eq] at h
  suffices μ.real {x | ↑R < |(μ[f|m]) x|} * ↑R < μ.real {x | ↑R < |(μ[f|m]) x|} * ↑R by
    exact this.ne rfl
  refine lt_of_lt_of_le (setIntegral_gt_gt R.coe_nonneg ?_ (by simpa only [not_le] using h.ne')) ?_
  · exact integrable_condExp.abs.integrableOn
  refine (_root_.MeasureTheory.setIntegral_abs_condExp_le ?_ _).trans ?_
  · simp_rw [← Real.norm_eq_abs]
    exact @measurableSet_lt _ _ _ _ _ m _ _ _ _ _ measurable_const
      stronglyMeasurable_condExp.norm.measurable
  simp only [← smul_eq_mul, ← setIntegral_const]
  refine setIntegral_mono_ae hfint.abs.integrableOn ?_ hbdd
  refine ⟨aestronglyMeasurable_const, lt_of_le_of_lt ?_
    (integrable_condExp.integrableOn : IntegrableOn (μ[f|m]) {x | ↑R < |(μ[f|m]) x|} μ).2⟩
  refine setLIntegral_mono
    (stronglyMeasurable_condExp.mono hnm).measurable.nnnorm.coe_nnreal_ennreal fun x hx => ?_
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, Real.nnnorm_of_nonneg R.coe_nonneg]
  exact Subtype.mk_le_mk.2 (le_of_lt hx)

/-- If the pairs `(Y, Z)` and `(Y', Z)` have the same law, then for measurable `B` the conditional
expectations of `𝟙_B ∘ Y` and `𝟙_B ∘ Y'` given `σ(Z)` agree almost everywhere. -/
theorem condExp_indicator_eq_of_pair_law_eq {Ω α β : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace α] [mβ : MeasurableSpace β] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Y Y' : Ω → α) (Z : Ω → β) (hY : Measurable Y) (hY' : Measurable Y') (hZ : Measurable Z)
    (hpair : μ.map (fun ω => (Y ω, Z ω)) = μ.map (fun ω => (Y' ω, Z ω)))
    {B : Set α} (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ Y | MeasurableSpace.comap Z mβ]
      =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ Y' | MeasurableSpace.comap Z mβ] := by
  classical
  set f := Set.indicator B (fun _ => (1 : ℝ)) ∘ Y with hf_def
  set f' := Set.indicator B (fun _ => (1 : ℝ)) ∘ Y' with hf'_def
  set mZ := MeasurableSpace.comap Z mβ with hmZ_def
  have hmZ_le : mZ ≤ mΩ := by
    rintro s ⟨E, hE, rfl⟩
    exact hZ hE
  have hf_int : Integrable f μ := Integrable.indicator (integrable_const (1 : ℝ)) (hY hB)
  have hf'_int : Integrable f' μ := Integrable.indicator (integrable_const (1 : ℝ)) (hY' hB)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmZ_le hf_int
    (fun s _ _ => integrable_condExp.integrableOn) (fun A hA _ => ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  obtain ⟨E, hE, rfl⟩ := hA
  have h_meas_eq : μ (Y ⁻¹' B ∩ Z ⁻¹' E) = μ (Y' ⁻¹' B ∩ Z ⁻¹' E) := by
    have h := congr_arg (fun ν => ν (B ×ˢ E)) hpair
    simp only [Measure.map_apply (hY.prodMk hZ) (hB.prod hE),
      Measure.map_apply (hY'.prodMk hZ) (hB.prod hE), Set.mk_preimage_prod] at h
    exact h
  -- The set-integral of a preimage indicator over `Z ⁻¹' E`, shared by both coordinates.
  have hint : ∀ W : Ω → α, Measurable[mΩ] W →
      ∫ ω in Z ⁻¹' E, (W ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω ∂μ
        = (μ (W ⁻¹' B ∩ Z ⁻¹' E)).toReal := by
    intro W hW
    rw [setIntegral_indicator (hW hB), setIntegral_const, Set.inter_comm]
    simp [Measure.real]
  have h_lhs : ∫ ω in Z ⁻¹' E, f ω ∂μ = (μ (Y ⁻¹' B ∩ Z ⁻¹' E)).toReal := by
    have hf_eq : f = (Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
      ext ω; simp only [hf_def, Function.comp_apply, Set.indicator, Set.mem_preimage]
    rw [hf_eq]; exact hint Y hY
  have h_rhs_ce : ∫ ω in Z ⁻¹' E, μ[f' | mZ] ω ∂μ = ∫ ω in Z ⁻¹' E, f' ω ∂μ :=
    setIntegral_condExp hmZ_le hf'_int ⟨E, hE, rfl⟩
  have h_rhs : ∫ ω in Z ⁻¹' E, f' ω ∂μ = (μ (Y' ⁻¹' B ∩ Z ⁻¹' E)).toReal := by
    have hf'_eq : f' = (Y' ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
      ext ω; simp only [hf'_def, Function.comp_apply, Set.indicator, Set.mem_preimage]
    rw [hf'_eq]; exact hint Y' hY'
  simp_rw [h_lhs, h_rhs_ce, h_rhs, h_meas_eq]

/-- **L¹-continuity of conditional expectation.** If `Xn → Xlim` in `L¹` (in `eLpNorm`) and each
`μ[Xn n | F]` agrees a.e. with a fixed `Y`, then `μ[Xlim | F]` agrees a.e. with `Y`. -/
-- Stated for an arbitrary conditioning σ-algebra `F` (no `F ≤ m₀`, no `[SigmaFinite (μ.trim)]`):
-- the bound goes through the L¹ contraction for conditional expectation, which holds at
-- every `F` via the `condExp = 0` convention — whereas `condExpL1CLM` would require both. Proof:
-- bound `‖μ[Xlim|F] - Y‖₁` by `‖Xlim - Xn n‖₁` (triangle + `condExp_sub` + the contraction + the
-- vanishing `μ[Xn n|F] - Y` term), then let `n → ∞`. Consumed by the reverse-martingale
-- Lévy-downward theorem `MeasureTheory.tendsto_ae_condExp_iInf`.
lemma condExp_ae_eq_of_forall_condExp_ae_eq_of_tendsto_eLpNorm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : MeasurableSpace Ω} {Xlim Y : Ω → ℝ} {Xn : ℕ → Ω → ℝ}
    (hXlimint : Integrable Xlim μ) (hXn_int : ∀ n, Integrable (Xn n) μ)
    (h_condExp : ∀ n, μ[Xn n | F] =ᵐ[μ] Y)
    (hL1 : Tendsto (fun n => eLpNorm (Xlim - Xn n) 1 μ) atTop (𝓝 0)) :
    μ[Xlim | F] =ᵐ[μ] Y := by
  have hY_meas := integrable_condExp.aestronglyMeasurable.congr (h_condExp 0)
  have h_bound (n : ℕ) : eLpNorm (μ[Xlim | F] - Y) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := by
    have htri : eLpNorm (μ[Xlim | F] - Y) 1 μ
                ≤ eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ
                  + eLpNorm (μ[Xn n | F] - Y) 1 μ := by
      have : μ[Xlim | F] - Y = (μ[Xlim | F] - μ[Xn n | F]) + (μ[Xn n | F] - Y) := by ring
      rw [this]
      refine eLpNorm_add_le ?_ ?_ ?_
      · exact (integrable_condExp.sub integrable_condExp).aestronglyMeasurable
      · exact integrable_condExp.aestronglyMeasurable.sub hY_meas
      · norm_num
    have hzero : eLpNorm (μ[Xn n | F] - Y) 1 μ = 0 := by
      have h0 : μ[Xn n | F] - Y =ᵐ[μ] 0 := by
        filter_upwards [h_condExp n] with ω hω; simp [hω]
      rw [eLpNorm_congr_ae h0]; simp
    have hfirst : eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := by
      have hsub : μ[Xlim | F] - μ[Xn n | F] =ᵐ[μ] μ[Xlim - Xn n | F] :=
        (condExp_sub hXlimint (hXn_int n) F).symm
      rw [eLpNorm_congr_ae hsub]
      exact eLpNorm_condExp_le_eLpNorm_real _
    calc eLpNorm (μ[Xlim | F] - Y) 1 μ
        ≤ eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ + eLpNorm (μ[Xn n | F] - Y) 1 μ := htri
      _ = eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ := by rw [hzero]; ring
      _ ≤ eLpNorm (Xlim - Xn n) 1 μ := hfirst
  have h_norm_zero : eLpNorm (μ[Xlim | F] - Y) 1 μ = 0 :=
    le_antisymm
      (le_of_tendsto_of_tendsto tendsto_const_nhds hL1 (Eventually.of_forall h_bound)) bot_le
  rw [eLpNorm_eq_zero_iff (integrable_condExp.aestronglyMeasurable.sub hY_meas)
    one_ne_zero] at h_norm_zero
  filter_upwards [h_norm_zero] with ω hω
  simp only [Pi.zero_apply] at hω
  exact sub_eq_zero.mp hω

end MeasureTheory

end TauCeti
