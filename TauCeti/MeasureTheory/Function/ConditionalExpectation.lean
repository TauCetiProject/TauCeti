/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
-- Non-public: `eLpNorm_condExp_le_eLpNorm` (the Lᵖ contraction of conditional expectation) is
-- used only inside the proof of the L¹-continuity lemma below, not in any public signature.
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Generic conditional-expectation facts

- `condExp_comp_ae_eq_of_pair_law_eq`: if `(Y, Z)` and `(Y', Z)` have the same law, then for a
  measurable real observable `f` the conditional expectations of `f ∘ Y` and `f ∘ Y'` given `σ(Z)`
  agree a.e.
- `condExp_ae_eq_of_forall_condExp_ae_eq_of_tendsto_eLpNorm`: L¹-continuity of conditional
  expectation — if `Xn → Xlim` in L¹ (in `eLpNorm`) and each `μ[Xn n | F]` agrees a.e. with a fixed
  `Y`, then `μ[Xlim | F]` agrees a.e. with `Y`.
- `condExp_ae_eq_integral_of_forall_zero_or_one`: conditioning on a `μ`-trivial σ-algebra — one
  all of whose sets have measure `0` or `1` — is integrating: `μ[f | m']` is a.e. the constant
  `∫ f ∂μ`.
- `ae_eq_condExp_of_forall_setIntegral_fiber_eq`: conditional-expectation uniqueness can be
  checked on the fibers of a countable-valued observation.
- `condExp_ae_eq_of_le_of_le`: if conditioning on a σ-algebra agrees a.e. with conditioning on a
  coarser one, then so does conditioning on every σ-algebra between them.

All are generic conditional-expectation facts (no exchangeability/tail/directing-measure
hypotheses), each the bridge for a downstream construction.

The first two are adapted from `cameronfreer/exchangeability` (`Probability/CondExp.lean` and
`Probability/Martingale/Convergence.lean`, pin `e0532e59ceff23edab44dda9ab0655debbc9cc22`); the
third from `Graphon/LevyDownward.lean` in `cameronfreer/graphon` (Apache 2.0) at commit
`175911f9d2e053f2a33d966658dfce0e4ae2811d`.
-/

public section

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace TauCeti

namespace MeasureTheory

/-- If the pairs `(Y, Z)` and `(Y', Z)` have the same law, then for a measurable real observable
`f` the conditional expectations of `f ∘ Y` and `f ∘ Y'` given `σ(Z)` agree almost everywhere.

Both conditional expectations are pinned down by their integrals over the sets `Z ⁻¹' E`, and each
such integral is an integral of `fun p => f p.1` over the slab `univ ×ˢ E` against the joint law,
which is where the hypothesis applies. Equal laws make `f ∘ Y` integrable exactly when `f ∘ Y'` is,
so no integrability hypothesis is needed: when it fails both sides are `0`. -/
theorem condExp_comp_ae_eq_of_pair_law_eq {Ω α β : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace α] [mβ : MeasurableSpace β] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Y Y' : Ω → α) (Z : Ω → β) (hY : Measurable Y) (hY' : Measurable Y') (hZ : Measurable Z)
    (hpair : μ.map (fun ω => (Y ω, Z ω)) = μ.map (fun ω => (Y' ω, Z ω)))
    {f : α → ℝ} (hf : Measurable f) :
    μ[fun ω => f (Y ω) | MeasurableSpace.comap Z mβ]
      =ᵐ[μ] μ[fun ω => f (Y' ω) | MeasurableSpace.comap Z mβ] := by
  have hmZ_le : MeasurableSpace.comap Z mβ ≤ mΩ := by
    rintro s ⟨E, hE, rfl⟩
    exact hZ hE
  -- Equal joint laws have equal first marginals, so integrability transfers to `Y'`.
  have hmap : μ.map Y = μ.map Y' := by
    have h := congrArg (Measure.map Prod.fst) hpair
    rwa [Measure.map_map measurable_fst (hY.prodMk hZ),
      Measure.map_map measurable_fst (hY'.prodMk hZ)] at h
  have hiff : Integrable (fun ω => f (Y ω)) μ ↔ Integrable (fun ω => f (Y' ω)) μ := by
    have h : Integrable f (μ.map Y) ↔ Integrable (fun ω => f (Y ω)) μ :=
      integrable_map_measure hf.aestronglyMeasurable hY.aemeasurable
    have h' : Integrable f (μ.map Y') ↔ Integrable (fun ω => f (Y' ω)) μ :=
      integrable_map_measure hf.aestronglyMeasurable hY'.aemeasurable
    rw [hmap] at h
    exact h.symm.trans h'
  by_cases hf_int : Integrable (fun ω => f (Y ω)) μ
  case neg =>
    -- Neither composite is integrable, so both conditional expectations are `0`.
    rw [condExp_of_not_integrable hf_int, condExp_of_not_integrable (mt hiff.2 hf_int)]
  have hf'_int : Integrable (fun ω => f (Y' ω)) μ := hiff.1 hf_int
  have hslice : ∀ W : Ω → α, Measurable W → ∀ {E : Set β}, MeasurableSet E →
      ∫ p in Set.univ ×ˢ E, f p.1 ∂(μ.map fun ω => (W ω, Z ω))
        = ∫ ω in Z ⁻¹' E, f (W ω) ∂μ := by
    intro W hW E hE
    have hfst : Measurable fun p : α × β => f p.1 := hf.comp measurable_fst
    rw [setIntegral_map (MeasurableSet.univ.prod hE) hfst.aestronglyMeasurable
      (hW.prodMk hZ).aemeasurable]
    have hpre : (fun ω => (W ω, Z ω)) ⁻¹' (Set.univ ×ˢ E) = Z ⁻¹' E := by
      ext ω; simp
    rw [hpre]
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmZ_le hf_int
    (fun s _ _ => integrable_condExp.integrableOn) (fun A hA _ => ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  obtain ⟨E, hE, rfl⟩ := hA
  rw [setIntegral_condExp hmZ_le hf'_int ⟨E, hE, rfl⟩, ← hslice Y' hY' hE, ← hpair,
    hslice Y hY hE]

/-- **L¹-continuity of conditional expectation.** If `Xn → Xlim` in `L¹` (in `eLpNorm`) and each
`μ[Xn n | F]` agrees a.e. with a fixed `Y`, then `μ[Xlim | F]` agrees a.e. with `Y`. -/
-- Stated for an arbitrary conditioning σ-algebra `F` (no `F ≤ m₀`, no `[SigmaFinite (μ.trim)]`):
-- the bound goes through Mathlib's Lᵖ contraction `eLpNorm_condExp_le_eLpNorm`, which holds at
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
  have h_bound (n : ℕ) : eLpNorm (μ[Xlim | F] - Y) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := by
    have htri : eLpNorm (μ[Xlim | F] - Y) 1 μ
                ≤ eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ
                  + eLpNorm (μ[Xn n | F] - Y) 1 μ := by
      have : μ[Xlim | F] - Y = (μ[Xlim | F] - μ[Xn n | F]) + (μ[Xn n | F] - Y) := by ring
      rw [this]
      exact eLpNorm_add_le le_rfl
    have hzero : eLpNorm (μ[Xn n | F] - Y) 1 μ = 0 := by
      have h0 : μ[Xn n | F] - Y =ᵐ[μ] 0 := by
        filter_upwards [h_condExp n] with ω hω; simp [hω]
      rw [eLpNorm_congr_ae h0]; simp
    have hfirst : eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := by
      have hsub : μ[Xlim | F] - μ[Xn n | F] =ᵐ[μ] μ[Xlim - Xn n | F] :=
        (condExp_sub hXlimint (hXn_int n) F).symm
      rw [eLpNorm_congr_ae hsub]
      exact eLpNorm_condExp_le_eLpNorm _ le_rfl
    calc eLpNorm (μ[Xlim | F] - Y) 1 μ
        ≤ eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ + eLpNorm (μ[Xn n | F] - Y) 1 μ := htri
      _ = eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ := by rw [hzero]; ring
      _ ≤ eLpNorm (Xlim - Xn n) 1 μ := hfirst
  have h_norm_zero : eLpNorm (μ[Xlim | F] - Y) 1 μ = 0 :=
    le_antisymm
      (le_of_tendsto_of_tendsto tendsto_const_nhds hL1 (Eventually.of_forall h_bound)) bot_le
  rw [eLpNorm_eq_zero_iff one_ne_zero] at h_norm_zero
  filter_upwards [h_norm_zero] with ω hω
  simp only [Pi.zero_apply] at hω
  exact sub_eq_zero.mp hω

/-- Conditioning on a `μ`-trivial σ-algebra is integrating: if every `m'`-measurable set has
measure `0` or `1`, then `μ[f | m']` is a.e. the constant `∫ f ∂μ`. -/
theorem condExp_ae_eq_integral_of_forall_zero_or_one {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} {m' : MeasurableSpace Ω} (hm' : m' ≤ m0)
    (htriv : ∀ s, MeasurableSet[m'] s → μ s = 0 ∨ μ s = 1) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : Ω → E} (hf : Integrable f μ) :
    μ[f | m'] =ᵐ[μ] fun _ => ∫ x, f x ∂μ := by
  have : IsZeroOrProbabilityMeasure μ := ⟨htriv Set.univ MeasurableSet.univ⟩
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | _
  · simp [Filter.EventuallyEq, ae_zero]
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm' hf
    (fun s _ _ => integrableOn_const) ?_
    stronglyMeasurable_const.aestronglyMeasurable).symm
  intro s hs _
  rcases htriv s hs with h0 | h1
  · rw [setIntegral_measure_zero _ h0, setIntegral_measure_zero _ h0]
  · have hcompl : μ sᶜ = 0 := by
      have := measure_compl (hm' s hs) (measure_ne_top μ s)
      rw [h1] at this
      simpa using this
    have hs_int : ∫ x in s, f x ∂μ = ∫ x, f x ∂μ := by
      rw [← integral_add_compl (hm' s hs) hf, setIntegral_measure_zero _ hcompl, add_zero]
    rw [hs_int, setIntegral_const]
    have hsr : μ.real s = 1 := by
      rw [Measure.real, h1, ENNReal.toReal_one]
    rw [hsr, one_smul]

/-- To identify a conditional expectation given a countable-valued observation, it suffices to
compare integrals on its fibers. The candidate must be integrable and measurable with respect to
the observation's σ-algebra. -/
theorem ae_eq_condExp_of_forall_setIntegral_fiber_eq
    {Ω ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {μ : Measure Ω} {X : Ω → ι} (hX : Measurable X)
    [SigmaFinite (μ.trim hX.comap_le)] {f g : Ω → E}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hgm : AEStronglyMeasurable[MeasurableSpace.comap X ‹MeasurableSpace ι›] g μ)
    (hfg : ∀ i, ∫ x in X ⁻¹' {i}, g x ∂μ = ∫ x in X ⁻¹' {i}, f x ∂μ) :
    g =ᵐ[μ] μ[f | MeasurableSpace.comap X ‹MeasurableSpace ι›] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hf
    (fun _ _ _ => hg.integrableOn) ?_ hgm
  rintro _ ⟨s, _, rfl⟩ _
  have hs : X ⁻¹' s = ⋃ i : s, X ⁻¹' {i.val} := by
    ext x
    simp
  have hmeas (i : s) : MeasurableSet (X ⁻¹' {i.val}) := hX (measurableSet_singleton _)
  have hdisj : Pairwise (Function.onFun Disjoint fun i : s => X ⁻¹' {i.val}) :=
    (pairwise_disjoint_fiber X).comp_of_injective Subtype.val_injective
  rw [hs, integral_iUnion hmeas hdisj hg.integrableOn,
    integral_iUnion hmeas hdisj hf.integrableOn]
  exact tsum_congr fun i => hfg i.val

/-- **Conditioning on an intermediate σ-algebra.** If conditioning `f` on `m₃` gives a.e. the same
result as conditioning on the coarser `m₁ ≤ m₃`, then so does conditioning on any `m₂` between
them. -/
theorem condExp_ae_eq_of_le_of_le {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {m₁ m₂ m₃ m₀ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → E}
    (h₁₂ : m₁ ≤ m₂) (h₂₃ : m₂ ≤ m₃) (h₃ : m₃ ≤ m₀) [SigmaFinite (μ.trim h₃)]
    [SigmaFinite (μ.trim (h₂₃.trans h₃))] (h : μ[f | m₃] =ᵐ[μ] μ[f | m₁]) :
    μ[f | m₂] =ᵐ[μ] μ[f | m₁] := calc
  μ[f | m₂] =ᵐ[μ] μ[μ[f | m₃] | m₂] := (condExp_condExp_of_le h₂₃ h₃).symm
  _ =ᵐ[μ] μ[μ[f | m₁] | m₂] := condExp_congr_ae h
  _ = μ[f | m₁] := condExp_of_stronglyMeasurable (h₂₃.trans h₃)
    (stronglyMeasurable_condExp.mono h₁₂) integrable_condExp

end MeasureTheory

end TauCeti
