/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan Braams, Claude
-/
module

public import TauCeti.Probability.Kernel.GroupAverage
public import TauCeti.Statistics.Decision.Criteria

/-!
# Equivariant rules in invariant decision problems

A finite group `G` acts on the parameter set `Θ`, the sample space `X` and the action space `A`,
measurably on `X` and `A`. The decision problem is *invariant* if `P (g • θ)` is the image of
`P θ` under `g • ·` and the loss satisfies `L (g • θ) (g • a) = L θ a`. A randomized rule `κ` is
*equivariant* if `κ (g • x) = (κ x).map (g • ·)`.

Averaging a rule over the group (`ProbabilityTheory.Kernel.groupAverage`) gives an equivariant
rule whose risk at `θ` is the average of the risks of the original rule over the orbit of `θ`.
Since an average is at most a supremum, a minimax rule yields an equivariant minimax rule.

## Main results

* `TauCeti.exists_equivariant_rule_risk_eq_average`: every randomized rule with integrable loss
  has an equivariant rule whose risk at `θ` is the average of its risks at `g • θ`.
* `TauCeti.IsMinimaxRule.exists_equivariant`: if a minimax randomized rule with integrable loss
  exists, an equivariant minimax rule exists.

The averaging theorem is adapted from `CKSD.exists_equivariant_rule_risk_eq_average` in
lean-CKSD, `CKSD/Inference/Decision.lean`.

## References

* T. S. Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*, Academic Press
  (1967), §4.3, Theorems 4.3.1 and 4.3.2.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

variable {Θ G X A : Type*} [Group G] [MeasurableSpace X] [MeasurableSpace A]
  [MulAction G Θ] [MulAction G X] [MulAction G A]

/-- **Averaging over a finite group.** In an invariant decision problem, every randomized rule
`κ` whose loss is integrable at every parameter has an equivariant randomized rule whose risk at
`θ` is the average of the risks of `κ` at the points `g • θ` of the orbit of `θ`. -/
theorem exists_equivariant_rule_risk_eq_average [Fintype G]
    (hX : ∀ g : G, Measurable fun x : X ↦ g • x) (hA : ∀ g : G, Measurable fun a : A ↦ g • a)
    (P : Θ → Measure X) (hP : ∀ (g : G) θ, P (g • θ) = (P θ).map fun x ↦ g • x)
    (L : Θ → A → ℝ) (hLinv : ∀ (g : G) θ a, L (g • θ) (g • a) = L θ a)
    (κ : Kernel X A) [IsMarkovKernel κ] (hL : ∀ θ, Integrable (L θ) (κ ∘ₘ P θ)) :
    ∃ κ' : Kernel X A, IsMarkovKernel κ' ∧
      (∀ (g : G) x, κ' (g • x) = (κ' x).map fun a ↦ g • a) ∧
      ∀ θ, risk P L κ' θ = (Fintype.card G : ℝ)⁻¹ * ∑ g : G, risk P L κ (g • θ) := by
  have : MeasurableConstSMul G X := ⟨hX⟩
  have : MeasurableConstSMul G A := ⟨hA⟩
  refine ⟨Kernel.groupAverage G κ, inferInstance, Kernel.groupAverage_smul_apply G κ,
    fun θ ↦ ?_⟩
  -- the loss at `θ` of the action `g • a` is the loss at `g⁻¹ • θ` of `a`
  have hLg (g : G) (a : A) : L θ (g • a) = L (g⁻¹ • θ) a := by
    rw [← hLinv g (g⁻¹ • θ), smul_inv_smul]
  have hint (g : G) : Integrable (L θ) ((κ ∘ₘ P (g⁻¹ • θ)).map (g • ·)) := by
    rw [(measurableEmbedding_const_smul g).integrable_map_iff, Function.comp_def]
    simpa only [hLg] using hL (g⁻¹ • θ)
  have hterm (g : G) :
      ∫ a, L θ a ∂(κ ∘ₘ P (g⁻¹ • θ)).map (g • ·) = risk P L κ (g⁻¹ • θ) := by
    simp only [(measurableEmbedding_const_smul g).integral_map, hLg, risk_def]
  simp only [risk_def P L (Kernel.groupAverage G κ), Kernel.groupAverage_comp, ← hP]
  rw [integral_smul_measure, integral_finsetSum_measure fun g _ ↦ hint g]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, hterm]
  -- reindex the orbit sum by `g ↦ g⁻¹`
  exact congrArg _ (Equiv.sum_comp (Equiv.inv G) fun g ↦ risk P L κ (g • θ))

/-- **Equivariant minimax rules.** In an invariant decision problem, if a randomized rule `κ`
whose loss is integrable at every parameter is minimax among the randomized rules, then some
equivariant randomized rule is minimax among them as well. -/
theorem IsMinimaxRule.exists_equivariant [Finite G]
    (hX : ∀ g : G, Measurable fun x : X ↦ g • x) (hA : ∀ g : G, Measurable fun a : A ↦ g • a)
    {P : Θ → Measure X} (hP : ∀ (g : G) θ, P (g • θ) = (P θ).map fun x ↦ g • x)
    {L : Θ → A → ℝ} (hLinv : ∀ (g : G) θ a, L (g • θ) (g • a) = L θ a)
    {κ : {κ : Kernel X A // IsMarkovKernel κ}}
    (hκ : IsMinimaxRule (fun κ : {κ : Kernel X A // IsMarkovKernel κ} ↦ risk P L κ.val) κ)
    (hL : ∀ θ, Integrable (L θ) (κ.val ∘ₘ P θ)) :
    ∃ κ' : {κ : Kernel X A // IsMarkovKernel κ},
      (∀ (g : G) x, κ'.val (g • x) = (κ'.val x).map fun a ↦ g • a) ∧
      IsMinimaxRule (fun κ : {κ : Kernel X A // IsMarkovKernel κ} ↦ risk P L κ.val) κ' := by
  have := Fintype.ofFinite G
  have := κ.property
  obtain ⟨κ', hκ', hequiv, hrisk⟩ :=
    exists_equivariant_rule_risk_eq_average hX hA P hP L hLinv κ.val hL
  obtain ⟨M, hM⟩ := hκ.bddAbove
  -- the averaged risk is at most every upper bound of the risk of `κ`
  have hle {c : ℝ} (hc : ∀ θ, risk P L κ.val θ ≤ c) (θ : Θ) : risk P L κ' θ ≤ c := by
    rw [hrisk, inv_mul_le_iff₀ (by exact_mod_cast Fintype.card_pos)]
    simpa using Finset.sum_le_card_nsmul Finset.univ _ c fun g _ ↦ hc (g • θ)
  have hbdd : BddAbove (range (risk P L κ')) :=
    ⟨M, forall_mem_range.2 (hle fun θ ↦ hM (mem_range_self θ))⟩
  refine ⟨⟨κ', hκ'⟩, hequiv, hbdd, fun δ' hδ' ↦ ?_⟩
  refine le_trans ?_ (hκ.iSup_le δ' hδ')
  rcases isEmpty_or_nonempty Θ with hΘ | hΘ
  · simp
  · exact ciSup_le (hle fun θ ↦ le_ciSup hκ.bddAbove θ)

end TauCeti
