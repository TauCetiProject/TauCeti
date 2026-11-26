/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import TauCeti.MeasureTheory.Measure.Real

/-!
# Entropy of a finite label

For a measure `μ` on `Ω` and a label `X : Ω → A` into a finite type, the label entropy is
`labelEntropy μ X = ∑ a, negMulLog (μ.real (X ⁻¹' {a}))`, with natural logarithms; values of
mass zero contribute zero. For a second label `Y : Ω → B`, the conditional entropy is
`condLabelEntropy μ X Y = ∑ a, ∑ b, p_ab * log (p_b / p_ab)`, where
`p_ab = μ.real (X ⁻¹' {a} ∩ Y ⁻¹' {b})` and `p_b = μ.real (Y ⁻¹' {b})`. Cells of mass zero
contribute zero through Mathlib's conventions `0 * x = 0` and `log 0 = 0`. No hypothesis on the
measurable structure of `Ω` (standard Borel, countably generated) is needed.

## Main results

* `TauCeti.labelEntropy_pair_eq_add`: the chain rule `H((X, Y)) = H(Y) + H(X | Y)` for the joint
  label `ω ↦ (X ω, Y ω)`, for a finite measure and a measurable `X`.
* `TauCeti.labelEntropy_nonneg_le_log_card`: for a probability measure and a measurable `X`,
  `0 ≤ H(X) ≤ log |A|`.
* `TauCeti.labelEntropy_pair_of_indepFun`: independent labels have additive entropy.
* `TauCeti.labelEntropy_comp_of_injective`: relabeling by an injection, in particular enlarging
  the alphabet by unused values, leaves the entropy unchanged.
* `TauCeti.condLabelEntropy_self`: a label conditioned on itself has entropy zero.

## References

* T. Tao, The logarithmically averaged Chowla and Elliott conjectures for two-point
  correlations, Forum Math. Pi 4 (2016), arXiv:1509.05422, §3, (3.1)–(3.5).
-/

public section

open MeasureTheory ProbabilityTheory Real

namespace TauCeti

variable {Ω A B C : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

section Definitions

variable [Fintype A] [Fintype B]

/-- The Shannon entropy, in natural units, of a label `X : Ω → A` into a finite type under the
measure `μ`: the sum of `negMulLog` of the masses of the fibres of `X`. -/
noncomputable def labelEntropy (μ : Measure Ω) (X : Ω → A) : ℝ :=
  ∑ a, negMulLog (μ.real (X ⁻¹' {a}))

/-- The conditional entropy of the label `X` given the label `Y`: the sum over the cells
`X ⁻¹' {a} ∩ Y ⁻¹' {b}` of `p_ab * log (p_b / p_ab)`, where `p_ab` is the mass of the cell and
`p_b` the mass of `Y ⁻¹' {b}`. Cells of mass zero contribute zero. -/
noncomputable def condLabelEntropy (μ : Measure Ω) (X : Ω → A) (Y : Ω → B) : ℝ :=
  ∑ a, ∑ b, μ.real (X ⁻¹' {a} ∩ Y ⁻¹' {b}) *
    log (μ.real (Y ⁻¹' {b}) / μ.real (X ⁻¹' {a} ∩ Y ⁻¹' {b}))

theorem labelEntropy_def (μ : Measure Ω) (X : Ω → A) :
    labelEntropy μ X = ∑ a, negMulLog (μ.real (X ⁻¹' {a})) :=
  (rfl)

theorem condLabelEntropy_def (μ : Measure Ω) (X : Ω → A) (Y : Ω → B) :
    condLabelEntropy μ X Y = ∑ a, ∑ b, μ.real (X ⁻¹' {a} ∩ Y ⁻¹' {b}) *
      log (μ.real (Y ⁻¹' {b}) / μ.real (X ⁻¹' {a} ∩ Y ⁻¹' {b})) :=
  (rfl)

end Definitions

section Basic

variable [Fintype A] [Fintype B]

/-- A constant label has entropy zero under a probability measure (or the zero measure). -/
@[simp]
theorem labelEntropy_const [IsZeroOrProbabilityMeasure μ] (a₀ : A) :
    labelEntropy μ (fun _ : Ω ↦ a₀) = 0 := by
  classical
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  by_cases h : a₀ = a
  · obtain rfl | _ := eq_zero_or_isProbabilityMeasure (μ := μ) <;> simp [h]
  · simp [Set.preimage_const_of_notMem (Set.notMem_singleton_iff.mpr h)]

/-- Under the zero measure every label has entropy zero. -/
@[simp]
theorem labelEntropy_zero_measure (X : Ω → A) : labelEntropy (0 : Measure Ω) X = 0 := by
  simp [labelEntropy]

/-- Under a probability measure or the zero measure, the label entropy is nonnegative. -/
theorem labelEntropy_nonneg [IsZeroOrProbabilityMeasure μ] (X : Ω → A) :
    0 ≤ labelEntropy μ X :=
  Finset.sum_nonneg fun _ _ ↦ negMulLog_nonneg measureReal_nonneg measureReal_le_one

/-- Relabeling by an injection does not change the entropy. In particular, enlarging the
alphabet by values that the label does not take leaves the entropy unchanged. -/
theorem labelEntropy_comp_of_injective [Fintype C] (X : Ω → A) {e : A → C}
    (he : Function.Injective e) : labelEntropy μ (e ∘ X) = labelEntropy μ X := by
  classical
  unfold labelEntropy
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨e, he⟩)) fun c _ hc ↦ ?_,
    Finset.sum_map]
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [Function.Embedding.coeFn_mk, Set.preimage_comp]
    rw [show e ⁻¹' {e a} = {a} from Set.ext fun _ ↦ he.eq_iff]
  · have : (e ∘ X) ⁻¹' {c} = ∅ := Set.eq_empty_of_forall_notMem fun ω hω ↦
      hc (Finset.mem_map.mpr ⟨X ω, Finset.mem_univ _, hω⟩)
    simp [this]

/-- The entropy of the joint label is the double sum over cells. -/
theorem labelEntropy_pair (μ : Measure Ω) (X : Ω → A) (Y : Ω → B) :
    labelEntropy μ (fun ω ↦ (X ω, Y ω)) =
      ∑ a, ∑ b, negMulLog (μ.real (X ⁻¹' {a} ∩ Y ⁻¹' {b})) := by
  simp only [labelEntropy, ← Set.singleton_prod_singleton, Set.mk_preimage_prod,
    Fintype.sum_prod_type]

/-- A label joined with itself has the same entropy: `H((X, X)) = H(X)`. -/
@[simp]
theorem labelEntropy_pair_self (μ : Measure Ω) (X : Ω → A) :
    labelEntropy μ (fun ω ↦ (X ω, X ω)) = labelEntropy μ X :=
  labelEntropy_comp_of_injective (e := fun a ↦ (a, a)) X fun _ _ h ↦ (Prod.mk.inj h).1

/-- A label conditioned on itself has conditional entropy zero. -/
@[simp]
theorem condLabelEntropy_self (μ : Measure Ω) (X : Ω → A) : condLabelEntropy μ X X = 0 := by
  classical
  refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ ?_
  by_cases h : a = b
  · subst h
    simp only [Set.inter_self]
    rcases eq_or_ne (μ.real (X ⁻¹' {a})) 0 with h0 | h0
    · simp [h0]
    · simp [div_self h0]
  · simp [((Set.disjoint_singleton.mpr h).preimage X).inter_eq]

/-- Under the zero measure every conditional entropy is zero. -/
@[simp]
theorem condLabelEntropy_zero_measure (X : Ω → A) (Y : Ω → B) :
    condLabelEntropy (0 : Measure Ω) X Y = 0 := by
  simp [condLabelEntropy]

/-- A cell term `μ.real (s ∩ t) * log (μ.real t / μ.real (s ∩ t))` of a conditional entropy is
nonnegative, for every measure: if `t` has finite mass then `μ.real (s ∩ t) ≤ μ.real t`, and
otherwise `μ.real t = 0` and the term vanishes through `log 0 = 0`. -/
theorem measureReal_inter_mul_log_div_nonneg (μ : Measure Ω) (s t : Set Ω) :
    0 ≤ μ.real (s ∩ t) * log (μ.real t / μ.real (s ∩ t)) := by
  rcases eq_or_ne (μ t) ⊤ with h | h
  · simp [measureReal_def, h]
  rcases (measureReal_nonneg (μ := μ) (s := s ∩ t)).eq_or_lt with h0 | h0
  · simp [← h0]
  exact mul_nonneg h0.le
    (log_nonneg ((one_le_div h0).mpr (measureReal_mono Set.inter_subset_right h)))

/-- The conditional entropy is nonnegative, for every measure. -/
theorem condLabelEntropy_nonneg (μ : Measure Ω) (X : Ω → A) (Y : Ω → B) :
    0 ≤ condLabelEntropy μ X Y :=
  Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun b _ ↦
    measureReal_inter_mul_log_div_nonneg μ (X ⁻¹' {a}) (Y ⁻¹' {b})

end Basic

section Additivity

variable [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- **Chain rule.** For a finite measure and a measurable label `X`, the entropy of the joint
label is `H((X, Y)) = H(Y) + H(X | Y)`. -/
theorem labelEntropy_pair_eq_add [IsFiniteMeasure μ] {X : Ω → A} (hX : Measurable X)
    (Y : Ω → B) :
    labelEntropy μ (fun ω ↦ (X ω, Y ω)) = labelEntropy μ Y + condLabelEntropy μ X Y := by
  have hcell : ∀ a b, negMulLog (μ.real (X ⁻¹' {a} ∩ Y ⁻¹' {b})) =
      μ.real (X ⁻¹' {a} ∩ Y ⁻¹' {b}) * -log (μ.real (Y ⁻¹' {b})) +
        μ.real (X ⁻¹' {a} ∩ Y ⁻¹' {b}) *
          log (μ.real (Y ⁻¹' {b}) / μ.real (X ⁻¹' {a} ∩ Y ⁻¹' {b})) := fun a b ↦ by
    set p := μ.real (X ⁻¹' {a} ∩ Y ⁻¹' {b})
    set q := μ.real (Y ⁻¹' {b})
    rcases eq_or_ne p 0 with hp | hp
    · simp [hp]
    have hq : q ≠ 0 := by
      refine ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne measureReal_nonneg (Ne.symm hp)) ?_)
      exact measureReal_mono Set.inter_subset_right
    rw [log_div hq hp, negMulLog]
    ring
  rw [labelEntropy_pair]
  simp only [hcell, Finset.sum_add_distrib]
  rw [labelEntropy_def, condLabelEntropy_def]
  congr 1
  -- Summing the cells over `a` recovers the mass of `Y ⁻¹' {b}`.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [← Finset.sum_mul,
    sum_measureReal_preimage_singleton_inter (hX <| measurableSet_singleton ·) (Y ⁻¹' {b}),
    negMulLog]
  ring

/-- **Alphabet bound.** For a probability measure and a measurable label,
`0 ≤ H(X) ≤ log |A|`. -/
theorem labelEntropy_nonneg_le_log_card [IsProbabilityMeasure μ] {X : Ω → A}
    (hX : Measurable X) :
    0 ≤ labelEntropy μ X ∧ labelEntropy μ X ≤ log (Fintype.card A) := by
  refine ⟨labelEntropy_nonneg X, ?_⟩
  rcases isEmpty_or_nonempty A with hA | hA
  · simp [labelEntropy]
  have hn : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hJ := concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun _ : A ↦ (Fintype.card A : ℝ)⁻¹) (p := fun a ↦ μ.real (X ⁻¹' {a}))
    (fun _ _ ↦ inv_nonneg.mpr hn.le) (by simp [Finset.card_univ, hn.ne'])
    (fun _ _ ↦ Set.mem_Ici.mpr measureReal_nonneg)
  simp only [smul_eq_mul, ← Finset.mul_sum,
    sum_measureReal_preimage_singleton_eq_one (hX <| measurableSet_singleton ·), mul_one] at hJ
  rw [negMulLog, log_inv, neg_mul_neg] at hJ
  exact le_of_mul_le_mul_left hJ (inv_pos.mpr hn)

/-- **Independence.** If the measurable labels `X` and `Y` are independent under a probability
measure, the entropy of the joint label is `H((X, Y)) = H(X) + H(Y)`. -/
theorem labelEntropy_pair_of_indepFun [IsProbabilityMeasure μ] [MeasurableSpace B]
    [MeasurableSingletonClass B] {X : Ω → A} {Y : Ω → B} (hX : Measurable X)
    (hY : Measurable Y) (hXY : IndepFun X Y μ) :
    labelEntropy μ (fun ω ↦ (X ω, Y ω)) = labelEntropy μ X + labelEntropy μ Y := by
  have hcell : ∀ a b, μ.real (X ⁻¹' {a} ∩ Y ⁻¹' {b}) =
      μ.real (X ⁻¹' {a}) * μ.real (Y ⁻¹' {b}) := fun a b ↦ by
    simp only [measureReal_def, hXY.measure_inter_preimage_eq_mul _ _
      (measurableSet_singleton a) (measurableSet_singleton b), ENNReal.toReal_mul]
  rw [labelEntropy_pair, labelEntropy_def, labelEntropy_def]
  simp only [hcell, negMulLog_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    sum_measureReal_preimage_singleton_eq_one (hX <| measurableSet_singleton ·),
    sum_measureReal_preimage_singleton_eq_one (hY <| measurableSet_singleton ·),
    one_mul]

end Additivity

end TauCeti
