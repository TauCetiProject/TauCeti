/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import TauCeti.Analysis.SpecialFunctions.Log.MulLog
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Entropy of countable measurable partitions

A countable measurable partition of a measure space `X` is represented by a label `a : X → ι`
into a countable type; its atoms are the fibres `a ⁻¹' {i}`, empty atoms included, and the join
of two labels `a`, `b` is the pair label `x ↦ (a x, b x)`.

* `TauCeti.countablePartitionEntropy μ a` is the extended nonnegative sum of
  `-p_i log p_i = negMulLog p_i` over the atom masses `p_i = μ.real (a ⁻¹' {i})`, in natural
  units, with `0 log 0 = 0`. It may be infinite.
* `TauCeti.conditionalPartitionEntropy μ a b` is the extended sum of `p_ij * log (p_j / p_ij)`
  over the cells `a ⁻¹' {i} ∩ b ⁻¹' {j}`, where `p_j = μ.real (b ⁻¹' {j})`; cells of mass zero
  contribute zero.

## Main results

* `TauCeti.countablePartitionEntropy_pair_eq_add`: the chain rule
  `H(a ∨ b) = H(b) + H(a | b)` for a measurable countable label `a`, under a probability (or
  zero) measure.
* `TauCeti.conditionalPartitionEntropy_le`: conditioning on a measurable countable label does not
  increase entropy, `H(a | b) ≤ H(a)`, under a probability (or zero) measure.
* `TauCeti.countablePartitionEntropy_pair_le_add`: subadditivity `H(a ∨ b) ≤ H(a) + H(b)`, under
  a probability (or zero) measure.
* `TauCeti.countablePartitionEntropy_le_pair`, `TauCeti.countablePartitionEntropy_comp_le`:
  for every measure, refining a partition by a countable label does not decrease entropy and
  coarsening a countable label does not increase it.
* `TauCeti.countablePartitionEntropy_comp_of_measurePreserving`: pulling a label back along a
  measure-preserving map does not change its entropy.
* `TauCeti.countablePartitionEntropy_pair_of_indepFun`: independent labels have additive entropy.
* `TauCeti.countablePartitionEntropy_comp_of_injective`: relabeling by an injection, for instance
  embedding a countable alphabet into `ℕ`, does not change the entropy.
* `TauCeti.countablePartitionEntropy_eq_ofReal_sum`: on a finite alphabet, under a probability
  (or zero) measure, the entropy is the finite sum `∑ i, negMulLog p_i`.

## References

* G. A. Margulis and G. M. Tomanov, Invariant measures for actions of unipotent groups over local
  fields on homogeneous spaces, Invent. Math. 116 (1994), 347–392, §9.3, pp. 381–383,
  doi:10.1007/BF01231565.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace TauCeti

variable {X ι κ ι' : Type*} {mX : MeasurableSpace X} {μ : Measure X}

/-- The entropy of a measurable partition with countably many atoms, given by a label
`a : X → ι`: the extended sum of `negMulLog` of the atom masses. Atoms of mass zero contribute
zero, and the value may be `∞`. -/
noncomputable def countablePartitionEntropy (μ : Measure X) (a : X → ι) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (negMulLog (μ.real (a ⁻¹' {i})))

/-- The conditional entropy of the label `a` given the label `b`: the extended sum over the cells
`a ⁻¹' {i} ∩ b ⁻¹' {j}` of `p_ij * log (p_j / p_ij)`, where `p_ij` is the mass of the cell and
`p_j` the mass of `b ⁻¹' {j}`. Cells of mass zero contribute zero. -/
noncomputable def conditionalPartitionEntropy (μ : Measure X) (a : X → ι) (b : X → κ) : ℝ≥0∞ :=
  ∑' p : ι × κ, ENNReal.ofReal (μ.real (a ⁻¹' {p.1} ∩ b ⁻¹' {p.2}) *
    log (μ.real (b ⁻¹' {p.2}) / μ.real (a ⁻¹' {p.1} ∩ b ⁻¹' {p.2})))

theorem countablePartitionEntropy_def (μ : Measure X) (a : X → ι) :
    countablePartitionEntropy μ a = ∑' i, ENNReal.ofReal (negMulLog (μ.real (a ⁻¹' {i}))) :=
  (rfl)

theorem conditionalPartitionEntropy_def (μ : Measure X) (a : X → ι) (b : X → κ) :
    conditionalPartitionEntropy μ a b =
      ∑' p : ι × κ, ENNReal.ofReal (μ.real (a ⁻¹' {p.1} ∩ b ⁻¹' {p.2}) *
        log (μ.real (b ⁻¹' {p.2}) / μ.real (a ⁻¹' {p.1} ∩ b ⁻¹' {p.2}))) :=
  (rfl)

/-- The entropy of the pair label is the extended double sum over its cells. -/
theorem countablePartitionEntropy_pair (μ : Measure X) (a : X → ι) (b : X → κ) :
    countablePartitionEntropy μ (fun x ↦ (a x, b x)) =
      ∑' i, ∑' j, ENNReal.ofReal (negMulLog (μ.real (a ⁻¹' {i} ∩ b ⁻¹' {j}))) := by
  rw [countablePartitionEntropy_def, tsum_prod']
  simp only [← Set.singleton_prod_singleton, Set.mk_preimage_prod]

/-- Under the zero measure every partition has entropy zero. -/
@[simp]
theorem countablePartitionEntropy_zero_measure (a : X → ι) :
    countablePartitionEntropy (0 : Measure X) a = 0 := by
  simp [countablePartitionEntropy_def]

/-- Under a Dirac probability every atom has mass `0` or `1`, so every partition has entropy
zero. -/
@[simp]
theorem countablePartitionEntropy_dirac (a : X → ι) (x : X) :
    countablePartitionEntropy (Measure.dirac x) a = 0 := by
  refine tsum_eq_zero_iff.mpr fun i ↦ ?_
  rcases Measure.dirac_apply_eq_zero_or_one (a := x) (s := a ⁻¹' {i}) with h | h <;>
    simp [measureReal_def, h]

/-- A one-atom partition has entropy zero under a probability measure (or the zero measure),
whatever empty atoms its alphabet carries. -/
@[simp]
theorem countablePartitionEntropy_const [IsZeroOrProbabilityMeasure μ] (i₀ : ι) :
    countablePartitionEntropy μ (fun _ : X ↦ i₀) = 0 := by
  classical
  refine tsum_eq_zero_iff.mpr fun i ↦ ?_
  by_cases h : i₀ = i
  · obtain rfl | _ := eq_zero_or_isProbabilityMeasure (μ := μ) <;> simp [h]
  · simp [Set.preimage_const_of_notMem (h ∘ Set.mem_singleton_iff.mp)]

/-- Relabeling by an injection does not change the entropy: the atoms off the range are empty.
In particular a countable alphabet may be embedded into `ℕ`. -/
theorem countablePartitionEntropy_comp_of_injective (a : X → ι) {e : ι → ι'}
    (he : Function.Injective e) :
    countablePartitionEntropy μ (e ∘ a) = countablePartitionEntropy μ a := by
  rw [countablePartitionEntropy_def, countablePartitionEntropy_def,
    ← he.tsum_eq fun c hc ↦ ?_]
  · refine tsum_congr fun i ↦ ?_
    rw [Set.preimage_comp, show e ⁻¹' {e i} = {i} from Set.ext fun _ ↦ he.eq_iff]
  · by_contra hcr
    have : (e ∘ a) ⁻¹' {c} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx ↦ hcr ⟨a x, hx⟩
    simp [this] at hc

/-- Joining a partition with itself does not change it: `H(a ∨ a) = H(a)`. -/
theorem countablePartitionEntropy_pair_self (μ : Measure X) (a : X → ι) :
    countablePartitionEntropy μ (fun x ↦ (a x, a x)) = countablePartitionEntropy μ a :=
  countablePartitionEntropy_comp_of_injective (e := fun i ↦ (i, i)) a
    fun _ _ h ↦ congrArg Prod.fst h

/-- **Refinement.** Refining a partition by a countable label `a` does not decrease its entropy:
`H(b) ≤ H(a ∨ b)`. This holds for every measure: a cell of `b` of mass `p ≤ 1` is covered by its
cells in `a ∨ b`, each of mass `c ≤ p`, and `-c log c ≥ -c log p`. -/
theorem countablePartitionEntropy_le_pair [Countable ι] (a : X → ι) (b : X → κ) :
    countablePartitionEntropy μ b ≤ countablePartitionEntropy μ (fun x ↦ (a x, b x)) := by
  rw [countablePartitionEntropy_pair, tsum_comm, countablePartitionEntropy_def]
  refine tsum_le_tsum fun j ↦ ?_
  set B := b ⁻¹' {j}
  have hcell (i : ι) : μ (a ⁻¹' {i} ∩ B) * ENNReal.ofReal (-log (μ.real B)) ≤
      ENNReal.ofReal (negMulLog (μ.real (a ⁻¹' {i} ∩ B))) := by
    rcases eq_or_ne (μ B) ∞ with hB | hB
    · simp [measureReal_def, hB]
    have hc : μ (a ⁻¹' {i} ∩ B) ≠ ∞ := ne_top_of_le_ne_top hB (measure_mono Set.inter_subset_right)
    rw [← ofReal_measureReal hc, ofReal_negMulLog measureReal_nonneg]
    rcases (measureReal_nonneg (μ := μ) (s := a ⁻¹' {i} ∩ B)).eq_or_lt with h0 | h0
    · simp [← h0]
    · gcongr
      exact Set.inter_subset_right
  calc ENNReal.ofReal (negMulLog (μ.real B))
      = ENNReal.ofReal (μ.real B) * ENNReal.ofReal (-log (μ.real B)) :=
        ofReal_negMulLog measureReal_nonneg
    _ ≤ (∑' i, μ (a ⁻¹' {i} ∩ B)) * ENNReal.ofReal (-log (μ.real B)) := by
        gcongr
        refine ENNReal.ofReal_toReal_le.trans ((measure_mono fun x hx ↦ ?_).trans
          (measure_iUnion_le _))
        exact Set.mem_iUnion.mpr ⟨a x, rfl, hx⟩
    _ ≤ _ := by
        rw [← ENNReal.tsum_mul_right]
        exact tsum_le_tsum hcell

/-- **Coarsening.** A coarsening `f ∘ a` of a countable label `a` has entropy at most `H(a)`, for
every measure. -/
theorem countablePartitionEntropy_comp_le [Countable ι] (a : X → ι) (f : ι → κ) :
    countablePartitionEntropy μ (f ∘ a) ≤ countablePartitionEntropy μ a :=
  (countablePartitionEntropy_le_pair a (f ∘ a)).trans_eq <|
    countablePartitionEntropy_comp_of_injective (e := fun i ↦ (i, f i)) a
      fun _ _ h ↦ congrArg Prod.fst h

/-- On a finite alphabet, the entropy of a partition under a probability measure (or the zero
measure) is the finite sum of `negMulLog` of its atom masses. -/
theorem countablePartitionEntropy_eq_ofReal_sum [Fintype ι] [IsZeroOrProbabilityMeasure μ]
    (a : X → ι) :
    countablePartitionEntropy μ a = ENNReal.ofReal (∑ i, negMulLog (μ.real (a ⁻¹' {i}))) := by
  rw [countablePartitionEntropy_def, tsum_fintype, ENNReal.ofReal_sum_of_nonneg]
  exact fun _ _ ↦ negMulLog_nonneg measureReal_nonneg measureReal_le_one

/-- A partition conditioned on itself has conditional entropy zero. -/
@[simp]
theorem conditionalPartitionEntropy_self (μ : Measure X) (a : X → ι) :
    conditionalPartitionEntropy μ a a = 0 := by
  classical
  refine tsum_eq_zero_iff.mpr fun ⟨i, j⟩ ↦ ?_
  by_cases h : i = j
  · subst h
    simp only [Set.inter_self]
    rcases eq_or_ne (μ.real (a ⁻¹' {i})) 0 with h0 | h0
    · simp [h0]
    · simp [div_self h0]
  · have : a ⁻¹' {i} ∩ a ⁻¹' {j} = ∅ := by
      rw [← Set.preimage_inter, Set.singleton_inter_eq_empty.mpr h, Set.preimage_empty]
    simp [this]

section Measurable

variable [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The per-cell identity behind the chain rule:
`negMulLog p = p * (-log q) + p * log (q / p)` for `0 ≤ p ≤ q ≤ 1`, with both terms
nonnegative. -/
private theorem ofReal_negMulLog_eq_add {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    ENNReal.ofReal (negMulLog p) =
      ENNReal.ofReal p * ENNReal.ofReal (-log q) + ENNReal.ofReal (p * log (q / p)) := by
  rcases hp.eq_or_lt with rfl | hp
  · simp
  have hq0 : 0 < q := hp.trans_le hpq
  rw [← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_add
    (mul_nonneg hp.le (neg_nonneg.mpr (log_nonpos hq0.le hq)))
    (mul_nonneg hp.le (log_nonneg ((one_le_div hp).mpr hpq))),
    log_div hq0.ne' hp.ne', negMulLog]
  ring_nf

section ChainRule

variable [IsZeroOrProbabilityMeasure μ]

/-- **Chain rule.** Under a probability measure (or the zero measure), for a measurable countable
label `a` and any label `b`, the entropy of the pair label is `H(a ∨ b) = H(b) + H(a | b)`, with
values in `[0, ∞]`. -/
theorem countablePartitionEntropy_pair_eq_add {a : X → ι} (ha : Measurable a) (b : X → κ) :
    countablePartitionEntropy μ (fun x ↦ (a x, b x)) =
      countablePartitionEntropy μ b + conditionalPartitionEntropy μ a b := by
  have hcell : ∀ i j, ENNReal.ofReal (negMulLog (μ.real (a ⁻¹' {i} ∩ b ⁻¹' {j}))) =
      μ (a ⁻¹' {i} ∩ b ⁻¹' {j}) * ENNReal.ofReal (-log (μ.real (b ⁻¹' {j}))) +
        ENNReal.ofReal (μ.real (a ⁻¹' {i} ∩ b ⁻¹' {j}) *
          log (μ.real (b ⁻¹' {j}) / μ.real (a ⁻¹' {i} ∩ b ⁻¹' {j}))) := fun i j ↦ by
    rw [ofReal_negMulLog_eq_add measureReal_nonneg (measureReal_mono Set.inter_subset_right)
      measureReal_le_one, ofReal_measureReal]
  rw [countablePartitionEntropy_pair, conditionalPartitionEntropy_def, tsum_prod']
  simp only [hcell, tsum_add]
  congr 1
  rw [tsum_comm, countablePartitionEntropy_def]
  refine tsum_congr fun j ↦ ?_
  simp_rw [Set.inter_comm (a ⁻¹' _)]
  rw [ENNReal.tsum_mul_right, tsum_measure_inter_preimage_singleton ha,
    ofReal_negMulLog measureReal_nonneg, ofReal_measureReal]

end ChainRule

variable [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- The per-cell inequality behind `H(a | b) ≤ H(a)`: for `0 ≤ p ≤ q` and `p ≤ r`,
`p * log (r / p) + p ≤ p * (-log q) + q * r`, read in `ℝ≥0∞`. In `ℝ` it is `log y ≤ y - 1` at
`y = q * r / p`. -/
private theorem ofReal_mul_log_div_add_le {p q r : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hpr : p ≤ r) :
    ENNReal.ofReal (p * log (r / p)) + ENNReal.ofReal p ≤
      ENNReal.ofReal p * ENNReal.ofReal (-log q) + ENNReal.ofReal q * ENNReal.ofReal r := by
  rcases hp.eq_or_lt with rfl | hp
  · simp
  have hq0 := hp.trans_le hpq
  have hr := hp.trans_le hpr
  have hreal : p * log (r / p) + p ≤ p * (-log q) + q * r := by
    have hy := log_le_sub_one_of_pos (show 0 < q * r / p by positivity)
    rw [log_div (by positivity) hp.ne', log_mul hq0.ne' hr.ne'] at hy
    have h := mul_le_mul_of_nonneg_left hy hp.le
    rw [show p * (q * r / p - 1) = q * r - p by field_simp] at h
    rw [log_div hr.ne' hp.ne']
    linarith
  have hlog : 0 ≤ p * log (r / p) := mul_nonneg hp.le (log_nonneg ((one_le_div hp).mpr hpr))
  rw [← ENNReal.ofReal_add hlog hp.le, ← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_mul hq0.le]
  exact (ENNReal.ofReal_le_ofReal hreal).trans ENNReal.ofReal_add_le

/-- **Conditioning reduces entropy.** Under a probability measure (or the zero measure), for a
measurable countable label `b` and any label `a`, `H(a | b) ≤ H(a)`. -/
theorem conditionalPartitionEntropy_le [IsZeroOrProbabilityMeasure μ] (a : X → ι') {b : X → κ}
    (hb : Measurable b) :
    conditionalPartitionEntropy μ a b ≤ countablePartitionEntropy μ a := by
  rw [conditionalPartitionEntropy_def, tsum_prod', countablePartitionEntropy_def]
  refine tsum_le_tsum fun i ↦ ?_
  set A := a ⁻¹' {i}
  have hsplit := tsum_measure_inter_preimage_singleton (μ := μ) hb
  have hcell : ∀ j, ENNReal.ofReal (μ.real (A ∩ b ⁻¹' {j}) *
        log (μ.real (b ⁻¹' {j}) / μ.real (A ∩ b ⁻¹' {j}))) + μ (A ∩ b ⁻¹' {j}) ≤
      μ (A ∩ b ⁻¹' {j}) * ENNReal.ofReal (-log (μ.real A)) + μ A * μ (b ⁻¹' {j}) := fun j ↦ by
    have hμ (s : Set X) : ENNReal.ofReal (μ.real s) = μ s := ofReal_measureReal
    simpa only [hμ] using ofReal_mul_log_div_add_le measureReal_nonneg
      (measureReal_mono (μ := μ) Set.inter_subset_left)
      (measureReal_mono (μ := μ) Set.inter_subset_right)
  have htot : ∑' j, μ (b ⁻¹' {j}) ≤ 1 := by
    simpa using (hsplit Set.univ).le.trans prob_le_one
  refine ENNReal.le_of_add_le_add_right (measure_ne_top μ A) ?_
  calc _ = ∑' j, (ENNReal.ofReal (μ.real (A ∩ b ⁻¹' {j}) *
        log (μ.real (b ⁻¹' {j}) / μ.real (A ∩ b ⁻¹' {j}))) + μ (A ∩ b ⁻¹' {j})) := by
        rw [tsum_add, hsplit]
    _ ≤ ∑' j, (μ (A ∩ b ⁻¹' {j}) * ENNReal.ofReal (-log (μ.real A)) +
        μ A * μ (b ⁻¹' {j})) := tsum_le_tsum hcell
    _ ≤ μ A * ENNReal.ofReal (-log (μ.real A)) + μ A := by
        rw [tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hsplit]
        gcongr
        exact (mul_le_mul_right htot _).trans_eq (mul_one _)
    _ = _ := by rw [ofReal_negMulLog measureReal_nonneg, ofReal_measureReal]

/-- **Subadditivity.** Under a probability measure (or the zero measure), the entropy of the join
of two measurable countable labels is at most the sum of their entropies:
`H(a ∨ b) ≤ H(a) + H(b)`. -/
theorem countablePartitionEntropy_pair_le_add [IsZeroOrProbabilityMeasure μ] {a : X → ι}
    {b : X → κ} (ha : Measurable a) (hb : Measurable b) :
    countablePartitionEntropy μ (fun x ↦ (a x, b x)) ≤
      countablePartitionEntropy μ a + countablePartitionEntropy μ b := by
  rw [countablePartitionEntropy_pair_eq_add ha, add_comm (countablePartitionEntropy μ a)]
  gcongr
  exact conditionalPartitionEntropy_le a hb

private theorem countablePartitionEntropy_pair_of_indepFun_of_isProbabilityMeasure
    [IsProbabilityMeasure μ] {a : X → ι} {b : X → κ} (ha : Measurable a)
    (hb : Measurable b) (hab : IndepFun a b μ) :
    countablePartitionEntropy μ (fun x ↦ (a x, b x)) =
      countablePartitionEntropy μ a + countablePartitionEntropy μ b := by
  have hcell : ∀ i j, ENNReal.ofReal (negMulLog (μ.real (a ⁻¹' {i} ∩ b ⁻¹' {j}))) =
      ENNReal.ofReal (negMulLog (μ.real (a ⁻¹' {i}))) * μ (b ⁻¹' {j}) +
        μ (a ⁻¹' {i}) * ENNReal.ofReal (negMulLog (μ.real (b ⁻¹' {j}))) := fun i j ↦ by
    have hm : μ.real (a ⁻¹' {i} ∩ b ⁻¹' {j}) = μ.real (a ⁻¹' {i}) * μ.real (b ⁻¹' {j}) := by
      simp only [measureReal_def, hab.measure_inter_preimage_eq_mul _ _
        (measurableSet_singleton i) (measurableSet_singleton j), ENNReal.toReal_mul]
    have h1 := negMulLog_nonneg (measureReal_nonneg (μ := μ) (s := a ⁻¹' {i}))
      measureReal_le_one
    have h2 := negMulLog_nonneg (measureReal_nonneg (μ := μ) (s := b ⁻¹' {j}))
      measureReal_le_one
    rw [hm, negMulLog_mul, ENNReal.ofReal_add (mul_nonneg measureReal_nonneg h1)
      (mul_nonneg measureReal_nonneg h2), ENNReal.ofReal_mul measureReal_nonneg,
      ENNReal.ofReal_mul measureReal_nonneg, ofReal_measureReal, ofReal_measureReal]
    ring
  have hA : ∑' i, μ (a ⁻¹' {i}) = 1 := by
    simpa using (tsum_univ (f := fun i ↦ μ (a ⁻¹' {i}))).symm.trans
      (tsum_measure_preimage_singleton Set.countable_univ fun i _ ↦ ha (measurableSet_singleton i))
  have hB : ∑' j, μ (b ⁻¹' {j}) = 1 := by
    simpa using (tsum_univ (f := fun j ↦ μ (b ⁻¹' {j}))).symm.trans
      (tsum_measure_preimage_singleton Set.countable_univ fun j _ ↦ hb (measurableSet_singleton j))
  rw [countablePartitionEntropy_pair]
  simp only [hcell, tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hA, hB, mul_one,
    one_mul]
  simp only [countablePartitionEntropy_def]

/-- **Independence.** If the measurable countable labels `a` and `b` are independent, the
entropy of the pair label is `H(a ∨ b) = H(a) + H(b)`. Independence forces `μ univ` to be `0`,
`1` or `∞`, and in the last case every atom has real mass zero. -/
theorem countablePartitionEntropy_pair_of_indepFun {a : X → ι} {b : X → κ} (ha : Measurable a)
    (hb : Measurable b) (hab : IndepFun a b μ) :
    countablePartitionEntropy μ (fun x ↦ (a x, b x)) =
      countablePartitionEntropy μ a + countablePartitionEntropy μ b := by
  have hmul : ∀ s t, MeasurableSet s → MeasurableSet t →
      μ (a ⁻¹' s ∩ b ⁻¹' t) = μ (a ⁻¹' s) * μ (b ⁻¹' t) := fun s t hs ht ↦
    hab.measure_inter_preimage_eq_mul s t hs ht
  have huniv : μ Set.univ = μ Set.univ * μ Set.univ := by
    simpa using hmul Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
  rcases eq_or_ne (μ Set.univ) ∞ with htop | htop
  · -- Every atom and every cell has mass `0` or `∞`, hence real mass zero.
    have hA : ∀ i, μ.real (a ⁻¹' {i}) = 0 := fun i ↦ by
      have := hmul {i} Set.univ (measurableSet_singleton i) MeasurableSet.univ
      simp only [Set.preimage_univ, Set.inter_univ, htop] at this
      rw [measureReal_def, this, ENNReal.toReal_mul_top]
    have hB : ∀ j, μ.real (b ⁻¹' {j}) = 0 := fun j ↦ by
      have := hmul Set.univ {j} MeasurableSet.univ (measurableSet_singleton j)
      simp only [Set.preimage_univ, Set.univ_inter, htop] at this
      rw [measureReal_def, this, mul_comm, ENNReal.toReal_mul_top]
    have hC : ∀ i j, μ.real (a ⁻¹' {i} ∩ b ⁻¹' {j}) = 0 := fun i j ↦ by
      rw [measureReal_def, hmul _ _ (measurableSet_singleton i) (measurableSet_singleton j),
        ENNReal.toReal_mul, ← measureReal_def, hA, zero_mul]
    rw [countablePartitionEntropy_pair]
    simp [countablePartitionEntropy_def, hA, hB, hC]
  have : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr htop⟩
  have h01 : μ Set.univ = 0 ∨ μ Set.univ = 1 := by
    rcases eq_or_ne (μ Set.univ) 0 with h | h
    · exact Or.inl h
    · exact Or.inr ((ENNReal.mul_eq_left h htop).mp huniv.symm)
  rcases h01 with h | h
  · simp [Measure.measure_univ_eq_zero.mp h]
  · have : IsProbabilityMeasure μ := ⟨h⟩
    exact countablePartitionEntropy_pair_of_indepFun_of_isProbabilityMeasure ha hb hab

end Measurable

/-- Pulling a measurable countable label back along a measure-preserving map does not change its
entropy. -/
theorem countablePartitionEntropy_comp_of_measurePreserving {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [MeasurableSpace ι] [MeasurableSingletonClass ι] {T : X → Y}
    (hT : MeasurePreserving T μ ν) {a : Y → ι} (ha : Measurable a) :
    countablePartitionEntropy μ (a ∘ T) = countablePartitionEntropy ν a := by
  simp only [countablePartitionEntropy_def, Set.preimage_comp,
    hT.measureReal_preimage (ha (measurableSet_singleton _)).nullMeasurableSet]

end TauCeti
