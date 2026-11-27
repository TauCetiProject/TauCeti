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
import TauCeti.InformationTheory.KullbackLeibler.KLFun
import TauCeti.MeasureTheory.Measure.Restrict
import TauCeti.Probability.Independence.Basic

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
* `TauCeti.countablePartitionEntropy_comp_of_measurePreserving`,
  `TauCeti.conditionalPartitionEntropy_comp_of_measurePreserving`: pulling labels back along a
  measure-preserving map does not change their entropy or conditional entropy.
* `TauCeti.countablePartitionEntropy_pair_of_indepFun`: independent labels have additive entropy;
  `TauCeti.countablePartitionEntropy_prod` is the case of a label on each factor of a product of
  probability measures, `H_{μ × ν}((a, b)) = H_μ(a) + H_ν(b)`.
* `TauCeti.countablePartitionEntropy_comp_of_injective`: relabeling by an injection, for instance
  embedding a countable alphabet into `ℕ`, does not change the entropy;
  `TauCeti.conditionalPartitionEntropy_comp_right_of_injective` is the same for the conditioning
  label.
* `TauCeti.countablePartitionEntropy_congr_ae`, `TauCeti.conditionalPartitionEntropy_congr_ae`:
  almost-everywhere equal labels have equal entropy and conditional entropy.
* `TauCeti.conditionalPartitionEntropy_comp_right_self_eq_tsum`: the conditional entropy
  `H(a | f ∘ a)` of a label given a coarsening of itself, as a sum over the atoms of `a`.
* `TauCeti.tendsto_conditionalPartitionEntropy_min`: a label `a : X → ℕ` of finite entropy is
  approximated by its truncations, `H(a | min a N) → 0` as `N → ∞`.

## References

* G. A. Margulis and G. M. Tomanov, Invariant measures for actions of unipotent groups over local
  fields on homogeneous spaces, Invent. Math. 116 (1994), 347–392, §9.3, pp. 381–383,
  doi:10.1007/BF01231565.
-/

public section

open MeasureTheory ProbabilityTheory Real InformationTheory
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

/-- Relabeling the conditioning label by an injection does not change the conditional entropy. -/
theorem conditionalPartitionEntropy_comp_right_of_injective (a : X → ι) (b : X → κ)
    {e : κ → ι'} (he : Function.Injective e) :
    conditionalPartitionEntropy μ a (e ∘ b) = conditionalPartitionEntropy μ a b := by
  rw [conditionalPartitionEntropy_def, conditionalPartitionEntropy_def,
    ← (Function.Injective.prodMap Function.injective_id he).tsum_eq fun p hp ↦ ?_]
  · refine tsum_congr fun p ↦ ?_
    simp only [Prod.map_fst, id_eq, Prod.map_snd, Set.preimage_comp,
      show e ⁻¹' {e p.2} = {p.2} from Set.ext fun _ ↦ he.eq_iff]
  · -- The cells over labels off the range of `e` are empty.
    by_contra hpr
    have : (e ∘ b) ⁻¹' {p.2} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx ↦ hpr ⟨(p.1, b x), Prod.ext rfl hx⟩
    simp [this] at hp

/-- Almost-everywhere equal labels have equal entropy. No measurability is needed: the atoms
differ by null sets. -/
theorem countablePartitionEntropy_congr_ae {a a' : X → ι} (h : a =ᵐ[μ] a') :
    countablePartitionEntropy μ a = countablePartitionEntropy μ a' := by
  simp only [countablePartitionEntropy_def, measureReal_def,
    measure_congr (h.preimage _)]

/-- Almost-everywhere equal labels have equal conditional entropy. -/
theorem conditionalPartitionEntropy_congr_ae {a a' : X → ι} {b b' : X → κ} (ha : a =ᵐ[μ] a')
    (hb : b =ᵐ[μ] b') :
    conditionalPartitionEntropy μ a b = conditionalPartitionEntropy μ a' b' := by
  simp only [conditionalPartitionEntropy_def, measureReal_def,
    measure_congr ((ha.preimage _).inter (hb.preimage _)),
    measure_congr (hb.preimage _)]

/-- Almost-everywhere equality passes to joins, so joins of almost-everywhere equal labels have
equal entropy. -/
theorem countablePartitionEntropy_pair_congr_ae {a a' : X → ι} {b b' : X → κ}
    (ha : a =ᵐ[μ] a') (hb : b =ᵐ[μ] b') :
    countablePartitionEntropy μ (fun x ↦ (a x, b x)) =
      countablePartitionEntropy μ (fun x ↦ (a' x, b' x)) :=
  countablePartitionEntropy_congr_ae (ha.prodMk hb)

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

/-- On a finite alphabet the entropy is finite, for any measure. -/
theorem countablePartitionEntropy_ne_top [Finite ι] (μ : Measure X) (a : X → ι) :
    countablePartitionEntropy μ a ≠ ∞ := by
  have := Fintype.ofFinite ι
  rw [countablePartitionEntropy_def, tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.ofReal_ne_top

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

/-- The conditional entropy of a label given a coarsening `f ∘ a` of itself: each atom
`a ⁻¹' {i}` lies in the atom `a ⁻¹' (f ⁻¹' {f i})` of the coarsening, and contributes
`p_i log (q_i / p_i)`, with `p_i`, `q_i` the masses of the two atoms. -/
theorem conditionalPartitionEntropy_comp_right_self_eq_tsum (μ : Measure X) (a : X → ι)
    (f : ι → κ) :
    conditionalPartitionEntropy μ a (f ∘ a) = ∑' i, ENNReal.ofReal (μ.real (a ⁻¹' {i}) *
      log (μ.real (a ⁻¹' (f ⁻¹' {f i})) / μ.real (a ⁻¹' {i}))) := by
  rw [conditionalPartitionEntropy_def, tsum_prod']
  refine tsum_congr fun i ↦ ?_
  rw [tsum_eq_single (f i) fun j hj ↦ ?_]
  · have hcell : a ⁻¹' {i} ∩ (f ∘ a) ⁻¹' {f i} = a ⁻¹' {i} :=
      Set.inter_eq_left.mpr fun x hx ↦ by simp_all
    rw [hcell, Set.preimage_comp]
  · have hcell : a ⁻¹' {i} ∩ (f ∘ a) ⁻¹' {j} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x ⟨h1, h2⟩ ↦ hj (by
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply] at h1 h2
        rw [← h2, h1])
    simp [hcell]

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
    (mul_log_div_nonneg hp.le hpq),
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
`p * log (r / p) + p ≤ p * (-log q) + q * r`, read in `ℝ≥0∞`. In `ℝ` the gap is
`q * r * klFun (p / (q * r))`, nonnegative by Mathlib's `InformationTheory.klFun_nonneg`. -/
private theorem ofReal_mul_log_div_add_le {p q r : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hpr : p ≤ r) :
    ENNReal.ofReal (p * log (r / p)) + ENNReal.ofReal p ≤
      ENNReal.ofReal p * ENNReal.ofReal (-log q) + ENNReal.ofReal q * ENNReal.ofReal r := by
  rcases hp.eq_or_lt with rfl | hp
  · simp
  have hq0 := hp.trans_le hpq
  have hr := hp.trans_le hpr
  have hreal : p * log (r / p) + p ≤ p * (-log q) + q * r := by
    have h0 : 0 ≤ q * r * klFun (p / (q * r)) :=
      mul_nonneg (by positivity) (klFun_nonneg (by positivity))
    rw [mul_klFun_div (mul_ne_zero hq0.ne' hr.ne'), log_mul hq0.ne' hr.ne'] at h0
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
  rw [countablePartitionEntropy_pair]
  simp only [hcell, tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
    tsum_measure_preimage_singleton_eq_measure_univ ha,
    tsum_measure_preimage_singleton_eq_measure_univ hb, measure_univ, mul_one, one_mul]
  simp only [countablePartitionEntropy_def]

/-- **Independence.** If the measurable countable labels `a` and `b` are independent, the
entropy of the pair label is `H(a ∨ b) = H(a) + H(b)`. Independence forces `μ univ` to be `0`,
`1` or `∞`, and in the last case every atom has real mass zero. -/
theorem countablePartitionEntropy_pair_of_indepFun {a : X → ι} {b : X → κ} (ha : Measurable a)
    (hb : Measurable b) (hab : IndepFun a b μ) :
    countablePartitionEntropy μ (fun x ↦ (a x, b x)) =
      countablePartitionEntropy μ a + countablePartitionEntropy μ b := by
  rcases eq_or_ne (μ Set.univ) ∞ with htop | htop
  · -- Every atom and every cell has real mass zero.
    have hC : ∀ i j, μ.real (a ⁻¹' {i} ∩ b ⁻¹' {j}) = 0 := fun i j ↦
      hab.measureReal_inter_preimage_eq_zero_of_measure_univ_eq_top htop
        (measurableSet_singleton i) (measurableSet_singleton j)
    have hA : ∀ i, μ.real (a ⁻¹' {i}) = 0 := fun i ↦
      hab.measureReal_preimage_eq_zero_of_measure_univ_eq_top htop (measurableSet_singleton i)
    have hB : ∀ j, μ.real (b ⁻¹' {j}) = 0 := fun j ↦
      hab.symm.measureReal_preimage_eq_zero_of_measure_univ_eq_top htop
        (measurableSet_singleton j)
    rw [countablePartitionEntropy_pair]
    simp [countablePartitionEntropy_def, hA, hB, hC]
  have : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr htop⟩
  have := hab.isZeroOrProbabilityMeasure
  obtain rfl | _ := eq_zero_or_isProbabilityMeasure (μ := μ)
  · simp
  · exact countablePartitionEntropy_pair_of_indepFun_of_isProbabilityMeasure ha hb hab

end Measurable

/-- Pulling a measurable countable label back along a measure-preserving map does not change its
entropy. -/
theorem countablePartitionEntropy_comp_of_measurePreserving {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [MeasurableSpace ι] [MeasurableSingletonClass ι] {T : X → Y}
    (hT : MeasurePreserving T μ ν) {a : Y → ι} (ha : Measurable a) :
    countablePartitionEntropy μ (a ∘ T) = countablePartitionEntropy ν a := by
  simp only [countablePartitionEntropy_def, Set.preimage_comp,
    hT.measureReal_preimage (ha (measurableSet_singleton _)).nullMeasurableSet]


/-- Pulling two measurable labels back along a measure-preserving map does not change the
conditional entropy of one given the other. -/
theorem conditionalPartitionEntropy_comp_of_measurePreserving {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] {T : X → Y} (hT : MeasurePreserving T μ ν) {a : Y → ι}
    {b : Y → κ} (ha : Measurable a) (hb : Measurable b) :
    conditionalPartitionEntropy μ (a ∘ T) (b ∘ T) = conditionalPartitionEntropy ν a b := by
  simp only [conditionalPartitionEntropy_def, Set.preimage_comp, ← Set.preimage_inter,
    hT.measureReal_preimage
      ((ha (measurableSet_singleton _)).inter (hb (measurableSet_singleton _))).nullMeasurableSet,
    hT.measureReal_preimage (hb (measurableSet_singleton _)).nullMeasurableSet]

open Filter Topology in
/-- **Truncation.** Under a probability measure (or the zero measure), a label `a : X → ℕ` of
finite entropy is approximated by its finite truncations `min a N`: the conditional entropy
`H(a | min a N)` tends to zero as `N → ∞`. No measurability is needed. -/
theorem tendsto_conditionalPartitionEntropy_min [IsZeroOrProbabilityMeasure μ] {a : X → ℕ}
    (hfin : countablePartitionEntropy μ a ≠ ∞) :
    Tendsto (fun N : ℕ ↦ conditionalPartitionEntropy μ a fun x ↦ min (a x) N) atTop (𝓝 0) := by
  set g : ℕ → ℝ≥0∞ := fun i ↦ ENNReal.ofReal (negMulLog (μ.real (a ⁻¹' {i})))
  have hbound (N : ℕ) :
      conditionalPartitionEntropy μ a (fun x ↦ min (a x) N) ≤ ∑' k, g (k + N) := by
    set t : ℕ → ℝ≥0∞ := fun i ↦ ENNReal.ofReal (μ.real (a ⁻¹' {i}) *
      log (μ.real (a ⁻¹' ((fun j ↦ min j N) ⁻¹' {min i N})) / μ.real (a ⁻¹' {i})))
    have hlow : ∀ i ∈ Finset.range N, t i = 0 := fun i hi ↦ by
      have hiN := Finset.mem_range.mp hi
      have hfib : (fun j ↦ min j N) ⁻¹' {min i N} = {i} := by
        ext j
        simp only [Set.mem_preimage, Set.mem_singleton_iff, min_eq_left hiN.le]
        omega
      simp [t, hfib]
    have hhigh (i : ℕ) : t i ≤ g i := by
      refine ENNReal.ofReal_le_ofReal ?_
      set p := μ.real (a ⁻¹' {i})
      set r := μ.real (a ⁻¹' ((fun j ↦ min j N) ⁻¹' {min i N}))
      have hpr : p ≤ r := measureReal_mono (Set.preimage_mono (by simp))
      rcases (measureReal_nonneg : 0 ≤ p).eq_or_lt with hp | hp
      · rw [show p = 0 from hp.symm]
        simp
      rw [log_div (hp.trans_le hpr).ne' hp.ne', negMulLog, mul_sub]
      have : p * log r ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hp.le (log_nonpos (hp.le.trans hpr) measureReal_le_one)
      linarith
    calc conditionalPartitionEntropy μ a (fun x ↦ min (a x) N) = ∑' i, t i :=
          conditionalPartitionEntropy_comp_right_self_eq_tsum μ a fun j ↦ min j N
      _ = ∑' k, t (k + N) := by
          rw [← CompleteLattice.summable.sum_add_tsum_nat_add' (k := N), Finset.sum_eq_zero hlow,
            zero_add]
      _ ≤ ∑' k, g (k + N) := tsum_le_tsum fun k ↦ hhigh _
  rw [countablePartitionEntropy_def] at hfin
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ENNReal.tendsto_sum_nat_add g hfin) (fun _ ↦ zero_le) hbound

/-- **Product labels.** Under a product of probability measures, the entropy of the product of a
measurable countable label on each factor is the sum of their entropies. -/
theorem countablePartitionEntropy_prod {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Countable ι] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    [Countable κ] {a : X → ι} {b : Y → κ} (ha : Measurable a) (hb : Measurable b) :
    countablePartitionEntropy (μ.prod ν) (fun p ↦ (a p.1, b p.2)) =
      countablePartitionEntropy μ a + countablePartitionEntropy ν b := by
  refine (countablePartitionEntropy_pair_of_indepFun (a := fun p : X × Y ↦ a p.1)
    (b := fun p : X × Y ↦ b p.2) (ha.comp measurable_fst) (hb.comp measurable_snd)
    (indepFun_prod ha hb)).trans ?_
  exact congrArg₂ (· + ·)
    (countablePartitionEntropy_comp_of_measurePreserving (measurePreserving_fst) ha)
    (countablePartitionEntropy_comp_of_measurePreserving (measurePreserving_snd) hb)

end TauCeti
