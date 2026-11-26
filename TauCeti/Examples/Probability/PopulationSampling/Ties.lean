/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.Probability.PopulationSampling.RepeatedValues
public import TauCeti.Probability.Exchangeability.FiniteDeFinetti
public import TauCeti.Probability.Exchangeability.PermutedPopulation
import Mathlib.Tactic.NormNum

/-!
# Examples: sampling discrepancy of random populations with ties

Worked values of the tie-weighted sampling bounds of
`TauCeti.Probability.PopulationSampling.Ties` and of the finite de Finetti bound with ties
`TauCeti.Probability.ExchangeableAt.finiteDeFinetti_ties`. Draw `m` values from a random
population of size `n` with law `ρ`, once without replacement (`sampleWithoutReplacement`) and once
with replacement (`sampleWithReplacement`), and write `p = n.descFactorial m / n ^ m`,
`t = m.descFactorial 2 / n.descFactorial 2`. If `S` is a measurable set of populations with a
repeated value, the two laws differ on every event, in either direction, by at most
`1 - p - t * min p (1 - p) * ρ(S)`.

* With `S = ∅` the error is the collision probability `1 - p`, both for random populations and in
  the finite de Finetti form, where it is the error of
  `TauCeti.Probability.ExchangeableAt.finiteDeFinetti_exact_collision`. If the population has a
  repeated value almost surely, the error is the one-pair error `1 - p - t * min p (1 - p)`.
* For `n = 3`, `m = 2`, let `ρ` be the even mixture of the distinct-valued population
  `id : Fin 3 → Fin 3` and the one-pair population `update id 1 0`, and let `S` contain the second.
  The error is `1/3 - 1/18 = 5/18`, the average of the errors `1/3` and `2/9` of the two
  populations, against `1/3` for `S = ∅`. The all-distinct event has masses `5/6` and `5/9` under
  the two sampling laws, so the largest event excess is exactly `5/18`.
* A uniformly random ordering of the population `(0, 0, 2)` is exchangeable at `n = 3`, and its
  `3`-prefix has a repeated value almost surely. With `m = 2` the error of the finite de Finetti
  bound with ties is `2/9`, against `1/3` for `S = ∅`, and the largest event excess between the
  `2`-prefix law and the with-replacement sample of the `3`-prefix law is exactly `2/9`.

## References

* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764.
-/

public section

noncomputable section

open Function MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

/-! ### Degenerate tie sets -/

-- With no tied populations singled out (`S = ∅`), the error of the mixture bound with ties is the
-- collision probability `1 - p`, in both directions.
example {ι κ α : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    [MeasurableSpace α] (ρ : Measure (κ → α)) [IsProbabilityMeasure ρ] (A : Set (ι → α)) :
    sampleWithoutReplacement ρ A ≤ sampleWithReplacement ρ A +
        (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
          (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) ∧
      sampleWithReplacement ρ A ≤ sampleWithoutReplacement ρ A +
        (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
          (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) := by
  have hSx : ∀ x ∈ (∅ : Set (κ → α)), ¬ Injective x := fun _ hx => hx.elim
  rw [one_sub_descFactorial_div_pow_eq_ofReal]
  constructor
  · simpa only [measure_empty, ENNReal.toReal_zero, mul_zero, sub_zero] using
      sampleWithoutReplacement_le_sampleWithReplacement_add_ties ρ MeasurableSet.empty hSx A
  · simpa only [measure_empty, ENNReal.toReal_zero, mul_zero, sub_zero] using
      sampleWithReplacement_le_sampleWithoutReplacement_add_ties ρ MeasurableSet.empty hSx A

-- With `S = ∅`, the finite de Finetti bound with ties is the exact-collision finite de Finetti
-- bound `ExchangeableAt.finiteDeFinetti_exact_collision`.
example {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) (A : Set (Fin m → α)) :
    prefixLaw μ X m A ≤ sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A +
        (1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m) ∧
      sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A ≤ prefixLaw μ X m A +
        (1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m) := by
  rw [one_sub_descFactorial_div_pow_eq_ofReal]
  simpa only [measure_empty, ENNReal.toReal_zero, mul_zero, sub_zero] using
    h.finiteDeFinetti_ties hmn hX MeasurableSet.empty (fun _ hx => hx.elim) A

-- If the `n`-prefix of an exchangeable process has a repeated value almost surely, the error of
-- the finite de Finetti bound with ties is the one-pair error `1 - p - t * min p (1 - p)`.
example {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) {S : Set (Fin n → α)} (hS : MeasurableSet S)
    (hSx : ∀ x ∈ S, ¬ Injective x) (hS1 : prefixLaw μ X n S = 1) (A : Set (Fin m → α)) :
    let p : ℝ := n.descFactorial m / (n : ℝ) ^ m
    let t : ℝ := m.descFactorial 2 / n.descFactorial 2
    prefixLaw μ X m A ≤ sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A +
        ENNReal.ofReal (1 - p - t * min p (1 - p)) ∧
      sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A ≤ prefixLaw μ X m A +
        ENNReal.ofReal (1 - p - t * min p (1 - p)) := by
  simpa only [hS1, ENNReal.toReal_one, mul_one] using h.finiteDeFinetti_ties hmn hX hS hSx A

/-! ### An even mixture of distinct values and one pair -/

section TieMixture

/-- The even mixture of the distinct-valued population `id : Fin 3 → Fin 3` and the one-pair
population `update id 1 0`. -/
local notation "ρₘ" => (2⁻¹ : ℝ≥0∞) • Measure.dirac (id : Fin 3 → Fin 3) +
  (2⁻¹ : ℝ≥0∞) • Measure.dirac (update id (1 : Fin 3) 0)

/-- The even mixture of the distinct-valued population `id : Fin 3 → Fin 3` and the one-pair
population `update id 1 0` is a probability measure. -/
private theorem isProbabilityMeasure_tieMixture : IsProbabilityMeasure ρₘ :=
  ⟨by simp [ENNReal.inv_two_add_inv_two]⟩

/-- Sampling the even mixture of `id : Fin 3 → Fin 3` and `update id 1 0` twice without
replacement gives every event the average of its masses under sampling the two populations. -/
private theorem sampleWithoutReplacement_tieMixture_apply (A : Set (Fin 2 → Fin 3)) :
    sampleWithoutReplacement ρₘ A =
      2⁻¹ * sampleWithoutReplacement (Measure.dirac (id : Fin 3 → Fin 3)) A +
        2⁻¹ * sampleWithoutReplacement (Measure.dirac (update id (1 : Fin 3) 0)) A := by
  simp only [sampleWithoutReplacement_def, samplePopulation_add_right, samplePopulation_smul_right,
    add_apply, smul_apply, smul_eq_mul]

/-- Sampling the even mixture of `id : Fin 3 → Fin 3` and `update id 1 0` twice with replacement
gives every event the average of its masses under sampling the two populations. -/
private theorem sampleWithReplacement_tieMixture_apply (A : Set (Fin 2 → Fin 3)) :
    sampleWithReplacement ρₘ A =
      2⁻¹ * sampleWithReplacement (Measure.dirac (id : Fin 3 → Fin 3)) A +
        2⁻¹ * sampleWithReplacement (Measure.dirac (update id (1 : Fin 3) 0)) A := by
  simp only [sampleWithReplacement_def, samplePopulation_add_right, samplePopulation_smul_right,
    add_apply, smul_apply, smul_eq_mul]

/-- The mixture gives the one-pair population `update id 1 0` mass `1/2`. -/
private theorem tieMixture_singleton_update_id : ρₘ {update id (1 : Fin 3) 0} = 2⁻¹ := by
  have h : (id : Fin 3 → Fin 3) ∉ ({update id (1 : Fin 3) 0} : Set (Fin 3 → Fin 3)) := by
    simp only [Set.mem_singleton_iff]
    decide
  simp [h]

/-- **The mixture bound with ties for `n = 3`, `m = 2`.** For the even mixture of the
distinct-valued population `id : Fin 3 → Fin 3` and the one-pair population `update id 1 0`, with
`S` the one-pair population, the two sampling laws differ on every event, in either direction, by
at most `1 - p - t * min p (1 - p) * ρ(S) = 1 - 2/3 - (1/3) * (1/3) * (1/2) = 5/18`, the average of
the errors `1/3` and `2/9` of the two populations. -/
private theorem tieMixture_le_add (A : Set (Fin 2 → Fin 3)) :
    sampleWithoutReplacement ρₘ A ≤ sampleWithReplacement ρₘ A + 5 / 18 ∧
      sampleWithReplacement ρₘ A ≤ sampleWithoutReplacement ρₘ A + 5 / 18 := by
  have := isProbabilityMeasure_tieMixture
  have hS : MeasurableSet ({update id (1 : Fin 3) 0} : Set (Fin 3 → Fin 3)) :=
    measurableSet_singleton _
  have hSx : ∀ x ∈ ({update id (1 : Fin 3) 0} : Set (Fin 3 → Fin 3)), ¬ Injective x := by
    rintro x rfl
    exact not_injective_iff.2 ⟨1, 0, by decide, by decide⟩
  constructor
  · convert sampleWithoutReplacement_le_sampleWithReplacement_add_ties ρₘ hS hSx A using 2
    rw [tieMixture_singleton_update_id]
    norm_num [Nat.descFactorial, ENNReal.ofReal_div_of_pos]
  · convert sampleWithReplacement_le_sampleWithoutReplacement_add_ties ρₘ hS hSx A using 2
    rw [tieMixture_singleton_update_id]
    norm_num [Nat.descFactorial, ENNReal.ofReal_div_of_pos]

/-- For `n = 3` and `m = 2`, the word of a sample of the one-pair population `update id 1 0` has
distinct letters for exactly four of the six embeddings `Fin 2 ↪ Fin 3`: those whose image does
not contain both `0` and `1`. -/
private theorem natCard_embedding_update_id_fin_three_comp_injective :
    Nat.card {f : Fin 2 ↪ Fin 3 //
      update id (1 : Fin 3) 0 ∘ f ∈ {g : Fin 2 → Fin 3 | Injective g}} = 4 := by
  -- Count injective index maps instead of embeddings, so that the count is decidable.
  rw [← Nat.card_congr ((Equiv.subtypeInjectiveEquivEmbedding (Fin 2) (Fin 3)).subtypeEquiv
      (p := fun f => Injective (update id (1 : Fin 3) 0 ∘ f.val)) fun _ => Iff.rfl),
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter Injective
      fun f => Injective (update id (1 : Fin 3) 0 ∘ f)), Nat.card_eq_fintype_card]
  decide

/-- For `n = 3` and `m = 2`, the word of a sample of the one-pair population `update id 1 0` has
distinct letters for exactly four of the nine index maps `Fin 2 → Fin 3`: one position takes `0`
or `1` and the other takes `2`. -/
private theorem natCard_update_id_fin_three_comp_injective :
    Nat.card {f : Fin 2 → Fin 3 //
      update id (1 : Fin 3) 0 ∘ f ∈ {g : Fin 2 → Fin 3 | Injective g}} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- Sampling the mixture twice without replacement gives the all-distinct event mass
`(1/2) * 1 + (1/2) * (4/6) = 5/6`. -/
private theorem sampleWithoutReplacement_tieMixture_injective :
    sampleWithoutReplacement ρₘ {f : Fin 2 → Fin 3 | Injective f} = 5 / 6 := by
  rw [sampleWithoutReplacement_tieMixture_apply,
    sampleWithoutReplacement_dirac_injective_apply_eq_one injective_id ⟨![0, 1], by decide⟩
      .of_discrete,
    sampleWithoutReplacement_dirac_apply _ .of_discrete,
    natCard_embedding_update_id_fin_three_comp_injective]
  norm_num only [Fintype.card_fin, Nat.descFactorial, Nat.cast_ofNat]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

/-- Sampling the mixture twice with replacement gives the all-distinct event mass
`(1/2) * (6/9) + (1/2) * (4/9) = 5/9`. -/
private theorem sampleWithReplacement_tieMixture_injective :
    sampleWithReplacement ρₘ {f : Fin 2 → Fin 3 | Injective f} = 5 / 9 := by
  rw [sampleWithReplacement_tieMixture_apply,
    sampleWithReplacement_dirac_injective_apply_eq injective_id .of_discrete,
    sampleWithReplacement_dirac_apply _ .of_discrete,
    natCard_update_id_fin_three_comp_injective]
  norm_num only [Fintype.card_fin, Nat.descFactorial, Nat.cast_ofNat]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num

/-- **The mixture bound with ties is attained for `n = 3`, `m = 2`.** For the even mixture of the
distinct-valued population `id : Fin 3 → Fin 3` and the one-pair population `update id 1 0`, the
largest event excess of sampling without replacement over sampling with replacement is exactly
the error `5/18` of the mixture bound with ties. The all-distinct event attains it, with masses
`5/6` and `5/9`. -/
theorem
    iSup_sampleWithoutReplacement_sub_sampleWithReplacement_smul_dirac_id_add_smul_dirac_fin_three :
    (⨆ (A : Set (Fin 2 → Fin 3)) (_ : MeasurableSet A),
      sampleWithoutReplacement ρₘ A - sampleWithReplacement ρₘ A) = 5 / 18 := by
  refine le_antisymm (iSup₂_le fun A _ => tsub_le_iff_left.2 ?_) ?_
  · exact (tieMixture_le_add A).1
  · refine le_iSup₂_of_le {f : Fin 2 → Fin 3 | Injective f} .of_discrete (le_of_eq ?_)
    rw [sampleWithoutReplacement_tieMixture_injective, sampleWithReplacement_tieMixture_injective]
    refine (ENNReal.sub_eq_of_eq_add_rev (by finiteness) ?_).symm
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    norm_num

end TieMixture

/-! ### A uniformly random ordering of a population with a tie -/

section PermutedTie

-- Any discrete measurable space on the permutations will do; it is a variable rather than an
-- instance argument because Mathlib has no global measurable space on `Equiv.Perm (Fin 3)`.
variable {_ : MeasurableSpace (Equiv.Perm (Fin 3))} [MeasurableSingletonClass (Equiv.Perm (Fin 3))]

/-- A uniformly random ordering of the population `(0, 0, 2) = update id 1 0` has a repeated
value in its `3`-prefix almost surely. -/
private theorem prefixLaw_permutedTie_setOf_not_injective :
    prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin 3))))
        (permutedPopulation (update id (1 : Fin 3) 0) 0) 3 {f | ¬ Injective f} = 1 := by
  have := isProbabilityMeasure_sampleWithoutReplacement (ι := Fin 3)
    (Measure.dirac (update id (1 : Fin 3) 0)) (Embedding.refl _)
  rw [prefixLaw_permutedPopulation_self, ← Set.compl_ofPred,
    prob_compl_eq_one_iff .of_discrete, sampleWithoutReplacement_dirac_apply _ .of_discrete]
  have : IsEmpty {f : Fin 3 ↪ Fin 3 //
      update id (1 : Fin 3) 0 ∘ f ∈ {g : Fin 3 → Fin 3 | Injective g}} :=
    ⟨fun f => (by decide : ∀ g : Fin 3 → Fin 3, ¬ Injective (update id (1 : Fin 3) 0 ∘ g))
      f.val f.property⟩
  simp

-- **Finite de Finetti with ties for a random ordering of `(0, 0, 2)`.** The uniformly random
-- ordering of the population `(0, 0, 2) = update id 1 0` is exchangeable at `n = 3`
-- (`exchangeableAt_permutedPopulation`). Since its `3`-prefix has a repeated value almost surely,
-- its `2`-prefix law and the with-replacement sample of its `3`-prefix law differ on every event,
-- in either direction, by at most the one-pair error `1 - 2/3 - (1/3) * (1/3) = 2/9`, against the
-- collision probability `1/3` of the exact-collision bound.
example (A : Set (Fin 2 → Fin 3)) :
    prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin 3))))
        (permutedPopulation (update id (1 : Fin 3) 0) 0) 2 A ≤
        sampleWithReplacement (ι := Fin 2)
          (prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin 3))))
            (permutedPopulation (update id (1 : Fin 3) 0) 0) 3) A + 2 / 9 ∧
      sampleWithReplacement (ι := Fin 2)
          (prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin 3))))
            (permutedPopulation (update id (1 : Fin 3) 0) 0) 3) A ≤
        prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin 3))))
          (permutedPopulation (update id (1 : Fin 3) 0) 0) 2 A + 2 / 9 := by
  have h := (exchangeableAt_permutedPopulation (update id (1 : Fin 3) 0) 0).finiteDeFinetti_ties
    (m := 2) (by norm_num) (fun i => (measurable_permutedPopulation _ _ _).aemeasurable)
    (S := {f | ¬ Injective f}) .of_discrete (fun _ hx => hx) A
  -- Only the error term changes: compute it as `2/9` in both directions.
  convert h using 3 <;>
    rw [prefixLaw_permutedTie_setOf_not_injective] <;>
    norm_num [Nat.descFactorial, ENNReal.ofReal_div_of_pos]

/-- **The bound is attained for a random ordering of `(0, 0, 2)`.** For the uniformly random
ordering of the population `(0, 0, 2) = update id 1 0`, the largest event excess of the `2`-prefix
law over the with-replacement sample of the `3`-prefix law is exactly the error `2/9` of the
finite de Finetti bound with ties: the two laws are the sampling laws of the one-pair population.
-/
theorem iSup_prefixLaw_sub_sampleWithReplacement_permutedPopulation_update_id_fin_three :
    (⨆ (A : Set (Fin 2 → Fin 3)) (_ : MeasurableSet A),
      prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin 3))))
          (permutedPopulation (update id (1 : Fin 3) 0) 0) 2 A -
        sampleWithReplacement (ι := Fin 2)
          (prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin 3))))
            (permutedPopulation (update id (1 : Fin 3) 0) 0) 3) A) = 2 / 9 := by
  rw [prefixLaw_permutedPopulation_of_le _ _ (by norm_num),
    sampleWithReplacement_prefixLaw_permutedPopulation]
  exact iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_update_id_fin_three

end PermutedTie

end TauCeti.Probability
