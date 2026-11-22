/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.FiniteDeFinetti
public import TauCeti.Probability.Exchangeability.PermutedPopulation
import Mathlib.Tactic.NormNum

/-!
# Worked examples: sampling deterministic populations and the exact collision bound

Draw `m` values from a population of `n` values, once without replacement
(`sampleWithoutReplacement`) and once with replacement (`sampleWithReplacement`), and write
`p = n.descFactorial m / n ^ m` for the probability that a uniform index map is injective. Every
event has the same probability under the two laws up to the collision probability `1 - p`, in
either direction, and for distinct population values the all-distinct event attains this error.
These examples evaluate the general results in small cases.

* Sampling a population of three distinct values twice gives each of the six injective words
  mass `1/6` without replacement and each of the nine words mass `1/9` with replacement. A
  constant observation of a sampled population leaves the total mass on the constant word.
* For `n = 3`, `m = 2` the uniform index map is injective with probability `6/9`. For `n = 2`,
  `m = 3` it never is. When there is no index map at all (`n = 0`, `m = 1`) the uniform law is
  zero, so the collision mass is `0` rather than `1 - p = 1`.
* For `n = 3`, `m = 2` and distinct values, the all-distinct event has masses `1` and `2/3`, so
  the exact error `1/3` is attained. For `n = 4`, `m = 3` the exact error is `5/8`, below the
  union bound `choose 3 2 / 4 = 3/4`.
* For a process exchangeable at `n = 2` the two-term prefix law is within `1/2` of the
  with-replacement sample, and a uniformly random ordering of two distinct values attains `1/2`.
  For one term the error is `0` and the two laws agree.
* For samples of size at most one, `p = 1` and the two sampling laws of a distinct-valued
  population are at excess `0`. The all-distinct event must be measurable for the error to be
  attained: under the trivial σ-algebra it is not, and the excess drops to `0`.

## References

* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764, Theorem 13.
-/

public section

open Function MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Examples.PopulationSampling

open TauCeti.Probability

/-! ### Sampling a deterministic population -/

-- There are six injective words of length two in three letters.
example : Fintype.card {y : Fin 2 → Fin 3 // Injective y} = 6 := by decide

-- Sampling three distinct values twice without replacement gives each injective word mass `1/6`.
example {y : Fin 2 → Fin 3} (hy : Injective y) :
    sampleWithoutReplacement (ι := Fin 2) (Measure.dirac (id : Fin 3 → Fin 3)) {y} = 1 / 6 := by
  have hcard : Nat.card {f : Fin 2 ↪ Fin 3 // id ∘ f = y} = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨⟨fun f g => Subtype.ext <| Embedding.ext fun i =>
      congrFun (f.property.trans g.property.symm) i⟩, ⟨⟨⟨y, hy⟩, rfl⟩⟩⟩
  rw [sampleWithoutReplacement_dirac_apply_singleton, hcard]
  norm_num [Nat.descFactorial]

-- A word with a repeated letter never occurs without replacement.
example {y : Fin 2 → Fin 3} (hy : ¬ Injective y) :
    sampleWithoutReplacement (ι := Fin 2) (Measure.dirac (id : Fin 3 → Fin 3)) {y} = 0 := by
  have hcard : Nat.card {f : Fin 2 ↪ Fin 3 // id ∘ f = y} = 0 :=
    Nat.card_eq_zero.2 <| .inl ⟨fun f => hy (f.property ▸ f.val.injective)⟩
  rw [sampleWithoutReplacement_dirac_apply_singleton, hcard]
  simp

-- Sampling three distinct values twice with replacement gives each word mass `1/9`.
example (y : Fin 2 → Fin 3) :
    sampleWithReplacement (ι := Fin 2) (Measure.dirac (id : Fin 3 → Fin 3)) {y} = 1 / 9 := by
  have hcard : Nat.card {f : Fin 2 → Fin 3 // id ∘ f = y} = 1 :=
    Nat.card_eq_one_iff_unique.2
      ⟨⟨fun f g => Subtype.ext (f.property.trans g.property.symm)⟩, ⟨⟨y, rfl⟩⟩⟩
  rw [sampleWithReplacement_dirac_apply_singleton, hcard]
  norm_num

-- A constant observation of a sampled population puts the total mass `σ univ * ρ univ` on the
-- constant word.
example {α β ι κ : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] (σ : Measure (ι → κ)) (ρ : Measure (κ → α))
    [SFinite σ] [SFinite ρ] (c : β) :
    samplePopulation σ (ρ.map fun _ (_ : κ) => c) =
      (σ Set.univ * ρ Set.univ) • Measure.dirac fun _ => c := by
  rw [samplePopulation_map σ ρ (measurable_const (a := c)), Measure.map_const,
    samplePopulation_def, Measure.map_apply measurable_reindexPopulation .univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod]

/-! ### Collision masses of uniform index maps -/

-- For `n = 3`, `m = 2` a uniform index map is injective with probability `6/9`.
example : uniformOn (Set.univ : Set (Fin 2 → Fin 3)) {k | Injective k} = 6 / 9 := by
  norm_num [Nat.descFactorial]

-- For `n = 3`, `m = 2` the collision probability is `1 - 6/9 = 1/3`.
example : uniformOn (Set.univ : Set (Fin 2 → Fin 3)) {k | ¬ Injective k} = 1 / 3 := by
  rw [← ofReal_measureReal, uniformOn_real_not_injective_apply_eq]
  norm_num [Nat.descFactorial, ENNReal.ofReal_div_of_pos]

-- For `m > n ≥ 1` no index map is injective: `p = 0` and the collision mass is `1`.
example : uniformOn (Set.univ : Set (Fin 3 → Fin 2)) {k | Injective k} = 0 ∧
    uniformOn (Set.univ : Set (Fin 3 → Fin 2)) {k | ¬ Injective k} = 1 := by
  simp [Nat.descFactorial]

-- Without an index map (`n = 0`, `m = 1`) the uniform law is zero, so the collision mass is `0`
-- while `1 - p = 1 - 0 / 0 = 1`: `uniformOn_not_injective_apply_eq` needs `Nonempty (ι → κ)`.
example : uniformOn (Set.univ : Set (Fin 1 → Fin 0)) {k | ¬ Injective k} ≠
    1 - (Fintype.card (Fin 0)).descFactorial (Fintype.card (Fin 1)) /
      (Fintype.card (Fin 0) : ℝ≥0∞) ^ Fintype.card (Fin 1) := by
  rw [Set.univ_eq_empty_iff.2 inferInstance, uniformOn_empty_meas]
  simp

/-! ### The exact collision bound for random populations -/

-- For three distinct values sampled twice, the all-distinct event has mass `1` without
-- replacement.
example :
    sampleWithoutReplacement (ι := Fin 2) (Measure.dirac (id : Fin 3 → Fin 3))
      {f | Injective f} = 1 :=
  sampleWithoutReplacement_dirac_injective_apply_eq_one injective_id (Fin.castLEEmb (by decide))
    .of_discrete

/-- For three distinct values sampled twice, the all-distinct event has mass `2/3` with
replacement. -/
theorem sampleWithReplacement_dirac_id_fin_three_injective :
    sampleWithReplacement (ι := Fin 2) (Measure.dirac (id : Fin 3 → Fin 3))
      {f | Injective f} = 2 / 3 := by
  rw [sampleWithReplacement_dirac_injective_apply_eq injective_id .of_discrete,
    ENNReal.div_eq_div_iff] <;> norm_num [Nat.descFactorial]

-- The all-distinct event attains the exact error `1/3`: its mass without replacement is its mass
-- with replacement plus `1/3`.
example :
    sampleWithoutReplacement (ι := Fin 2) (Measure.dirac (id : Fin 3 → Fin 3))
        {f | Injective f} =
      sampleWithReplacement (ι := Fin 2) (Measure.dirac (id : Fin 3 → Fin 3))
        {f | Injective f} + 1 / 3 := by
  rw [sampleWithoutReplacement_dirac_injective_apply_eq_one injective_id
    (Fin.castLEEmb (by decide)) .of_discrete, sampleWithReplacement_dirac_id_fin_three_injective,
    ENNReal.div_add_div_same, show (2 : ℝ≥0∞) + 1 = 3 by norm_num,
    ENNReal.div_self (by norm_num) (by norm_num)]

/-- For `n = 4`, `m = 3` the collision probability is `1 - 24/64 = 5/8`. -/
theorem one_sub_descFactorial_div_pow_four_three :
    1 - (Fintype.card (Fin 4)).descFactorial (Fintype.card (Fin 3)) /
      (Fintype.card (Fin 4) : ℝ≥0∞) ^ Fintype.card (Fin 3) = 5 / 8 := by
  rw [← uniformOn_not_injective_apply_eq, ← ofReal_measureReal,
    uniformOn_real_not_injective_apply_eq]
  norm_num [Nat.descFactorial, ENNReal.ofReal_div_of_pos]

-- For every random population of four values and every event, sampling three values without
-- replacement exceeds sampling with replacement by at most `5/8`, in either direction.
example {α : Type*} [MeasurableSpace α] (ρ : Measure (Fin 4 → α)) [IsProbabilityMeasure ρ]
    (A : Set (Fin 3 → α)) :
    sampleWithoutReplacement ρ A ≤ sampleWithReplacement ρ A + 5 / 8 ∧
      sampleWithReplacement ρ A ≤ sampleWithoutReplacement ρ A + 5 / 8 := by
  rw [← one_sub_descFactorial_div_pow_four_three]
  exact ⟨sampleWithoutReplacement_le_sampleWithReplacement_add_exact_collision A,
    sampleWithReplacement_le_sampleWithoutReplacement_add_exact_collision A⟩

-- The exact error `5/8` is below the union bound `choose 3 2 / 4 = 3/4`.
example : (5 / 8 : ℝ≥0∞) <
    (Fintype.card (Fin 3)).choose 2 / (Fintype.card (Fin 4) : ℝ≥0∞) := by
  norm_num [Nat.choose]
  rw [← ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by norm_num) (by norm_num))
    (ENNReal.div_ne_top (by norm_num) (by norm_num))]
  norm_num [ENNReal.toReal_div]

/-! ### Exact-collision finite de Finetti -/

/-- For `n = m = 2` the collision probability is `1 - 2/4 = 1/2`. -/
theorem one_sub_descFactorial_div_pow_two_two :
    1 - (Nat.descFactorial 2 2 : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 2 = 1 / 2 := by
  simpa using (uniformOn_not_injective_apply_eq (ι := Fin 2) (κ := Fin 2)).symm.trans <| by
    rw [← ofReal_measureReal, uniformOn_real_not_injective_apply_eq]
    norm_num [Nat.descFactorial, ENNReal.ofReal_div_of_pos]

-- For a process exchangeable at `n = 2`, the two-term prefix law and the with-replacement sample
-- of the same prefix differ by at most `1 - 2/4 = 1/2` on every event.
example {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → α} (h : ExchangeableAt μ X 2)
    (hX : ∀ i : Fin 2, AEMeasurable (X i.val) μ) (A : Set (Fin 2 → α)) :
    prefixLaw μ X 2 A ≤ sampleWithReplacement (ι := Fin 2) (prefixLaw μ X 2) A + 1 / 2 ∧
      sampleWithReplacement (ι := Fin 2) (prefixLaw μ X 2) A ≤ prefixLaw μ X 2 A + 1 / 2 := by
  simpa only [Nat.cast_ofNat, one_sub_descFactorial_div_pow_two_two] using
    h.finiteDeFinetti_exact_collision le_rfl hX A

-- For one term the error `1 - n / n` vanishes, and the with-replacement sample of the `n`-prefix
-- law is the one-term prefix law.
example {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → α} {n : ℕ} (h : ExchangeableAt μ X n) (hn : 1 ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    1 - (n.descFactorial 1 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 1 = 0 ∧
      sampleWithReplacement (ι := Fin 1) (prefixLaw μ X n) = prefixLaw μ X 1 := by
  refine ⟨?_, h.sampleWithReplacement_eq_prefixLaw_of_le_one le_rfl hn hX⟩
  rw [Nat.descFactorial_one, pow_one, ENNReal.div_self (by simp; omega) (by simp), tsub_self]

-- A uniformly random ordering of two distinct values attains the error `1/2`: its two-term prefix
-- law exceeds the with-replacement sample of its prefix by exactly `1/2`.
example [MeasurableSpace (Equiv.Perm (Fin 2))] [MeasurableSingletonClass (Equiv.Perm (Fin 2))] :
    (⨆ (A : Set (Fin 2 → Fin 2)) (_ : MeasurableSet A),
      prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin 2))))
          (permutedPopulation id 0) 2 A -
        sampleWithReplacement (ι := Fin 2)
          (prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin 2))))
            (permutedPopulation id 0) 2) A) = 1 / 2 := by
  rw [iSup_prefixLaw_sub_sampleWithReplacement_permutedPopulation_eq le_rfl injective_id
    .of_discrete]
  exact_mod_cast one_sub_descFactorial_div_pow_two_two

-- For `n = m = 2` and distinct values, the exchangeable process attaining the bound gives the
-- all-distinct event mass `1` under its prefix law and `2/4` under the with-replacement sample.
example : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
    (X : ℕ → Ω → Fin 2), ExchangeableAt μ X 2 ∧ (∀ i, Measurable (X i)) ∧
      prefixLaw μ X 2 {f | Injective f} = 1 ∧
      sampleWithReplacement (ι := Fin 2) (prefixLaw μ X 2) {f | Injective f} = 2 / 4 := by
  simpa [Nat.descFactorial, show (2 : ℝ≥0∞) ^ 2 = 4 by norm_num] using
    exists_exchangeableAt_attains_collision (m := 2) le_rfl (id : Fin 2 → Fin 2) injective_id
      .of_discrete

-- For `n = m = 0` both masses are `1`: the empty word is all-distinct.
example {α : Type*} [MeasurableSpace α] [Nonempty α] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → α), ExchangeableAt μ X 0 ∧ (∀ i, Measurable (X i)) ∧
        prefixLaw μ X 0 {f | Injective f} = 1 ∧
        sampleWithReplacement (ι := Fin 0) (prefixLaw μ X 0) {f | Injective f} = 1 := by
  have hI : {f : Fin 0 → α | Injective f} = Set.univ :=
    Set.eq_univ_of_forall fun f => injective_of_subsingleton f
  simpa using exists_exchangeableAt_attains_collision (m := 0) le_rfl (Fin.elim0 : Fin 0 → α)
    (injective_of_subsingleton _) (hI ▸ .univ)

/-! ### Samples of size at most one, and the measurability of the all-distinct event -/

-- For samples of size at most one, `p = 1` and a distinct-valued population has excess `0`.
example {α ι κ : Type*} [MeasurableSpace α] [Fintype ι] [Subsingleton ι] [Fintype κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] {x : κ → α} (hx : Injective x)
    (e : ι ↪ κ) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac x) A -
        sampleWithReplacement (Measure.dirac x) A) = 0 := by
  have : Nonempty (ι → κ) := ⟨e⟩
  have hI : {f : ι → α | Injective f} = Set.univ :=
    Set.eq_univ_of_forall fun f => injective_of_subsingleton f
  rw [iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq hx e (hI ▸ .univ),
    ← uniformOn_not_injective_apply_eq, uniformOn_not_injective_eq_zero_of_subsingleton]

-- Under the trivial σ-algebra on values, whose product is again trivial, words of length at least
-- two with distinct letters form a nonempty proper subset, so they are not measurable.
example {ι α : Type*} [Nontrivial ι] (e : ι ↪ α) :
    ¬ MeasurableSet[MeasurableSpace.pi (X := fun _ : ι => α) (m := fun _ => ⊥)]
      {f : ι → α | Injective f} := by
  have hbot : MeasurableSpace.pi (X := fun _ : ι => α) (m := fun _ => ⊥) = ⊥ := by
    simp [MeasurableSpace.pi, MeasurableSpace.comap_bot]
  rw [hbot, MeasurableSpace.measurableSet_bot_iff]
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  rintro (h | h)
  · exact (Set.eq_empty_iff_forall_notMem.1 h) e e.injective
  · exact hij (Set.eq_univ_iff_forall.1 h (fun _ => e i) rfl)

-- Under the trivial σ-algebra on values, sampling any three values twice has excess `0`, even
-- for distinct values whose collision probability is `1/3`: the only measurable events are `∅`
-- and `univ`.
example {α : Type*} {x : Fin 3 → α} :
    letI : MeasurableSpace α := ⊥
    (⨆ (A : Set (Fin 2 → α)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac x) A -
        sampleWithReplacement (Measure.dirac x) A) = 0 := by
  let : MeasurableSpace α := ⊥
  have := isProbabilityMeasure_sampleWithoutReplacement (ι := Fin 2) (Measure.dirac x)
    (Fin.castLEEmb (by decide))
  have := isProbabilityMeasure_sampleWithReplacement (ι := Fin 2) (Measure.dirac x)
  refine le_antisymm (iSup₂_le fun A hA => ?_) bot_le
  have hbot : MeasurableSpace.pi (X := fun _ : Fin 2 => α) (m := fun _ => ⊥) = ⊥ := by
    simp [MeasurableSpace.pi, MeasurableSpace.comap_bot]
  have hA' : MeasurableSet[⊥] A := hbot ▸ hA
  rcases MeasurableSpace.measurableSet_bot_iff.1 hA' with rfl | rfl <;>
    simp only [measure_empty, measure_univ, tsub_self, le_refl]

end TauCeti.Examples.PopulationSampling
