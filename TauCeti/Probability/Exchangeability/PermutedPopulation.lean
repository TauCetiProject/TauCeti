/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.FiniteDeFinetti
public import TauCeti.Probability.PopulationSampling.Distinct
public import TauCeti.Probability.PopulationSampling.Reindex
import Mathlib.Data.Fin.Embedding

/-!
# Uniformly permuted finite populations and sharpness of finite de Finetti

Any deterministic finite population `x : Fin n → α` gives rise to a process exchangeable at
length `n`: draw a uniformly random permutation `σ : Equiv.Perm (Fin n)`, emit `x (σ i)` at
coordinates `i < n`, and emit a fixed padding value `d : α` from coordinate `n` onwards.

For every `m ≤ n`, the `m`-prefix law of this process is `sampleWithoutReplacement` from the
deterministic population `x`, whereas sampling `m` entries with replacement from its `n`-prefix
law recovers `sampleWithReplacement` from `x`. Neither identity requires `x` to have distinct
values, so the construction models arbitrary finite exchangeable urn processes with deterministic
composition.

When `x` is injective and the set of injective `m`-tuples is measurable, the all-distinct event
has mass `1` under the `m`-prefix law and mass `n.descFactorial m / n ^ m` under the
with-replacement sample of the `n`-prefix law. Consequently the exact-collision finite de Finetti
bound `ExchangeableAt.finiteDeFinetti_exact_collision` and its total-variation form
`ExchangeableAt.etvDist_prefixLaw_sampleWithReplacement_le_exact_collision` hold with equality.

## Main declarations

* `permutedPopulation`: the process reading a finite population in random permutation order on
  its first `n` coordinates and a constant padding value thereafter.
* `exchangeableAt_permutedPopulation`: exchangeability at length `n` under the uniform law on
  `Equiv.Perm (Fin n)`.
* `prefixLaw_permutedPopulation_of_le`, `sampleWithReplacement_prefixLaw_permutedPopulation`:
  exact identification of the prefix and empirical-mixture laws with `sampleWithoutReplacement`
  and `sampleWithReplacement` from `Measure.dirac x`.
* `iSup_prefixLaw_sub_sampleWithReplacement_permutedPopulation_eq`,
  `etvDist_prefixLaw_sampleWithReplacement_permutedPopulation_eq`: exact excess and
  total-variation distance for distinct population values.
* `exists_exchangeableAt_attains_collision`: existential sharpness witness for the exact-collision
  finite de Finetti bound.

## References

* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764, Theorem 13.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

section Construction

variable {α : Type*} {m n : ℕ}

/-- Read a finite population `x : Fin n → α` in permutation order `σ` on coordinates below `n`,
and return a fixed padding value `d` from coordinate `n` onwards. -/
def permutedPopulation (x : Fin n → α) (d : α) (i : ℕ) (σ : Equiv.Perm (Fin n)) : α :=
  if h : i < n then x (σ ⟨i, h⟩) else d

/-- The piecewise definition of `permutedPopulation`. -/
theorem permutedPopulation_def (x : Fin n → α) (d : α) (i : ℕ) (σ : Equiv.Perm (Fin n)) :
    permutedPopulation x d i σ = if h : i < n then x (σ ⟨i, h⟩) else d :=
  (rfl)

/-- Below `n`, `permutedPopulation` reads the population at the permuted index. -/
@[simp]
theorem permutedPopulation_of_lt (x : Fin n → α) (d : α) {i : ℕ} (hi : i < n)
    (σ : Equiv.Perm (Fin n)) :
    permutedPopulation x d i σ = x (σ ⟨i, hi⟩) :=
  dite_eq_left hi

/-- From `n` onwards, `permutedPopulation` takes the constant padding value `d`. -/
@[simp]
theorem permutedPopulation_of_le (x : Fin n → α) (d : α) {i : ℕ} (hi : n ≤ i)
    (σ : Equiv.Perm (Fin n)) :
    permutedPopulation x d i σ = d :=
  dite_eq_right (Nat.not_lt.mpr hi)

variable [MeasurableSpace α]
  [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))]

/-- Each coordinate of `permutedPopulation` is measurable on any discrete measurable space of
permutations. -/
@[fun_prop]
theorem measurable_permutedPopulation (x : Fin n → α) (d : α) (i : ℕ) :
    Measurable (permutedPopulation x d i) :=
  measurable_of_countable _

/-- Along any embedding into `Fin n`, the block law of a uniformly permuted population is
sampling without replacement from that deterministic population. -/
theorem blockLaw_permutedPopulation_of_embedding (x : Fin n → α) (d : α) (e : Fin m ↪ Fin n) :
    blockLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin n)))) (permutedPopulation x d)
        (fun j : Fin m => (e j).val) =
      sampleWithoutReplacement (ι := Fin m) (Measure.dirac x) := by
  rw [blockLaw_def, ← map_readPopulation_comp_uniformOn_perm x e]
  congr 1
  funext σ j
  simp

/-- For `m ≤ n`, the `m`-prefix law of a uniformly permuted population of size `n` is sampling
`m` entries without replacement from `x`. -/
theorem prefixLaw_permutedPopulation_of_le (x : Fin n → α) (d : α) (hmn : m ≤ n) :
    prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin n)))) (permutedPopulation x d) m =
      sampleWithoutReplacement (ι := Fin m) (Measure.dirac x) := by
  simpa only [prefixLaw_def, Fin.coe_castLEEmb, Function.comp_apply, Fin.val_castLE] using
    blockLaw_permutedPopulation_of_embedding x d (Fin.castLEEmb hmn)

/-- The full `n`-prefix law of a uniformly permuted population of size `n` is full-population
sampling without replacement from `x`. -/
theorem prefixLaw_permutedPopulation_self (x : Fin n → α) (d : α) :
    prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin n)))) (permutedPopulation x d) n =
      sampleWithoutReplacement (ι := Fin n) (Measure.dirac x) :=
  prefixLaw_permutedPopulation_of_le x d le_rfl

/-- A uniformly permuted population of size `n` is exchangeable at length `n`. -/
theorem exchangeableAt_permutedPopulation (x : Fin n → α) (d : α) :
    ExchangeableAt (uniformOn (Set.univ : Set (Equiv.Perm (Fin n))))
      (permutedPopulation x d) n := by
  intro τ
  rw [prefixLaw_permutedPopulation_self]
  simpa using blockLaw_permutedPopulation_of_embedding x d τ.toEmbedding

/-- Sampling `m` entries with replacement from the `n`-prefix law of a uniformly permuted
population recovers sampling `m` entries with replacement from the deterministic population `x`. -/
theorem sampleWithReplacement_prefixLaw_permutedPopulation (x : Fin n → α) (d : α) :
    sampleWithReplacement (ι := Fin m)
        (prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin n))))
          (permutedPopulation x d) n) =
      sampleWithReplacement (ι := Fin m) (Measure.dirac x) := by
  rw [prefixLaw_permutedPopulation_self, sampleWithReplacement_sampleWithoutReplacement_self]

/-- For a population of distinct values and `m ≤ n`, the `m`-prefix law of the uniformly permuted
population gives the all-distinct event mass `1`. -/
theorem prefixLaw_permutedPopulation_injective_apply_eq_one (hmn : m ≤ n) {x : Fin n → α}
    {d : α} (hx : Function.Injective x)
    (hI : MeasurableSet {f : Fin m → α | Function.Injective f}) :
    prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin n)))) (permutedPopulation x d) m
        {f | Function.Injective f} = 1 := by
  rw [prefixLaw_permutedPopulation_of_le x d hmn]
  exact sampleWithoutReplacement_dirac_injective_apply_eq_one hx (Fin.castLEEmb hmn) hI

/-- For a population of distinct values, sampling `m` entries with replacement from the `n`-prefix
law of the uniformly permuted population gives the all-distinct event mass
`n.descFactorial m / n ^ m`. -/
theorem sampleWithReplacement_prefixLaw_permutedPopulation_injective_apply_eq {x : Fin n → α}
    {d : α} (hx : Function.Injective x)
    (hI : MeasurableSet {f : Fin m → α | Function.Injective f}) :
    sampleWithReplacement (ι := Fin m)
        (prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin n))))
          (permutedPopulation x d) n)
        {f | Function.Injective f} =
      n.descFactorial m / (n : ℝ≥0∞) ^ m := by
  rw [sampleWithReplacement_prefixLaw_permutedPopulation]
  simpa using sampleWithReplacement_dirac_injective_apply_eq (ι := Fin m) hx hI

/-- For a population of distinct values and `m ≤ n`, the largest eventwise excess of the
`m`-prefix law of `permutedPopulation x d` over the with-replacement sample of its `n`-prefix law
is `1 - n.descFactorial m / n ^ m`. -/
theorem iSup_prefixLaw_sub_sampleWithReplacement_permutedPopulation_eq (hmn : m ≤ n)
    {x : Fin n → α} {d : α} (hx : Function.Injective x)
    (hI : MeasurableSet {f : Fin m → α | Function.Injective f}) :
    (⨆ (A : Set (Fin m → α)) (_ : MeasurableSet A),
        prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin n))))
            (permutedPopulation x d) m A -
          sampleWithReplacement (ι := Fin m)
            (prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin n))))
              (permutedPopulation x d) n) A) =
      1 - n.descFactorial m / (n : ℝ≥0∞) ^ m := by
  rw [prefixLaw_permutedPopulation_of_le x d hmn,
    sampleWithReplacement_prefixLaw_permutedPopulation]
  simpa using iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq hx
    (Fin.castLEEmb hmn) hI

/-- For a population of distinct values and `m ≤ n`, Mathlib's total variation distance `etvDist`
between the `m`-prefix law of `permutedPopulation x d` and the with-replacement sample of its
`n`-prefix law is twice the exact collision probability. -/
theorem etvDist_prefixLaw_sampleWithReplacement_permutedPopulation_eq (hmn : m ≤ n)
    {x : Fin n → α} {d : α} (hx : Function.Injective x)
    (hI : MeasurableSet {f : Fin m → α | Function.Injective f}) :
    etvDist
      (prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin n)))) (permutedPopulation x d) m)
      (sampleWithReplacement (ι := Fin m)
        (prefixLaw (uniformOn (Set.univ : Set (Equiv.Perm (Fin n))))
          (permutedPopulation x d) n)) =
      2 * (1 - n.descFactorial m / (n : ℝ≥0∞) ^ m) := by
  rw [prefixLaw_permutedPopulation_of_le x d hmn,
    sampleWithReplacement_prefixLaw_permutedPopulation]
  simpa using etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq hx
    (Fin.castLEEmb hmn) hI

end Construction

/-- **Sharpness of exact-collision finite de Finetti.** For every `m ≤ n` and every population
`x : Fin n → α` of distinct values in a nonempty measurable space whose all-distinct `m`-tuples
form a measurable set, there is a probability space carrying a coordinatewise measurable process
exchangeable at `n` whose `m`-prefix law gives the all-distinct event mass `1` while the
with-replacement sample of its `n`-prefix law gives it mass `n.descFactorial m / n ^ m`. -/
theorem exists_exchangeableAt_attains_collision {α : Type*} [MeasurableSpace α] [Nonempty α]
    {m n : ℕ} (hmn : m ≤ n) (x : Fin n → α) (hx : Function.Injective x)
    (hA : MeasurableSet {f : Fin m → α | Function.Injective f}) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → α), ExchangeableAt μ X n ∧ (∀ i, Measurable (X i)) ∧
        prefixLaw μ X m {f | Function.Injective f} = 1 ∧
        sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) {f | Function.Injective f} =
          n.descFactorial m / (n : ℝ≥0∞) ^ m := by
  let _ : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have : MeasurableSingletonClass (Equiv.Perm (Fin n)) := ⟨fun _ => trivial⟩
  let d : α := Classical.arbitrary α
  exact ⟨Equiv.Perm (Fin n), ⊤, uniformOn Set.univ, inferInstance,
    permutedPopulation x d,
    exchangeableAt_permutedPopulation x d,
    measurable_permutedPopulation x d,
    prefixLaw_permutedPopulation_injective_apply_eq_one hmn hx hA,
    sampleWithReplacement_prefixLaw_permutedPopulation_injective_apply_eq hx hA⟩

end TauCeti.Probability
