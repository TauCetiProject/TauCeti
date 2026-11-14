/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
public import TauCeti.Probability.Exchangeability.Basic
public import TauCeti.Probability.PopulationSampling.Finite
import TauCeti.Probability.Distributions.Uniform.Permutation
import TauCeti.Probability.PopulationSampling.Distinct

/-!
# Exchangeable processes from uniformly permuted finite populations

Drawing a permutation `π : Equiv.Perm (Fin n)` uniformly at random and reading a deterministic
population `x : Fin n → α` along `π` produces the canonical `n`-exchangeable process: its first `n`
coordinates sample `x` in a uniformly random order without replacement, and for every `m ≤ n` its
`m`-prefix law is `sampleWithoutReplacement (ι := Fin m) (Measure.dirac x)`. Moreover, sampling
with replacement from its `n`-prefix law recovers `sampleWithReplacement (Measure.dirac x)`, since
the empirical multiset of `x ∘ π` is invariant under every permutation `π`.

When the entries of `x` are pairwise distinct and the all-distinct event
`{f : Fin m → α | Function.Injective f}` is measurable, this construction attains the exact
collision error `1 - n.descFactorial m / n ^ m` of the finite de Finetti theorem
(`ExchangeableAt.finiteDeFinetti_exact_collision`), and twice that error in Mathlib's total
variation distance `etvDist`
(`ExchangeableAt.etvDist_prefixLaw_sampleWithReplacement_le_exact_collision`).

The law and sharpness results are proved first in a probability-space-agnostic form assuming only
`HasLaw π (uniformOn Set.univ) μ` and almost-sure coordinate agreement on `Fin n`, then specialized
to the concrete process `permutedPopulationProcess x a₀` on `Equiv.Perm (Fin n)` and packaged as
the existential attainment theorem `exists_exchangeableAt_attains_collision`.

## Main declarations

* `blockLaw_eq_sampleWithoutReplacement_dirac_of_hasLaw_perm`: any injective block of a family
  almost surely read from `x` along a uniform permutation has law
  `sampleWithoutReplacement (Measure.dirac x)`;
* `ExchangeableAt.of_hasLaw_perm`: any process whose first `n` coordinates agree almost surely with
  a uniformly permuted `n`-population is exchangeable at `n`;
* `prefixLaw_eq_sampleWithoutReplacement_dirac_of_hasLaw_perm`,
  `sampleWithReplacement_prefixLaw_eq_dirac_of_hasLaw_perm`: its `m`-prefix law (`m ≤ n`) and
  with-replacement empirical-mixture law;
* `iSup_prefixLaw_sub_sampleWithReplacement_eq_of_hasLaw_perm`,
  `etvDist_prefixLaw_sampleWithReplacement_eq_of_hasLaw_perm`: exact excess and `etvDist`
  attainment for distinct population values;
* `permutedPopulationProcess`: canonical process on `Equiv.Perm (Fin n)` padded by `a₀` from `n`
  onward;
* `exists_exchangeableAt_prefixLaw_eq_sampleWithoutReplacement_dirac`: realization of any
  deterministic finite population `x : κ → α` by a `(Fintype.card κ)`-exchangeable process;
* `exists_exchangeableAt_attains_collision`: existence of an `n`-exchangeable process attaining the
  exact finite de Finetti collision bound.

## References

* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764, Theorem 13.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

section HasLawPerm

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω}

/-- Along any injective selection `k : Fin m → κ`, a family almost surely read from a finite
population `x : κ → α` through a uniform random permutation `π` has block law equal to sampling `x`
without replacement. -/
theorem blockLaw_eq_sampleWithoutReplacement_dirac_of_hasLaw_perm {κ : Type*} [Finite κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    [MeasurableSpace (Equiv.Perm κ)] [MeasurableSingletonClass (Equiv.Perm κ)]
    {π : Ω → Equiv.Perm κ} (hπ : HasLaw π (uniformOn Set.univ) μ)
    {Y : κ → Ω → α} {x : κ → α} (hY : ∀ j : κ, Y j =ᵐ[μ] fun ω => x (π ω j))
    {m : ℕ} {k : Fin m → κ} (hk : Function.Injective k) :
    blockLaw μ Y k = sampleWithoutReplacement (ι := Fin m) (Measure.dirac x) := by
  have hcongr : blockLaw μ Y k = μ.map (fun ω i => x (π ω (k i))) := by
    rw [blockLaw_def]
    refine Measure.map_congr ?_
    filter_upwards [ae_all_iff.2 fun i : Fin m => hY (k i)] with ω hω using funext hω
  have hlaw : HasLaw (fun ω i => x (π ω (k i)))
      ((uniformOn {f : Fin m → κ | Function.Injective f}).map fun f i => x (f i)) μ :=
    (hasLaw_map (measurable_readPopulation x).aemeasurable).comp
      (hπ.comp_embedding_uniformOn_perm ⟨k, hk⟩)
  rw [hcongr, hlaw.map_eq, sampleWithoutReplacement_dirac]

section FinPopulation

variable {n : ℕ}
  [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))]
  {π : Ω → Equiv.Perm (Fin n)} {X : ℕ → Ω → α} {x : Fin n → α}

/-- Coordinates almost surely read from a finite population along a random permutation with law
`uniformOn Set.univ` are almost everywhere measurable. -/
theorem aemeasurable_of_hasLaw_perm (hπ : HasLaw π (uniformOn Set.univ) μ)
    (hX : ∀ i : Fin n, X i.val =ᵐ[μ] fun ω => x (π ω i)) (i : Fin n) :
    AEMeasurable (X i.val) μ :=
  ((measurable_of_countable fun τ : Equiv.Perm (Fin n) => x (τ i)).comp_aemeasurable
    hπ.aemeasurable).congr (hX i).symm

/-- **Exchangeability of a uniformly permuted finite population.** Any process whose first `n`
coordinates agree almost surely with reading `x : Fin n → α` along a uniform random permutation is
exchangeable at `n`. -/
theorem ExchangeableAt.of_hasLaw_perm (hπ : HasLaw π (uniformOn Set.univ) μ)
    (hX : ∀ i : Fin n, X i.val =ᵐ[μ] fun ω => x (π ω i)) :
    ExchangeableAt μ X n := by
  intro σ
  have hσ : blockLaw μ X (fun i : Fin n => (σ i).val) =
      blockLaw μ (fun j : Fin n => X j.val) σ := by
    rw [blockLaw_def, blockLaw_def]
  have hid : prefixLaw μ X n =
      blockLaw μ (fun j : Fin n => X j.val) id := by
    rw [prefixLaw_def, blockLaw_def, blockLaw_def]
    rfl
  rw [hσ, hid, blockLaw_eq_sampleWithoutReplacement_dirac_of_hasLaw_perm hπ hX σ.injective,
    blockLaw_eq_sampleWithoutReplacement_dirac_of_hasLaw_perm hπ hX Function.injective_id]

/-- For `m ≤ n`, the `m`-prefix law of a process whose first `n` coordinates almost surely read
`x : Fin n → α` along a uniform random permutation is without-replacement sampling from `x`. -/
theorem prefixLaw_eq_sampleWithoutReplacement_dirac_of_hasLaw_perm
    (hπ : HasLaw π (uniformOn Set.univ) μ)
    (hX : ∀ i : Fin n, X i.val =ᵐ[μ] fun ω => x (π ω i)) {m : ℕ} (hmn : m ≤ n) :
    prefixLaw μ X m = sampleWithoutReplacement (ι := Fin m) (Measure.dirac x) := by
  have hcast : prefixLaw μ X m =
      blockLaw μ (fun j : Fin n => X j.val) (Fin.castLE hmn) := by
    rw [prefixLaw_def, blockLaw_def, blockLaw_def]
    rfl
  rw [hcast,
    blockLaw_eq_sampleWithoutReplacement_dirac_of_hasLaw_perm hπ hX (Fin.castLE_injective hmn)]

/-- Sampling with replacement from the `n`-prefix law of a uniformly permuted `n`-population has
the same law as sampling with replacement directly from the deterministic population `x`. -/
theorem sampleWithReplacement_prefixLaw_eq_dirac_of_hasLaw_perm {ι : Type*} [Fintype ι]
    (hπ : HasLaw π (uniformOn Set.univ) μ)
    (hX : ∀ i : Fin n, X i.val =ᵐ[μ] fun ω => x (π ω i)) :
    sampleWithReplacement (ι := ι) (prefixLaw μ X n) =
      sampleWithReplacement (ι := ι) (Measure.dirac x) := by
  rw [prefixLaw_eq_sampleWithoutReplacement_dirac_of_hasLaw_perm hπ hX le_rfl,
    sampleWithReplacement_sampleWithoutReplacement_self]

/-- For a population of distinct values, the `m`-prefix (`m ≤ n`) of a uniformly permuted
population has pairwise distinct entries with probability one. -/
theorem prefixLaw_injective_apply_eq_one_of_hasLaw_perm
    (hπ : HasLaw π (uniformOn Set.univ) μ)
    (hX : ∀ i : Fin n, X i.val =ᵐ[μ] fun ω => x (π ω i))
    {m : ℕ} (hmn : m ≤ n) (hx : Function.Injective x)
    (hI : MeasurableSet {f : Fin m → α | Function.Injective f}) :
    prefixLaw μ X m {f | Function.Injective f} = 1 := by
  rw [prefixLaw_eq_sampleWithoutReplacement_dirac_of_hasLaw_perm hπ hX hmn]
  exact sampleWithoutReplacement_dirac_injective_apply_eq_one hx
    ⟨Fin.castLE hmn, Fin.castLE_injective hmn⟩ hI

/-- For a population of distinct values, sampling `m` entries with replacement from the `n`-prefix
law of a uniformly permuted population produces pairwise distinct entries with probability
`n.descFactorial m / n ^ m`. -/
theorem sampleWithReplacement_prefixLaw_injective_apply_eq_of_hasLaw_perm
    (hπ : HasLaw π (uniformOn Set.univ) μ)
    (hX : ∀ i : Fin n, X i.val =ᵐ[μ] fun ω => x (π ω i))
    {m : ℕ} (hx : Function.Injective x)
    (hI : MeasurableSet {f : Fin m → α | Function.Injective f}) :
    sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) {f | Function.Injective f} =
      n.descFactorial m / (n : ℝ≥0∞) ^ m := by
  rw [sampleWithReplacement_prefixLaw_eq_dirac_of_hasLaw_perm hπ hX,
    sampleWithReplacement_dirac_injective_apply_eq hx hI, Fintype.card_fin, Fintype.card_fin]

/-- For a population of distinct values and `m ≤ n`, the largest measurable-event excess of the
`m`-prefix law over the with-replacement sample of the `n`-prefix law equals the exact collision
probability `1 - n.descFactorial m / n ^ m`. -/
theorem iSup_prefixLaw_sub_sampleWithReplacement_eq_of_hasLaw_perm
    (hπ : HasLaw π (uniformOn Set.univ) μ)
    (hX : ∀ i : Fin n, X i.val =ᵐ[μ] fun ω => x (π ω i))
    {m : ℕ} (hmn : m ≤ n) (hx : Function.Injective x)
    (hI : MeasurableSet {f : Fin m → α | Function.Injective f}) :
    (⨆ (A : Set (Fin m → α)) (_ : MeasurableSet A),
        prefixLaw μ X m A - sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A) =
      1 - n.descFactorial m / (n : ℝ≥0∞) ^ m := by
  rw [prefixLaw_eq_sampleWithoutReplacement_dirac_of_hasLaw_perm hπ hX hmn,
    sampleWithReplacement_prefixLaw_eq_dirac_of_hasLaw_perm hπ hX,
    iSup_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq hx
      ⟨Fin.castLE hmn, Fin.castLE_injective hmn⟩ hI,
    Fintype.card_fin, Fintype.card_fin]

/-- For a population of distinct values and `m ≤ n`, Mathlib's total variation distance `etvDist`
between the `m`-prefix law and the with-replacement sample of the `n`-prefix law equals twice the
exact collision probability `2 * (1 - n.descFactorial m / n ^ m)`. -/
theorem etvDist_prefixLaw_sampleWithReplacement_eq_of_hasLaw_perm
    (hπ : HasLaw π (uniformOn Set.univ) μ)
    (hX : ∀ i : Fin n, X i.val =ᵐ[μ] fun ω => x (π ω i))
    {m : ℕ} (hmn : m ≤ n) (hx : Function.Injective x)
    (hI : MeasurableSet {f : Fin m → α | Function.Injective f}) :
    etvDist (prefixLaw μ X m) (sampleWithReplacement (ι := Fin m) (prefixLaw μ X n)) =
      2 * (1 - n.descFactorial m / (n : ℝ≥0∞) ^ m) := by
  rw [prefixLaw_eq_sampleWithoutReplacement_dirac_of_hasLaw_perm hπ hX hmn,
    sampleWithReplacement_prefixLaw_eq_dirac_of_hasLaw_perm hπ hX,
    etvDist_sampleWithoutReplacement_sampleWithReplacement_dirac_eq hx
      ⟨Fin.castLE hmn, Fin.castLE_injective hmn⟩ hI,
    Fintype.card_fin, Fintype.card_fin]

end FinPopulation

end HasLawPerm

section PermutedPopulationProcess

/-- The canonical process on `Equiv.Perm (Fin n)` whose `i`-th coordinate reads `x (σ ⟨i, hi⟩)`
for `i < n` and takes a fixed padding value `a₀` for `i ≥ n`. -/
def permutedPopulationProcess {α : Type*} {n : ℕ} (x : Fin n → α) (a₀ : α) (i : ℕ)
    (σ : Equiv.Perm (Fin n)) : α :=
  if hi : i < n then x (σ ⟨i, hi⟩) else a₀

/-- The defining piecewise formula for `permutedPopulationProcess`. -/
theorem permutedPopulationProcess_def {α : Type*} {n : ℕ} (x : Fin n → α) (a₀ : α) (i : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    permutedPopulationProcess x a₀ i σ = if hi : i < n then x (σ ⟨i, hi⟩) else a₀ :=
  (rfl)

/-- Below `n`, `permutedPopulationProcess` reads `x` at the permuted coordinate. -/
theorem permutedPopulationProcess_apply_lt {α : Type*} {n i : ℕ} (x : Fin n → α) (a₀ : α)
    (hi : i < n) (σ : Equiv.Perm (Fin n)) :
    permutedPopulationProcess x a₀ i σ = x (σ ⟨i, hi⟩) :=
  dite_eq_left hi

/-- On `Fin n`, `permutedPopulationProcess` reads `x` at `σ i`. -/
@[simp]
theorem permutedPopulationProcess_apply_fin {α : Type*} {n : ℕ} (x : Fin n → α) (a₀ : α)
    (i : Fin n) (σ : Equiv.Perm (Fin n)) :
    permutedPopulationProcess x a₀ i.val σ = x (σ i) :=
  dite_eq_left i.isLt

/-- From index `n` onward, `permutedPopulationProcess` returns the padding value `a₀`. -/
theorem permutedPopulationProcess_apply_of_le {α : Type*} {n i : ℕ} (x : Fin n → α) (a₀ : α)
    (hi : n ≤ i) (σ : Equiv.Perm (Fin n)) :
    permutedPopulationProcess x a₀ i σ = a₀ :=
  dite_eq_right (Nat.not_lt.mpr hi)

private theorem hasLaw_id_uniformOn_perm {n : ℕ} [MeasurableSpace (Equiv.Perm (Fin n))] :
    HasLaw (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n))
      (uniformOn Set.univ) (uniformOn Set.univ) :=
  ⟨measurable_id.aemeasurable, Measure.map_id⟩

variable {α : Type*} [MeasurableSpace α] {n : ℕ}
  [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))]

/-- Each coordinate of `permutedPopulationProcess` is measurable when `Equiv.Perm (Fin n)` has
measurable singletons. -/
theorem measurable_permutedPopulationProcess (x : Fin n → α) (a₀ : α) (i : ℕ) :
    Measurable (permutedPopulationProcess x a₀ i) :=
  measurable_of_countable _

/-- Under the uniform measure on `Equiv.Perm (Fin n)`, `permutedPopulationProcess x a₀` is
exchangeable at `n`. -/
theorem exchangeableAt_permutedPopulationProcess (x : Fin n → α) (a₀ : α) :
    ExchangeableAt (uniformOn Set.univ) (permutedPopulationProcess x a₀) n :=
  ExchangeableAt.of_hasLaw_perm hasLaw_id_uniformOn_perm fun i =>
    Filter.Eventually.of_forall (permutedPopulationProcess_apply_fin x a₀ i)

/-- Under the uniform measure on `Equiv.Perm (Fin n)`, the `m`-prefix law (`m ≤ n`) of
`permutedPopulationProcess x a₀` is without-replacement sampling from `x`. -/
theorem prefixLaw_permutedPopulationProcess (x : Fin n → α) (a₀ : α) {m : ℕ} (hmn : m ≤ n) :
    prefixLaw (uniformOn Set.univ) (permutedPopulationProcess x a₀) m =
      sampleWithoutReplacement (ι := Fin m) (Measure.dirac x) :=
  prefixLaw_eq_sampleWithoutReplacement_dirac_of_hasLaw_perm hasLaw_id_uniformOn_perm
    (fun i => Filter.Eventually.of_forall (permutedPopulationProcess_apply_fin x a₀ i)) hmn

/-- Sampling with replacement from the `n`-prefix law of `permutedPopulationProcess x a₀` recovers
with-replacement sampling from `x`. -/
theorem sampleWithReplacement_prefixLaw_permutedPopulationProcess {ι : Type*} [Fintype ι]
    (x : Fin n → α) (a₀ : α) :
    sampleWithReplacement (ι := ι)
        (prefixLaw (uniformOn Set.univ) (permutedPopulationProcess x a₀) n) =
      sampleWithReplacement (ι := ι) (Measure.dirac x) :=
  sampleWithReplacement_prefixLaw_eq_dirac_of_hasLaw_perm hasLaw_id_uniformOn_perm fun i =>
    Filter.Eventually.of_forall (permutedPopulationProcess_apply_fin x a₀ i)

/-- For distinct population values and `m ≤ n`, `permutedPopulationProcess` attains the exact
finite de Finetti collision error in measurable-event excess. -/
theorem iSup_prefixLaw_sub_sampleWithReplacement_permutedPopulationProcess
    (x : Fin n → α) (a₀ : α) {m : ℕ} (hmn : m ≤ n) (hx : Function.Injective x)
    (hI : MeasurableSet {f : Fin m → α | Function.Injective f}) :
    (⨆ (A : Set (Fin m → α)) (_ : MeasurableSet A),
        prefixLaw (uniformOn Set.univ) (permutedPopulationProcess x a₀) m A -
          sampleWithReplacement (ι := Fin m)
            (prefixLaw (uniformOn Set.univ) (permutedPopulationProcess x a₀) n) A) =
      1 - n.descFactorial m / (n : ℝ≥0∞) ^ m :=
  iSup_prefixLaw_sub_sampleWithReplacement_eq_of_hasLaw_perm hasLaw_id_uniformOn_perm
    (fun i => Filter.Eventually.of_forall (permutedPopulationProcess_apply_fin x a₀ i)) hmn hx hI

/-- For distinct population values and `m ≤ n`, `permutedPopulationProcess` attains twice the exact
collision probability in Mathlib's total variation distance `etvDist`. -/
theorem etvDist_prefixLaw_sampleWithReplacement_permutedPopulationProcess
    (x : Fin n → α) (a₀ : α) {m : ℕ} (hmn : m ≤ n) (hx : Function.Injective x)
    (hI : MeasurableSet {f : Fin m → α | Function.Injective f}) :
    etvDist (prefixLaw (uniformOn Set.univ) (permutedPopulationProcess x a₀) m)
        (sampleWithReplacement (ι := Fin m)
          (prefixLaw (uniformOn Set.univ) (permutedPopulationProcess x a₀) n)) =
      2 * (1 - n.descFactorial m / (n : ℝ≥0∞) ^ m) :=
  etvDist_prefixLaw_sampleWithReplacement_eq_of_hasLaw_perm hasLaw_id_uniformOn_perm
    (fun i => Filter.Eventually.of_forall (permutedPopulationProcess_apply_fin x a₀ i)) hmn hx hI

end PermutedPopulationProcess

/-- Any deterministic finite population `x : κ → α` in a nonempty measurable space is realized by a
`(Fintype.card κ)`-exchangeable measurable process on a probability space whose `m`-prefix laws
(`m ≤ Fintype.card κ`) equal `sampleWithoutReplacement (Measure.dirac x)` and whose with-replacement
empirical-mixture laws equal `sampleWithReplacement (Measure.dirac x)`. -/
theorem exists_exchangeableAt_prefixLaw_eq_sampleWithoutReplacement_dirac
    {α κ : Type*} [MeasurableSpace α] [Nonempty α]
    [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] (x : κ → α) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → α),
        ExchangeableAt μ X (Fintype.card κ) ∧ (∀ i, Measurable (X i)) ∧
          (∀ {m : ℕ}, m ≤ Fintype.card κ →
            prefixLaw μ X m = sampleWithoutReplacement (ι := Fin m) (Measure.dirac x)) ∧
          ∀ {m : ℕ},
            sampleWithReplacement (ι := Fin m) (prefixLaw μ X (Fintype.card κ)) =
              sampleWithReplacement (ι := Fin m) (Measure.dirac x) := by
  obtain ⟨a₀⟩ := ‹Nonempty α›
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let ms : MeasurableSpace (Equiv.Perm (Fin (Fintype.card κ))) := ⊤
  refine ⟨Equiv.Perm (Fin (Fintype.card κ)), ms, uniformOn Set.univ, inferInstance,
    permutedPopulationProcess (x ∘ e) a₀,
    exchangeableAt_permutedPopulationProcess (x ∘ e) a₀,
    measurable_permutedPopulationProcess (x ∘ e) a₀, ?_, ?_⟩
  · intro m hmn
    rw [prefixLaw_permutedPopulationProcess (x ∘ e) a₀ hmn,
      sampleWithoutReplacement_dirac_comp_equiv x e]
  · intro m
    rw [sampleWithReplacement_prefixLaw_permutedPopulationProcess (x ∘ e) a₀,
      sampleWithReplacement_dirac_comp_equiv x e]

/-- **Attainment of the exact finite de Finetti collision bound.** For every population
`x : Fin n → α` of distinct values in a nonempty measurable space and every `m ≤ n`, when the
all-distinct event is measurable there exists an `n`-exchangeable measurable process on a
probability space whose `m`-prefix law gives the all-distinct event mass one while the
with-replacement sample of its `n`-prefix law gives it mass `n.descFactorial m / n ^ m`. -/
theorem exists_exchangeableAt_attains_collision {α : Type*} [MeasurableSpace α] [Nonempty α]
    {m n : ℕ} (hmn : m ≤ n) (x : Fin n → α) (hx : Function.Injective x)
    (hA : MeasurableSet {f : Fin m → α | Function.Injective f}) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → α), ExchangeableAt μ X n ∧ (∀ i, Measurable (X i)) ∧
        prefixLaw μ X m {f | Function.Injective f} = 1 ∧
        sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) {f | Function.Injective f} =
          n.descFactorial m / (n : ℝ≥0∞) ^ m := by
  obtain ⟨a₀⟩ := ‹Nonempty α›
  let ms : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  refine ⟨Equiv.Perm (Fin n), ms, uniformOn Set.univ, inferInstance,
    permutedPopulationProcess x a₀,
    exchangeableAt_permutedPopulationProcess x a₀,
    measurable_permutedPopulationProcess x a₀, ?_, ?_⟩
  · exact prefixLaw_injective_apply_eq_one_of_hasLaw_perm hasLaw_id_uniformOn_perm
      (fun i => Filter.Eventually.of_forall (permutedPopulationProcess_apply_fin x a₀ i)) hmn hx hA
  · exact sampleWithReplacement_prefixLaw_injective_apply_eq_of_hasLaw_perm
      hasLaw_id_uniformOn_perm
      (fun i => Filter.Eventually.of_forall (permutedPopulationProcess_apply_fin x a₀ i)) hx hA

end TauCeti.Probability
