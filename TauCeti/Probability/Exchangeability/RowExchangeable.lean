/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.DeFinetti.Theorem
public import TauCeti.Probability.Exchangeability.FullyExchangeable
public import TauCeti.Probability.Process.Array
public import TauCeti.Algebra.GroupAction.FiniteSupportPerm
-- Non-public: two finite-valued functions with equal second and mixed moments are a.e. equal.
import TauCeti.MeasureTheory.Function.AEEqOfLIntegralMul
-- Non-public: evaluating a random probability measure at a fixed measurable set is measurable.
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Ext
-- Non-public: equality of process laws is reduced to their finite-dimensional laws.
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Row exchangeable arrays and the factorization of their directing measure

An array `Y : ι × ℕ → Ω → α` is **row exchangeable** when its law is unchanged by permuting the
entries of each row separately: for every family `π : ι → Equiv.Perm ℕ` of time permutations, one
for each row, the array `(a, k) ↦ Y (a, π a k)` has the law of `Y`. This is the symmetry of the
array of successors of a Markov exchangeable process, and it is stronger than asking that each row
be exchangeable on its own, because the permutations may be chosen independently.

Reading an array column by column gives the process `arrayCol Y : ℕ → Ω → (ι → α)`, whose
`k`-th value is the vector of the `k`-th entries of all rows. Row exchangeability contains the
diagonal case `π = fun _ => σ`, so `arrayCol Y` is a fully exchangeable process valued in
`ι → α`, which for countable `ι` and standard Borel `α` is again standard Borel. De Finetti's
theorem therefore hands the columns a directing measure `λ : Ω → ProbabilityMeasure (ι → α)`.

The theorem of this file is that the extra, off-diagonal part of the symmetry makes that directing
measure **factor over the rows**: almost surely, its mass on a finite box
`{x | ∀ a ∈ F, x a ∈ B a}` is the product over `a ∈ F` of its one-row masses. So conditionally on
the directing measure distinct rows are independent, while the entries are identically distributed
within each row. This is the mixture-of-independent-i.i.d.-rows form that the Diaconis–Freedman
representation of Markov exchangeable processes consumes.

## Main definition

* `TauCeti.Probability.RowExchangeable`: invariance of the array law under independent
  permutations of the individual rows.

The symmetry-free column process `TauCeti.Probability.arrayCol` and its measurability API live
in `TauCeti.Probability.Process.Array`.

## Main results

* `TauCeti.Probability.RowExchangeable.fullyExchangeable_row` and
  `TauCeti.Probability.RowExchangeable.fullyExchangeable_arrayCol`: each row, and the column
  process, is fully exchangeable;
* `TauCeti.Probability.rowExchangeable_iff_forall_prodCongrRight_mem_finitary`: it suffices to
  check families of row permutations that move only finitely many cells altogether;
* `TauCeti.Probability.RowExchangeable.map_values`: closure under coordinatewise pushforward;
* `TauCeti.Probability.RowExchangeable.measure_setOf_forall_pair_eq`: the combinatorial core —
  the probability that each row of a finite set lands in its own target set at two prescribed
  times does not depend on which two times are prescribed;
* `TauCeti.Probability.RowExchangeable.ae_apply_pi_union`: the directing measure of the column
  process is almost surely multiplicative across disjoint sets of rows;
* `TauCeti.Probability.RowExchangeable.ae_apply_pi_eq_prod` and
  `TauCeti.Probability.RowExchangeable.exists_directing_pi_eq_prod`: the resulting product formula
  over a finite set of rows, at a given witness and at the witness de Finetti supplies;
* `TauCeti.Probability.RowExchangeable.measure_setOf_forall_mem_eq_lintegral_prod`: the mass of an
  event reading finitely many pairwise distinct cells is the mixture of the product of the row
  marginals' masses — the form in which a consumer reads a finite block of array entries.

## Implementation

The multiplicativity is proved by a second-moment argument that never leaves the world of finite
blocks. Write `C` and `D` for the boxes cut out by two disjoint finite sets of rows. The mixture
identity turns each of

```text
∫ λ(C ∩ D)²,      ∫ λ(C ∩ D) · λ(C) · λ(D),      ∫ λ(C)² · λ(D)²
```

into the probability of an array event in which **every** row involved is tested at exactly two
times — times that differ from term to term. Row exchangeability moves those times back to `0` and
`1` one row at a time, so the three integrals coincide, and the integral of
`(λ(C ∩ D) - λ(C) · λ(D))²` vanishes.

Only the mixture identity `MixedIIDWith` is used, not the joint-law disintegration: the argument
tests the directing measure against nothing but block probabilities, so the factorization theorem
needs no standard Borel structure at all. That hypothesis enters exactly once, in the de Finetti
wrapper at the end, which is what produces a witness in the first place. Countability of the row
index is present throughout, since it is what makes an array with a.e. measurable entries an a.e.
measurable map into `ι × ℕ → α`.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "Markov exchangeability".

No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable sequences
rather than arrays.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Countable ι]

/-- **Row exchangeability.** The law of the array is invariant under permuting the entries of each
row by a permutation of time chosen separately for that row.

Taking one and the same permutation in every row recovers the exchangeability of the columns; the
content beyond that is that the rows may be shuffled against one another. -/
def RowExchangeable (μ : Measure Ω) (Y : ι × ℕ → Ω → α) : Prop :=
  ∀ π : ι → Equiv.Perm ℕ,
    (μ.map fun ω (p : ι × ℕ) => Y (p.1, π p.1 p.2) ω) = μ.map fun ω (p : ι × ℕ) => Y p ω

variable {μ : Measure Ω} {Y : ι × ℕ → Ω → α}

omit [Countable ι] in
/-- Characterization of row exchangeability by invariance under every family of row-wise time
permutations. -/
theorem rowExchangeable_def :
    RowExchangeable μ Y ↔ ∀ π : ι → Equiv.Perm ℕ,
      (μ.map fun ω (p : ι × ℕ) => Y (p.1, π p.1 p.2) ω) =
        μ.map fun ω (p : ι × ℕ) => Y p ω :=
  Iff.rfl

omit [Countable ι] in
/-- **It suffices to check row exchangeability for permutation families of finite total support.**
For a finite base measure and an a.e.-measurable array, invariance under every family `π` that
moves only finitely many cells `(a, k)` implies invariance under arbitrary row-wise permutations. -/
theorem rowExchangeable_iff_forall_prodCongrRight_mem_finitary [IsFiniteMeasure μ]
    (hY : AEMeasurable (fun ω => fun p : ι × ℕ => Y p ω) μ) :
    RowExchangeable μ Y ↔
      ∀ π : ι → Equiv.Perm ℕ,
        Equiv.prodCongrRight π ∈ Equiv.Perm.finitary (ι × ℕ) →
        (μ.map fun ω (p : ι × ℕ) => Y (p.1, π p.1 p.2) ω) =
          μ.map fun ω (p : ι × ℕ) => Y p ω := by
  constructor
  · intro h π _
    exact rowExchangeable_def.mp h π
  · intro h
    rw [rowExchangeable_def]
    intro π
    have hshift : ∀ ρ : ι → Equiv.Perm ℕ,
        AEMeasurable (fun ω => fun p : ι × ℕ => Y (p.1, ρ p.1 p.2) ω) μ := by
      intro ρ
      have hρ : Measurable (fun y : ι × ℕ → α =>
          fun p : ι × ℕ => y (p.1, ρ p.1 p.2)) :=
        Measurable.of_eval fun p => measurable_pi_apply (p.1, ρ p.1 p.2)
      exact hρ.comp_aemeasurable hY
    rw [ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq (hshift π) hY]
    intro F
    obtain ⟨τ, hτfin, hτ⟩ :=
      Equiv.Perm.exists_prodCongrRight_mem_finitary_apply_eq_on_finset π F
    have hτmap := (ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq
      (hshift τ) hY).mp (h τ hτfin) F
    have heq : (fun ω => F.restrict fun p : ι × ℕ => Y (p.1, τ p.1 p.2) ω) =
        fun ω => F.restrict fun p : ι × ℕ => Y (p.1, π p.1 p.2) ω := by
      funext ω p
      obtain ⟨q, hq⟩ := p
      simpa only [Finset.restrict_def] using
        congrArg (fun k => Y (q.1, k) ω) (hτ q hq)
    rwa [heq] at hτmap

/-- **Each row of a row exchangeable array is fully exchangeable.** -/
theorem RowExchangeable.fullyExchangeable_row (h : RowExchangeable μ Y)
    (hY : ∀ p, AEMeasurable (Y p) μ) (a : ι) :
    FullyExchangeable μ fun k => Y (a, k) := by
  classical
  intro σ
  set π : ι → Equiv.Perm ℕ := fun b => if b = a then σ else 1 with hπ
  have hrow : Measurable fun y : ι × ℕ → α => fun k => y (a, k) :=
    Measurable.of_eval fun k => measurable_pi_apply (a, k)
  have hmap := congrArg (fun ρ : Measure (ι × ℕ → α) => ρ.map fun y => fun k => y (a, k))
    (rowExchangeable_def.mp h π)
  rw [AEMeasurable.map_map_of_aemeasurable hrow.aemeasurable
      (AEMeasurable.of_eval fun p => hY (p.1, π p.1 p.2)),
    AEMeasurable.map_map_of_aemeasurable hrow.aemeasurable
      (AEMeasurable.of_eval fun p => hY p)] at hmap
  have hπa : π a = σ := by simp [hπ]
  simpa [Function.comp_def, pathLaw, hπa] using hmap

/-- **The column process of a row exchangeable array is fully exchangeable.** This is the diagonal
case `π = fun _ => σ` of the definition. -/
theorem RowExchangeable.fullyExchangeable_arrayCol (h : RowExchangeable μ Y)
    (hY : ∀ p, AEMeasurable (Y p) μ) :
    FullyExchangeable μ (arrayCol Y) := by
  intro σ
  have hcol : Measurable fun y : ι × ℕ → α => fun (k : ℕ) (a : ι) => y (a, k) :=
    Measurable.of_eval fun k => Measurable.of_eval fun a => measurable_pi_apply (a, k)
  have hmap := congrArg
    (fun ρ : Measure (ι × ℕ → α) =>
      ρ.map fun y => fun (k : ℕ) (a : ι) => y (a, k))
    (rowExchangeable_def.mp h fun _ => σ)
  rw [AEMeasurable.map_map_of_aemeasurable hcol.aemeasurable
      (AEMeasurable.of_eval fun p => hY (p.1, σ p.2)),
    AEMeasurable.map_map_of_aemeasurable hcol.aemeasurable
      (AEMeasurable.of_eval fun p => hY p)] at hmap
  have hleft : (fun ω (i : ℕ) => arrayCol Y (σ i) ω) =
      fun (x : Ω) (k : ℕ) (a : ι) => Y (a, σ k) x := by
    funext ω k a
    rw [arrayCol_apply]
  have hright : (fun ω (i : ℕ) => arrayCol Y i ω) =
      fun (x : Ω) (k : ℕ) (a : ι) => Y (a, k) x := by
    funext ω k a
    rw [arrayCol_apply]
  rw [pathLaw, hleft, hright]
  simpa [Function.comp_def] using hmap

/-- **Row exchangeability is closed under row-wise coordinatewise pushforward.** Applying a
measurable map, allowed to depend on the row, to every entry leaves the array row exchangeable. -/
theorem RowExchangeable.map_values {β : Type*} [MeasurableSpace β] (h : RowExchangeable μ Y)
    (hY : ∀ p, AEMeasurable (Y p) μ) {f : ι → α → β} (hf : ∀ a, Measurable (f a)) :
    RowExchangeable μ fun p ω => f p.1 (Y p ω) := by
  rw [rowExchangeable_def] at h ⊢
  intro π
  have hpush : Measurable fun y : ι × ℕ → α => fun p : ι × ℕ => f p.1 (y p) :=
    Measurable.of_eval fun p => (hf p.1).comp (measurable_pi_apply p)
  have hmap := congrArg
    (fun ρ : Measure (ι × ℕ → α) => ρ.map fun y => fun p : ι × ℕ => f p.1 (y p)) (h π)
  rw [AEMeasurable.map_map_of_aemeasurable hpush.aemeasurable
      (AEMeasurable.of_eval fun p => hY (p.1, π p.1 p.2)),
    AEMeasurable.map_map_of_aemeasurable hpush.aemeasurable
      (AEMeasurable.of_eval fun p => hY p)] at hmap
  simpa [Function.comp_def] using hmap

/-- **The exchangeability of the columns.** -/
theorem RowExchangeable.exchangeable_arrayCol (h : RowExchangeable μ Y)
    (hY : ∀ p, AEMeasurable (Y p) μ) :
    Exchangeable μ (arrayCol Y) :=
  FullyExchangeable.exchangeable (h.fullyExchangeable_arrayCol hY)
    (aemeasurable_arrayCol hY)

section TwoTimes

omit [Countable ι] in
private theorem measurableSet_pairEventPath (F : Finset ι) {B₀ B₁ : ι → Set α}
    (hB₀ : ∀ a ∈ F, MeasurableSet (B₀ a)) (hB₁ : ∀ a ∈ F, MeasurableSet (B₁ a))
    (c d : ι → ℕ) :
    MeasurableSet {y : ι × ℕ → α | ∀ a ∈ F, y (a, c a) ∈ B₀ a ∧ y (a, d a) ∈ B₁ a} := by
  have : {y : ι × ℕ → α | ∀ a ∈ F, y (a, c a) ∈ B₀ a ∧ y (a, d a) ∈ B₁ a} =
      ⋂ a ∈ F, ((fun y : ι × ℕ → α => y (a, c a)) ⁻¹' B₀ a ∩
        (fun y : ι × ℕ → α => y (a, d a)) ⁻¹' B₁ a) := by
    ext y; simp [Set.mem_iInter]
  rw [this]
  exact MeasurableSet.biInter F.countable_toSet fun a _ =>
    ((measurable_pi_apply _) (hB₀ a ‹a ∈ F›)).inter
      ((measurable_pi_apply _) (hB₁ a ‹a ∈ F›))

/-- **The two-time pattern lemma.** Under row exchangeability the probability that every row of a
finite set lands in two specified target sets at two prescribed times is the same for all choices
of the two times, so long as the two times chosen in each row of that set are distinct.

This is the whole combinatorial input to the factorization theorem: each moment of the directing
measure computes such a probability, with a different time pattern. -/
theorem RowExchangeable.measure_setOf_forall_pair_eq (h : RowExchangeable μ Y)
    (hY : ∀ p, AEMeasurable (Y p) μ) (F : Finset ι) {B₀ B₁ : ι → Set α}
    (hB₀ : ∀ a ∈ F, MeasurableSet (B₀ a)) (hB₁ : ∀ a ∈ F, MeasurableSet (B₁ a))
    {c d : ι → ℕ} (hcd : ∀ a ∈ F, c a ≠ d a) :
    μ {ω | ∀ a ∈ F, Y (a, c a) ω ∈ B₀ a ∧ Y (a, d a) ω ∈ B₁ a} =
      μ {ω | ∀ a ∈ F, Y (a, 0) ω ∈ B₀ a ∧ Y (a, 1) ω ∈ B₁ a} := by
  classical
  -- A permutation of time in row `a` carrying `0` to `c a` and `1` to `d a`. Only the rows of `F`
  -- are constrained, so rows outside `F` — where `c` and `d` may agree — take the identity.
  have hexists : ∀ a : ι, ∃ σ : Equiv.Perm ℕ, a ∈ F → σ 0 = c a ∧ σ 1 = d a := by
    intro a
    by_cases ha : a ∈ F
    · have h01 : Function.Injective (![0, 1] : Fin 2 → ℕ) := by
        intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
      have hcd' : Function.Injective (![c a, d a] : Fin 2 → ℕ) := by
        intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [hcd a ha, (hcd a ha).symm]
      obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ h01 hcd'
      exact ⟨σ, fun _ => ⟨by simpa using hσ 0, by simpa using hσ 1⟩⟩
    · exact ⟨1, fun ha' => absurd ha' ha⟩
  choose π hπ using hexists
  set A : Set (ι × ℕ → α) :=
    {y : ι × ℕ → α | ∀ a ∈ F, y (a, 0) ∈ B₀ a ∧ y (a, 1) ∈ B₁ a} with hA
  have hAmeas : MeasurableSet A := measurableSet_pairEventPath F hB₀ hB₁ _ _
  have hLHS : (μ.map fun ω (p : ι × ℕ) => Y (p.1, π p.1 p.2) ω) A =
      μ {ω | ∀ a ∈ F, Y (a, c a) ω ∈ B₀ a ∧ Y (a, d a) ω ∈ B₁ a} := by
    rw [Measure.map_apply_of_aemeasurable
      (AEMeasurable.of_eval fun p => hY (p.1, π p.1 p.2)) hAmeas]
    congr 1
    ext ω
    simp only [hA, Set.mem_preimage, Set.mem_ofPred_eq]
    refine forall_congr' fun a => forall_congr' fun ha => ?_
    rw [(hπ a ha).1, (hπ a ha).2]
  have hRHS : (μ.map fun ω (p : ι × ℕ) => Y p ω) A =
      μ {ω | ∀ a ∈ F, Y (a, 0) ω ∈ B₀ a ∧ Y (a, 1) ω ∈ B₁ a} := by
    rw [Measure.map_apply_of_aemeasurable (AEMeasurable.of_eval fun p => hY p) hAmeas]
    rfl
  rw [← hLHS, ← hRHS, rowExchangeable_def.mp h π]

end TwoTimes

private theorem RowExchangeable.measure_setOf_two_blocks_eq (h : RowExchangeable μ Y)
    (hY : ∀ p, AEMeasurable (Y p) μ) {F G : Finset ι} (hFG : Disjoint F G) {B : ι → Set α}
    (hB : ∀ a, a ∈ F ∨ a ∈ G → MeasurableSet (B a)) {m n m' n' : ℕ} (hmn : m ≠ n)
    (hmn' : m' ≠ n') :
    μ {ω | (∀ a ∈ F, Y (a, m) ω ∈ B a ∧ Y (a, n) ω ∈ B a) ∧
        ∀ a ∈ G, Y (a, m') ω ∈ B a ∧ Y (a, n') ω ∈ B a} =
      μ {ω | (∀ a ∈ F, Y (a, 0) ω ∈ B a ∧ Y (a, 1) ω ∈ B a) ∧
        ∀ a ∈ G, Y (a, 0) ω ∈ B a ∧ Y (a, 1) ω ∈ B a} := by
  classical
  -- Split a box over `F ∪ G` into its two halves; no disjointness is needed for that.
  have hsplit : ∀ c d : ι → ℕ,
      {ω | ∀ a ∈ F ∪ G, Y (a, c a) ω ∈ B a ∧ Y (a, d a) ω ∈ B a} =
        {ω | (∀ a ∈ F, Y (a, c a) ω ∈ B a ∧ Y (a, d a) ω ∈ B a) ∧
          ∀ a ∈ G, Y (a, c a) ω ∈ B a ∧ Y (a, d a) ω ∈ B a} :=
    fun _ _ => Set.ext fun _ => Finset.forall_mem_union
  -- The two time patterns, glued from the two blocks.
  set c : ι → ℕ := fun a => if a ∈ F then m else m' with hc
  set d : ι → ℕ := fun a => if a ∈ F then n else n' with hd
  have hcd : ∀ a, c a ≠ d a := by
    intro a
    by_cases ha : a ∈ F <;> simp [hc, hd, ha, hmn, hmn']
  have hglue : {ω | (∀ a ∈ F, Y (a, c a) ω ∈ B a ∧ Y (a, d a) ω ∈ B a) ∧
      ∀ a ∈ G, Y (a, c a) ω ∈ B a ∧ Y (a, d a) ω ∈ B a} =
        {ω | (∀ a ∈ F, Y (a, m) ω ∈ B a ∧ Y (a, n) ω ∈ B a) ∧
          ∀ a ∈ G, Y (a, m') ω ∈ B a ∧ Y (a, n') ω ∈ B a} := by
    ext ω
    simp +contextual [hc, hd, Finset.disjoint_right.mp hFG]
  rw [← hglue, ← hsplit c d, ← hsplit (fun _ => 0) (fun _ => 1),
    h.measure_setOf_forall_pair_eq hY (F ∪ G)
      (fun a ha => hB a (Finset.mem_union.mp ha))
      (fun a ha => hB a (Finset.mem_union.mp ha)) fun a _ => hcd a]

section Factorization

variable {lam : Ω → ProbabilityMeasure (ι → α)}

/-- **Multiplicativity of the directing measure across disjoint sets of rows.** If the columns of a
row exchangeable array are mixed i.i.d. with mixing representative `lam`, then almost surely `lam`
gives the box over `F ∪ G` the product of the masses of its two halves.

The proof is the second-moment computation described in the module docstring: the three integrals
that make up the mean square of the difference are, by the two-block pattern lemma, one and the
same array probability. -/
theorem RowExchangeable.ae_apply_pi_union [IsFiniteMeasure μ] (h : RowExchangeable μ Y)
    (hlam : MixedIIDWith μ (arrayCol Y) lam)
    {F G : Finset ι} (hFG : Disjoint F G) {B : ι → Set α}
    (hB : ∀ a, a ∈ F ∨ a ∈ G → MeasurableSet (B a)) :
    ∀ᵐ ω ∂μ, (lam ω : Measure (ι → α)) (Set.pi (↑F ∪ ↑G) B) =
      (lam ω : Measure (ι → α)) (Set.pi (↑F) B) * (lam ω : Measure (ι → α)) (Set.pi (↑G) B) := by
  classical
  -- each entry is a coordinate of its column, which the witness makes a.e. measurable
  have hY : ∀ p, AEMeasurable (Y p) μ := fun p => by
    simpa only [arrayCol_apply] using (hlam.aemeasurable p.2).eval p.1
  set C : Set (ι → α) := Set.pi (↑F) B with hC
  set D : Set (ι → α) := Set.pi (↑G) B with hD
  have hCm : MeasurableSet C := .pi F.countable_toSet fun a ha => hB a (Or.inl ha)
  have hDm : MeasurableSet D := .pi G.countable_toSet fun a ha => hB a (Or.inr ha)
  have hm : ∀ S, MeasurableSet S → Measurable fun ω => (lam ω : Measure (ι → α)) S := fun _ hS =>
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_toMeasure_apply hS).comp
      hlam.measurable_mixingRepresentative
  set T : ℝ≥0∞ := μ {ω | (∀ a ∈ F, Y (a, 0) ω ∈ B a ∧ Y (a, 1) ω ∈ B a) ∧
    ∀ a ∈ G, Y (a, 0) ω ∈ B a ∧ Y (a, 1) ω ∈ B a} with hT
  -- Every mixed moment of `lam` on these boxes is the probability of an array event in which each
  -- row of `F` and of `G` is tested at two distinct times, so by the two-block lemma it is `T`.
  have hpat : ∀ {r : ℕ} (k : Fin r → ℕ) (E : Fin r → Set (ι → α)) {m n m' n' : ℕ},
      Function.Injective k → (∀ j, MeasurableSet (E j)) → m ≠ n → m' ≠ n' →
      (∀ ω, (∀ j, arrayCol Y (k j) ω ∈ E j) ↔ (∀ a ∈ F, Y (a, m) ω ∈ B a ∧ Y (a, n) ω ∈ B a) ∧
        ∀ a ∈ G, Y (a, m') ω ∈ B a ∧ Y (a, n') ω ∈ B a) →
      ∫⁻ ω, ∏ j, (lam ω : Measure (ι → α)) (E j) ∂μ = T := by
    intro r k E m n m' n' hk hE hmn hmn' hiff
    rw [← hlam.blockLaw_univ_pi k hk E hE, blockLaw_apply_rectangle μ (arrayCol Y) k
      (fun j => hlam.aemeasurable (k j)) E hE, hT,
      ← h.measure_setOf_two_blocks_eq hY hFG hB hmn hmn']
    exact congrArg μ (Set.ext hiff)
  have hT1 := hpat ![0, 1] ![C ∩ D, C ∩ D] (m := 0) (n := 1) (m' := 0) (n' := 1) (by decide)
    (by simp [Fin.forall_fin_two, hCm.inter hDm]) zero_ne_one zero_ne_one fun ω => by
      simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_inter_iff,
        hC, hD, Set.mem_pi, Finset.mem_coe, arrayCol_apply, imp_and, forall_and]
      tauto
  have hT2 := hpat ![0, 1, 2] ![C ∩ D, C, D] (m := 0) (n := 1) (m' := 0) (n' := 2) (by decide)
    (by simp [Fin.forall_fin_succ, hCm.inter hDm, hCm, hDm]) zero_ne_one (by norm_num) fun ω => by
      simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Set.mem_inter_iff, hC, hD, Set.mem_pi, Finset.mem_coe,
        arrayCol_apply, imp_and, forall_and]
      tauto
  have hT3 := hpat ![0, 2, 1, 3] ![C, D, C, D] (m := 0) (n := 1) (m' := 2) (n' := 3) (by decide)
    (by simp [Fin.forall_fin_succ, hCm, hDm]) zero_ne_one (by norm_num) fun ω => by
      simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true, Matrix.cons_val_zero,
        Matrix.cons_val_succ, hC, hD, Set.mem_pi, Finset.mem_coe, arrayCol_apply, imp_and,
        forall_and]
      tauto
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, Matrix.cons_val_zero,
    Matrix.cons_val_succ] at hT1 hT2 hT3
  rw [Set.union_pi]
  exact ae_eq_of_lintegral_mul_eq (hm _ (hCm.inter hDm)) ((hm _ hCm).mul (hm _ hDm))
    (fun _ => measure_ne_top _ _) (fun _ => ENNReal.mul_ne_top (measure_ne_top _ _)
      (measure_ne_top _ _)) (measure_ne_top μ _) hT1 hT2 (by simpa only [mul_assoc] using hT3)

/-- **The directing measure of a row exchangeable array factors over the rows.** For a finite set
`F` of rows and measurable target sets `B`, the mass that the mixing representative of the columns
gives to the box `{x | ∀ a ∈ F, x a ∈ B a}` is almost surely the product of the masses it gives to
the individual rows. -/
theorem RowExchangeable.ae_apply_pi_eq_prod [IsFiniteMeasure μ] (h : RowExchangeable μ Y)
    (hlam : MixedIIDWith μ (arrayCol Y) lam)
    {B : ι → Set α} (F : Finset ι) (hB : ∀ a ∈ F, MeasurableSet (B a)) :
    ∀ᵐ ω ∂μ, (lam ω : Measure (ι → α)) (Set.pi (↑F) B) =
      ∏ a ∈ F, (lam ω : Measure (ι → α)) {x : ι → α | x a ∈ B a} := by
  classical
  induction F using Finset.induction_on with
  | empty => filter_upwards with ω; simp
  | insert a s ha ih =>
      have hdisj : Disjoint ({a} : Finset ι) s := by simpa using ha
      have hcoe : ((↑(insert a s) : Set ι)) = (↑({a} : Finset ι) : Set ι) ∪ (↑s : Set ι) := by
        simp
      filter_upwards [h.ae_apply_pi_union (B := B) hlam hdisj
        (fun b hb => hB b (by
          simpa only [Finset.mem_singleton, Finset.mem_insert] using hb)),
        ih (fun b hb => hB b (Finset.mem_insert_of_mem hb))] with ω h1 h2
      rw [hcoe, h1, h2, Finset.prod_insert ha, Finset.coe_singleton, Set.singleton_pi']

/-- **Distinct cells of a row exchangeable array are conditionally independent given the mixing
representative of its columns.** The joint mass of finitely many *pairwise distinct* cells landing
in prescribed measurable sets is the mixture, over the mixing representative, of the product of the
masses that its individual row marginals give those sets.

This is the form the array law is consumed in downstream: an event that reads finitely many entries
of the array, no two of them the same cell, has the mass of an independent product, once the mixing
representative is integrated out. Distinctness is essential — a repeated cell is read twice and is
of course not independent of itself.

The cells are grouped by their column index, where the mixture identity of the columns applies,
and the row factorization `TauCeti.Probability.RowExchangeable.ae_apply_pi_eq_prod` splits each
column's contribution into one factor per row it constrains. Injectivity enters twice: it makes the
cells in a single column pairwise distinct as rows, and it makes the two nested products a single
product over cells. -/
theorem RowExchangeable.measure_setOf_forall_mem_eq_lintegral_prod [IsFiniteMeasure μ]
    (h : RowExchangeable μ Y) (hlam : MixedIIDWith μ (arrayCol Y) lam)
    {r : ℕ} {c : Fin r → ι × ℕ} (hc : Function.Injective c)
    {B : Fin r → Set α} (hB : ∀ t, MeasurableSet (B t)) :
    μ {ω | ∀ t, Y (c t) ω ∈ B t} =
      ∫⁻ ω, ∏ t : Fin r, (lam ω : Measure (ι → α)) {v : ι → α | v (c t).1 ∈ B t} ∂μ := by
  classical
  -- A horizon past every column the cells occupy, and the cells' columns inside it.
  set m : ℕ := (Finset.univ.sup fun t : Fin r => (c t).2) + 1
  set g : Fin r → Fin m := fun t => ⟨(c t).2, Nat.lt_succ_of_le
    (Finset.le_sup (f := fun t : Fin r => (c t).2) (Finset.mem_univ t))⟩
  -- The target set a row is constrained to inside a given column, and the rows a column constrains.
  set target : ι → Fin m → Set α := fun a j => ⋂ t ∈ {t | c t = (a, (j : ℕ))}, B t
  set F : Fin m → Finset ι :=
    fun j => (Finset.univ.filter fun t : Fin r => g t = j).image fun t => (c t).1
  -- Injectivity: the cell `c t` is the only one constraining its row in its column.
  have htarget : ∀ t, target (c t).1 (g t) = B t := fun t => Set.ext fun _ =>
    Set.mem_iInter₂.trans ⟨fun hx => hx t rfl, fun hx s hs => by rwa [@hc s t hs]⟩
  have hmeas : ∀ j : Fin m, MeasurableSet (Set.pi (↑(F j)) fun a => target a j) := fun j =>
    .pi (F j).countable_toSet fun _ _ => .biInter (Set.to_countable _) fun t _ => hB t
  -- The cell event is the event that every column lands in its box.
  have hset : {ω | ∀ t, Y (c t) ω ∈ B t} =
      {ω | ∀ j : Fin m, arrayCol Y (j : ℕ) ω ∈ Set.pi (↑(F j)) fun a => target a j} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, arrayCol_apply, target,
      Set.mem_iInter₂]
    refine ⟨fun hω j a _ t ht => ht ▸ hω t, fun hω t => hω (g t) _ ?_ t rfl⟩
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
  rw [hset, ← blockLaw_apply_rectangle μ (arrayCol Y) (fun j : Fin m => (j : ℕ))
      (fun j => hlam.aemeasurable (j : ℕ)) _ hmeas,
    hlam.blockLaw_univ_pi (fun j : Fin m => (j : ℕ)) Fin.val_injective _ hmeas]
  -- Split each column's mass into one factor per constrained row, then merge the two products.
  refine lintegral_congr_ae ?_
  filter_upwards [ae_all_iff.2 fun j => h.ae_apply_pi_eq_prod hlam (B := fun a => target a j)
    (F j) fun _ _ => .biInter (Set.to_countable _) fun t _ => hB t] with ω hω
  refine (Finset.prod_congr rfl fun j _ => ?_).trans (Finset.prod_fiberwise Finset.univ g _)
  -- Both cells sit in the fibre over `j`, so their column indices agree.
  rw [hω j, Finset.prod_image fun s hs t ht hst => hc (Prod.ext hst (congrArg Fin.val
    ((Finset.mem_filter.1 hs).2.trans (Finset.mem_filter.1 ht).2.symm)))]
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [← (Finset.mem_filter.1 ht).2, htarget t]

/-- **De Finetti for a row exchangeable array.** Over a countable row index and a nonempty standard
Borel state space, the columns of a row exchangeable array are conditionally i.i.d., and their
directing measure almost surely factors over the rows: conditionally on it, the rows are
independent as well as identically distributed within each row. -/
theorem RowExchangeable.exists_directing_pi_eq_prod [StandardBorelSpace α] [Nonempty α]
    [IsFiniteMeasure μ] (h : RowExchangeable μ Y) (hY : ∀ p, AEMeasurable (Y p) μ) :
    ∃ lam : Ω → ProbabilityMeasure (ι → α), ConditionallyIIDWith μ (arrayCol Y) lam ∧
      ∀ (B : ι → Set α) (F : Finset ι), (∀ a ∈ F, MeasurableSet (B a)) →
        ∀ᵐ ω ∂μ, (lam ω : Measure (ι → α)) (Set.pi (↑F) B) =
          ∏ a ∈ F, (lam ω : Measure (ι → α)) {x : ι → α | x a ∈ B a} := by
  obtain ⟨lam, hlam⟩ := ConditionallyIID.exists_directing
    (deFinetti (X := arrayCol Y) (aemeasurable_arrayCol hY) (h.exchangeable_arrayCol hY))
  exact ⟨lam, hlam, fun B F hB =>
    h.ae_apply_pi_eq_prod (mixedIIDWith_of_conditionallyIIDWith hlam) F hB⟩

end Factorization

end Probability

end TauCeti

end

end
