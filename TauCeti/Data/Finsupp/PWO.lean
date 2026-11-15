/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.PWO
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.PiLex
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.WellFoundedSet

-- Proof-only: binomial summation for degree-bounded exponent counts, Dickson minimal vertices,
-- and sequential compactness of `(σ →₀ ℕ) → Bool` to extract a pointwise-convergent subsequence.
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Minimal
import Mathlib.Order.OrderIsoNat
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Sequences

/-!
# Degree-bounded exponent counts and Dickson stabilization of upper sets

For a finite variable set `σ`, there are `(Nat.card σ).multichoose n` finitely supported exponent
vectors `f : σ →₀ ℕ` of total degree `n` and `(n + Nat.card σ).choose (Nat.card σ)` of total
degree at most `n` (`Finsupp.ncard_setOf_degree_eq`, `Finsupp.ncard_setOf_degree_le`).

For an upward-closed subset `D : Set (σ →₀ ℕ)` in the componentwise order, the degree-bounded
complement count `ℓ ↦ {f : σ →₀ ℕ | f.degree ≤ ℓ ∧ f ∉ D}.ncard` records how many exponents of
total degree at most `ℓ` avoid `D` (for instance when `D` is Hironaka's diagram of initial
exponents of a formal power series ideal). Although `Lex (ℕ → ℕ)` has infinite strictly descending
chains such as `ℓ ↦ (if ℓ < N - j then 1 else 2)`, Dickson's lemma (`Finsupp.wellQuasiOrderedLE`)
ensures that the subset of `Lex (ℕ → ℕ)` realized by upward-closed subsets of `σ →₀ ℕ` is
well-founded (`Finsupp.isWF_toLex_ncard_setOf_degree_le_notMem`). Every sequence of upward-closed
sets in `σ →₀ ℕ` admits a subsequence converging pointwise to an upward-closed limit `D₀` that is
eventually contained in the subsequence terms (`Finsupp.exists_subseq_isUpperSet_limit`).
Consequently any lexicographically (or pointwise) nonincreasing sequence of degree-complement
counts of upper sets in `σ →₀ ℕ` is eventually constant
(`Finsupp.exists_forall_ncard_setOf_degree_le_notMem_eq_of_antitone_toLex`,
`Finsupp.exists_forall_ncard_setOf_degree_le_notMem_eq_of_antitone`).

## Main results

* `Finsupp.ncard_setOf_degree_eq`, `Finsupp.ncard_setOf_degree_le`: multichoose and binomial
  formulas for `{f : σ →₀ ℕ | f.degree = n}.ncard` and `{f : σ →₀ ℕ | f.degree ≤ n}.ncard`.
* `Finsupp.exists_subseq_isUpperSet_limit`: every sequence of upper sets in `σ →₀ ℕ` has a
  pointwise-convergent subsequence whose limit upper set is eventually contained in the terms.
* `Finsupp.isWF_toLex_ncard_setOf_degree_le_notMem`: lexicographic well-foundedness of the set of
  degree-complement counting functions of upper sets in `σ →₀ ℕ`.
* `Finsupp.exists_forall_ncard_setOf_degree_le_notMem_eq_of_antitone_toLex`: lexicographically
  nonincreasing degree-complement counts of upper sets in `σ →₀ ℕ` stabilize.
* `Finsupp.exists_forall_ncard_setOf_degree_le_notMem_eq_of_antitone`: pointwise nonincreasing
  degree-complement counts of upper sets in `σ →₀ ℕ` stabilize.

## References

* Edward Bierstone and Pierre D. Milman, *Uniformization of analytic spaces*, J. Amer. Math. Soc.
  2 (1989), 801–836, Theorem 5.2.1.
* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302, §3.
-/

public section

open Filter Topology

namespace Finsupp

section DegreeCount

variable {σ : Type*}

/-- For finitely many variables `σ`, there are `(Nat.card σ).multichoose n` exponent vectors
`f : σ →₀ ℕ` of total degree `n`. -/
theorem ncard_setOf_degree_eq [Finite σ] (n : ℕ) :
    {f : σ →₀ ℕ | f.degree = n}.ncard = (Nat.card σ).multichoose n := by
  classical
  cases nonempty_fintype σ
  have hset : {f : σ →₀ ℕ | f.degree = n} =
      ((Finset.univ : Finset σ).finsuppAntidiag n : Set (σ →₀ ℕ)) := by
    ext f
    simp [Finset.mem_finsuppAntidiag, degree_eq_sum]
  rw [hset, Set.ncard_coe_finset, Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ,
    Nat.card_eq_fintype_card]

/-- For finitely many variables `σ`, there are `(n + Nat.card σ).choose (Nat.card σ)` exponent
vectors `f : σ →₀ ℕ` of total degree at most `n`. -/
theorem ncard_setOf_degree_le [Finite σ] (n : ℕ) :
    {f : σ →₀ ℕ | f.degree ≤ n}.ncard = (n + Nat.card σ).choose (Nat.card σ) := by
  classical
  cases nonempty_fintype σ
  have hset : {f : σ →₀ ℕ | f.degree ≤ n} =
      ↑((Finset.range (n + 1)).biUnion ((Finset.univ : Finset σ).finsuppAntidiag ·)) := by
    ext f
    simp [Finset.mem_finsuppAntidiag, degree_eq_sum]
  rw [hset, Set.ncard_coe_finset, Finset.card_biUnion]
  · simp [Finset.card_finsuppAntidiag_nat_eq_multichoose, Nat.sum_range_multichoose,
      Nat.card_eq_fintype_card]
  · intro k _ l _ hkl
    refine Finset.disjoint_left.mpr fun f hk hl ↦ hkl ?_
    rw [Finset.mem_finsuppAntidiag] at hk hl
    exact hk.1.symm.trans hl.1

/-- For finitely many variables `σ`, the set of exponents of total degree at most `n` outside `D`
is finite. -/
theorem finite_setOf_degree_le_notMem [Finite σ] (D : Set (σ →₀ ℕ)) (n : ℕ) :
    {f : σ →₀ ℕ | f.degree ≤ n ∧ f ∉ D}.Finite :=
  (finite_of_degree_le n).subset fun _ hf ↦ hf.1

/-- Larger excluded sets `D` have no larger degree-bounded complement counts. -/
theorem ncard_setOf_degree_le_notMem_anti [Finite σ] {D₁ D₂ : Set (σ →₀ ℕ)} (h : D₁ ⊆ D₂)
    (n : ℕ) :
    {f : σ →₀ ℕ | f.degree ≤ n ∧ f ∉ D₂}.ncard ≤
      {f : σ →₀ ℕ | f.degree ≤ n ∧ f ∉ D₁}.ncard :=
  Set.ncard_le_ncard (fun _ hf ↦ ⟨hf.1, fun hmem ↦ hf.2 (h hmem)⟩)
    (finite_setOf_degree_le_notMem D₁ n)

/-- Excluding the empty set leaves all `(n + Nat.card σ).choose (Nat.card σ)` exponents of total
degree at most `n`. -/
theorem ncard_setOf_degree_le_notMem_empty [Finite σ] (n : ℕ) :
    {f : σ →₀ ℕ | f.degree ≤ n ∧ f ∉ (∅ : Set (σ →₀ ℕ))}.ncard =
      (n + Nat.card σ).choose (Nat.card σ) := by
  simp [ncard_setOf_degree_le]

/-- Excluding `Set.univ` leaves zero exponents of total degree at most `n`. -/
theorem ncard_setOf_degree_le_notMem_univ (n : ℕ) :
    {f : σ →₀ ℕ | f.degree ≤ n ∧ f ∉ (Set.univ : Set (σ →₀ ℕ))}.ncard = 0 := by
  simp

/-- Express `{f : σ →₀ ℕ | f.degree ≤ n ∧ f ∉ D}.ncard` as the cardinality of a filtered `Finset`.
-/
theorem ncard_setOf_degree_le_notMem_eq_card_filter [Finite σ] (D : Set (σ →₀ ℕ))
    [DecidablePred (· ∈ D)] (n : ℕ) :
    {f : σ →₀ ℕ | f.degree ≤ n ∧ f ∉ D}.ncard =
      ((finite_of_degree_le n).toFinset.filter (· ∉ D)).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext f
  simp

end DegreeCount

section Stabilization

variable {σ : Type*} [Finite σ]

/-- Every sequence of upward-closed sets `D : ℕ → Set (σ →₀ ℕ)` in finitely many variables admits a
strictly increasing subsequence `g` and an upward-closed limit `D₀` such that each exponent
eventually belongs to `D (g k)` iff it belongs to `D₀`, and eventually `D₀ ⊆ D (g k)`. -/
theorem exists_subseq_isUpperSet_limit (D : ℕ → Set (σ →₀ ℕ))
    (hD : ∀ j, IsUpperSet (D j)) :
    ∃ (g : ℕ → ℕ) (D₀ : Set (σ →₀ ℕ)), StrictMono g ∧ IsUpperSet D₀ ∧
      (∀ α : σ →₀ ℕ, ∀ᶠ k in atTop, α ∈ D (g k) ↔ α ∈ D₀) ∧
      (∀ᶠ k in atTop, D₀ ⊆ D (g k)) := by
  classical
  obtain ⟨c, g, hg, hlim⟩ :=
    CompactSpace.tendsto_subseq fun j (α : σ →₀ ℕ) ↦ decide (α ∈ D j)
  let D₀ : Set (σ →₀ ℕ) := {α | c α = true}
  have hev (α : σ →₀ ℕ) : ∀ᶠ k in atTop, α ∈ D (g k) ↔ α ∈ D₀ := by
    have hα := tendsto_pi_nhds.mp hlim α
    rw [nhds_discrete, tendsto_pure] at hα
    exact hα.mono fun k hk ↦ by simp [D₀, ← hk]
  have hupper : IsUpperSet D₀ := by
    intro α β hle hα
    obtain ⟨k, hkα, hkβ⟩ := ((hev α).and (hev β)).exists
    exact hkβ.mp (hD (g k) hle (hkα.mpr hα))
  have hminFin : {v : σ →₀ ℕ | Minimal (· ∈ D₀) v}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)
  have hsub : ∀ᶠ k in atTop, D₀ ⊆ D (g k) := by
    have hminEv : ∀ᶠ k in atTop, ∀ v ∈ {v : σ →₀ ℕ | Minimal (· ∈ D₀) v}, v ∈ D (g k) :=
      (eventually_all_finite hminFin).mpr fun v hv ↦ (hev v).mono fun _ hk ↦ hk.mpr hv.prop
    refine hminEv.mono fun k hk α hα ↦ ?_
    obtain ⟨v, hvle, hvmin⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ D₀) α hα
    exact hD (g k) hvle (hk v hvmin)
  exact ⟨g, D₀, hg, hupper, hev, hsub⟩

/-- **Bierstone–Milman Theorem 5.2.1 (well-foundedness form)**: for finitely many variables `σ`,
the set of lexicographically ordered degree-complement counting functions realized by upward-closed
subsets `D : Set (σ →₀ ℕ)` is well-founded. -/
theorem isWF_toLex_ncard_setOf_degree_le_notMem :
    {h : Lex (ℕ → ℕ) | ∃ D : Set (σ →₀ ℕ), IsUpperSet D ∧
      ofLex h = fun ℓ ↦ {f : σ →₀ ℕ | f.degree ≤ ℓ ∧ f ∉ D}.ncard}.IsWF := by
  rw [Set.IsWF, Set.wellFoundedOn_iff_no_descending_seq]
  rintro ⟨f, hf⟩ hmem
  choose D hD hfeq using hmem
  let count (S : Set (σ →₀ ℕ)) (ℓ : ℕ) : ℕ := {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ S}.ncard
  have hf_eq (j : ℕ) : f j = toLex (count (D j)) := toLex_inj.mp (hfeq j)
  have hdesc {i j : ℕ} (hij : i < j) : toLex (count (D j)) < toLex (count (D i)) := by
    rw [← hf_eq j, ← hf_eq i]
    exact hf.mpr hij
  obtain ⟨g, D₀, hg, -, hev, hsub⟩ := exists_subseq_isUpperSet_limit D hD
  obtain ⟨k₁, hk₁⟩ := hsub.exists
  have hle₁ : toLex (count (D (g k₁))) ≤ toLex (count D₀) :=
    Pi.toLex_monotone fun ℓ ↦ ncard_setOf_degree_le_notMem_anti hk₁ ℓ
  have hlt₁ : toLex (count (D (g (k₁ + 1)))) < toLex (count D₀) :=
    (hdesc (hg (Nat.lt_succ_self k₁))).trans_le hle₁
  obtain ⟨ℓ₀, hlt_eq, hlt_ℓ₀⟩ := hlt₁
  have hball : ∀ᶠ k in atTop, ∀ α : σ →₀ ℕ, α.degree ≤ ℓ₀ → (α ∈ D (g k) ↔ α ∈ D₀) :=
    (eventually_all_finite (finite_of_degree_le ℓ₀)).mpr fun α _ ↦ hev α
  obtain ⟨k₂, hk₂ge, hk₂ball⟩ := (eventually_ge_atTop (k₁ + 1) |>.and hball).exists
  have heq₂ (ℓ : ℕ) (hℓ : ℓ ≤ ℓ₀) : count (D (g k₂)) ℓ = count D₀ ℓ := by
    dsimp only [count]
    congr 1
    ext α
    exact and_congr_right fun hdeg ↦ not_congr (hk₂ball α (hdeg.trans hℓ))
  have hlt₂ : toLex (count (D (g (k₁ + 1)))) < toLex (count (D (g k₂))) :=
    ⟨ℓ₀, fun j hj ↦ (hlt_eq j hj).trans (heq₂ j hj.le).symm,
      by simpa only [Pi.toLex_apply, heq₂ ℓ₀ le_rfl] using hlt_ℓ₀⟩
  rcases hk₂ge.eq_or_lt with rfl | hklt
  · exact lt_irrefl _ hlt₂
  · exact (hdesc (hg hklt)).not_gt hlt₂

/-- **Bierstone–Milman Theorem 5.2.1**: if `D : ℕ → Set (σ →₀ ℕ)` is a sequence of upward-closed
sets whose degree-bounded complement counts are lexicographically nonincreasing, then those counts
stabilize. -/
theorem exists_forall_ncard_setOf_degree_le_notMem_eq_of_antitone_toLex
    (D : ℕ → Set (σ →₀ ℕ)) (hD : ∀ j, IsUpperSet (D j))
    (hlex : ∀ j,
      toLex (fun ℓ ↦ {f : σ →₀ ℕ | f.degree ≤ ℓ ∧ f ∉ D (j + 1)}.ncard) ≤
        toLex (fun ℓ ↦ {f : σ →₀ ℕ | f.degree ≤ ℓ ∧ f ∉ D j}.ncard)) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      (fun ℓ ↦ {f : σ →₀ ℕ | f.degree ≤ ℓ ∧ f ∉ D j}.ncard) =
        (fun ℓ ↦ {f : σ →₀ ℕ | f.degree ≤ ℓ ∧ f ∉ D j₀}.ncard) := by
  let S : Set (Lex (ℕ → ℕ)) :=
    {h | ∃ E : Set (σ →₀ ℕ), IsUpperSet E ∧
      ofLex h = fun ℓ ↦ {f : σ →₀ ℕ | f.degree ≤ ℓ ∧ f ∉ E}.ncard}
  have : WellFoundedLT S := isWF_toLex_ncard_setOf_degree_le_notMem (σ := σ)
  let seq (j : ℕ) : S := ⟨toLex (fun ℓ ↦ {f : σ →₀ ℕ | f.degree ≤ ℓ ∧ f ∉ D j}.ncard),
    D j, hD j, rfl⟩
  have hanti : Antitone seq := antitone_nat_of_succ_le fun j ↦ hlex j
  obtain ⟨j₀, hj₀⟩ := WellFoundedLT.antitone_chain_condition hanti
  exact ⟨j₀, fun j hj ↦ ofLex_inj.mpr (congrArg Subtype.val (hj₀ j hj)).symm⟩

/-- Pointwise nonincreasing degree-bounded complement counts of upward-closed sets in `σ →₀ ℕ`
stabilize. -/
theorem exists_forall_ncard_setOf_degree_le_notMem_eq_of_antitone
    (D : ℕ → Set (σ →₀ ℕ)) (hD : ∀ j, IsUpperSet (D j))
    (hanti : ∀ j ℓ,
      {f : σ →₀ ℕ | f.degree ≤ ℓ ∧ f ∉ D (j + 1)}.ncard ≤
        {f : σ →₀ ℕ | f.degree ≤ ℓ ∧ f ∉ D j}.ncard) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      (fun ℓ ↦ {f : σ →₀ ℕ | f.degree ≤ ℓ ∧ f ∉ D j}.ncard) =
        (fun ℓ ↦ {f : σ →₀ ℕ | f.degree ≤ ℓ ∧ f ∉ D j₀}.ncard) :=
  exists_forall_ncard_setOf_degree_le_notMem_eq_of_antitone_toLex D hD fun j ↦
    Pi.toLex_monotone (hanti j)

end Stabilization

end Finsupp
