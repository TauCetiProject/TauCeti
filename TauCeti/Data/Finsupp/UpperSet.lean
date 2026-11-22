/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.PWO
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Set.Card
public import Mathlib.Order.PiLex
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.WellFoundedSet
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Sequences

/-!
# Lexicographic stabilization of counting functions of upper sets of exponents

For an upper set `D` of exponents `σ →₀ ℕ` in finitely many variables, the counting function
`ℓ ↦ #{α ∉ D | |α| ≤ ℓ}` records how many exponents of degree at most `ℓ` lie outside `D`. When `D`
is the diagram of initial exponents, for the graded lexicographic order, of an ideal of formal
power series over a field, this is the Hilbert–Samuel function of the quotient.

The counting functions of upper sets form a well-founded subset of `Lex (ℕ → ℕ)`, the
lexicographic order comparing two functions at the least argument where they differ. Hence every
lexicographically nonincreasing sequence of such functions is eventually constant, and in
particular so is every pointwise nonincreasing sequence. The lexicographic order on all of
`ℕ → ℕ` is not well-founded: the functions vanishing below `j` and equal to `1` from `j` on
decrease strictly with `j`. Realizability by upper sets in a fixed finite number of variables is
therefore essential.

The proof follows the finite-vertex diagram argument of Bierstone–Milman, *Uniformization of
analytic spaces* (1989), Theorem 5.2.1, as used in Bierstone–Milman–Temkin, *𝒬-universal
desingularization* (2011), §6.1. A strictly decreasing sequence of counting functions has a
subsequence of upper sets converging to a set `E` on every finite set of exponents. By Dickson's
lemma `E` has finitely many minimal elements, so eventually every member of the subsequence
contains `E`, and its counting function is pointwise at most that of `E`, with equality up to any
given degree for late members. A strict lexicographic decrease must then occur beyond every
degree, which is impossible.

## Main declarations

* `TauCeti.isWF_range_toLex_ncard_sdiff`: the lexicographic order is well-founded on the set of
  counting functions of upper sets in `σ →₀ ℕ`, for finite `σ`.
* `TauCeti.exists_forall_ge_ncard_sdiff_eq_of_antitone`: a lexicographically nonincreasing
  sequence of such counting functions is eventually constant.
* `TauCeti.exists_forall_ge_ncard_sdiff_eq_of_forall_le`: a pointwise nonincreasing sequence of
  such counting functions is eventually constant.
-/

public section

open Filter Topology

namespace TauCeti

variable {σ : Type*} [Finite σ]

/-- A strictly decreasing sequence of counting functions of upper sets of `σ →₀ ℕ`, in the
lexicographic order, is impossible. -/
theorem not_strictAnti_toLex_ncard_sdiff {D : ℕ → Set (σ →₀ ℕ)} (hD : ∀ j, IsUpperSet (D j)) :
    ¬ StrictAnti fun j ↦ toLex fun ℓ ↦ ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ D j).ncard := by
  classical
  intro hanti
  -- Pass to a subsequence `D ∘ φ` converging to `E` in the product topology on `(σ →₀ ℕ) → Bool`.
  obtain ⟨a, φ, hφ, ht⟩ := CompactSpace.tendsto_subseq fun j (α : σ →₀ ℕ) ↦ decide (α ∈ D j)
  set E : Set (σ →₀ ℕ) := {α | a α = true}
  have hconv {s : Set (σ →₀ ℕ)} (hs : s.Finite) :
      ∀ᶠ m in atTop, ∀ α ∈ s, (α ∈ D (φ m) ↔ α ∈ E) := by
    refine (eventually_all_finite hs).2 fun α _ ↦ ?_
    have := tendsto_pi_nhds.1 ht α
    rw [nhds_discrete, tendsto_pure] at this
    filter_upwards [this] with m hm
    simpa [E] using congrArg (· = true) hm
  -- By Dickson's lemma, eventually every `D (φ m)` contains the minimal vertices of `E`, hence `E`.
  have hsub : ∀ᶠ m in atTop, E ⊆ D (φ m) := by
    have hfin : {α | Minimal (· ∈ E) α}.Finite :=
      WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)
    filter_upwards [hconv hfin] with m hm γ hγ
    obtain ⟨α, hαγ, hα⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ E) γ hγ
    exact hD _ hαγ ((hm α hα).2 hα.prop)
  obtain ⟨M, hM⟩ := eventually_atTop.1 hsub
  set c : Set (σ →₀ ℕ) → ℕ → ℕ := fun F ℓ ↦ ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ F).ncard
  have hle {m : ℕ} (hm : M ≤ m) (ℓ : ℕ) : c (D (φ m)) ℓ ≤ c E ℓ :=
    Set.ncard_le_ncard (Set.sdiff_subset_sdiff_right (hM m hm))
      ((Finsupp.finite_of_degree_le ℓ).sdiff)
  -- Late members of the subsequence have the counting function of `E` up to any given degree.
  have hagree (ℓ : ℕ) : ∀ᶠ m in atTop, ∀ i ≤ ℓ, c (D (φ m)) i = c E i := by
    filter_upwards [hconv (Finsupp.finite_of_degree_le ℓ)] with m hm i hi
    refine congrArg Set.ncard (Set.ext fun α ↦ ?_)
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
    exact and_congr_right fun hα ↦ not_congr (hm α (hα.trans hi))
  have heq {m : ℕ} (hm : M ≤ m) : c (D (φ m)) = c E := by
    funext ℓ
    obtain ⟨m', hm', hagree'⟩ := ((eventually_gt_atTop m).and (hagree ℓ)).exists
    -- Mathlib has no unfolding lemma for `<` on `Lex (ℕ → ℕ)`, which is `Pi.Lex` by definition;
    -- we restate the components of the first difference at `ℕ → ℕ`.
    obtain ⟨i, hi, hlt⟩ := hanti (hφ hm')
    have hlt : c (D (φ m')) i < c (D (φ m)) i := hlt
    have hi : ∀ j < i, c (D (φ m')) j = c (D (φ m)) j := hi
    rcases lt_or_ge ℓ i with hℓi | hiℓ
    · rw [← hi ℓ hℓi, hagree' ℓ le_rfl]
    · exact absurd (hlt.trans_le (hle hm i)) (hagree' i hiℓ).not_lt
  exact (hanti (hφ (Nat.lt_succ_self M))).ne
    (congrArg toLex ((heq (Nat.le_succ M)).trans (heq le_rfl).symm))

/-- The counting functions `ℓ ↦ #{α ∉ D | |α| ≤ ℓ}` of upper sets `D` of `σ →₀ ℕ` form a
well-founded subset of `Lex (ℕ → ℕ)`. -/
theorem isWF_range_toLex_ncard_sdiff :
    (Set.range fun D : UpperSet (σ →₀ ℕ) ↦
      toLex fun ℓ ↦ ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ (D : Set (σ →₀ ℕ))).ncard).IsWF := by
  refine Set.isWF_iff_no_descending_seq.2 fun f hf hmem ↦ ?_
  choose D hD using hmem
  refine not_strictAnti_toLex_ncard_sdiff (fun j ↦ (D j).upper) ?_
  simpa only [hD] using hf

/-- A lexicographically nonincreasing sequence of counting functions
`ℓ ↦ #{α ∉ D j | |α| ≤ ℓ}` of upper sets `D j` of `σ →₀ ℕ` is eventually constant. -/
theorem exists_forall_ge_ncard_sdiff_eq_of_antitone {D : ℕ → Set (σ →₀ ℕ)}
    (hD : ∀ j, IsUpperSet (D j))
    (h : Antitone fun j ↦ toLex fun ℓ ↦ ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ D j).ncard) :
    ∃ j₀, ∀ j, j₀ ≤ j → ∀ ℓ, ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ D j).ncard =
      ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ D j₀).ncard := by
  have hwf := (isWF_range_toLex_ncard_sdiff (σ := σ)).mono
    (Set.range_subset_iff.2 fun j ↦ ⟨⟨D j, hD j⟩, rfl⟩)
  obtain ⟨j₀, hj₀⟩ := hwf.min_mem (Set.range_nonempty _)
  refine ⟨j₀, fun j hj ↦ congrFun ?_⟩
  exact (h hj).eq_of_not_lt (hj₀ ▸ hwf.not_lt_min _ ⟨j, rfl⟩)

/-- A pointwise nonincreasing sequence of counting functions `ℓ ↦ #{α ∉ D j | |α| ≤ ℓ}` of upper
sets `D j` of `σ →₀ ℕ` is eventually constant. -/
theorem exists_forall_ge_ncard_sdiff_eq_of_forall_le {D : ℕ → Set (σ →₀ ℕ)}
    (hD : ∀ j, IsUpperSet (D j))
    (h : ∀ j ℓ, ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ D (j + 1)).ncard ≤
      ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ D j).ncard) :
    ∃ j₀, ∀ j, j₀ ≤ j → ∀ ℓ, ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ D j).ncard =
      ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ D j₀).ncard :=
  exists_forall_ge_ncard_sdiff_eq_of_antitone hD
    (antitone_nat_of_succ_le fun j ↦ Pi.toLex_monotone (h j))

/-- Realizability is essential: on all of `ℕ → ℕ` the lexicographic order admits the strictly
decreasing sequence of functions vanishing below `j` and equal to `1` from `j` on. -/
example : StrictAnti fun j : ℕ ↦ toLex fun ℓ : ℕ ↦ if j ≤ ℓ then 1 else 0 :=
  -- `<` on `Lex (ℕ → ℕ)` is `Pi.Lex` by definition; the first difference is at `i`.
  fun i j hij ↦ ⟨i, fun k hk ↦ by simp [hk.not_ge, (hk.trans hij).not_ge], by simp [hij.not_ge]⟩

end TauCeti
