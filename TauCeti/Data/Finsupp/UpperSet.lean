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
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.WellFoundedSet
import Mathlib.Order.Filter.AtTopBot.Basic
import TauCeti.Order.WellFounded.UpperSet

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
desingularization* (2011), §6.1. Exponents form a well-quasi-order by Dickson's lemma, so by
`TauCeti.exists_frequently_subset_and_agree_on_finite` a sequence of upper sets has a set `E`
such that, for every degree, frequently a member contains `E` and agrees with it up to that
degree. The counting function of a member containing `E` is pointwise at most that of `E`, so a
strict lexicographic decrease from it to a later member agreeing with `E` up to a given degree
must occur beyond that degree. Hence every member containing `E` has the counting function of
`E`, which is impossible for two of them in a strictly decreasing sequence.

Degree bounds count exponents of one exact degree instead of all degrees up to `ℓ`. Over a
field `k`, the number of monomials of degree exactly `r ^ j` outside a monomial ideal `I` is
the dimension of the degree-`r ^ j` piece of `k[X_s : s ∈ σ] / I`, since the monomials
outside `I` form a basis of the quotient. An index `i` is a *degree bound* for `r` and counts
`n : ℕ → ℕ` if every upper set that omits at most `n j` exponents of degree `r ^ j` for each
`j ≤ i` does so for every `j`; then checking the finitely many degrees `r ^ j`, `j ≤ i`,
certifies the bounds `n j` in all the degrees `r ^ j`. In finitely many variables every large
`i` is a degree bound, by
`TauCeti.eventually_forall_encard_sdiff_le_of_isUpperSet_of_forall_le` and Dickson's lemma.

## Main declarations

* `TauCeti.isWF_range_toLex_ncard_sdiff`: the lexicographic order is well-founded on the set of
  counting functions of upper sets in `σ →₀ ℕ`, for finite `σ`.
* `TauCeti.exists_forall_ge_ncard_sdiff_eq_of_antitone`: a lexicographically nonincreasing
  sequence of such counting functions is eventually constant.
* `TauCeti.exists_forall_ge_ncard_sdiff_eq_of_forall_le`: a pointwise nonincreasing sequence of
  such counting functions is eventually constant.
* `TauCeti.IsDegreeBound σ r n i`: `i` is a degree bound for `r` and `n` in the variables `σ`,
  with `TauCeti.isDegreeBound_iff_ncard` for finite `σ` and `TauCeti.IsDegreeBound.mono`.
* `TauCeti.eventually_isDegreeBound`: for finite `σ`, every large `i` is a degree bound.

## References

* The degree bound follows the route of the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207,
  file `Lib/Shimura/ThetaModuli/FlatClosure` (declaration
  `New.Variety.ThetaNull.eventually_isCutDegree`).
-/

public section

open Filter

namespace TauCeti

variable {σ : Type*} [Finite σ]

/-- A strictly decreasing sequence of counting functions of upper sets of `σ →₀ ℕ`, in the
lexicographic order, is impossible. -/
theorem not_strictAnti_toLex_ncard_sdiff {D : ℕ → Set (σ →₀ ℕ)} (hD : ∀ j, IsUpperSet (D j)) :
    ¬ StrictAnti fun j ↦ toLex fun ℓ ↦ ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ D j).ncard := by
  intro hanti
  -- On every finite set, frequently `D m` contains `E` and agrees with it.
  obtain ⟨E, -, hE⟩ := exists_frequently_subset_and_agree_on_finite (l := atTop) hD
  set c : Set (σ →₀ ℕ) → ℕ → ℕ := fun F ℓ ↦ ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ F).ncard
  -- Every `D m` containing `E` has the counting function of `E`.
  have heq {m : ℕ} (hm : E ⊆ D m) : c (D m) = c E := by
    funext ℓ
    obtain ⟨m', ⟨-, hagree⟩, hmm'⟩ :=
      ((hE _ (Finsupp.finite_of_degree_le ℓ)).and_eventually (eventually_gt_atTop m)).exists
    have hagree' (i : ℕ) (hi : i ≤ ℓ) : c (D m') i = c E i := by
      refine congrArg Set.ncard (Set.ext fun α ↦ ?_)
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
      exact and_congr_right fun hα ↦ not_congr (hagree α (hα.trans hi))
    -- Mathlib has no unfolding lemma for `<` on `Lex (ℕ → ℕ)`, which is `Pi.Lex` by definition;
    -- we restate the components of the first difference at `ℕ → ℕ`.
    obtain ⟨i, hi, hlt⟩ := hanti hmm'
    have hlt : c (D m') i < c (D m) i := hlt
    have hi : ∀ j < i, c (D m') j = c (D m) j := hi
    rcases lt_or_ge ℓ i with hℓi | hiℓ
    · rw [← hi ℓ hℓi, hagree' ℓ le_rfl]
    · refine absurd (hlt.trans_le ?_) (hagree' i hiℓ).not_lt
      exact Set.ncard_le_ncard (Set.sdiff_subset_sdiff_right hm)
        (Finsupp.finite_of_degree_le i).sdiff
  -- Two members containing `E` would have equal counting functions.
  obtain ⟨m, hm, -⟩ := (hE ∅ Set.finite_empty).exists
  obtain ⟨m', ⟨hm', -⟩, hmm'⟩ :=
    ((hE ∅ Set.finite_empty).and_eventually (eventually_gt_atTop m)).exists
  exact (hanti hmm').ne (congrArg toLex ((heq hm').trans (heq hm).symm))

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

/-- An index `i` is a *degree bound* for `r : ℕ` and counts `n : ℕ → ℕ` in the variables `σ` if
every upper set `D` of exponents in `σ →₀ ℕ` (the exponents of a monomial ideal) that omits at
most `n j` exponents of degree `r ^ j` for each `j ≤ i` does so for every `j`. The omitted
exponents are counted with `Set.encard`, so infinitely many omissions never satisfy a bound. -/
def IsDegreeBound (σ : Type*) (r : ℕ) (n : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ D : Set (σ →₀ ℕ), IsUpperSet D →
    (∀ j ≤ i, ({α : σ →₀ ℕ | α.degree = r ^ j} \ D).encard ≤ n j) →
      ∀ j, ({α : σ →₀ ℕ | α.degree = r ^ j} \ D).encard ≤ n j

omit [Finite σ] in
/-- Unfolding lemma for `TauCeti.IsDegreeBound`. -/
theorem isDegreeBound_iff {r : ℕ} {n : ℕ → ℕ} {i : ℕ} :
    IsDegreeBound σ r n i ↔ ∀ D : Set (σ →₀ ℕ), IsUpperSet D →
      (∀ j ≤ i, ({α : σ →₀ ℕ | α.degree = r ^ j} \ D).encard ≤ n j) →
        ∀ j, ({α : σ →₀ ℕ | α.degree = r ^ j} \ D).encard ≤ n j :=
  Iff.rfl

/-- In finitely many variables the exponents of each degree are finitely many, so a degree bound
can be stated with `Set.ncard`. -/
theorem isDegreeBound_iff_ncard {r : ℕ} {n : ℕ → ℕ} {i : ℕ} :
    IsDegreeBound σ r n i ↔ ∀ D : Set (σ →₀ ℕ), IsUpperSet D →
      (∀ j ≤ i, ({α : σ →₀ ℕ | α.degree = r ^ j} \ D).ncard ≤ n j) →
        ∀ j, ({α : σ →₀ ℕ | α.degree = r ^ j} \ D).ncard ≤ n j := by
  have hfin (j : ℕ) (D : Set (σ →₀ ℕ)) : ({α : σ →₀ ℕ | α.degree = r ^ j} \ D).Finite :=
    (Finsupp.finite_of_degree_eq _).sdiff
  simp only [isDegreeBound_iff, Set.encard_le_coe_iff_finite_ncard_le, hfin, true_and]

omit [Finite σ] in
/-- Every index above a degree bound is a degree bound. -/
theorem IsDegreeBound.mono {r : ℕ} {n : ℕ → ℕ} {i i' : ℕ} (h : IsDegreeBound σ r n i)
    (hii' : i ≤ i') : IsDegreeBound σ r n i' :=
  fun D hD hle ↦ h D hD fun j hj ↦ hle j (hj.trans hii')

/-- In finitely many variables, every large index is a degree bound: for all large `i`, every
upper set of exponents that omits at most `n j` exponents of degree `r ^ j` for each `j ≤ i`
does so for every `j`. This is the case of the exponents of degree `r ^ j` in
`TauCeti.eventually_forall_encard_sdiff_le_of_isUpperSet_of_forall_le`, by Dickson's lemma. -/
theorem eventually_isDegreeBound (r : ℕ) (n : ℕ → ℕ) :
    ∀ᶠ i in atTop, IsDegreeBound σ r n i :=
  eventually_forall_encard_sdiff_le_of_isUpperSet_of_forall_le _ n

/-- Realizability is essential: on all of `ℕ → ℕ` the lexicographic order admits the strictly
decreasing sequence of functions vanishing below `j` and equal to `1` from `j` on. -/
example : StrictAnti fun j : ℕ ↦ toLex fun ℓ : ℕ ↦ if j ≤ ℓ then 1 else 0 :=
  -- `<` on `Lex (ℕ → ℕ)` is `Pi.Lex` by definition; the first difference is at `i`.
  fun i j hij ↦ ⟨i, fun k hk ↦ by simp [hk.not_ge, (hk.trans hij).not_ge], by simp [hij.not_ge]⟩

end TauCeti
