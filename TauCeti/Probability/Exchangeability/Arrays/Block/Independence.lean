/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Block.Basic
public import Mathlib.Probability.Independence.Conditional
import TauCeti.Probability.Independence.Conditional
import TauCeti.Data.Set.Infinite

/-!
# Local conditional independence of finite array blocks

For a separately exchangeable array, any finite block of entries inside an infinite rectangle is
conditionally independent of the entries outside the block given the other entries of the
rectangle. This is the finite-block form of the local conditional-independence principle used to
factor the visible-cell laws in the Aldous--Hoover representation.

The block whose law is controlled may be a sub-block of the hidden block: if `C` is a finite set
of cells in the rectangle and `B ⊆ C`, then `B` is conditionally independent of the complement of
the hidden block `C` given the reservoir, the rectangle with `C` removed. Nothing forces `B` to
be all of `C`, and `C` need not be minimal, so the reservoir -- the rest of the rectangle -- may be
chosen coarsely as long as it still avoids `B`.

A jointly exchangeable array is only invariant under relabelling both axes at once, so for it the
infinite rectangle becomes an infinite square `S ×ˢ S`. The finite block may then contain diagonal
entries and both orientations `(i, j)` and `(j, i)` of an off-diagonal cell, as the cell noise of
the jointly exchangeable Aldous--Hoover representation requires.

Both statements come from the reindexing criterion `condIndepFun_domRestrict_of_reindexing`: a
self-injection of the index set fixing the block moves everything outside it into the reservoir,
without changing the array law (`SeparatelyExchangeable.map_arrayBlock_eq`,
`JointlyExchangeable.map_arrayBlock_diag_eq`).

## Main results

* `SeparatelyExchangeable.condIndepFun_domRestrict_subblock_compl_of_finite_block_of_subset`
  — local conditional independence inside an infinite rectangle;
* `JointlyExchangeable.condIndepFun_domRestrict_subblock_compl_of_finite_block_of_subset`
  — local conditional independence inside an infinite square, for jointly exchangeable arrays.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
  {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]

/-- Conditional independence of all entries in `U` follows when every finite subset can be fixed
by a reindexing of the two axes that moves `D` into the intermediate conditioning set `R`. -/
theorem SeparatelyExchangeable.condIndepFun_domRestrict_of_finite_reindexing
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p) (R D U : Set (ℕ × ℕ))
    (hRD : R ⊆ D)
    (hreindex : ∀ C : Set (ℕ × ℕ), C.Finite → C ⊆ U →
      ∃ a b : ℕ → ℕ, Function.Injective a ∧ Function.Injective b ∧
        (∀ p ∈ C, (a p.1, b p.2) = p) ∧ ∀ p ∈ D, (a p.1, b p.2) ∈ R) :
    U.domRestrict ⟂ᵢ[R.domRestrict, Set.measurable_restrict _; ρ] D.domRestrict := by
  refine TauCeti.Probability.condIndepFun_domRestrict_of_finite_reindexing hRD fun C hC hCU ↦ ?_
  obtain ⟨a, b, ha, hb, hfix, hinto⟩ := hreindex C hC hCU
  refine ⟨fun p ↦ (a p.1, b p.2), ?_, hfix, hinto⟩
  simpa only [Measure.map_id'] using
    hρ.map_arrayBlock_eq (fun p ↦ (measurable_pi_apply p).aemeasurable) ha hb

/-- **A finite block of array entries in an infinite rectangle is conditionally independent of
everything outside a finite block containing it, given the rest of the rectangle.**

The entries that are read off are the sub-block `B ⊆ C`, while the conditioning set is the
rectangle with the whole hidden block `C` removed, and the events compared are those of the
complement of `C`. Taking `B = C` recovers the statement that one finite block is conditionally
independent of the rest of the array given the other entries of the rectangle; taking `B` to be
a proper sub-block of `C` says the same for a part of the hidden block, with a reservoir that is
allowed to hide more of the hidden block than that part needs.

`C` is the only set that has to be finite: `B` needs no finiteness hypothesis of its own, since
`B ⊆ C`. -/
theorem SeparatelyExchangeable.condIndepFun_domRestrict_subblock_compl_of_finite_block_of_subset
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p) {S T : Set ℕ} (hS : S.Infinite)
    (hT : T.Infinite) {B C : Set (ℕ × ℕ)} (hC : C.Finite) (hBsub : B ⊆ C)
    (hCsub : C ⊆ S ×ˢ T) :
    B.domRestrict ⟂ᵢ[((S ×ˢ T) \ C).domRestrict, Set.measurable_restrict _; ρ]
      Cᶜ.domRestrict := by
  have hFS : Prod.fst '' C ⊆ S := by
    rintro i ⟨p, hp, rfl⟩
    exact (hCsub hp).1
  have hGT : Prod.snd '' C ⊆ T := by
    rintro j ⟨p, hp, rfl⟩
    exact (hCsub hp).2
  -- Each axis of the rectangle reindexes into itself while fixing every coordinate used by `C`.
  obtain ⟨a, ha, haF, haS⟩ := hS.exists_injective_into_eqOn_of_finite
    (hC.image Prod.fst) hFS
  obtain ⟨b, hb, hbG, hbT⟩ := hT.exists_injective_into_eqOn_of_finite
    (hC.image Prod.snd) hGT
  refine hρ.condIndepFun_domRestrict_of_finite_reindexing (S ×ˢ T \ C) Cᶜ B
    (Set.sdiff_subset_compl _ _) ?_
  intro C' _ hC'B
  refine ⟨a, b, ha, hb, fun p hp => ?_, fun p hp => ?_⟩
  · exact Prod.ext (haF p.1 ⟨p, hBsub (hC'B hp), rfl⟩) (hbG p.2 ⟨p, hBsub (hC'B hp), rfl⟩)
  · refine ⟨⟨haS p.1, hbT p.2⟩, fun hc ↦ hp ?_⟩
    have hp1 : p.1 = a p.1 :=
      ha (haF (a p.1) ⟨(a p.1, b p.2), hc, rfl⟩).symm
    have hp2 : p.2 = b p.2 :=
      hb (hbG (b p.2) ⟨(a p.1, b p.2), hc, rfl⟩).symm
    have hpEq : p = (a p.1, b p.2) := Prod.ext hp1 hp2
    exact hpEq ▸ hc

/-- **A finite block of entries of a jointly exchangeable array inside an infinite square is
conditionally independent of everything outside a finite block containing it, given the rest of
the square.**

This is the jointly exchangeable form of
`SeparatelyExchangeable.condIndepFun_domRestrict_subblock_compl_of_finite_block_of_subset`: the
rectangle `S ×ˢ T` becomes the square `S ×ˢ S`, since only a simultaneous relabelling of both axes
preserves the array law. The blocks may contain diagonal entries, and both orientations of an
off-diagonal cell. -/
theorem JointlyExchangeable.condIndepFun_domRestrict_subblock_compl_of_finite_block_of_subset
    (hρ : JointlyExchangeable ρ fun p x ↦ x p) {S : Set ℕ} (hS : S.Infinite)
    {B C : Set (ℕ × ℕ)} (hC : C.Finite) (hBsub : B ⊆ C) (hCsub : C ⊆ S ×ˢ S) :
    B.domRestrict ⟂ᵢ[((S ×ˢ S) \ C).domRestrict, Set.measurable_restrict _; ρ]
      Cᶜ.domRestrict := by
  -- A single self-injection of `S` fixes every index occurring in `C`.
  have hFS : Prod.fst '' C ∪ Prod.snd '' C ⊆ S := by
    rintro i (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    exacts [(hCsub hp).1, (hCsub hp).2]
  obtain ⟨a, ha, haF, haS⟩ := hS.exists_injective_into_eqOn_of_finite
    ((hC.image _).union (hC.image _)) hFS
  refine condIndepFun_domRestrict_of_reindexing (Set.sdiff_subset_compl _ _)
    (fun p ↦ (a p.1, a p.2)) ?_ (fun p hp ↦ ?_) (fun p hp ↦ ⟨⟨haS _, haS _⟩, fun hc ↦ hp ?_⟩)
  · simpa only [Measure.map_id'] using
      hρ.map_arrayBlock_diag_eq (fun p ↦ (measurable_pi_apply p).aemeasurable) ha
  · exact Prod.ext (haF _ (Or.inl ⟨p, hBsub hp, rfl⟩)) (haF _ (Or.inr ⟨p, hBsub hp, rfl⟩))
  · -- `a` fixes both indices of the cell `(a p.1, a p.2) ∈ C`, so by injectivity it is `p`.
    have h₁ : a p.1 = p.1 := ha (haF _ (Or.inl ⟨_, hc, rfl⟩))
    have h₂ : a p.2 = p.2 := ha (haF _ (Or.inr ⟨_, hc, rfl⟩))
    simpa only [h₁, h₂, Prod.mk.eta] using hc

end TauCeti.Probability

end

end
