/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Setoid.Smallness
public import TauCeti.ModelTheory.Counting.Scattered.Concentration
public import TauCeti.ModelTheory.RelationalConfiguration.LevelSentence
public import TauCeti.SetTheory.Ordinal.RankBounds

/-!
# Finding large back-and-forth classes from small sentence cuts

Let smallness be closed under countable unions. If a non-small class of structures meets
countably many classes at a back-and-forth level, some level class has non-small intersection
with it. If every sentence cut has a small side, the complement of that intersection is small:
level classes are themselves defined by Scott approximation sentences.

We instantiate this argument with smallness meaning countably many isomorphism classes or a
rank bound below `ω₁`. Consequently a back-and-forth scattered class whose every sentence cut
has a countable side is concentrated at back-and-forth levels. No definability or isomorphism
invariance of the class is
needed. These are the class-selection steps in the analysis of minimally uncountable sentences.

## References

* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII,
  §XII.2, for the large-class selection argument for minimally unbounded sentences.
-/

public section

universe u v w o r

open FirstOrder FirstOrder.Language Ordinal Set

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ n, L.Relations n)]
variable {V : Type w} [Countable V] {K : Set (RelationalConfiguration L V)}

/-- A non-small class with countably many classes at level `α` has a non-small level class with
small complement, provided smallness is closed under countable unions and every sentence cut
has a small side. The centre belongs to the original class. -/
theorem exists_bfClass_not_small_and_small_sdiff
    (small : Set (RelationalConfiguration L V) → Prop)
    (hUnion : ∀ S : Set (Set (RelationalConfiguration L V)),
      S.Countable → (∀ s ∈ S, small s) → small (⋃₀ S))
    (hK : ¬ small K)
    (hsplit : ∀ θ : L.Sentenceω, small (K ∩ modelsOf θ) ∨ small (K \ modelsOf θ))
    {α : Ordinal.{o}} (hα : α < ω₁)
    [Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : K → _)))] :
    ∃ c ∈ K, ¬ small (K ∩ {d | bfEquivSetoid L V α c d}) ∧
      small (K \ {d | bfEquivSetoid L V α c d}) := by
  refine (bfEquivSetoid L V α).exists_class_not_small_and_small_sdiff K small hUnion hK
    (fun c _ => ?_)
  simpa only [modelsOf_scottSentenceAtLevel c hα] using hsplit (c.scottSentenceAtLevel α)

/-- If a class meets uncountably many isomorphism classes, has countably many classes at level
`α`, and every sentence cut has a side meeting only countably many isomorphism classes, then
one level-`α` class meets uncountably many, and its complement meets only countably many. -/
theorem exists_bfClass_uncountable_isoClasses_and_countable_sdiff
    (hK : ¬ (Quotient.mk (isoSetoid L V) '' K).Countable)
    (hsplit : ∀ θ : L.Sentenceω,
      (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L V) '' (K \ modelsOf θ)).Countable)
    {α : Ordinal.{o}} (hα : α < ω₁)
    [Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : K → _)))] :
    ∃ c ∈ K,
      ¬ (Quotient.mk (isoSetoid L V) '' (K ∩ {d | bfEquivSetoid L V α c d})).Countable ∧
        (Quotient.mk (isoSetoid L V) '' (K \ {d | bfEquivSetoid L V α c d})).Countable := by
  refine exists_bfClass_not_small_and_small_sdiff
    (fun A => (Quotient.mk (isoSetoid L V) '' A).Countable) ?_ hK hsplit hα
  intro S hS hs
  rw [image_sUnion, sUnion_image]
  exact hS.biUnion hs

/-- For a rank-unbounded class with countably many classes at level `α`, if every sentence cut
has a rank-bounded side, one level class is rank-unbounded and its complement is rank-bounded.
The rank need not be invariant under isomorphism or isolating. -/
theorem exists_bfClass_unboundedRankOn_and_boundedRankOn_sdiff
    {ρ : RelationalConfiguration L V → Ordinal.{r}} (hK : UnboundedRankOn ρ K)
    (hsplit : ∀ θ : L.Sentenceω,
      BoundedRankOn ρ (K ∩ modelsOf θ) ∨ BoundedRankOn ρ (K \ modelsOf θ))
    {α : Ordinal.{o}} (hα : α < ω₁)
    [Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : K → _)))] :
    ∃ c ∈ K, UnboundedRankOn ρ (K ∩ {d | bfEquivSetoid L V α c d}) ∧
      BoundedRankOn ρ (K \ {d | bfEquivSetoid L V α c d}) := by
  simpa only [unboundedRankOn_iff_not_boundedRankOn] using
    exists_bfClass_not_small_and_small_sdiff (BoundedRankOn ρ)
      (fun _ hS hs => (boundedRankOn_sUnion_iff hS).2 hs)
      (unboundedRankOn_iff_not_boundedRankOn.1 hK) hsplit hα

/-- A back-and-forth scattered class with a countable side at every sentence cut is concentrated.
The class need not be analytic, Borel, or invariant under isomorphism, and it may itself meet
only countably many isomorphism classes. -/
theorem concentratedAtBFLevels_of_bfScattered_of_sentence_splits
    {K : Set (RelationalConfiguration L ℕ)} (hK : BFScattered K)
    (hsplit : ∀ θ : L.Sentenceω,
      (Quotient.mk (isoSetoid L ℕ) '' (K ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L ℕ) '' (K \ modelsOf θ)).Countable) :
    ConcentratedAtBFLevels K := by
  by_cases hcount : (Quotient.mk (isoSetoid L ℕ) '' K).Countable
  · have := Setoid.countable_quotient_comap_val_iff.2 hcount
    exact ConcentratedAtBFLevels.of_countable_isoClasses
  · refine concentratedAtBFLevels_iff.2 fun α hα => ?_
    have := hK.countable_quotient hα
    obtain ⟨c, _, _, hc⟩ :=
      exists_bfClass_uncountable_isoClasses_and_countable_sdiff hcount hsplit hα
    refine ⟨c, ?_⟩
    have heq : {d ∈ K | ¬ bfEquivSetoid L ℕ α d c} =
        K \ {d | bfEquivSetoid L ℕ α c d} := by
      ext d
      simp only [mem_ofPred_eq, mem_sdiff, (bfEquivSetoid L ℕ α).comm']
    rwa [heq]

end TauCeti
