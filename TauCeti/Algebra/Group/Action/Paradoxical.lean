/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.AddContent
public import TauCeti.Algebra.Group.Action.Equidecomp
public import TauCeti.Algebra.Group.Action.Equipartition

/-!
# Paradoxical sets

Let `G` act on `X`. A set `S : Set X` is *paradoxical*, `TauCeti.Paradoxical G S`, when it is
nonempty and splits into two disjoint pieces `A` and `B`, each equidecomposable with `S` itself:
cutting `S` into finitely many pieces and moving them by elements of `G` produces two copies of
`S`. The empty set is excluded by definition.

For a group action it suffices to find two disjoint subsets of `S`, each equidecomposable with `S`,
that need not cover `S` (`TauCeti.paradoxical_iff_exists_subset`): by the Schröder–Bernstein
theorem for equidecompositions, the complement of one of them is still equidecomposable with `S`.
Being paradoxical is invariant under equidecomposition and under equivariant bijections.

A finitely additive set function on all subsets of `X` that is invariant under `G` takes equal
values on equidecomposable sets (`TauCeti.Equidecomposable.addContent_eq`), since both are finite
disjoint unions of pieces matched by translations. On a paradoxical set `S` it therefore satisfies
`ν S = ν A + ν B = ν S + ν S`. Hence a finite invariant content cannot give a paradoxical set
positive mass, and an invariant finitely additive probability on `X` rules out a paradoxical
decomposition of `X`. This is the obstruction that relates paradoxical decompositions to
amenability.

## Main definitions

* `TauCeti.Paradoxical G S`: `S` is nonempty and the disjoint union of two sets each
  equidecomposable with `S`.

## Main results

* `TauCeti.paradoxical_iff_exists_subset`: `S` is paradoxical exactly when it is nonempty and
  contains two disjoint subsets each equidecomposable with `S`.
* `TauCeti.Equidecomposable.paradoxical_iff`: equidecomposable sets are paradoxical together.
* `TauCeti.paradoxical_image_equiv_iff`: being paradoxical is invariant under equivariant
  bijections.
* `TauCeti.Equidecomposable.addContent_eq`: an invariant content takes equal values on
  equidecomposable sets.
* `TauCeti.Paradoxical.addContent_eq_zero_or_eq_top`: an invariant `ℝ≥0∞`-valued content takes
  the value `0` or `∞` on a paradoxical set.
* `TauCeti.not_paradoxical_univ_of_addContent`: if `X` carries an invariant finitely additive
  probability, then `X` is not paradoxical.

## References

* A. Garrido, *An introduction to amenable groups*, Definition 1.1, Theorem 1.2 and
  Corollary 1.3.
* G. Tomkowicz, S. Wagon, *The Banach–Tarski Paradox*, 2nd ed., Chapters 1 and 3.
-/

public section

open Set MeasureTheory
open scoped ENNReal Pointwise

variable {X Y G : Type*}

namespace TauCeti

section SMul

variable [SMul G X] {S : Set X}

variable (G) in
/-- A set `S : Set X` is *paradoxical* for the action of `G` when it is nonempty and is the disjoint
union of two sets `A` and `B` each equidecomposable with `S` using `G`. -/
def Paradoxical (S : Set X) : Prop :=
  S.Nonempty ∧ ∃ A B : Set X, Disjoint A B ∧ A ∪ B = S ∧
    Equidecomposable G A S ∧ Equidecomposable G B S

/-- Unfolds `Paradoxical`: `S` is nonempty and the disjoint union of two sets each equidecomposable
with `S`. -/
theorem paradoxical_iff :
    Paradoxical G S ↔ S.Nonempty ∧ ∃ A B : Set X, Disjoint A B ∧ A ∪ B = S ∧
      Equidecomposable G A S ∧ Equidecomposable G B S :=
  Iff.rfl

/-- A paradoxical set is nonempty. -/
theorem Paradoxical.nonempty (h : Paradoxical G S) : S.Nonempty :=
  h.1

/-- The empty set is not paradoxical. -/
@[simp]
theorem not_paradoxical_empty : ¬ Paradoxical G (∅ : Set X) :=
  fun h => not_nonempty_empty h.nonempty

end SMul

section Group

variable [Group G] [MulAction G X] {S T : Set X}

/-- **Paradoxical sets from disjoint subcopies.** A set `S` is paradoxical exactly when it is
nonempty and contains two disjoint subsets, each equidecomposable with `S`. The two subsets need
not cover `S`. -/
theorem paradoxical_iff_exists_subset :
    Paradoxical G S ↔ S.Nonempty ∧ ∃ A ⊆ S, ∃ B ⊆ S, Disjoint A B ∧
      Equidecomposable G A S ∧ Equidecomposable G B S := by
  refine ⟨fun ⟨hS, A, B, hAB, hU, hA, hB⟩ =>
    ⟨hS, A, hU ▸ subset_union_left, B, hU ▸ subset_union_right, hAB, hA, hB⟩, ?_⟩
  rintro ⟨hS, A, hAS, B, hBS, hAB, hA, hB⟩
  -- `S \ A` lies in `S` and contains the copy `B` of `S`, so it is equidecomposable with `S`.
  refine ⟨hS, A, S \ A, disjoint_sdiff_right, union_sdiff_cancel hAS, hA, ?_⟩
  exact (equidecomposableLE_of_subset sdiff_subset).antisymm
    (equidecomposableLE_iff.2 ⟨B, subset_sdiff.2 ⟨hBS, hAB.symm⟩, hB.symm⟩)

/-- A set equidecomposable with a paradoxical set is paradoxical. -/
theorem Paradoxical.of_equidecomposable (h : Paradoxical G S) (hST : Equidecomposable G S T) :
    Paradoxical G T := by
  obtain ⟨hS, A, hAS, B, hBS, hAB, hA, hB⟩ := paradoxical_iff_exists_subset.1 h
  obtain ⟨f, rfl, rfl⟩ := equidecomposable_iff.1 hST
  -- Move the two disjoint copies `A` and `B` along `f`.
  have hsub {C : Set X} (hC : C ⊆ f.source) : f '' C ⊆ f.target :=
    f.image_source_eq_target ▸ image_mono hC
  have hcopy {C : Set X} (hC : C ⊆ f.source) (hCS : Equidecomposable G C f.source) :
      Equidecomposable G (f '' C) f.target :=
    (f.equidecomposable_image hC).symm.trans (hCS.trans f.equidecomposable)
  exact paradoxical_iff_exists_subset.2 ⟨f.image_source_eq_target ▸ hS.image f, f '' A, hsub hAS,
    f '' B, hsub hBS, hAB.image f.injOn hAS hBS, hcopy hAS hA, hcopy hBS hB⟩

/-- Equidecomposable sets are paradoxical together. -/
theorem Equidecomposable.paradoxical_iff (h : Equidecomposable G S T) :
    Paradoxical G S ↔ Paradoxical G T :=
  ⟨fun hS => hS.of_equidecomposable h, fun hT => hT.of_equidecomposable h.symm⟩

/-- An equivariant bijection `e : X ≃ Y` carries paradoxical sets to paradoxical sets. -/
theorem Paradoxical.image_equiv [MulAction G Y] (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (h : Paradoxical G S) :
    Paradoxical G (e '' S) := by
  obtain ⟨hS, A, hAS, B, hBS, hAB, hA, hB⟩ := paradoxical_iff_exists_subset.1 h
  exact paradoxical_iff_exists_subset.2 ⟨hS.image e, e '' A, image_mono hAS, e '' B,
    image_mono hBS, (disjoint_image_iff e.injective).2 hAB, hA.image_equiv e he,
    hB.image_equiv e he⟩

/-- Being paradoxical is invariant under equivariant bijections. -/
theorem paradoxical_image_equiv_iff [MulAction G Y] (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    Paradoxical G (e '' S) ↔ Paradoxical G S := by
  refine ⟨fun h => ?_, Paradoxical.image_equiv e he⟩
  have he' : ∀ (g : G) (y : Y), e.symm (g • y) = g • e.symm y := fun g y => by
    rw [e.symm_apply_eq, he, e.apply_symm_apply]
  simpa [e.symm_image_image] using h.image_equiv e.symm he'

section AddContent

variable {M : Type*} [AddCommMonoid M] {ν : AddContent M (univ : Set (Set X))}

/-- An additive content on all subsets of `X` that is invariant under `G` takes equal values on
equidecomposable sets. -/
theorem Equidecomposable.addContent_eq (hν : ∀ (g : G) (s : Set X), ν (g • s) = ν s)
    (h : Equidecomposable G S T) : ν S = ν T := by
  obtain ⟨E, rfl, rfl⟩ := Equidecomp.exists_iff_exists_equipartition.1 (equidecomposable_iff.1 h)
  have hsource : E.source = ⋃ p ∈ E.pieces, p.1 := by
    ext x
    simp [Equidecomp.Equipartition.mem_source]
  have htarget : E.target = ⋃ p ∈ E.pieces, p.2 • p.1 := by
    ext y
    simp [Equidecomp.Equipartition.mem_target]
  rw [hsource, htarget,
    addContent_biUnion (fun _ _ => mem_univ _) E.pairwiseDisjoint_fst (mem_univ _),
    addContent_biUnion (fun _ _ => mem_univ _) E.pairwiseDisjoint_smul (mem_univ _)]
  exact Finset.sum_congr rfl fun p _ => (hν p.2 p.1).symm

/-- An invariant additive content satisfies `ν S + ν S = ν S` on a paradoxical set `S`. -/
theorem Paradoxical.addContent_add_self (hν : ∀ (g : G) (s : Set X), ν (g • s) = ν s)
    (h : Paradoxical G S) : ν S + ν S = ν S := by
  obtain ⟨-, A, B, hAB, rfl, hA, hB⟩ := h
  have hunion := addContent_union' (m := ν) (mem_univ A) (mem_univ B) (mem_univ _) hAB
  rw [hA.addContent_eq hν, hB.addContent_eq hν] at hunion
  exact hunion.symm

/-- An invariant additive content with values in a cancellative monoid vanishes on paradoxical
sets. -/
theorem Paradoxical.addContent_eq_zero [IsLeftCancelAdd M]
    (hν : ∀ (g : G) (s : Set X), ν (g • s) = ν s) (h : Paradoxical G S) : ν S = 0 :=
  add_eq_left.1 (h.addContent_add_self hν)

/-- An invariant `ℝ≥0∞`-valued additive content takes the value `0` or `∞` on a paradoxical set.
Thus a finite invariant content cannot give a paradoxical set positive mass. -/
theorem Paradoxical.addContent_eq_zero_or_eq_top {ν : AddContent ℝ≥0∞ (univ : Set (Set X))}
    (hν : ∀ (g : G) (s : Set X), ν (g • s) = ν s) (h : Paradoxical G S) :
    ν S = 0 ∨ ν S = ∞ := by
  refine or_iff_not_imp_right.2 fun htop => ?_
  exact (ENNReal.add_right_inj htop).1 ((h.addContent_add_self hν).trans (add_zero _).symm)

/-- If `X` carries an invariant finitely additive probability on all subsets, then `X` is not
paradoxical. -/
theorem not_paradoxical_univ_of_addContent {ν : AddContent ℝ≥0∞ (univ : Set (Set X))}
    (hν : ∀ (g : G) (s : Set X), ν (g • s) = ν s) (hν₁ : ν univ = 1) :
    ¬ Paradoxical G (univ : Set X) := fun h => by
  rcases h.addContent_eq_zero_or_eq_top hν with h0 | h0 <;> simp [hν₁] at h0

end AddContent

end Group

end TauCeti
