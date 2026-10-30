/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Action.Equidecomp

/-!
# Paradoxical sets

Let `G` act on `X`. A set `S : Set X` is *paradoxical*, `TauCeti.Paradoxical G S`, when it is
nonempty and splits into two disjoint sets `A ∪ B = S` each of which is equidecomposable with `S`
using `G`. Informally, `S` can be cut into finitely many pieces which, moved by elements of `G`,
reassemble into two copies of `S`. The empty set satisfies the splitting condition trivially and is
excluded by the nonemptiness requirement.

The main result, `TauCeti.paradoxical_iff_exists_subset`, says that it is enough to find two
disjoint subsets of `S`, not necessarily covering `S`, each equidecomposable with `S`. This is how
paradoxical decompositions are usually exhibited, for instance for the free group of rank two. The
proof enlarges one of the two subsets to the complement of the other using the Schröder–Bernstein
theorem for equidecompositions, `TauCeti.EquidecomposableLE.antisymm`.

Paradoxicality is invariant under equidecomposition, under equivariant bijections, and under
changes of the acting group that do not change the action.

## Main definitions

* `TauCeti.Paradoxical G S`: `S` is nonempty and is the union of two disjoint sets, each
  equidecomposable with `S` using `G`.

## Main results

* `TauCeti.paradoxical_iff_exists_subset`: `S` is paradoxical exactly when it is nonempty and has
  two disjoint subsets each equidecomposable with `S`.
* `TauCeti.Paradoxical.of_equidecomposable`, `TauCeti.Equidecomposable.paradoxical_iff`:
  paradoxicality passes to equidecomposable sets.
* `TauCeti.paradoxical_image_equiv_iff`: paradoxicality is invariant under equivariant bijections.
* `TauCeti.paradoxical_iff_of_surjective`: paradoxicality depends only on the transformations
  through which the group acts.

## References

* A. Garrido, *An introduction to amenable groups*, §1.
* G. Tomkowicz, S. Wagon, *The Banach–Tarski Paradox*, 2nd ed., Definition 1.1 and Chapter 3.
-/

public section

open Function Set

variable {X Y G H : Type*}

namespace TauCeti

section SMul

variable [SMul G X]

variable (G) in
/-- A set `S : Set X` is *paradoxical* for the action of `G` when it is nonempty and is the union
of two disjoint sets `A` and `B`, each equidecomposable with `S` using `G`. -/
def Paradoxical (S : Set X) : Prop :=
  S.Nonempty ∧ ∃ A B : Set X, Disjoint A B ∧ A ∪ B = S ∧
    Equidecomposable G A S ∧ Equidecomposable G B S

variable {S : Set X}

/-- Unfolds `Paradoxical`. -/
theorem paradoxical_iff :
    Paradoxical G S ↔ S.Nonempty ∧ ∃ A B : Set X, Disjoint A B ∧ A ∪ B = S ∧
      Equidecomposable G A S ∧ Equidecomposable G B S :=
  Iff.rfl

/-- A paradoxical set is nonempty. -/
theorem Paradoxical.nonempty (h : Paradoxical G S) : S.Nonempty :=
  h.1

/-- The empty set is not paradoxical. -/
@[simp]
theorem not_paradoxical_empty : ¬Paradoxical G (∅ : Set X) :=
  fun h => not_nonempty_empty h.nonempty

/-- Paradoxicality is preserved by an equivariant bijection `e : X ≃ Y`. -/
theorem Paradoxical.image_equiv [SMul G Y] (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (h : Paradoxical G S) :
    Paradoxical G (e '' S) := by
  obtain ⟨hS, A, B, hAB, rfl, hA, hB⟩ := h
  exact ⟨hS.image e, e '' A, e '' B, hAB.image e.injective.injOn (subset_univ _) (subset_univ _),
    (image_union e A B).symm, hA.image_equiv e he, hB.image_equiv e he⟩

/-- Paradoxicality is invariant under equivariant bijections. -/
theorem paradoxical_image_equiv_iff [SMul G Y] (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    Paradoxical G (e '' S) ↔ Paradoxical G S := by
  refine ⟨fun h => ?_, Paradoxical.image_equiv e he⟩
  have he' : ∀ (g : G) (y : Y), e.symm (g • y) = g • e.symm y := fun g y => by
    rw [e.symm_apply_eq, he, e.apply_symm_apply]
  simpa [e.symm_image_image] using h.image_equiv e.symm he'

/-- A set paradoxical using `G` is paradoxical using `H` when each element of `G` acts as some
element of `H` does. -/
theorem Paradoxical.of_smul_eq [SMul H X] (φ : G → H) (hφ : ∀ (g : G) (x : X), φ g • x = g • x)
    (h : Paradoxical G S) : Paradoxical H S := by
  obtain ⟨hS, A, B, hAB, hAB', hA, hB⟩ := h
  exact ⟨hS, A, B, hAB, hAB', hA.of_smul_eq φ hφ, hB.of_smul_eq φ hφ⟩

/-- Paradoxicality depends only on the transformations through which the group acts: a surjection
`φ : G → H` with `φ g • x = g • x` identifies paradoxicality using `G` and using `H`. -/
theorem paradoxical_iff_of_surjective [SMul H X] {φ : G → H} (hφs : Surjective φ)
    (hφ : ∀ (g : G) (x : X), φ g • x = g • x) : Paradoxical G S ↔ Paradoxical H S := by
  simp only [paradoxical_iff, equidecomposable_iff_of_surjective hφs hφ]

end SMul

section Group

variable [Group G] [MulAction G X] {S T : Set X}

/-- **Paradoxical decompositions from disjoint subcopies.** A set `S` is paradoxical exactly when
it is nonempty and has two disjoint subsets `A, B ⊆ S`, not necessarily covering `S`, each
equidecomposable with `S`. -/
theorem paradoxical_iff_exists_subset :
    Paradoxical G S ↔ S.Nonempty ∧ ∃ A ⊆ S, ∃ B ⊆ S, Disjoint A B ∧
      Equidecomposable G A S ∧ Equidecomposable G B S := by
  refine ⟨fun ⟨hS, A, B, hAB, hU, hA, hB⟩ => ⟨hS, A, hU ▸ subset_union_left, B,
    hU ▸ subset_union_right, hAB, hA, hB⟩, fun ⟨hS, A, hAS, B, hBS, hAB, hA, hB⟩ => ?_⟩
  -- Enlarge `B` to the complement `S \ A`: it lies between `B` and `S`, and `B ∼ S`.
  have hB' : Equidecomposable G (S \ A) S :=
    (equidecomposableLE_of_subset sdiff_subset).antisymm
      (equidecomposableLE_iff.2 ⟨B, subset_sdiff.2 ⟨hBS, hAB.symm⟩, hB.symm⟩)
  exact ⟨hS, A, S \ A, disjoint_sdiff_right, union_sdiff_cancel hAS, hA, hB'⟩

/-- Paradoxicality passes from a set to every set equidecomposable with it. -/
theorem Paradoxical.of_equidecomposable (hS : Paradoxical G S) (hST : Equidecomposable G S T) :
    Paradoxical G T := by
  obtain ⟨hne, A, hAS, B, hBS, hAB, hA, hB⟩ := paradoxical_iff_exists_subset.1 hS
  obtain ⟨f, rfl, rfl⟩ := equidecomposable_iff.1 hST
  refine paradoxical_iff_exists_subset.2 ⟨f.equidecomposable.nonempty_iff.1 hne, f '' A,
    f.image_source_eq_target ▸ image_mono hAS, f '' B, f.image_source_eq_target ▸ image_mono hBS,
    hAB.image f.injOn hAS hBS, ?_, ?_⟩
  · exact (f.equidecomposable_image hAS).symm.trans (hA.trans f.equidecomposable)
  · exact (f.equidecomposable_image hBS).symm.trans (hB.trans f.equidecomposable)

/-- Equidecomposable sets are simultaneously paradoxical or not. -/
theorem Equidecomposable.paradoxical_iff (hST : Equidecomposable G S T) :
    Paradoxical G S ↔ Paradoxical G T :=
  ⟨fun h => h.of_equidecomposable hST, fun h => h.of_equidecomposable hST.symm⟩

end Group

end TauCeti
