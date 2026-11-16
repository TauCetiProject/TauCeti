/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PresentedGroup
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree
public import TauCeti.ModelTheory.Algebra.Group.ExistentialUniversal

/-!
# Triviality of words in a presented residually free group

Let `G` be a residually free group with a finite presentation `⟨x₁, …, x_n ∣ S⟩`. A word `w` in
the generators is trivial in `G` if and only if the universal sentence

`Φ_{S,w} = ∀ x₁ … ∀ x_n, (⋀ s ∈ S, s(x) = 1) → w(x) = 1`

of the language of groups (without constants) holds in the free group `F₂` of rank two. This
applies in particular to fully residually free groups, hence to limit groups.

* If `w` is trivial in `G` it lies in the normal closure of `S`, so it vanishes at every tuple
  of every group at which `S` vanishes.
* Conversely, suppose `F₂` satisfies `Φ_{S,w}` but `w` is nontrivial at the generating tuple
  `x` of `G`. A homomorphism `φ : G → F₂` keeping `w(x)` nontrivial maps `x` to a tuple of `F₂` at
  which `S` vanishes and `w` does not, which contradicts `Φ_{S,w}`.

The second argument uses only that `Φ_{S,w}` is a quasi-identity: such sentences pass from `F₂`
to every group separated by `F₂`. This reduces the word problem of such a group to the universal
theory of a free group. In the terminology of algebraic geometry over groups, `Φ_{S,w}` says that
`w` belongs to the radical of the coefficient-free system `S = 1` over a free group, and for a
residually free group `⟨x₁, …, x_n ∣ S⟩` this radical is the normal closure of `S`.

## Main results

* `TauCeti.LimitGroup.IsResiduallyFree.lift_eq_one_of_realize_noSolutionSentence`: in a
  residually free group, a word vanishes at every tuple satisfying relators `S` as soon as `F₂`
  satisfies `Φ_{S,w}`.
* `TauCeti.LimitGroup.IsResiduallyFree.lift_eq_one_iff_realize_noSolutionSentence`: for a tuple
  of a residually free group whose relations are exactly the normal closure of a finite set `S`,
  a word vanishes at the tuple if and only if `F₂` satisfies `Φ_{S,w}`.
* `TauCeti.LimitGroup.IsResiduallyFree.mk_eq_one_iff_realize_noSolutionSentence`: the same
  criterion for the group `PresentedGroup S`.

The file ends with two instances of the criterion: the presentation of a free group with no
relators, where it says that `F₂` satisfies the law `w = 1` only for the trivial word, and the
presentation `⟨x ∣ x⟩` of the trivial group, where it says that every word is a consequence of
`x`.

## References

* O. Kharlampovich, A. G. Myasnikov, *Effective JSJ decompositions*, in *Groups, languages,
  algorithms*, Contemp. Math. 378 (2005), §3, Theorem 3.1 (1) and §3.2.
-/

public section

open FirstOrder FirstOrder.Language

namespace TauCeti.LimitGroup

attribute [local instance] TauCeti.Group.structureOfGroup

variable {G : Type*} [Group G] {n : ℕ}

/-- In a residually free group `G`, if the free group `F₂` satisfies the universal sentence
`∀ x, S(x) = 1 → w(x) = 1`, then `w` vanishes at every tuple of `G` at which the words of `S`
vanish. -/
theorem IsResiduallyFree.lift_eq_one_of_realize_noSolutionSentence
    (h : IsResiduallyFree G) {X : Fin n → G} {S : Finset (FreeGroup (Fin n))}
    (hS : ∀ s ∈ S, FreeGroup.lift X s = 1) {w : FreeGroup (Fin n)}
    (hw : FreeGroup (Fin 2) ⊨ group.noSolutionSentence S {w}) : FreeGroup.lift X w = 1 := by
  by_contra hne
  obtain ⟨φ, hφ⟩ := isResiduallyFree_iff_fin_two.1 h _ hne
  have hφX (u) : φ (FreeGroup.lift X u) = FreeGroup.lift (φ ∘ X) u :=
    FreeGroup.lift_unique (φ.comp (FreeGroup.lift X)) (by simp)
  exact hφ <| (hφX w).trans <| (group.realize_noSolutionSentence_singleton S w).1 hw _
    fun s hs => by rw [← hφX, hS s hs, map_one]

/-- **Triviality of a word as a universal sentence.** Let `X` be a tuple of a residually free
group `G` whose relations are exactly the consequences of a finite set `S` of words, that
is, the kernel of `FreeGroup.lift X` is the normal closure of `S`. Then a word `w` is trivial at
`X` if and only if the free group `F₂` satisfies the universal sentence
`∀ x, S(x) = 1 → w(x) = 1`. -/
theorem IsResiduallyFree.lift_eq_one_iff_realize_noSolutionSentence
    (h : IsResiduallyFree G) {X : Fin n → G} {S : Finset (FreeGroup (Fin n))}
    (hS : (FreeGroup.lift X).ker = Subgroup.normalClosure (S : Set (FreeGroup (Fin n))))
    (w : FreeGroup (Fin n)) :
    FreeGroup.lift X w = 1 ↔ FreeGroup (Fin 2) ⊨ group.noSolutionSentence S {w} := by
  refine ⟨fun hw => group.realize_noSolutionSentence_singleton_of_mem_normalClosure ?_,
    h.lift_eq_one_of_realize_noSolutionSentence fun s hs => ?_⟩
  · rwa [← hS, MonoidHom.mem_ker]
  · rw [← MonoidHom.mem_ker, hS]
    exact Subgroup.subset_normalClosure hs

/-- **Triviality of a word in a finitely presented residually free group.** If the group
`⟨x₁, …, x_n ∣ S⟩` presented by a finite set `S` of relators is residually free, a word `w`
represents its identity if and only if the free group `F₂` satisfies the universal sentence
`∀ x, S(x) = 1 → w(x) = 1`. -/
theorem IsResiduallyFree.mk_eq_one_iff_realize_noSolutionSentence
    {S : Finset (FreeGroup (Fin n))}
    (h : IsResiduallyFree (PresentedGroup (S : Set (FreeGroup (Fin n)))))
    (w : FreeGroup (Fin n)) :
    PresentedGroup.mk (S : Set (FreeGroup (Fin n))) w = 1 ↔
      FreeGroup (Fin 2) ⊨ group.noSolutionSentence S {w} := by
  rw [← PresentedGroup.lift_of_eq_mk]
  exact h.lift_eq_one_iff_realize_noSolutionSentence
    (by ext g; simp [PresentedGroup.mk_eq_one_iff]) w

/-! ### The free presentation and the trivial group -/

/-- For the presentation of the free group on `n` generators with no relators, the criterion
agrees with the reduction criterion for triviality of a word: the free group `F₂` satisfies the
law `∀ x, w(x) = 1` exactly when the reduced word of `w` is empty. -/
example (w : FreeGroup (Fin n)) :
    FreeGroup (Fin 2) ⊨ group.noSolutionSentence ∅ {w} ↔ w.toWord = [] := by
  have h := IsResiduallyFree.lift_eq_one_iff_realize_noSolutionSentence
    isFullyResiduallyFree_of_isFreeGroup.isResiduallyFree
    (X := (FreeGroup.of : Fin n → FreeGroup (Fin n))) (S := ∅)
    (by simp [FreeGroup.lift_of_eq_id]) w
  rw [← h, FreeGroup.lift_of_apply, FreeGroup.toWord_eq_nil_iff]

/-- In the presentation `⟨x ∣ x⟩` of the trivial group every word represents the identity:
`F₂` satisfies `∀ x, x = 1 → w(x) = 1` for every word `w` in one variable. -/
example (w : FreeGroup (Fin 1)) :
    FreeGroup (Fin 2) ⊨ group.noSolutionSentence {FreeGroup.of 0} {w} := by
  have hS : (FreeGroup.lift fun _ : Fin 1 => (1 : Unit)).ker =
      Subgroup.normalClosure (({FreeGroup.of 0} : Finset (FreeGroup (Fin 1))) :
        Set (FreeGroup (Fin 1))) := by
    refine le_antisymm (fun g _ => ?_) fun g _ => Subsingleton.elim _ _
    have hcl : Subgroup.closure (Set.range (FreeGroup.of : Fin 1 → FreeGroup (Fin 1))) ≤
        Subgroup.normalClosure {FreeGroup.of 0} := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_normalClosure (by simp [Subsingleton.elim i 0])
    simpa using hcl (by simp [FreeGroup.closure_range_of])
  exact (IsResiduallyFree.lift_eq_one_iff_realize_noSolutionSentence
    isFullyResiduallyFree_of_subsingleton.isResiduallyFree hS w).1 (Subsingleton.elim _ _)

end TauCeti.LimitGroup
