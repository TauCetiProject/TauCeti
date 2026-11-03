/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.UniversalTheory
public import TauCeti.GroupTheory.LimitGroup.Characterization
public import TauCeti.ModelTheory.Algebra.Group.ExistentialUniversal
public import TauCeti.ModelTheory.Complexity

/-!
# Fully residually free groups and the universal theory of free groups

A finitely generated group is fully residually free if and only if it satisfies every universal
sentence of the language of groups (without constants) that holds in the free group `F₂` of rank
two.

* A fully residually free group is discriminated by `F₂`, and discrimination preserves universal
  sentences (`TauCeti.GroupAlgGeom.IsDiscriminatedBy.realize_of_isUniversal`).
* Conversely, let `G` satisfy every universal sentence true in some free group `F`, and let
  `S : Fin n → G`. For a finite set `W` of words, the words of `W` that vanish at `S` and those
  that do not form a system of equations and inequations solved by `S`. The universal sentence
  saying that this system has no solution therefore fails in `G`, hence in `F`. A solution in
  `F` is a marking of a free group that agrees with `S` on `W`, and as `W` grows these markings
  converge to the marking of `S` in the space of marked groups. So `G` is a limit group when it
  is finitely generated, hence fully residually free.

This gives one inclusion of universal theories between a finitely generated fully residually free
group and a free group, and shows that it already characterizes full residual freeness.

## Main results

* `TauCeti.LimitGroup.IsFullyResiduallyFree.realize_of_isUniversal`: a fully residually free group
  satisfies every universal sentence that holds in `F₂`.
* `TauCeti.LimitGroup.ofMarking_mem_closure_freeMarkings_of_forall_isUniversal`: if every universal
  sentence true in a free group holds in `G`, every finite tuple of `G` marks a limit of markings
  of free groups.
* `TauCeti.LimitGroup.isFullyResiduallyFree_iff_forall_isUniversal`: a finitely generated group is
  fully residually free if and only if it satisfies every universal sentence true in `F₂`.
* `TauCeti.LimitGroup.isLimitGroup_iff_forall_isUniversal`: the same characterization of limit
  groups.

## References

* C. Champetier, V. Guirardel, *Limit groups as limits of free groups*, Israel J. Math. 146
  (2005), Theorem 1.1.
* V. N. Remeslennikov, *∃-free groups*, Siberian Math. J. 30 (1989).
-/

public section

open Filter Topology FirstOrder FirstOrder.Language

namespace TauCeti.LimitGroup

open GroupAlgGeom MarkedGroup

attribute [local instance] TauCeti.Group.structureOfGroup

variable {G : Type*} [Group G]

/-- A fully residually free group satisfies every universal sentence of the group language that
holds in the free group of rank two. -/
theorem IsFullyResiduallyFree.realize_of_isUniversal (h : IsFullyResiduallyFree G)
    {σ : Language.group.Sentence} (hσ : σ.IsUniversal) (hF : FreeGroup (Fin 2) ⊨ σ) :
    G ⊨ σ := by
  -- Read `σ` in the group language with an empty set of coefficient names.
  let c : Empty → Unit := Empty.elim
  let : (constantsOn Empty).Structure G := constantsOn.structure ((1 : Unit →* G) ∘ c)
  let : (constantsOn Empty).Structure (FreeGroup (Fin 2)) :=
    constantsOn.structure ((1 : Unit →* FreeGroup (Fin 2)) ∘ c)
  have := (isFullyResiduallyFree_iff_isDiscriminatedBy.1 h).realize_of_isUniversal
    (σ := (Language.group.lhomWithConstants Empty).onSentence σ) c (hσ.onBoundedFormula _)
  rw [LHom.realize_onSentence, LHom.realize_onSentence] at this
  exact this hF

/-- If every universal sentence of the group language that holds in a free group `F` holds in
`G`, then every finite tuple of `G` marks a limit of markings of free groups. -/
theorem ofMarking_mem_closure_freeMarkings_of_forall_isUniversal {F : Type*} [Group F]
    [IsFreeGroup F] (h : ∀ σ : Language.group.Sentence, σ.IsUniversal → F ⊨ σ → G ⊨ σ)
    {n : ℕ} (S : Fin n → G) : ofMarking S ∈ closure (freeMarkings n) := by
  classical
  -- For each finite set of words, a tuple of `F` on which the same words vanish as at `S`.
  have hT (W : Finset (FreeGroup (Fin n))) : ∃ T : Fin n → F,
      ∀ w ∈ W, (FreeGroup.lift T w = 1 ↔ FreeGroup.lift S w = 1) := by
    have hG : ¬G ⊨ group.noSolutionSentence (W.filter (FreeGroup.lift S · = 1))
        (W.filter (FreeGroup.lift S · ≠ 1)) := by
      rw [group.realize_noSolutionSentence, not_not]
      exact ⟨S, fun e he => (Finset.mem_filter.1 he).2, fun i hi => (Finset.mem_filter.1 hi).2⟩
    have hF := mt (h _ (group.isUniversal_noSolutionSentence _ _)) hG
    rw [group.realize_noSolutionSentence, not_not] at hF
    obtain ⟨T, hE, hI⟩ := hF
    refine ⟨T, fun w hw => ?_⟩
    by_cases hw' : FreeGroup.lift S w = 1
    · exact iff_of_true (hE w (Finset.mem_filter.2 ⟨hw, hw'⟩)) hw'
    · exact iff_of_false (hI w (Finset.mem_filter.2 ⟨hw, hw'⟩)) hw'
  choose T hT using hT
  refine mem_closure_of_tendsto (f := fun W => ofMarking (T W)) (b := atTop) ?_
    (Eventually.of_forall fun W => ofMarking_mem_freeMarkings _)
  rw [tendsto_nhds_iff]
  intro w
  filter_upwards [eventually_ge_atTop {w}] with W hW
  simpa only [mem_ofMarking_ker] using hT W w (hW (Finset.mem_singleton_self w))

/-- A finitely generated group satisfying every universal sentence of the group language that
holds in a free group `F` is fully residually free. -/
theorem isFullyResiduallyFree_of_forall_isUniversal [Group.FG G] {F : Type*} [Group F]
    [IsFreeGroup F] (h : ∀ σ : Language.group.Sentence, σ.IsUniversal → F ⊨ σ → G ⊨ σ) :
    IsFullyResiduallyFree G :=
  (isLimitGroup_iff.2 ⟨‹_›, fun _ S =>
    ofMarking_mem_closure_freeMarkings_of_forall_isUniversal h S⟩).isFullyResiduallyFree

/-- **Universal characterization of fully residually free groups.** A finitely generated group is
fully residually free if and only if it satisfies every universal sentence of the group language
that holds in the free group of rank two. -/
theorem isFullyResiduallyFree_iff_forall_isUniversal [Group.FG G] :
    IsFullyResiduallyFree G ↔
      ∀ σ : Language.group.Sentence, σ.IsUniversal → FreeGroup (Fin 2) ⊨ σ → G ⊨ σ :=
  ⟨fun h _ hσ hF => h.realize_of_isUniversal hσ hF, isFullyResiduallyFree_of_forall_isUniversal⟩

/-- A group is a limit group if and only if it is finitely generated and satisfies every universal
sentence of the group language that holds in the free group of rank two. -/
theorem isLimitGroup_iff_forall_isUniversal :
    IsLimitGroup G ↔ Group.FG G ∧
      ∀ σ : Language.group.Sentence, σ.IsUniversal → FreeGroup (Fin 2) ⊨ σ → G ⊨ σ := by
  rw [isLimitGroup_iff_isFullyResiduallyFree]
  exact ⟨fun ⟨_, h⟩ => ⟨‹_›, isFullyResiduallyFree_iff_forall_isUniversal.1 h⟩,
    fun ⟨_, h⟩ => ⟨‹_›, isFullyResiduallyFree_iff_forall_isUniversal.2 h⟩⟩

end TauCeti.LimitGroup
