/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.UniversalTheory
public import TauCeti.GroupTheory.LimitGroup.Characterization
public import TauCeti.ModelTheory.Algebra.Group.ExistentialUniversal
import TauCeti.GroupTheory.LimitGroup.TwoGenerator

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

Among finitely generated groups, this inclusion of universal theories already characterizes full
residual freeness. The reverse inclusion holds as well, with the free group chosen according to
three cases:

* a nonabelian residually free group contains a free group of rank two, and universal sentences
  pass to subgroups, so a nonabelian fully residually free group has the universal theory of `F₂`;
* a fully residually free group is torsion-free, and a nontrivial torsion-free abelian group has
  the universal theory of `ℤ` (see `TauCeti.GroupTheory.GroupAlgGeom.UniversalTheory`);
* a trivial group is the free group of rank zero.

Hence a fully residually free group has the universal theory of a free group of rank at most two.
A finitely generated group is therefore fully residually free, or equivalently a limit group, if
and only if it has the universal theory of a free group of finite rank: these are the
equivalences of conditions (5), respectively (2), with (3) in Theorem 1.1 of Champetier and
Guirardel. The three cases are their Theorem 5.1.

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
* `TauCeti.LimitGroup.IsResiduallyFree.realize_freeGroup_of_isUniversal`: a universal sentence
  that holds in a nonabelian residually free group holds in `F₂`.
* `IsFullyResiduallyFree.realize_iff_freeGroup_of_not_isMulCommutative_of_isUniversal`, in
  `TauCeti.LimitGroup`: a nonabelian fully residually free group has the universal theory of
  `F₂`.
* `TauCeti.LimitGroup.IsFullyResiduallyFree.exists_forall_isUniversal_realize_iff_freeGroup`: a
  fully residually free group has the universal theory of a free group of rank at most two.
* `TauCeti.LimitGroup.isFullyResiduallyFree_iff_exists_forall_isUniversal_realize_iff_freeGroup`:
  a finitely generated group is fully residually free if and only if it has the universal theory
  of a free group of finite rank.
* `TauCeti.LimitGroup.isLimitGroup_iff_exists_forall_isUniversal_realize_iff_freeGroup`: a group
  is a limit group if and only if it is finitely generated and has the universal theory of a free
  group of finite rank.

## References

* C. Champetier, V. Guirardel, *Limit groups as limits of free groups*, Israel J. Math. 146
  (2005), Theorem 1.1 and Theorem 5.1.
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
    G ⊨ σ :=
  (isFullyResiduallyFree_iff_isDiscriminatedBy.1 h).realize_of_isUniversal hσ hF

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

/-- Every universal sentence of the group language that holds in a nonabelian residually free
group also holds in the free group of rank two. -/
theorem IsResiduallyFree.realize_freeGroup_of_isUniversal (h : IsResiduallyFree G)
    (hG : ¬IsMulCommutative G) {σ : Language.group.Sentence} (hσ : σ.IsUniversal) (hGσ : G ⊨ σ) :
    FreeGroup (Fin 2) ⊨ σ := by
  obtain ⟨a, b, hab⟩ : ∃ a b : G, ¬Commute a b := by
    by_contra! hc
    exact hG ⟨⟨hc⟩⟩
  -- The two noncommuting elements generate a free subgroup of rank two.
  exact (FreeGroup.lift ![a, b]).realize_of_isUniversal_of_injective
    (h.injective_lift_of_not_commute hab) hσ hGσ

/-- A nonabelian fully residually free group has the universal theory of the free group of rank
two. -/
theorem IsFullyResiduallyFree.realize_iff_freeGroup_of_not_isMulCommutative_of_isUniversal
    (h : IsFullyResiduallyFree G) (hG : ¬IsMulCommutative G) {σ : Language.group.Sentence}
    (hσ : σ.IsUniversal) : G ⊨ σ ↔ FreeGroup (Fin 2) ⊨ σ :=
  ⟨h.isResiduallyFree.realize_freeGroup_of_isUniversal hG hσ, h.realize_of_isUniversal hσ⟩

/-- **The universal theory of a fully residually free group.** A fully residually free group has
the universal theory of a free group of rank at most two. -/
theorem IsFullyResiduallyFree.exists_forall_isUniversal_realize_iff_freeGroup
    (h : IsFullyResiduallyFree G) :
    ∃ n ≤ 2, ∀ σ : Language.group.Sentence, σ.IsUniversal → (G ⊨ σ ↔ FreeGroup (Fin n) ⊨ σ) := by
  by_cases hG : IsMulCommutative G
  · rcases subsingleton_or_nontrivial G with _ | _
    · have := uniqueOfSubsingleton (1 : G)
      exact ⟨0, zero_le_two, fun σ _ =>
        (MulEquiv.ofUnique : G ≃* FreeGroup (Fin 0)).realize_sentence_iff σ⟩
    · have := h.isResiduallyFree.isMulTorsionFree
      exact ⟨1, one_le_two, fun σ hσ =>
        (realize_iff_multiplicative_int_of_isMulCommutative_of_isMulTorsionFree_of_isUniversal
          hσ).trans ((FreeGroup.mulEquivIntOfUnique (α := Fin 1)).realize_sentence_iff σ).symm⟩
  · exact ⟨2, le_rfl, fun σ hσ =>
      h.realize_iff_freeGroup_of_not_isMulCommutative_of_isUniversal hG hσ⟩

/-- A finitely generated group is fully residually free if and only if it has the universal
theory of a free group of finite rank (Champetier and Guirardel, Theorem 1.1). -/
theorem isFullyResiduallyFree_iff_exists_forall_isUniversal_realize_iff_freeGroup [Group.FG G] :
    IsFullyResiduallyFree G ↔ ∃ n : ℕ, ∀ σ : Language.group.Sentence, σ.IsUniversal →
      (G ⊨ σ ↔ FreeGroup (Fin n) ⊨ σ) :=
  ⟨fun h => h.exists_forall_isUniversal_realize_iff_freeGroup.imp fun _ => And.right,
    fun ⟨_, hn⟩ => isFullyResiduallyFree_of_forall_isUniversal fun σ hσ => (hn σ hσ).2⟩

/-- A group is a limit group if and only if it is finitely generated and satisfies every universal
sentence of the group language that holds in the free group of rank two. -/
theorem isLimitGroup_iff_forall_isUniversal :
    IsLimitGroup G ↔ Group.FG G ∧
      ∀ σ : Language.group.Sentence, σ.IsUniversal → FreeGroup (Fin 2) ⊨ σ → G ⊨ σ :=
  isLimitGroup_iff_isFullyResiduallyFree.trans <| and_congr_right fun _ =>
    isFullyResiduallyFree_iff_forall_isUniversal

/-- A group is a limit group if and only if it is finitely generated and has the universal theory
of a free group of finite rank (Champetier and Guirardel, Theorem 1.1). -/
theorem isLimitGroup_iff_exists_forall_isUniversal_realize_iff_freeGroup :
    IsLimitGroup G ↔ Group.FG G ∧ ∃ n : ℕ, ∀ σ : Language.group.Sentence, σ.IsUniversal →
      (G ⊨ σ ↔ FreeGroup (Fin n) ⊨ σ) :=
  isLimitGroup_iff_isFullyResiduallyFree.trans <| and_congr_right fun _ =>
    isFullyResiduallyFree_iff_exists_forall_isUniversal_realize_iff_freeGroup

end TauCeti.LimitGroup
