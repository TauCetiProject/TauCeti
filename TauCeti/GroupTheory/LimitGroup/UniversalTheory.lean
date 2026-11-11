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

This inclusion of universal theories already characterizes full residual freeness. The reverse
inclusion holds as well, with the free group chosen according to three cases, because universal
sentences pass to subgroups:

* a nonabelian residually free group contains a free group of rank two, so a nonabelian fully
  residually free group has the universal theory of `F₂`;
* a nontrivial torsion-free abelian group contains `ℤ`, and each of its finitely generated
  subgroups is a free abelian group of finite rank, hence discriminated by `ℤ`; as a universal
  sentence holds in a group as soon as it holds in its finitely generated subgroups, such a group
  has the universal theory of `ℤ`;
* a trivial group is the free group of rank zero.

Hence a fully residually free group has the universal theory of a free group of rank at most two,
and a finitely generated group is fully residually free if and only if it has the universal
theory of a free group of finite rank, which is the equivalence of conditions (3) and (5) in
Theorem 1.1 of Champetier and Guirardel; the three cases are their Theorem 5.1.

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
* `TauCeti.LimitGroup.IsFullyResiduallyFree.realize_iff_freeGroup_of_not_isMulCommutative`: a
  nonabelian fully residually free group has the universal theory of `F₂`.
* `TauCeti.LimitGroup.realize_iff_multiplicative_int_of_isMulTorsionFree`: a nontrivial
  torsion-free abelian group has the universal theory of `ℤ`.
* `TauCeti.LimitGroup.IsFullyResiduallyFree.exists_forall_realize_iff_freeGroup`: a fully
  residually free group has the universal theory of a free group of rank at most two.
* `TauCeti.LimitGroup.isFullyResiduallyFree_iff_exists_forall_realize_iff`: a finitely generated
  group is fully residually free if and only if it has the universal theory of a free group of
  finite rank.

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
  (isFullyResiduallyFree_iff_isDiscriminatedBy.1 h).realize_group_of_isUniversal hσ hF

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

/-- A nonabelian residually free group contains a free group of rank two, so every universal
sentence of the group language that holds in it holds in the free group of rank two. -/
theorem IsResiduallyFree.realize_freeGroup_of_isUniversal (h : IsResiduallyFree G)
    (hG : ¬IsMulCommutative G) {σ : Language.group.Sentence} (hσ : σ.IsUniversal) (hGσ : G ⊨ σ) :
    FreeGroup (Fin 2) ⊨ σ := by
  obtain ⟨a, b, hab⟩ : ∃ a b : G, ¬Commute a b := by
    by_contra! hc
    exact hG ⟨⟨hc⟩⟩
  exact (FreeGroup.lift ![a, b]).realize_of_isUniversal_of_injective
    (h.injective_lift_of_not_commute hab) hσ hGσ

/-- A nonabelian fully residually free group has the universal theory of the free group of rank
two. -/
theorem IsFullyResiduallyFree.realize_iff_freeGroup_of_not_isMulCommutative
    (h : IsFullyResiduallyFree G) (hG : ¬IsMulCommutative G) {σ : Language.group.Sentence}
    (hσ : σ.IsUniversal) : G ⊨ σ ↔ FreeGroup (Fin 2) ⊨ σ :=
  ⟨h.isResiduallyFree.realize_freeGroup_of_isUniversal hG hσ, h.realize_of_isUniversal hσ⟩

/-- A nontrivial torsion-free abelian group has the universal theory of the infinite cyclic group
`ℤ`: it contains `ℤ`, and each of its finitely generated subgroups is a free abelian group of
finite rank, hence discriminated by `ℤ`. -/
theorem realize_iff_multiplicative_int_of_isMulTorsionFree [IsMulCommutative G]
    [IsMulTorsionFree G] [Nontrivial G] {σ : Language.group.Sentence} (hσ : σ.IsUniversal) :
    G ⊨ σ ↔ Multiplicative ℤ ⊨ σ := by
  classical
  refine ⟨fun hG => ?_, fun hZ => group.realize_of_isUniversal_of_forall_closure hσ fun S => ?_⟩
  · obtain ⟨g, hg⟩ := exists_ne (1 : G)
    exact (zpowersHom G g).realize_of_isUniversal_of_injective
      (injective_zpow_iff_not_isOfFinOrder.2 (not_isOfFinOrder_of_isMulTorsionFree hg)) hσ hG
  · obtain ⟨k, -, ⟨e⟩⟩ := Subgroup.exists_mulEquiv_closure_of_pairwise_commute
      (s := S) fun a _ b _ _ => mul_comm' a b
    exact (e.realize_sentence_iff σ).2
      ((isDiscriminatedBy_multiplicative_pi_int (Fin k)).realize_group_of_isUniversal hσ hZ)

/-- **The universal theory of a fully residually free group.** A fully residually free group has
the universal theory of a free group: of the trivial group if it is trivial, of `ℤ` if it is
abelian and nontrivial, and of the free group of rank two if it is not abelian. -/
theorem IsFullyResiduallyFree.exists_forall_realize_iff_freeGroup (h : IsFullyResiduallyFree G) :
    ∃ n : ℕ, ∀ σ : Language.group.Sentence, σ.IsUniversal →
      (G ⊨ σ ↔ FreeGroup (Fin n) ⊨ σ) := by
  by_cases hG : IsMulCommutative G
  · rcases subsingleton_or_nontrivial G with _ | _
    · have := uniqueOfSubsingleton (1 : G)
      exact ⟨0, fun σ _ => (MulEquiv.ofUnique : G ≃* FreeGroup (Fin 0)).realize_sentence_iff σ⟩
    · have := h.isResiduallyFree.isMulTorsionFree
      exact ⟨1, fun σ hσ => (realize_iff_multiplicative_int_of_isMulTorsionFree hσ).trans
        ((FreeGroup.mulEquivIntOfUnique (α := Fin 1)).realize_sentence_iff σ).symm⟩
  · exact ⟨2, fun σ hσ => h.realize_iff_freeGroup_of_not_isMulCommutative hG hσ⟩

/-- A finitely generated group is fully residually free if and only if it has the universal
theory of a free group of finite rank (Champetier and Guirardel, Theorem 1.1). -/
theorem isFullyResiduallyFree_iff_exists_forall_realize_iff [Group.FG G] :
    IsFullyResiduallyFree G ↔ ∃ n : ℕ, ∀ σ : Language.group.Sentence, σ.IsUniversal →
      (G ⊨ σ ↔ FreeGroup (Fin n) ⊨ σ) :=
  ⟨fun h => h.exists_forall_realize_iff_freeGroup, fun ⟨_, hn⟩ =>
    isFullyResiduallyFree_of_forall_isUniversal fun σ hσ => (hn σ hσ).2⟩

/-- A group is a limit group if and only if it is finitely generated and satisfies every universal
sentence of the group language that holds in the free group of rank two. -/
theorem isLimitGroup_iff_forall_isUniversal :
    IsLimitGroup G ↔ Group.FG G ∧
      ∀ σ : Language.group.Sentence, σ.IsUniversal → FreeGroup (Fin 2) ⊨ σ → G ⊨ σ := by
  rw [isLimitGroup_iff_isFullyResiduallyFree]
  exact ⟨fun ⟨_, h⟩ => ⟨‹_›, isFullyResiduallyFree_iff_forall_isUniversal.1 h⟩,
    fun ⟨_, h⟩ => ⟨‹_›, isFullyResiduallyFree_iff_forall_isUniversal.2 h⟩⟩

end TauCeti.LimitGroup
