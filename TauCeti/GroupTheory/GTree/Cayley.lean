/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cayley
public import TauCeti.GroupTheory.FreeGroup.Conjugacy.Basic
public import TauCeti.GroupTheory.GTree.JSJ

/-!
# The Cayley tree of a free group

A free group acts by left multiplication on its Cayley graph with respect to a basis, which is a
tree, and the action has no inversions because it preserves the letter of every dart. This is the
Cayley tree of the free group, `GTree.cayley`.

The action is free: the stabilizers of vertices and of darts are trivial, so every nontrivial
element is hyperbolic. The translation length of an element is the length of its cyclic
reduction, the least length of a conjugate (`GTree.cayley_translationLength`); for basis elements
`a` and `b`, the element `a b` has translation length `2` and `a b a⁻¹` has translation length
`1`. The Cayley tree is minimal, since the action is transitive on vertices.

Since the action is free and minimal, the Cayley tree is a JSJ tree of the free group over every
family of subgroups containing the trivial subgroup, relative to a family of trivial subgroups
(`GTree.cayley_isJSJ`). Over such families the JSJ trees of a free group, among the trees whose
vertices and darts lie in the universe of the basis, are exactly its minimal free actions
(`GTree.isJSJ_iff_forall_stabilizer_eq_bot_freeGroup`).

## Main declarations

* `TauCeti.GTree.cayley`: the Cayley tree of `FreeGroup α`, a tree for `FreeGroup α`.
* `TauCeti.GTree.cayley_stabilizer_vertex`, `TauCeti.GTree.cayley_stabilizer_dart`: the action is
  free.
* `TauCeti.GTree.cayley_isHyperbolic_iff`: the hyperbolic elements are the nontrivial ones.
* `TauCeti.GTree.cayley_translationLength`: the translation length is the length of the cyclic
  reduction.
* `TauCeti.GTree.cayley_isJSJ`: the Cayley tree is a JSJ tree of the free group, over a family
  containing the trivial subgroup and relative to trivial subgroups.
* `TauCeti.GTree.isJSJ_iff_forall_stabilizer_eq_bot_freeGroup`: over the same families, the JSJ
  trees of a free group are its minimal free actions.

## References

* J.-P. Serre, *Trees*, Chapter I, §3.2 and §6.4.
* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.1 and
  §3.1.
-/

public section

universe u

namespace TauCeti

open SerreGraph _root_.MulAction

namespace GTree

variable {α : Type u}

/-- The Cayley tree of a free group: its Cayley graph with respect to the basis, with the action
by left multiplication. -/
@[expose] def cayley (α : Type u) : GTree.{u, u} (FreeGroup α) where
  toSerreGraph := SerreGraph.cayley α
  isTree := cayley_isTree
  action := cayleyMulLeft
  action_smul_ne_rev g e h := by
    -- Left multiplication keeps the letter of a dart, while reversal inverts it.
    rw [← Aut.smul_dart_def] at h
    simpa [Prod.ext_iff] using congrArg cayleyDartEquiv h

/-- Left multiplication acts on the vertices of the Cayley tree. -/
@[simp] theorem cayleyVertexEquiv_cayley_smul (g : FreeGroup α) (v : (cayley α).V) :
    cayleyVertexEquiv (g • v) = g * cayleyVertexEquiv v :=
  cayleyVertexEquiv_cayleyMulLeft_smul g v

/-- Left multiplication moves the source of a dart of the Cayley tree and keeps its letter. -/
@[simp] theorem cayleyDartEquiv_cayley_smul (g : FreeGroup α) (e : (cayley α).E) :
    cayleyDartEquiv (g • e) = (g * (cayleyDartEquiv e).1, (cayleyDartEquiv e).2) :=
  cayleyDartEquiv_cayleyMulLeft_smul g e

/-! ### The action is free -/

/-- A free group acts freely on the vertices of its Cayley tree. -/
theorem cayley_stabilizer_vertex (v : (cayley α).V) : stabilizer (FreeGroup α) v = ⊥ := by
  refine eq_bot_iff.mpr fun g hg => Subgroup.mem_bot.mpr ?_
  have h : g • v = v := mem_stabilizer_iff.mp hg
  simpa using congrArg cayleyVertexEquiv h

/-- A free group acts freely on the darts of its Cayley tree. -/
theorem cayley_stabilizer_dart (e : (cayley α).E) : stabilizer (FreeGroup α) e = ⊥ := by
  refine eq_bot_iff.mpr fun g hg => Subgroup.mem_bot.mpr ?_
  have h : g • e = e := mem_stabilizer_iff.mp hg
  simpa using congrArg (fun x => (cayleyDartEquiv x).1) h

/-- Only the identity is elliptic in the Cayley tree. -/
@[simp] theorem cayley_isElliptic_iff {g : FreeGroup α} : (cayley α).IsElliptic g ↔ g = 1 :=
  ⟨fun h => by
    obtain ⟨v, hv⟩ := isElliptic_iff.mp h
    exact Subgroup.mem_bot.mp (cayley_stabilizer_vertex v ▸ mem_stabilizer_iff.mpr hv),
    fun h => h ▸ isElliptic_one _⟩

/-- Every nontrivial element of a free group is hyperbolic in the Cayley tree. -/
@[simp] theorem cayley_isHyperbolic_iff {g : FreeGroup α} : (cayley α).IsHyperbolic g ↔ g ≠ 1 :=
  (not_iff_comm.mp (not_isHyperbolic_iff.trans cayley_isElliptic_iff)).symm

/-- The Cayley tree is relative to any family of subgroups containing the trivial subgroup and any
family of trivial subgroups. -/
theorem cayley_isRelative {𝒜 ℋ : Set (Subgroup (FreeGroup α))} (h𝒜 : ⊥ ∈ 𝒜) (hℋ : ℋ ⊆ {⊥}) :
    (cayley α).IsRelative 𝒜 ℋ :=
  isRelative_of_forall_stabilizer_eq_bot h𝒜 hℋ cayley_stabilizer_vertex

/-- The Cayley tree of a free group is a minimal tree. -/
theorem cayley_isMinimal : (cayley α).IsMinimal := by
  refine isMinimal_iff.mpr fun S ⟨v, hv⟩ _ hS => Set.eq_univ_of_forall fun w => ?_
  have hw : (cayleyVertexEquiv w * (cayleyVertexEquiv v)⁻¹) • v = w :=
    cayleyVertexEquiv.injective (by simp)
  exact hw ▸ hS _ v hv

/-! ### Translation lengths -/

/-- The translation length of an element of a free group on the Cayley tree is the length of its
cyclic reduction. -/
theorem cayley_translationLength [DecidableEq α] (g : FreeGroup α) :
    (cayley α).translationLength g = (FreeGroup.reduceCyclically g.toWord).length := by
  -- The vertex `v` is moved by the length of the conjugate `v⁻¹ * g * v`.
  have key (v : (cayley α).V) : (cayley α).dist v (g • v) =
      ((cayleyVertexEquiv v)⁻¹ * g * cayleyVertexEquiv v).norm :=
    (SerreGraph.cayley_dist v (g • v)).trans (by rw [cayleyVertexEquiv_cayley_smul, mul_assoc])
  refine le_antisymm ?_ ?_
  · obtain ⟨v, hv⟩ : ∃ v : (cayley α).V, cayleyVertexEquiv v =
        FreeGroup.mk (FreeGroup.reduceCyclically.conjugator g.toWord) :=
      ⟨cayleyVertexEquiv.symm _, Equiv.apply_symm_apply _ _⟩
    refine (translationLength_le g v).trans_eq ?_
    rw [key, hv, FreeGroup.norm_inv_mk_conjugator_mul_mul]
  · obtain ⟨v, hv⟩ := exists_dist_eq_translationLength (T := cayley α) g
    rw [← hv, key]
    exact FreeGroup.length_reduceCyclically_toWord_le_norm_of_isConj
      (isConj_iff.mpr ⟨(cayleyVertexEquiv v)⁻¹, by rw [inv_inv]⟩)

/-- A basis element translates the Cayley tree by one step. -/
theorem cayley_translationLength_of (a : α) :
    (cayley α).translationLength (FreeGroup.of a) = 1 := by
  classical
  rw [cayley_translationLength, FreeGroup.toWord_of, FreeGroup.reduceCyclically.singleton,
    List.length_singleton]

/-- The product of two basis elements translates the Cayley tree by two steps. -/
theorem cayley_translationLength_of_mul_of (a b : α) :
    (cayley α).translationLength (FreeGroup.of a * FreeGroup.of b) = 2 := by
  classical
  have h : (FreeGroup.of a * FreeGroup.of b).toWord = (a, true) :: ([] ++ [(b, true)]) :=
    (FreeGroup.toWord_mk (L₁ := [(a, true), (b, true)])).trans
      (FreeGroup.IsReduced.reduce_eq (by simp [FreeGroup.IsReduced]))
  rw [cayley_translationLength, h, FreeGroup.reduceCyclically.cons_append]
  simp

/-- The conjugate `a b a⁻¹` of a basis element translates the Cayley tree by one step. -/
theorem cayley_translationLength_of_mul_of_mul_inv_of (a b : α) :
    (cayley α).translationLength (FreeGroup.of a * FreeGroup.of b * (FreeGroup.of a)⁻¹) = 1 := by
  rw [translationLength_conj, cayley_translationLength_of]

/-! ### The Cayley tree is a JSJ tree -/

/-- The Cayley tree of a free group is a JSJ tree, over any family of subgroups containing the
trivial subgroup and relative to at most the trivial subgroup. -/
theorem cayley_isJSJ {𝒜 ℋ : Set (Subgroup (FreeGroup α))} (h𝒜 : ⊥ ∈ 𝒜) (hℋ : ℋ ⊆ {⊥}) :
    (cayley α).IsJSJ 𝒜 ℋ :=
  .of_forall_stabilizer_eq_bot cayley_isMinimal (cayley_isRelative h𝒜 hℋ) cayley_stabilizer_vertex

/-- Over a family of subgroups containing the trivial subgroup, relative to at most the trivial
subgroup, a tree of a free group (with vertices and darts in the universe of the basis) is a JSJ
tree exactly when it is minimal and its vertex stabilizers are trivial: the JSJ deformation space
of a free group is the space of its minimal free actions. -/
theorem isJSJ_iff_forall_stabilizer_eq_bot_freeGroup {T : GTree.{u, u} (FreeGroup α)}
    {𝒜 ℋ : Set (Subgroup (FreeGroup α))} (h𝒜 : ⊥ ∈ 𝒜) (hℋ : ℋ ⊆ {⊥}) :
    T.IsJSJ 𝒜 ℋ ↔ T.IsMinimal ∧ ∀ x : T.V, stabilizer (FreeGroup α) x = ⊥ :=
  (cayley_isJSJ h𝒜 hℋ).isJSJ_iff_forall_stabilizer_eq_bot cayley_stabilizer_vertex

end GTree

end TauCeti
