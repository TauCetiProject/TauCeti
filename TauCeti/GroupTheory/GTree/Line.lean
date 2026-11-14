/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Line
public import TauCeti.GroupTheory.GTree.Basic

/-!
# The line as a `G`-tree

The integers act on the line by translation without inversions, so the line is a `G`-tree for
the infinite cyclic group, the free group of rank one; it is the Cayley tree of that group. It is
a minimal tree on which the translation by `k` moves every vertex by `|k|`, so that it has
translation length `|k|` and is hyperbolic when `k ≠ 0`. The integers act freely on its darts,
and the line is not dominated by the one-vertex tree, although it dominates it.

## Main declarations

* `TauCeti.GTree.line`: the line as a tree for `Multiplicative ℤ`.
* `TauCeti.GTree.line_dist_smul`, `TauCeti.GTree.line_translationLength`,
  `TauCeti.GTree.line_isMinimal`, `TauCeti.GTree.not_point_dominates_line`.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2 and §6.4.
-/

public section

universe u v

namespace TauCeti

open SerreGraph _root_.MulAction

namespace GTree

/-- The line as a tree for the integers acting by translation. It is the Cayley tree of the
infinite cyclic group, the free group of rank one. -/
@[expose] def line : GTree.{0, 0} (Multiplicative ℤ) where
  toSerreGraph := SerreGraph.line
  isTree := line_isTree
  action := lineShift
  action_smul_ne_rev := lineShift_smul_ne_rev

/-- The source of a dart of the line, as an integer. -/
@[simp] theorem lineVertexEquiv_line_src (e : ℤ × Bool) :
    lineVertexEquiv (GTree.line.src e) = if e.2 then e.1 else e.1 + 1 :=
  SerreGraph.lineVertexEquiv_src e

/-- The target of a dart of the line, as an integer. -/
@[simp] theorem lineVertexEquiv_line_tgt (e : ℤ × Bool) :
    lineVertexEquiv (GTree.line.tgt e) = if e.2 then e.1 + 1 else e.1 :=
  (SerreGraph.lineVertexEquiv_tgt e).trans <| by
    rw [SerreGraph.lineVertexEquiv_src e]
    split_ifs <;> omega

/-- Translation adds to the coordinate of a vertex of the line. -/
@[simp] theorem lineVertexEquiv_line_smul (k : Multiplicative ℤ) (v : line.V) :
    lineVertexEquiv (k • v) = k.toAdd + lineVertexEquiv v :=
  lineVertexEquiv_lineShift_smul k v

/-- Translation moves a dart of the line without changing its orientation. -/
@[simp] theorem line_smul_dart (k : Multiplicative ℤ) (e : line.E) :
    k • e = Prod.mk (k.toAdd + Prod.fst e) (Prod.snd e) :=
  lineShift_smul_dart k e

/-- Every nontrivial translation of the line is hyperbolic. -/
theorem line_isHyperbolic {k : Multiplicative ℤ} (hk : k ≠ 1) : line.IsHyperbolic k := by
  refine isHyperbolic_iff.mpr fun v hv => hk (toAdd_eq_zero.mp ?_)
  have := congrArg lineVertexEquiv hv
  rw [lineVertexEquiv_line_smul] at this
  omega

/-- The translation by `k` moves every vertex of the line by `|k|`. -/
theorem line_dist_smul (k : Multiplicative ℤ) (v : line.V) :
    line.dist v (k • v) = k.toAdd.natAbs :=
  Int.ofNat_inj.mp <| (line_dist _ _).trans <| by
    rw [lineVertexEquiv_line_smul, Int.natCast_natAbs, sub_add_cancel_right, abs_neg]

/-- The translation of the line by `k` has translation length `|k|`. -/
@[simp] theorem line_translationLength (k : Multiplicative ℤ) :
    line.translationLength k = k.toAdd.natAbs := by
  obtain ⟨v, hv⟩ := exists_dist_eq_translationLength (T := line) k
  rw [← hv, line_dist_smul]

/-- The line is a minimal tree. -/
theorem line_isMinimal : line.IsMinimal := by
  refine isMinimal_iff.mpr fun S ⟨v, hv⟩ _ hS => Set.eq_univ_of_forall fun w => ?_
  have hw : Multiplicative.ofAdd (lineVertexEquiv w - lineVertexEquiv v) • v = w := by
    apply lineVertexEquiv.injective
    rw [lineVertexEquiv_line_smul, toAdd_ofAdd, sub_add_cancel]
  exact hw ▸ hS _ v hv

/-- The integers act freely on the darts of the line. -/
theorem line_stabilizer_dart (e : line.E) : stabilizer (Multiplicative ℤ) e = ⊥ := by
  refine eq_bot_iff.mpr fun k hk => Subgroup.mem_bot.mpr (toAdd_eq_zero.mp ?_)
  have h := (line_smul_dart k e).symm.trans (mem_stabilizer_iff.mp hk)
  have h₁ : k.toAdd + Prod.fst e = Prod.fst e := congrArg Prod.fst h
  omega

/-- The integers act freely on the vertices of the line. -/
theorem line_stabilizer_vertex (v : line.V) : stabilizer (Multiplicative ℤ) v = ⊥ :=
  eq_bot_iff.mpr fun _ hk => Subgroup.mem_bot.mpr <| of_not_not fun h =>
    isHyperbolic_iff.mp (line_isHyperbolic h) v (mem_stabilizer_iff.mp hk)

/-- The line is relative to any family of subgroups containing the trivial subgroup and any family
of trivial subgroups. -/
theorem line_isRelative {𝒜 ℋ : Set (Subgroup (Multiplicative ℤ))} (h𝒜 : ⊥ ∈ 𝒜) (hℋ : ℋ ⊆ {⊥}) :
    line.IsRelative 𝒜 ℋ :=
  isRelative_of_forall_stabilizer_eq_bot h𝒜 hℋ line_stabilizer_vertex

/-- The one-vertex tree does not dominate the line, although the line dominates it. -/
theorem not_point_dominates_line : ¬(point.{u, v} (Multiplicative ℤ)).Dominates line := by
  rw [point_dominates_iff]
  exact fun h => not_isHyperbolic_iff.mpr (h.isElliptic (Subgroup.mem_top _))
    (line_isHyperbolic (k := Multiplicative.ofAdd 1) (by decide))

end GTree

end TauCeti
