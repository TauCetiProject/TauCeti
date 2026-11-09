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
a minimal tree on which every nontrivial translation is hyperbolic and the generator has
translation length one. The integers act freely on its darts, and the line is not dominated by
the one-vertex tree, although it dominates it.

## Main declarations

* `TauCeti.GTree.line`: the line as a tree for `Multiplicative ℤ`.
* `TauCeti.GTree.line_translationLength_ofAdd_one`, `TauCeti.GTree.line_isMinimal`,
  `TauCeti.GTree.not_point_dominates_line`.

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
  action_smul_ne_rev k e h := by
    -- Translation keeps the orientation of a dart, while reversal changes it.
    rw [← Aut.smul_dart_def, lineShift_smul_dart] at h
    exact (Bool.eq_not_self _).mp (congrArg Prod.snd (h.trans (line_rev e)))

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

/-- The generator of the integers translates the line by one step. -/
theorem line_translationLength_ofAdd_one :
    line.translationLength (Multiplicative.ofAdd (1 : ℤ)) = 1 := by
  refine le_antisymm ?_ (Nat.one_le_iff_ne_zero.mpr fun h =>
    not_isHyperbolic_iff.mpr (translationLength_eq_zero_iff.mp h) (line_isHyperbolic (by decide)))
  -- The generator carries the source of the dart `(0, true)` to its target.
  have hv : Multiplicative.ofAdd (1 : ℤ) • line.src ((0 : ℤ), true) =
      line.tgt ((0 : ℤ), true) := by
    apply lineVertexEquiv.injective
    simp
  calc line.translationLength (Multiplicative.ofAdd 1)
      ≤ line.dist (line.src ((0 : ℤ), true)) (Multiplicative.ofAdd 1 • line.src ((0 : ℤ), true)) :=
        translationLength_le _ _
    _ = line.dist (line.src ((0 : ℤ), true)) (line.tgt ((0 : ℤ), true)) := by rw [hv]
    _ ≤ 1 := dist_src_tgt_le_one _

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

/-- The line is relative to the trivial edge family and the trivial elliptic family. -/
theorem line_isRelative : line.IsRelative {⊥} {⊥} :=
  isRelative_iff.mpr ⟨fun e => line_stabilizer_dart e, fun _ hH => hH ▸ isEllipticSubgroup_bot line⟩

/-- The one-vertex tree does not dominate the line, although the line dominates it. -/
theorem not_point_dominates_line : ¬(point.{u, v} (Multiplicative ℤ)).Dominates line := by
  rw [point_dominates_iff]
  exact fun h => not_isHyperbolic_iff.mpr (h.isElliptic (Subgroup.mem_top _))
    (line_isHyperbolic (k := Multiplicative.ofAdd 1) (by decide))

end GTree

end TauCeti
