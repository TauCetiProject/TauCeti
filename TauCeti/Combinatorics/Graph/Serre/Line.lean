/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.OfParent
public import TauCeti.Combinatorics.Graph.Serre.Quotient
public import Mathlib.Algebra.Group.Action.TypeTags
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# The line

The line is the Serre graph with the integers as vertices and one geometric edge between `n` and
`n + 1`: the graph `SerreGraph.ofParent` of the parent map `n ↦ n + 1`. It is the Cayley graph of
the infinite cyclic group, that is of the free group of rank one, and it is a tree: no integer is
a proper iterate of itself under `n ↦ n + 1`, and any two integers have a common iterate. The
distance between two vertices is the absolute value of the difference of their coordinates.

The coordinate `SerreGraph.lineVertexEquiv` identifies the vertices with the integers, and the
integers act on the line by translation, `SerreGraph.lineShift`, with `k • n = k + n`. This
action has no inversions, and its quotient graph is a loop: it has a single vertex, and its two
darts, identified with `Bool` through their orientation by `SerreGraph.lineQuotientDartEquiv`, are
exchanged by reversal.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2, §3.1 and §6.4.
-/

public section

namespace TauCeti
namespace SerreGraph

/-- The line, the graph of the parent map `n ↦ n + 1` on the integers: the dart `(n, true)` runs
from `n` to `n + 1`, and its reverse `(n, false)` runs back. -/
@[expose] def line : SerreGraph.{0, 0} :=
  ofParent fun n : ℤ => n + 1

theorem line_src (e : ℤ × Bool) : line.src e = if e.2 then e.1 else e.1 + 1 := (rfl)

@[simp] theorem line_rev (e : ℤ × Bool) : line.rev e = (e.1, !e.2) := (rfl)

theorem line_tgt (e : ℤ × Bool) : line.tgt e = if e.2 then e.1 + 1 else e.1 := by
  obtain ⟨n, d⟩ := e
  cases d <;> rfl

/-- The vertices of the line are the integers. -/
def lineVertexEquiv : line.V ≃ ℤ :=
  Equiv.refl ℤ

@[simp] theorem lineVertexEquiv_src (e : ℤ × Bool) :
    lineVertexEquiv (line.src e) = if e.2 then e.1 else e.1 + 1 := (rfl)

/-- A dart of the line moves one step up or down according to its orientation. -/
@[simp] theorem lineVertexEquiv_tgt (e : ℤ × Bool) :
    lineVertexEquiv (line.tgt e) = lineVertexEquiv (line.src e) + if e.2 then 1 else -1 := by
  obtain ⟨n, d⟩ := e
  rw [lineVertexEquiv_src]
  -- The target of `(n, d)` is the integer `n + 1` or `n`, by the definition of the line.
  cases d
  · exact (add_neg_cancel_right n 1).symm
  · rfl

/-- The line is acyclic. -/
theorem line_isAcyclic : line.IsAcyclic :=
  ofParent_isAcyclic _ fun v m n h => by
    simp at h
    omega

/-- The line is connected. -/
theorem line_connected : line.Connected :=
  (connected_iff line).mpr ⟨⟨lineVertexEquiv.symm 0⟩, (ofParent_preconnected_iff _).mpr
    fun a b => ⟨(b - a).toNat, (a - b).toNat, by simp; omega⟩⟩

/-- The line is a tree. -/
theorem line_isTree : line.IsTree :=
  (isTree_iff line).mpr ⟨line_connected, line_isAcyclic⟩

/-- The distance between two vertices of the line is the absolute value of the difference of
their coordinates. -/
theorem line_dist (a b : line.V) :
    (line.dist a b : ℤ) = |lineVertexEquiv a - lineVertexEquiv b| := by
  obtain ⟨p, hp⟩ := line_isTree.existsUnique_isReduced a b |>.exists
  obtain ⟨k, l, hkl, heq, hne⟩ := exists_iterate_eq_of_isReduced _ p hp
  have hlen : p.length = k + l := hkl.symm
  -- The coordinate `lineVertexEquiv` is the identity of `ℤ`, the type of vertices of the line.
  have ha : lineVertexEquiv a = a := rfl
  have hb : lineVertexEquiv b = b := rfl
  simp at heq hne
  rw [line_isAcyclic.dist_eq_length hp, hlen, abs_eq_max_neg]
  omega

/-- The translation action of the integers on the line, `k • n = k + n`. -/
def lineShift : Multiplicative ℤ →* line.Aut :=
  ofParentAction _ fun k n => by
    rw [← toAdd_vadd, ← toAdd_vadd, vadd_eq_add, vadd_eq_add, add_assoc]

/-- Translation adds to the coordinate of a vertex. -/
@[simp] theorem lineVertexEquiv_lineShift_smul (k : Multiplicative ℤ) (v : line.V) :
    lineVertexEquiv (lineShift k • v) = k.toAdd + lineVertexEquiv v := by
  rw [← vadd_eq_add, toAdd_vadd]
  -- The graph `line` is `ofParent (· + 1)`, so `lineShift k` is the automorphism
  -- `ofParentAction _ _ k`, and the coordinate `lineVertexEquiv` is the identity of `ℤ`.
  exact ofParentAction_smul_vertex _ k v

/-- Translation moves a dart without changing its orientation. -/
@[simp] theorem lineShift_smul_dart (k : Multiplicative ℤ) (e : line.E) :
    lineShift k • e = Prod.mk (k.toAdd + Prod.fst e) (Prod.snd e) := by
  rw [← vadd_eq_add, toAdd_vadd]
  -- The graph `line` is `ofParent (· + 1)`, so `lineShift k` is the automorphism
  -- `ofParentAction _ _ k`.
  exact ofParentAction_smul_dart _ k e

/-- Translation keeps the orientation of a dart, while reversal changes it: the integers act on
the line without inversions. -/
theorem lineShift_smul_ne_rev (k : Multiplicative ℤ) (e : line.E) :
    lineShift k • e ≠ line.rev e :=
  ofParentAction_equivE_ne_rev _ k e

/-! ### The quotient of the line by its translations -/

/-- The quotient of the line by its translations has a single vertex. -/
instance : Unique (line.quotient lineShift lineShift_smul_ne_rev).V where
  default := (line.quotientMap lineShift lineShift_smul_ne_rev).mapV (lineVertexEquiv.symm 0)
  uniq a := by
    obtain ⟨a, rfl⟩ := quotientMap_mapV_surjective _ _ _ a
    refine quotientMap_mapV_eq_iff.mpr
      ⟨Multiplicative.ofAdd (-lineVertexEquiv a), lineVertexEquiv.injective ?_⟩
    rw [lineVertexEquiv_lineShift_smul, toAdd_ofAdd, neg_add_cancel, Equiv.apply_symm_apply]

/-- The darts of the quotient of the line by its translations are identified with `Bool` through
their orientation. -/
def lineQuotientDartEquiv : (line.quotient lineShift lineShift_smul_ne_rev).E ≃ Bool where
  toFun := quotientLiftE lineShift_smul_ne_rev (fun e : line.E => e.2) fun k e => by
    rw [lineShift_smul_dart]
  invFun d := (line.quotientMap lineShift lineShift_smul_ne_rev).mapE (0, d)
  left_inv y := by
    obtain ⟨e, rfl⟩ := quotientMap_mapE_surjective _ _ _ y
    rw [quotientLiftE_quotientMap (fun e : line.E => e.2)]
    exact quotientMap_mapE_eq_iff.mpr ⟨Multiplicative.ofAdd e.1,
      (lineShift_smul_dart _ _).trans (Prod.ext (by simp) rfl)⟩
  right_inv d := quotientLiftE_quotientMap (fun e : line.E => e.2) _ (0, d)

/-- The orbit of a dart of the line under translation is its orientation. -/
@[simp] theorem lineQuotientDartEquiv_quotientMap (e : line.E) :
    lineQuotientDartEquiv ((line.quotientMap lineShift lineShift_smul_ne_rev).mapE e) =
      Prod.snd e :=
  quotientLiftE_quotientMap (fun e : line.E => e.2) _ e

@[simp] theorem lineQuotientDartEquiv_symm_apply (d : Bool) :
    lineQuotientDartEquiv.symm d =
      (line.quotientMap lineShift lineShift_smul_ne_rev).mapE (0, d) := (rfl)

/-- Reversal exchanges the two darts of the quotient of the line by its translations. -/
@[simp] theorem lineQuotientDartEquiv_rev (y : (line.quotient lineShift lineShift_smul_ne_rev).E) :
    lineQuotientDartEquiv ((line.quotient lineShift lineShift_smul_ne_rev).rev y) =
      !lineQuotientDartEquiv y := by
  obtain ⟨e, rfl⟩ := quotientMap_mapE_surjective _ _ _ y
  rw [← Hom.map_rev, lineQuotientDartEquiv_quotientMap, lineQuotientDartEquiv_quotientMap]
  exact congrArg Prod.snd (line_rev e)

end SerreGraph
end TauCeti
