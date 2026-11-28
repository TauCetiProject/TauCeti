/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.RibbonGraph.Basic
import TauCeti.Data.Fintype.Fiber

/-!
# Face lengths of bipartite ribbon graphs

The face of an edge is its orbit under the face permutation. Face length counts edge
occurrences in that orbit, so repeated visits to a vertex are counted separately. The lengths
are positive, agree with the periods of the face permutation, and sum to the number of edges.
These counts provide the face-degree terms in Euler-characteristic arguments.
-/

public section

namespace TauCeti.BipartiteRibbonGraph

open Equiv Equiv.Perm Function
open scoped BigOperators

variable (Γ : BipartiteRibbonGraph.{u})

/-- The face containing an edge occurrence. -/
def faceOfEdge (e : Γ.E) : Γ.Face := Quotient.mk'' e

/-- Every face contains an edge occurrence. -/
theorem faceOfEdge_surjective : Surjective Γ.faceOfEdge := Quotient.mk''_surjective

/-- Two edges belong to the same face exactly when they lie in the same face-permutation cycle. -/
theorem faceOfEdge_eq_iff (e e' : Γ.E) :
    Γ.faceOfEdge e = Γ.faceOfEdge e' ↔ Γ.facePerm.SameCycle e e' := Quotient.eq''

/-- A step of the face permutation remains in the same face. -/
@[simp] theorem faceOfEdge_facePerm (e : Γ.E) :
    Γ.faceOfEdge (Γ.facePerm e) = Γ.faceOfEdge e :=
  (Γ.faceOfEdge_eq_iff _ _).mpr (sameCycle_apply_left.mpr (SameCycle.refl _ _))

/-- The number of edge occurrences along a face boundary. -/
noncomputable def faceLength (f : Γ.Face) : ℕ := occCount Γ.faceOfEdge f

/-- Face length is the cardinality of the fibre of its edge projection. -/
theorem faceLength_def (f : Γ.Face) :
    Γ.faceLength f = Nat.card {e : Γ.E // Γ.faceOfEdge e = f} := occCount_def _ _

/-- The face through an edge has length equal to the period of its face permutation. -/
@[simp] theorem faceLength_faceOfEdge (e : Γ.E) :
    Γ.faceLength (Γ.faceOfEdge e) = minimalPeriod Γ.facePerm e := by
  rw [faceLength_def, ← Γ.facePerm.ncard_setOf_sameCycle, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
    (Γ.faceOfEdge_eq_iff _ _).trans sameCycle_comm)

/-- Every face has positive length. -/
@[simp] theorem faceLength_pos (f : Γ.Face) : 0 < Γ.faceLength f :=
  (occCount_pos Γ.faceOfEdge f).mpr (Γ.faceOfEdge_surjective f)

/-- The face boundaries partition the edge occurrences. -/
theorem sum_faceLength : ∑ f : Γ.Face, Γ.faceLength f = Fintype.card Γ.E := by
  classical
  simpa only [faceLength, Nat.card_eq_fintype_card] using
    sum_occCount_eq_card Γ.faceOfEdge (fun _ => Finset.mem_univ _)

end TauCeti.BipartiteRibbonGraph
