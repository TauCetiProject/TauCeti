/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.Fin.VecNotation
public import TauCeti.GroupTheory.FreeGroup.GenEq.Basic

/-!
# Solutions of a generalised equation from group solutions

A solution of a generalised equation `Ω` (Kharlampovich–Myasnikov, Definition 9) is a tuple of
nonempty reduced words such that every side of every equation is reduced as written and the two
sides of every equation agree letter by letter. Two reduced words that represent the same element
of `F(A)` are equal, so the last condition may be replaced by: the tuple is a point of `Ω*` in
`F(A)` (Remark 4). This is the form in which the elementary transformations of Makanin's process
produce solutions: they change the equations in a way that is easy to follow in the group, and
only the sides that must be reduced as written have to be compared.

## Main definitions

* `TauCeti.GenEq.Solution.ofMemV`: the solution given by a tuple of nonempty reduced words which
  is a point of `Ω*` and makes every side reduced as written.

## Main results

* `TauCeti.GenEq.substituteVars_eq_of_mem_V`: for a point of `Ω*`, the two sides of an equation
  are equal as words as soon as both are reduced as written.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.1, Definition 9 and Remark 4.
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom
open FreeGroup (substituteVars substituteVars_singleton_inl mk_substituteVars)

variable {A : Type*} {Ω : GenEq A}

/-- If a tuple of words is a point of `Ω*` in `F(A)` and both sides of an equation of `Ω` are
reduced as written after substitution, the two sides are equal as words. -/
theorem substituteVars_eq_of_mem_V {w : Fin Ω.numItems → List (A × Bool)}
    (hV : (fun k => FreeGroup.mk (w k)) ∈ V (MonoidHom.id (FreeGroup A)) Ω.toSystem)
    {e : List ((Fin Ω.numItems ⊕ A) × Bool) × List ((Fin Ω.numItems ⊕ A) × Bool)}
    (he : e ∈ Ω.equations) (h₁ : FreeGroup.IsReduced (substituteVars w e.1))
    (h₂ : FreeGroup.IsReduced (substituteVars w e.2)) :
    substituteVars w e.1 = substituteVars w e.2 := by
  refine h₁.eq_of_mk_eq h₂ ?_
  simpa [mk_substituteVars] using Ω.mem_V_toSystem_iff.1 hV e he

namespace Solution

/-- The solution given by a tuple of nonempty reduced words which is a point of `Ω*` in `F(A)` and
makes both sides of every equation reduced as written. -/
def ofMemV (w : Fin Ω.numItems → List (A × Bool)) (hw : ∀ k, FreeGroup.IsReduced (w k))
    (hw' : ∀ k, w k ≠ [])
    (hred : ∀ e ∈ Ω.equations, FreeGroup.IsReduced (substituteVars w e.1) ∧
      FreeGroup.IsReduced (substituteVars w e.2))
    (hV : (fun k => FreeGroup.mk (w k)) ∈ V (MonoidHom.id (FreeGroup A)) Ω.toSystem) :
    Ω.Solution where
  word := w
  isReduced_word := hw
  word_ne_nil := hw'
  isReduced_subst := hred
  subst_eq e he := substituteVars_eq_of_mem_V hV he (hred e he).1 (hred e he).2

/-- The words of the solution built from a point of `Ω*` are the given words. -/
@[simp]
theorem ofMemV_word (w : Fin Ω.numItems → List (A × Bool)) (hw : ∀ k, FreeGroup.IsReduced (w k))
    (hw' : ∀ k, w k ≠ [])
    (hred : ∀ e ∈ Ω.equations, FreeGroup.IsReduced (substituteVars w e.1) ∧
      FreeGroup.IsReduced (substituteVars w e.2))
    (hV : (fun k => FreeGroup.mk (w k)) ∈ V (MonoidHom.id (FreeGroup A)) Ω.toSystem) :
    (ofMemV w hw hw' hred hV).word = w :=
  (rfl)

end Solution

/-! ### Example -/

/-- The generalised equation with the single basic equation `h₁ = h₂`. -/
private abbrev equalExample : GenEq A where
  numItems := 2
  numBases := 2
  left := ![0, 1]
  right := ![1, 2]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)

/-- Every nonempty reduced word `u` gives the solution `h₁ = h₂ = u` of the generalised equation
`h₁ = h₂`: the tuple `(u, u)` is a point of `Ω*`, and both sides of the equation are the reduced
word `u`. -/
example {u : List (A × Bool)} (hu : FreeGroup.IsReduced u) (hu' : u ≠ []) :
    ∃ U : (equalExample (A := A)).Solution, ∀ k, U.word k = u := by
  have h₀ : (equalExample (A := A)).segment 0 1 true = [(Sum.inl 0, true)] :=
    equalExample.segment_succ 0
  have h₁ : (equalExample (A := A)).segment 1 2 true = [(Sum.inl 1, true)] :=
    equalExample.segment_succ 1
  have hsub : ∀ e ∈ (equalExample (A := A)).equations,
      substituteVars (fun _ => u) e.1 = u ∧ substituteVars (fun _ => u) e.2 = u := by
    refine (forall_mem_equations _).2 ⟨?_, by simp, by simp⟩
    rw [Fin.forall_fin_two]
    simp [h₀, h₁, substituteVars_singleton_inl]
  refine ⟨Solution.ofMemV (fun _ => u) (fun _ => hu) (fun _ => hu')
    (fun e he => by rw [(hsub e he).1, (hsub e he).2]; exact ⟨hu, hu⟩) ?_,
    fun k => congrFun (Solution.ofMemV_word ..) k⟩
  refine (mem_V_toSystem_iff _).2 fun e he => ?_
  rw [MonoidHom.coe_id, Function.id_comp, ← mk_substituteVars, ← mk_substituteVars,
    (hsub e he).1, (hsub e he).2]

end GenEq

end TauCeti
