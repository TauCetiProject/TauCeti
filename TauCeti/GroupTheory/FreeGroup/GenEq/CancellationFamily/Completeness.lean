/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.CancellationFamily.Basic
import TauCeti.GroupTheory.FreeGroup.GenEq.Completeness

/-!
# Every solution of a system of equations and inequations comes from a cancellation scheme

Let `S` be a finite system of equations and inequations over the free group `F(A)`, in the
variables of a finite type `X`. A solution `U` of the generalised equation of a cancellation scheme
`T` of `S` gives the solution `x ↦ P_x(U)` of `S`. This file proves the converse, over any
alphabet `A`: every solution `W` of `S` is `x ↦ P_x(U)`, graphically, for a solution `U` of the
generalised equation of a cancellation scheme `T` over the auxiliary alphabet `Fin n`, where
`n = systemSize S.toWords`. The entries of `T` are words over `Fin n ⊕ A`: they may contain
constants of `A`, and they need not use every auxiliary letter. When `A` is finite, such a `T`
is a member of the finite cancellation family of `S`, so a system whose cancellation family is
empty has no solution.

## Main results

* `TauCeti.EqIneqSystem.exists_isCancellationScheme_of_isSolution`: **Lemma 14(3)**, every
  solution `W` of `S` is `x ↦ P_x(U)`, graphically, for a solution `U` of the generalised
  equation of a cancellation scheme `T` over the auxiliary alphabet `Fin (systemSize S.toWords)`.
* `TauCeti.EqIneqSystem.not_isSolution_of_cancellationFamily_eq_empty`: **Lemma 14(1)**, over a
  finite alphabet `A`, a system whose cancellation family is empty has no solution in `F(A)`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.2, Lemma 14.
* V. Diekert, A. Jez, W. Plandowski, *Finding all solutions of equations in free groups and
  monoids with involution*, Inform. and Comput. 251 (2016), §1.3 (an inequation as an equation
  with a new variable different from `1`).
-/

public section

namespace TauCeti

namespace EqIneqSystem

open GenEq
open FreeGroup (substituteVars)

variable {X A : Type*} [Finite X] [DecidableEq X] [DecidableEq A]

/-- **Kharlampovich–Myasnikov, Lemma 14(3), with inequations.** Every solution `W` of a system of
equations and inequations over `F(A)`, for any alphabet `A`, comes from a cancellation scheme `T`
over the auxiliary alphabet `Fin n`, where `n = systemSize S.toWords`, with entries words over
`Fin n ⊕ A` (a member of the cancellation family when `A` is finite), and a solution `U` of its
generalised equation: `W = P(U)`, graphically, as `P_x(U)` is the reduced word of `W x` for every
variable `x`. -/
theorem exists_isCancellationScheme_of_isSolution {S : EqIneqSystem X A} {W : X → FreeGroup A}
    (hW : S.IsSolution W FreeGroup.of) :
    ∃ T : Occurrence S.toWords → List ((Fin (systemSize S.toWords) ⊕ A) × Bool),
      S.IsCancellationScheme T ∧ ∃ U : (S.genEq T).Solution,
        ∀ x : X, substituteVars U.word (S.wordMap T x) = (W x).toWord := by
  -- Extend `W` by the values `z k ≠ 1` of the inequations and apply Lemma 14(3) to the words.
  obtain ⟨z, hz, h⟩ := (isSolution_iff_exists_forall_mem_toWords S W FreeGroup.of).1 hW
  obtain ⟨T, hT, U, hU⟩ := GenEq.exists_solution_wordMap_eq h
  refine ⟨T, ⟨hT, fun o k ho h₀ => hz k ?_⟩, U, fun x => ?_⟩
  · -- An empty word of a witness would spell the reduced word of `z k`.
    refine FreeGroup.toWord_eq_nil_iff.1 ((hU o (Sum.inr k) ho).symm.trans ?_)
    rw [(hT.wordMap_eq_nil_iff ho).2 h₀, FreeGroup.substituteVars_nil]
  · -- The variable `x` occurs in its word `x x⁻¹`.
    obtain ⟨o, ho⟩ := exists_occurrence_of_mem (S.pair_mem_toWords (Sum.inl x)) (j := 0) (by simp)
    exact hU o (Sum.inl x) (congrArg Prod.fst ho)

/-- **Kharlampovich–Myasnikov, Lemma 14(1), with inequations.** A system of equations and
inequations over `F(A)`, for a finite alphabet `A`, whose cancellation family is empty has no
solution in `F(A)`. -/
theorem not_isSolution_of_cancellationFamily_eq_empty [Finite A] {S : EqIneqSystem X A}
    (h : S.cancellationFamily = ∅) (W : X → FreeGroup A) : ¬ S.IsSolution W FreeGroup.of :=
  fun hW => have ⟨T, hT, _⟩ := exists_isCancellationScheme_of_isSolution hW
    Finset.eq_empty_iff_forall_notMem.1 h T (mem_cancellationFamily.2 hT)

/-! ### Examples -/

section Examples

/-- The solution `x = a` of the inequation `x ≠ 1` comes from a member of its cancellation family:
a solution `U` of its generalised equation with `P_x(U) = a`. -/
example [Finite A] (x : X) (a : A) :
    ∃ T ∈ (⟨[], [FreeGroup.of (Sum.inl x)]⟩ : EqIneqSystem X A).cancellationFamily,
      ∃ U : (genEq _ T).Solution, substituteVars U.word (wordMap _ T x) = [(a, true)] := by
  obtain ⟨T, hT, U, hU⟩ := exists_isCancellationScheme_of_isSolution
    (S := ⟨[], [FreeGroup.of (Sum.inl x)]⟩) (W := fun _ => FreeGroup.of a)
    (by simp [isSolution_iff])
  exact ⟨T, mem_cancellationFamily.2 hT, U, (hU x).trans (FreeGroup.toWord_of a)⟩

/-- The inequation `1 ≠ 1` has an empty cancellation family: in a partition table the witness has
the empty word in its word `z⁻¹`, while a scheme makes it nonempty. -/
private theorem cancellationFamily_ineq_one [Finite A] :
    (⟨[], [1]⟩ : EqIneqSystem X A).cancellationFamily = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun T hT => ?_
  obtain ⟨hT, hne⟩ := mem_cancellationFamily.1 hT
  -- The word `z⁻¹` of the witness.
  obtain ⟨o, ho, h⟩ := hT.exists_occurrence_eq_nil_of_singleton_mem
    (y := (Sum.inl (Sum.inr ⟨0, Nat.zero_lt_one⟩), false))
    (mem_toWords.2 (.inr (.inl ⟨⟨0, Nat.zero_lt_one⟩, .inl (by simp)⟩)))
  exact hne o ⟨0, Nat.zero_lt_one⟩ (congrArg Prod.fst ho) h

/-- The inequation `1 ≠ 1` has no solution, by Lemma 14(1). -/
example [Finite A] (W : X → FreeGroup A) :
    ¬ (⟨[], [1]⟩ : EqIneqSystem X A).IsSolution W FreeGroup.of :=
  not_isSolution_of_cancellationFamily_eq_empty cancellationFamily_ineq_one W

end Examples

end EqIneqSystem

end TauCeti
