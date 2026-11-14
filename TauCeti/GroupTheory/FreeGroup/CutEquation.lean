/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import TauCeti.GroupTheory.FreeGroup.EqIneqSystem.Basic
public import TauCeti.GroupTheory.FreeGroup.Substitution

/-!
# Cut equations over a free group

A *cut equation* `Π = (E, M, X, f_M, f_X)` over the free group `F = F(A)` (Kharlampovich–Myasnikov,
Definition 21) consists of a set `E` of intervals, a set `M` of variables (the *pieces*), a set
`X` of parameters and two labelling functions `f_X : E → F[X]` and `f_M : E → F[M]`. The label
`f_M(σ)` is a word in the pieces `M^{±1}` and the letters of `A^{±1}`, called a partition of
`f_X(σ)`: the interval `σ` is cut into the pieces listed by `f_M(σ)`.

Given an `F`-homomorphism `β : F[X] → F`, that is, a tuple `β : X → F`, a *solution* of `Π` with
respect to `β` (Definition 22) is a tuple `α` of nonempty reduced words over `A^{±1}`, one for each
piece, such that for every interval `σ` the word obtained from `f_M(σ)` by substituting `α` is
reduced as written and is, letter by letter, the reduced form of `β(f_X(σ))`. If one only asks that
`α(f_M(σ)) = β(f_X(σ))` in the group `F`, so that cancellation may occur in the substituted
words, then `α` is a *group solution* of `Π` with respect to `β`.

Cut equations are the modification of Makanin's generalised equations used in the proof of the
implicit function theorem over free groups: the solutions in `F` of a finite system `S(X, Y) = 1`
are described by finitely many cut equations whose parameter labels are letters of `X^{±1}`.

Here the piece label of an interval is a word, an element of `List ((M ⊕ A) × Bool)`, since being
reduced as written is a property of words; the parameter label is an element of `F(A)[X]`, since
only its values in `F(A)` are used. The sets `E`, `M` and `X` are arbitrary types; the finiteness
of the source is imposed by `Finite` instances where it is needed.

## Main definitions

* `TauCeti.CutEquation A E X M`: cut equations over `F(A)` with intervals `E`, parameters `X` and
  pieces `M`.
* `TauCeti.CutEquation.pieceElement`: the piece label of an interval as an element of `F(A)[M]`.
* `TauCeti.CutEquation.IsGroupSolution`: group solutions with respect to a tuple of parameter
  values.
* `TauCeti.CutEquation.IsSolution`: solutions by nonempty reduced words, reduced as written.
* `TauCeti.CutEquation.oneInterval`: the cut equation with one interval, labelled by a parameter
  `x` and by the product `m₀ ⋯ m_{n-1}` of `n` pieces.

## Main results

* `TauCeti.CutEquation.isSolution_iff_toWord`: a tuple of nonempty reduced words is a solution
  exactly when each substituted piece label is the reduced word of the value of the parameter
  label.
* `TauCeti.CutEquation.IsSolution.isReduced_pieceLabel`: the piece labels of a cut equation with
  a solution are reduced words.
* `TauCeti.CutEquation.isSolution_oneInterval_iff`: the solutions of the one-interval cut equation
  are the factorisations of the reduced word of `β(x)` into `n` nonempty subwords.
* `TauCeti.CutEquation.le_length_toWord_of_isSolution_oneInterval`: such a factorisation needs a
  word of length at least `n`.
* `TauCeti.CutEquation.isSolution_oneInterval_one_iff`: for a single piece `m`, the assignment
  `α(m) = β(x)` is a solution precisely when that word is nonempty.
* `TauCeti.CutEquation.isGroupSolution_oneInterval_cancel`,
  `TauCeti.CutEquation.not_isSolution_oneInterval_two_of_letter`: the pieces `(a, a⁻¹b)` are a
  group solution of `m₀m₁ = x` at `x = b`, which has no solution with respect to that value.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.7, Definitions 21 and 22.
* O. Kharlampovich, A. Myasnikov, *Algebraic geometry over free groups: lifting solutions into
  generic points*, Contemp. Math. 378 (2005), §3, Definitions 3.1 and 3.2.
-/

public section

namespace TauCeti

open Monoid.Coprod GroupAlgGeom
open FreeGroup (IsReduced substituteVars)

/-- A cut equation over the free group `F(A)` (Kharlampovich–Myasnikov, Definition 21): a set `E`
of intervals, a set `X` of parameters, a set `M` of pieces, and for each interval a label in
`F(A)[X]` and a partition of it, a word in the pieces `M^{±1}` and the letters of `A^{±1}`. -/
@[ext]
structure CutEquation (A E X M : Type*) where
  /-- The label `f_X(σ)` of an interval, an element of `F(A)[X]`. -/
  paramLabel : E → GX (FreeGroup A) X
  /-- The label `f_M(σ)` of an interval: the word in the pieces and the letters of `A` into which
  the interval is cut. -/
  pieceLabel : E → List ((M ⊕ A) × Bool)

namespace CutEquation

variable {A E X M : Type*} (P : CutEquation A E X M)

/-! ### Group solutions -/

/-- The piece label `f_M(σ)` of an interval, read as an element of `F(A)[M]`. -/
def pieceElement (σ : E) : GX (FreeGroup A) M :=
  EqIneqSystem.toGX M FreeGroup.of (FreeGroup.mk (P.pieceLabel σ))

theorem pieceElement_def (σ : E) :
    P.pieceElement σ = EqIneqSystem.toGX M FreeGroup.of (FreeGroup.mk (P.pieceLabel σ)) := (rfl)

/-- Evaluating the piece label of an interval at a tuple of values of the pieces evaluates the
word at the pieces and at the letters. -/
@[simp]
theorem eval_pieceElement {H : Type*} [Group H] (ι : FreeGroup A →* H) (α : M → H) (σ : E) :
    eval ι α (P.pieceElement σ) =
      FreeGroup.lift (Sum.elim α (ι ∘ FreeGroup.of)) (FreeGroup.mk (P.pieceLabel σ)) := by
  rw [pieceElement, EqIneqSystem.eval_toGX, EqIneqSystem.eval_eq_lift]

/-- Evaluating the piece label of an interval at a tuple of words is substitution of the words,
followed by free reduction. -/
theorem eval_pieceElement_mk (α : M → List (A × Bool)) (σ : E) :
    eval (MonoidHom.id (FreeGroup A)) (fun m => FreeGroup.mk (α m)) (P.pieceElement σ) =
      FreeGroup.mk (substituteVars α (P.pieceLabel σ)) := by
  rw [eval_pieceElement, FreeGroup.mk_substituteVars, MonoidHom.coe_id, Function.id_comp]

/-- A group solution of a cut equation with respect to the parameter values `β`
(Kharlampovich–Myasnikov, after Definition 22): values `α` of the pieces in `F(A)` such that for
every interval the two labels have the same value in `F(A)`. Cancellation may occur between the
values of the pieces. -/
def IsGroupSolution (β : X → FreeGroup A) (α : M → FreeGroup A) : Prop :=
  ∀ σ, eval (MonoidHom.id (FreeGroup A)) α (P.pieceElement σ) =
    eval (MonoidHom.id (FreeGroup A)) β (P.paramLabel σ)

variable {P} {β : X → FreeGroup A}

theorem isGroupSolution_iff {α : M → FreeGroup A} :
    P.IsGroupSolution β α ↔ ∀ σ, eval (MonoidHom.id (FreeGroup A)) α (P.pieceElement σ) =
      eval (MonoidHom.id (FreeGroup A)) β (P.paramLabel σ) :=
  Iff.rfl

/-- Values of the pieces are a group solution exactly when each piece label, evaluated at them,
is the value of the parameter label. -/
theorem isGroupSolution_iff_lift {α : M → FreeGroup A} :
    P.IsGroupSolution β α ↔ ∀ σ,
      FreeGroup.lift (Sum.elim α FreeGroup.of) (FreeGroup.mk (P.pieceLabel σ)) =
        eval (MonoidHom.id (FreeGroup A)) β (P.paramLabel σ) := by
  simp [isGroupSolution_iff]

/-- A tuple of words is a group solution exactly when each substituted piece label represents
the value of the parameter label. -/
theorem isGroupSolution_mk_iff {α : M → List (A × Bool)} :
    (P.IsGroupSolution β fun m => FreeGroup.mk (α m)) ↔ ∀ σ,
      FreeGroup.mk (substituteVars α (P.pieceLabel σ)) =
        eval (MonoidHom.id (FreeGroup A)) β (P.paramLabel σ) := by
  simp only [isGroupSolution_iff, eval_pieceElement_mk]

/-! ### Solutions -/

variable (P β) in
/-- A solution of a cut equation with respect to the parameter values `β`
(Kharlampovich–Myasnikov, Definition 22): a tuple of nonempty reduced words over `A^{±1}`, one for
each piece, such that after substitution every piece label is reduced as written and represents
the value of the parameter label. Equivalently, every substituted piece label is, letter by
letter, the reduced word of the value of the parameter label
(`TauCeti.CutEquation.isSolution_iff_toWord`). -/
structure IsSolution (α : M → List (A × Bool)) : Prop where
  /-- Each piece is assigned a nonempty word. -/
  ne_nil : ∀ m, α m ≠ []
  /-- Each piece is assigned a reduced word. -/
  isReduced : ∀ m, IsReduced (α m)
  /-- Every substituted piece label is reduced as written. -/
  isReduced_substituteVars : ∀ σ, IsReduced (substituteVars α (P.pieceLabel σ))
  /-- The words assigned to the pieces are a group solution. -/
  isGroupSolution : P.IsGroupSolution β fun m => FreeGroup.mk (α m)

variable {α : M → List (A × Bool)}

/-- A solution is a group solution by nonempty reduced words whose substituted piece labels are
reduced as written. -/
theorem isSolution_iff : P.IsSolution β α ↔ (∀ m, α m ≠ []) ∧ (∀ m, IsReduced (α m)) ∧
    (∀ σ, IsReduced (substituteVars α (P.pieceLabel σ))) ∧
      P.IsGroupSolution β fun m => FreeGroup.mk (α m) :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

namespace IsSolution

/-- The substituted piece label of an interval represents the value of its parameter label. -/
theorem mk_substituteVars (h : P.IsSolution β α) (σ : E) :
    FreeGroup.mk (substituteVars α (P.pieceLabel σ)) =
      eval (MonoidHom.id (FreeGroup A)) β (P.paramLabel σ) :=
  isGroupSolution_mk_iff.1 h.isGroupSolution σ

/-- The substituted piece label of an interval is, letter by letter, the reduced word of the
value of its parameter label. -/
theorem substituteVars_eq_toWord [DecidableEq A] (h : P.IsSolution β α) (σ : E) :
    substituteVars α (P.pieceLabel σ) =
      (eval (MonoidHom.id (FreeGroup A)) β (P.paramLabel σ)).toWord := by
  rw [← h.mk_substituteVars σ, FreeGroup.toWord_mk, (h.isReduced_substituteVars σ).reduce_eq]

/-- The piece labels of a cut equation with a solution are reduced words. -/
theorem isReduced_pieceLabel (h : P.IsSolution β α) (σ : E) : IsReduced (P.pieceLabel σ) :=
  (h.isReduced_substituteVars σ).of_substituteVars h.ne_nil

end IsSolution

/-- A tuple of words is a solution exactly when the words are nonempty and reduced and each
substituted piece label is, letter by letter, the reduced word of the value of the parameter
label. -/
theorem isSolution_iff_toWord [DecidableEq A] :
    P.IsSolution β α ↔ (∀ m, α m ≠ []) ∧ (∀ m, IsReduced (α m)) ∧ ∀ σ,
      substituteVars α (P.pieceLabel σ) =
        (eval (MonoidHom.id (FreeGroup A)) β (P.paramLabel σ)).toWord := by
  refine ⟨fun h => ⟨h.ne_nil, h.isReduced, h.substituteVars_eq_toWord⟩, fun h => ?_⟩
  refine ⟨h.1, h.2.1, fun σ => h.2.2 σ ▸ FreeGroup.isReduced_toWord,
    isGroupSolution_mk_iff.2 fun σ => ?_⟩
  rw [h.2.2 σ, FreeGroup.mk_toWord]

/-! ### The cut equation of one interval -/

variable (A) in
/-- The cut equation with one interval, labelled by a parameter `x` and cut into the `n` pieces
`m₀ ⋯ m_{n-1}`. -/
def oneInterval (n : ℕ) : CutEquation A Unit Unit (Fin n) where
  paramLabel _ := inr (FreeGroup.of ())
  pieceLabel _ := (List.finRange n).map fun i => (Sum.inl i, true)

variable {n : ℕ} {β : Unit → FreeGroup A}

@[simp]
theorem oneInterval_paramLabel (σ : Unit) :
    (oneInterval A n).paramLabel σ = inr (FreeGroup.of ()) := (rfl)

@[simp]
theorem oneInterval_pieceLabel (σ : Unit) :
    (oneInterval A n).pieceLabel σ = (List.finRange n).map fun i => (Sum.inl i, true) := (rfl)

/-- Values of the pieces are a group solution of `m₀ ⋯ m_{n-1} = x` exactly when their product is
the value of `x`. -/
theorem isGroupSolution_oneInterval_iff {α : Fin n → FreeGroup A} :
    (oneInterval A n).IsGroupSolution β α ↔ (List.ofFn α).prod = β () := by
  simp [isGroupSolution_iff_lift, List.ofFn_eq_map, Function.comp_def]

/-- The solutions of `m₀ ⋯ m_{n-1} = x` with respect to a value of `x` are the factorisations of
the reduced word of that value into `n` nonempty subwords. -/
theorem isSolution_oneInterval_iff [DecidableEq A] {α : Fin n → List (A × Bool)} :
    (oneInterval A n).IsSolution β α ↔ (∀ i, α i ≠ []) ∧ (List.ofFn α).flatten = (β ()).toWord := by
  have hsub : substituteVars α ((oneInterval A n).pieceLabel ()) = (List.ofFn α).flatten := by
    rw [oneInterval_pieceLabel, FreeGroup.substituteVars_map_inl, List.flatMap_def,
      List.ofFn_eq_map]
  simp only [isSolution_iff_toWord, forall_const, hsub, oneInterval_paramLabel, eval_inr_of]
  refine ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun i => ?_, h.2⟩⟩
  exact (h.2 ▸ FreeGroup.isReduced_toWord).infix
    (List.infix_of_mem_flatten ((List.mem_ofFn' α _).2 ⟨i, rfl⟩))

/-- A cut equation `m₀ ⋯ m_{n-1} = x` with a solution with respect to a value of `x` cuts a word
of length at least `n`. -/
theorem le_length_toWord_of_isSolution_oneInterval [DecidableEq A] {α : Fin n → List (A × Bool)}
    (h : (oneInterval A n).IsSolution β α) : n ≤ (β ()).toWord.length := by
  obtain ⟨hne, hα⟩ := isSolution_oneInterval_iff.1 h
  rw [← hα, List.length_flatten]
  refine le_trans (by simp) (List.length_le_sum_of_one_le _ fun k hk => ?_)
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hk
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' α w).1 hw
  exact List.length_pos_iff.2 (hne i)

/-- If the reduced word of the value of `x` has fewer than `n` letters, the cut equation
`m₀ ⋯ m_{n-1} = x` has no solution with respect to that value. -/
theorem not_isSolution_oneInterval_of_length_lt [DecidableEq A] {α : Fin n → List (A × Bool)}
    (h : (β ()).toWord.length < n) : ¬ (oneInterval A n).IsSolution β α :=
  fun hα => (le_length_toWord_of_isSolution_oneInterval hα).not_gt h

/-- For the one-interval cut equation labelled `x` and `m`, the assignment `α(m) = β(x)` is a
solution precisely when that word is nonempty. -/
theorem isSolution_oneInterval_one_iff [DecidableEq A] {α : Fin 1 → List (A × Bool)} :
    (oneInterval A 1).IsSolution β α ↔ α 0 = (β ()).toWord ∧ β () ≠ 1 := by
  rw [isSolution_oneInterval_iff, ← (FreeGroup.toWord_eq_nil_iff (x := β ())).ne]
  simp only [Fin.forall_fin_one, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  exact ⟨fun h => ⟨h.2, h.2 ▸ h.1⟩, fun h => ⟨h.1 ▸ h.2, h.1⟩⟩

/-- The pieces `(a, a⁻¹b)` are a group solution of `m₀m₁ = x` at `x = b` in `F(a, b)`, with
`a = 0` and `b = 1`: the product `a · a⁻¹b` is `b` after cancellation. -/
theorem isGroupSolution_oneInterval_cancel :
    (oneInterval (Fin 2) 2).IsGroupSolution (fun _ => FreeGroup.of 1)
      fun i => FreeGroup.mk (![[(0, true)], [(0, false), (1, true)]] i) := by
  rw [isGroupSolution_oneInterval_iff]
  have h : FreeGroup.mk [((0 : Fin 2), true), (0, false), (1, true)] = FreeGroup.mk [(1, true)] :=
    Quot.sound (FreeGroup.Red.Step.not (L₁ := []))
  simpa [FreeGroup.of] using h

/-- The cut equation `m₀m₁ = x` has no solution with respect to a value of `x` that is a letter,
since a one-letter word is not a product of two nonempty words. In particular the pieces
`(a, a⁻¹b)` are not a solution at `x = b`: the word `a a⁻¹ b` is not reduced as written. -/
theorem not_isSolution_oneInterval_two_of_letter (a : A) {α : Fin 2 → List (A × Bool)} :
    ¬ (oneInterval A 2).IsSolution (fun _ => FreeGroup.of a) α := by
  classical exact not_isSolution_oneInterval_of_length_lt (by simp)

end CutEquation

end TauCeti
