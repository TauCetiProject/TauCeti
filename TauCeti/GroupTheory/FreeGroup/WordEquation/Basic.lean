/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.StarVal
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# Word equations with constraints over a free monoid with involution

An *equation with constraints* over the free monoid with involution on an alphabet `β` consists
of two words in variables `X`, letters of `β` and their formal inverses, a valuation of the
letters in `N`, and a prescribed value in `N` for every variable (`TauCeti.InvWordEq`). Letters
and variables are signed, so no letter and no variable is its own inverse. A solution assigns to
every variable a signed word over `β` such that the two sides become the same word (not merely
the same element of the free group) and every variable takes its prescribed value, the value of a
word being computed in a monoid `N` with a `star` operation (`TauCeti.InvWordEq.IsSolution`). The
formal inverse of a variable is replaced by the formal inverse of its word, so a solution respects
the involution by construction. With values in a finite monoid with involution, the prescribed
values record regular constraints on the words of the variables.

Two operations on the sides of an equation transport solutions backwards:

* `TauCeti.InvWordEq.mapLetters` replaces letters by words. If an equation is the image of
  another one under a substitution of words for letters that respects the values, then the
  substitution maps solutions of the second to solutions of the first
  (`TauCeti.InvWordEq.IsSolution.flatMap_substituteLetter`), multiplying their lengths by at
  most a bound on the lengths of the substituted words
  (`TauCeti.InvWordEq.HasSolutionLE.of_mapLetters`);
* `TauCeti.InvWordEq.substVars` replaces variables by words in variables and letters. If an
  equation is obtained from another one in this way and the values agree, then composition maps
  its solutions to solutions of the original equation
  (`TauCeti.InvWordEq.IsSolution.substituteVars`).

These are the two parts of the inverse operators by which solutions are transported back along
the steps of recompression in [DJP16, §2.2, §3], for the steps that create no letter equal to its
own inverse.

## Main definitions

* `TauCeti.InvWordEq`: word equations with constraints over the free monoid with involution.
* `TauCeti.InvWordEq.IsSolution`, `TauCeti.InvWordEq.HasSolutionLE`: solutions, and solutions
  by words of bounded length.
* `TauCeti.InvWordEq.mapLetters`, `TauCeti.InvWordEq.substVars`: replacing the letters, and the
  variables, of an equation side by words.

## Main results

* `TauCeti.InvWordEq.IsSolution.flatMap_substituteLetter`,
  `TauCeti.InvWordEq.HasSolutionLE.of_mapLetters`: transport of solutions, and of length bounds,
  back along a replacement of letters.
* `TauCeti.InvWordEq.IsSolution.substituteVars`: transport of solutions back along a replacement
  of variables.

## References

* [DJP16] V. Diekert, A. Jez, W. Plandowski, *Finding all solutions of equations in free groups
  and monoids with involution*, Inform. and Comput. 251 (2016), 263–286; arXiv:1405.5133,
  §1.1 (Definition 1, Example 1), §2.2, §3.1 (Definition 3), proofs of Lemmas 6 and 7.
-/

public section

namespace TauCeti

open FreeGroup

/-- A word equation with constraints over the free monoid with involution on `β`: two words in
variables `X` and letters of `β`, a valuation of the letters in `N`, and a prescribed value for
each variable. Letters and variables come with their formal inverses, so no letter and no
variable is its own inverse. -/
@[ext]
structure InvWordEq (X β N : Type*) where
  /-- The left-hand side. -/
  lhs : List ((X ⊕ β) × Bool)
  /-- The right-hand side. -/
  rhs : List ((X ⊕ β) × Bool)
  /-- The value of each letter. -/
  val : β → N
  /-- The prescribed value of each variable. -/
  varVal : X → N

namespace InvWordEq

variable {X Y β γ N : Type*}

section Size

/-- The number of occurrences of variables on the two sides of an equation. -/
def numVar (E : InvWordEq X β N) : ℕ :=
  (E.lhs.countP fun s => s.1.isLeft) + E.rhs.countP fun s => s.1.isLeft

/-- The number of occurrences of letters on the two sides of an equation. -/
def numConst (E : InvWordEq X β N) : ℕ :=
  (E.lhs.countP fun s => s.1.isRight) + E.rhs.countP fun s => s.1.isRight

/-- The number of occurrences of variables is the number of symbols of the two sides that are
variables. -/
theorem numVar_def (E : InvWordEq X β N) :
    E.numVar = (E.lhs.countP fun s => s.1.isLeft) + E.rhs.countP fun s => s.1.isLeft :=
  (rfl)

/-- The number of occurrences of letters is the number of symbols of the two sides that are
letters. -/
theorem numConst_def (E : InvWordEq X β N) :
    E.numConst = (E.lhs.countP fun s => s.1.isRight) + E.rhs.countP fun s => s.1.isRight :=
  (rfl)

/-- The two counts add up to the total length of the two sides. -/
theorem numVar_add_numConst (E : InvWordEq X β N) :
    E.numVar + E.numConst = E.lhs.length + E.rhs.length := by
  have h (u : List ((X ⊕ β) × Bool)) :
      (u.countP fun s => s.1.isLeft) + (u.countP fun s => s.1.isRight) = u.length := by
    simp [List.length_eq_countP_add_countP (fun s : (X ⊕ β) × Bool => s.1.isLeft) (l := u)]
  rw [numVar, numConst, add_add_add_comm, h, h]

end Size

section Solution

variable [Monoid N] [Star N]

/-- An assignment of signed words to the variables solves an equation with constraints when
the two sides become the same word and every variable takes its prescribed value. -/
structure IsSolution (E : InvWordEq X β N) (σ : X → List (β × Bool)) : Prop where
  /-- Substituting the words for the variables makes the two sides the same word. -/
  substituteVars_eq : substituteVars σ E.lhs = substituteVars σ E.rhs
  /-- Every variable takes its prescribed value. -/
  starVal_eq : ∀ x, starVal E.val (σ x) = E.varVal x

/-- A solution makes the two sides equal and gives every variable its prescribed value. -/
theorem isSolution_iff (E : InvWordEq X β N) (σ : X → List (β × Bool)) :
    E.IsSolution σ ↔
      substituteVars σ E.lhs = substituteVars σ E.rhs ∧ ∀ x, starVal E.val (σ x) = E.varVal x :=
  ⟨fun h => ⟨h.substituteVars_eq, h.starVal_eq⟩, fun h => ⟨h.1, h.2⟩⟩

/-- An equation has a solution all of whose words have length at most `s`. -/
def HasSolutionLE (E : InvWordEq X β N) (s : ℕ) : Prop :=
  ∃ σ, E.IsSolution σ ∧ ∀ x, (σ x).length ≤ s

/-- An equation has a solution of length at most `s` when some solution assigns words of length
at most `s` to all variables. -/
theorem hasSolutionLE_iff (E : InvWordEq X β N) (s : ℕ) :
    E.HasSolutionLE s ↔ ∃ σ, E.IsSolution σ ∧ ∀ x, (σ x).length ≤ s :=
  Iff.rfl

/-- A solution whose words have length at most `s` witnesses `HasSolutionLE`. -/
theorem IsSolution.hasSolutionLE {E : InvWordEq X β N} {σ : X → List (β × Bool)}
    (h : E.IsSolution σ) {s : ℕ} (hs : ∀ x, (σ x).length ≤ s) : E.HasSolutionLE s :=
  ⟨σ, h, hs⟩

/-- A solution of length at most `s` has length at most any larger bound. -/
theorem HasSolutionLE.mono {E : InvWordEq X β N} {s t : ℕ} (h : E.HasSolutionLE s) (hst : s ≤ t) :
    E.HasSolutionLE t :=
  let ⟨_, hσ, hs⟩ := h
  hσ.hasSolutionLE fun x => (hs x).trans hst

end Solution

section Operations

/-- Replace the letters of a word in variables and letters by signed words over another
alphabet, keeping the variables. -/
def mapLetters (ψ : γ → List (β × Bool)) (u : List ((X ⊕ γ) × Bool)) : List ((X ⊕ β) × Bool) :=
  u.flatMap (substituteLetter
    (Sum.elim (fun x => [(Sum.inl x, true)]) fun c => (ψ c).map (Prod.map Sum.inr id)))

/-- Replace the variables of a word in variables and letters by words in (other) variables and
letters, keeping the letters. -/
def substVars (τ : X → List ((Y ⊕ β) × Bool)) (u : List ((X ⊕ β) × Bool)) : List ((Y ⊕ β) × Bool) :=
  u.flatMap (substituteLetter (Sum.elim τ fun b => [(Sum.inr b, true)]))

variable (ψ : γ → List (β × Bool)) (τ : X → List ((Y ⊕ β) × Bool))

/-- Replacing letters is substitution, letter by letter, of the words of the letters. -/
theorem mapLetters_def (u : List ((X ⊕ γ) × Bool)) :
    mapLetters ψ u = u.flatMap (substituteLetter
      (Sum.elim (fun x => [(Sum.inl x, true)]) fun c => (ψ c).map (Prod.map Sum.inr id))) :=
  (rfl)

/-- Replacing variables is substitution, letter by letter, of the words of the variables. -/
theorem substVars_def (u : List ((X ⊕ β) × Bool)) :
    substVars τ u = u.flatMap (substituteLetter (Sum.elim τ fun b => [(Sum.inr b, true)])) :=
  (rfl)

/-- The empty word has no letters to replace. -/
@[simp] theorem mapLetters_nil : mapLetters ψ ([] : List ((X ⊕ γ) × Bool)) = [] :=
  List.flatMap_nil

/-- Letters are replaced in each part of a concatenation. -/
@[simp] theorem mapLetters_append (u v : List ((X ⊕ γ) × Bool)) :
    mapLetters ψ (u ++ v) = mapLetters ψ u ++ mapLetters ψ v :=
  List.flatMap_append

/-- A variable is kept. -/
@[simp] theorem mapLetters_singleton_inl (x : X) (e : Bool) :
    mapLetters ψ [(Sum.inl x, e)] = [(Sum.inl x, e)] := by
  cases e <;> simp [mapLetters, invRev]

/-- A positive letter is replaced by its word. -/
@[simp] theorem mapLetters_singleton_inr (c : γ) :
    mapLetters (X := X) ψ [(Sum.inr c, true)] = (ψ c).map (Prod.map Sum.inr id) := by
  simp [mapLetters]

/-- A negative letter is replaced by the formal inverse of its word. -/
@[simp] theorem mapLetters_singleton_inr_false (c : γ) :
    mapLetters (X := X) ψ [(Sum.inr c, false)] = (invRev (ψ c)).map (Prod.map Sum.inr id) := by
  simp [mapLetters, invRev, List.map_reverse]

/-- Replacing letters commutes with formal inverses. -/
theorem mapLetters_invRev (u : List ((X ⊕ γ) × Bool)) :
    mapLetters ψ (invRev u) = invRev (mapLetters ψ u) :=
  flatMap_substituteLetter_invRev _ u

/-- The empty word has no variables to replace. -/
@[simp] theorem substVars_nil : substVars τ [] = [] :=
  List.flatMap_nil

/-- Variables are replaced in each part of a concatenation. -/
@[simp] theorem substVars_append (u v : List ((X ⊕ β) × Bool)) :
    substVars τ (u ++ v) = substVars τ u ++ substVars τ v :=
  List.flatMap_append

/-- A positive variable is replaced by its word. -/
@[simp] theorem substVars_singleton_inl (x : X) : substVars τ [(Sum.inl x, true)] = τ x := by
  simp [substVars]

/-- A negative variable is replaced by the formal inverse of its word. -/
@[simp] theorem substVars_singleton_inl_false (x : X) :
    substVars τ [(Sum.inl x, false)] = invRev (τ x) := by
  simp [substVars]

/-- A letter is kept. -/
@[simp] theorem substVars_singleton_inr (b : β) (e : Bool) :
    substVars τ [(Sum.inr b, e)] = [(Sum.inr b, e)] := by
  cases e <;> simp [substVars, invRev]

/-- Replacing variables commutes with formal inverses. -/
theorem substVars_invRev (u : List ((X ⊕ β) × Bool)) :
    substVars τ (invRev u) = invRev (substVars τ u) :=
  flatMap_substituteLetter_invRev _ u

/-- Replacing the letters of an equation side by their words `ψ c` and then each variable `x` by
the word obtained from `σ x` by the same replacement is the same as replacing each variable `x` by
`σ x` and then the letters by their words. -/
theorem substituteVars_mapLetters (σ : X → List (γ × Bool)) (u : List ((X ⊕ γ) × Bool)) :
    substituteVars (fun x => (σ x).flatMap (substituteLetter ψ)) (mapLetters ψ u) =
      (substituteVars σ u).flatMap (substituteLetter ψ) := by
  simp only [substituteVars, mapLetters, flatMap_substituteLetter_flatMap_substituteLetter]
  congr 2
  funext s
  rcases s with x | c <;> simp

/-- Substituting for the variables after replacing variables by words in variables and letters
is substitution of the composite assignment. -/
@[simp]
theorem substituteVars_substVars (σ : Y → List (β × Bool)) (u : List ((X ⊕ β) × Bool)) :
    substituteVars σ (substVars τ u) = substituteVars (fun x => substituteVars σ (τ x)) u := by
  simp only [substituteVars, substVars, flatMap_substituteLetter_flatMap_substituteLetter]
  congr 2
  funext s
  rcases s with x | b <;> simp

end Operations

section Transport

variable [Monoid N] [StarMul N]

/-- If an equation is the image of another one under a substitution of words for letters that
is compatible with the values of the letters, then the substitution maps solutions of the
second equation to solutions of the first. -/
theorem IsSolution.flatMap_substituteLetter {E : InvWordEq X β N} {E' : InvWordEq X γ N}
    {ψ : γ → List (β × Bool)} {σ : X → List (γ × Bool)} (h : E'.IsSolution σ)
    (hl : E.lhs = mapLetters ψ E'.lhs) (hr : E.rhs = mapLetters ψ E'.rhs)
    (hval : ∀ c, starVal E.val (ψ c) = E'.val c) (hvar : E.varVal = E'.varVal) :
    E.IsSolution fun x => (σ x).flatMap (substituteLetter ψ) where
  substituteVars_eq := by
    rw [hl, hr, substituteVars_mapLetters, substituteVars_mapLetters, h.substituteVars_eq]
  starVal_eq x := by
    rw [starVal_flatMap_substituteLetter, funext hval, h.starVal_eq, hvar]

/-- If an equation is the image of another one under a substitution of words of length at most
`k` for letters that is compatible with the values of the letters, and the second equation has a
solution of length at most `s`, then the first has a solution of length at most `k * s`. -/
theorem HasSolutionLE.of_mapLetters {E : InvWordEq X β N} {E' : InvWordEq X γ N}
    {ψ : γ → List (β × Bool)} {s k : ℕ} (h : E'.HasSolutionLE s) (hψ : ∀ c, (ψ c).length ≤ k)
    (hl : E.lhs = mapLetters ψ E'.lhs) (hr : E.rhs = mapLetters ψ E'.rhs)
    (hval : ∀ c, starVal E.val (ψ c) = E'.val c) (hvar : E.varVal = E'.varVal) :
    E.HasSolutionLE (k * s) :=
  let ⟨_, hσ, hs⟩ := h
  (hσ.flatMap_substituteLetter hl hr hval hvar).hasSolutionLE fun x =>
    (length_flatMap_substituteLetter_le fun a _ => hψ a.1).trans (Nat.mul_le_mul_left k (hs x))

/-- If an equation `E₁` with the same values of the letters is obtained from `E` by replacing
each variable `x` by a word `τ x` in variables and letters whose value, computed with the
prescribed values of `E₁`, is the prescribed value of `x` in `E`, then composition with `τ` maps
solutions of `E₁` to solutions of `E`. -/
theorem IsSolution.substituteVars {E : InvWordEq X β N} {E₁ : InvWordEq Y β N}
    {τ : X → List ((Y ⊕ β) × Bool)} {σ : Y → List (β × Bool)} (h : E₁.IsSolution σ)
    (hl : E₁.lhs = substVars τ E.lhs) (hr : E₁.rhs = substVars τ E.rhs) (hval : E₁.val = E.val)
    (hvar : ∀ x, starVal (Sum.elim E₁.varVal E.val) (τ x) = E.varVal x) :
    E.IsSolution fun x => FreeGroup.substituteVars σ (τ x) where
  substituteVars_eq := by
    rw [← substituteVars_substVars, ← substituteVars_substVars, ← hl, ← hr, h.substituteVars_eq]
  starVal_eq x := by
    rw [← hvar x, FreeGroup.substituteVars, starVal_flatMap_substituteLetter]
    congr 1
    funext s
    rcases s with y | b
    · simpa [hval] using h.starVal_eq y
    · simp

end Transport

section Examples

/-- [DJP16, Example 1]: the equation `x a a⁻¹ y = y a⁻¹ a x` is solved by `x = a⁻¹ a a⁻¹`,
`y = a⁻¹ a a⁻¹ a a⁻¹`. With the value `2` in `ℕ` for the letter, the constraints prescribe the
lengths `3` and `5` of the words of `x` and `y`, so the equation has a solution by words of
length at most `5`. -/
example : (⟨[(Sum.inl true, true), (Sum.inr (), true), (Sum.inr (), false), (Sum.inl false, true)],
      [(Sum.inl false, true), (Sum.inr (), false), (Sum.inr (), true), (Sum.inl true, true)],
      fun _ => 2, fun x => bif x then 8 else 32⟩ : InvWordEq Bool Unit ℕ).HasSolutionLE 5 :=
  IsSolution.hasSolutionLE (σ := fun x => bif x then [((), false), ((), true), ((), false)]
      else [((), false), ((), true), ((), false), ((), true), ((), false)])
    ⟨by decide, fun x => by cases x <;> simp⟩ fun x => by cases x <;> decide

/-- The equation of [DJP16, Example 1] has four occurrences of variables and four of letters. -/
example : let E : InvWordEq Bool Unit ℕ :=
      ⟨[(Sum.inl true, true), (Sum.inr (), true), (Sum.inr (), false), (Sum.inl false, true)],
        [(Sum.inl false, true), (Sum.inr (), false), (Sum.inr (), true), (Sum.inl true, true)],
        fun _ => 2, fun x => bif x then 8 else 32⟩
    E.numVar = 4 ∧ E.numConst = 4 := by
  decide

/-- Equality of the two sides is equality of words, not in the free group: the word `a a⁻¹` does
not solve the equation `x = 1`. -/
example : ¬ (⟨[(Sum.inl (), true)], [], fun _ => 1, fun _ => 1⟩ :
      InvWordEq Unit Unit ℕ).IsSolution fun _ => [((), true), ((), false)] :=
  fun h => by simpa using h.substituteVars_eq

/-- The word `a a⁻¹` is its own formal inverse, so it solves the equation `x = x⁻¹`. -/
example : (⟨[(Sum.inl (), true)], [(Sum.inl (), false)], fun _ => 1, fun _ => 1⟩ :
      InvWordEq Unit Unit ℕ).IsSolution fun _ => [((), true), ((), false)] where
  substituteVars_eq := by decide
  starVal_eq _ := by simp

/-- The equation `x = x⁻¹` has no solution by a nonempty reduced word. -/
example (σ : Unit → List (Unit × Bool)) (h : IsReduced (σ ())) (h0 : σ () ≠ []) :
    ¬ (⟨[(Sum.inl (), true)], [(Sum.inl (), false)], fun _ => 1, fun _ => 1⟩ :
      InvWordEq Unit Unit ℕ).IsSolution σ := by
  intro hσ
  have hw : σ () = invRev (σ ()) := by simpa using hσ.substituteVars_eq
  have hsq : FreeGroup.mk (σ ()) ^ 2 = 1 := by
    rw [sq]
    nth_rw 2 [hw]
    rw [← inv_mk, mul_inv_cancel]
  exact h0 (h.eq_of_mk_eq .nil (by rw [← one_eq_mk]; exact sq_eq_one.1 hsq))

end Examples

end InvWordEq

end TauCeti
