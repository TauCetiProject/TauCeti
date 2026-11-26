/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.StarVal

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

Two operations on the sides of an equation, `FreeGroup.substituteConsts` and
`FreeGroup.substituteVars` of `TauCeti.GroupTheory.FreeGroup.Substitution`, transport solutions
backwards:

* `FreeGroup.substituteConsts ψ` replaces letters by words. Suppose that an equation is the image
  of another one under `ψ`, that the value of each word `ψ c` is the value of the letter `c`, and
  that the two equations prescribe the same value for every variable. Then `ψ` maps solutions of
  the second equation to solutions of the first (`TauCeti.InvWordEq.IsSolution.substituteConsts`),
  multiplying their lengths by at most a bound on the lengths of the words `ψ c`
  (`TauCeti.InvWordEq.HasSolutionLE.of_substituteConsts`);
* `FreeGroup.substituteVars τ`, applied to a side whose letters are retagged as letters of the
  output, replaces variables by words `τ x` in variables and letters and keeps the letters. If an
  equation is obtained from another one in this way, with the same values of the letters, and the
  value of each `τ x` is the prescribed value of `x`, then composition with `τ` maps its solutions
  to solutions of the original equation (`TauCeti.InvWordEq.IsSolution.substituteVars`),
  multiplying their lengths by at most a bound on the lengths of the words `τ x`
  (`TauCeti.InvWordEq.HasSolutionLE.of_substituteVars`).

These are the two parts of the inverse operators by which solutions are transported back along
the steps of recompression in [DJP16, §2.2, §3], for the steps that create no letter equal to its
own inverse.

## Main definitions

* `TauCeti.InvWordEq`: word equations with constraints over the free monoid with involution.
* `TauCeti.InvWordEq.IsSolution`, `TauCeti.InvWordEq.HasSolutionLE`: solutions, and solutions
  by words of bounded length.
* `TauCeti.InvWordEq.numVarOccurrences`, `TauCeti.InvWordEq.numConstOccurrences`: the numbers of
  occurrences of variables and of letters.

## Main results

* `TauCeti.InvWordEq.IsSolution.substituteConsts`,
  `TauCeti.InvWordEq.HasSolutionLE.of_substituteConsts`: transport of solutions, and of length
  bounds, back along a replacement of letters.
* `TauCeti.InvWordEq.IsSolution.substituteVars`,
  `TauCeti.InvWordEq.HasSolutionLE.of_substituteVars`: transport of solutions, and of length
  bounds, back along a replacement of variables.

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
def numVarOccurrences (E : InvWordEq X β N) : ℕ :=
  (E.lhs.countP fun s => s.1.isLeft) + E.rhs.countP fun s => s.1.isLeft

/-- The number of occurrences of letters on the two sides of an equation. -/
def numConstOccurrences (E : InvWordEq X β N) : ℕ :=
  (E.lhs.countP fun s => s.1.isRight) + E.rhs.countP fun s => s.1.isRight

/-- The number of occurrences of variables is the number of symbols of the two sides that are
variables. -/
theorem numVarOccurrences_def (E : InvWordEq X β N) :
    E.numVarOccurrences =
      (E.lhs.countP fun s => s.1.isLeft) + E.rhs.countP fun s => s.1.isLeft :=
  (rfl)

/-- The number of occurrences of letters is the number of symbols of the two sides that are
letters. -/
theorem numConstOccurrences_def (E : InvWordEq X β N) :
    E.numConstOccurrences =
      (E.lhs.countP fun s => s.1.isRight) + E.rhs.countP fun s => s.1.isRight :=
  (rfl)

/-- The two counts add up to the total length of the two sides. -/
theorem numVarOccurrences_add_numConstOccurrences (E : InvWordEq X β N) :
    E.numVarOccurrences + E.numConstOccurrences = E.lhs.length + E.rhs.length := by
  have h (u : List ((X ⊕ β) × Bool)) :
      (u.countP fun s => s.1.isLeft) + (u.countP fun s => s.1.isRight) = u.length := by
    simp [List.length_eq_countP_add_countP (fun s : (X ⊕ β) × Bool => s.1.isLeft) (l := u)]
  rw [numVarOccurrences, numConstOccurrences, add_add_add_comm, h, h]

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

section Transport

variable [Monoid N] [StarMul N]

/-- If an equation is the image of another one under a substitution of words for letters that is
compatible with the values of the letters, and the two equations prescribe the same value for
every variable, then the substitution maps solutions of the second equation to solutions of the
first. -/
theorem IsSolution.substituteConsts {E : InvWordEq X β N} {E' : InvWordEq X γ N}
    {ψ : γ → List (β × Bool)} {σ : X → List (γ × Bool)} (h : E'.IsSolution σ)
    (hl : E.lhs = substituteConsts ψ E'.lhs) (hr : E.rhs = substituteConsts ψ E'.rhs)
    (hval : ∀ c, starVal E.val (ψ c) = E'.val c) (hvar : E.varVal = E'.varVal) :
    E.IsSolution fun x => (σ x).flatMap (substituteLetter ψ) where
  substituteVars_eq := by
    rw [hl, hr, substituteVars_substituteConsts, substituteVars_substituteConsts,
      h.substituteVars_eq]
  starVal_eq x := by
    rw [starVal_flatMap_substituteLetter, funext hval, h.starVal_eq, hvar]

/-- If an equation is the image of another one under a substitution of words of length at most
`k` for letters that is compatible with the values of the letters, the two equations prescribe the
same value for every variable, and the second equation has a solution of length at most `s`, then
the first has a solution of length at most `k * s`. -/
theorem HasSolutionLE.of_substituteConsts {E : InvWordEq X β N} {E' : InvWordEq X γ N}
    {ψ : γ → List (β × Bool)} {s k : ℕ} (h : E'.HasSolutionLE s) (hψ : ∀ c, (ψ c).length ≤ k)
    (hl : E.lhs = substituteConsts ψ E'.lhs) (hr : E.rhs = substituteConsts ψ E'.rhs)
    (hval : ∀ c, starVal E.val (ψ c) = E'.val c) (hvar : E.varVal = E'.varVal) :
    E.HasSolutionLE (k * s) :=
  let ⟨_, hσ, hs⟩ := h
  (hσ.substituteConsts hl hr hval hvar).hasSolutionLE fun x =>
    (length_flatMap_substituteLetter_le fun a _ => hψ a.1).trans (Nat.mul_le_mul_left k (hs x))

/-- If an equation `E₁` with the same values of the letters is obtained from `E` by replacing
each variable `x` by a word `τ x` in variables and letters, keeping the letters, and the value of
`τ x`, computed with the prescribed values of `E₁`, is the prescribed value of `x` in `E`, then
composition with `τ` maps solutions of `E₁` to solutions of `E`. -/
theorem IsSolution.substituteVars {E : InvWordEq X β N} {E₁ : InvWordEq Y β N}
    {τ : X → List ((Y ⊕ β) × Bool)} {σ : Y → List (β × Bool)} (h : E₁.IsSolution σ)
    (hl : E₁.lhs = FreeGroup.substituteVars τ (E.lhs.map (Prod.map (Sum.map id Sum.inr) id)))
    (hr : E₁.rhs = FreeGroup.substituteVars τ (E.rhs.map (Prod.map (Sum.map id Sum.inr) id)))
    (hval : E₁.val = E.val)
    (hvar : ∀ x, starVal (Sum.elim E₁.varVal E.val) (τ x) = E.varVal x) :
    E.IsSolution fun x => FreeGroup.substituteVars σ (τ x) where
  substituteVars_eq := by
    rw [← substituteVars_substituteVars_map, ← substituteVars_substituteVars_map, ← hl, ← hr,
      h.substituteVars_eq]
  starVal_eq x := by
    have hρ : (fun s => starVal E.val (Sum.elim σ (fun b => [(b, true)]) s)) =
        Sum.elim E₁.varVal E.val := by
      funext s
      rcases s with y | b
      · simpa [hval] using h.starVal_eq y
      · simp
    rw [← hvar x, FreeGroup.substituteVars, starVal_flatMap_substituteLetter, hρ]

/-- If an equation `E₁` with the same values of the letters is obtained from `E` by replacing
each variable `x` by a word `τ x` of length at most `k` in variables and letters, keeping the
letters, the value of `τ x`, computed with the prescribed values of `E₁`, is the prescribed value of
`x` in `E`, and `E₁` has a solution of length at most `s`, then `E` has a solution of length at most
`k * max 1 s`: each letter of `τ x` contributes one letter, and each variable at most `s`. -/
theorem HasSolutionLE.of_substituteVars {E : InvWordEq X β N} {E₁ : InvWordEq Y β N}
    {τ : X → List ((Y ⊕ β) × Bool)} {s k : ℕ} (h : E₁.HasSolutionLE s)
    (hτ : ∀ x, (τ x).length ≤ k)
    (hl : E₁.lhs = FreeGroup.substituteVars τ (E.lhs.map (Prod.map (Sum.map id Sum.inr) id)))
    (hr : E₁.rhs = FreeGroup.substituteVars τ (E.rhs.map (Prod.map (Sum.map id Sum.inr) id)))
    (hval : E₁.val = E.val)
    (hvar : ∀ x, starVal (Sum.elim E₁.varVal E.val) (τ x) = E.varVal x) :
    E.HasSolutionLE (k * max 1 s) :=
  let ⟨σ, hσ, hs⟩ := h
  (hσ.substituteVars hl hr hval hvar).hasSolutionLE fun x => by
    refine (length_flatMap_substituteLetter_le (k := max 1 s) fun a _ => ?_).trans ?_
    · rcases a with ⟨y | b, _⟩
      · exact (hs y).trans (le_max_right 1 s)
      · exact le_max_left 1 s
    · rw [mul_comm]
      exact Nat.mul_le_mul_right _ (hτ x)

end Transport

section Examples

/-- The equation `x a a⁻¹ y = y a⁻¹ a x` of [DJP16, Example 1], with the value `2` in `ℕ` for the
letter and the prescribed values `8` for `x` and `32` for `y`. -/
private def djpEq : InvWordEq Bool Unit ℕ :=
  ⟨[(Sum.inl true, true), (Sum.inr (), true), (Sum.inr (), false), (Sum.inl false, true)],
    [(Sum.inl false, true), (Sum.inr (), false), (Sum.inr (), true), (Sum.inl true, true)],
    fun _ => 2, fun x => bif x then 8 else 32⟩

/-- The equation `x = x⁻¹` in one variable over a one-letter alphabet, without constraints. -/
private def selfInvEq : InvWordEq Unit Unit ℕ :=
  ⟨[(Sum.inl (), true)], [(Sum.inl (), false)], fun _ => 1, fun _ => 1⟩

/-- [DJP16, Example 1]: the equation `x a a⁻¹ y = y a⁻¹ a x` is solved by `x = a⁻¹ a a⁻¹`,
`y = a⁻¹ a a⁻¹ a a⁻¹`. With the value `2` in `ℕ` for the letter, the constraints prescribe the
lengths `3` and `5` of the words of `x` and `y`, so the equation has a solution by words of
length at most `5`. -/
example : djpEq.HasSolutionLE 5 :=
  IsSolution.hasSolutionLE (σ := fun x => bif x then [((), false), ((), true), ((), false)]
      else [((), false), ((), true), ((), false), ((), true), ((), false)])
    ⟨by decide, fun x => by cases x <;> simp [djpEq]⟩ fun x => by cases x <;> decide

/-- The equation of [DJP16, Example 1] has four occurrences of variables and four of letters. -/
example : djpEq.numVarOccurrences = 4 ∧ djpEq.numConstOccurrences = 4 := by
  decide

/-- Equality of the two sides is equality of words, not in the free group: the word `a a⁻¹` does
not solve the equation `x = 1`. -/
example : ¬ (⟨[(Sum.inl (), true)], [], fun _ => 1, fun _ => 1⟩ :
      InvWordEq Unit Unit ℕ).IsSolution fun _ => [((), true), ((), false)] :=
  fun h => by simpa using h.substituteVars_eq

/-- The word `a a⁻¹` is its own formal inverse, so it solves the equation `x = x⁻¹`. -/
example : selfInvEq.IsSolution fun _ => [((), true), ((), false)] where
  substituteVars_eq := by decide
  starVal_eq _ := by simp [selfInvEq]

/-- The equation `x = x⁻¹` has no solution by a nonempty reduced word. -/
example (σ : Unit → List (Unit × Bool)) (h : IsReduced (σ ())) (h0 : σ () ≠ []) :
    ¬ selfInvEq.IsSolution σ := by
  intro hσ
  have hw : σ () = invRev (σ ()) := by simpa [selfInvEq] using hσ.substituteVars_eq
  exact h.invRev_ne_self h0 hw.symm

end Examples

end InvWordEq

end TauCeti
