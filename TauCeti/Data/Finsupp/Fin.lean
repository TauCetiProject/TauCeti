/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Fin
public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Order.Fin.Tuple

/-!
# `Finsupp.cons`, `Finsupp.snoc` and their lexicographic comparison

`Finsupp.cons x s : Fin (n + 1) →₀ M` puts `x` in front of `s`. Adding two of them adds heads and
tails separately. The lexicographic order compares the entries at `0` first, so two of them are
compared by their heads, and then by their tails.

Dually, `Finsupp.snoc s x : Fin (n + 1) →₀ M` appends `x` after `s`, and `Finsupp.init t` forgets
the last entry of `t`; these are the `Finsupp` versions of `Fin.snoc` and `Fin.init`. Adding two
such vectors adds initial parts and last entries separately. Two such vectors are compared
lexicographically by their initial parts first, and then by their last entries.
-/

public section

namespace Finsupp

variable {n : ℕ} {M : Type*}

theorem cons_add_cons [AddZeroClass M] (x y : M) (s t : Fin n →₀ M) :
    cons x s + cons y t = cons (x + y) (s + t) := by
  ext i
  cases i using Fin.cases <;> simp

/-- Strict lexicographic comparison of `Finsupp.cons` compares the heads first and compares
the tails when the heads are equal. -/
theorem toLex_cons_lt_toLex_cons_iff [Zero M] [LT M] {x y : M} {s t : Fin n →₀ M} :
    toLex (cons x s) < toLex (cons y t) ↔ x < y ∨ x = y ∧ toLex s < toLex t := by
  simp only [Lex.lt_iff, ofLex_toLex]
  exact Fin.pi_lex_lt_cons_cons (α := fun _ ↦ M) (s := fun {_} ↦ (· < ·))

section Snoc

variable [Zero M]

/-- `Finsupp.snoc s y : Fin (n + 1) →₀ M` appends `y` after `s`. See `Fin.snoc`. -/
noncomputable def snoc (s : Fin n →₀ M) (y : M) : Fin (n + 1) →₀ M :=
  equivFunOnFinite.symm (Fin.snoc (s : Fin n → M) y)

/-- `Finsupp.init t : Fin n →₀ M` forgets the last entry of `t`. See `Fin.init`. -/
noncomputable def init (t : Fin (n + 1) →₀ M) : Fin n →₀ M :=
  equivFunOnFinite.symm (Fin.init t)

@[simp]
theorem coe_snoc (s : Fin n →₀ M) (y : M) : ⇑(snoc s y) = Fin.snoc (s : Fin n → M) y :=
  (rfl)

@[simp]
theorem coe_init (t : Fin (n + 1) →₀ M) : ⇑(init t) = Fin.init t :=
  (rfl)

theorem snoc_castSucc (s : Fin n →₀ M) (y : M) (i : Fin n) : snoc s y i.castSucc = s i := by
  simp

theorem snoc_last (s : Fin n →₀ M) (y : M) : snoc s y (Fin.last n) = y := by
  simp

theorem init_apply (t : Fin (n + 1) →₀ M) (i : Fin n) : init t i = t i.castSucc :=
  (rfl)

@[simp]
theorem init_snoc (s : Fin n →₀ M) (y : M) : init (snoc s y) = s := by
  ext i
  simp

@[simp]
theorem snoc_init_self (t : Fin (n + 1) →₀ M) : snoc (init t) (t (Fin.last n)) = t := by
  ext i
  simp

@[simp]
theorem snoc_zero_zero : snoc (0 : Fin n →₀ M) 0 = 0 := by
  ext i
  cases i using Fin.lastCases <;> simp

theorem snoc_injective2 : Function.Injective2 (snoc (n := n) (M := M)) := by
  intro s s' y y' h
  exact ⟨by simpa using congrArg init h, by simpa using DFunLike.congr_fun h (Fin.last n)⟩

@[simp]
theorem snoc_inj {s s' : Fin n →₀ M} {y y' : M} : snoc s y = snoc s' y' ↔ s = s' ∧ y = y' :=
  snoc_injective2.eq_iff

theorem eq_snoc_iff {t : Fin (n + 1) →₀ M} {s : Fin n →₀ M} {y : M} :
    t = snoc s y ↔ init t = s ∧ t (Fin.last n) = y := by
  conv_lhs => rw [← snoc_init_self t]
  exact snoc_inj

/-- Strict lexicographic comparison of `Finsupp.snoc` compares the initial parts first and
compares the last entries when the initial parts are equal. -/
theorem toLex_snoc_lt_toLex_snoc_iff [LT M] {x y : M} {s t : Fin n →₀ M} :
    toLex (snoc s x) < toLex (snoc t y) ↔ toLex s < toLex t ∨ s = t ∧ x < y := by
  simp only [Lex.lt_iff, ofLex_toLex, coe_snoc]
  constructor
  · rintro ⟨i, hlt, hi⟩
    cases i using Fin.lastCases with
    | last =>
      refine .inr ⟨ext fun j ↦ ?_, by simpa using hi⟩
      simpa using hlt j.castSucc (Fin.castSucc_lt_last j)
    | cast i =>
      refine .inl ⟨i, fun j hj ↦ ?_, by simpa using hi⟩
      simpa using hlt j.castSucc (Fin.castSucc_lt_castSucc_iff.2 hj)
  · rintro (⟨i, hlt, hi⟩ | ⟨rfl, h⟩)
    · refine ⟨i.castSucc, fun j hj ↦ ?_, by simpa using hi⟩
      cases j using Fin.lastCases with
      | last => exact absurd hj (Fin.castSucc_lt_last i).not_gt
      | cast j => simpa using hlt j (Fin.castSucc_lt_castSucc_iff.1 hj)
    · refine ⟨Fin.last n, fun j hj ↦ ?_, by simpa using h⟩
      cases j using Fin.lastCases with
      | last => exact absurd hj (lt_irrefl _)
      | cast j => simp

end Snoc

theorem snoc_add_snoc [AddZeroClass M] (s t : Fin n →₀ M) (x y : M) :
    snoc s x + snoc t y = snoc (s + t) (x + y) := by
  ext i
  cases i using Fin.lastCases <;> simp

end Finsupp
