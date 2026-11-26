/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.GroupTheory.Perm.Sign
public import TauCeti.RingTheory.MilnorK.Basic
import Mathlib.Algebra.CharP.Two
import TauCeti.Algebra.BigOperators.Ring.List

/-!
# Permutation signs of Milnor symbols

Over a field `F` the degree-one classes `{a}` of the Milnor K-ring anticommute, so permuting the
entries of a Milnor symbol multiplies it by the sign of the permutation:
`{a_{σ 0}, …, a_{σ (n - 1)}} = sign σ • {a₀, …, a_{n - 1}}`.

The classes `{a}` do not square to zero, since `{a, a} = {a, -1}`, so the Milnor ring is not an
exterior algebra and a symbol with a repeated entry need not vanish: over `ℝ` the symbol
`{-1, -1}` is nonzero (Weibel, Example III.7.2(c)). What the sign rule does give is the following.
If the unit `a` occurs twice in a list `l` of units, then moving both copies to the front shows
`{l} = {a, -1} · {l'}`, where `l'` is `l` with the two copies removed; the sign of the moving
permutation is absorbed because `{a, -1}` has order dividing two. Consequently a symbol with a
repeated entry is killed by `2`, it vanishes in characteristic two, and it is twice another
element as soon as `-1` is a square in `F`.

## Main results

* `TauCeti.MilnorK.symbol_ofFn_comp_perm`: permuting the entries of a Milnor symbol multiplies it
  by the sign of the permutation.
* `TauCeti.MilnorK.symbol_ofFn_comp_swap`: interchanging two entries negates a Milnor symbol.
* `TauCeti.MilnorK.symbol_eq_ofUnit_mul_ofUnit_neg_one_mul_of_perm`: if `l` is a permutation of
  `a :: a :: l'`, then `{l} = {a, -1} · {l'}`.
* `TauCeti.MilnorK.exists_perm_and_symbol_eq_ofUnit_mul_ofUnit_neg_one_mul_of_not_nodup`: a
  symbol with a repeated entry `a` is `{a, -1} · {l'}`, where `l'` is the list with two copies of
  `a` removed.
* `TauCeti.MilnorK.two_nsmul_symbol_of_not_nodup`: a symbol with a repeated entry is killed by `2`.
* `TauCeti.MilnorK.symbol_eq_zero_of_not_nodup`: in characteristic two, a symbol with a repeated
  entry vanishes.
* `TauCeti.MilnorK.exists_symbol_eq_two_nsmul_of_not_nodup`: if `-1` is a square, a symbol with a
  repeated entry is divisible by `2`.

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), 318–344, §1.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Definition 7.1 and Example 7.2.
-/

public section

namespace TauCeti

namespace MilnorK

variable {F : Type*} [Field F]

/-- **Permutation signs of Milnor symbols.** Over a field, permuting the entries of a Milnor symbol
multiplies it by the sign of the permutation:
`{a_{σ 0}, …, a_{σ (n - 1)}} = sign σ • {a₀, …, a_{n - 1}}`. -/
theorem symbol_ofFn_comp_perm {n : ℕ} (f : Fin n → Fˣ) (σ : Equiv.Perm (Fin n)) :
    symbol (List.ofFn (f ∘ σ)) = Equiv.Perm.sign σ • symbol (List.ofFn f) := by
  simp only [symbol_def, List.map_ofFn, ← Function.comp_assoc]
  exact List.prod_ofFn_comp_perm (fun _ _ _ ↦ ofUnit_mul_ofUnit_comm _ _) σ

/-- Over a field, interchanging two distinct entries of a Milnor symbol negates it. -/
theorem symbol_ofFn_comp_swap {n : ℕ} (f : Fin n → Fˣ) {i j : Fin n} (hij : i ≠ j) :
    symbol (List.ofFn (f ∘ Equiv.swap i j)) = -symbol (List.ofFn f) := by
  rw [symbol_ofFn_comp_perm, Equiv.Perm.sign_swap hij, Units.neg_smul, one_smul]

/-- The Milnor symbols of two lists that are permutations of each other agree up to sign. -/
private theorem symbol_eq_or_eq_neg_of_perm {l₁ l₂ : List Fˣ} (h : l₁.Perm l₂) :
    symbol l₂ = symbol l₁ ∨ symbol l₂ = -symbol l₁ := by
  induction h with
  | nil => exact .inl rfl
  | cons a _ ih => rcases ih with ih | ih <;> simp [ih]
  | swap a b l =>
    exact .inr (by simp only [symbol_cons, ← mul_assoc, ofUnit_mul_ofUnit_comm a b, neg_mul])
  | trans _ _ ih₁ ih₂ =>
    rcases ih₁ with ih₁ | ih₁ <;> rcases ih₂ with ih₂ | ih₂ <;> simp [ih₁, ih₂]

/-- Over a field, if the list `l` is a permutation of `a :: a :: l'`, then the Milnor symbol of `l`
is `{a, -1} · {l'}`. No sign appears, because `{a, -1}` has order dividing two. -/
theorem symbol_eq_ofUnit_mul_ofUnit_neg_one_mul_of_perm {l l' : List Fˣ} {a : Fˣ}
    (h : l.Perm (a :: a :: l')) : symbol l = ofUnit a * ofUnit (-1) * symbol l' := by
  have hneg : -(ofUnit a * ofUnit (-1) * symbol l') = ofUnit a * ofUnit (-1) * symbol l' := by
    rw [← neg_mul, neg_ofUnit_mul_ofUnit_neg_one]
  rcases symbol_eq_or_eq_neg_of_perm h with h | h <;>
    rw [symbol_cons, symbol_cons, ← mul_assoc, ofUnit_mul_ofUnit_self] at h
  · exact h.symm
  · rw [← hneg, h, neg_neg]

/-- Over a field, a Milnor symbol with a repeated entry `a` is `{a, -1} · {l'}`, where `l'` is
the list with two copies of `a` removed, in the sense that `l` is a permutation of
`a :: a :: l'`. -/
theorem exists_perm_and_symbol_eq_ofUnit_mul_ofUnit_neg_one_mul_of_not_nodup {l : List Fˣ}
    (h : ¬l.Nodup) :
    ∃ a l', l.Perm (a :: a :: l') ∧ symbol l = ofUnit a * ofUnit (-1) * symbol l' := by
  obtain ⟨a, ha⟩ : ∃ a, [a, a].Sublist l := by simpa [List.nodup_iff_sublist] using h
  obtain ⟨l', hl'⟩ := ha.exists_perm_append
  exact ⟨a, l', hl', symbol_eq_ofUnit_mul_ofUnit_neg_one_mul_of_perm hl'⟩

/-- Over a field, a Milnor symbol with a repeated entry is killed by `2`. It need not vanish:
`{-1, -1} ≠ 0` over `ℝ`. -/
theorem two_nsmul_symbol_of_not_nodup {l : List Fˣ} (h : ¬l.Nodup) : 2 • symbol l = 0 := by
  obtain ⟨a, l', -, hl⟩ := exists_perm_and_symbol_eq_ofUnit_mul_ofUnit_neg_one_mul_of_not_nodup h
  rw [hl, two_nsmul, ← add_mul,
    eq_neg_iff_add_eq_zero.1 (neg_ofUnit_mul_ofUnit_neg_one a).symm, zero_mul]

/-- Over a field of characteristic two, a Milnor symbol with a repeated entry vanishes. -/
theorem symbol_eq_zero_of_not_nodup [CharP F 2] {l : List Fˣ} (h : ¬l.Nodup) : symbol l = 0 := by
  obtain ⟨a, l', -, hl⟩ := exists_perm_and_symbol_eq_ofUnit_mul_ofUnit_neg_one_mul_of_not_nodup h
  have h1 : (-1 : Fˣ) = 1 := Units.ext (by simp [CharTwo.neg_one_eq_one])
  rw [hl, h1, ofUnit_one, mul_zero, zero_mul]

/-- Over a field in which `-1` is a square, a Milnor symbol with a repeated entry is twice another
element of the Milnor K-ring, so it vanishes modulo `2`. -/
theorem exists_symbol_eq_two_nsmul_of_not_nodup (hsq : IsSquare (-1 : F)) {l : List Fˣ}
    (h : ¬l.Nodup) : ∃ y, symbol l = 2 • y := by
  obtain ⟨a, l', -, hl⟩ := exists_perm_and_symbol_eq_ofUnit_mul_ofUnit_neg_one_mul_of_not_nodup h
  obtain ⟨b, hb⟩ := hsq
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  have hu : (-1 : Fˣ) = Units.mk0 b hb0 * Units.mk0 b hb0 := Units.ext (by simp [hb])
  refine ⟨ofUnit a * ofUnit (Units.mk0 b hb0) * symbol l', ?_⟩
  rw [hl, hu, ofUnit_mul, mul_add, add_mul, two_nsmul]

end MilnorK

end TauCeti
