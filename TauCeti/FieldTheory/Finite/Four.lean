/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.LinearCombination

/-!
# The four elements of a field of order four

A root `ω` of `X² + X + 1` labels the four elements as `0, 1, ω, ω²`.
The explicit enumeration supports finite calculations over this alphabet without choosing
another model of the field. Squaring exchanges the two roots in characteristic two.

Additively, a field of four elements is the Klein four-group: `zmodTwoProdAddEquiv` sends
`(a, b) : ZMod 2 × ZMod 2` to `a + bω`, so that the three nonzero elements `1, ω, ω²` correspond
to `(1, 0)`, `(0, 1)` and `(1, 1)`. The absolute trace to the prime field is `z ↦ z + z²`.
-/

public section

namespace TauCeti

/-- The Galois field of order four has four elements, independently of its enumeration. -/
theorem card_galoisField_two_two [Fintype (GaloisField 2 2)] :
    Fintype.card (GaloisField 2 2) = 4 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)]
  decide

variable {F : Type*} [Field F] [Finite F]

/-- Every element other than zero and one in a field of order four is a root of
`X² + X + 1`. -/
theorem sq_add_self_add_one_eq_zero (hF : Nat.card F = 4) {ω : F}
    (h0 : ω ≠ 0) (h1 : ω ≠ 1) : ω ^ 2 + ω + 1 = 0 := by
  let := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by simpa only [Nat.card_eq_fintype_card] using hF
  have hpow : ω ^ 3 = 1 := by simpa [hcard] using FiniteField.pow_card_sub_one_eq_one ω h0
  have hmul : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
    linear_combination hpow
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr h1)

/-- Squaring preserves roots of `X² + X + 1` in characteristic two. -/
theorem sq_sq_add_sq_add_one_eq_zero {R : Type*} [CommSemiring R] [CharP R 2]
    {ω : R} (hω : ω ^ 2 + ω + 1 = 0) : (ω ^ 2) ^ 2 + ω ^ 2 + 1 = 0 := by
  simpa only [map_add, map_pow, map_one, map_zero, frobenius_def] using
    congrArg (frobenius R 2) hω

/-- Every field of order four contains a root of `X² + X + 1`. -/
theorem exists_sq_add_self_add_one_eq_zero_of_card_eq_four (hF : Nat.card F = 4) :
    ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  classical
  let := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by simpa only [Nat.card_eq_fintype_card] using hF
  obtain ⟨ω, _, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset F)) (t := Finset.univ) (by simp [hcard])
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  exact ⟨ω, sq_add_self_add_one_eq_zero hF hω.1 hω.2⟩

omit [Finite F] in
/-- The four elements of a field of order four, labelled by a root of `X² + X + 1`. -/
theorem univ_eq_zero_one_root_sq [Fintype F] [DecidableEq F] (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : Finset.univ = {0, 1, ω, ω ^ 2} := by
  classical
  have hcard : Fintype.card F = 4 := by simpa only [Nat.card_eq_fintype_card] using hF
  let := charP_of_card_eq_prime_pow (p := 2) (f := 2) hcard
  have h0 : ω ≠ 0 := by rintro rfl; simp at hω
  have h1 : ω ≠ 1 := by rintro rfl; simp [CharTwo.add_self_eq_zero] at hω
  have hs0 : ω ^ 2 ≠ 0 := pow_ne_zero _ h0
  have hs1 : ω ^ 2 ≠ 1 := by
    intro h
    have : ω = 0 := by linear_combination hω - h - (CharTwo.two_eq_zero (R := F))
    exact h0 this
  have hself : ω ^ 2 ≠ ω := by
    intro h
    simp [h, CharTwo.add_self_eq_zero] at hω
  apply (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
  simp [hcard, Ne.symm hself, Ne.symm h0, Ne.symm h1,
    Ne.symm hs0, Ne.symm hs1]

/-- Label a field of four elements by `0, 1, ω, ω²`, in that order. -/
noncomputable def finFourEquiv (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : Fin 4 ≃ F := by
  classical
  letI := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by simpa only [Nat.card_eq_fintype_card] using hF
  refine Equiv.ofBijective ![0, 1, ω, ω ^ 2] ?_
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, by simp [hcard]⟩
  intro x
  have hx : x ∈ ({0, 1, ω, ω ^ 2} : Finset F) := by
    rw [← univ_eq_zero_one_root_sq hF hω]
    exact Finset.mem_univ x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- The four-element labelling evaluates to the displayed tuple. -/
@[simp]
theorem finFourEquiv_apply (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (i : Fin 4) :
    finFourEquiv hF hω i = ![0, 1, ω, ω ^ 2] i := (rfl)


/-! ### The additive group of a field of order four -/

/-- In a field of order four every element has additive order dividing two. -/
private theorem two_zsmul_eq_zero_of_natCard_eq_four (hF : Nat.card F = 4) (x : F) :
    (2 : ℤ) • x = 0 := by
  let := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 ^ 2 := Nat.card_eq_fintype_card.symm.trans hF
  let := charP_of_card_eq_prime_pow hcard
  rw [two_zsmul, CharTwo.add_self_eq_zero]

/-- The additive homomorphism `ℤ/2 → F` sending `1` to `x`. -/
private noncomputable def zmodTwoHom (hF : Nat.card F = 4) (x : F) : ZMod 2 →+ F :=
  ZMod.lift 2 ⟨zmultiplesHom F x, by simpa using two_zsmul_eq_zero_of_natCard_eq_four hF x⟩

private theorem zmodTwoHom_apply (hF : Nat.card F = 4) (x : F) (a : ZMod 2) :
    zmodTwoHom hF x a = (a.val : F) * x := by
  have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hcases a with rfl | rfl
  · rw [map_zero, ZMod.val_zero, Nat.cast_zero, zero_mul]
  · rw [zmodTwoHom, ← Int.cast_one, ZMod.lift_coe, Int.cast_one, ZMod.val_one, Nat.cast_one,
      one_mul]
    exact one_zsmul x

/-- **A field of order four is additively the Klein four-group**: given a root `ω` of
`X² + X + 1`, the pair `(a, b)` of residues modulo two corresponds to `a + bω`. -/
noncomputable def zmodTwoProdAddEquiv (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : ZMod 2 × ZMod 2 ≃+ F := by
  refine AddEquiv.ofBijective ((zmodTwoHom hF 1).coprod (zmodTwoHom hF ω)) ?_
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, by simp [hF]⟩
  have h0 : ω ≠ 0 := by rintro rfl; simp at hω
  have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  obtain ⟨a, b⟩ := x
  simp only [AddMonoidHom.coprod_apply, zmodTwoHom_apply] at hx
  rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl <;>
    simp only [ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul,
      mul_one, add_zero, zero_add, one_ne_zero] at hx
  · rfl
  · exact absurd hx h0
  · have hω' : ω = -1 := eq_neg_of_add_eq_zero_right hx
    have : (1 : F) = 0 := by rw [← hω]; rw [hω']; ring
    exact absurd this one_ne_zero

/-- The additive identification sends `(a, b)` to `a + bω`, using the canonical
representatives of `a` and `b`. -/
theorem zmodTwoProdAddEquiv_apply (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (a b : ZMod 2) :
    zmodTwoProdAddEquiv hF hω (a, b) = (a.val : F) + (b.val : F) * ω := by
  rw [zmodTwoProdAddEquiv, AddEquiv.ofBijective_apply, AddMonoidHom.coprod_apply,
    zmodTwoHom_apply, zmodTwoHom_apply, mul_one]

/-- The additive identification sends the first generator to `1`. -/
@[simp]
theorem zmodTwoProdAddEquiv_apply_one_zero (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : zmodTwoProdAddEquiv hF hω (1, 0) = 1 := by
  rw [zmodTwoProdAddEquiv_apply, ZMod.val_one, ZMod.val_zero, Nat.cast_one, Nat.cast_zero,
    zero_mul, add_zero]

/-- The additive identification sends the second generator to `ω`. -/
@[simp]
theorem zmodTwoProdAddEquiv_apply_zero_one (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : zmodTwoProdAddEquiv hF hω (0, 1) = ω := by
  rw [zmodTwoProdAddEquiv_apply, ZMod.val_one, ZMod.val_zero, Nat.cast_one, Nat.cast_zero,
    one_mul, zero_add]

/-- The additive identification sends the diagonal generator to `ω²`. -/
@[simp]
theorem zmodTwoProdAddEquiv_apply_one_one (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : zmodTwoProdAddEquiv hF hω (1, 1) = ω ^ 2 := by
  let := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 ^ 2 := Nat.card_eq_fintype_card.symm.trans hF
  let := charP_of_card_eq_prime_pow hcard
  rw [zmodTwoProdAddEquiv_apply, ZMod.val_one, Nat.cast_one, one_mul]
  linear_combination hω - ω ^ 2 * CharTwo.two_eq_zero (R := F)

/-- The inverse additive identification sends `1` to the first generator. -/
@[simp]
theorem zmodTwoProdAddEquiv_symm_one (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : (zmodTwoProdAddEquiv hF hω).symm 1 = (1, 0) :=
  (AddEquiv.symm_apply_eq _).mpr (zmodTwoProdAddEquiv_apply_one_zero hF hω).symm

/-- The inverse additive identification sends `ω` to the second generator. -/
@[simp]
theorem zmodTwoProdAddEquiv_symm_root (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : (zmodTwoProdAddEquiv hF hω).symm ω = (0, 1) :=
  (AddEquiv.symm_apply_eq _).mpr (zmodTwoProdAddEquiv_apply_zero_one hF hω).symm

/-- The inverse additive identification sends `ω²` to the diagonal generator. -/
@[simp]
theorem zmodTwoProdAddEquiv_symm_root_sq (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : (zmodTwoProdAddEquiv hF hω).symm (ω ^ 2) = (1, 1) :=
  (AddEquiv.symm_apply_eq _).mpr (zmodTwoProdAddEquiv_apply_one_one hF hω).symm

/-- The absolute trace of a field of order four to its prime field is `z ↦ z + z²`. -/
theorem algebraMap_trace_eq_add_sq_of_natCard_eq_four [Algebra (ZMod 2) F] (hF : Nat.card F = 4)
    (z : F) :
    algebraMap (ZMod 2) F (Algebra.trace (ZMod 2) F z) = z + z ^ 2 := by
  let := Fintype.ofFinite F
  have hfinrank : Module.finrank (ZMod 2) F = 2 := by
    have hcard := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hF] at hcard
    exact Nat.pow_right_injective le_rfl (hcard.symm.trans (by norm_num))
  rw [FiniteField.algebraMap_trace_eq_sum_pow, hfinrank, Nat.card_zmod]
  simp [Finset.sum_range_succ]

end TauCeti
