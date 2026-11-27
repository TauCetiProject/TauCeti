/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.United
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Data.ZMod.Units

/-!
# Genus characters of binary quadratic forms

Gauss sorts the primitive forms of a discriminant `D` into genera by the values of his
*assigned characters* on the integers they represent. This file sets up those characters on the
form side, for every discriminant, fundamental or not.

A multiplicative character `χ` modulo `n` is a *genus character of discriminant `D`*
(`IsGenusChar D χ`) when it is trivial on the values prime to `n` of the principal form of
discriminant `D`. Because the product of two values of a form of discriminant `D` is a value of
the principal form (`exists_eval_mul_eval_eq_eval_principalForm`), such a `χ` takes one value on
all the values prime to `n` of any form of discriminant `D`
(`IsGenusChar.apply_eval_eq_apply_eval`), and that value squares to `1`. This common value
is `genusChar χ f`. It is unchanged by proper changes of variables
(`IsGenusChar.genusChar_smul`), is `1` on the principal form, and is multiplicative under
Dirichlet composition (`IsGenusChar.genusChar_mk_mul`), because the composition of united
forms represents the products of their values (`eval_mul_eval_eq_eval_mk_mul`).

The assigned characters are genus characters. For a prime `p ∣ D` this is the Legendre symbol
`(· | p)` (`isGenusChar_quadraticChar`), which carries information only for odd `p`. For
`D = 4N` the characters of `(ℤ/8ℤ)ˣ` are `δ(m) = (-1)^((m - 1)/2)` (Mathlib's `ZMod.χ₄`),
`ε(m) = (-1)^((m² - 1)/8)` (`ZMod.χ₈`) and `δε` (`ZMod.χ₈'`). Here `δ` is a genus character
when `N ≡ 0, 3 mod 4` (`isGenusChar_χ₄`), `ε` when `N ≡ 0, 2 mod 8` (`isGenusChar_χ₈`), `δε`
when `N ≡ 0, 6 mod 8` (`isGenusChar_χ₈'`), and every character modulo `8` when `8 ∣ N`
(`isGenusChar_of_emod_eight_eq_zero`). For these residues of `N`, each of them is constant on
the odd values of `x² - Ny²`.

## Main definitions

* `TauCeti.BinaryQuadraticForm.IsGenusChar D χ`: `χ` is trivial on the values prime to its
  modulus of the principal form of discriminant `D`.
* `TauCeti.BinaryQuadraticForm.genusChar χ f`: the value of `χ` at a value of `f` prime to the
  modulus of `χ`.

## References

* C. F. Gauss, *Disquisitiones Arithmeticae*, art. 229–231.
* D. A. Cox, *Primes of the Form x² + ny²*, §3.B, and Theorem 3.15 there.
-/

public section

open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

variable {n : ℕ} {R : Type*} [CommMonoidWithZero R]

/-- A multiplicative character `χ` modulo `n` is a **genus character of discriminant `D`** when it
takes the value `1` at every value prime to `n` of the principal form of discriminant `D`. -/
def IsGenusChar (D : ℤ) (χ : MulChar (ZMod n) R) : Prop :=
  ∀ x y : ℤ, IsUnit (((principalForm D).eval x y : ℤ) : ZMod n) →
    χ ((principalForm D).eval x y) = 1

/-- Unfolding `IsGenusChar`: `χ` is `1` at every value prime to `n` of the principal form. -/
theorem isGenusChar_iff {D : ℤ} {χ : MulChar (ZMod n) R} :
    IsGenusChar D χ ↔ ∀ x y : ℤ, IsUnit (((principalForm D).eval x y : ℤ) : ZMod n) →
      χ ((principalForm D).eval x y) = 1 :=
  Iff.rfl

/-- The **genus character** of the form `f` for a character `χ` modulo `n`: the value of `χ` at a
value of `f` prime to `n`. When `χ` is a genus character of the discriminant of `f`, this is the
value of `χ` at every value of `f` prime to `n` (`IsGenusChar.genusChar_eq`). It is `0` when
`f` takes no value prime to `n` (`genusChar_eq_zero`). -/
noncomputable def genusChar (χ : MulChar (ZMod n) R) (f : BinaryQuadraticForm ℤ) : R :=
  let v := Classical.epsilon fun v : ℤ × ℤ ↦ IsUnit ((f.eval v.1 v.2 : ℤ) : ZMod n)
  χ (f.eval v.1 v.2)

/-- Unfolding `genusChar`: it is the value of `χ` at the value of `f` at the chosen point. -/
private theorem genusChar_def (χ : MulChar (ZMod n) R) (f : BinaryQuadraticForm ℤ) :
    genusChar χ f = χ (f.eval
      (Classical.epsilon fun v : ℤ × ℤ ↦ IsUnit ((f.eval v.1 v.2 : ℤ) : ZMod n)).1
      (Classical.epsilon fun v : ℤ × ℤ ↦ IsUnit ((f.eval v.1 v.2 : ℤ) : ZMod n)).2) :=
  rfl

/-- A form taking no value prime to `n` has genus character `0`. -/
theorem genusChar_eq_zero {χ : MulChar (ZMod n) R} {f : BinaryQuadraticForm ℤ}
    (hf : ∀ x y : ℤ, ¬ IsUnit ((f.eval x y : ℤ) : ZMod n)) : genusChar χ f = 0 := by
  rw [genusChar_def]
  exact χ.map_nonunit (hf _ _)

/-- **Negating a form twists its genus character by `χ(-1)`**: `-f` and `f` take values prime to
`n` at the same points, and every value of `-f` is the negative of the value of `f`. So negation
preserves the genus characters with `χ(-1) = 1` and changes the sign of the others, on every form
taking a value prime to the modulus. -/
theorem genusChar_neg (χ : MulChar (ZMod n) R) (f : BinaryQuadraticForm ℤ) :
    genusChar χ (-f) = χ (-1) * genusChar χ f := by
  have hp : (fun v : ℤ × ℤ ↦ IsUnit (((-f).eval v.1 v.2 : ℤ) : ZMod n)) =
      fun v ↦ IsUnit ((f.eval v.1 v.2 : ℤ) : ZMod n) := by
    funext v
    rw [eval_neg, Int.cast_neg, IsUnit.neg_iff]
  rw [genusChar_def, genusChar_def, hp, eval_neg, Int.cast_neg, neg_eq_neg_one_mul, map_mul]

/-- A primitive form takes a value prime to any nonzero `n` (Cox, Lemma 2.25). -/
theorem IsPrimitive.exists_isUnit_eval {f : BinaryQuadraticForm ℤ} (hf : f.IsPrimitive)
    (hn : n ≠ 0) : ∃ x y : ℤ, IsUnit ((f.eval x y : ℤ) : ZMod n) := by
  obtain ⟨x, y, -, h⟩ := hf.exists_isCoprime_eval (M := n) (by exact_mod_cast hn)
  exact ⟨x, y, (ZMod.isUnit_intCast_iff_isCoprime _ _).mpr h.symm⟩

namespace IsGenusChar

variable {χ : MulChar (ZMod n) R}

/-- A genus character takes the value `1` at a product of two values of a form when that product
is prime to the modulus. -/
private theorem apply_mul_apply_eval {f : BinaryQuadraticForm ℤ}
    (hχ : IsGenusChar f.discrim χ) {x y z w : ℤ}
    (h : IsUnit ((f.eval x y : ℤ) : ZMod n) ∧ IsUnit ((f.eval z w : ℤ) : ZMod n)) :
    χ (f.eval x y) * χ (f.eval z w) = 1 := by
  obtain ⟨u, v, huv⟩ := exists_eval_mul_eval_eq_eval_principalForm f x y z w
  rw [← map_mul, ← Int.cast_mul, huv]
  exact hχ u v (huv ▸ Int.cast_mul (α := ZMod n) _ _ ▸ h.1.mul h.2)

/-- **A genus character is constant on the values of a form prime to its modulus.** -/
theorem apply_eval_eq_apply_eval {f : BinaryQuadraticForm ℤ} (hχ : IsGenusChar f.discrim χ)
    {x y z w : ℤ} (hxy : IsUnit ((f.eval x y : ℤ) : ZMod n))
    (hzw : IsUnit ((f.eval z w : ℤ) : ZMod n)) : χ (f.eval x y) = χ (f.eval z w) := by
  calc χ (f.eval x y) = χ (f.eval x y) * (χ (f.eval x y) * χ (f.eval z w)) := by
        rw [hχ.apply_mul_apply_eval ⟨hxy, hzw⟩, mul_one]
    _ = χ (f.eval x y) * χ (f.eval x y) * χ (f.eval z w) := (mul_assoc _ _ _).symm
    _ = χ (f.eval z w) := by rw [hχ.apply_mul_apply_eval ⟨hxy, hxy⟩, one_mul]

/-- The genus character of a form is the value of `χ` at any of its values prime to the
modulus. -/
theorem genusChar_eq {f : BinaryQuadraticForm ℤ} (hχ : IsGenusChar f.discrim χ) {x y : ℤ}
    (h : IsUnit ((f.eval x y : ℤ) : ZMod n)) : genusChar χ f = χ (f.eval x y) := by
  rw [genusChar_def]
  exact hχ.apply_eval_eq_apply_eval
    (Classical.epsilon_spec (p := fun v : ℤ × ℤ ↦ IsUnit ((f.eval v.1 v.2 : ℤ) : ZMod n))
      ⟨(x, y), h⟩) h

/-- The genus character of a form taking a value prime to the modulus squares to `1`. -/
theorem genusChar_sq {f : BinaryQuadraticForm ℤ} (hχ : IsGenusChar f.discrim χ)
    (hf : ∃ x y : ℤ, IsUnit ((f.eval x y : ℤ) : ZMod n)) : genusChar χ f ^ 2 = 1 := by
  obtain ⟨x, y, h⟩ := hf
  rw [hχ.genusChar_eq h, sq, hχ.apply_mul_apply_eval ⟨h, h⟩]

/-- **The genus character is an invariant of the proper class.** -/
theorem genusChar_smul {f : BinaryQuadraticForm ℤ} (hχ : IsGenusChar f.discrim χ)
    (γ : SL(2, ℤ)) : genusChar χ (γ • f) = genusChar χ f := by
  by_cases hf : ∃ x y : ℤ, IsUnit ((f.eval x y : ℤ) : ZMod n)
  · obtain ⟨x, y, h⟩ := hf
    -- `f = γ⁻¹ • (γ • f)`, so every value of `f` is a value of `γ • f`.
    obtain ⟨x', y', hv⟩ : ∃ x' y' : ℤ, f.eval x y = (γ • f).eval x' y' :=
      ⟨_, _, by rw [← eval_smul, inv_smul_smul]⟩
    have hγχ : IsGenusChar (γ • f).discrim χ := by rwa [discrim_smul]
    rw [hγχ.genusChar_eq (hv ▸ h), ← hv, hχ.genusChar_eq h]
  · push Not at hf
    rw [genusChar_eq_zero hf, genusChar_eq_zero fun x y ↦ by rw [eval_smul]; exact hf _ _]

/-- The genus character of the principal form is `1`. -/
theorem genusChar_principalForm {D : ℤ} (hχ : IsGenusChar D χ) :
    genusChar χ (principalForm D) = 1 := by
  rw [genusChar_def]
  exact hχ _ _ (Classical.epsilon_spec (p := fun v : ℤ × ℤ ↦
    IsUnit (((principalForm D).eval v.1 v.2 : ℤ) : ZMod n)) ⟨(1, 0), by simp⟩)

/-- **The genus character is multiplicative under Dirichlet composition.** The composition
`(aa', B, C)` of `(a, B, a'C)` and `(a', B, aC)` has as genus character the product of theirs,
provided both take values prime to the modulus (as primitive forms do,
`IsPrimitive.exists_isUnit_eval`). -/
theorem genusChar_mk_mul {a a' B C : ℤ}
    (hχ : IsGenusChar (⟨a * a', B, C⟩ : BinaryQuadraticForm ℤ).discrim χ)
    (hf : ∃ x y : ℤ, IsUnit (((⟨a, B, a' * C⟩ : BinaryQuadraticForm ℤ).eval x y : ℤ) : ZMod n))
    (hg : ∃ x y : ℤ, IsUnit (((⟨a', B, a * C⟩ : BinaryQuadraticForm ℤ).eval x y : ℤ) : ZMod n)) :
    genusChar χ ⟨a * a', B, C⟩ = genusChar χ ⟨a, B, a' * C⟩ * genusChar χ ⟨a', B, a * C⟩ := by
  obtain ⟨x, y, hxy⟩ := hf
  obtain ⟨z, w, hzw⟩ := hg
  have hfχ : IsGenusChar (⟨a, B, a' * C⟩ : BinaryQuadraticForm ℤ).discrim χ := by
    rwa [discrim_mk_mul_left]
  have hgχ : IsGenusChar (⟨a', B, a * C⟩ : BinaryQuadraticForm ℤ).discrim χ := by
    rwa [discrim_mk_mul_right]
  have hprod := eval_mul_eval_eq_eval_mk_mul a a' B C x y z w
  have hunit := hxy.mul hzw
  rw [← Int.cast_mul, hprod] at hunit
  rw [hχ.genusChar_eq hunit, ← hprod, Int.cast_mul, map_mul, hfχ.genusChar_eq hxy,
    hgχ.genusChar_eq hzw]

end IsGenusChar

/-! ### The assigned characters -/

/-- For a prime `p` dividing `D ≡ 0, 1 mod 4`, the Legendre symbol `(· | p)` is a genus character
of discriminant `D`. -/
theorem isGenusChar_quadraticChar {p : ℕ} [Fact p.Prime] {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1)
    (hpD : (p : ℤ) ∣ D) : IsGenusChar D (quadraticChar (ZMod p)) := by
  intro x y hxy
  -- For `p = 2` the only value prime to `p` modulo `p` is `1`; for odd `p`, four times a value of
  -- the principal form is `(2x + δy)² - Dy²`, a square modulo `p`.
  rcases eq_or_ne p 2 with rfl | hp
  · generalize (((principalForm D).eval x y : ℤ) : ZMod 2) = a at hxy ⊢
    fin_cases a
    · exact absurd hxy not_isUnit_zero
    · exact map_one _
  have h4 := congrArg (Int.cast : ℤ → ZMod p) (four_mul_eval_principalForm hD x y)
  push_cast at h4
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr hpD, zero_mul, sub_zero] at h4
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have hsq : ((2 * x + D % 2 * y : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    intro h
    rw [h, zero_pow two_ne_zero] at h4
    exact (mul_ne_zero (pow_ne_zero 2 h2) hxy.ne_zero) (by rw [← h4]; norm_num)
  have := quadraticChar_sq_one' hsq
  push_cast at this
  rwa [← h4, map_mul, show (4 : ZMod p) = 2 ^ 2 by norm_num, quadraticChar_sq_one' h2,
    one_mul] at this

/-- A character modulo `m` is a genus character of discriminant `4N` once it is `1` at every unit
`X² - rY²` of `ℤ/mℤ`, where `r` is `N` modulo `m`. -/
private theorem isGenusChar_four_mul {m : ℕ} {χ : MulChar (ZMod m) R} {N : ℤ} {r : ZMod m}
    (hr : (N : ZMod m) = r) (h : ∀ X Y : ZMod m, IsUnit (X ^ 2 - r * Y ^ 2) →
      χ (X ^ 2 - r * Y ^ 2) = 1) :
    IsGenusChar (4 * N) χ := by
  intro x y hxy
  simp only [principalForm_four_mul, eval_mk, one_mul, zero_mul, add_zero, neg_mul,
    ← sub_eq_add_neg, Int.cast_sub, Int.cast_pow, Int.cast_mul, hr] at hxy ⊢
  exact h _ _ hxy

/-- An integer with residue `k` modulo `8` is `k` in `ZMod 8`. -/
private theorem intCast_zmod_eight {N k : ℤ} (hN : N % 8 = k) : (N : ZMod 8) = k := by
  rw [← ZMod.intCast_mod N 8, Nat.cast_ofNat, hN]

/-- **`δ` is a genus character of discriminant `4N` for `N ≡ 0, 3 mod 4`**: the odd values of
`x² - Ny²` are then `1` modulo `4`. Here `δ(m) = (-1)^((m - 1)/2)` is Mathlib's `ZMod.χ₄`. -/
theorem isGenusChar_χ₄ {N : ℤ} (hN : N % 4 = 0 ∨ N % 4 = 3) :
    IsGenusChar (4 * N) ZMod.χ₄ := by
  have hval : ∀ r : ZMod 4, r = 0 ∨ r = 3 → ∀ X Y : ZMod 4,
      ZMod.χ₄ (X ^ 2 - r * Y ^ 2) = 0 ∨ ZMod.χ₄ (X ^ 2 - r * Y ^ 2) = 1 := by
    decide
  refine isGenusChar_four_mul (ZMod.intCast_mod N 4).symm fun X Y hu ↦
    (hval _ ?_ X Y).resolve_left (hu.map ZMod.χ₄).ne_zero
  rcases hN with h | h <;> simp [h]

/-- **Every character modulo `8` is a genus character of discriminant `4N` for `8 ∣ N`**: the odd
values of `x² - Ny²` are then `1` modulo `8`. In particular `ε` and `δε` are. -/
theorem isGenusChar_of_emod_eight_eq_zero {N : ℤ} (hN : N % 8 = 0)
    (χ : MulChar (ZMod 8) R) : IsGenusChar (4 * N) χ := by
  have hval : ∀ X : ZMod 8, X ^ 2 = 1 ∨ X ^ 2 * 2 = 0 := by decide
  refine isGenusChar_four_mul (r := 0) ?_ fun X Y hu ↦ ?_
  · rw [intCast_zmod_eight hN, Int.cast_zero]
  · rw [zero_mul, sub_zero] at hu ⊢
    rcases hval X with h | h
    · rw [h, map_one]
    · exact absurd (hu.mul_right_eq_zero.mp h) (by decide)

/-- **`ε` is a genus character of discriminant `4N` for `N ≡ 0, 2 mod 8`**: the odd values of
`x² - Ny²` are then `±1` modulo `8`. Here `ε(m) = (-1)^((m² - 1)/8)` is Mathlib's `ZMod.χ₈`. -/
theorem isGenusChar_χ₈ {N : ℤ} (hN : N % 8 = 0 ∨ N % 8 = 2) : IsGenusChar (4 * N) ZMod.χ₈ := by
  rcases hN with hN | hN
  · exact isGenusChar_of_emod_eight_eq_zero hN _
  have hval : ∀ X Y : ZMod 8,
      ZMod.χ₈ (X ^ 2 - 2 * Y ^ 2) = 0 ∨ ZMod.χ₈ (X ^ 2 - 2 * Y ^ 2) = 1 := by
    decide
  refine isGenusChar_four_mul ?_ fun X Y hu ↦
    (hval X Y).resolve_left (hu.map ZMod.χ₈).ne_zero
  rw [intCast_zmod_eight hN, Int.cast_ofNat]

/-- **`δε` is a genus character of discriminant `4N` for `N ≡ 0, 6 mod 8`**: the odd values of
`x² - Ny²` are then `1` or `3` modulo `8`. Here `δε` is Mathlib's `ZMod.χ₈'`. -/
theorem isGenusChar_χ₈' {N : ℤ} (hN : N % 8 = 0 ∨ N % 8 = 6) : IsGenusChar (4 * N) ZMod.χ₈' := by
  rcases hN with hN | hN
  · exact isGenusChar_of_emod_eight_eq_zero hN _
  have hval : ∀ X Y : ZMod 8,
      ZMod.χ₈' (X ^ 2 - 6 * Y ^ 2) = 0 ∨ ZMod.χ₈' (X ^ 2 - 6 * Y ^ 2) = 1 := by
    decide
  refine isGenusChar_four_mul ?_ fun X Y hu ↦
    (hval X Y).resolve_left (hu.map ZMod.χ₈').ne_zero
  rw [intCast_zmod_eight hN, Int.cast_ofNat]

/-- At discriminant `-20` the form `2x² + 2xy + 3y²` has `δ`-genus character `-1`, since it
represents `3 ≡ 3 mod 4`. This differs from the value `1` of the principal form `x² + 5y²`
(`IsGenusChar.genusChar_principalForm`). -/
theorem genusChar_χ₄_mk_two_two_three : genusChar ZMod.χ₄ ⟨2, 2, 3⟩ = -1 := by
  have hχ : IsGenusChar (⟨2, 2, 3⟩ : BinaryQuadraticForm ℤ).discrim ZMod.χ₄ := by
    rw [discrim_def, discrim, show (2 : ℤ) ^ 2 - 4 * 2 * 3 = 4 * -5 by norm_num]
    exact isGenusChar_χ₄ (by decide)
  have h3 : IsUnit (((3 : ℤ) : ZMod 4)) := by decide
  rw [hχ.genusChar_eq (x := 0) (y := 1) (by rwa [eval_zero_one]), eval_zero_one]
  decide

end TauCeti.BinaryQuadraticForm
