/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import TauCeti.Algebra.BigOperators.ZPow
import TauCeti.Algebra.Group.AddChar.Basic
import TauCeti.NumberTheory.GaussSum.Basic
import TauCeti.NumberTheory.MulChar.Basic
import TauCeti.NumberTheory.MulChar.Cyclic

/-!
# Finite hypergeometric sums

Let `F` be a finite field with `q` elements, `ω` a multiplicative and `ψ` an additive character
of `F` with complex values, and write `g(m) = g(ω ^ m, ψ)` for the Gauss sum of the power `ω ^ m`,
`m ∈ ℤ`. A finite hypergeometric sum is attached to two multisets `a`, `b` of `d` integers, the
exponents of the characters `ω ^ aᵢ` and `ω ^ bⱼ`. When `ω` has order `q - 1`, these are the
parameter pairs `α = a / (q - 1)` and `β = b / (q - 1)` in `ℚ/ℤ` of a hypergeometric family, read
modulo `q - 1`. This file defines the three standard normalizations of the sum.

* `katzExpSum ω ψ a b t`, Katz's exponential sum over the torus `t ∏ xᵢ = ∏ yⱼ`,
  `∑ ψ(∑ xᵢ - ∑ yⱼ) ∏ ω^{aᵢ}(xᵢ) ∏ ω^{-bⱼ}(yⱼ)`, with the parameters indexed by finite types.
* `katzSum ω ψ a b t`, the sum
  `S_q(a, b | t) = (q - 1)⁻¹ ∑_{m < q - 1} ∏ᵢ g(m + aᵢ) g(-m - bᵢ) · ω((-1)^d t)^m`.
* `hypergeometricSum ω ψ a b t`, the normalized sum
  `H_q(a, b | t) = -(∏ᵢ g(aᵢ) g(-bᵢ))⁻¹ S_q(a, b | t)` of Beukers, Cohen and Mellit, their
  Definition 1.1. For the parameters of a hypergeometric motive, Katz showed that a power of `q`
  times `H_q(a, b | t)` is a Frobenius trace of the motive; that is the role of this sum.

The comparison `katzExpSum_eq` is Beukers–Cohen–Mellit Proposition 3.1: for `ω` of order `q - 1`
and `t ≠ 0`, Katz's sum is `ω(-1)^{∑ b} S_q(a, b | t)`. The indicator of `t ∏ xᵢ = ∏ yⱼ` is
expanded over the powers of `ω` (`MulChar.sum_range_pow_apply_eq_ite`), after which the sum over
the torus factors into Gauss sums. In particular `S_q` is then an algebraic integer
(`isIntegral_katzSum`).

Mathlib's convention that every multiplicative character, the trivial one included, vanishes at
`0` makes `g(0) = -1` for nontrivial `ψ`, so with `ψ` primitive the normalizing product of
`H_q` never vanishes (`TauCeti.gaussSum_ne_zero`). The value of the sums at `t = 0` is the single
term `m = 0`, which makes `H_q(a, b | 0) = 1/(1 - q)` (`hypergeometricSum_zero`); the comparison
with the torus sum, which vanishes at `t = 0`, needs `t ≠ 0`.

## Main declarations

* `TauCeti.Hypergeometric.katzExpSum`, with `katzExpSum_zero`, `katzExpSum_comp_equiv` (the
  parameters may be permuted) and `isIntegral_katzExpSum`.
* `TauCeti.Hypergeometric.katzSum`, with `katzSum_zero` and `isIntegral_katzSum`.
* `TauCeti.Hypergeometric.hypergeometricSum`, with `hypergeometricSum_eq_sum` (Definition 1.1 of
  Beukers–Cohen–Mellit), `prod_gaussSum_mul_prod_gaussSum_ne_zero` (the normalizing product is
  nonzero), `katzSum_eq_neg_mul_hypergeometricSum` and `hypergeometricSum_zero`.
* `TauCeti.Hypergeometric.katzExpSum_eq`: Beukers–Cohen–Mellit Proposition 3.1.

## References

* F. Beukers, H. Cohen and A. Mellit, *Finite hypergeometric functions*, Pure Appl. Math. Q. 11
  (2015), no. 4, §§1–3: Definition 1.1, (3.1) and Proposition 3.1.
* N. M. Katz, *Exponential sums and differential equations*, Annals of Mathematics Studies 124,
  Princeton University Press, 1990, §8.2.
-/

public section

namespace TauCeti.Hypergeometric

open Finset

variable {F : Type*} [Field F] [Fintype F]

/-- The finite hypergeometric sum
`S_q(a, b | t) = (q - 1)⁻¹ ∑_{m < q - 1} ∏ᵢ g(m + aᵢ) g(-m - bᵢ) · ω((-1)^d t)^m` over a finite
field with `q` elements, where `g(n)` is the Gauss sum of `ω ^ n` and `ψ`, and `d` is the number
of entries of `a`. -/
noncomputable def katzSum (ω : MulChar F ℂ) (ψ : AddChar F ℂ) (a b : Multiset ℤ) (t : F) : ℂ :=
  ((Fintype.card F - 1 : ℕ) : ℂ)⁻¹ * ∑ m ∈ range (Fintype.card F - 1),
    (a.map fun aᵢ ↦ gaussSum (ω ^ ((m : ℤ) + aᵢ)) ψ).prod *
      (b.map fun bᵢ ↦ gaussSum (ω ^ (-(m : ℤ) - bᵢ)) ψ).prod * ω ((-1) ^ Multiset.card a * t) ^ m

/-- The defining formula of `katzSum`. -/
theorem katzSum_def (ω : MulChar F ℂ) (ψ : AddChar F ℂ) (a b : Multiset ℤ) (t : F) :
    katzSum ω ψ a b t = ((Fintype.card F - 1 : ℕ) : ℂ)⁻¹ * ∑ m ∈ range (Fintype.card F - 1),
      (a.map fun aᵢ ↦ gaussSum (ω ^ ((m : ℤ) + aᵢ)) ψ).prod *
        (b.map fun bᵢ ↦ gaussSum (ω ^ (-(m : ℤ) - bᵢ)) ψ).prod *
          ω ((-1) ^ Multiset.card a * t) ^ m :=
  (rfl)

/-- The normalized finite hypergeometric sum of Beukers, Cohen and Mellit,
`H_q(a, b | t) = -(∏ᵢ g(aᵢ) g(-bᵢ))⁻¹ S_q(a, b | t)`, where `g(n)` is the Gauss sum of `ω ^ n`
and `ψ` and `S_q` is `katzSum`. With `ψ` primitive the normalizing product is nonzero, and the
normalization makes the value at `t = 0` equal to `1/(1 - q)` (`hypergeometricSum_zero`). -/
noncomputable def hypergeometricSum (ω : MulChar F ℂ) (ψ : AddChar F ℂ) (a b : Multiset ℤ)
    (t : F) : ℂ :=
  -((a.map fun aᵢ ↦ gaussSum (ω ^ aᵢ) ψ).prod * (b.map fun bᵢ ↦ gaussSum (ω ^ (-bᵢ)) ψ).prod)⁻¹ *
    katzSum ω ψ a b t

/-- Beukers–Cohen–Mellit (3.1): `H_q(a, b | t) = -(∏ᵢ g(aᵢ) g(-bᵢ))⁻¹ S_q(a, b | t)`. -/
theorem hypergeometricSum_def (ω : MulChar F ℂ) (ψ : AddChar F ℂ) (a b : Multiset ℤ) (t : F) :
    hypergeometricSum ω ψ a b t =
      -((a.map fun aᵢ ↦ gaussSum (ω ^ aᵢ) ψ).prod *
        (b.map fun bᵢ ↦ gaussSum (ω ^ (-bᵢ)) ψ).prod)⁻¹ * katzSum ω ψ a b t :=
  (rfl)

/-- `q - 1`, the number of terms of `katzSum`, is nonzero in `ℂ`. -/
private theorem card_sub_one_ne_zero : ((Fintype.card F - 1 : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.sub_ne_zero_of_lt Fintype.one_lt_card)

/-- `q - 1`, the number of terms of `katzSum`, is `#F - 1` in `ℂ`. -/
private theorem cast_card_sub_one : ((Fintype.card F - 1 : ℕ) : ℂ) = Fintype.card F - 1 := by
  rw [Nat.cast_sub Fintype.card_pos, Nat.cast_one]

/-- **Beukers–Cohen–Mellit, Definition 1.1.** The normalized sum is
`H_q(a, b | t) = (1 - q)⁻¹ ∑_{m < q - 1} ∏ᵢ (g(m + aᵢ) / g(aᵢ)) (g(-m - bᵢ) / g(-bᵢ))`
`· ω((-1)^d t)^m`. -/
theorem hypergeometricSum_eq_sum (ω : MulChar F ℂ) (ψ : AddChar F ℂ) (a b : Multiset ℤ) (t : F) :
    hypergeometricSum ω ψ a b t = (1 - (Fintype.card F : ℂ))⁻¹ *
      ∑ m ∈ range (Fintype.card F - 1),
        (a.map fun aᵢ ↦ gaussSum (ω ^ ((m : ℤ) + aᵢ)) ψ / gaussSum (ω ^ aᵢ) ψ).prod *
          (b.map fun bᵢ ↦ gaussSum (ω ^ (-(m : ℤ) - bᵢ)) ψ / gaussSum (ω ^ (-bᵢ)) ψ).prod *
            ω ((-1) ^ Multiset.card a * t) ^ m := by
  simp_rw [hypergeometricSum_def, katzSum_def, Multiset.prod_map_div, cast_card_sub_one,
    mul_sum]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [← neg_sub, inv_neg]
  ring

/-- With `ψ` primitive, the normalizing product `∏ᵢ g(aᵢ) g(-bᵢ)` of `hypergeometricSum` is
nonzero, since every Gauss sum `g(n)`, `g(0) = -1` included, is. -/
theorem prod_gaussSum_mul_prod_gaussSum_ne_zero (ω : MulChar F ℂ) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (a b : Multiset ℤ) :
    (a.map fun aᵢ ↦ gaussSum (ω ^ aᵢ) ψ).prod * (b.map fun bᵢ ↦ gaussSum (ω ^ (-bᵢ)) ψ).prod ≠
      0 := by
  have h : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  refine mul_ne_zero ?_ ?_ <;> refine Multiset.prod_ne_zero fun h0 ↦ ?_ <;>
    obtain ⟨n, -, hn⟩ := Multiset.mem_map.mp h0 <;> exact gaussSum_ne_zero h _ hψ hn

/-- With `ψ` primitive, `S_q(a, b | t) = -(∏ᵢ g(aᵢ) g(-bᵢ)) H_q(a, b | t)`, which inverts the
normalization defining `hypergeometricSum`. -/
theorem katzSum_eq_neg_mul_hypergeometricSum (ω : MulChar F ℂ) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (a b : Multiset ℤ) (t : F) :
    katzSum ω ψ a b t = -((a.map fun aᵢ ↦ gaussSum (ω ^ aᵢ) ψ).prod *
      (b.map fun bᵢ ↦ gaussSum (ω ^ (-bᵢ)) ψ).prod) * hypergeometricSum ω ψ a b t := by
  rw [hypergeometricSum_def, ← mul_assoc, neg_mul_neg,
    mul_inv_cancel₀ (prod_gaussSum_mul_prod_gaussSum_ne_zero ω hψ a b), one_mul]

/-- At `t = 0` only the term `m = 0` of `S_q` survives:
`S_q(a, b | 0) = (q - 1)⁻¹ ∏ᵢ g(aᵢ) g(-bᵢ)`. -/
@[simp]
theorem katzSum_zero (ω : MulChar F ℂ) (ψ : AddChar F ℂ) (a b : Multiset ℤ) :
    katzSum ω ψ a b 0 = ((Fintype.card F - 1 : ℕ) : ℂ)⁻¹ *
      ((a.map fun aᵢ ↦ gaussSum (ω ^ aᵢ) ψ).prod *
        (b.map fun bᵢ ↦ gaussSum (ω ^ (-bᵢ)) ψ).prod) := by
  rw [katzSum_def, mul_zero, MulChar.map_zero, sum_eq_single_of_mem 0
    (mem_range.mpr (Nat.sub_pos_of_lt Fintype.one_lt_card)) fun m _ hm ↦ by simp [hm]]
  simp [sub_eq_add_neg]

/-- **The value at `0`.** With `ψ` primitive, `H_q(a, b | 0) = 1/(1 - q)`, whatever the
parameters. -/
@[simp]
theorem hypergeometricSum_zero (ω : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (a b : Multiset ℤ) : hypergeometricSum ω ψ a b 0 = (1 - (Fintype.card F : ℂ))⁻¹ := by
  -- cancel the normalizing product from `S_q(a, b | 0) = -(∏ᵢ g(aᵢ) g(-bᵢ)) H_q(a, b | 0)`
  refine mul_left_cancel₀
    (neg_ne_zero.mpr (prod_gaussSum_mul_prod_gaussSum_ne_zero ω hψ a b)) ?_
  rw [← katzSum_eq_neg_mul_hypergeometricSum ω hψ, katzSum_zero, cast_card_sub_one,
    ← neg_sub (Fintype.card F : ℂ), inv_neg]
  ring

section ExpSum

variable [DecidableEq F] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **Katz's exponential sum** over the torus `t ∏ᵢ xᵢ = ∏ⱼ yⱼ`,
`∑ ψ(∑ᵢ xᵢ - ∑ⱼ yⱼ) ∏ᵢ ω^{aᵢ}(xᵢ) ∏ⱼ ω^{-bⱼ}(yⱼ)`, the parameters indexed by finite types. A
point with a zero coordinate contributes nothing, since every character vanishes at `0`. -/
noncomputable def katzExpSum (ω : MulChar F ℂ) (ψ : AddChar F ℂ) (a : ι → ℤ) (b : κ → ℤ)
    (t : F) : ℂ :=
  ∑ x : ι → F, ∑ y : κ → F,
    if t * ∏ i, x i = ∏ j, y j then
      ψ (∑ i, x i - ∑ j, y j) * ((∏ i, (ω ^ a i) (x i)) * ∏ j, (ω ^ (-b j)) (y j))
    else 0

/-- The defining formula of `katzExpSum`. -/
theorem katzExpSum_def (ω : MulChar F ℂ) (ψ : AddChar F ℂ) (a : ι → ℤ) (b : κ → ℤ) (t : F) :
    katzExpSum ω ψ a b t = ∑ x : ι → F, ∑ y : κ → F,
      if t * ∏ i, x i = ∏ j, y j then
        ψ (∑ i, x i - ∑ j, y j) * ((∏ i, (ω ^ a i) (x i)) * ∏ j, (ω ^ (-b j)) (y j))
      else 0 :=
  (rfl)

/-- Katz's exponential sum vanishes at `t = 0`: there `∏ⱼ yⱼ = 0`, and a character factor
vanishes at the zero coordinate. -/
@[simp]
theorem katzExpSum_zero (ω : MulChar F ℂ) (ψ : AddChar F ℂ) (a : ι → ℤ) (b : κ → ℤ) :
    katzExpSum ω ψ a b 0 = 0 := by
  refine Fintype.sum_eq_zero _ fun x ↦ Fintype.sum_eq_zero _ fun y ↦ ?_
  rw [zero_mul, ite_eq_right_iff]
  intro h
  rw [MulChar.prod_apply_eq_zero_of_prod_eq_zero _ h.symm, mul_zero, mul_zero]

/-- Katz's exponential sum does not depend on the indexing of the parameters. -/
theorem katzExpSum_comp_equiv {ι' κ' : Type*} [Fintype ι'] [Fintype κ'] [DecidableEq ι']
    [DecidableEq κ'] (e : ι' ≃ ι) (e' : κ' ≃ κ) (ω : MulChar F ℂ) (ψ : AddChar F ℂ) (a : ι → ℤ)
    (b : κ → ℤ) (t : F) : katzExpSum ω ψ (a ∘ e) (b ∘ e') t = katzExpSum ω ψ a b t := by
  refine Fintype.sum_equiv (e.arrowCongr (Equiv.refl F)) _ _ fun x ↦
    Fintype.sum_equiv (e'.arrowCongr (Equiv.refl F)) _ _ fun y ↦ ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq]
  rw [← e.prod_comp, ← e.sum_comp, ← e.prod_comp, ← e'.prod_comp, ← e'.sum_comp, ← e'.prod_comp]
  simp

/-- Katz's exponential sum is an algebraic integer. -/
theorem isIntegral_katzExpSum (ω : MulChar F ℂ) (ψ : AddChar F ℂ) (a : ι → ℤ) (b : κ → ℤ)
    (t : F) : IsIntegral ℤ (katzExpSum ω ψ a b t) := by
  refine IsIntegral.sum _ fun x _ ↦ IsIntegral.sum _ fun y _ ↦ ?_
  split_ifs
  · exact (ψ.isIntegral_apply _).mul <|
      (IsIntegral.prod _ fun i _ ↦ MulChar.isIntegral_apply _ _).mul <|
        IsIntegral.prod _ fun j _ ↦ MulChar.isIntegral_apply _ _
  · exact isIntegral_zero

omit [DecidableEq ι] [DecidableEq κ] in
/-- The indicator of `t ∏ᵢ xᵢ = ∏ⱼ yⱼ`, multiplied by a factor `c P` whose last factor `P`
carries the characters `ω ^ (-bⱼ)` at the `yⱼ`, expanded over the powers of a generator `ω`. -/
private theorem ite_eq_sum_range {ω : MulChar F ℂ} (hω : orderOf ω = Fintype.card F - 1)
    (a : ι → ℤ) (b : κ → ℤ) (t : F) (x : ι → F) (y : κ → F) (c : ℂ) :
    (if t * ∏ i, x i = ∏ j, y j then
        c * ((∏ i, (ω ^ a i) (x i)) * ∏ j, (ω ^ (-b j)) (y j)) else 0) =
      ((Fintype.card F - 1 : ℕ) : ℂ)⁻¹ * ∑ m ∈ range (Fintype.card F - 1),
        (ω ^ m) t * (∏ i, (ω ^ m) (x i)) * (∏ j, (ω ^ m)⁻¹ (y j)) *
          (c * ((∏ i, (ω ^ a i) (x i)) * ∏ j, (ω ^ (-b j)) (y j))) := by
  by_cases hy : ∏ j, y j = 0
  · simp only [MulChar.prod_apply_eq_zero_of_prod_eq_zero _ hy, mul_zero, ite_self,
      sum_const_zero]
  have key (m : ℕ) : (ω ^ m) t * (∏ i, (ω ^ m) (x i)) * (∏ j, (ω ^ m)⁻¹ (y j)) =
      (ω ^ m) (t * (∏ i, x i) * (∏ j, y j)⁻¹) := by
    rw [← map_prod, ← map_prod, MulChar.inv_apply', map_mul, map_mul]
  simp_rw [key, ← sum_mul]
  have hω' : orderOf ω = Fintype.card Fˣ := by rw [hω, Fintype.card_units]
  have horth := MulChar.sum_range_pow_apply_eq_ite hω' (t * (∏ i, x i) * (∏ j, y j)⁻¹)
  rw [Fintype.card_units] at horth
  simp only [horth, mul_inv_eq_one₀ hy]
  split_ifs
  · rw [inv_mul_cancel_left₀ card_sub_one_ne_zero]
  · simp

/-- Expanding the indicator of the torus over the powers of a generator `ω` writes Katz's sum
as a sum over `m < q - 1` of products of two sums over `F^ι` and `F^κ`. -/
private theorem katzExpSum_eq_sum_range {ω : MulChar F ℂ} (hω : orderOf ω = Fintype.card F - 1)
    (ψ : AddChar F ℂ) (a : ι → ℤ) (b : κ → ℤ) (t : F) :
    katzExpSum ω ψ a b t = ((Fintype.card F - 1 : ℕ) : ℂ)⁻¹ *
      ∑ m ∈ range (Fintype.card F - 1), (ω ^ m) t *
        ((∑ x : ι → F, ∏ i, ψ (x i) * (ω ^ ((m : ℤ) + a i)) (x i)) *
          (∑ y : κ → F, ∏ j, ψ (-y j) * (ω ^ (-(m : ℤ) - b j)) (y j))) := by
  rw [katzExpSum_def]
  -- pair up the sums over `x` and `y`, then bring the sum over `m` outside on the left
  simp_rw [ite_eq_sum_range hω a b t, sum_mul_sum, mul_sum, ← Fintype.sum_prod_type']
  rw [sum_comm]
  refine sum_congr rfl fun m _ ↦ sum_congr rfl fun p _ ↦ ?_
  simp only [zpow_add, zpow_neg, zpow_natCast, MulChar.mul_apply, prod_mul_distrib,
    sub_eq_add_neg, AddChar.map_add_eq_mul, ← sum_neg_distrib, AddChar.map_sum_eq_prod]
  ring

/-- **Beukers–Cohen–Mellit, Proposition 3.1.** For `ω` of order `q - 1` and `t ≠ 0`, Katz's
exponential sum is `ω(-1)^{∑ⱼ bⱼ} S_q(a, b | t)`, the parameters being equally many. -/
theorem katzExpSum_eq {ω : MulChar F ℂ} (hω : orderOf ω = Fintype.card F - 1) (ψ : AddChar F ℂ)
    (a : ι → ℤ) (b : κ → ℤ) (hab : Fintype.card ι = Fintype.card κ) {t : F} (ht : t ≠ 0) :
    katzExpSum ω ψ a b t =
      ω (-1) ^ (∑ j, b j) * katzSum ω ψ (univ.val.map a) (univ.val.map b) t := by
  have hs0 : ω (-1) ≠ 0 := (isUnit_neg_one.map ω).ne_zero
  -- `ω (-1) = ±1`, so every integer power of `ω (-1)` is its own inverse
  have hinv (n : ℤ) : (ω (-1) ^ n)⁻¹ = ω (-1) ^ n :=
    inv_eq_of_mul_eq_one_right (ω.apply_neg_one_zpow_mul_self n)
  have hneg (n : ℤ) : (ω ^ n) (-1) = ω (-1) ^ n := by
    simpa using ω.zpow_apply_coe_eq_zpow n (-1)
  have ht' (m : ℕ) : (ω ^ m) t = ω t ^ m := by simpa using ω.pow_apply_coe m (Units.mk0 t ht)
  rw [katzExpSum_eq_sum_range hω ψ a b t, katzSum_def]
  conv_rhs => rw [mul_left_comm, mul_sum]
  congr 1
  refine sum_congr rfl fun m _ ↦ ?_
  -- the sign: `ω (-1) ^ ∑ⱼ (-m - bⱼ) = ω (-1) ^ (∑ b) (ω (-1) ^ d) ^ m`
  have hsign : ω (-1) ^ ∑ j, (-(m : ℤ) - b j) =
      ω (-1) ^ (∑ j, b j) * (ω (-1) ^ Fintype.card κ) ^ m := by
    have hsum : ∑ j, (-(m : ℤ) - b j) = -(((Fintype.card κ * m : ℕ) : ℤ) + ∑ j, b j) := by
      simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [hsum, zpow_neg, hinv, zpow_add₀ hs0, zpow_natCast]
    ring
  rw [sum_prod_eq_prod_gaussSum ψ fun i ↦ ω ^ ((m : ℤ) + a i),
    sum_prod_neg_eq_prod_gaussSum ψ fun j ↦ ω ^ (-(m : ℤ) - b j)]
  simp only [hneg, prod_mul_distrib]
  rw [prod_zpow_eq_zpow_sum_of_isUnit _ (isUnit_neg_one.map ω), hsign]
  simp only [Multiset.map_map, Function.comp_def, prod_map_val, Multiset.card_map, card_val,
    card_univ, hab, ht', map_mul, map_pow, mul_pow]
  ring

end ExpSum

/-- With `ω` of order `q - 1` and `t ≠ 0`, the sum `S_q(a, b | t)` over two multisets of equally
many parameters is an algebraic integer. -/
theorem isIntegral_katzSum {ω : MulChar F ℂ} (hω : orderOf ω = Fintype.card F - 1)
    (ψ : AddChar F ℂ) {a b : Multiset ℤ} (hab : Multiset.card a = Multiset.card b) {t : F}
    (ht : t ≠ 0) : IsIntegral ℤ (katzSum ω ψ a b t) := by
  classical
  have hmap (s : Multiset ℤ) : univ.val.map s.toList.get = s := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have h := katzExpSum_eq hω ψ a.toList.get b.toList.get (by simpa using hab) ht
  rw [hmap, hmap] at h
  -- the sign `s = ω (-1) ^ ∑ b` satisfies `s * s = 1`
  set s := ω (-1) ^ ∑ j, b.toList.get j
  have hs : s * s = 1 := ω.apply_neg_one_zpow_mul_self _
  have hkatz : katzSum ω ψ a b t = s * katzExpSum ω ψ a.toList.get b.toList.get t := by
    rw [h, ← mul_assoc, hs, one_mul]
  rw [hkatz]
  exact (IsIntegral.of_pow two_pos (by rw [sq, hs]; exact isIntegral_one)).mul
    (isIntegral_katzExpSum ..)

end TauCeti.Hypergeometric
