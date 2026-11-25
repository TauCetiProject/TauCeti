/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import TauCeti.Algebra.Category.ModuleCat.Ext.QuotSMulTop

/-!
# Checks for `Ext` of cyclic groups

For a nonzero integer `n`, `Ext¹_ℤ(ℤ ⧸ n, ℤ) ≃ ℤ ⧸ n` (`ModuleCat.extOneQuotSMulTopEquiv`), so it
is a finite group of order `|n|`, and `Extᵏ_ℤ(ℤ ⧸ n, X) = 0` for `k ≥ 2`. For the Cuntz algebra
`O_n` with `n ≥ 2`, whose `K₀`-group is cyclic of order `n - 1`, the `Ext` term of the universal
coefficient theorem is `Ext¹_ℤ(ℤ ⧸ (n - 1), ℤ)`, of order `n - 1`.
-/

public section

open CategoryTheory CategoryTheory.Abelian ModuleCat Pointwise

namespace TauCeti.ExtQuotSMulTopExample

/-- `ℤ ⧸ n ℤ` has `|n|` elements. -/
theorem natCard_quotSMulTop_int (n : ℤ) : Nat.card (QuotSMulTop n ℤ) = n.natAbs := by
  have h : (n • ⊤ : Submodule ℤ ℤ) = Ideal.span {n} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  rw [Nat.card_congr ((Submodule.quotEquivOfEq _ _ h).toEquiv.trans
    (Int.quotientSpanEquivZMod n).toEquiv), Nat.card_zmod]

/-- **`Ext¹(ℤ ⧸ n, ℤ) ≃ ℤ ⧸ n`.** For `n ≠ 0`, `Ext¹_ℤ(ℤ ⧸ n, ℤ)` has `|n|` elements. -/
theorem natCard_ext_one_quotSMulTop_int {n : ℤ} (hn : n ≠ 0) :
    Nat.card (Ext.{0} (of ℤ (QuotSMulTop n ℤ)) (of ℤ ℤ) 1) = n.natAbs := by
  rw [Nat.card_congr (extOneQuotSMulTopEquiv (.of_ne_zero hn) (of ℤ ℤ)).toEquiv,
    natCard_quotSMulTop_int]

/-- Higher `Ext` out of `ℤ ⧸ n` vanishes for `n ≠ 0`. -/
theorem ext_quotSMulTop_int_add_two_eq_zero {n : ℤ} (hn : n ≠ 0) (X : ModuleCat.{0} ℤ) (k : ℕ)
    (e : Ext.{0} (of ℤ (QuotSMulTop n ℤ)) X (k + 2)) : e = 0 :=
  ext_quotSMulTop_add_two_eq_zero (.of_ne_zero hn) X k e

/-- **The Cuntz algebra case.** For `n ≥ 2`, `Ext¹_ℤ(ℤ ⧸ (n - 1), ℤ)`, the `Ext` term of the
universal coefficient theorem for `O_n`, has `n - 1` elements. -/
theorem natCard_ext_one_cuntz {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (Ext.{0} (of ℤ (QuotSMulTop ((n : ℤ) - 1) ℤ)) (of ℤ ℤ) 1) = n - 1 := by
  rw [natCard_ext_one_quotSMulTop_int (by omega)]
  omega

end TauCeti.ExtQuotSMulTopExample
