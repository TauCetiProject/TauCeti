/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Conj
public import TauCeti.Algebra.Group.Exponent

/-!
# Powers coprime to the exponent permute the conjugacy classes

If `n` is coprime to the exponent of a monoid `M`, then `g ↦ g ^ n` has an inverse of the same
form, since `n` is invertible modulo the exponent (`Monoid.exists_forall_pow_mul_eq_self`). Hence
powering by `n` permutes the conjugacy classes of `M`. In a group this permutation also fixes the
class sizes.

These are the class permutations through which the Galois group of a cyclotomic field acts on the
columns of a character table: see J.-P. Serre, *Linear Representations of Finite Groups*, §12.4.

## Main statements

* `ConjClasses.powEquiv`: the permutation `C ↦ C ^ n` of the conjugacy classes.
* `ConjClasses.powEquiv_one`: this permutation fixes the class of the identity.
* `ConjClasses.card_carrier_pow`: a power coprime to the exponent preserves class sizes.
-/

public section

namespace ConjClasses

section Monoid

variable {M : Type*} [Monoid M] {n : ℕ}

/-- **Powering by `n` permutes the conjugacy classes** when `n` is coprime to the exponent. -/
noncomputable def powEquiv (hn : (Monoid.exponent M).Coprime n) :
    ConjClasses M ≃ ConjClasses M :=
  have hm := (Monoid.exists_forall_pow_mul_eq_self hn).choose_spec
  { toFun C := C ^ n
    invFun C := C ^ (Monoid.exists_forall_pow_mul_eq_self hn).choose
    left_inv C := by
      obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
      simp only [mk_pow, ← _root_.pow_mul, hm]
    right_inv C := by
      obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
      simp only [mk_pow, ← _root_.pow_mul, mul_comm _ n, hm] }

/-- The permutation `ConjClasses.powEquiv` is powering by `n`. -/
@[simp]
theorem powEquiv_apply (hn : (Monoid.exponent M).Coprime n) (C : ConjClasses M) :
    powEquiv hn C = C ^ n :=
  (rfl)

/-- The permutation `ConjClasses.powEquiv` fixes the class of the identity. -/
theorem powEquiv_one (hn : (Monoid.exponent M).Coprime n) :
    powEquiv hn (1 : ConjClasses M) = 1 := by
  rw [powEquiv_apply, one_eq_mk_one, mk_pow, one_pow]

end Monoid

/-- A power coprime to the exponent of a group preserves the size of a conjugacy class. -/
theorem card_carrier_pow {G : Type*} [Group G] {n : ℕ} (hn : (Monoid.exponent G).Coprime n)
    (C : ConjClasses G) : Nat.card (C ^ n).carrier = Nat.card C.carrier := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  rw [mk_pow]
  exact card_carrier_mk_pow g (hn.coprime_dvd_left (Monoid.order_dvd_exponent g))

end ConjClasses
