/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.Divisible

import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.FieldSimp
import TauCeti.Data.Rat.NumDenDvd

/-!
# Homomorphisms from `ℚ` and compatible systems of roots

A homomorphism `r` from `(ℚ, +)` to a group `G` is determined by its values `y n = r (1 / n!)`,
which form a *compatible system of factorial roots*: `y (n + 1) ^ (n + 1) = y n` for every `n`.
Conversely every such sequence comes from a unique homomorphism, which sends `a / n!` to
`y n ^ a`. No commutativity is assumed: the terms of a compatible system are powers of one another,
so they commute.

Consequently, in an `ℕ`-rootable group every element `x` is `r (ofAdd 1)` for a homomorphism
`r : Multiplicative ℚ →* G`: choose the roots one after the other, starting from `x`
(`TauCeti.factorialRoots`).

## Main definitions

* `TauCeti.factorialRoots x`: the compatible system of factorial roots of `x` in an `ℕ`-rootable
  monoid, obtained by taking roots one after the other.
* `MonoidHom.ofFactorialRoots y hy`: the homomorphism `Multiplicative ℚ →* G` sending `a / n!` to
  `y n ^ a`, for a compatible system `y` of factorial roots.
* `TauCeti.factorialRootsEquiv G`: compatible systems of factorial roots in `G` correspond to
  homomorphisms `Multiplicative ℚ →* G`.

## Main results

* `TauCeti.pow_factorial_div_factorial_eq`: in a compatible system, `y m ^ (m! / n!) = y n` for
  `n ≤ m`.
* `MonoidHom.ofFactorialRoots_apply_inv_factorial`: `ofFactorialRoots y hy` sends `1 / n!` to
  `y n`; `MonoidHom.ext_rat_inv_factorial`: a homomorphism from `Multiplicative ℚ` is determined
  by its values at the `1 / n!`; `MonoidHom.comp_ofFactorialRoots`: naturality in the target.
* `TauCeti.exists_monoidHom_rat_apply_ofAdd_one`: in an `ℕ`-rootable group every element is the
  value at `ofAdd 1` of a homomorphism from `Multiplicative ℚ`.
* `TauCeti.forall_exists_monoidHom_rat_apply_ofAdd_one_iff`: this property characterises the
  groups in which every element has an `n`-th root for every `n ≠ 0`.
-/

public section

open Multiplicative Nat

variable {M : Type*} [Monoid M] {G : Type*} [Group G]

namespace TauCeti

/-- In a compatible system of factorial roots `y (n + 1) ^ (n + 1) = y n` in a monoid, `y n` is
the `(m! / n!)`-th power of `y m` for `n ≤ m`. -/
theorem pow_factorial_div_factorial_eq {y : ℕ → M} (hy : ∀ n, y (n + 1) ^ (n + 1) = y n)
    {n m : ℕ} (hnm : n ≤ m) : y m ^ (m ! / n !) = y n := by
  induction m, hnm using Nat.le_induction with
  | base => rw [Nat.div_self (factorial_pos n), pow_one]
  | succ m hnm ih =>
    rw [factorial_succ, Nat.mul_div_assoc _ (factorial_dvd_factorial hnm), pow_mul, hy, ih]

/-- The compatible system of factorial roots of `x` in an `ℕ`-rootable monoid, obtained by taking
roots one after the other: `factorialRoots x 0 = x`, and `factorialRoots x (n + 1)` is the chosen
`(n + 1)`-th root `RootableBy.root` of `factorialRoots x n`. -/
noncomputable def factorialRoots [RootableBy M ℕ] (x : M) : ℕ → M
  | 0 => x
  | n + 1 => RootableBy.root (factorialRoots x n) (n + 1)

@[simp]
theorem factorialRoots_zero [RootableBy M ℕ] (x : M) : factorialRoots x 0 = x := by
  rw [factorialRoots]

/-- The term of `factorialRoots x` at level `n + 1` is the root chosen by `RootableBy.root`. -/
theorem factorialRoots_succ [RootableBy M ℕ] (x : M) (n : ℕ) :
    factorialRoots x (n + 1) = RootableBy.root (factorialRoots x n) (n + 1) := by
  rw [factorialRoots]

@[simp]
theorem factorialRoots_succ_pow [RootableBy M ℕ] (x : M) (n : ℕ) :
    factorialRoots x (n + 1) ^ (n + 1) = factorialRoots x n := by
  rw [factorialRoots, RootableBy.root_cancel _ n.succ_ne_zero]

end TauCeti

namespace MonoidHom

/-- Every rational number `q` is `a / n!` for an integer `a`, as soon as `q.den ≤ n`: the
factorial case of `Rat.den_dvd_iff_exists_mul_intCast_eq`. -/
private theorem exists_mul_factorial_eq (q : ℚ) {n : ℕ} (hn : q.den ≤ n) :
    ∃ a : ℤ, q * n ! = a := by
  simpa only [Int.cast_natCast] using (Rat.den_dvd_iff_exists_mul_intCast_eq q (n ! : ℕ)).1
    (Int.natCast_dvd_natCast.2 (dvd_factorial q.den_pos hn))

/-- A homomorphism from `Multiplicative ℚ` to a monoid is determined by its values at the
`1 / n!`. -/
theorem ext_rat_inv_factorial {f g : Multiplicative ℚ →* M}
    (h : ∀ n : ℕ, f (ofAdd (n ! : ℚ)⁻¹) = g (ofAdd (n ! : ℚ)⁻¹)) : f = g := by
  -- The values are units, and in `Mˣ` integer powers are available.
  suffices f.toHomUnits = g.toHomUnits from
    DFunLike.ext _ _ fun x ↦ congrArg Units.val (DFunLike.congr_fun this x)
  refine DFunLike.ext _ _ fun x ↦ ?_
  obtain ⟨a, ha⟩ := exists_mul_factorial_eq x.toAdd le_rfl
  -- Write `x` as the `a`-th power of `1 / n!`, with `n` the denominator of `x`.
  have hx : x = ofAdd ((x.toAdd.den ! : ℚ)⁻¹) ^ a := by
    rw [← ofAdd_zsmul, zsmul_eq_mul, ← ha,
      mul_inv_cancel_right₀ (by exact_mod_cast factorial_ne_zero _), ofAdd_toAdd]
  rw [hx, map_zpow, map_zpow]
  exact congrArg (· ^ a) (Units.ext (by simpa using h _))

/-- The terms `r (1 / n!)` of a homomorphism `r : Multiplicative ℚ →* M` form a compatible system
of factorial roots. -/
@[simp]
theorem apply_inv_factorial_succ_pow (f : Multiplicative ℚ →* M) (n : ℕ) :
    f (ofAdd ((n + 1)! : ℚ)⁻¹) ^ (n + 1) = f (ofAdd (n ! : ℚ)⁻¹) := by
  rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, factorial_succ, cast_mul, mul_inv,
    ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast n.succ_ne_zero), one_mul]

section FactorialRoots

variable (y : ℕ → G) (hy : ∀ n, y (n + 1) ^ (n + 1) = y n)

include hy in
/-- Two descriptions `q = a / n! = b / m!` of the same rational number give the same power. -/
private theorem zpow_eq_zpow_of_mul_factorial_eq {q : ℚ} {n m : ℕ} {a b : ℤ}
    (ha : q * n ! = a) (hb : q * m ! = b) : y n ^ a = y m ^ b := by
  wlog hnm : n ≤ m generalizing n m a b
  · exact (this hb ha (le_of_not_ge hnm)).symm
  have hab : ((m ! / n ! : ℕ) : ℤ) * a = b := by
    have h0 : (n ! : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero n
    refine Int.cast_injective (α := ℚ) ?_
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div (factorial_dvd_factorial hnm) h0, ← ha,
      ← hb]
    field_simp
  rw [← TauCeti.pow_factorial_div_factorial_eq hy hnm, ← zpow_natCast, ← zpow_mul, hab]

/-- The homomorphism `Multiplicative ℚ →* G` attached to a compatible system `y` of factorial
roots, `y (n + 1) ^ (n + 1) = y n`: it sends `a / n!` to `y n ^ a`
(`MonoidHom.ofFactorialRoots_apply_of_mul_factorial_eq`). -/
noncomputable def ofFactorialRoots : Multiplicative ℚ →* G where
  toFun x := y x.toAdd.den ^ (exists_mul_factorial_eq x.toAdd le_rfl).choose
  map_one' := by
    rw [zpow_eq_zpow_of_mul_factorial_eq y hy (exists_mul_factorial_eq _ le_rfl).choose_spec
      (m := 0) (b := 0) (by simp), zpow_zero]
  map_mul' x z := by
    obtain ⟨a, ha⟩ := exists_mul_factorial_eq x.toAdd (le_add_right le_rfl :
      x.toAdd.den ≤ x.toAdd.den + z.toAdd.den)
    obtain ⟨b, hb⟩ := exists_mul_factorial_eq z.toAdd (le_add_left le_rfl :
      z.toAdd.den ≤ x.toAdd.den + z.toAdd.den)
    have hab : (x * z).toAdd * (x.toAdd.den + z.toAdd.den)! = ((a + b : ℤ) : ℚ) := by
      rw [toAdd_mul, add_mul, ha, hb, Int.cast_add]
    rw [zpow_eq_zpow_of_mul_factorial_eq y hy (exists_mul_factorial_eq _ le_rfl).choose_spec hab,
      zpow_eq_zpow_of_mul_factorial_eq y hy (exists_mul_factorial_eq _ le_rfl).choose_spec ha,
      zpow_eq_zpow_of_mul_factorial_eq y hy (exists_mul_factorial_eq _ le_rfl).choose_spec hb,
      zpow_add]

/-- `ofFactorialRoots y hy` sends `q = a / n!` to `y n ^ a`. -/
theorem ofFactorialRoots_apply_of_mul_factorial_eq {q : ℚ} {n : ℕ} {a : ℤ} (h : q * n ! = a) :
    ofFactorialRoots y hy (ofAdd q) = y n ^ a :=
  zpow_eq_zpow_of_mul_factorial_eq y hy (exists_mul_factorial_eq q le_rfl).choose_spec h

/-- `ofFactorialRoots y hy` sends `1 / n!` to `y n`. -/
@[simp]
theorem ofFactorialRoots_apply_inv_factorial (n : ℕ) :
    ofFactorialRoots y hy (ofAdd (n ! : ℚ)⁻¹) = y n := by
  rw [ofFactorialRoots_apply_of_mul_factorial_eq y hy (n := n) (a := 1)
    (by rw [Int.cast_one, inv_mul_cancel₀ (by exact_mod_cast factorial_ne_zero n)]), zpow_one]

/-- `ofFactorialRoots y hy` sends `ofAdd 1` to `y 0`. -/
@[simp]
theorem ofFactorialRoots_apply_ofAdd_one : ofFactorialRoots y hy (ofAdd 1) = y 0 := by
  simpa using ofFactorialRoots_apply_inv_factorial y hy 0

/-- Postcomposing `ofFactorialRoots y hy` with a homomorphism `k` gives the homomorphism of the
compatible system `n ↦ k (y n)`. -/
@[simp]
theorem comp_ofFactorialRoots {H : Type*} [Group H] (k : G →* H) :
    k.comp (ofFactorialRoots y hy) =
      ofFactorialRoots (fun n ↦ k (y n)) (fun n ↦ by rw [← map_pow, hy]) :=
  ext_rat_inv_factorial fun n ↦ by simp

end FactorialRoots

/-- In a commutative group, `ofFactorialRoots` sends the pointwise product of two compatible
systems to the product of their homomorphisms. -/
@[simp]
theorem ofFactorialRoots_mul {A : Type*} [CommGroup A] (y z : ℕ → A)
    (hy : ∀ n, y (n + 1) ^ (n + 1) = y n) (hz : ∀ n, z (n + 1) ^ (n + 1) = z n) :
    ofFactorialRoots (y * z) (fun n ↦ by rw [Pi.mul_apply, Pi.mul_apply, mul_pow, hy, hz]) =
      ofFactorialRoots y hy * ofFactorialRoots z hz :=
  ext_rat_inv_factorial fun n ↦ by simp

end MonoidHom

namespace TauCeti

open MonoidHom

variable (G) in
/-- Compatible systems of factorial roots `y (n + 1) ^ (n + 1) = y n` in a group `G` correspond to
homomorphisms `Multiplicative ℚ →* G`: the system `y` gives `ofFactorialRoots y`, and a
homomorphism `r` gives `n ↦ r (1 / n!)`. -/
noncomputable def factorialRootsEquiv :
    {y : ℕ → G // ∀ n, y (n + 1) ^ (n + 1) = y n} ≃ (Multiplicative ℚ →* G) where
  toFun y := ofFactorialRoots y.val y.property
  invFun f := ⟨fun n ↦ f (ofAdd (n ! : ℚ)⁻¹), apply_inv_factorial_succ_pow f⟩
  left_inv y := Subtype.ext <| funext <| ofFactorialRoots_apply_inv_factorial y.val y.property
  right_inv _ := ext_rat_inv_factorial fun n ↦ ofFactorialRoots_apply_inv_factorial _ _ n

@[simp]
theorem factorialRootsEquiv_apply (y : {y : ℕ → G // ∀ n, y (n + 1) ^ (n + 1) = y n}) :
    factorialRootsEquiv G y = ofFactorialRoots y.val y.property :=
  (rfl)

@[simp]
theorem factorialRootsEquiv_symm_apply_val (f : Multiplicative ℚ →* G) (n : ℕ) :
    ((factorialRootsEquiv G).symm f).val n = f (ofAdd (n ! : ℚ)⁻¹) :=
  (rfl)

/-- In an `ℕ`-rootable group every element `x` is the value at `ofAdd 1` of a homomorphism
`Multiplicative ℚ →* G`, namely `MonoidHom.ofFactorialRoots` of `factorialRoots x`. -/
theorem exists_monoidHom_rat_apply_ofAdd_one [RootableBy G ℕ] (x : G) :
    ∃ r : Multiplicative ℚ →* G, r (ofAdd 1) = x :=
  ⟨MonoidHom.ofFactorialRoots (factorialRoots x) (factorialRoots_succ_pow x), by simp⟩

/-- Every element of a group `G` is the value at `ofAdd 1` of a homomorphism
`Multiplicative ℚ →* G` if and only if every element of `G` has an `n`-th root for every
`n ≠ 0`. -/
theorem forall_exists_monoidHom_rat_apply_ofAdd_one_iff :
    (∀ x : G, ∃ r : Multiplicative ℚ →* G, r (ofAdd 1) = x) ↔
      ∀ n : ℕ, n ≠ 0 → Function.Surjective fun z : G ↦ z ^ n := by
  refine ⟨fun h n hn x ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨r, rfl⟩ := h x
    refine ⟨r (ofAdd (n : ℚ)⁻¹), ?_⟩
    dsimp only
    rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_inv_cancel₀ (by exact_mod_cast hn)]
  · let := rootableByOfPowLeftSurj G ℕ fun hn ↦ h _ hn
    exact exists_monoidHom_rat_apply_ofAdd_one

end TauCeti
