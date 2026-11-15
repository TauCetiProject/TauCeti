/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Groups with exponents in a ring

Let `A` be a (semi)ring. A group `G` with an exponentiation `G → A → G`, written `g ^ a`, is an
*`A`-group*, or *exponential group over `A`*, when

* (E1) `g ^ 1 = g`, `g ^ (a + b) = g ^ a * g ^ b` and `g ^ (a * b) = (g ^ a) ^ b`;
* (E2) exponentiation commutes with conjugation, `(g * h * g⁻¹) ^ a = g * h ^ a * g⁻¹`;
* (E3) `(g * h) ^ a = g ^ a * h ^ a` whenever `g` and `h` commute.

Axioms (E1) and (E2) are Lyndon's; (E3) was added by Myasnikov and Remeslennikov. The case of
interest is the polynomial ring `A = ℤ[t]`: Lyndon's free `ℤ[t]`-group `F^{ℤ[t]}` is the
`ℤ[t]`-completion of a free group `F`, and when `F` is nonabelian it contains every finitely
generated fully residually free group. In a `ℤ[t]`-group the laws give, for instance,
`g ^ (t + 1) = g ^ t * g` (`IsExponentialGroup.pow_add_one`) and `(g ^ t) ^ t = g ^ t ^ 2`
(`IsExponentialGroup.pow_sq`).

## Main definitions

* `TauCeti.IsExponentialGroup A G`: the exponentiation `Pow G A` makes the group `G` an `A`-group.
* `TauCeti.IsExponentialGroup.MultiplicativePow.instPow`: the exponentiation
  `ofAdd m ^ a = ofAdd (a • m)` on `Multiplicative M`, for scalars `A` acting on `M`. It is a
  scoped instance.

## Main results

* `TauCeti.IsExponentialGroup.pow_zero`, `one_pow`, `inv_pow`, `pow_neg`, `pow_natCast`,
  `pow_ofNat`, `pow_intCast`: the laws `g ^ 0 = 1`, `1 ^ a = 1`, `g⁻¹ ^ a = (g ^ a)⁻¹`,
  `g ^ (-a) = (g ^ a)⁻¹`, and the agreement of exponents `n : ℕ` and `n : ℤ`, cast to `A`, with
  the usual powers. Kharlampovich and Myasnikov list the first two among the axioms; they follow
  from (E1) and (E3).
* `Commute.exponentialPow_right`, `TauCeti.IsExponentialGroup.pow_mem_centralizer`: an element
  commuting with `h` commutes with every `h ^ a`, so centralizers are closed under
  exponentiation.
* Every group is a `ℤ`-group and an `ℕ`-group, with the usual powers.
* `TauCeti.IsExponentialGroup.MultiplicativePow.instIsExponentialGroup`: a module `M` over a
  commutative semiring `A` is an `A`-group, written multiplicatively.

## Implementation notes

`IsExponentialGroup A G` is a `Prop`-valued mixin on an exponentiation `Pow G A`, so that the
`ℕ`- and `ℤ`-group structures of a group are carried by its usual powers, and an `A`-group
structure is determined by the exponentiation. The conjugation law is stated in Mathlib's
convention (`conj_pow`); the sources write `(g⁻¹ * h * g) ^ a = g⁻¹ * h ^ a * g`, which is the
same law at `g⁻¹`.

The exponentiation on `Multiplicative M` by scalars is not a global instance: for `A = ℕ` or
`A = ℤ` it would compete with the usual powers of the group `Multiplicative M`, to which it is
only propositionally equal. It and the resulting `A`-group structure are scoped instances,
activated by `open scoped TauCeti.IsExponentialGroup.MultiplicativePow`. The module structure
makes `Multiplicative M` an `A`-group only for commutative `A`, since `(g ^ a) ^ b = g ^ (a * b)`
reads `b • a • m = (a * b) • m`.

## References

* A. G. Myasnikov, V. N. Remeslennikov, D. E. Serbin, *Regular free length functions on Lyndon's
  free `ℤ[t]`-group `F^{ℤ[t]}`*, §2.1, axioms (E1)–(E3).
* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I*, §1,
  Definition 6.
* R. C. Lyndon, *Groups with parametric exponents*, Trans. Amer. Math. Soc. 96 (1960).
* A. G. Myasnikov, V. N. Remeslennikov, *Exponential groups. II. Extensions of centralizers and
  tensor completion of CSA-groups*, Internat. J. Algebra Comput. 6 (1996).
-/

public section

namespace TauCeti

/-- A group `G` with an exponentiation `g ^ a` by the elements of a semiring `A` is an
*`A`-group* (an *exponential group* over `A`) if `g ^ 1 = g`, `g ^ (a + b) = g ^ a * g ^ b`,
`g ^ (a * b) = (g ^ a) ^ b`, exponentiation commutes with conjugation, and
`(g * h) ^ a = g ^ a * h ^ a` for commuting `g` and `h`. -/
class IsExponentialGroup (A G : Type*) [Semiring A] [Group G] [Pow G A] : Prop where
  /-- The exponent `1` acts trivially. -/
  protected pow_one (g : G) : g ^ (1 : A) = g
  /-- Exponentiation turns sums of exponents into products. -/
  protected pow_add (g : G) (a b : A) : g ^ (a + b) = g ^ a * g ^ b
  /-- Exponentiation turns products of exponents into iterated powers. -/
  protected pow_mul (g : G) (a b : A) : g ^ (a * b) = (g ^ a) ^ b
  /-- Exponentiation commutes with conjugation. -/
  protected conj_pow (g h : G) (a : A) : (g * h * g⁻¹) ^ a = g * h ^ a * g⁻¹
  /-- Exponentiation is multiplicative on commuting elements. -/
  protected mul_pow {g h : G} (hc : Commute g h) (a : A) : (g * h) ^ a = g ^ a * h ^ a

end TauCeti

namespace Commute

open TauCeti

variable {A G : Type*} [Semiring A] [Group G] [Pow G A] [IsExponentialGroup A G] {g h : G}

/-- An element commuting with `h` commutes with the powers of `h` in an `A`-group. -/
theorem exponentialPow_right (hc : Commute g h) (a : A) : Commute g (h ^ a) := by
  have key := IsExponentialGroup.conj_pow g h a
  rw [hc.mul_inv_cancel, eq_mul_inv_iff_mul_eq] at key
  exact (commute_iff_eq _ _).2 key.symm

/-- The powers of `g` in an `A`-group commute with every element commuting with `g`. -/
theorem exponentialPow_left (hc : Commute g h) (a : A) : Commute (g ^ a) h :=
  (hc.symm.exponentialPow_right a).symm

/-- Powers of commuting elements of an `A`-group commute. -/
theorem exponentialPow_exponentialPow (hc : Commute g h) (a b : A) : Commute (g ^ a) (h ^ b) :=
  (hc.exponentialPow_left a).exponentialPow_right b

end Commute

namespace TauCeti.IsExponentialGroup

attribute [simp] IsExponentialGroup.pow_one

section Semiring

variable {A G : Type*} [Semiring A] [Group G] [Pow G A] [IsExponentialGroup A G]

@[simp]
protected theorem pow_zero (g : G) : g ^ (0 : A) = 1 := by
  simpa using IsExponentialGroup.pow_add g (0 : A) 0

@[simp]
protected theorem one_pow (a : A) : (1 : G) ^ a = 1 := by
  simpa using IsExponentialGroup.mul_pow (Commute.one_left (1 : G)) a

theorem pow_add_one (g : G) (a : A) : g ^ (a + 1) = g ^ a * g := by
  rw [IsExponentialGroup.pow_add, IsExponentialGroup.pow_one]

theorem pow_one_add (g : G) (a : A) : g ^ (1 + a) = g * g ^ a := by
  rw [IsExponentialGroup.pow_add, IsExponentialGroup.pow_one]

/-- The square of an exponent acts as the exponent applied twice. -/
theorem pow_sq (g : G) (a : A) : g ^ a ^ 2 = (g ^ a) ^ a := by
  rw [sq, IsExponentialGroup.pow_mul]

/-- Exponents that are natural numbers act as the usual powers. -/
@[simp, norm_cast]
theorem pow_natCast (g : G) (n : ℕ) : g ^ (n : A) = g ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, pow_add_one, ih, pow_succ]

/-- Numeral exponents act as the usual powers. -/
@[simp]
theorem pow_ofNat (g : G) (n : ℕ) [n.AtLeastTwo] : g ^ (ofNat(n) : A) = g ^ OfNat.ofNat n :=
  pow_natCast g n

/-- The powers of one element commute. -/
theorem commute_pow_pow_self (g : G) (a b : A) : Commute (g ^ a) (g ^ b) :=
  (commute_iff_eq _ _).2 <| by
    rw [← IsExponentialGroup.pow_add, ← IsExponentialGroup.pow_add, add_comm]

/-- An element commutes with its powers. -/
theorem commute_self_pow (g : G) (a : A) : Commute g (g ^ a) := by
  simpa using commute_pow_pow_self g (1 : A) a

/-- Centralizers are closed under exponentiation. -/
theorem pow_mem_centralizer {S : Set G} {h : G} (hh : h ∈ Subgroup.centralizer S) (a : A) :
    h ^ a ∈ Subgroup.centralizer S :=
  Subgroup.mem_centralizer_iff.2 fun g hg =>
    (((commute_iff_eq g h).2 (Subgroup.mem_centralizer_iff.1 hh g hg)).exponentialPow_right a).eq

@[simp]
protected theorem inv_pow (g : G) (a : A) : g⁻¹ ^ a = (g ^ a)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by
    rw [← IsExponentialGroup.mul_pow (Commute.inv_left (Commute.refl g)), inv_mul_cancel,
      IsExponentialGroup.one_pow]

end Semiring

section CommSemiring

variable {A G : Type*} [CommSemiring A] [Group G] [Pow G A] [IsExponentialGroup A G]

/-- Over a commutative semiring, iterated powers may be taken in either order. -/
protected theorem pow_right_comm (g : G) (a b : A) : (g ^ a) ^ b = (g ^ b) ^ a := by
  rw [← IsExponentialGroup.pow_mul, ← IsExponentialGroup.pow_mul, mul_comm]

end CommSemiring

section Ring

variable {A G : Type*} [Ring A] [Group G] [Pow G A] [IsExponentialGroup A G]

@[simp]
protected theorem pow_neg (g : G) (a : A) : g ^ (-a) = (g ^ a)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by
    rw [← IsExponentialGroup.pow_add, neg_add_cancel, IsExponentialGroup.pow_zero]

protected theorem pow_sub (g : G) (a b : A) : g ^ (a - b) = g ^ a * (g ^ b)⁻¹ := by
  rw [sub_eq_add_neg, IsExponentialGroup.pow_add, IsExponentialGroup.pow_neg]

/-- Exponents that are integers act as the usual powers. -/
@[simp, norm_cast]
theorem pow_intCast (g : G) (n : ℤ) : g ^ (n : A) = g ^ n := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg <;> simp

end Ring

section Instances

variable (G : Type*) [Group G]

/-- Every group is a `ℤ`-group, with its integer powers. -/
instance : IsExponentialGroup ℤ G where
  pow_one := zpow_one
  pow_add := zpow_add
  pow_mul := zpow_mul
  conj_pow _ _ _ := conj_zpow
  mul_pow hc a := hc.mul_zpow a

/-- Every group is an `ℕ`-group, with its natural-number powers. -/
instance : IsExponentialGroup ℕ G where
  pow_one := pow_one
  pow_add := pow_add
  pow_mul := pow_mul
  conj_pow _ _ _ := conj_pow
  mul_pow hc a := hc.mul_pow a

end Instances

namespace MultiplicativePow

/-- The exponentiation `ofAdd m ^ a = ofAdd (a • m)` on `Multiplicative M`, by scalars `A` acting
on `M`. It is a scoped instance, activated by
`open scoped TauCeti.IsExponentialGroup.MultiplicativePow`: for `A = ℕ` and `A = ℤ` it would
compete with the usual powers of the group `Multiplicative M`. -/
scoped instance instPow {A M : Type*} [SMul A M] : Pow (Multiplicative M) A :=
  ⟨fun x a => .ofAdd (a • x.toAdd)⟩

end MultiplicativePow

end TauCeti.IsExponentialGroup

namespace Multiplicative

open scoped TauCeti.IsExponentialGroup.MultiplicativePow

variable {A M : Type*} [SMul A M]

theorem multiplicativePow_def (x : Multiplicative M) (a : A) : x ^ a = .ofAdd (a • x.toAdd) := by
  rfl

@[simp]
theorem toAdd_multiplicativePow (x : Multiplicative M) (a : A) : (x ^ a).toAdd = a • x.toAdd := by
  rfl

end Multiplicative

namespace TauCeti.IsExponentialGroup.MultiplicativePow

open Multiplicative

variable {A M : Type*}

theorem ofAdd_multiplicativePow [SMul A M] (m : M) (a : A) :
    Multiplicative.ofAdd m ^ a = .ofAdd (a • m) := by
  rfl

/-- A module over a commutative semiring `A` is an `A`-group, written multiplicatively, with
exponentiation `ofAdd m ^ a = ofAdd (a • m)`. -/
scoped instance instIsExponentialGroup [CommSemiring A] [AddCommGroup M] [Module A M] :
    IsExponentialGroup A (Multiplicative M) where
  pow_one x := by simp [multiplicativePow_def]
  pow_add x a b := by simp [multiplicativePow_def, add_smul]
  pow_mul x a b := by
    rw [multiplicativePow_def, multiplicativePow_def, toAdd_multiplicativePow, smul_smul, mul_comm]
  conj_pow g h a := by rw [mul_inv_cancel_comm, mul_inv_cancel_comm]
  mul_pow _ a := by simp [multiplicativePow_def, smul_add]

end TauCeti.IsExponentialGroup.MultiplicativePow
