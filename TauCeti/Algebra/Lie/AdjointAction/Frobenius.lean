/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Nilpotent.Defs
public import TauCeti.Algebra.Lie.AdjointAction.Basic

/-!
# The adjoint action of an associative algebra and the Frobenius

Let `A` be an associative `R`-algebra, bracketed by its ring commutator, and let
`ad R A a : Module.End R A` be the inner derivation `b ↦ ⁅a, b⁆`.  Two powers are in play and
they must not be confused: `a ^ n` is a power in the ring `A`, while `ad R A a ^ n` is a power in
the endomorphism ring `Module.End R A`, that is, the `n`-fold iterated commutator with `a`.

The main theorem of this file is that the two agree along the Frobenius: in exponential
characteristic `p`,

`ad R A (a ^ p ^ n) = ad R A a ^ p ^ n`.

The reason is that `ad R A a` is the difference of the commuting endomorphisms
`LinearMap.mulLeft R a` and `LinearMap.mulRight R a`, so the Frobenius of `Module.End R A` is
additive on it, and each of the two factors is a multiplication operator by a power of `a`.  The
identity is characteristic-free in the exponential sense: for `p = 1` it is a tautology, and its
content is the prime case.

Two consequences follow at once.  Iterating the commutator `p ^ n` times collapses to a single
commutator with `a ^ p ^ n` (`ad_pow_expChar_pow_apply`), and, when `p` is a genuine prime,
`ad R A a` is nilpotent exactly when some Frobenius power `a ^ p ^ n` is central
(`isNilpotent_ad_iff_exists_pow_expChar_pow_mem_center`).  The forward direction of that
equivalence is the passage from adjoint nilpotence to a central `p`-th power that the
positive-characteristic half of Ado--Iwasawa runs on.

The characteristic-free iterated-commutator expansion that this identity collapses,
`ad_pow_apply`, is in `TauCeti.Algebra.Lie.AdjointAction.Basic`.

## Main statements

* `TauCeti.LieAlgebra.ad_pow_expChar_pow`: the Frobenius commutator identity.
* `TauCeti.LieAlgebra.ad_pow_expChar_pow_eq_zero_iff`: the `p ^ n`-th power of `ad R A a` vanishes
  exactly when `a ^ p ^ n` is central.
* `TauCeti.LieAlgebra.isNilpotent_ad_iff_exists_pow_expChar_pow_mem_center`: in characteristic
  `p`, adjoint nilpotence is centrality of a Frobenius power.

## References

The formal source is `Mathlib/FieldTheory/JacobsonNoether.lean`, whose
`JacobsonNoether.exist_pow_eq_zero_of_le` carries out this Frobenius calculation inline, for a
division algebra purely inseparable over its centre and phrased with `Function.iterate`, from the
same four ingredients used here: `sub_pow_expChar_pow_of_commute`,
`LinearMap.commute_mulLeft_right`, `LinearMap.pow_mulLeft` and `LinearMap.pow_mulRight`.  This file
generalizes that calculation to an arbitrary associative algebra and states it as a theorem about
powers in `Module.End R A`.

* G. Hochschild, *An Addition to Ado's Theorem*, Proc. Amer. Math. Soc. **17** (1966), 531--533.
* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter V.
-/

public section

namespace TauCeti.LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- **The Frobenius commutator identity.**  In exponential characteristic `p`, taking the
`p ^ n`-th power in the algebra `A` and iterating the commutator `p ^ n` times in
`Module.End R A` give the same endomorphism. -/
@[simp]
theorem ad_pow_expChar_pow (p : ℕ) [ExpChar A p] (a : A) (n : ℕ) :
    LieAlgebra.ad R A (a ^ p ^ n) = LieAlgebra.ad R A a ^ p ^ n := by
  have : ExpChar (Module.End R A) p :=
    expChar_of_injective_ringHom
      (f := (Algebra.lmul R A : A →ₐ[R] Module.End R A).toRingHom) Algebra.lmul_injective p
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right, Pi.sub_apply, Pi.sub_apply,
    sub_pow_expChar_pow_of_commute p n (LinearMap.commute_mulLeft_right a a),
    LinearMap.pow_mulLeft, LinearMap.pow_mulRight]

/-- Iterating the commutator with `a` exactly `p ^ n` times collapses to a single commutator with
`a ^ p ^ n`.  This is the concrete reading of `ad_pow_expChar_pow`, and the reason the expansion
`ad_pow_apply` degenerates in characteristic `p`. -/
@[simp]
theorem ad_pow_expChar_pow_apply (p : ℕ) [ExpChar A p] (a b : A) (n : ℕ) :
    (LieAlgebra.ad R A a ^ p ^ n) b = a ^ p ^ n * b - b * a ^ p ^ n := by
  rw [← ad_pow_expChar_pow p a n, LieAlgebra.ad_apply, Ring.lie_def]

/-- **The quantitative form of the Frobenius commutator identity.**  The `p ^ n`-fold commutator
with `a` vanishes exactly when the Frobenius power `a ^ p ^ n` is central.  Both nilpotence
statements below are this equivalence with the exponent quantified. -/
@[simp]
theorem ad_pow_expChar_pow_eq_zero_iff (p : ℕ) [ExpChar A p] (a : A) (n : ℕ) :
    LieAlgebra.ad R A a ^ p ^ n = 0 ↔ a ^ p ^ n ∈ Subalgebra.center R A := by
  rw [← ad_pow_expChar_pow p a n, ad_eq_zero_iff_mem_center]

/-- If some Frobenius power `a ^ p ^ n` is central, then `ad R A a` is nilpotent. -/
theorem isNilpotent_ad_of_pow_expChar_pow_mem_center (p : ℕ) [ExpChar A p] {a : A} {n : ℕ}
    (h : a ^ p ^ n ∈ Subalgebra.center R A) : IsNilpotent (LieAlgebra.ad R A a) :=
  ⟨p ^ n, (ad_pow_expChar_pow_eq_zero_iff p a n).mpr h⟩

/-- If `ad R A a` is nilpotent and `p` is a genuine prime characteristic, then some Frobenius
power `a ^ p ^ n` is central. -/
theorem exists_pow_expChar_pow_mem_center_of_isNilpotent_ad (p : ℕ) [ExpChar A p] (hp : p ≠ 1)
    {a : A} (h : IsNilpotent (LieAlgebra.ad R A a)) :
    ∃ n : ℕ, a ^ p ^ n ∈ Subalgebra.center R A := by
  obtain ⟨k, hk⟩ := h
  have hpos := expChar_pos A p
  have hp1 : 1 < p := by omega
  refine ⟨k, (ad_pow_expChar_pow_eq_zero_iff p a k).mp ?_⟩
  rw [← Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_pow_self hp1)), pow_add, hk, mul_zero]

/-- **Adjoint nilpotence is centrality of a Frobenius power.**  Over an algebra of prime
characteristic `p`, the inner derivation attached to `a` is nilpotent exactly when one of the
elements `a ^ p ^ n` is central.  The forward direction is the step that, inside a universal
enveloping algebra, produces the central `p`-polynomial attached to an `ad`-nilpotent element. -/
theorem isNilpotent_ad_iff_exists_pow_expChar_pow_mem_center (p : ℕ) [ExpChar A p] (hp : p ≠ 1)
    (a : A) :
    IsNilpotent (LieAlgebra.ad R A a) ↔ ∃ n : ℕ, a ^ p ^ n ∈ Subalgebra.center R A :=
  ⟨exists_pow_expChar_pow_mem_center_of_isNilpotent_ad p hp,
    fun ⟨_, h⟩ ↦ isNilpotent_ad_of_pow_expChar_pow_mem_center p h⟩

end TauCeti.LieAlgebra
