/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.Nilpotent.Defs

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

The supporting iterated-commutator expansion, valid over any commutative ring, is
`ad_pow_apply`: the binomial theorem for the commuting pair `(mulLeft, mulRight)`, with the sign
absorbed into `(-a) ^ (n - m)` rather than carried separately.

## Main statements

* `TauCeti.LieAlgebra.ad_pow_eq_sum` and `TauCeti.LieAlgebra.ad_pow_apply`: the
  iterated-commutator expansion of `ad R A a ^ n`, at operator level and evaluated.
* `TauCeti.LieAlgebra.ad_pow_expChar_pow` and `TauCeti.LieAlgebra.ad_pow_expChar`: the Frobenius
  commutator identity.
* `TauCeti.LieAlgebra.ad_eq_zero_iff_mem_center` and
  `TauCeti.LieAlgebra.ad_pow_expChar_pow_eq_zero_iff`: `ad R A a` vanishes exactly on the centre,
  and its `p ^ n`-th power vanishes exactly when `a ^ p ^ n` is central.
* `TauCeti.LieAlgebra.isNilpotent_ad_iff_exists_pow_expChar_pow_mem_center`: in characteristic
  `p`, adjoint nilpotence is centrality of a Frobenius power.

## References

This is the "Frobenius commutator identity" milestone of Layer 6 in
`TauCetiRoadmap/RepresentationTheory/AdoIwasawa/README.md`, together with the associative-algebra
form of that layer's adjoint-nilpotent specialization.

* G. Hochschild, *An Addition to Ado's Theorem*, Proc. Amer. Math. Soc. **17** (1966), 531--533.
* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter V.
-/

public section

namespace TauCeti.LieAlgebra

open Finset

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The applied form of Mathlib's `LieAlgebra.ad_eq_lmul_left_sub_lmul_right`, which is stated as
an equality of functions. -/
private theorem ad_eq_mulLeft_sub_mulRight (a : A) :
    LieAlgebra.ad R A a = LinearMap.mulLeft R a - LinearMap.mulRight R a := by
  have h := congrFun (LieAlgebra.ad_eq_lmul_left_sub_lmul_right (R := R) A) a
  simpa using h

/-- Right multiplication by `-a` is the negative of right multiplication by `a`.  Absorbing the
sign of the binomial expansion this way keeps `ad_pow_apply` free of a separate `(-1) ^ k`. -/
private theorem mulRight_neg (a : A) :
    LinearMap.mulRight R (-a) = -LinearMap.mulRight R a := by
  ext b
  simp

/-- **The iterated-commutator expansion, at operator level.**  Left and right multiplication by
`a` commute by associativity, so the `n`-fold commutator with `a` is their binomial expansion.
The sign that usually accompanies such an expansion is absorbed into `(-a) ^ (n - m)`. -/
theorem ad_pow_eq_sum (a : A) (n : ℕ) :
    LieAlgebra.ad R A a ^ n =
      ∑ m ∈ range (n + 1),
        n.choose m • (LinearMap.mulLeft R (a ^ m) * LinearMap.mulRight R ((-a) ^ (n - m))) := by
  have hcomm : Commute (LinearMap.mulLeft R a) (LinearMap.mulRight R (-a)) :=
    LinearMap.commute_mulLeft_right a (-a)
  rw [ad_eq_mulLeft_sub_mulRight, sub_eq_add_neg, ← mulRight_neg, hcomm.add_pow n]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [LinearMap.pow_mulLeft, LinearMap.pow_mulRight, nsmul_eq_mul]
  exact (Nat.cast_commute (n.choose m) _).eq.symm

/-- **The iterated-commutator expansion, evaluated.**  This is `ad_pow_eq_sum` applied to an
element: the `n`-fold commutator of `a` with `b` is the binomial sum of the products
`a ^ m * b * (-a) ^ (n - m)`. -/
theorem ad_pow_apply (a b : A) (n : ℕ) :
    (LieAlgebra.ad R A a ^ n) b =
      ∑ m ∈ range (n + 1), n.choose m • (a ^ m * b * (-a) ^ (n - m)) := by
  rw [ad_pow_eq_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  simp only [LinearMap.smul_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, mul_assoc]

/-- **The Frobenius commutator identity.**  In exponential characteristic `p`, taking the
`p ^ n`-th power in the algebra `A` and iterating the commutator `p ^ n` times in
`Module.End R A` give the same endomorphism. -/
theorem ad_pow_expChar_pow (p : ℕ) [ExpChar A p] (a : A) (n : ℕ) :
    LieAlgebra.ad R A (a ^ p ^ n) = LieAlgebra.ad R A a ^ p ^ n := by
  have : ExpChar (Module.End R A) p :=
    expChar_of_injective_ringHom
      (f := (Algebra.lmul R A : A →ₐ[R] Module.End R A).toRingHom) Algebra.lmul_injective p
  rw [ad_eq_mulLeft_sub_mulRight, ad_eq_mulLeft_sub_mulRight,
    sub_pow_expChar_pow_of_commute p n (LinearMap.commute_mulLeft_right a a),
    LinearMap.pow_mulLeft, LinearMap.pow_mulRight]

/-- The Frobenius commutator identity at `n = 1`. -/
theorem ad_pow_expChar (p : ℕ) [ExpChar A p] (a : A) :
    LieAlgebra.ad R A (a ^ p) = LieAlgebra.ad R A a ^ p := by
  simpa using ad_pow_expChar_pow (R := R) p a 1

/-- Iterating the commutator with `a` exactly `p ^ n` times collapses to a single commutator with
`a ^ p ^ n`.  This is the concrete reading of `ad_pow_expChar_pow`, and the reason the expansion
`ad_pow_apply` degenerates in characteristic `p`. -/
theorem ad_pow_expChar_pow_apply (p : ℕ) [ExpChar A p] (a b : A) (n : ℕ) :
    (LieAlgebra.ad R A a ^ p ^ n) b = a ^ p ^ n * b - b * a ^ p ^ n := by
  rw [← ad_pow_expChar_pow p a n]
  simp [LieAlgebra.ad_apply, Ring.lie_def]

/-- The adjoint action of `a` vanishes exactly when `a` is central. -/
theorem ad_eq_zero_iff_mem_center (a : A) :
    LieAlgebra.ad R A a = 0 ↔ a ∈ Subalgebra.center R A := by
  rw [LinearMap.ext_iff, Subalgebra.mem_center_iff]
  refine forall_congr' fun b ↦ ?_
  rw [LieAlgebra.ad_apply, Ring.lie_def, LinearMap.zero_apply, sub_eq_zero, eq_comm]

/-- **The quantitative form of the Frobenius commutator identity.**  The `p ^ n`-fold commutator
with `a` vanishes exactly when the Frobenius power `a ^ p ^ n` is central.  Both nilpotence
statements below are this equivalence with the exponent quantified. -/
theorem ad_pow_expChar_pow_eq_zero_iff (p : ℕ) [ExpChar A p] (a : A) (n : ℕ) :
    LieAlgebra.ad R A a ^ p ^ n = 0 ↔ a ^ p ^ n ∈ Subalgebra.center R A := by
  rw [← ad_pow_expChar_pow p a n, ad_eq_zero_iff_mem_center]

/-- If some Frobenius power of `a` is central, then `ad R A a` is nilpotent: its `p ^ n`-th power
is the adjoint action of that central element. -/
theorem isNilpotent_ad_of_pow_expChar_pow_mem_center (p : ℕ) [ExpChar A p] {a : A} {n : ℕ}
    (h : a ^ p ^ n ∈ Subalgebra.center R A) : IsNilpotent (LieAlgebra.ad R A a) :=
  ⟨p ^ n, (ad_pow_expChar_pow_eq_zero_iff p a n).mpr h⟩

/-- If `ad R A a` is nilpotent and `p` is a genuine prime characteristic, then some Frobenius
power of `a` is central: raise `p` to a power past the nilpotency index and use the Frobenius
commutator identity. -/
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
