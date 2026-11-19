/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Reflection
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix

/-!
# The order of a product of two simple reflections

The product of the reflections in two roots `αᵢ`, `αⱼ` changes every weight by an element of the
span of the two roots. When `3 ≠ 0` and `4 ≠ 0`, its order is read off the Cartan product
`c = ⟨αᵢ, αⱼ^∨⟩⟨αⱼ, αᵢ^∨⟩`: the values `1`, `2`, `3` give the orders `3`, `4`, `6`. This file proves
the corresponding upper bounds over an arbitrary commutative ring and these exact orders when `3`
and `4` are nonzero. It then proves — for two simple roots of a base of a finite crystallographic
pairing over a characteristic-zero domain, where `c = 0` is the remaining possibility and gives the
order `2` — that the entries of
`TauCeti.coxeterMatrixOfBase` really are the orders they are named for, so that the braid relations
of the Coxeter presentation of a Weyl group hold in the Weyl group.

The iterates of the product are supplied by Mathlib's
`Module.reflection_mul_reflection_pow_apply` and `Module.reflection_mul_reflection_pow_apply_self`,
which express `(r₁r₂)ⁿ` over an arbitrary commutative ring through the Chebyshev `S`-polynomials
(`Polynomial.Chebyshev.S`) evaluated at `t = c - 2`;
`RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_smul` and
`RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_smul_root` are those formulas for a product of
two reflections of a root pairing, read as elements of the Weyl group. Substituting `c = 1, 2, 3`,
that is `t = -1, 0, 1`, makes the two Chebyshev coefficients of the general formula vanish at the
exponents `3`, `4`, `6`, which gives `g³ = 1`, `g⁴ = 1`, `g⁶ = 1`, the root-pairing case of
`Module.reflection_mul_reflection_pow_three_eq_one` and its siblings; the remaining value `c = 0` is
the orthogonal case, already settled in `TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix`, where the
two reflections commute, and where the order is pinned to `2` only for two distinct simple roots of
a base.

That the order is no smaller is `Module.orderOf_reflection_mul_reflection_eq_three` and its
siblings, read in the Weyl group: the `αᵢ^∨`-coordinate of `gⁿ • αᵢ` is again a Chebyshev expression
in `c`, and for the relevant powers that expression avoids the value `⟨αᵢ, αᵢ^∨⟩ = 2`.

The iterate formulas and upper bounds are stated over an arbitrary commutative ring. The exact-order
results add `3 ≠ 0` and `4 ≠ 0`, but still concern an arbitrary pair of roots of an arbitrary root
pairing, the Cartan product entering only as a hypothesis on `RootPairing.pairing`; no finiteness,
crystallographic or reducedness assumption is used there. The last section specialises to a pair of
simple roots of a base, where `TauCeti.cartanMatrix_mul_cartanMatrix_mem_of_ne` confines the Cartan
product to `{0, 1, 2, 3}` and the case analysis closes.

## Main results

* `RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_smul` and
  `RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_smul_root`: the iterates of a product of two
  reflections, acting on a weight and on the first of the two roots.
* `RootPairing.weylGroup.pow_three_ofIdx_mul_ofIdx_eq_one`,
  `RootPairing.weylGroup.pow_four_ofIdx_mul_ofIdx_eq_one`,
  `RootPairing.weylGroup.pow_six_ofIdx_mul_ofIdx_eq_one`: the braid relations at Cartan
  product `1`, `2`, `3`, and
  `RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_three`,
  `RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_four`,
  `RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_six`: the matching exact orders when `3` and
  `4` are nonzero.
* `RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase`: **the entries of
  the Coxeter matrix of a base are the orders of the products of the corresponding simple
  reflections.**
* `RootPairing.weylGroup.pow_coxeterMatrixOfBase_ofIdx_mul_ofIdx_eq_one`: the braid
  relations of that Coxeter matrix hold in the Weyl group.

## References

The rank-two computation is Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6, Ch. VI, §1.3,
and Humphreys, *Introduction to Lie Algebras and Representation Theory*, §9.
-/

public section

namespace RootPairing.weylGroup

open TauCeti

open Set Polynomial.Chebyshev

universe u v w x

section

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (i j : ι)

/-! ## The rank-two computation -/

/-- The action of an iterate of the product of the two reflections is the action of the
corresponding iterate of the product of the two linear reflections. -/
private lemma pow_ofIdx_mul_ofIdx_smul_eq (n : ℕ) (x : M) :
    ((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) ^ n) • x =
      ((P.reflection i * P.reflection j) ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, pow_succ', _root_.mul_apply_eq_comp, mul_smul]
    simp [_root_.RootPairing.reflection_apply]

/-- The Cartan product of the two roots, in the form in which it enters the linear reflections
`Module.reflection (P.coroot_root_two i)` and `Module.reflection (P.coroot_root_two j)`. -/
private lemma coroot_root_mul_coroot_root :
    P.toLinearMap.flip (P.coroot i) (P.root j) * P.toLinearMap.flip (P.coroot j) (P.root i) =
      P.pairing i j * P.pairing j i := by
  rw [P.coroot_root_eq_pairing, P.coroot_root_eq_pairing, mul_comm]

/-- **The iterates of a product of two reflections.** This is Mathlib's
`Module.reflection_mul_reflection_pow_apply` for the reflections in two roots `αᵢ`, `αⱼ` of a root
pairing, read in the Weyl group; its Chebyshev polynomials are evaluated at the Cartan product
shifted by `2`, that is at `t = ⟨αᵢ, αⱼ^∨⟩⟨αⱼ, αᵢ^∨⟩ - 2`. -/
theorem pow_ofIdx_mul_ofIdx_smul (n : ℕ) (x : M)
    (t : R := P.pairing i j * P.pairing j i - 2)
    (ht : t = P.pairing i j * P.pairing j i - 2 := by rfl) :
    ((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) ^ n) • x =
      x +
        ((S R ((n - 2) / 2)).eval t * ((S R ((n - 1) / 2)).eval t + (S R ((n - 3) / 2)).eval t)) •
          ((P.pairing i j * P.coroot' i x - P.coroot' j x) • P.root j - P.coroot' i x • P.root i) +
        ((S R ((n - 1) / 2)).eval t * ((S R (n / 2)).eval t + (S R ((n - 2) / 2)).eval t)) •
          ((P.pairing j i * P.coroot' j x - P.coroot' i x) • P.root i -
            P.coroot' j x • P.root j) := by
  rw [RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_smul_eq]
  exact Module.reflection_mul_reflection_pow_apply (P.coroot_root_two i) (P.coroot_root_two j) n x t
    (by rw [ht, RootPairing.weylGroup.coroot_root_mul_coroot_root])

/-- **The iterates of a product of two reflections on the first of the two roots.** This is
Mathlib's `Module.reflection_mul_reflection_pow_apply_self` read in the Weyl group; it is the case
`x = αᵢ` of `RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_smul`, in a form where the two
coefficients are single Chebyshev values. -/
theorem pow_ofIdx_mul_ofIdx_smul_root (n : ℕ)
    (t : R := P.pairing i j * P.pairing j i - 2)
    (ht : t = P.pairing i j * P.pairing j i - 2 := by rfl) :
    ((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) ^ n) • P.root i =
      ((S R n).eval t + (S R (n - 1)).eval t) • P.root i +
        ((S R (n - 1)).eval t * -P.pairing i j) • P.root j := by
  rw [RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_smul_eq]
  exact Module.reflection_mul_reflection_pow_apply_self (P.coroot_root_two i)
    (P.coroot_root_two j) n t
    (by rw [ht, RootPairing.weylGroup.coroot_root_mul_coroot_root])

/-! ## The braid relations -/

/-- A power of the product of the two reflections is trivial in the Weyl group exactly when the
same power of the product of the two linear reflections is. -/
lemma pow_ofIdx_mul_ofIdx_eq_one_iff (n : ℕ) :
    (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ n = 1 ↔
      (P.reflection i * P.reflection j) ^ n = 1 := by
  refine ⟨fun h ↦ LinearEquiv.ext fun x ↦ ?_, fun h ↦
    RootPairing.weylGroup.eq_one_of_smul_eq_self fun x ↦ ?_⟩
  · rw [← RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_smul_eq, h, one_smul]
    simp
  · rw [RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_smul_eq, h]
    simp

/-- **The braid relation at Cartan product `1`**: the product of the two reflections has order
dividing `3`, the `A₂` configuration. -/
@[simp, grind =]
theorem pow_three_ofIdx_mul_ofIdx_eq_one
    (h : P.pairing i j * P.pairing j i = 1) :
    (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 3 = 1 :=
  (RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_eq_one_iff P i j 3).mpr
    (Module.reflection_mul_reflection_pow_three_eq_one (P.coroot_root_two i) (P.coroot_root_two j)
      ((RootPairing.weylGroup.coroot_root_mul_coroot_root P i j).trans h))

/-- **The braid relation at Cartan product `2`**: the product of the two reflections has order
dividing `4`, the `B₂` configuration. -/
@[simp, grind =]
theorem pow_four_ofIdx_mul_ofIdx_eq_one
    (h : P.pairing i j * P.pairing j i = 2) :
    (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 4 = 1 :=
  (RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_eq_one_iff P i j 4).mpr
    (Module.reflection_mul_reflection_pow_four_eq_one (P.coroot_root_two i) (P.coroot_root_two j)
      ((RootPairing.weylGroup.coroot_root_mul_coroot_root P i j).trans h))

/-- **The braid relation at Cartan product `3`**: the product of the two reflections has order
dividing `6`, the `G₂` configuration. -/
@[simp, grind =]
theorem pow_six_ofIdx_mul_ofIdx_eq_one
    (h : P.pairing i j * P.pairing j i = 3) :
    (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 6 = 1 :=
  (RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_eq_one_iff P i j 6).mpr
    (Module.reflection_mul_reflection_pow_six_eq_one (P.coroot_root_two i) (P.coroot_root_two j)
      ((RootPairing.weylGroup.coroot_root_mul_coroot_root P i j).trans h))

/-! ## The order is no smaller

The exact orders are those of the two linear reflections, computed in
`Module.orderOf_reflection_mul_reflection_eq_three` and its siblings from the `αᵢ^∨`-coordinate of
`gⁿ • αᵢ`, which avoids the value `⟨αᵢ, αᵢ^∨⟩ = 2`. -/

/-- The product of the two reflections has the same order in the Weyl group as the product of the
two linear reflections. -/
lemma orderOf_ofIdx_mul_ofIdx :
    orderOf (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) = orderOf (P.reflection i * P.reflection j) :=
  orderOf_eq_orderOf_iff.mpr (RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_eq_one_iff P i j)

/-- **At Cartan product `1` the product of the two reflections has order exactly `3`**, provided
`3 ≠ 0`. -/
@[simp, grind =]
theorem orderOf_ofIdx_mul_ofIdx_eq_three
    (h : P.pairing i j * P.pairing j i = 1) (h3 : (3 : R) ≠ 0) :
    orderOf (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) = 3 := by
  rw [RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx]
  exact Module.orderOf_reflection_mul_reflection_eq_three (hf := P.coroot_root_two i)
    (hg := P.coroot_root_two j)
    ((RootPairing.weylGroup.coroot_root_mul_coroot_root P i j).trans h) h3

/-- **At Cartan product `2` the product of the two reflections has order exactly `4`**, provided
`4 ≠ 0`. -/
@[simp, grind =]
theorem orderOf_ofIdx_mul_ofIdx_eq_four
    (h : P.pairing i j * P.pairing j i = 2) (h4 : (4 : R) ≠ 0) :
    orderOf (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) = 4 := by
  rw [RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx]
  exact Module.orderOf_reflection_mul_reflection_eq_four (hf := P.coroot_root_two i)
    (hg := P.coroot_root_two j)
    ((RootPairing.weylGroup.coroot_root_mul_coroot_root P i j).trans h) h4

/-- **At Cartan product `3` the product of the two reflections has order exactly `6`**, provided
`3 ≠ 0` and `4 ≠ 0`. -/
@[simp, grind =]
theorem orderOf_ofIdx_mul_ofIdx_eq_six
    (h : P.pairing i j * P.pairing j i = 3) (h3 : (3 : R) ≠ 0) (h4 : (4 : R) ≠ 0) :
    orderOf (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) = 6 := by
  rw [RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx]
  exact Module.orderOf_reflection_mul_reflection_eq_six (hf := P.coroot_root_two i)
    (hg := P.coroot_root_two j)
    ((RootPairing.weylGroup.coroot_root_mul_coroot_root P i j).trans h) h3 h4

/-! ## The entries of the Coxeter matrix of a base -/

section Base

variable [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic] (b : P.Base)

omit [Finite ι] [CharZero R] [IsDomain R] in
private lemma pairing_mul_pairing_eq_cast (k l : b.support) :
    P.pairing k l * P.pairing l k =
      ((b.cartanMatrix k l * b.cartanMatrix l k : ℤ) : R) := by
  have hk : ∀ m n : b.support, ((b.cartanMatrix m n : ℤ) : R) = P.pairing m n := fun m n ↦ by
    simpa using b.algebraMap_cartanMatrixIn_apply (S := ℤ) m n
  push_cast
  rw [hk, hk]

/-- **The entries of the Coxeter matrix of a base are the orders of the products of the
corresponding simple reflections.** On the diagonal both sides are `1`, a simple reflection being
an involution; off the diagonal the four Cartan products `0`, `1`, `2`, `3` give the four dihedral
orders `2`, `3`, `4`, `6`. -/
@[simp, grind =]
theorem orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase
    (k l : b.support) :
    orderOf (_root_.RootPairing.weylGroup.ofIdx P (k : ι) *
      _root_.RootPairing.weylGroup.ofIdx P (l : ι)) = coxeterMatrixOfBase P b k l := by
  rcases eq_or_ne k l with rfl | hkl
  · rw [RootPairing.weylGroup.ofIdx_mul_self, orderOf_one]
    simp
  have hmem := cartanMatrix_mul_cartanMatrix_mem_of_ne P b hkl
  have hcast := RootPairing.weylGroup.pairing_mul_pairing_eq_cast P b k l
  simp only [mem_insert_iff, mem_singleton_iff] at hmem
  rcases hmem with hc | hc | hc | hc <;> rw [hc] at hcast <;> push_cast at hcast
  · have h₂ : coxeterMatrixOfBase P b k l = 2 := by
      rw [coxeterMatrixOfBase_apply, hc, coxeterOrder_zero]
    rw [h₂]
    exact RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_two_of_coxeterMatrixOfBase_eq_two P b h₂
  · rw [coxeterMatrixOfBase_apply, hc, coxeterOrder_one]
    exact RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_three P _ _ hcast (by norm_num)
  · rw [coxeterMatrixOfBase_apply, hc, coxeterOrder_two]
    exact RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_four P _ _ hcast (by norm_num)
  · rw [coxeterMatrixOfBase_apply, hc, coxeterOrder_three]
    exact RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_six P _ _ hcast (by norm_num)
      (by norm_num)

/-- **The braid relations of the Coxeter matrix of a base hold in the Weyl group.** This is the
relation half of the Coxeter presentation of the Weyl group. It is not a `simp` lemma: its
left-hand side is not in simp normal form, because the exponent `coxeterMatrixOfBase P b k l` is
itself rewritten by `TauCeti.coxeterMatrixOfBase_apply`. -/
@[grind =]
theorem pow_coxeterMatrixOfBase_ofIdx_mul_ofIdx_eq_one
    (k l : b.support) :
    (_root_.RootPairing.weylGroup.ofIdx P (k : ι) *
      _root_.RootPairing.weylGroup.ofIdx P (l : ι)) ^ coxeterMatrixOfBase P b k l = 1 := by
  rw [← RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase P b k l,
    pow_orderOf_eq_one]

end Base

end

end RootPairing.weylGroup
