/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.RingTheory.Nilpotent.BaseChangeAction
import TauCeti.RingTheory.Nilpotent.RootString.Basic

/-!
# Doubly-laced Chevalley commutator relations for enveloping-algebra exponentials

Let `L` be a Lie algebra over a commutative ring `K`, `ρ` a ring homomorphism from `U_K(L)` into a
`ℚ`-algebra `A`, and `M` an additive subgroup of an `A`-module `V` preserved by the divided powers
of the relevant root-vector images. Over any commutative ring `R`, `TauCeti.baseChangeExp` and
`TauCeti.baseChangeExpHom` attach to each nilpotent `ρ(ι K e)` an integral divided-power
exponential and a one-parameter subgroup `Multiplicative R →* (R ⊗[ℤ] M ≃ₗ[R] R ⊗[ℤ] M)`.

This file transports `TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul` and
`TauCeti.commutatorElement_baseChangeExpHom_of_commutator_eq_two_nsmul` to `U_K(L)` with integer
structure constants absorbed into the parameters, proving Steinberg's doubly-laced
element-commutator identities in the normalization `⁅g, h⁆ = g * h * g⁻¹ * h⁻¹` for both root
orders:
* `{α + β, 2α + β}`: `⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(d t² u)` under `⁅x, y⁆ = c • z`,
  `⁅x, ⁅x, y⁆⁆ = (2 * d) • w`, and `⁅x, w⁆ = ⁅y, z⁆ = 0` (commutation of `ρ(ι K y)` with
  `d • ρ(ι K w)` follows in `A` via `Commute.of_commutator_eq_of_commutator_eq_smul_left`);
* `{α + β, α + 2β}`: `⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(-d t u²)` under `⁅x, y⁆ = c • z`,
  `⁅y, ⁅y, x⁆⁆ = (2 * d) • w`, and `⁅y, w⁆ = ⁅x, z⁆ = 0`, deduced from the `{α + β, 2α + β}`
  relation on `(y, x, z, w)` by inverting the commutator and commuting the two output factors via
  `Commute.of_commutator_eq_of_commutator_eq_smul`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.baseChangeExp_mul_baseChangeExp_of_lie_lie_eq`:
  doubly-laced exponential product relation along `{α + β, 2α + β}`.
* `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_baseChangeExpHom_of_lie_lie_eq`:
  doubly-laced commutator relation for `{α + β, 2α + β}`.
* `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_baseChangeExpHom_of_lie_lie_rev_eq`:
  doubly-laced commutator relation for `{α + β, α + 2β}`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--27.
-/

public section

open Multiplicative (ofAdd toAdd)
open TensorProduct
open scoped commutatorElement

namespace TauCeti.UniversalEnvelopingAlgebra

open Associative _root_.UniversalEnvelopingAlgebra

section DividedPowerCommutator

variable {K : Type*} [CommRing K] {L : Type*} [LieRing L] [LieAlgebra K L] {A : Type*} [Ring A]
variable {F : Type*} [FunLike F (_root_.UniversalEnvelopingAlgebra K L) A]
  [NonUnitalRingHomClass F (_root_.UniversalEnvelopingAlgebra K L) A]

private theorem mul_zsmul_of_lie (ρ : F) {a b c : L} (q r : ℤ) (n : ℕ)
    (h : q • ⁅a, b⁆ = (n * r) • c) :
    ρ (ι K a) * (q • ρ (ι K b)) = (q • ρ (ι K b)) * ρ (ι K a) + n • (r • ρ (ι K c)) := by
  simpa using zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ (p := 1) (by simpa using h)

variable [Algebra ℚ A] {V : Type*} [AddCommGroup V] [Module A V]
variable {S : Type*} [SetLike S V] [AddSubgroupClass S V]

attribute [local instance high] Algebra.toModule

variable {R : Type*} [CommRing R] [Algebra ℤ R]

/-- The two-factor integral exponential product relation along `{α + β, 2α + β}`, with integer
structure constants `c` and `d` absorbed into the parameters. Only the four vectors' divided powers
need preserve the lattice. -/
theorem baseChangeExp_mul_baseChangeExp_of_lie_lie_eq (ρ : F) (M : S) {x y z w : L} {c d : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxxy : ⁅x, ⁅x, y⁆⁆ = (2 * d) • w) (hxw : ⁅x, w⁆ = 0)
    (hyz : ⁅y, z⁆ = 0)
    (hx : IsNilpotent (ρ (ι K x))) (hy : IsNilpotent (ρ (ι K y)))
    (hz : IsNilpotent (ρ (ι K z))) (hw : IsNilpotent (ρ (ι K w)))
    (hMx : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι K x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι K y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι K z)) • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι K w)) • v ∈ M)
    (t u : R) :
    baseChangeExp (ρ (ι K x)) M hMx t * baseChangeExp (ρ (ι K y)) M hMy u =
      baseChangeExp (ρ (ι K y)) M hMy u *
        baseChangeExp (ρ (ι K z)) M hMz ((c : R) * (t * u)) *
        baseChangeExp (ρ (ι K w)) M hMw ((d : R) * (t ^ 2 * u)) *
        baseChangeExp (ρ (ι K x)) M hMx t := by
  have hxz : c • ⁅x, z⁆ = (2 * d) • w := by rw [← lie_zsmul, ← hxy, hxxy]
  have hMcz := fun n => Associative.dividedPower_zsmul_smul_mem c _ M (hMz n)
  have hMdw := fun n => Associative.dividedPower_zsmul_smul_mem d _ M (hMw n)
  rw [← baseChangeExp_zsmul c M hMz hMcz hz, ← baseChangeExp_zsmul d M hMw hMdw hw]
  exact baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul M
    (mul_eq_mul_add_zsmul_of_lie_eq ρ hxy) (mul_zsmul_of_lie ρ c d 2 hxz)
    ((commute_of_lie_eq_zero ρ hxw).smul_right d) ((commute_of_lie_eq_zero ρ hyz).smul_right c)
    hx hy (hz.smul c) hMx hMy hMcz hMdw t u

/-- **Steinberg's Chevalley commutator relation for the chain `α + β, 2α + β`.** If
`⁅x, y⁆ = c • z` and `⁅x, ⁅x, y⁆⁆ = (2 * d) • w` with `⁅x, w⁆ = ⁅y, z⁆ = 0`, then
`⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(d t² u)`. -/
theorem commutatorElement_baseChangeExpHom_of_lie_lie_eq (ρ : F) (M : S) {x y z w : L} {c d : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxxy : ⁅x, ⁅x, y⁆⁆ = (2 * d) • w) (hxw : ⁅x, w⁆ = 0) (hyz : ⁅y, z⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι K x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι K y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι K z)) • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι K w)) • v ∈ M)
    (hx : IsNilpotent (ρ (ι K x))) (hy : IsNilpotent (ρ (ι K y)))
    (hz : IsNilpotent (ρ (ι K z))) (hw : IsNilpotent (ρ (ι K w))) (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (ι K x)) M hMx hx t, baseChangeExpHom (ρ (ι K y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (ι K z)) M hMz hz (ofAdd ((c : R) * (toAdd t * toAdd u))) *
        baseChangeExpHom (ρ (ι K w)) M hMw hw (ofAdd ((d : R) * (toAdd t ^ 2 * toAdd u))) := by
  have hxz : c • ⁅x, z⁆ = (2 * d) • w := by rw [← lie_zsmul, ← hxy, hxxy]
  have hMcz := fun n => Associative.dividedPower_zsmul_smul_mem c _ M (hMz n)
  have hMdw := fun n => Associative.dividedPower_zsmul_smul_mem d _ M (hMw n)
  simpa only [baseChangeExpHom_zsmul c M hMz hMcz hz, baseChangeExpHom_zsmul d M hMw hMdw hw,
    toAdd_ofAdd] using
    commutatorElement_baseChangeExpHom_of_commutator_eq_two_nsmul M
      (mul_eq_mul_add_zsmul_of_lie_eq ρ hxy) (mul_zsmul_of_lie ρ c d 2 hxz)
      ((commute_of_lie_eq_zero ρ hxw).smul_right d) ((commute_of_lie_eq_zero ρ hyz).smul_right c)
      hx hy (hz.smul c) (hw.smul d) hMx hMy hMcz hMdw t u

/-- **Steinberg's Chevalley commutator relation for the reversed chain `α + β, α + 2β`.** If
`⁅x, y⁆ = c • z` and `⁅y, ⁅y, x⁆⁆ = (2 * d) • w` with `⁅y, w⁆ = ⁅x, z⁆ = 0`, then
`⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(-d t u²)`. -/
theorem commutatorElement_baseChangeExpHom_of_lie_lie_rev_eq (ρ : F) (M : S) {x y z w : L}
    {c d : ℤ} (hxy : ⁅x, y⁆ = c • z) (hyyx : ⁅y, ⁅y, x⁆⁆ = (2 * d) • w) (hyw : ⁅y, w⁆ = 0)
    (hxz : ⁅x, z⁆ = 0) (hMx : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι K x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι K y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι K z)) • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι K w)) • v ∈ M)
    (hx : IsNilpotent (ρ (ι K x))) (hy : IsNilpotent (ρ (ι K y)))
    (hz : IsNilpotent (ρ (ι K z))) (hw : IsNilpotent (ρ (ι K w))) (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (ι K x)) M hMx hx t, baseChangeExpHom (ρ (ι K y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (ι K z)) M hMz hz (ofAdd ((c : R) * (toAdd t * toAdd u))) *
        baseChangeExpHom (ρ (ι K w)) M hMw hw (ofAdd ((-d : R) * (toAdd t * toAdd u ^ 2))) := by
  have hyx : ⁅y, x⁆ = (-c) • z := by rw [← lie_skew y x, hxy, neg_zsmul]
  have hyz : (-c) • ⁅y, z⁆ = (2 * d) • w := by rw [← lie_zsmul, ← hyx, hyyx]
  have hMcz := fun n => Associative.dividedPower_zsmul_smul_mem (-c) _ M (hMz n)
  have hMdw := fun n => Associative.dividedPower_zsmul_smul_mem d _ M (hMw n)
  have hzw : Commute ((-c) • ρ (ι K z)) (d • ρ (ι K w)) :=
    ((commute_of_lie_eq_zero ρ hyw).smul_right d).of_commutator_eq_of_commutator_eq_smul
      (R := ℚ) (c := 2) (mul_eq_mul_add_zsmul_of_lie_eq ρ hyx)
      (by simpa only [← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_ofNat] using
        mul_zsmul_of_lie ρ (-c) d 2 hyz)
      ((commute_of_lie_eq_zero ρ hxz).smul_right (-c)) (isUnit_iff_ne_zero.mpr (by norm_num))
  have hz' : baseChangeExpHom ((-c) • ρ (ι K z)) M hMcz (hz.smul (-c))
        (ofAdd (toAdd u * toAdd t)) =
      baseChangeExpHom (ρ (ι K z)) M hMz hz (ofAdd (((-c : ℤ) : R) * (toAdd u * toAdd t))) := by
    rw [baseChangeExpHom_zsmul, toAdd_ofAdd]
  have hw' : baseChangeExpHom (d • ρ (ι K w)) M hMdw (hw.smul d)
        (ofAdd (toAdd u ^ 2 * toAdd t)) =
      baseChangeExpHom (ρ (ι K w)) M hMw hw (ofAdd ((d : R) * (toAdd u ^ 2 * toAdd t))) := by
    rw [baseChangeExpHom_zsmul, toAdd_ofAdd]
  rw [← commutatorElement_inv, commutatorElement_baseChangeExpHom_of_lie_lie_eq ρ M hyx hyyx hyw
      hxz hMy hMx hMz hMw hy hx hz hw u t, ← hz', ← hw', mul_inv_rev, ← MonoidHom.map_inv,
    ← MonoidHom.map_inv,
    (commute_baseChangeExpHom M hzw.symm hMdw hMcz (hw.smul d) (hz.smul (-c)) _ _).eq,
    baseChangeExpHom_zsmul (-c) M hMz hMcz hz (hz.smul (-c)),
    baseChangeExpHom_zsmul d M hMw hMdw hw (hw.smul d)]
  simp only [toAdd_inv, toAdd_ofAdd, Int.cast_neg]
  congr 3 <;> ring

end DividedPowerCommutator

end TauCeti.UniversalEnvelopingAlgebra
