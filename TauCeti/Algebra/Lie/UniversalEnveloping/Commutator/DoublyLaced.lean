/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.RingTheory.Nilpotent.BaseChangeAction
import Mathlib.Algebra.Module.Rat
import TauCeti.Algebra.Lie.RootStringJacobi
import TauCeti.RingTheory.Nilpotent.RootString.Basic

/-!
# Doubly-laced Chevalley commutator relations for enveloping-algebra one-parameter subgroups

Let `L` be a Lie algebra over `ℚ`, `ρ` a ring homomorphism from `U(L)` into a `ℚ`-algebra `A`, and
`M` an additive subgroup of an `A`-module `V` preserved by the divided powers of the relevant
root-vector images. Over any commutative ring `R`, `TauCeti.baseChangeExpHom` attaches to each
nilpotent `ρ(ι e)` a one-parameter subgroup `Multiplicative R →* (R ⊗[ℤ] M ≃ₗ[R] R ⊗[ℤ] M)`.

This file proves Steinberg's doubly-laced element-commutator identities in the normalization
`⁅g, h⁆ = g * h * g⁻¹ * h⁻¹` for both root orders:
* `{α + β, 2α + β}`: `⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(d t² u)` under `⁅x, y⁆ = c • z`,
  `⁅x, ⁅x, y⁆⁆ = (2 * d) • w`, and `⁅x, w⁆ = ⁅y, z⁆ = 0`, using
  `TauCeti.zsmul_lie_eq_zero_of_zsmul_lie_eq_two_mul_zsmul` so no separate `⁅y, w⁆ = 0` hypothesis
  is required;
* `{α + β, α + 2β}`: `⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(-d t u²)` under `⁅x, y⁆ = c • z`,
  `⁅y, ⁅y, x⁆⁆ = (2 * d) • w`, and `⁅y, w⁆ = ⁅x, z⁆ = 0`, derived directly by collecting
  `E_y(u) * E_x(-t)` via `TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul`.

## Main results

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

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {A : Type*} [Ring A]
variable {F : Type*} [FunLike F (_root_.UniversalEnvelopingAlgebra ℚ L) A]
  [NonUnitalRingHomClass F (_root_.UniversalEnvelopingAlgebra ℚ L) A]

private theorem mul_zsmul_of_lie (ρ : F) {a b c : L} (q r : ℤ) (n : ℕ)
    (h : q • ⁅a, b⁆ = (n * r) • c) :
    ρ (ι ℚ a) * (q • ρ (ι ℚ b)) = (q • ρ (ι ℚ b)) * ρ (ι ℚ a) + n • (r • ρ (ι ℚ c)) := by
  simpa using zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ (p := 1) (by simpa using h)

variable [Algebra ℚ A] {V : Type*} [AddCommGroup V] [Module A V]
variable {S : Type*} [SetLike S V] [AddSubgroupClass S V]

attribute [local instance high] Algebra.toModule

variable {R : Type*} [CommRing R] [Algebra ℤ R]

private theorem commute_exp_zsmul_right (ρ : F) (M : S) {a b : L} {q : ℤ} (hab : q • ⁅a, b⁆ = 0)
    (hMa : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι ℚ a)) • v ∈ M)
    (hMb : ∀ n, ∀ v ∈ M, dividedPower n (q • ρ (ι ℚ b)) • v ∈ M)
    (ha : IsNilpotent (ρ (ι ℚ a))) (hb : IsNilpotent (q • ρ (ι ℚ b))) (t u : Multiplicative R) :
    Commute (baseChangeExpHom (ρ (ι ℚ a)) M hMa ha t)
      (baseChangeExpHom (q • ρ (ι ℚ b)) M hMb hb u) :=
  commute_baseChangeExpHom M (by simpa only [one_zsmul] using
    commute_zsmul_of_zsmul_lie_eq_zero ρ (p := 1) (q := q) (by simpa using hab)) hMa hMb ha hb t u

/-- **Steinberg's Chevalley commutator relation for the chain `α + β, 2α + β`.** If
`⁅x, y⁆ = c • z` and `⁅x, ⁅x, y⁆⁆ = (2 * d) • w` with `⁅x, w⁆ = ⁅y, z⁆ = 0`, then
`⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(d t² u)`. -/
theorem commutatorElement_baseChangeExpHom_of_lie_lie_eq (ρ : F) (M : S) {x y z w : L} {c d : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxxy : ⁅x, ⁅x, y⁆⁆ = (2 * d) • w) (hxw : ⁅x, w⁆ = 0) (hyz : ⁅y, z⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι ℚ y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι ℚ z)) • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι ℚ w)) • v ∈ M)
    (hx : IsNilpotent (ρ (ι ℚ x))) (hy : IsNilpotent (ρ (ι ℚ y)))
    (hz : IsNilpotent (ρ (ι ℚ z))) (hw : IsNilpotent (ρ (ι ℚ w))) (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t, baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (ι ℚ z)) M hMz hz (ofAdd ((c : R) * (toAdd t * toAdd u))) *
        baseChangeExpHom (ρ (ι ℚ w)) M hMw hw (ofAdd ((d : R) * (toAdd t ^ 2 * toAdd u))) := by
  have _ : HasUniqueDiv L := .of_module_rat L
  have hxz : c • ⁅x, z⁆ = (2 * d) • w := by rw [← lie_zsmul, ← hxy, hxxy]
  have hyw := zsmul_lie_eq_zero_of_zsmul_lie_eq_two_mul_zsmul hxy hxz hyz
  have hMcz := fun n => Associative.dividedPower_zsmul_smul_mem c _ M (hMz n)
  have hMdw := fun n => Associative.dividedPower_zsmul_smul_mem d _ M (hMw n)
  let tr := toAdd t; let ur := toAdd u; let E (a : A) hM ha := baseChangeExpHom (R := R) a M hM ha
  have hmul : E (ρ (ι ℚ x)) hMx hx t * E (ρ (ι ℚ y)) hMy hy u = E (ρ (ι ℚ y)) hMy hy u *
        E (c • ρ (ι ℚ z)) hMcz (hz.smul c) (ofAdd (tr * ur)) *
        E (d • ρ (ι ℚ w)) hMdw (hw.smul d) (ofAdd (tr ^ 2 * ur)) * E (ρ (ι ℚ x)) hMx hx t :=
    LinearEquiv.toLinearMap_inj.mp <| by
      simp only [E, LinearEquiv.coe_toLinearMap_mul, baseChangeExpHom_toLinearMap, toAdd_ofAdd]
      exact baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul M
        (mul_eq_mul_add_zsmul_of_lie_eq ρ hxy) (mul_zsmul_of_lie ρ c d 2 hxz)
        ((commute_of_lie_eq_zero ρ hxw).smul_right d) ((commute_of_lie_eq_zero ρ hyz).smul_right c)
        hx hy (hz.smul c) hMx hMy hMcz hMdw tr ur
  dsimp only [E] at hmul
  rw [commutatorElement_def, hmul, mul_inv_cancel_right,
    mul_assoc (baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u),
    ((commute_baseChangeExpHom M ((commute_of_lie_eq_zero ρ hyz).smul_right c) hMy hMcz hy _ u
      _).mul_right (commute_exp_zsmul_right ρ M hyw hMy hMdw hy _ u _)).mul_inv_cancel,
    baseChangeExpHom_zsmul c M hMz hMcz hz _, baseChangeExpHom_zsmul d M hMw hMdw hw _]
  simp only [toAdd_ofAdd, tr, ur]

/-- **Steinberg's Chevalley commutator relation for the reversed chain `α + β, α + 2β`.** If
`⁅x, y⁆ = c • z` and `⁅y, ⁅y, x⁆⁆ = (2 * d) • w` with `⁅y, w⁆ = ⁅x, z⁆ = 0`, then
`⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(-d t u²)`. -/
theorem commutatorElement_baseChangeExpHom_of_lie_lie_rev_eq (ρ : F) (M : S) {x y z w : L}
    {c d : ℤ} (hxy : ⁅x, y⁆ = c • z) (hyyx : ⁅y, ⁅y, x⁆⁆ = (2 * d) • w) (hyw : ⁅y, w⁆ = 0)
    (hxz : ⁅x, z⁆ = 0) (hMx : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι ℚ y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι ℚ z)) • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M, dividedPower n (ρ (ι ℚ w)) • v ∈ M)
    (hx : IsNilpotent (ρ (ι ℚ x))) (hy : IsNilpotent (ρ (ι ℚ y)))
    (hz : IsNilpotent (ρ (ι ℚ z))) (hw : IsNilpotent (ρ (ι ℚ w))) (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t, baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (ι ℚ z)) M hMz hz (ofAdd ((c : R) * (toAdd t * toAdd u))) *
        baseChangeExpHom (ρ (ι ℚ w)) M hMw hw (ofAdd ((-d : R) * (toAdd t * toAdd u ^ 2))) := by
  have hyx : ⁅y, x⁆ = (-c) • z := by rw [← lie_skew y x, hxy, neg_zsmul]
  have hyz : (-c) • ⁅y, z⁆ = (2 * d) • w := by rw [← lie_zsmul, ← hyx, hyyx]
  have hMcz := fun n => Associative.dividedPower_zsmul_smul_mem (-c) _ M (hMz n)
  have hMdw := fun n => Associative.dividedPower_zsmul_smul_mem d _ M (hMw n)
  let tr := toAdd t; let ur := toAdd u; let E (a : A) hM ha := baseChangeExpHom (R := R) a M hM ha
  have hmul : E (ρ (ι ℚ y)) hMy hy u * E (ρ (ι ℚ x)) hMx hx t⁻¹ = E (ρ (ι ℚ x)) hMx hx t⁻¹ *
        E ((-c) • ρ (ι ℚ z)) hMcz (hz.smul (-c)) (ofAdd (ur * -tr)) *
        E (d • ρ (ι ℚ w)) hMdw (hw.smul d) (ofAdd (ur ^ 2 * -tr)) * E (ρ (ι ℚ y)) hMy hy u :=
    LinearEquiv.toLinearMap_inj.mp <| by
      simp only [E, LinearEquiv.coe_toLinearMap_mul, baseChangeExpHom_toLinearMap,
        toAdd_ofAdd, toAdd_inv]
      exact baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul M
        (mul_eq_mul_add_zsmul_of_lie_eq ρ hyx) (mul_zsmul_of_lie ρ (-c) d 2 hyz)
        ((commute_of_lie_eq_zero ρ hyw).smul_right d)
        ((commute_of_lie_eq_zero ρ hxz).smul_right (-c))
        hy hx (hz.smul (-c)) hMy hMx hMcz hMdw ur (-tr)
  rw [map_inv] at hmul; dsimp only [E] at hmul
  rw [commutatorElement_def, mul_assoc (baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t), hmul]
  simp only [@mul_assoc (_ ≃ₗ[R] _) _, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  rw [baseChangeExpHom_zsmul (-c) M hMz hMcz hz _, baseChangeExpHom_zsmul d M hMw hMdw hw _]
  simp only [toAdd_ofAdd, Int.cast_neg]; congr 3 <;> ring

end DividedPowerCommutator

end TauCeti.UniversalEnvelopingAlgebra
