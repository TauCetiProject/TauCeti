/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import TauCeti.RingTheory.DividedPowers.NormalOrdering
public import TauCeti.RingTheory.Nilpotent.BaseChangeAction
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# The Chevalley commutator relation for integral nilpotent exponentials

Let `V` be a module over a `ℚ`-algebra `A`, let `M ≤ V` be an additive subgroup, and let
`x`, `y`, `z` be elements of `A` with

```text
x * y = y * x + z,   z commuting with both x and y.
```

The integral divided-power exponentials of `x`, `y`, `z` act on the scalar extension `R ⊗[ℤ] M`
over every commutative ring `R`, by `TauCeti.baseChangeExp`. The main result below is that they
satisfy the **Chevalley commutator relation**

```text
E_x(t) E_y(u) = E_y(u) E_z(t * u) E_x(t).
```

Equivalently `E_x(t) E_y(u) E_x(t)⁻¹ = E_y(u) E_z(t * u)`: conjugating the one-parameter subgroup
of `y` by the one-parameter subgroup of `x` multiplies it by the one-parameter subgroup of the
commutator, at the product parameter. Reading these actions as bundled one-parameter subgroups
`TauCeti.baseChangeExpHom` in `(R ⊗[ℤ] M ≃ₗ[R] R ⊗[ℤ] M)` yields the group-commutator identity
`⁅E_x(t), E_y(u)⁆ = E_z(t * u)`. This is the class-two case of the Chevalley commutator formula,
the case in which the only root of the form `i α + j β` besides `α` and `β` is `α + β`; in a
simply-laced root system every pair of non-proportional roots falls under it or under the commuting
case `TauCeti.commute_baseChangeExp` from `TauCeti.RingTheory.Nilpotent.BaseChangeAction`.

Nothing here divides by a factorial in `R`, so the relation holds over a ring of arbitrary
characteristic. The whole point is the coefficient-one normal-ordering rule
`TauCeti.Associative.dividedPower_mul_dividedPower_of_commutator_eq`, which says that the
rational divided powers reorder with integral structure constants; the exponential identity is
its generating-function form.

## Main results

* `TauCeti.integralDividedPower_mul_integralDividedPower_of_commutator_eq`: normal ordering for the
  integral operators restricted to `M`.
* `TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq` and
  `TauCeti.baseChangeExp_conj_of_commutator_eq`: the Chevalley commutator relation and its
  conjugation form.
* `TauCeti.baseChangeExpHom_mul_of_commutator_eq` and
  `TauCeti.commutatorElement_baseChangeExpHom_of_commutator_eq`: multiplication and
  element-commutator laws for `baseChangeExpHom`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4 and Theorem 5.2.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti

open Finset Multiplicative TensorProduct
open scoped commutatorElement

universe u v

variable {A : Type*} [Ring A] [Algebra ℚ A]
variable {V : Type u} [AddCommGroup V] [Module A V]
variable {S : Type*} [SetLike S V] [AddSubgroupClass S V]

/-! ## Normal ordering the restricted operators -/

/-- **Normal ordering for restricted divided powers.** If `x * y = y * x + z` and `z` commutes with
both `x` and `y`, the integral operators obtained by restricting divided powers to a stable additive
subgroup satisfy the coefficient-one straightening rule. -/
theorem integralDividedPower_mul_integralDividedPower_of_commutator_eq
    {x y z : A} (M : S) (hxy : x * y = y * x + z) (hxz : Commute x z) (hyz : Commute y z)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n z • v ∈ M)
    (m n : ℕ) :
    integralDividedPower x M m (hMx m) * integralDividedPower y M n (hMy n) =
      ∑ k ∈ range (min m n + 1),
        integralDividedPower y M (n - k) (hMy (n - k)) *
          integralDividedPower z M k (hMz k) *
          integralDividedPower x M (m - k) (hMx (m - k)) := by
  ext v
  simp only [mul_apply_eq_comp, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum,
    coe_integralDividedPower_apply, ← mul_smul, ← Finset.sum_smul]
  congr 1
  simpa only [mul_assoc] using
    Associative.dividedPower_mul_dividedPower_of_commutator_eq hxy hxz hyz m n

-- Match tensor products to the module structure carried by the explicit `ℤ`-algebra.
attribute [local instance high] Algebra.toModule

/-! ## The Chevalley commutator relation -/

section Commutator

variable {R : Type v} [CommRing R] [Algebra ℤ R]

/-- **The Chevalley commutator relation for integral nilpotent exponentials.** If
`x * y = y * x + z` with `z` commuting with `x` and with `y`, then over every commutative ring `R`
the integral divided-power exponentials on `R ⊗[ℤ] M` satisfy

```text
E_x(t) E_y(u) = E_y(u) E_z(t * u) E_x(t).
```

No factorial is inverted in `R`: the relation holds in every characteristic. -/
theorem baseChangeExp_mul_baseChangeExp_of_commutator_eq
    {x y z : A} (M : S) (hxy : x * y = y * x + z) (hxz : Commute x z) (hyz : Commute y z)
    (hx : IsNilpotent x) (hy : IsNilpotent y)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n z • v ∈ M)
    (t u : R) :
    baseChangeExp x M hMx t * baseChangeExp y M hMy u =
      baseChangeExp y M hMy u * baseChangeExp z M hMz (t * u) * baseChangeExp x M hMx t := by
  classical
  obtain ⟨kz, hkz⟩ := Associative.isNilpotent_of_commutator_eq hxy hxz hyz hx
  obtain ⟨kx, hkx⟩ := hx
  obtain ⟨ky, hky⟩ := hy
  set N := kx + ky + kz with _
  have hxN : x ^ N = 0 := pow_eq_zero_of_le (by omega) hkx
  have hyN : y ^ N = 0 := pow_eq_zero_of_le (by omega) hky
  have hzN : z ^ N = 0 := pow_eq_zero_of_le (by omega) hkz
  rw [baseChangeExp_of_pow_eq_zero x M hMx hxN,
    baseChangeExp_of_pow_eq_zero y M hMy hyN,
    baseChangeExp_of_pow_eq_zero z M hMz hzN]
  refine Finset.sum_smul_mul_sum_smul_of_mul_eq_sum (R := R)
    (fun n => (integralDividedPower x M n (hMx n)).baseChange R)
    (fun n => (integralDividedPower y M n (hMy n)).baseChange R)
    (fun n => (integralDividedPower z M n (hMz n)).baseChange R) N ?_ ?_ t u
  · intro m n
    have h := congrArg (fun f : Module.End ℤ M => (Module.End.baseChangeHom ℤ R M) f)
      (integralDividedPower_mul_integralDividedPower_of_commutator_eq M hxy hxz hyz hMx hMy hMz m n)
    simp only [map_mul, map_sum] at h
    exact h
  · -- Outside the truncation the reordered triple has a vanishing factor.
    have hvx := forall_baseChange_integralDividedPower_eq_zero_of_le (R := R) x M hMx hkx
    have hvy := forall_baseChange_integralDividedPower_eq_zero_of_le (R := R) y M hMy hky
    have hvz := forall_baseChange_integralDividedPower_eq_zero_of_le (R := R) z M hMz hkz
    rintro p k q (hpk | hqk)
    · rcases le_or_gt ky p with hp | hp
      · rw [hvy p hp, zero_mul, zero_mul]
      · rw [hvz k (by omega), mul_zero, zero_mul]
    · rcases le_or_gt kx q with hq | hq
      · rw [hvx q hq, mul_zero]
      · rw [hvz k (by omega), mul_zero, zero_mul]

/-- The conjugation form of the Chevalley commutator relation: conjugating the one-parameter
subgroup of `y` by that of `x` multiplies it by the one-parameter subgroup of the commutator `z`,
at the product parameter. -/
theorem baseChangeExp_conj_of_commutator_eq
    {x y z : A} (M : S) (hxy : x * y = y * x + z) (hxz : Commute x z) (hyz : Commute y z)
    (hx : IsNilpotent x) (hy : IsNilpotent y)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n z • v ∈ M)
    (t u : R) :
    baseChangeExp x M hMx t * baseChangeExp y M hMy u * baseChangeExp x M hMx (-t) =
      baseChangeExp y M hMy u * baseChangeExp z M hMz (t * u) := by
  rw [baseChangeExp_mul_baseChangeExp_of_commutator_eq M hxy hxz hyz hx hy hMx hMy hMz t u,
    mul_assoc, ← baseChangeExp_add x M hMx hx t (-t), add_neg_cancel,
    baseChangeExp_zero x M hMx hx, mul_one]

/-- **Class-two multiplication law for `baseChangeExpHom`.** If `x * y = y * x + z` with `z`
commuting with both `x` and `y`, then `E_x(t) E_y(u) = E_y(u) E_z(t * u) E_x(t)`. -/
theorem baseChangeExpHom_mul_of_commutator_eq {x y z : A} (M : S)
    (hxy : x * y = y * x + z) (hxz : Commute x z) (hyz : Commute y z)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n z • v ∈ M)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (hz : IsNilpotent z) (t u : Multiplicative R) :
    baseChangeExpHom x M hMx hx t * baseChangeExpHom y M hMy hy u =
      baseChangeExpHom y M hMy hy u * baseChangeExpHom z M hMz hz (ofAdd (toAdd t * toAdd u)) *
        baseChangeExpHom x M hMx hx t :=
  LinearEquiv.toLinearMap_inj.mp <| by
    simp only [LinearEquiv.coe_toLinearMap_mul, baseChangeExpHom_toLinearMap, toAdd_ofAdd]
    exact baseChangeExp_mul_baseChangeExp_of_commutator_eq M hxy hxz hyz hx hy hMx hMy hMz
      (toAdd t) (toAdd u)

/-- **Class-two element-commutator relation for `baseChangeExpHom`.** If `x * y = y * x + z` with
`z` commuting with both `x` and `y`, then `⁅E_x(t), E_y(u)⁆ = E_z(t * u)`. -/
theorem commutatorElement_baseChangeExpHom_of_commutator_eq {x y z : A} (M : S)
    (hxy : x * y = y * x + z) (hxz : Commute x z) (hyz : Commute y z)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n z • v ∈ M)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (hz : IsNilpotent z) (t u : Multiplicative R) :
    ⁅baseChangeExpHom x M hMx hx t, baseChangeExpHom y M hMy hy u⁆ =
      baseChangeExpHom z M hMz hz (ofAdd (toAdd t * toAdd u)) := by
  rw [commutatorElement_def,
    baseChangeExpHom_mul_of_commutator_eq M hxy hxz hyz hMx hMy hMz hx hy hz t u,
    mul_inv_cancel_right, (commute_baseChangeExpHom M hyz hMy hMz hy hz u _).eq,
    mul_inv_cancel_right]

end Commutator

end TauCeti
