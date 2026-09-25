/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.Range
public import TauCeti.RingTheory.Nilpotent.BaseChangeAction
public import Mathlib.Algebra.Lie.Derivation.BaseChange

/-!
# Integral exponentials of nilpotent Lie derivations

Let `D` be a nilpotent derivation of a Lie algebra over `ℚ`, and let an integral Lie subalgebra be
stable under every divided power `Dⁿ / n!`. The restricted divided powers obey the coefficient-free
Leibniz rule. Consequently their finite exponential preserves the Lie bracket after scalar
extension to an arbitrary commutative ring, even when factorials are not invertible in that ring.

## Main declarations

* `LieDerivation.dividedPower_apply_lie`: coefficient-free divided-power Leibniz rule.
* `TauCeti.integralDividedPower_lie`: the rule on the integral Lie subalgebra.
* `TauCeti.baseChangeExp_lie`: bracket preservation after arbitrary base change.
* `TauCeti.baseChangeExpLieEquiv`: the resulting Lie algebra automorphism.
-/

public section

open Finset TensorProduct

universe u v

noncomputable section

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

namespace LieDerivation

/-- Divided powers of a Lie derivation satisfy the coefficient-free divided-power Leibniz rule. -/
theorem dividedPower_apply_lie (D : LieDerivation ℚ L L) (n : ℕ) (x y : L) :
    TauCeti.Associative.dividedPower n D.toLinearMap ⁅x, y⁆ =
      ∑ ij ∈ antidiagonal n,
        ⁅TauCeti.Associative.dividedPower ij.1 D.toLinearMap x,
          TauCeti.Associative.dividedPower ij.2 D.toLinearMap y⁆ := by
  -- `Module.End.pow_apply` presents iteration through the underlying linear-map function,
  -- whereas `LieDerivation.iterate_apply_lie` uses the derivation's function coercion.
  rw [TauCeti.Associative.dividedPower_def, LinearMap.smul_apply, Module.End.pow_apply,
    show (⇑D.toLinearMap)^[n] ⁅x, y⁆ = D^[n] ⁅x, y⁆ from rfl,
    LieDerivation.iterate_apply_lie]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  simp only [TauCeti.Associative.dividedPower_def, LinearMap.smul_apply, Module.End.pow_apply,
    lie_smul, smul_lie, smul_smul]
  rw [mem_antidiagonal] at hij
  subst n
  -- After expanding both divided powers, the remaining equality is purely the equality of
  -- their rational scalar coefficients; `change` exposes those coefficients.
  change
    ((↑(ij.1 + ij.2).factorial : ℚ)⁻¹ * ↑((ij.1 + ij.2).choose ij.1)) •
        ⁅D^[ij.1] x, D^[ij.2] y⁆ =
      ((↑ij.2.factorial : ℚ)⁻¹ * (↑ij.1.factorial : ℚ)⁻¹) •
        ⁅D^[ij.1] x, D^[ij.2] y⁆
  congr 1
  field_simp
  exact_mod_cast (by
    simpa [Nat.add_comm] using Nat.add_choose_mul_factorial_mul_factorial ij.2 ij.1)

end LieDerivation

namespace TauCeti

/-- Restricted integral divided powers inherit the coefficient-free Leibniz rule. -/
theorem integralDividedPower_lie (D : LieDerivation ℚ L L) (M : LieSubalgebra ℤ L)
    (hM : ∀ n, ∀ x ∈ M, Associative.dividedPower n D.toLinearMap x ∈ M)
    (n : ℕ) (x y : M) :
    integralDividedPower D.toLinearMap M n (hM n) ⁅x, y⁆ =
      ∑ ij ∈ antidiagonal n,
        ⁅integralDividedPower D.toLinearMap M ij.1 (hM ij.1) x,
          integralDividedPower D.toLinearMap M ij.2 (hM ij.2) y⁆ := by
  apply SetLike.coe_eq_coe.mp
  rw [coe_integralDividedPower_apply]
  simp only [LieSubalgebra.coe_bracket, AddSubmonoidClass.coe_finsetSum]
  -- Coercing the subtype-valued equality to `L` leaves the ambient divided power on the left.
  change Associative.dividedPower n D.toLinearMap ⁅(x : L), (y : L)⁆ = _
  rw [LieDerivation.dividedPower_apply_lie]
  exact Finset.sum_congr rfl fun ij _ => by
    rw [coe_integralDividedPower_apply, coe_integralDividedPower_apply]
    rfl

variable {R : Type v} [CommRing R] [Algebra ℤ R]

attribute [local instance high] Algebra.toModule

/-- The integral divided-power exponential preserves the Lie bracket on pure tensors after an
arbitrary base change. -/
private theorem baseChangeExp_tmul_lie (D : LieDerivation ℚ L L) (M : LieSubalgebra ℤ L)
    (hM : ∀ n, ∀ x ∈ M, Associative.dividedPower n D.toLinearMap x ∈ M)
    (hD : IsNilpotent D.toLinearMap) (t a b : R) (x y : M) :
    baseChangeExp D.toLinearMap M hM t
        ⁅a ⊗ₜ[ℤ] x, b ⊗ₜ[ℤ] y⁆ =
      ⁅baseChangeExp D.toLinearMap M hM t (a ⊗ₜ[ℤ] x),
        baseChangeExp D.toLinearMap M hM t (b ⊗ₜ[ℤ] y)⁆ := by
  obtain ⟨k, hk⟩ := hD
  -- `pow_add` requires the doubled exponent to be presented as a sum.
  have two_mul_k : 2 * k = k + k := by omega
  have hk2 : D.toLinearMap ^ (2 * k) = 0 := by
    rw [two_mul_k, pow_add, hk, zero_mul]
  let d := fun n => integralDividedPower D.toLinearMap M n (hM n)
  rw [LieAlgebra.ExtendScalars.bracket_tmul,
    baseChangeExp_tmul_of_pow_eq_zero D.toLinearMap M hM hk2,
    baseChangeExp_tmul_of_pow_eq_zero D.toLinearMap M hM hk,
    baseChangeExp_tmul_of_pow_eq_zero D.toLinearMap M hM hk]
  rw [sum_lie (range k)
    (fun n => (t ^ n * a) ⊗ₜ[ℤ] d n x)
    (∑ n ∈ range k, (t ^ n * b) ⊗ₜ[ℤ] d n y)]
  simp_rw [lie_sum, LieAlgebra.ExtendScalars.bracket_tmul]
  calc
    (∑ n ∈ range (2 * k), (t ^ n * (a * b)) ⊗ₜ[ℤ] d n ⁅x, y⁆) =
        ∑ n ∈ range (2 * k), ∑ ij ∈ antidiagonal n,
          (t ^ (ij.1 + ij.2) * (a * b)) ⊗ₜ[ℤ] ⁅d ij.1 x, d ij.2 y⁆ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [integralDividedPower_lie, TensorProduct.tmul_sum]
      apply Finset.sum_congr rfl
      intro ij hij
      rw [mem_antidiagonal] at hij
      rw [hij]
    _ = ∑ i ∈ range k, ∑ j ∈ range k,
          (t ^ (i + j) * (a * b)) ⊗ₜ[ℤ] ⁅d i x, d j y⁆ := by
      rw [two_mul_k]
      apply sum_range_add_antidiagonal_of_support
      intro i j hij
      dsimp only [d]
      rcases hij with hi | hj
      · rw [integralDividedPower_eq_zero_of_le D.toLinearMap M i (hM i) hk hi,
          LinearMap.zero_apply, zero_lie, TensorProduct.tmul_zero]
      · rw [integralDividedPower_eq_zero_of_le D.toLinearMap M j (hM j) hk hj,
          LinearMap.zero_apply, lie_zero, TensorProduct.tmul_zero]
    _ = ∑ i ∈ range k, ∑ j ∈ range k,
          ((t ^ i * a) * (t ^ j * b)) ⊗ₜ[ℤ] ⁅d i x, d j y⁆ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring

/-- The integral divided-power exponential preserves the Lie bracket after an arbitrary base
change. No finite-dimensionality, flatness, or characteristic assumption is needed on the new
base ring. -/
theorem baseChangeExp_lie (D : LieDerivation ℚ L L) (M : LieSubalgebra ℤ L)
    (hM : ∀ n, ∀ x ∈ M, Associative.dividedPower n D.toLinearMap x ∈ M)
    (hD : IsNilpotent D.toLinearMap) (t : R) (x y : R ⊗[ℤ] M) :
    baseChangeExp D.toLinearMap M hM t ⁅x, y⁆ =
      ⁅baseChangeExp D.toLinearMap M hM t x,
        baseChangeExp D.toLinearMap M hM t y⁆ := by
  let _ : LieRing (R ⊗[ℤ] M) := LieAlgebra.ExtendScalars.instLieRing ℤ R M
  let _ : LieAlgebra R (R ⊗[ℤ] M) := LieAlgebra.ExtendScalars.instLieAlgebra ℤ R M
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y => exact baseChangeExp_tmul_lie D M hM hD t a b x y
      | add y z hy hz =>
          rw [lie_add, map_add, hy, hz]
          rw [map_add, lie_add]
  | add x z hx hz =>
      rw [add_lie, map_add, hx, hz]
      rw [map_add, add_lie]

/-- The integral divided-power exponential of a nilpotent Lie derivation, after arbitrary base
change, as a Lie algebra automorphism. -/
noncomputable def baseChangeExpLieEquiv (D : LieDerivation ℚ L L) (M : LieSubalgebra ℤ L)
    (hM : ∀ n, ∀ x ∈ M, Associative.dividedPower n D.toLinearMap x ∈ M)
    (hD : IsNilpotent D.toLinearMap) (t : R) :
    R ⊗[ℤ] M ≃ₗ⁅R⁆ R ⊗[ℤ] M :=
  { baseChangeExpLinearEquiv D.toLinearMap M hM hD t with
    map_lie' := by
      intro x y
      -- The structure-extension syntax presents the inherited `LinearEquiv` through its
      -- `toLinearMap`; expose it so the named underlying-map theorem can rewrite the goal.
      change (baseChangeExpLinearEquiv D.toLinearMap M hM hD t).toLinearMap ⁅x, y⁆ = _
      rw [baseChangeExpLinearEquiv_toLinearMap]
      exact baseChangeExp_lie D M hM hD t x y }

/-- The underlying action of the base-changed Lie exponential is the existing divided-power
exponential. -/
@[simp]
theorem baseChangeExpLieEquiv_apply (D : LieDerivation ℚ L L) (M : LieSubalgebra ℤ L)
    (hM : ∀ n, ∀ x ∈ M, Associative.dividedPower n D.toLinearMap x ∈ M)
    (hD : IsNilpotent D.toLinearMap) (t : R) (x : R ⊗[ℤ] M) :
    baseChangeExpLieEquiv D M hM hD t x = baseChangeExp D.toLinearMap M hM t x := by
  -- Evaluation of the structure extension is definitionally evaluation of its `LinearEquiv`.
  change baseChangeExpLinearEquiv D.toLinearMap M hM hD t x = _
  exact congrFun (coe_baseChangeExpLinearEquiv D.toLinearMap M hM hD t) x

/-- The Lie exponential at zero is the identity automorphism. -/
@[simp]
theorem baseChangeExpLieEquiv_zero (D : LieDerivation ℚ L L) (M : LieSubalgebra ℤ L)
    (hM : ∀ n, ∀ x ∈ M, Associative.dividedPower n D.toLinearMap x ∈ M)
    (hD : IsNilpotent D.toLinearMap) :
    baseChangeExpLieEquiv (R := R) D M hM hD 0 = LieEquiv.refl := by
  ext x
  rw [baseChangeExpLieEquiv_apply, baseChangeExp_zero D.toLinearMap M hM hD]
  rfl

/-- Lie exponentials compose by adding their parameters. -/
@[simp]
theorem baseChangeExpLieEquiv_trans (D : LieDerivation ℚ L L) (M : LieSubalgebra ℤ L)
    (hM : ∀ n, ∀ x ∈ M, Associative.dividedPower n D.toLinearMap x ∈ M)
    (hD : IsNilpotent D.toLinearMap) (t u : R) :
    (baseChangeExpLieEquiv D M hM hD t).trans (baseChangeExpLieEquiv D M hM hD u) =
      baseChangeExpLieEquiv D M hM hD (t + u) := by
  ext x
  simp only [LieEquiv.trans_apply, baseChangeExpLieEquiv_apply]
  rw [← Module.End.mul_apply, ← baseChangeExp_add D.toLinearMap M hM hD u t, add_comm]

/-- The inverse of a Lie exponential is the exponential at the negative parameter. -/
@[simp]
theorem baseChangeExpLieEquiv_symm (D : LieDerivation ℚ L L) (M : LieSubalgebra ℤ L)
    (hM : ∀ n, ∀ x ∈ M, Associative.dividedPower n D.toLinearMap x ∈ M)
    (hD : IsNilpotent D.toLinearMap) (t : R) :
    (baseChangeExpLieEquiv D M hM hD t).symm =
      baseChangeExpLieEquiv D M hM hD (-t) := by
  apply LieEquiv.toLinearEquiv_injective
  exact baseChangeExpLinearEquiv_symm D.toLinearMap M hM hD t

end TauCeti

end
