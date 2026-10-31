/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowerAlgebra.Init
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.RingTheory.PowerSeries.DividedPowerSequence
import Mathlib.Data.Nat.Choose.Sum

/-!
# The divided-power exponential

For a module `M` over a commutative semiring `R` and a commutative `R`-algebra `S`, this file
defines the divided-power exponential `exp(x) = ∑_d γ_d(x) X ^ d` of `x : S ⊗[R] M`, a power
series with coefficients in `S ⊗[R] Γ_R(M)`. It is determined by
`exp(s ⊗ m) = ∑ₙ (s ^ n ⊗ dp R n m) X ^ n` and `exp(x + y) = exp(x) * exp(y)`, and its
coefficients satisfy the divided-power relations `γ₀ = 1` and
`γₘ * γₙ = (m + n).choose m • γₘ₊ₙ`.

## Main declarations

* `DividedPowerAlgebra.exp`: the divided-power exponential; `DividedPowerAlgebra.coeff_exp_tmul`,
  `exp_zero`, `exp_add`, `exp_smul` and `exp_rTensor` characterize it.
* `DividedPowerAlgebra.constantCoeff_exp` and `DividedPowerAlgebra.coeff_exp_mul_coeff_exp`: the
  coefficients of the exponential satisfy the divided-power relations `γ₀ = 1` and
  `γₘ * γₙ = (m + n).choose m • γₘ₊ₙ`.

## Implementation notes

The Roby relations `dp_add`, `dp_mul` and `dp_smul` say exactly that the formula
`exp(s ⊗ m) = ∑ₙ (s ^ n ⊗ dp R n m) X ^ n` is multiplicative in each of `s` and `m`, and
balanced, so that `exp` is a well-defined map from `S ⊗[R] M` to the multiplicative monoid of
power series.

## References

* [N. Roby, *Lois polynômes et lois formelles en théorie des modules* (1963),
  Proposition IV.1][Roby-1963]
* The ambient `DividedPowerAlgebra` is the Mathlib formalization by Antoine Chambert-Loir and
  María Inés de Frutos-Fernández.
-/

public section

noncomputable section

open TensorProduct PowerSeries

namespace DividedPowerAlgebra

variable {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]

variable {S : Type*} [CommSemiring S] [Algebra R S]

variable (R) in
/-- The divided-power exponential `∑ₙ (s ^ n ⊗ dp R n m) X ^ n` of a pure tensor `s ⊗ m`. -/
private def expTmul (s : S) (m : M) : (S ⊗[R] DividedPowerAlgebra R M)⟦X⟧ :=
  PowerSeries.mk fun n ↦ (s ^ n) ⊗ₜ[R] dp R n m

private theorem coeff_expTmul (s : S) (m : M) (n : ℕ) :
    coeff n (expTmul R s m) = (s ^ n) ⊗ₜ[R] dp R n m :=
  coeff_mk _ _

private theorem expTmul_zero_right (s : S) : expTmul R s (0 : M) = 1 := by
  ext n
  rw [coeff_expTmul, coeff_one, dp_null]
  split_ifs with hn
  · rw [hn, pow_zero, Algebra.TensorProduct.one_def]
  · rw [tmul_zero]

private theorem expTmul_add_right (s : S) (m m' : M) :
    expTmul R s (m + m') = expTmul R s m * expTmul R s m' := by
  ext n
  rw [coeff_mul, coeff_expTmul, dp_add, tmul_sum]
  refine Finset.sum_congr rfl fun ⟨a, b⟩ hab ↦ ?_
  rw [coeff_expTmul, coeff_expTmul, Algebra.TensorProduct.tmul_mul_tmul, ← pow_add,
    Finset.mem_antidiagonal.mp hab]

private theorem expTmul_zero_left (m : M) : expTmul R (0 : S) m = 1 := by
  ext n
  rw [coeff_expTmul, coeff_one]
  rcases n with _ | n
  · simp [dp_zero, Algebra.TensorProduct.one_def]
  · simp

private theorem expTmul_add_left (s s' : S) (m : M) :
    expTmul R (s + s') m = expTmul R s m * expTmul R s' m := by
  ext n
  rw [coeff_mul, coeff_expTmul, (Commute.all s s').add_pow', sum_tmul]
  refine Finset.sum_congr rfl fun ⟨a, b⟩ hab ↦ ?_
  rw [coeff_expTmul, coeff_expTmul, Algebra.TensorProduct.tmul_mul_tmul, dp_mul,
    Finset.mem_antidiagonal.mp hab, smul_tmul]

private theorem expTmul_smul (r : R) (s : S) (m : M) :
    expTmul R (r • s) m = expTmul R s (r • m) := by
  ext n
  rw [coeff_expTmul, coeff_expTmul, smul_pow, dp_smul, smul_tmul]

/-- A shortcut instance: without it, synthesizing the additive structure on
`M →+ Additive (S ⊗[R] DividedPowerAlgebra R M)⟦X⟧` fails, because the search for a commutative
monoid structure on the power series ring tries instance paths that abort the search. -/
private local instance instAddCommMonoidAdditiveExpSeries :
    AddCommMonoid (Additive ((S ⊗[R] DividedPowerAlgebra R M)⟦X⟧)) :=
  Additive.addCommMonoid

variable (R M S) in
/-- The divided-power exponential of pure tensors, as a biadditive map to the multiplicative monoid
of power series. -/
private def expTmulHom : S →+ M →+ Additive ((S ⊗[R] DividedPowerAlgebra R M)⟦X⟧) where
  toFun s :=
    { toFun m := Additive.ofMul (expTmul R s m)
      map_zero' := by rw [expTmul_zero_right, ofMul_one]
      map_add' m m' := by rw [expTmul_add_right, ofMul_mul] }
  map_zero' := AddMonoidHom.ext fun m ↦ congrArg Additive.ofMul (expTmul_zero_left m)
  map_add' s s' := AddMonoidHom.ext fun m ↦ congrArg Additive.ofMul (expTmul_add_left s s' m)

private theorem expTmulHom_apply_apply (s : S) (m : M) :
    expTmulHom R M S s m = Additive.ofMul (expTmul R s m) :=
  rfl

variable (R M S) in
/-- The divided-power exponential, as an additive map to the multiplicative monoid of power
series. -/
private def expAddHom : S ⊗[R] M →+ Additive ((S ⊗[R] DividedPowerAlgebra R M)⟦X⟧) :=
  liftAddHom (expTmulHom R M S) fun r s m ↦ by
    rw [expTmulHom_apply_apply, expTmulHom_apply_apply, expTmul_smul]

/-- The divided-power exponential `exp(x) = ∑_d γ_d(x) X ^ d` of `x : S ⊗[R] M`, a power series
with coefficients in `S ⊗[R] Γ_R(M)`. It is the additive-to-multiplicative map determined by
`exp(s ⊗ m) = ∑ₙ (s ^ n ⊗ dp R n m) X ^ n` (`coeff_exp_tmul`, `exp_zero`, `exp_add`). -/
def exp (x : S ⊗[R] M) : (S ⊗[R] DividedPowerAlgebra R M)⟦X⟧ :=
  (expAddHom R M S x).toMul

private theorem exp_tmul (s : S) (m : M) : exp (s ⊗ₜ[R] m) = expTmul R s m := by
  rw [exp, expAddHom, liftAddHom_tmul, expTmulHom_apply_apply, toMul_ofMul]

/-- The coefficients of the exponential of a pure tensor:
`exp(s ⊗ m) = ∑ₙ (s ^ n ⊗ dp R n m) X ^ n`. -/
@[simp]
theorem coeff_exp_tmul (s : S) (m : M) (n : ℕ) :
    coeff n (exp (s ⊗ₜ[R] m)) = (s ^ n) ⊗ₜ[R] dp R n m := by
  rw [exp_tmul, coeff_expTmul]

/-- The exponential of `0` is `1`. -/
@[simp]
theorem exp_zero : exp (0 : S ⊗[R] M) = 1 := by
  rw [exp, map_zero, toMul_zero]

/-- The exponential turns sums into products. -/
theorem exp_add (x y : S ⊗[R] M) : exp (x + y) = exp x * exp y := by
  simp only [exp, map_add, toMul_add]

/-- The exponential is natural in the algebra `S`. -/
theorem exp_rTensor {T : Type*} [CommSemiring T] [Algebra R T] (φ : S →ₐ[R] T)
    (x : S ⊗[R] M) :
    exp (φ.toLinearMap.rTensor M x) =
      PowerSeries.map (Algebra.TensorProduct.rTensor (DividedPowerAlgebra R M) φ).toRingHom
        (exp x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
      ext n
      rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, exp_tmul, exp_tmul, coeff_map,
        coeff_expTmul, coeff_expTmul]
      simp
  | add x y hx hy => rw [map_add, exp_add, exp_add, hx, hy, map_mul]

/-- Scalar multiplication by `s` rescales the exponential by `s ⊗ 1`. -/
theorem exp_smul (s : S) (x : S ⊗[R] M) :
    exp (s • x) = rescale (s ⊗ₜ[R] (1 : DividedPowerAlgebra R M)) (exp x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s' m =>
      ext n
      rw [smul_tmul', exp_tmul, exp_tmul, coeff_rescale (R := S ⊗[R] DividedPowerAlgebra R M),
        coeff_expTmul, coeff_expTmul]
      simp [mul_pow]
  | add x y hx hy => rw [smul_add, exp_add, exp_add, hx, hy, map_mul]


/-- The constant coefficient of the exponential is `1`: the divided-power relation `γ₀ = 1`. -/
@[simp]
theorem constantCoeff_exp (x : S ⊗[R] M) : constantCoeff (exp x) = 1 := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_exp_tmul, pow_zero, dp_zero,
        Algebra.TensorProduct.one_def]
  | add x y hx hy => rw [exp_add, map_mul, hx, hy, mul_one]

/-- The coefficients of the exponential multiply like divided powers:
`γₘ(x) * γₙ(x) = (m + n).choose m • γₘ₊ₙ(x)`. -/
theorem coeff_exp_mul_coeff_exp (x : S ⊗[R] M) (m n : ℕ) :
    coeff m (exp x) * coeff n (exp x) = (m + n).choose m • coeff (m + n) (exp x) := by
  induction x using TensorProduct.inductionOn generalizing m n with
  | tmul s a =>
      rw [coeff_exp_tmul, coeff_exp_tmul, coeff_exp_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        ← pow_add, dp_mul, tmul_smul]
  | add x y hx hy =>
      rw [exp_add]
      -- Elaborating the closure lemma before unifying it with the goal avoids a slow unification
      -- of the instance paths on the coefficient ring.
      have h := coeff_mul_coeff_mul_eq_choose_nsmul (A := S ⊗[R] DividedPowerAlgebra R M)
        (f := exp x) (g := exp y)
      exact h hx hy m n

end DividedPowerAlgebra
