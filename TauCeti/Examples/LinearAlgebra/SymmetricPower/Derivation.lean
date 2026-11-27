/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.FinTwo
import Mathlib.Data.ZMod.Basic

/-!
# Jordan blocks of the differential of a symmetric power

Checks of `TauCeti.LinearAlgebra.SymmetricPower.Derivation` on `M = R²` with standard basis
`e₁ = Pi.single 0 1`, `e₂ = Pi.single 1 1` and the nilpotent endomorphism `N` with `N e₂ = e₁`,
`N e₁ = 0`. Write `f n j = e₁^{n-j} e₂^j` for the pure symmetric tensor of degree `n` with `n - j`
factors `e₁` followed by `j` factors `e₂`.

* `d Symⁿ(N) (f n (j + 1)) = (j + 1) • f n j` over every commutative ring: the monomials
  `f n 0, …, f n n` form a single Jordan block of size `n + 1` when the integers `1, …, n` are
  invertible.
* For `Sym²` over `ℚ`, `N² = 0` but `d Sym²(N)² ≠ 0`, while `d Sym²(N)³ = 0`: the nilpotency order
  of the differential is that of a Jordan block of size `3`, not that of `N`. Only the unipotence of
  `Sym²(exp N)` is transported, as `Sym²(exp N) = exp (d Sym²(N))`.
* Over `𝔽₃`, `d Sym³(N)` kills both `f 3 3 = e₂³` (since `3 = 0`) and `f 3 0 = e₁³`, so the
  monomials do not form a single Jordan block of size `4`; over `ℚ` it does not kill `e₂³`.
-/

public section

open scoped TensorProduct
open SymmetricPower

namespace TauCeti.Examples

variable {R : Type*} [CommRing R]

/-- The nilpotent endomorphism of `R²` with `N e₂ = e₁` and `N e₁ = 0`. -/
noncomputable abbrev nilpotentTwo (R : Type*) [CommRing R] : Module.End R (Fin 2 → R) :=
  LinearMap.single R (fun _ ↦ R) 0 ∘ₗ LinearMap.proj 1

/-- **The differential on monomials**: `d Symⁿ(N) (e₁^{n-j-1} e₂^{j+1}) = (j + 1) • e₁^{n-j} e₂^j`.
The monomials form a single Jordan block of size `n + 1` only when `1, …, n` are invertible in
`R`. -/
theorem differential_nilpotentTwo_symFinTwoMonomial {n j : ℕ} (hj : j + 1 ≤ n) :
    differential R _ n (nilpotentTwo R) (symFinTwoMonomial R n (j + 1)) =
      (j + 1) • symFinTwoMonomial R n j := by
  apply toSymmetricAlgebra_injective n
  obtain ⟨m, rfl⟩ : ∃ m, n = j + 1 + m := ⟨n - (j + 1), by omega⟩
  rw [toSymmetricAlgebra_differential, map_nsmul, toSymmetricAlgebra_symFinTwoMonomial hj,
    toSymmetricAlgebra_symFinTwoMonomial (by omega)]
  simp [Derivation.leibniz, Derivation.leibniz_pow, show j + 1 + m - j = m + 1 by omega]
  ring

/-- `N² = 0`. -/
theorem nilpotentTwo_sq : nilpotentTwo R ^ 2 = 0 := by
  ext x i
  fin_cases i <;> simp [pow_two, Pi.single_apply]

/-- `d Sym²(N)³ = 0`. -/
example : differential R _ 2 (nilpotentTwo R) ^ 3 = 0 :=
  differential_pow_eq_zero 2 (k := 2) nilpotentTwo_sq

/-- `d Sym²(N)² ≠ 0` over `ℚ`: it sends `e₂²` to `2 e₁²`. -/
example : differential ℚ _ 2 (nilpotentTwo ℚ) ^ 2 ≠ 0 := by
  intro h
  have h₂ := congr($h (symFinTwoMonomial ℚ 2 2))
  rw [pow_two, mul_apply_eq_comp, differential_nilpotentTwo_symFinTwoMonomial le_rfl, map_nsmul,
    differential_nilpotentTwo_symFinTwoMonomial (by norm_num), LinearMap.zero_apply] at h₂
  rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul] at h₂
  exact smul_ne_zero (by norm_num) (symFinTwoMonomial_ne_zero _ _) h₂

/-- Over `𝔽₃`, `d Sym³(N)` kills `e₂³`. -/
example :
    differential (ZMod 3) _ 3 (nilpotentTwo (ZMod 3)) (symFinTwoMonomial (ZMod 3) 3 3) = 0 := by
  rw [differential_nilpotentTwo_symFinTwoMonomial le_rfl]
  rw [← Nat.cast_smul_eq_nsmul (ZMod 3), show ((2 + 1 : ℕ) : ZMod 3) = 0 by decide, zero_smul]

/-- `d Sym³(N)` kills `e₁³`. -/
example : differential R _ 3 (nilpotentTwo R) (symFinTwoMonomial R 3 0) = 0 := by
  apply toSymmetricAlgebra_injective 3
  simp [toSymmetricAlgebra_differential, toSymmetricAlgebra_symFinTwoMonomial,
    Derivation.leibniz_pow]

/-- Over `ℚ`, `d Sym³(N)` does not kill `e₂³`. -/
example : differential ℚ _ 3 (nilpotentTwo ℚ) (symFinTwoMonomial ℚ 3 3) ≠ 0 := by
  rw [differential_nilpotentTwo_symFinTwoMonomial le_rfl, ← Nat.cast_smul_eq_nsmul ℚ]
  exact smul_ne_zero (by norm_num) (symFinTwoMonomial_ne_zero _ _)

end TauCeti.Examples
