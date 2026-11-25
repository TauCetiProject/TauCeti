/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Padics.ContinuousMapLattice

/-!
# Checks: continuous maps into `V` land in a lattice

Checks of ArithmeticGaloisDuality R02.1.3 (*Continuous cochains into `V` land in a lattice*) for
`T = ℤ_p` inside `V = ℚ_p`, the `ℤ_p`-span of the basis `1`.

* For `X = ℤ_p`, the map `x ↦ x / p` lands in `p⁻¹ ℤ_p` and not in `ℤ_p`.
* Compactness is needed: on the discrete noncompact space `ℕ`, the continuous map `n ↦ p^{-n}`
  lands in no `p^{-n} ℤ_p`.
* For empty `X`, both `C(X, ℤ_p)` and `C(X, ℚ_p)` are zero.
-/

open TauCeti

variable (p : ℕ) [Fact p.Prime]

example : IsOpen ((Submodule.span ℤ_[p] (Set.range (Module.Basis.singleton Unit ℚ_[p])) :
    Submodule ℤ_[p] ℚ_[p]) : Set ℚ_[p]) :=
  isOpen_span_range_basis_padicInt _

/-- `x ↦ x / p` on `ℤ_p` lands in `p⁻¹ ℤ_p`. -/
example : ∀ x : ℤ_[p], (p : ℤ_[p]) ^ 1 • ((x : ℚ_[p]) / p) ∈
    Submodule.span ℤ_[p] (Set.range (Module.Basis.singleton Unit ℚ_[p])) := by
  intro x
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [mem_span_range_basis_padicInt_iff, Unique.forall_iff, Module.Basis.singleton_repr,
    ← algebraMap_smul ℚ_[p], smul_eq_mul, pow_one, PadicInt.algebraMap_apply,
    PadicInt.coe_natCast, mul_div_cancel₀ _ hp]
  exact x.norm_le_one

/-- `x ↦ x / p` on `ℤ_p` does not land in `ℤ_p`: its value at `1` is `1 / p`. -/
example : ((1 : ℤ_[p]) : ℚ_[p]) / p ∉
    Submodule.span ℤ_[p] (Set.range (Module.Basis.singleton Unit ℚ_[p])) := by
  rw [mem_span_range_basis_padicInt_iff, Unique.forall_iff, Module.Basis.singleton_repr,
    PadicInt.coe_one, norm_div, norm_one, Padic.norm_p, one_div, inv_inv, not_le]
  exact_mod_cast (Fact.out : p.Prime).one_lt

/-- Compactness is needed: on the discrete space `ℕ`, `n ↦ p^{-n}` lands in no `p^{-n} ℤ_p`. -/
example : ¬ ∃ n : ℕ, ∀ m : ℕ, (p : ℤ_[p]) ^ n • ((p : ℚ_[p]) ^ m)⁻¹ ∈
    Submodule.span ℤ_[p] (Set.range (Module.Basis.singleton Unit ℚ_[p])) := by
  rintro ⟨n, hn⟩
  have h := hn (n + 1)
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [mem_span_range_basis_padicInt_iff, Unique.forall_iff, Module.Basis.singleton_repr,
    ← algebraMap_smul ℚ_[p], smul_eq_mul, map_pow, PadicInt.algebraMap_apply,
    PadicInt.coe_natCast, pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hp),
    one_mul, norm_inv, Padic.norm_p, inv_inv] at h
  exact (not_le.2 (by exact_mod_cast (Fact.out : p.Prime).one_lt)) h

/-- For empty `X`, `C(X, ℚ_p)` is zero. -/
example {X : Type*} [TopologicalSpace X] [IsEmpty X] : Subsingleton C(X, ℚ_[p]) :=
  inferInstance

/-- For empty `X`, `C(X, ℤ_p)` is zero. -/
example {X : Type*} [TopologicalSpace X] [IsEmpty X] :
    Subsingleton C(X, Submodule.span ℤ_[p] (Set.range (Module.Basis.singleton Unit ℚ_[p]))) :=
  inferInstance
