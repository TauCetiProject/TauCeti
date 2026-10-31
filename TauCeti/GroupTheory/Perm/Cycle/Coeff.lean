/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Cycle.Enumeration
public import TauCeti.GroupTheory.Perm.SumCongr

/-!
# Cycle coefficients and monodromy of a weighted permutation

Let `π` be a permutation of `α` and `s : α → M` weights in a commutative monoid. Along the cycle
`x, π x, π² x, …` of a point `x`, the cycle coefficients are the prefix products
`c_r = s x * s (π x) * ⋯ * s (π ^ (r - 1) x)` (`Equiv.Perm.cycleCoeff`), and the monodromy of `x`
is `c_l` for the length `l` of its cycle (`Equiv.Perm.monodromy`), the product of `s` over the cycle
(`Equiv.Perm.monodromy_eq_prod`). If a linear map sends each vector `v i` of a family to
`s i • v (π i)`, its `r`-th iterate sends `v x` to `c_r • v (π ^ r x)`
(`Module.End.pow_apply_of_apply_eq_smul`).

## Main definitions

* `Equiv.Perm.cycleCoeff`: the cycle coefficients of a point.
* `Equiv.Perm.monodromy`: the monodromy of a point.

## Main results

* `Equiv.Perm.monodromy_eq_prod`: the monodromy is the product of the weights over the cycle.
* `Equiv.Perm.map_cycleCoeff`: monoid homomorphisms commute with the cycle coefficients.
* `Equiv.Perm.cycleCoeff_sumCongr_inl`, `Equiv.Perm.cycleCoeff_sumCongr_inr`: the cycle
  coefficients of a sum permutation.
-/

public section

open Function

namespace Equiv.Perm

variable {α M : Type*} [CommMonoid M] (π : Perm α) (s : α → M)

/-! ### Cycle coefficients and monodromy -/

/-- The cycle coefficient `c_r = s x * s (π x) * ⋯ * s (π ^ (r - 1) x)` of a point `x`: the
product of the weights `s` over the first `r` points of the cycle of `x` under `π`. -/
def cycleCoeff (x : α) (r : ℕ) : M :=
  ∏ k ∈ Finset.range r, s ((π ^ k) x)

theorem cycleCoeff_def (x : α) (r : ℕ) :
    π.cycleCoeff s x r = ∏ k ∈ Finset.range r, s ((π ^ k) x) :=
  (rfl)

@[simp]
theorem cycleCoeff_zero (x : α) : π.cycleCoeff s x 0 = 1 := by
  simp [cycleCoeff_def]

theorem cycleCoeff_succ (x : α) (r : ℕ) :
    π.cycleCoeff s x (r + 1) = π.cycleCoeff s x r * s ((π ^ r) x) := by
  simp [cycleCoeff_def, Finset.prod_range_succ]

@[simp]
theorem cycleCoeff_one (x : α) (r : ℕ) : π.cycleCoeff (1 : α → M) x r = 1 := by
  simp [cycleCoeff_def]

/-- The monodromy of a point `x`: its cycle coefficient at the length
`Function.minimalPeriod π x` of its cycle, which is the product of the weights over the cycle
(`Equiv.Perm.monodromy_eq_prod`). -/
noncomputable def monodromy (x : α) : M :=
  π.cycleCoeff s x (minimalPeriod π x)

theorem monodromy_def (x : α) : π.monodromy s x = π.cycleCoeff s x (minimalPeriod π x) :=
  (rfl)

@[simp]
theorem monodromy_one (x : α) : π.monodromy (1 : α → M) x = 1 :=
  π.cycleCoeff_one x _

/-- The monodromy of a point is the product of the weights over the points of its cycle; in
particular it only depends on the cycle. -/
theorem monodromy_eq_prod [Fintype α] [DecidableRel π.SameCycle] (x : α) :
    π.monodromy s x = ∏ y with π.SameCycle x y, s y :=
  π.prod_range_minimalPeriod s x

/-- A monoid homomorphism commutes with the cycle coefficients. -/
theorem map_cycleCoeff {N F : Type*} [CommMonoid N] [FunLike F M N] [MonoidHomClass F M N] (φ : F)
    (x : α) (r : ℕ) : φ (π.cycleCoeff s x r) = π.cycleCoeff (φ ∘ s) x r := by
  simp [cycleCoeff_def]

section SumCongr

variable {β : Type*} (τ : Perm β) (t : β → M)

/-- The cycle coefficients of a point of the left summand under a sum permutation are those
under the left permutation. -/
@[simp]
theorem cycleCoeff_sumCongr_inl (x : α) (r : ℕ) :
    (sumCongr π τ).cycleCoeff (Sum.elim s t) (.inl x) r = π.cycleCoeff s x r := by
  simp [cycleCoeff_def]

/-- The cycle coefficients of a point of the right summand under a sum permutation are those
under the right permutation. -/
@[simp]
theorem cycleCoeff_sumCongr_inr (y : β) (r : ℕ) :
    (sumCongr π τ).cycleCoeff (Sum.elim s t) (.inr y) r = τ.cycleCoeff t y r := by
  simp [cycleCoeff_def]

@[simp]
theorem monodromy_sumCongr_inl (x : α) :
    (sumCongr π τ).monodromy (Sum.elim s t) (.inl x) = π.monodromy s x := by
  simp [monodromy_def]

@[simp]
theorem monodromy_sumCongr_inr (y : β) :
    (sumCongr π τ).monodromy (Sum.elim s t) (.inr y) = τ.monodromy t y := by
  simp [monodromy_def]

end SumCongr

end Equiv.Perm
