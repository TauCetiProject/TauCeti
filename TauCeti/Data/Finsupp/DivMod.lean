/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Fin.Basic

/-!
# Entrywise division with remainder of exponents

Dividing every entry of an exponent `α : σ →₀ ℕ` by `p` with remainder writes `α` as
`p • μ + ν` with `ν i < p` for all `i`, where `μ` and `ν` are the entrywise quotients and
remainders. For `0 < p` the pair of remainders, valued in `Fin p`, and quotients determines `α`.

## Main definitions

* `Finsupp.modDivEquiv`: for `0 < p`, the equivalence `α ↦ (α % p, α / p)` between `σ →₀ ℕ` and
  `(σ →₀ Fin p) × (σ →₀ ℕ)`.

## Main results

* `Finsupp.nsmul_mapRange_div_add_mapRange_mod`: `p • (α / p) + α % p = α` entrywise.
* `Finsupp.modDivEquiv_nsmul_add`: adding `p • γ` keeps the remainders and adds `γ` to the
  quotients.
-/

public section

namespace Finsupp

variable {σ : Type*} (p : ℕ)

/-- Every exponent is `p • μ + ν` for its entrywise quotients `μ` and remainders `ν` by `p`. -/
theorem nsmul_mapRange_div_add_mapRange_mod (α : σ →₀ ℕ) :
    p • α.mapRange (· / p) (Nat.zero_div p) + α.mapRange (· % p) (Nat.zero_mod p) = α := by
  ext i
  simp [Nat.div_add_mod]

section ModDivEquiv

variable [NeZero p]

/-- For `0 < p`, an exponent `α` is determined by its entrywise remainders by `p`, valued in
`Fin p`, and its entrywise quotients by `p`: `α = p • (α / p) + α % p`. -/
noncomputable def modDivEquiv : (σ →₀ ℕ) ≃ (σ →₀ Fin p) × (σ →₀ ℕ) where
  toFun α := (α.mapRange (Fin.ofNat p) (Fin.ofNat_zero p), α.mapRange (· / p) (Nat.zero_div p))
  invFun βγ := βγ.1.mapRange Fin.val (Fin.val_zero p) + p • βγ.2
  left_inv α := by
    ext i
    simp [Nat.mod_add_div]
  right_inv βγ := by
    have hp : 0 < p := Nat.pos_of_neZero p
    ext i
    · simp [Nat.mod_eq_of_lt (βγ.1 i).isLt]
    · simp [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (βγ.1 i).isLt]

/-- The first component of `modDivEquiv p α` is the vector of remainders of `α` by `p`. -/
@[simp]
theorem modDivEquiv_apply_fst (α : σ →₀ ℕ) :
    (modDivEquiv p α).1 = α.mapRange (Fin.ofNat p) (Fin.ofNat_zero p) :=
  (rfl)

/-- The second component of `modDivEquiv p α` is the vector of quotients of `α` by `p`. -/
@[simp]
theorem modDivEquiv_apply_snd (α : σ →₀ ℕ) :
    (modDivEquiv p α).2 = α.mapRange (· / p) (Nat.zero_div p) :=
  (rfl)

/-- The inverse of `modDivEquiv p` sends remainders `β` and quotients `γ` to `β + p • γ`. -/
@[simp]
theorem modDivEquiv_symm_apply (βγ : (σ →₀ Fin p) × (σ →₀ ℕ)) :
    (modDivEquiv p).symm βγ = βγ.1.mapRange Fin.val (Fin.val_zero p) + p • βγ.2 :=
  (rfl)

/-- Adding `p • γ` to an exponent keeps its remainders by `p` and adds `γ` to its quotients. -/
theorem modDivEquiv_nsmul_add (γ α : σ →₀ ℕ) :
    modDivEquiv p (p • γ + α) = ((modDivEquiv p α).1, γ + (modDivEquiv p α).2) := by
  have hp : 0 < p := Nat.pos_of_neZero p
  ext i
  · simp
  · simp [Nat.mul_add_div hp]

end ModDivEquiv

end Finsupp
