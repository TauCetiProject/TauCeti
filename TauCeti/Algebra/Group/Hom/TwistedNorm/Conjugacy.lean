/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Hom.TwistedNorm
import Mathlib.Algebra.Group.Basic
import Mathlib.Logic.Function.Iterate

/-!
# Twisted-conjugacy equivariance of twisted norms

For a group endomorphism `τ : G →* G` and `p : ℕ`, the `p`-th twisted norm
`MonoidHom.twistedNorm τ p δ = δ * τ δ * ⋯ * τ^[p - 1] δ` intertwines `τ`-twisted conjugacy
`δ ↦ x⁻¹ * δ * τ x` with `x⁻¹ * (·) * τ^[p] x`. When `τ^[p] x = x`, twisted conjugacy on `δ`
induces ordinary conjugacy on `MonoidHom.twistedNorm τ p δ`.

## Main results

* `TauCeti.twistedNorm_one`: the twisted norm of `1` is `1`.
* `TauCeti.twistedNorm_inv_mul_mul_apply`:
  `twistedNorm τ p (x⁻¹ * δ * τ x) = x⁻¹ * twistedNorm τ p δ * τ^[p] x`.
* `TauCeti.twistedNorm_inv_mul_mul_of_iterate_eq`: if `τ^[p] x = x`, then
  `twistedNorm τ p (x⁻¹ * δ * τ x) = x⁻¹ * twistedNorm τ p δ * x`.
* `TauCeti.twistedNorm_mul_apply_inv_of_iterate_eq`: if `τ^[p] x = x`, then
  `twistedNorm τ p (x * δ * (τ x)⁻¹) = x * twistedNorm τ p δ * x⁻¹`.

## References

* Provenance: adapted from `New.twistedNorm_inv_mul_mul_galoisGf` in
  `grh/src/Lib/GaloisRep/BaseChange/TwistedTraceIdentity.lean` of `grh-lean`
  (https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`).
-/

public section

namespace TauCeti

/-- The twisted norm of `1` is `1`. -/
@[simp]
theorem twistedNorm_one {M : Type*} [Monoid M] (τ : M →* M) (p : ℕ) :
    MonoidHom.twistedNorm τ p 1 = 1 := by
  induction p with
  | zero => exact MonoidHom.twistedNorm_zero τ 1
  | succ p ih => simp [MonoidHom.twistedNorm_succ, ih]

variable {G : Type*} [Group G]

/-- Twisted-conjugacy telescoping formula for `MonoidHom.twistedNorm`:
`twistedNorm τ p (x⁻¹ * δ * τ x) = x⁻¹ * twistedNorm τ p δ * τ^[p] x`. -/
theorem twistedNorm_inv_mul_mul_apply (τ : G →* G) (p : ℕ) (x δ : G) :
    MonoidHom.twistedNorm τ p (x⁻¹ * δ * τ x) =
      x⁻¹ * MonoidHom.twistedNorm τ p δ * τ^[p] x := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [MonoidHom.twistedNorm_succ, ih, MonoidHom.twistedNorm_succ, map_mul, map_mul, map_inv,
      Function.iterate_succ_apply']
    simp [mul_assoc]

/-- If `τ^[p] x = x`, then `MonoidHom.twistedNorm τ p` sends the `τ`-twisted conjugate
`x⁻¹ * δ * τ x` to the ordinary conjugate `x⁻¹ * twistedNorm τ p δ * x`. -/
theorem twistedNorm_inv_mul_mul_of_iterate_eq (τ : G →* G) (p : ℕ) {x : G}
    (hx : τ^[p] x = x) (δ : G) :
    MonoidHom.twistedNorm τ p (x⁻¹ * δ * τ x) =
      x⁻¹ * MonoidHom.twistedNorm τ p δ * x := by
  rw [twistedNorm_inv_mul_mul_apply, hx]

/-- Reversed-orientation variant: if `τ^[p] x = x`, then
`twistedNorm τ p (x * δ * (τ x)⁻¹) = x * twistedNorm τ p δ * x⁻¹`. -/
theorem twistedNorm_mul_apply_inv_of_iterate_eq (τ : G →* G) (p : ℕ) {x : G}
    (hx : τ^[p] x = x) (δ : G) :
    MonoidHom.twistedNorm τ p (x * δ * (τ x)⁻¹) =
      x * MonoidHom.twistedNorm τ p δ * x⁻¹ := by
  have hx' : τ^[p] x⁻¹ = x⁻¹ := by
    have h_iter : ∀ n : ℕ, τ^[n] x⁻¹ = (τ^[n] x)⁻¹ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ih, map_inv, Function.iterate_succ_apply']
    rw [h_iter, hx]
  simpa [map_inv] using twistedNorm_inv_mul_mul_of_iterate_eq τ p hx' δ

end TauCeti
