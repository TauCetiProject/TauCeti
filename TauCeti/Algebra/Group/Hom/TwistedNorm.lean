/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Finset.Range

/-!
# Twisted norms of monoid endomorphisms

For an endomorphism `τ : M →* M` of a (possibly noncommutative) monoid `M`, the `p`-th **twisted
norm** `MonoidHom.twistedNorm τ p δ` is the ordered product
`δ * τ δ * τ² δ * ... * τ^(p - 1) δ`.

## Main definitions and results

* `MonoidHom.twistedNorm`: the `p`-th twisted norm of `δ` under `τ : M →* M`.
* `MonoidHom.twistedNorm_zero` and `MonoidHom.twistedNorm_succ`: defining recurrence.
* `MonoidHom.map_twistedNorm`: a monoid homomorphism intertwining `τ` and `τ'` carries
  `twistedNorm τ` to `twistedNorm τ'`.
* `MonoidHom.twistedNorm_eq_prod_iterate`: in a commutative monoid, `twistedNorm τ p δ` equals
  `∏ i ∈ Finset.range p, τ^[i] δ`.
* `MonoidHom.twistedNorm_ringHom_eq_prod_pow`: for a ring endomorphism `σ : R →+* R` of a
  commutative semiring, `twistedNorm (σ : R →* R) p x` equals `∏ i ∈ Finset.range p, (σ ^ i) x`.
-/

public section

open Finset

namespace MonoidHom

variable {M N : Type*} [Monoid M] [Monoid N]

/-- The **twisted norm** `δ * τ δ * τ² δ * ... * τ^(p - 1) δ` of an element `δ` of a monoid `M`
under an endomorphism `τ : M →* M`. -/
def twistedNorm (τ : M →* M) : ℕ → M → M
  | 0, _ => 1
  | p + 1, δ => δ * τ (twistedNorm τ p δ)

/-- The `0`-th twisted norm is `1`. -/
@[simp]
theorem twistedNorm_zero (τ : M →* M) (δ : M) : twistedNorm τ 0 δ = 1 :=
  (rfl)

/-- The `(p + 1)`-st twisted norm satisfies `N_{p+1}(δ) = δ * τ (N_p(δ))`. -/
@[simp]
theorem twistedNorm_succ (τ : M →* M) (p : ℕ) (δ : M) :
    twistedNorm τ (p + 1) δ = δ * τ (twistedNorm τ p δ) :=
  (rfl)

/-- A monoid homomorphism `f : M →* N` intertwining `τ : M →* M` and `τ' : N →* N` carries
`twistedNorm τ` to `twistedNorm τ'`. -/
theorem map_twistedNorm (f : M →* N) {τ : M →* M} {τ' : N →* N}
    (h : ∀ x : M, f (τ x) = τ' (f x)) (p : ℕ) (δ : M) :
    f (twistedNorm τ p δ) = twistedNorm τ' p (f δ) := by
  induction p with
  | zero => simp
  | succ p ih => rw [twistedNorm_succ, twistedNorm_succ, map_mul, h, ih]

/-- In a commutative monoid, the twisted norm equals `∏ i ∈ range p, τ^[i] δ`. -/
theorem twistedNorm_eq_prod_iterate {C : Type*} [CommMonoid C] (τ : C →* C) (p : ℕ) (δ : C) :
    twistedNorm τ p δ = ∏ i ∈ range p, τ^[i] δ := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [twistedNorm_succ]
    simp [ih, map_prod, prod_range_succ', mul_comm, Function.iterate_succ_apply']

/-- For a ring endomorphism `σ` of a commutative semiring, the twisted norm equals
`∏ i ∈ range p, (σ ^ i) x`. -/
theorem twistedNorm_ringHom_eq_prod_pow {R : Type*} [CommSemiring R] (σ : R →+* R) (p : ℕ)
    (x : R) :
    twistedNorm (σ : R →* R) p x = ∏ i ∈ range p, (σ ^ i) x := by
  rw [twistedNorm_eq_prod_iterate]
  refine prod_congr rfl fun i _ ↦ ?_
  simp [RingHom.coe_pow]

end MonoidHom
