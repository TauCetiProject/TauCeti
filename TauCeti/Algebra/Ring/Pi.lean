/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.Data.Fintype.EquivFin

/-!
# Ring homomorphisms from a finite product into a domain

A ring homomorphism `φ` from a finite product `∏ i, R i` into a domain `S` factors through one
of the projections. The standard idempotents `eᵢ = Pi.single i 1` are orthogonal and sum to `1`,
so exactly one of them is sent to `1` and the others to `0`; then `φ x = φ (x * eᵢ)` only
depends on the coordinate `x i`.

## Main results

* `RingHom.exists_eq_comp_evalRingHom`: a ring homomorphism from a finite product into a domain
  is `ψ ∘ evalᵢ` for some coordinate `i` and some ring homomorphism `ψ : R i →+* S`.
-/

public section

namespace RingHom

variable {ι : Type*} [Finite ι] {R : ι → Type*} [∀ i, Semiring (R i)] {S : Type*} [Semiring S]
  [IsDomain S]

/-- A ring homomorphism from a finite product into a domain factors through one of the
projections. -/
theorem exists_eq_comp_evalRingHom (φ : (∀ i, R i) →+* S) :
    ∃ i, ∃ ψ : R i →+* S, φ = ψ.comp (Pi.evalRingHom R i) := by
  classical
  have := Fintype.ofFinite ι
  -- Some standard idempotent `Pi.single i 1` is not killed by `φ`, since they add up to `1`.
  obtain ⟨i, hi⟩ : ∃ i, φ (Pi.single i 1) ≠ 0 := by
    by_contra! h
    have h1 : φ (∑ i, Pi.single i 1) = 0 := by simp [map_sum, h]
    rw [Finset.univ_sum_single, show (fun i ↦ (1 : R i)) = 1 from rfl, map_one] at h1
    exact one_ne_zero h1
  -- Being idempotent and nonzero in a domain, its image is `1`.
  have hi1 : φ (Pi.single i 1) = 1 := by
    have he : IsIdempotentElem (φ (Pi.single i 1)) := by
      rw [IsIdempotentElem, ← map_mul, ← Pi.single_mul, mul_one]
    exact (IsIdempotentElem.iff_eq_zero_or_one.mp he).resolve_left hi
  -- Hence `φ x = φ (x * Pi.single i 1) = φ (Pi.single i (x i))`.
  have hx (x : ∀ i, R i) : φ x = φ (Pi.single i (x i)) := by
    rw [← mul_one (x i), Pi.single_mul_right, map_mul, hi1, mul_one]
  let ψ : R i →+* S :=
    { toFun := fun y ↦ φ (Pi.single i y)
      map_one' := hi1
      map_mul' := fun y z ↦ by simp only [Pi.single_mul, map_mul]
      map_zero' := by simp
      map_add' := fun y z ↦ by simp [Pi.single_add] }
  exact ⟨i, ψ, RingHom.ext hx⟩

end RingHom
