/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Finite-product perfect pairings

Given a finite family of bilinear pairings `p i : M i →ₗ[R] N i →ₗ[R] R` over a commutative
semiring `R`, summing coordinate evaluations defines `LinearMap.piPairing p`, which is perfect
whenever every `p i` is perfect (`LinearMap.piPairing_isPerfPair`).
-/

public section

open Function

namespace LinearMap

variable {R : Type*} [CommSemiring R] {ι : Type*} [Fintype ι] {M N : ι → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

/-- The bilinear pairing on finite dependent products obtained by summing coordinate pairings. -/
def piPairing (p : ∀ i, M i →ₗ[R] N i →ₗ[R] R) : (∀ i, M i) →ₗ[R] (∀ i, N i) →ₗ[R] R :=
  LinearMap.mk₂ R (fun x y ↦ ∑ i, p i (x i) (y i))
    (fun _ _ _ ↦ by simp [← Finset.sum_add_distrib])
    (fun _ _ _ ↦ by simp [smul_eq_mul, Finset.mul_sum])
    (fun _ _ _ ↦ by simp [← Finset.sum_add_distrib])
    (fun _ _ _ ↦ by simp [smul_eq_mul, Finset.mul_sum])

/-- `LinearMap.piPairing` evaluates to the sum of the coordinate pairings. -/
@[simp] theorem piPairing_apply (p : ∀ i, M i →ₗ[R] N i →ₗ[R] R) (x : ∀ i, M i) (y : ∀ i, N i) :
    piPairing p x y = ∑ i, p i (x i) (y i) := (rfl)

/-- Flipping `LinearMap.piPairing` flips every coordinate pairing. -/
@[simp] theorem flip_piPairing (p : ∀ i, M i →ₗ[R] N i →ₗ[R] R) :
    (piPairing p).flip = piPairing fun i ↦ (p i).flip := by ext y x; simp

private theorem piPairing_bijective_left (p : ∀ i, M i →ₗ[R] N i →ₗ[R] R)
    [∀ i, (p i).IsPerfPair] : Bijective (piPairing p) := by
  classical
  have hsingle (x : ∀ i, M i) (i : ι) (n : N i) : piPairing p x (Pi.single i n) = p i (x i) n := by
    rw [piPairing_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Pi.single_eq_of_ne hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  refine ⟨fun x₁ x₂ hx ↦ funext fun i ↦ (IsPerfPair.bijective_left (p i)).injective <|
    LinearMap.ext fun n ↦ by simpa only [hsingle] using DFunLike.congr_fun hx (Pi.single i n),
    fun φ ↦ ⟨fun i ↦ (p i).toPerfPair.symm (φ.comp (LinearMap.single R N i)),
      LinearMap.ext fun y ↦ ?_⟩⟩
  conv_rhs => rw [← Finset.univ_sum_single y, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ DFunLike.congr_fun ((p i).apply_symm_toPerfPair_self _) (y i)

/-- A finite product of perfect pairings is a perfect pairing. -/
instance piPairing_isPerfPair (p : ∀ i, M i →ₗ[R] N i →ₗ[R] R) [∀ i, (p i).IsPerfPair] :
    (piPairing p).IsPerfPair :=
  ⟨piPairing_bijective_left p, flip_piPairing p ▸ piPairing_bijective_left fun i ↦ (p i).flip⟩

end LinearMap
