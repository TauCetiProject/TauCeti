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
# Finite-product and unit-scaled perfect pairings

Given a finite family of bilinear pairings `p i : M i →ₗ[R] N i →ₗ[R] R` over a commutative
semiring `R`, summing their coordinate evaluations defines a bilinear pairing
`LinearMap.piPairing p` between `(∀ i, M i)` and `(∀ i, N i)`. When each coordinate pairing is
perfect, the product pairing is perfect as well: coordinate inclusions `Pi.single` recover each
factor on the nose, and expanding any tuple as the finite sum of its single-coordinate pieces
reconstructs every functional on `(∀ i, N i)`.

We also record that scaling a perfect pairing by a unit scalar, negation, or a sign unit `ℤˣ`
preserves `LinearMap.IsPerfPair`.

## Main definitions and results

* `LinearMap.piPairing`: coordinatewise sum pairing `(x, y) ↦ ∑ i, p i (x i) (y i)`.
* `LinearMap.piPairing_isPerfPair`: `piPairing p` is perfect when every `p i` is perfect.
* `LinearMap.IsPerfPair.smul_of_isUnit`, `LinearMap.IsPerfPair.units_smul`,
  `LinearMap.IsPerfPair.neg`, `LinearMap.IsPerfPair.intUnits_smul`: invariance of perfectness
  under unit scaling and signs.
-/

public section

open Function

namespace LinearMap

section CommSemiring

variable {R : Type*} [CommSemiring R]

section UnitScale

variable {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Scaling a perfect pairing by a unit of the base commutative semiring preserves perfectness. -/
theorem IsPerfPair.smul_of_isUnit {c : R} (hc : IsUnit c) (p : M →ₗ[R] N →ₗ[R] R)
    [p.IsPerfPair] : (c • p).IsPerfPair := by
  obtain ⟨u, rfl⟩ := hc
  have hEq : (u : R) • p =
      p.compl₁₂ (LinearEquiv.smulOfUnit u).toLinearMap (LinearEquiv.refl R N).toLinearMap := by
    apply LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
    simp only [compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.refl_apply,
      LinearEquiv.smulOfUnit, DistribMulAction.toLinearEquiv_apply, Units.smul_def, map_smul]
    rfl
  rw [hEq]
  infer_instance

/-- Scaling a perfect pairing by `u : Rˣ` preserves perfectness. -/
instance IsPerfPair.units_smul (u : Rˣ) (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair] :
    (u • p).IsPerfPair := by
  rw [Units.smul_def]
  exact IsPerfPair.smul_of_isUnit u.isUnit p

end UnitScale

section Pi

variable {ι : Type*} [Fintype ι] {M N : ι → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

/-- The bilinear pairing on finite dependent products obtained by summing coordinate pairings. -/
def piPairing (p : ∀ i, M i →ₗ[R] N i →ₗ[R] R) :
    (∀ i, M i) →ₗ[R] (∀ i, N i) →ₗ[R] R :=
  LinearMap.mk₂ R (fun x y ↦ ∑ i, p i (x i) (y i))
    (fun x₁ x₂ y ↦ by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by simp only [Pi.add_apply, map_add]; rfl)
    (fun r x y ↦ by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by simp only [Pi.smul_apply, map_smul]; rfl)
    (fun x y₁ y₂ ↦ by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by simp only [Pi.add_apply, map_add])
    (fun r x y ↦ by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by simp only [Pi.smul_apply, map_smul, smul_eq_mul])

/-- `LinearMap.piPairing` evaluates to the sum of the coordinate pairings. -/
@[simp]
theorem piPairing_apply (p : ∀ i, M i →ₗ[R] N i →ₗ[R] R) (x : ∀ i, M i) (y : ∀ i, N i) :
    piPairing p x y = ∑ i, p i (x i) (y i) :=
  (rfl)

/-- Flipping `LinearMap.piPairing` flips every coordinate pairing. -/
@[simp]
theorem flip_piPairing (p : ∀ i, M i →ₗ[R] N i →ₗ[R] R) :
    (piPairing p).flip = piPairing fun i ↦ (p i).flip := by
  apply LinearMap.ext fun y ↦ LinearMap.ext fun x ↦ ?_
  simp only [flip_apply, piPairing_apply]

private theorem piPairing_bijective_left (p : ∀ i, M i →ₗ[R] N i →ₗ[R] R)
    [∀ i, (p i).IsPerfPair] : Bijective (piPairing p) := by
  classical
  have hsingle (x : ∀ i, M i) (i : ι) (n : N i) :
      piPairing p x (Pi.single i n) = p i (x i) n := by
    rw [piPairing_apply, Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same]
    · intro j _ hji
      simp only [Pi.single_eq_of_ne hji, map_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  refine ⟨fun x₁ x₂ hx ↦ funext fun i ↦ ?_, fun φ ↦ ?_⟩
  · apply (IsPerfPair.bijective_left (p i)).injective
    apply LinearMap.ext fun n ↦ ?_
    simpa only [hsingle] using DFunLike.congr_fun hx (Pi.single i n)
  · refine ⟨fun i ↦ (p i).toPerfPair.symm (φ.comp (LinearMap.single R N i)), ?_⟩
    apply LinearMap.ext fun y ↦ ?_
    have hy : (∑ i : ι, Pi.single i (y i)) = y := Finset.univ_sum_single y
    conv_rhs => rw [← hy]
    rw [map_sum, piPairing_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hi : p i (((p i).toPerfPair.symm) (φ.comp (LinearMap.single R N i))) (y i) =
        (φ.comp (LinearMap.single R N i)) (y i) :=
      DFunLike.congr_fun ((p i).apply_symm_toPerfPair_self _) (y i)
    rw [hi, comp_apply, single_apply]

/-- A finite product of perfect pairings is a perfect pairing. -/
instance piPairing_isPerfPair (p : ∀ i, M i →ₗ[R] N i →ₗ[R] R) [∀ i, (p i).IsPerfPair] :
    (piPairing p).IsPerfPair where
  bijective_left := piPairing_bijective_left p
  bijective_right := by
    rw [flip_piPairing]
    exact piPairing_bijective_left fun i ↦ (p i).flip

end Pi

end CommSemiring

section CommRing

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Negating a perfect pairing preserves perfectness. -/
instance IsPerfPair.neg (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair] : (-p).IsPerfPair := by
  rw [← neg_one_smul R p]
  exact IsPerfPair.smul_of_isUnit isUnit_one.neg p

/-- Scaling a perfect pairing by a sign unit `u : ℤˣ` preserves perfectness. -/
instance IsPerfPair.intUnits_smul (u : ℤˣ) (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair] :
    (u • p).IsPerfPair := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa only [one_smul] using ‹p.IsPerfPair›
  · simpa only [Units.neg_smul, one_smul] using inferInstanceAs (-p).IsPerfPair

end CommRing

end LinearMap
