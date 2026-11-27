/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Jacobson.Ideal
import TauCeti.RingTheory.Jacobson.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The integral shear `!![1, e₂; e₁, 1]`

For elements `e₁ e₂` of a commutative ring `O`, the integral shear is the matrix
`A(e₁, e₂) = !![1, e₂; e₁, 1]`. It acts on row vectors by `(F, G) ↦ (F + e₁ G, G + e₂ F)`, its
determinant is `1 - e₁ e₂`, and its adjugate is `A(-e₁, -e₂)`. Hence it is invertible over `O`
exactly when `1 - e₁ e₂` is a unit of `O`; a nonzero determinant is not enough.

Over a ring without zero divisors and with `1 - e₁ e₂ ≠ 0`, the shear moves lines through the
origin in a controlled way: the axis `F = 0` goes to the line `F' = e₁ G'`, the axis `G = 0` to
`G' = e₂ F'`, and the line `F = r G` to `(1 + e₂ r) F' = (e₁ + r) G'`.

If `e₁` lies in the Jacobson radical of `O`, then `1 - e₁ e₂` is a unit and `A(e₁, e₂)` is
invertible over `O`. When `I` is an infinite ideal contained in the Jacobson radical, `e₁, e₂ ∈ I`
can moreover be chosen nonzero and away from finitely many forbidden values. For a local domain
`O` that is not a field, such as `ℤ_[p]` or the integers of a finite extension of `ℚ_[p]`, the
maximal ideal is such an ideal: it is infinite by `TauCeti.IsLocalRing.infinite_maximalIdeal`
and it is the Jacobson radical by `IsLocalRing.ringJacobson_eq_maximalIdeal`. In particular, for
finitely many nonzero row vectors `v` over a ring without zero divisors containing `O`, the shear
can be chosen so that no `v A(e₁, e₂)` lies on a coordinate axis.

Lei, Loeffler and Zerbes apply such a constant change of basis to the Coleman maps of a
two-dimensional crystalline representation, whose image is cut out by finitely many lines, one at
each specialization point. They choose the shear so that none of the transformed lines is a
coordinate axis.

## Main definitions

* `TauCeti.integralShear e₁ e₂`: the matrix `!![1, e₂; e₁, 1]`.

## Main results

* `TauCeti.vecMul_integralShear`: `(F, G) A(e₁, e₂) = (F + e₁ G, G + e₂ F)`.
* `TauCeti.det_integralShear`: `det A(e₁, e₂) = 1 - e₁ e₂`.
* `TauCeti.isUnit_integralShear_iff`: `A(e₁, e₂)` is a unit iff `1 - e₁ e₂` is.
* `TauCeti.inv_integralShear`: `A(e₁, e₂)⁻¹ = (1 - e₁ e₂)⁻¹ A(-e₁, -e₂)`.
* `TauCeti.vecMul_integralShear_eq_mul_iff`: the line `F = r G` goes to
  `(1 + e₂ r) F' = (e₁ + r) G'`, with the two axes in
  `TauCeti.vecMul_integralShear_zero_eq_iff` and `TauCeti.vecMul_integralShear_one_eq_iff`.
* `TauCeti.isUnit_det_integralShear_of_mem_jacobson`: `det A(e₁, e₂)` is a unit when `e₁` lies
  in the Jacobson radical.
* `TauCeti.exists_integralShear_avoiding_slopes`: in an infinite ideal inside the Jacobson
  radical there are nonzero `e₁, e₂` with `e₁ + r ≠ 0` and `1 + e₂ r ≠ 0` for finitely many slopes
  `r`, and `det A(e₁, e₂)` a unit.
* `TauCeti.exists_integralShear_vecMul_ne_zero`: for finitely many nonzero rows `v` over a ring
  without zero divisors,
  `e₁, e₂` can be chosen in such an ideal so that both coordinates of every `v A(e₁, e₂)` are
  nonzero.

## References

* A. Lei, D. Loeffler and S. L. Zerbes, *Coleman maps and the p-adic regulator*, Algebra & Number
  Theory 5 (2011), no. 8, 1095–1131, §5C, Proposition 5.11 and its proof, and Remark 5.12.
-/

public section

open Matrix

namespace TauCeti

section Defs

variable {R : Type*} [One R]

/-- The integral shear `A(e₁, e₂) = !![1, e₂; e₁, 1]`. On row vectors it acts by
`(F, G) ↦ (F + e₁ G, G + e₂ F)` (`TauCeti.vecMul_integralShear`). -/
def integralShear (e₁ e₂ : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, e₂; e₁, 1]

/-- The defining formula of `TauCeti.integralShear`. -/
theorem integralShear_def (e₁ e₂ : R) : integralShear e₁ e₂ = !![1, e₂; e₁, 1] :=
  (rfl)

end Defs

@[simp]
theorem integralShear_zero_zero {R : Type*} [Zero R] [One R] : integralShear (0 : R) 0 = 1 := by
  rw [integralShear_def, one_fin_two]

@[simp]
theorem integralShear_map {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S)
    (e₁ e₂ : R) : (integralShear e₁ e₂).map f = integralShear (f e₁) (f e₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [integralShear_def]

@[simp]
theorem integralShear_transpose {R : Type*} [One R] (e₁ e₂ : R) :
    (integralShear e₁ e₂)ᵀ = integralShear e₂ e₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [integralShear_def]

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The integral shear acts on a row `(F, G)` by `(F, G) ↦ (F + e₁ G, G + e₂ F)`. -/
@[simp]
theorem vecMul_integralShear (e₁ e₂ : R) (v : Fin 2 → R) :
    v ᵥ* integralShear e₁ e₂ = ![v 0 + e₁ * v 1, v 1 + e₂ * v 0] := by
  ext k
  fin_cases k <;> simp [integralShear_def, vecMul, dotProduct, Fin.sum_univ_two] <;> ring

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- The determinant of `A(e₁, e₂)` is `1 - e₁ e₂`. -/
@[simp]
theorem det_integralShear (e₁ e₂ : R) : (integralShear e₁ e₂).det = 1 - e₁ * e₂ := by
  rw [integralShear_def, det_fin_two_of]
  ring

/-- The adjugate of `A(e₁, e₂)` is `A(-e₁, -e₂)`, so `A(e₁, e₂) A(-e₁, -e₂) = (1 - e₁ e₂) • 1`. -/
theorem adjugate_integralShear (e₁ e₂ : R) :
    (integralShear e₁ e₂).adjugate = integralShear (-e₁) (-e₂) := by
  rw [integralShear_def, integralShear_def, adjugate_fin_two_of]

/-- The integral shear is invertible over `R` exactly when `1 - e₁ e₂` is a unit of `R`. -/
theorem isUnit_integralShear_iff {e₁ e₂ : R} :
    IsUnit (integralShear e₁ e₂) ↔ IsUnit (1 - e₁ * e₂) := by
  rw [isUnit_iff_isUnit_det, det_integralShear]

/-- The inverse of `A(e₁, e₂)` is `(1 - e₁ e₂)⁻¹ A(-e₁, -e₂)`, with `Ring.inverse` taking the
value `0` when `1 - e₁ e₂` is not a unit. -/
theorem inv_integralShear (e₁ e₂ : R) :
    (integralShear e₁ e₂)⁻¹ = Ring.inverse (1 - e₁ * e₂) • integralShear (-e₁) (-e₂) := by
  rw [inv_def, det_integralShear, adjugate_integralShear]

end CommRing

/-! ### Lines through the origin under the shear -/

section Lines

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {e₁ e₂ : R}

/-- If `1 - e₁ e₂ ≠ 0`, a row `v` lies on the line `F = r G` exactly when `v A(e₁, e₂)` lies on
the line `(1 + e₂ r) F' = (e₁ + r) G'`. -/
theorem vecMul_integralShear_eq_mul_iff (h : 1 - e₁ * e₂ ≠ 0) (r : R) (v : Fin 2 → R) :
    (1 + e₂ * r) * (v ᵥ* integralShear e₁ e₂) 0 = (e₁ + r) * (v ᵥ* integralShear e₁ e₂) 1 ↔
      v 0 = r * v 1 := by
  have key : (1 + e₂ * r) * (v 0 + e₁ * v 1) - (e₁ + r) * (v 1 + e₂ * v 0) =
      (1 - e₁ * e₂) * (v 0 - r * v 1) := by
    ring
  simp only [vecMul_integralShear, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← sub_eq_zero, key, mul_eq_zero, or_iff_right h, sub_eq_zero]

/-- If `1 - e₁ e₂ ≠ 0`, a row `v` lies on the axis `F = 0` exactly when `v A(e₁, e₂)` lies on
the line `F' = e₁ G'`. -/
theorem vecMul_integralShear_zero_eq_iff (h : 1 - e₁ * e₂ ≠ 0) (v : Fin 2 → R) :
    (v ᵥ* integralShear e₁ e₂) 0 = e₁ * (v ᵥ* integralShear e₁ e₂) 1 ↔ v 0 = 0 := by
  simpa using vecMul_integralShear_eq_mul_iff h 0 v

/-- If `1 - e₁ e₂ ≠ 0`, a row `v` lies on the axis `G = 0` exactly when `v A(e₁, e₂)` lies on
the line `G' = e₂ F'`. -/
theorem vecMul_integralShear_one_eq_iff (h : 1 - e₁ * e₂ ≠ 0) (v : Fin 2 → R) :
    (v ᵥ* integralShear e₁ e₂) 1 = e₂ * (v ᵥ* integralShear e₁ e₂) 0 ↔ v 1 = 0 := by
  have key : (v 1 + e₂ * v 0) - e₂ * (v 0 + e₁ * v 1) = (1 - e₁ * e₂) * v 1 := by
    ring
  simp only [vecMul_integralShear, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← sub_eq_zero, key, mul_eq_zero, or_iff_right h]

end Lines

/-! ### Choosing the shear in an infinite ideal -/

section Avoiding

variable {O E : Type*} [CommRing O] [CommRing E] [Algebra O E]

/-- If `e₁` lies in the Jacobson radical of `O`, then `det A(e₁, e₂) = 1 - e₁ e₂` is a unit, so
`A(e₁, e₂)` is invertible over `O`. -/
theorem isUnit_det_integralShear_of_mem_jacobson {e₁ : O} (he₁ : e₁ ∈ Ring.jacobson O) (e₂ : O) :
    IsUnit (integralShear e₁ e₂).det := by
  rw [det_integralShear]
  exact Ideal.isUnit_one_sub_mul_of_le_jacobson le_rfl (Or.inl he₁)

/-- Let `O ⊆ E` and let `I` be an infinite ideal of `O` contained in the Jacobson radical, such as
the maximal ideal of a local domain that is not a field. For finitely many slopes `r ∈ E`, there
are nonzero `e₁, e₂ ∈ I` with `e₁ + r ≠ 0` and `1 + e₂ r ≠ 0` for every slope, and then
`det A(e₁, e₂) = 1 - e₁ e₂` is a unit of `O`. -/
theorem exists_integralShear_avoiding_slopes (hinj : Function.Injective (algebraMap O E))
    {I : Ideal O} (hI : (I : Set O).Infinite) (hIJ : I ≤ Ring.jacobson O) (s : Finset E) :
    ∃ e₁ ∈ I, ∃ e₂ ∈ I, e₁ ≠ 0 ∧ e₂ ≠ 0 ∧
      (∀ r ∈ s, algebraMap O E e₁ + r ≠ 0 ∧ 1 + algebraMap O E e₂ * r ≠ 0) ∧
      IsUnit (integralShear e₁ e₂).det := by
  -- Each slope `r` forbids at most one `e₁`, namely the preimage of `-r`.
  have h₁ : (⋃ r ∈ s, {e : O | algebraMap O E e + r = 0}).Finite :=
    s.finite_toSet.biUnion fun _ _ ↦ Set.Subsingleton.finite fun a ha b hb ↦ hinj (by
      simp only [Set.mem_ofPred_eq] at ha hb
      linear_combination ha - hb)
  -- Each slope `r` forbids at most one `e₂`, namely the preimage of `-r⁻¹` when `r` is a unit.
  have h₂ : (⋃ r ∈ s, {e : O | 1 + algebraMap O E e * r = 0}).Finite :=
    s.finite_toSet.biUnion fun _ _ ↦ Set.Subsingleton.finite fun a ha b hb ↦ hinj (by
      simp only [Set.mem_ofPred_eq] at ha hb
      linear_combination algebraMap O E a * hb - algebraMap O E b * ha)
  obtain ⟨e₁, he₁I, he₁⟩ := hI.exists_notMem_finite ((Set.finite_singleton (0 : O)).union h₁)
  obtain ⟨e₂, he₂I, he₂⟩ := hI.exists_notMem_finite ((Set.finite_singleton (0 : O)).union h₂)
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_ofPred_eq, not_or,
    not_exists] at he₁ he₂
  exact ⟨e₁, he₁I, e₂, he₂I, he₁.1, he₂.1, fun r hr ↦ ⟨he₁.2 r hr, he₂.2 r hr⟩,
    isUnit_det_integralShear_of_mem_jacobson (hIJ he₁I) e₂⟩

/-- Let `O ⊆ E` with `E` without zero divisors, such as a field, and let `I` be an infinite ideal
of `O` contained in the Jacobson radical. For finitely many nonzero rows `v ∈ E²`, there are
`e₁, e₂ ∈ I` with `A(e₁, e₂)` invertible over `O` such that no row `v A(e₁, e₂)` lies on a
coordinate axis. -/
theorem exists_integralShear_vecMul_ne_zero [NoZeroDivisors E]
    (hinj : Function.Injective (algebraMap O E)) {I : Ideal O} (hI : (I : Set O).Infinite)
    (hIJ : I ≤ Ring.jacobson O) (s : Finset (Fin 2 → E)) (hs : ∀ v ∈ s, v ≠ 0) :
    ∃ e₁ ∈ I, ∃ e₂ ∈ I, IsUnit (integralShear e₁ e₂).det ∧
      ∀ v ∈ s, ∀ k, (v ᵥ* integralShear (algebraMap O E e₁) (algebraMap O E e₂)) k ≠ 0 := by
  -- For `x, y` not both zero, at most one `e` satisfies `x + e y = 0`.
  have key (x y : E) (hxy : x ≠ 0 ∨ y ≠ 0) :
      {e : O | x + algebraMap O E e * y = 0}.Subsingleton := by
    intro a ha b hb
    simp only [Set.mem_ofPred_eq] at ha hb
    by_cases hy : y = 0
    · simp only [hy, mul_zero, add_zero] at ha
      exact absurd ha (hxy.resolve_right (not_not.mpr hy))
    · exact hinj (mul_right_cancel₀ hy (by linear_combination ha - hb))
  have hs' (v : Fin 2 → E) (hv : v ∈ s) : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra! h
    exact hs v hv (by ext i; fin_cases i <;> simp [h.1, h.2])
  obtain ⟨e₁, he₁I, he₁⟩ := hI.exists_notMem_finite
    (s.finite_toSet.biUnion fun v hv ↦ (key (v 0) (v 1) (hs' v hv)).finite)
  obtain ⟨e₂, he₂I, he₂⟩ := hI.exists_notMem_finite
    (s.finite_toSet.biUnion fun v hv ↦ (key (v 1) (v 0) (hs' v hv).symm).finite)
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_coe, not_exists] at he₁ he₂
  refine ⟨e₁, he₁I, e₂, he₂I, isUnit_det_integralShear_of_mem_jacobson (hIJ he₁I) e₂,
    fun v hv k ↦ ?_⟩
  fin_cases k
  · simpa using he₁ v hv
  · simpa using he₂ v hv

end Avoiding

end TauCeti
