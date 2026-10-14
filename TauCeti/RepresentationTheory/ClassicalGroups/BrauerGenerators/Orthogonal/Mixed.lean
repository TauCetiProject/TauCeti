/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.TensorPower

/-!
# Mixed crossing–arc relations on orthogonal tensor powers

For three distinct strands, the orthogonal cup-cap operators and the factor-permutation action
satisfy the mixed Brauer relation `sᵢ eᵢ₊₁ eᵢ = sᵢ₊₁ eᵢ` and its reverse product form
`eᵢ eᵢ₊₁ sᵢ = eᵢ sᵢ₊₁`. These are the relations between an arc and a crossing on an overlapping
pair of strands needed to extend the operators to an action of the Brauer algebra.

No loop is closed in the mixed relations, so their coefficient is one over every commutative
semiring, including at zero dimension and in positive characteristic.

The operators and their renaming law are those of
`TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.TensorPower`; the
relations mirror the diagram identities in `TauCeti.Combinatorics.Brauer.Relations`.

## References

* R. Brauer, *On algebras which are connected with the semisimple continuous groups*,
  Annals of Mathematics 38 (1937), 857–872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 9.
-/

public section

namespace TauCeti

universe u

variable {k : Type u} [CommSemiring k] {n d : ℕ}

/-- The mixed Brauer relation `sᵢ eᵢ₊₁ eᵢ = sᵢ₊₁ eᵢ`, on any three distinct strands.
The two successive arcs close no loop. -/
theorem permTensorAction_swap_mul_orthogonalCupCapAt_mul_orthogonalCupCapAt
    {i j l : Fin d} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    permTensorAction k n d (Equiv.swap i j) *
        (orthogonalCupCapAt k n d j l * orthogonalCupCapAt k n d i j) =
      permTensorAction k n d (Equiv.swap j l) * orthogonalCupCapAt k n d i j := by
  classical
  apply (tensorPowerBasis k n d).ext
  intro f
  simp only [Module.End.mul_apply, orthogonalCupCapAt_tensorPowerBasis hij]
  by_cases hf : f i = f j
  · simp only [hf, ite_true, map_sum, orthogonalCupCapAt_tensorPowerBasis hjl]
    simp only [Function.update_self, Function.update_of_ne hil.symm,
      Function.update_of_ne hjl.symm]
    simp only [apply_ite, map_sum, map_zero, permTensorAction_tensorPowerBasis]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    funext t
    by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htl : t = l <;>
      simp_all [Equiv.swap_apply_of_ne_of_ne, hij.symm, hjl.symm, hil.symm]
  · simp [hf]

/-- The reverse product form `eᵢ eᵢ₊₁ sᵢ = eᵢ sᵢ₊₁` of the mixed Brauer relation, on
three distinct strands. -/
theorem orthogonalCupCapAt_mul_orthogonalCupCapAt_mul_permTensorAction_swap
    {i j l : Fin d} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    (orthogonalCupCapAt k n d i j * orthogonalCupCapAt k n d j l) *
        permTensorAction k n d (Equiv.swap i j) =
      orthogonalCupCapAt k n d i j * permTensorAction k n d (Equiv.swap j l) := by
  have h := permTensorAction_swap_mul_orthogonalCupCapAt_mul_orthogonalCupCapAt
    (k := k) (n := n) hjl.symm hij.symm hil.symm
  rw [orthogonalCupCapAt_comm l j, orthogonalCupCapAt_comm j i,
    Equiv.swap_comm l j, Equiv.swap_comm j i] at h
  have hi : permTensorAction k n d (Equiv.swap i j) *
      permTensorAction k n d (Equiv.swap i j) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have hj : permTensorAction k n d (Equiv.swap j l) *
      permTensorAction k n d (Equiv.swap j l) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have hrename := permTensorAction_mul_orthogonalCupCapAt (k := k) (n := n)
    (Equiv.swap i j) j l
  have hrename' := permTensorAction_mul_orthogonalCupCapAt (k := k) (n := n)
    (Equiv.swap j l) i j
  simp only [Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm] at hrename
  simp only [Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hij hil] at hrename'
  apply ((Group.isUnit (Equiv.swap j l)).map (permTensorAction k n d)).mul_left_cancel
  calc
    permTensorAction k n d (Equiv.swap j l) *
        ((orthogonalCupCapAt k n d i j * orthogonalCupCapAt k n d j l) *
          permTensorAction k n d (Equiv.swap i j)) =
      (permTensorAction k n d (Equiv.swap i j) * orthogonalCupCapAt k n d j l) *
        permTensorAction k n d (Equiv.swap i j) := by rw [← mul_assoc, h]
    _ = orthogonalCupCapAt k n d i l := by
      rw [hrename, mul_assoc, hi, mul_one]
    _ = permTensorAction k n d (Equiv.swap j l) *
        (orthogonalCupCapAt k n d i j * permTensorAction k n d (Equiv.swap j l)) := by
      rw [← mul_assoc, hrename', mul_assoc, hj, mul_one]

end TauCeti
