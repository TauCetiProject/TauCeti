/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import TauCeti.Algebra.Star.PartialIsometry
import TauCeti.Data.Matrix.Basis

/-!
# Unitary conjugacy of `⋆`-homomorphisms out of a matrix algebra

Let `φ ψ : Mₙ(R) → B` be `⋆`-homomorphisms into a unital `⋆`-ring `B`. They are conjugate by a
unitary of `B` as soon as the images of one diagonal matrix unit, and the complements of the images
of the identity, are the initial and final projections of partial isometries. The conjugating
unitary is built from the images of the matrix units. Over `ℂ` this reduces the unitary
classification of `⋆`-homomorphisms `Mₙ(ℂ) → Mₘ(ℂ)` to their multiplicity
(`TauCeti/Analysis/Matrix/HomMultiplicity.lean`).

## Main statements

* `NonUnitalStarAlgHom.exists_mem_unitary_mul_map_mul_star_eq`: unitary conjugacy of two
  `⋆`-homomorphisms `Mₙ(R) → B` from partial isometries implementing the equivalences of the
  relevant projections.

## References

* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Cambridge University Press (2000), Chapter 7.
* K. R. Davidson, *C⋆-Algebras by Example*, Fields Institute Monographs 6 (1996), Chapter III.
-/

public section

namespace Matrix

open TauCeti

variable {n R B : Type*} [Fintype n] [DecidableEq n] [CommSemiring R] [StarRing R] [Ring B]
  [StarRing B] [Algebra R B]

/-- Products of images of matrix units, associated to the right. -/
private theorem map_single_mul_map_single_mul (φ : Matrix n n R →⋆ₙₐ[R] B) (i j k l : n)
    (x : B) : φ (single i j 1) * (φ (single k l 1) * x) =
      if j = k then φ (single i l 1) * x else 0 := by
  rw [← mul_assoc, map_single_mul_map_single, ite_mul, zero_mul]

variable (φ ψ : Matrix n n R →⋆ₙₐ[R] B) (i : n) {v : B}

/-- The element `V = ∑ₖ ψ(Eₖᵢ) v φ(Eᵢₖ)` intertwines `φ` and `ψ` on matrix units. -/
private theorem sum_mul_map_single (k l : n) :
    (∑ j, ψ (single j i 1) * v * φ (single i j 1)) * φ (single k l 1) =
      ψ (single k l 1) * ∑ j, ψ (single j i 1) * v * φ (single i j 1) := by
  simp [Finset.sum_mul, Finset.mul_sum, mul_assoc, map_single_mul_map_single_mul,
    map_single_mul_map_single]

/-- The element `V = ∑ₖ ψ(Eₖᵢ) v φ(Eᵢₖ)` intertwines `φ` and `ψ`. -/
private theorem sum_mul_map (x : Matrix n n R) :
    (∑ j, ψ (single j i 1) * v * φ (single i j 1)) * φ x =
      ψ x * ∑ j, ψ (single j i 1) * v * φ (single i j 1) := by
  induction x using Matrix.induction_on' with
  | h_zero => simp
  | h_add p q hp hq => rw [map_add, map_add, mul_add, add_mul, hp, hq]
  | h_std_basis k l c =>
    rw [single_eq_smul_single_one k l c, map_smul, map_smul, mul_smul_comm, smul_mul_assoc,
      sum_mul_map_single]

private theorem map_one_mul_sum :
    ψ 1 * ∑ j, ψ (single j i 1) * v * φ (single i j 1) =
      ∑ j, ψ (single j i 1) * v * φ (single i j 1) := by
  simp only [Finset.mul_sum, ← mul_assoc, ← map_mul, one_mul]

variable {φ ψ i}

/-- If `v` is a partial isometry from `φ(Eᵢᵢ)` to `ψ(Eᵢᵢ)`, then `V = ∑ₖ ψ(Eₖᵢ) v φ(Eᵢₖ)` is a
partial isometry from `φ 1` to `ψ 1`: its initial projection is `φ 1`. -/
private theorem star_sum_mul_sum (hv : IsPartialIsometry v) (hvφ : star v * v = φ (single i i 1))
    (hvψ : v * star v = ψ (single i i 1)) :
    star (∑ j, ψ (single j i 1) * v * φ (single i j 1)) *
      ∑ j, ψ (single j i 1) * v * φ (single i j 1) = φ 1 := by
  have hψv (y : B) : ψ (single i i 1) * (v * y) = v * y := by
    rw [← mul_assoc, ← hvψ, hv.mul_star_mul_self]
  have hvv (y : B) : star v * (v * y) = φ (single i i 1) * y := by rw [← mul_assoc, hvφ]
  simp only [star_sum, star_mul, star_map_single, Finset.sum_mul, Finset.mul_sum, mul_assoc,
    map_single_mul_map_single_mul, map_single_mul_map_single, hψv, hvv, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← map_sum, sum_single_one]

/-- The final projection of `V = ∑ₖ ψ(Eₖᵢ) v φ(Eᵢₖ)` is `ψ 1`: `star V` is the element built
from `ψ`, `φ` and the partial isometry `star v`, whose initial projection is `ψ 1`. -/
private theorem sum_mul_star_sum (hv : IsPartialIsometry v) (hvφ : star v * v = φ (single i i 1))
    (hvψ : v * star v = ψ (single i i 1)) :
    (∑ j, ψ (single j i 1) * v * φ (single i j 1)) *
      star (∑ j, ψ (single j i 1) * v * φ (single i j 1)) = ψ 1 := by
  have hV : star (∑ j, ψ (single j i 1) * v * φ (single i j 1)) =
      ∑ j, φ (single j i 1) * star v * ψ (single i j 1) := by
    simp [star_sum, star_mul, star_map_single, mul_assoc]
  have h := star_sum_mul_sum (φ := ψ) (ψ := φ) hv.star (by rw [star_star, hvψ])
    (by rw [star_star, hvφ])
  rwa [← hV, star_star] at h

variable (φ ψ i) in
/-- **Unitary conjugacy of `⋆`-homomorphisms out of a matrix algebra.** Let `φ ψ : Mₙ(R) → B` be
`⋆`-homomorphisms into a unital `⋆`-ring `B`. If some partial isometry `v` has initial projection
`φ(Eᵢᵢ)` and final projection `ψ(Eᵢᵢ)`, and some partial isometry `w` has initial projection
`1 - φ 1` and final projection `1 - ψ 1`, then `ψ` is the conjugate of `φ` by a unitary of `B`,
namely `u = ∑ₖ ψ(Eₖᵢ) v φ(Eᵢₖ) + w`. -/
theorem _root_.NonUnitalStarAlgHom.exists_mem_unitary_mul_map_mul_star_eq {w : B}
    (hv : IsPartialIsometry v)
    (hvφ : star v * v = φ (single i i 1)) (hvψ : v * star v = ψ (single i i 1))
    (hw : IsPartialIsometry w) (hwφ : star w * w = 1 - φ 1) (hwψ : w * star w = 1 - ψ 1) :
    ∃ u ∈ unitary B, ∀ x, u * φ x * star u = ψ x := by
  set V := ∑ j, ψ (single j i 1) * v * φ (single i j 1)
  have hVV : star V * V = φ 1 := star_sum_mul_sum hv hvφ hvψ
  have hVV' : V * star V = ψ 1 := sum_mul_star_sum hv hvφ hvψ
  have hψV : ψ 1 * V = V := map_one_mul_sum φ ψ i
  have hVx (x : Matrix n n R) : V * φ x = ψ x * V := sum_mul_map φ ψ i x
  have hVφ : V * φ 1 = V := by rw [hVx, hψV]
  -- `w` vanishes on the range of `φ 1`, and its range is orthogonal to the range of `ψ 1`
  have hwφx (x : Matrix n n R) : w * φ x = 0 := by
    rw [← hw.mul_star_mul_self, mul_assoc w, hwφ]
    simp [mul_assoc, sub_mul, ← map_mul]
  have hψw : ψ 1 * w = 0 := by
    rw [← hw.mul_star_mul_self, hwψ]
    simp [← mul_assoc, mul_sub, ← map_mul]
  have hVw : star V * w = 0 := by
    rw [← hψV]
    simp [mul_assoc, ← map_star, hψw]
  have hwV : star w * V = 0 := by rw [← star_star V, ← star_mul, hVw, star_zero]
  have hwV' : w * star V = 0 := by
    rw [← hVφ]
    simp [← mul_assoc, ← map_star, hwφx]
  have hVw' : V * star w = 0 := by rw [← star_star V, ← star_mul, hwV', star_zero]
  refine ⟨V + w, Unitary.mem_iff.mpr ⟨?_, ?_⟩, fun x => ?_⟩
  · simp [add_mul, mul_add, hVV, hVw, hwV, hwφ]
  · simp [add_mul, mul_add, hVV', hVw', hwV', hwψ]
  · rw [add_mul, hwφx, add_zero, hVx]
    simp [mul_assoc, mul_add, hVV', hVw', ← map_mul]


end Matrix
