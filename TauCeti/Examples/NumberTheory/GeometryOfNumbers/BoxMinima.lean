/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GeometryOfNumbers.BoxMinima

/-!
# Successive minima of the standard lattice for explicit boxes

Concrete values of the successive minima `ZLattice.successiveMin` and of their natural-index
extension `ZLattice.successiveMinNat`, read off from the minima of weighted boxes and
cross-polytopes (`ZLattice.successiveMin_box`, `ZLattice.successiveMin_pi_box`,
`ZLattice.successiveMin_pi_crosspolytope`).

* For `ℤ ⊆ ℝ` and `[-2, 2]` the only minimum is `1 / 2`: a body twice as long needs half the
  dilation to reach the lattice vector `1`.
* For `ℤ²` and the box `K₂₃ = [-1/2, 1/2] × [-1/3, 1/3]` the minima are `2` and `3`, and the same
  holds for the cross-polytope `2 |x₀| + 3 |x₁| ≤ 1`, although its area is `1 / 3` rather than
  `2 / 3`. The minima depend on more than the volume of the body.
* The natural-index extension of the minima is zero-based and vanishes from the dimension on. For
  `ℤ²` and `K₂₃` its values at `0, 1, 2` are `2, 3, 0`, and for `ℤ⁶` and the box with weights
  `1, …, 6` its value at `2` is the third minimum, `3`.
* For `ℤⁿ` and the cube `[-1, 1]ⁿ` every minimum is `1`.

## References

* J.-H. Evertse, *Diophantine approximation, Chapter 2: Geometry of numbers*, lecture notes,
  Leiden University, 2023, §2.3, the definition of successive minima and Examples 2 and 3.
-/

public section

open Module Submodule ZLattice

namespace TauCeti.BoxMinimaExample

/-- For the lattice `ℤ ⊆ ℝ` and the interval `[-2, 2]`, the first minimum is `1 / 2`. -/
theorem successiveMin_int_Icc {K : ConvexBody ℝ} (hK : (K : Set ℝ) = Set.Icc (-2) 2) :
    successiveMin (span ℤ {(1 : ℝ)}) K ⟨0, by simp⟩ = 1 / 2 := by
  -- `[-2, 2]` is the box of weight `1 / 2` for the basis `1` of `ℝ`.
  have h := successiveMin_box (b := (Basis.singleton (Fin 1) ℝ).reindex
    (finCongr (finrank_self ℝ).symm)) (a := fun _ ↦ 1 / 2) (K := K) (fun _ ↦ by norm_num)
    monotone_const ?_ ⟨0, by simp⟩
  · simpa [Basis.range_reindex, Pi.one_def] using h
  · ext x
    simp only [hK, Set.mem_Icc, Set.mem_ofPred_eq]
    simp [← abs_le, inv_mul_le_iff₀ (by norm_num : (0 : ℝ) < 2)]

/-- For the lattice `ℤ²` and the box `[-1/2, 1/2] × [-1/3, 1/3]`, the successive minima are `2`
and `3`. -/
theorem successiveMin_box_two_three {K : ConvexBody (Fin 2 → ℝ)}
    (hK : (K : Set (Fin 2 → ℝ)) = {x | 2 * |x 0| ≤ 1 ∧ 3 * |x 1| ≤ 1}) :
    successiveMin (span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))) K ⟨0, by simp⟩ = 2 ∧
      successiveMin (span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))) K ⟨1, by simp⟩ = 3 := by
  have hK' : (K : Set (Fin 2 → ℝ)) = {x | ∀ j : Fin 2, ((j : ℕ) + 2 : ℝ) * |x j| ≤ 1} := by
    rw [hK]
    norm_num [Fin.forall_fin_two]
  have h := successiveMin_pi_box (fun _ ↦ by positivity) (fun i j hij ↦ by simpa using hij) hK'
  exact ⟨by norm_num [h], by norm_num [h]⟩

/-- For the lattice `ℤ²` and the cross-polytope `2 |x₀| + 3 |x₁| ≤ 1`, the successive minima are
`2` and `3`, as for the box `[-1/2, 1/2] × [-1/3, 1/3]`. -/
theorem successiveMin_crosspolytope_two_three {K : ConvexBody (Fin 2 → ℝ)}
    (hK : (K : Set (Fin 2 → ℝ)) = {x | 2 * |x 0| + 3 * |x 1| ≤ 1}) :
    successiveMin (span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))) K ⟨0, by simp⟩ = 2 ∧
      successiveMin (span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))) K ⟨1, by simp⟩ = 3 := by
  have hK' : (K : Set (Fin 2 → ℝ)) = {x | ∑ j : Fin 2, ((j : ℕ) + 2 : ℝ) * |x j| ≤ 1} := by
    rw [hK]
    norm_num [Fin.sum_univ_two]
  have h := successiveMin_pi_crosspolytope (fun _ ↦ by positivity)
    (fun i j hij ↦ by simpa using hij) hK'
  exact ⟨by norm_num [h], by norm_num [h]⟩

/-- For the lattice `ℤ²` and the box `[-1/2, 1/2] × [-1/3, 1/3]`, the natural-index extension of
the successive minima takes the values `2, 3, 0` at `0, 1, 2`: the index `2` is the dimension, not a
third minimum. -/
theorem successiveMinNat_box_two_three {K : ConvexBody (Fin 2 → ℝ)}
    (hK : (K : Set (Fin 2 → ℝ)) = {x | 2 * |x 0| ≤ 1 ∧ 3 * |x 1| ≤ 1}) :
    successiveMinNat (span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))) K 0 = 2 ∧
      successiveMinNat (span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))) K 1 = 3 ∧
      successiveMinNat (span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))) K 2 = 0 := by
  obtain ⟨h0, h1⟩ := successiveMin_box_two_three hK
  refine ⟨?_, ?_, successiveMinNat_of_le _ _ (by simp)⟩
  · rwa [successiveMinNat_of_lt _ _ (by simp)]
  · rwa [successiveMinNat_of_lt _ _ (by simp)]

/-- For the lattice `ℤ⁶` and the box with weights `1, …, 6`, the natural index `2 = 2 * 1` denotes
the third successive minimum, which is `3`. -/
theorem successiveMinNat_box_six {K : ConvexBody (Fin 6 → ℝ)}
    (hK : (K : Set (Fin 6 → ℝ)) = {x | ∀ j : Fin 6, ((j : ℕ) + 1 : ℝ) * |x j| ≤ 1}) :
    successiveMinNat (span ℤ (Set.range (Pi.basisFun ℝ (Fin 6)))) K (2 * 1) = 3 := by
  rw [successiveMinNat_of_lt _ _ (by simp),
    successiveMin_pi_box (fun _ ↦ by positivity) (fun i j hij ↦ by simpa using hij) hK]
  norm_num

-- In `ℝ⁶` the natural index `6 = 2 * 3` is the dimension, where the value is zero for every
-- lattice and body.
example (L : Submodule ℤ (Fin 6 → ℝ)) (K : ConvexBody (Fin 6 → ℝ)) :
    successiveMinNat L K (2 * 3) = 0 :=
  successiveMinNat_of_le L K (by simp)

/-- For the lattice `ℤⁿ` and the cube `[-1, 1]ⁿ`, every successive minimum is `1`. -/
theorem successiveMin_cube {n : ℕ} {K : ConvexBody (Fin n → ℝ)}
    (hK : (K : Set (Fin n → ℝ)) = {x | ∀ j, |x j| ≤ 1}) (i : Fin (finrank ℝ (Fin n → ℝ))) :
    successiveMin (span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))) K i = 1 :=
  successiveMin_pi_box (w := 1) (fun _ ↦ one_pos) monotone_const (by simpa using hK) i

end TauCeti.BoxMinimaExample
