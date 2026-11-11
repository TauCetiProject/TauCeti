/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# `n`-positive maps and the Kadison–Schwarz inequality

A complex-linear map `φ : A → B` between C⋆-algebras is `n`-positive when its entrywise
amplification `M_n(A) → M_n(B)` is positive, with `M_n(A) = CStarMatrix (Fin n) (Fin n) A`
ordered as a C⋆-algebra. Mathlib's completely positive maps `A →CP B` are exactly the maps that
are `n`-positive for every `n`.

For a `2`-positive map with unital domain and codomain, positivity of the image of the matrix
`[[a⋆a, a⋆], [a, 1]] = [[a, 1], [0, 0]]⋆ [[a, 1], [0, 0]]` gives the **Kadison–Schwarz
inequality**

`φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆a)`,

and `φ(a)⋆ φ(a) ≤ φ(a⋆a)` when `φ` is unital. Together with the bound `‖φ p‖ ≤ ‖φ 1‖ ‖p‖` for
positive `p`, this gives `‖φ a‖ ≤ ‖φ 1‖ ‖a‖`, so the operator norm of a completely positive map
with unital domain is `‖φ 1‖`.

## Main declarations

* `TauCeti.IsNPositive`: `n`-positivity of a complex-linear map, and
  `CompletelyPositiveMap.isNPositive`: completely positive maps are `n`-positive for every `n`.
* `TauCeti.IsNPositive.map_nonneg`: an `n`-positive map with `0 < n` is positive.
* `TauCeti.IsNPositive.star_map_mul_map_le`: the Kadison–Schwarz inequality
  `φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆a)` for `2`-positive maps, and
  `TauCeti.IsNPositive.star_map_mul_map_le_of_map_one` for unital ones.
* `TauCeti.IsNPositive.norm_apply_le`: `‖φ a‖ ≤ ‖φ 1‖ * ‖a‖` for `2`-positive maps.
* `CompletelyPositiveMap.star_map_mul_map_le` and `CompletelyPositiveMap.opNorm_eq_norm_map_one`:
  the Schwarz inequality for unital completely positive maps, and `‖φ‖ = ‖φ 1‖`.
* `TauCeti.not_isNPositive_two_cstarMatrixTranspose`: the transpose on `M₂(ℂ)` is unital but not
  `2`-positive, since it violates the Schwarz inequality at a matrix unit.

## References

* B. Blackadar, *Operator Algebras*, II.6.9.4 and II.6.9.14.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Proposition 3.3 and
  Exercise 3.4.
-/

public section

open scoped CStarAlgebra

namespace TauCeti

variable {A B : Type*}

section NonUnital

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A complex-linear map `φ : A → B` between C⋆-algebras is **`n`-positive** when its entrywise
amplification to `n × n` matrices, ordered as the C⋆-algebras `CStarMatrix (Fin n) (Fin n) _`,
sends positive matrices to positive matrices. -/
def IsNPositive (n : ℕ) (φ : A →ₗ[ℂ] B) : Prop :=
  ∀ M : CStarMatrix (Fin n) (Fin n) A, 0 ≤ M → 0 ≤ M.map φ

/-- A completely positive map is `n`-positive for every `n`. -/
theorem _root_.CompletelyPositiveMap.isNPositive (φ : A →CP B) (n : ℕ) :
    IsNPositive n φ.toLinearMap :=
  φ.map_cstarMatrix_nonneg' n

/-- The diagonal entries of a positive matrix over a C⋆-algebra are positive. -/
theorem _root_.CStarMatrix.apply_self_nonneg {n : Type*} [Fintype n]
    {M : CStarMatrix n n A} (hM : 0 ≤ M) (i : n) : 0 ≤ M i i := by
  obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
  rw [CStarMatrix.mul_apply]
  exact Finset.sum_nonneg fun k _ => by
    simp [CStarMatrix.star_apply]

/-- An `n`-positive map with `0 < n` is positive: a positive `a` sits in a corner of the
positive diagonal matrix `diag(a, 0, …, 0)`. -/
theorem IsNPositive.map_nonneg {n : ℕ} {φ : A →ₗ[ℂ] B} (hφ : IsNPositive n φ) (hn : 0 < n)
    {a : A} (ha : 0 ≤ a) : 0 ≤ φ a := by
  let i₀ : Fin n := ⟨0, hn⟩
  let M : CStarMatrix (Fin n) (Fin n) A :=
    CStarMatrix.ofMatrix (Matrix.diagonal (Pi.single i₀ a))
  have hM : 0 ≤ M := CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun x => by
    simpa [M, CStarMatrix.ofMatrix_apply, Matrix.diagonal_apply, Pi.single_apply]
      using star_left_conjugate_nonneg ha (x i₀)
  simpa [M, CStarMatrix.map_apply, CStarMatrix.ofMatrix_apply] using
    CStarMatrix.apply_self_nonneg (hφ M hM) i₀

end NonUnital

section Unital

variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {φ : A →ₗ[ℂ] B}

/-- The quadratic form of the image under a `2`-positive map of the positive matrix
`[[a⋆a, a⋆], [a, 1]]`, with `φ(a⋆)` rewritten as `φ(a)⋆`. -/
theorem IsNPositive.quadratic_nonneg (hφ : IsNPositive 2 φ) (a : A) (x y : B) :
    0 ≤ star x * φ (star a * a) * x + star x * star (φ a) * y + star y * φ a * x +
      star y * φ 1 * y := by
  let M : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix !![star a * a, star a; a, 1]
  have hM : 0 ≤ M := CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun z => by
    have h : ∑ i, ∑ j, star (z i) * M i j * z j = star (a * z 0 + z 1) * (a * z 0 + z 1) := by
      simp only [M, Fin.sum_univ_two, CStarMatrix.ofMatrix_apply, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, star_add, star_mul, mul_add, add_mul, one_mul, mul_assoc]
      abel
    rw [h]
    exact star_mul_self_nonneg _
  have hN := hφ M hM
  -- The image matrix is self-adjoint, which identifies `φ(a⋆)` with `φ(a)⋆`.
  have hstar : φ (star a) = star (φ a) := by
    have := congrFun (congrFun hN.isSelfAdjoint.star_eq 0) 1
    simpa [M, CStarMatrix.star_apply, CStarMatrix.map_apply, CStarMatrix.ofMatrix_apply]
      using this.symm
  have := CStarMatrix.nonneg_iff_forall_sum_nonneg.mp hN ![x, y]
  simpa [M, Fin.sum_univ_two, CStarMatrix.map_apply, CStarMatrix.ofMatrix_apply, hstar,
    add_assoc] using this

/-- **Kadison–Schwarz inequality** for a unital `2`-positive map: `φ(a)⋆ φ(a) ≤ φ(a⋆a)`. -/
theorem IsNPositive.star_map_mul_map_le_of_map_one (hφ : IsNPositive 2 φ) (h1 : φ 1 = 1)
    (a : A) : star (φ a) * φ a ≤ φ (star a * a) := by
  have := hφ.quadratic_nonneg a 1 (-φ a)
  rw [← sub_nonneg]
  convert this using 1
  simp [h1]
  abel

/-- A `2`-positive map whose value at `1` vanishes is zero. -/
theorem IsNPositive.eq_zero_of_map_one (hφ : IsNPositive 2 φ) (h1 : φ 1 = 0) : φ = 0 := by
  let ψ : A →ₚ[ℂ] B := .mk₀ φ fun _ ha => hφ.map_nonneg two_pos ha
  refine LinearMap.ext_on (CStarAlgebra.span_nonneg (A := A)) fun a (ha : 0 ≤ a) => ?_
  have : ‖φ a‖ ≤ ‖φ 1‖ * ‖a‖ := ψ.norm_apply_le_of_nonneg a ha
  rw [h1, norm_zero, zero_mul] at this
  simpa using norm_le_zero_iff.mp this

/-- **Kadison–Schwarz inequality** for a `2`-positive map with unital domain:
`φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆a)`. -/
theorem IsNPositive.star_map_mul_map_le (hφ : IsNPositive 2 φ) (a : A) :
    star (φ a) * φ a ≤ ‖φ 1‖ • φ (star a * a) := by
  set c := ‖φ 1‖ with hc
  rcases (norm_nonneg (φ 1)).eq_or_lt with h0 | hpos
  · rw [hφ.eq_zero_of_map_one (norm_eq_zero.mp h0.symm)]
    simp
  set b := φ a
  have hq := hφ.quadratic_nonneg a (c • 1) (-b)
  have hconj : star b * φ 1 * b ≤ c • (star b * b) :=
    CStarAlgebra.star_left_conjugate_le_norm_smul b (φ 1)
      (hφ.map_nonneg two_pos zero_le_one).isSelfAdjoint
  have key : 0 ≤ c • (c • φ (star a * a) - star b * b) :=
    calc 0 ≤ _ := hq
      _ = c • c • φ (star a * a) - c • (star b * b) - c • (star b * b) + star b * φ 1 * b := by
        simp [b, star_smul]
        abel
      _ ≤ c • c • φ (star a * a) - c • (star b * b) - c • (star b * b) + c • (star b * b) :=
        add_le_add_right hconj _
      _ = c • (c • φ (star a * a) - star b * b) := by
        rw [smul_sub]
        abel
  have := smul_nonneg (inv_nonneg.mpr hpos.le) key
  rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul, sub_nonneg] at this
  exact this

/-- A `2`-positive map with unital domain is bounded by `‖φ 1‖`. -/
theorem IsNPositive.norm_apply_le (hφ : IsNPositive 2 φ) (a : A) : ‖φ a‖ ≤ ‖φ 1‖ * ‖a‖ := by
  let ψ : A →ₚ[ℂ] B := .mk₀ φ fun _ ha => hφ.map_nonneg two_pos ha
  have hψ : ‖φ (star a * a)‖ ≤ ‖φ 1‖ * ‖star a * a‖ :=
    ψ.norm_apply_le_of_nonneg _ (star_mul_self_nonneg a)
  have h : ‖φ a‖ * ‖φ a‖ ≤ (‖φ 1‖ * ‖a‖) * (‖φ 1‖ * ‖a‖) := by
    rw [← CStarRing.norm_star_mul_self]
    calc ‖star (φ a) * φ a‖ ≤ ‖‖φ 1‖ • φ (star a * a)‖ :=
          CStarAlgebra.norm_le_norm_of_le_of_nonneg (hφ.star_map_mul_map_le a)
            (star_mul_self_nonneg _)
      _ = ‖φ 1‖ * ‖φ (star a * a)‖ := by rw [norm_smul, norm_norm]
      _ ≤ ‖φ 1‖ * (‖φ 1‖ * ‖star a * a‖) := by gcongr
      _ = (‖φ 1‖ * ‖a‖) * (‖φ 1‖ * ‖a‖) := by rw [CStarRing.norm_star_mul_self]; ring
  exact (mul_self_le_mul_self_iff (norm_nonneg _) (by positivity)).mpr h

end Unital

end TauCeti

namespace CompletelyPositiveMap

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **Kadison–Schwarz inequality** for a unital completely positive map:
`φ(a)⋆ φ(a) ≤ φ(a⋆a)`. -/
theorem star_map_mul_map_le (φ : A →CP B) (hφ : φ 1 = 1) (a : A) :
    star (φ a) * φ a ≤ φ (star a * a) :=
  (φ.isNPositive 2).star_map_mul_map_le_of_map_one hφ a

/-- A completely positive map with unital domain is bounded by `‖φ 1‖`. -/
theorem norm_apply_le (φ : A →CP B) (a : A) : ‖φ a‖ ≤ ‖φ 1‖ * ‖a‖ :=
  (φ.isNPositive 2).norm_apply_le a

/-- The operator norm of a completely positive map with unital domain is `‖φ 1‖`; the map is
continuous since positive maps between C⋆-algebras are. -/
theorem opNorm_eq_norm_map_one (φ : A →CP B) :
    ‖((PositiveContinuousLinearMap.ofClass φ : A →P[ℂ] B) : A →L[ℂ] B)‖ = ‖φ 1‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) φ.norm_apply_le) ?_
  rcases subsingleton_or_nontrivial A with hA | hA
  · simp [Subsingleton.elim (1 : A) 0]
  simpa using ((PositiveContinuousLinearMap.ofClass φ : A →P[ℂ] B) : A →L[ℂ] B).le_opNorm 1

end CompletelyPositiveMap

namespace TauCeti

open scoped ComplexOrder

variable (n : Type*) in
/-- The transpose on `n × n` complex matrices, as a complex-linear map. -/
@[expose] def cstarMatrixTranspose : CStarMatrix n n ℂ →ₗ[ℂ] CStarMatrix n n ℂ where
  toFun M := M.transpose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem cstarMatrixTranspose_apply {n : Type*} (M : CStarMatrix n n ℂ) (i j : n) :
    cstarMatrixTranspose n M i j = M j i :=
  rfl

/-- The transpose on `M₂(ℂ)` is unital but not `2`-positive: it violates the Schwarz inequality
at the matrix unit `E₁₂`, whose image `E₂₁` has `E₂₁⋆ E₂₁ = E₁₁`, while `E₁₂⋆ E₁₂ = E₂₂`. -/
theorem not_isNPositive_two_cstarMatrixTranspose :
    ¬ IsNPositive 2 (cstarMatrixTranspose (Fin 2)) := by
  intro h
  have h1 : cstarMatrixTranspose (Fin 2) 1 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  let a : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix !![0, 1; 0, 0]
  have hle := sub_nonneg.mpr (h.star_map_mul_map_le_of_map_one h1 a)
  have := CStarMatrix.apply_self_nonneg hle 0
  simp [a, CStarMatrix.mul_apply, CStarMatrix.star_apply, CStarMatrix.ofMatrix_apply,
    Fin.sum_univ_two] at this
  norm_num at this

end TauCeti
