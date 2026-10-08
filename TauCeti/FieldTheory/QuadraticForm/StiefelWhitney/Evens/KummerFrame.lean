/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Evens.KummerRepresentation

/-!
# Diagonalizing the induced Kummer representation

For a separable quadratic extension `L/K`, the points `kummerPoint σ r s y` realize the
twisted trace plane in the separable closure. Given orthogonal vectors `y₀, y₁` with
nonzero trace norms, divide their images by square roots `c₀, c₁` of those norms.
The resulting matrix `kummerFrame` is orthogonal. No separate basis hypothesis is
needed: the normalized columns are orthonormal and therefore form a basis.

`kummerFrame_conj` identifies the Galois-twisted conjugate of the induced signed
permutation representation with the diagonal signs of `c₀, c₁`. This supplies the
change of frame from the transferred plane to its diagonal trace form, used when
comparing their lifted cocycles and twisted boundaries.

## References

* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59**
  (1984), 651–676, second proof of Théorème 1′.
* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations
  galoisiennes réelles*, Invent. Math. **78** (1984), 223–256, Lemme II.2.1.
-/

public section

noncomputable section

open scoped Matrix

namespace TauCeti

open Matrix

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The frame whose `j`-th column is the Kummer point of `y j` divided by `c j`. -/
def kummerFrame (σ : L →ₐ[K] SeparableClosure K) (r : SeparableClosure K)
    (s : AbsoluteGaloisGroup K) (y : Fin 2 → L) (c : Fin 2 → SeparableClosure K) :
    Matrix (Fin 2) (Fin 2) (SeparableClosure K) :=
  Matrix.of fun i j => kummerPoint σ r s (y j) i / c j

/-- The entries of the normalized Kummer frame. -/
@[simp]
theorem kummerFrame_apply (σ : L →ₐ[K] SeparableClosure K) (r : SeparableClosure K)
    (s : AbsoluteGaloisGroup K) (y : Fin 2 → L) (c : Fin 2 → SeparableClosure K)
    (i j : Fin 2) : kummerFrame σ r s y c i j = kummerPoint σ r s (y j) i / c j := (rfl)

section Gram

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
  (σ : L →ₐ[K] SeparableClosure K) (hdeg : Module.finrank K L = 2)
  (a : L) (r : SeparableClosure K) (hr : r ^ 2 = σ a)
  (s : AbsoluteGaloisGroup K) (hs : s ∉ galoisSubgroup K L σ)
  (y : Fin 2 → L) (c : Fin 2 → SeparableClosure K)

include hdeg hr hs in
/-- The Gram matrix of the normalized columns is the twisted trace Gram matrix
divided by the corresponding products of normalizing roots. -/
theorem kummerFrame_transpose_mul_apply (i j : Fin 2) :
    ((kummerFrame σ r s y c)ᵀ * kummerFrame σ r s y c) i j =
      algebraMap K (SeparableClosure K) (Algebra.trace K L (a * y i * y j)) /
        (c i * c j) := by
  rw [← kummerPoint_dotProduct σ hdeg a r hr s hs]
  simp only [Matrix.mul_apply, transpose_apply, kummerFrame_apply, dotProduct,
    div_mul_div_comm, ← Finset.sum_div]

variable
  (hy : Algebra.trace K L (a * y 0 * y 1) = 0)
  (hc : ∀ i, c i ^ 2 = algebraMap K (SeparableClosure K)
    (Algebra.trace K L (a * y i ^ 2)))
  (hc0 : ∀ i, c i ≠ 0)

include hdeg hr hs hy hc hc0 in
/-- Normalizing orthogonal trace vectors by nonzero square roots of their norms
gives an orthogonal matrix. -/
theorem kummerFrame_mem_orthogonalGroup :
    kummerFrame σ r s y c ∈ orthogonalGroup (Fin 2) (SeparableClosure K) := by
  rw [mem_orthogonalGroup_iff']
  apply Matrix.ext
  intro i j
  rw [kummerFrame_transpose_mul_apply σ hdeg a r hr s hs]
  have hdiag (k : Fin 2) :
      algebraMap K (SeparableClosure K) (Algebra.trace K L (a * y k * y k)) =
        c k * c k := by
    simpa only [pow_two, mul_assoc] using (hc k).symm
  have hy' : Algebra.trace K L (a * y 1 * y 0) = 0 := by
    simpa only [mul_right_comm] using hy
  fin_cases i <;> fin_cases j <;> simp [hdiag, hy, hy', hc0]

end Gram

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
  (σ : L →ₐ[K] SeparableClosure K) (hdeg : Module.finrank K L = 2)
  (a : Lˣ) (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L))
  (s : AbsoluteGaloisGroup K) (hs : s ∉ galoisSubgroup K L σ)
  (y : Fin 2 → L) (c : Fin 2 → SeparableClosure K)
  (hy : Algebra.trace K L ((a : L) * y 0 * y 1) = 0)
  (hc : ∀ i, c i ^ 2 = algebraMap K (SeparableClosure K)
    (Algebra.trace K L ((a : L) * y i ^ 2)))
  (hc0 : ∀ i, c i ≠ 0)

include hy hc hc0 in
/-- Twisted conjugation by the normalized Kummer frame diagonalizes the induced
representation, with diagonal entries the signs of the normalizing roots. -/
theorem kummerFrame_conj (g : AbsoluteGaloisGroup K) :
    (kummerFrame σ r s y c)⁻¹ * wreathSignedPerm (kummerInd σ hdeg a r hr s hs g) *
        (kummerFrame σ r s y c).map g =
      diagonal (fun i => (-1 : SeparableClosure K) ^ (rootSign (c i) g).val) := by
  let P := kummerFrame σ r s y c
  let M : Matrix (Fin 2) (Fin 2) (SeparableClosure K) :=
    wreathSignedPerm (kummerInd σ hdeg a r hr s hs g)
  have hM : M * Mᵀ = 1 := (mem_orthogonalGroup_iff _ _).mp
    (wreathSignedPerm_mem_orthogonalGroup _)
  have hroot (j : Fin 2) : g (c j) = (-1) ^ (rootSign (c j) g).val * c j :=
    apply_eq_neg_one_pow_rootSign_mul (g.apply_eq_or_eq_neg_of_sq_eq (hc j))
  have haction (j : Fin 2) :
      M *ᵥ (fun i => g (kummerPoint σ r s (y j) i)) = kummerPoint σ r s (y j) := by
    rw [kummerPoint_galois σ hdeg a r hr s hs, mulVec_mulVec, hM, one_mulVec]
  have hMP : M * P.map g =
      P * diagonal (fun j => (-1 : SeparableClosure K) ^ (rootSign (c j) g).val) := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, Matrix.map_apply, P, kummerFrame_apply, map_div₀,
      ← mul_div_assoc, ← Finset.sum_div]
    rw [← Matrix.mulVec_apply_eq_sum, haction, hroot]
    simp [div_eq_mul_inv, ← inv_pow, mul_comm, mul_left_comm, mul_assoc]
  have hP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _
    (Matrix.isUnit_det_of_left_inverse ((mem_orthogonalGroup_iff' _ _).mp
      (kummerFrame_mem_orthogonalGroup σ hdeg (a : L) r hr s hs y c hy hc hc0)))
  calc
    P⁻¹ * M * P.map g = P⁻¹ * (M * P.map g) := Matrix.mul_assoc ..
    _ = _ := by rw [hMP, ← Matrix.mul_assoc, hP, Matrix.one_mul]

end TauCeti
