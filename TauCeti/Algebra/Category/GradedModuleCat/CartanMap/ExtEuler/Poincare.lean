/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.Matrix
public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.ProjectiveCover
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.LinearResolution

/-!
# The graded Cartan matrix and the diagonal Ext Poincaré matrix

Let `A` be a finite-dimensional graded algebra over a field `k`, let the `Sᵢ` be concentrated
in internal degree zero, and let `C` be the graded Cartan matrix in a projective basis of classes
`[A eᵢ]` and a module basis `[Sⱼ]`. The **diagonal Ext Poincaré matrix** `P(t)` has `(i, j)` entry
`∑ n, dim_k Extⁿ(Sᵢ, Sⱼ{n}) tⁿ` (`TauCeti.diagonalExtPoincareMatrix`, truncated below a
cohomological vanishing bound).

If every pair of finite graded modules is graded Euler-admissible, every `Sᵢ` has a linear
graded projective resolution, and `gdim(eᵢ • Sⱼ) = 0` for `i ≠ j`, then
`Cᵀ · P(-q) = diagonal (fun i ↦ gdim(eᵢ • Sᵢ))`. When `Aeᵢ` covers the simple `Sᵢ`, the
corresponding diagonal entry is the constant `dim_k End_A(Sᵢ)`. This retains the division-algebra
factor over a general field. If all these dimensions are one, the identity says that `P(-q)` is
the inverse of `Cᵀ`.

The identity follows from the conjugate-transpose relation between the graded Cartan and q-Euler
matrices. For a linearly resolved source and a degree-zero target,
`invert χ_q(Sᵢ, Sⱼ) = Pᵢⱼ(-q)`
(`TauCeti.GradedProjectiveResolution.IsLinear.invert_gradedExtEuler_eq_eval₂`). The constant
diagonal is fixed by the Laurent involution.

## Main results

* `TauCeti.gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_diagonal`:
  `Cᵀ · P(-q) = diagonal (fun i ↦ gdim(eᵢ • Sᵢ))`.
* `TauCeti.gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_diagonal_finrank_end`:
  for actual projective covers of simples, the diagonal entries are `dim_k End_A(Sᵢ)`.
* `TauCeti.diagonalExtPoincareMatrix_map_eq_inv_gradedCartanMatrix_transpose`:
  `P(-q) = (Cᵀ)⁻¹` when all diagonal idempotent dimensions are one.

A common truncation degree for finitely many simples exists by
`TauCeti.exists_forall_isGradedExtBoundedBy`, and the truncated matrix does not depend on its
choice (`TauCeti.diagonalExtPoincareMatrix_eq_of_le`).

## References

* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  *Journal of the AMS* **9** (1996), Section 2.11, for the identity between the
  Hilbert matrix of a Koszul ring and the Poincaré matrix of its Ext algebra at `-t`.
* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Section 2.2, for the q-Euler convention and the
  graded Cartan matrix.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial
open scoped Matrix

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [Module.Finite k A]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI} [Fintype I] [DecidableEq I]
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)
  (bM : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
  (hbM : ∀ i, bM i = LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (S i))

include he₀ hne hbP hbM in
/-- **The general-field Cartan--Poincaré identity.** Let `C` be the
graded Cartan matrix in a projective basis of classes `[A eᵢ]` and the module basis
`[Sⱼ]`, with `gdim(eᵢ • Sⱼ) = 0` for `i ≠ j`. Suppose every pair of finite graded modules is
graded Euler-admissible, that every `Sᵢ` is concentrated in internal degree zero and has a linear
graded projective resolution, and that `b` bounds the cohomological support of Ext between any two
`Sᵢ`.
Then `Cᵀ · P(-q) = diagonal (fun i ↦ gdim(eᵢ • Sᵢ))`, where `P` is the diagonal Ext
Poincaré matrix truncated below `b`. Concentration makes these diagonal entries constant. -/
theorem gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_diagonal
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (hlin : ∀ i, ∃ r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading,
      r.IsLinear)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) {b : ℕ}
    (hb : ∀ i j, IsGradedExtBoundedBy.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj b) :
    (gradedCartanMatrix 𝒜 bP bM)ᵀ *
        (diagonalExtPoincareMatrix.{uA} k (fun i ↦ (S i).obj) b).map
          (Polynomial.eval₂RingHom C (-T 1)) =
      Matrix.diagonal fun i ↦ (S i).obj.smulGradedDimension (e i) := by
  have key := congrArg (Matrix.map · (LaurentPolynomial.invert (R := ℤ)))
    (gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_diagonal
      S he he₀ hI hne bP hbP bM hbM h)
  have hdiag : (Matrix.diagonal fun i ↦ (S i).obj.smulGradedDimension (e i)).map
      (LaurentPolynomial.invert (R := ℤ)) =
        Matrix.diagonal fun i ↦ (S i).obj.smulGradedDimension (e i) := by
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    rw [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hconc i), invert_C]
  rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, involutive_invert.comp_self,
    Matrix.map_id, hdiag] at key
  convert key using 2
  refine Matrix.ext fun i j ↦ ?_
  obtain ⟨r, hr⟩ := hlin i
  rw [Matrix.map_apply, Matrix.map_apply, diagonalExtPoincareMatrix_apply,
    gradedExtEulerMatrix_of_of (X := S i) (Y := S j) (hi := hbM i)
      (hj := hbM j),
    hr.invert_gradedExtEuler_eq_eval₂ (hconc j) _ (hb i j), Polynomial.coe_eval₂RingHom]

include he₀ hne hbP hbM in
/-- **The division-endomorphism correction to the Cartan--Poincaré identity.** If the `Aeᵢ`
cover the degree-zero simples `Sᵢ`, the diagonal is `dim_k End_A(Sᵢ)`, without a splitting-field
hypothesis. -/
theorem gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_diagonal_finrank_end
    [∀ i, IsSimpleModule A (S i).obj]
    {f : ∀ i, (Ideal.span {e i} : Ideal A) →ₗ[A] (S i).obj}
    (hf : ∀ i, IsProjectiveCover (f i))
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (hlin : ∀ i, ∃ r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading,
      r.IsLinear)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) {b : ℕ}
    (hb : ∀ i j, IsGradedExtBoundedBy.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj b) :
    (gradedCartanMatrix 𝒜 bP bM)ᵀ *
        (diagonalExtPoincareMatrix.{uA} k (fun i ↦ (S i).obj) b).map
          (Polynomial.eval₂RingHom C (-T 1)) =
      Matrix.diagonal fun i ↦ C (Module.finrank k (Module.End A (S i).obj) : ℤ) := by
  rw [gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_diagonal
    S he he₀ hI hne bP hbP bM hbM h hlin hconc hb]
  congr 1
  funext i
  exact (S i).obj.smulGradedDimension_eq_C_finrank_end_of_isProjectiveCover
    (he i) (hconc i) (hf i)

variable (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
  (hS : IsExhaustiveGradedSimpleFamily S)

include hbP in
/-- **The diagonal Ext Poincaré matrix at `-q` is the inverse of the transposed graded Cartan
matrix**: `P(-q) = (Cᵀ)⁻¹`, under the hypotheses of
`TauCeti.gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_diagonal`,
when all the idempotent diagonal dimensions are one. -/
theorem diagonalExtPoincareMatrix_map_eq_inv_gradedCartanMatrix_transpose
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (hlin : ∀ i, ∃ r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading,
      r.IsLinear)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) {b : ℕ}
    (hb : ∀ i j, IsGradedExtBoundedBy.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj b) :
    (diagonalExtPoincareMatrix.{uA} k (fun i ↦ (S i).obj) b).map
        (Polynomial.eval₂RingHom C (-T 1)) =
      (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasis S he he₀ hne hself hS))ᵀ⁻¹ :=
  (Matrix.inv_eq_right_inv (by
    simpa only [hself, Matrix.diagonal_one] using
      gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_diagonal
        S he he₀ hI hne bP hbP (gradedSimpleClassBasis S he he₀ hne hself hS)
        (fun i ↦ gradedSimpleClassBasis_apply S he he₀ hne hself hS i) h hlin hconc hb)).symm

end TauCeti
