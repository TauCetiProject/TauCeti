/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.Matrix
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.LinearResolution

/-!
# The graded Cartan matrix and the diagonal Ext Poincaré matrix

Let `A` be a finite-dimensional graded algebra over a field `k`, let `Sᵢ` be an exhaustive family
of graded simples concentrated in internal degree zero, and let `C` be the graded Cartan matrix in
a projective basis of classes `[A eᵢ]` and the graded simple-class basis `[Sⱼ]`. The **diagonal Ext
Poincaré matrix** `P(t)` has `(i, j)` entry `∑ n, dim_k Extⁿ(Sᵢ, Sⱼ{n}) tⁿ`
(`TauCeti.diagonalExtPoincareMatrix`, truncated below a cohomological vanishing bound).

If every pair of finite graded modules is graded Euler-admissible and every `Sᵢ` has a linear
graded projective resolution, then `Cᵀ · P(-q) = 1`: the graded Cartan matrix and the diagonal
Ext Poincaré matrix are inverse to each other up to transposition and the substitution `t ↦ -q`.
For a Koszul algebra the diagonal groups `Extⁿ(Sᵢ, Sⱼ{n})` make up the whole Ext algebra, which is
the quadratic dual `A^!` up to taking the opposite ring, and the identity is the matrix form of the
classical relation between the Hilbert series of `A` and of `A^!` at `-q`.

The identity specializes the conjugate-transpose relation `Cᴴ · E = 1` between the graded Cartan
matrix and the q-Euler matrix `E` of the graded simples
(`TauCeti.gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_one`), which holds
without any linearity hypothesis. For linearly resolved simples concentrated in degree zero,
`invert χ_q(Sᵢ, Sⱼ) = Pᵢⱼ(-q)`
(`TauCeti.GradedProjectiveResolution.IsLinear.invert_gradedExtEuler_eq_eval₂`).

## Main results

* `TauCeti.gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_one`:
  `Cᵀ · P(-q) = 1`.
* `TauCeti.diagonalExtPoincareMatrix_map_eq_inv_gradedCartanMatrix_transpose`:
  `P(-q) = (Cᵀ)⁻¹`.

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
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
  (hS : IsExhaustiveGradedSimpleFamily S)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)

include hbP in
/-- **The graded Cartan matrix inverts the diagonal Ext Poincaré matrix at `-q`.** Let `C` be the
graded Cartan matrix in a projective basis of classes `[A eᵢ]` and the graded simple-class basis
`[Sⱼ]`, with `gdim(eᵢ • Sⱼ) = δᵢⱼ`. Suppose that every pair of finite graded modules is graded
Euler-admissible, that every `Sᵢ` is concentrated in internal degree zero and has a linear graded
projective resolution, and that `b` bounds the cohomological support of Ext between any two `Sᵢ`.
Then `Cᵀ · P(-q) = 1`, where `P` is the diagonal Ext Poincaré matrix of the `Sᵢ` truncated
below `b`. -/
theorem gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_one
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (hlin : ∀ i, ∃ r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading,
      r.IsLinear)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) {b : ℕ}
    (hb : ∀ i j, IsGradedExtBoundedBy.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj b) :
    (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasis S he he₀ hne hself hS))ᵀ *
        (diagonalExtPoincareMatrix.{uA} k (fun i ↦ (S i).obj) b).map
          (Polynomial.eval₂RingHom C (-T 1)) = 1 := by
  have key := congrArg (Matrix.map · (LaurentPolynomial.invert (R := ℤ)))
    (gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_one S he he₀ hI hne
      hself hS bP hbP h)
  rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, involutive_invert.comp_self,
    Matrix.map_id, Matrix.map_one _ (map_zero _) (map_one _)] at key
  convert key using 2
  refine Matrix.ext fun i j ↦ ?_
  obtain ⟨r, hr⟩ := hlin i
  rw [Matrix.map_apply, Matrix.map_apply, diagonalExtPoincareMatrix_apply,
    gradedExtEulerMatrix_of_of (X := S i) (Y := S j) (hi := gradedSimpleClassBasis_apply ..)
      (hj := gradedSimpleClassBasis_apply ..),
    hr.invert_gradedExtEuler_eq_eval₂ (hconc j) _ (hb i j), Polynomial.coe_eval₂RingHom]

include hbP in
/-- **The diagonal Ext Poincaré matrix at `-q` is the inverse of the transposed graded Cartan
matrix**: `P(-q) = (Cᵀ)⁻¹`, under the hypotheses of
`TauCeti.gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_one`. -/
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
  (Matrix.inv_eq_right_inv
    (gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_one S he he₀ hI hne hself
      hS bP hbP h hlin hconc hb)).symm

end TauCeti
