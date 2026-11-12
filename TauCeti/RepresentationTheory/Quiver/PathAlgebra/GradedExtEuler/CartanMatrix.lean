/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedCartanMatrix
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedExtEuler.Pairing

/-!
# The q-Euler form of a path algebra and its graded Cartan matrix

Let `Q` be a finite quiver whose path algebra `kQ` is finite-dimensional, graded by path length.
Two computations of the same lattice meet here. The categorical q-Euler form on `G₀^gr(mod kQ)`
has matrix `1 - q⁻¹ A` in the basis of graded vertex simples, where the `(i, j)` entry of `A`
counts arrows `i ⟶ j` (`TauCeti.PathAlgebra.gradedExtEulerForm_basis`). The graded Cartan matrix
`C`, computed by counting paths, satisfies `(C.map invert)ᵀ (1 - q⁻¹ A) = 1`
(`TauCeti.PathAlgebra.gradedCartanMatrix_map_invert_transpose_mul_one_sub_T_neg_smul_eq_one`).
Together they identify `χ_q(Sᵢ, Sⱼ)` with the `(i, j)` entry of `((C.map invert)ᵀ)⁻¹`, the
path-algebra case of `TauCeti.gradedExtEuler_eq_inv_gradedCartanMatrix_map_invert_transpose`,
here obtained from the explicit formulas on both sides.

## Main results

* `TauCeti.PathAlgebra.gradedExtEulerForm_gradedVertexSimpleClassBasis_eq_inv`: the q-Euler
  matrix of the graded vertex simples is the inverse of the conjugate-transposed graded Cartan
  matrix.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Proposition 3.13, for the ungraded relation between the Cartan
  matrix and the Euler form.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Sections 2.2 and 3.1--3.2, for
  the q-antilinear convention and the conjugate-transpose relation.
-/

public section

noncomputable section

namespace TauCeti.PathAlgebra

open CategoryTheory LaurentPolynomial
open scoped Matrix

universe u v w

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q]
  [Fintype Q] [DecidableEq Q] [Module.Finite k (pathAlgebra k Q)]
  [HasExt.{max u v w} (GradedModuleCat.{max u v w} (integerGrade k Q))]

/-- **The q-Euler matrix of a path algebra is the inverse of its conjugate-transposed graded
Cartan matrix**: `χ_q(Sᵢ, Sⱼ)` is the `(i, j)` entry of `((C.map invert)ᵀ)⁻¹`, where `C` is the
graded Cartan matrix in the bases of graded vertex projectives and graded vertex simples. -/
theorem gradedExtEulerForm_gradedVertexSimpleClassBasis_eq_inv (i j : Q) :
    gradedExtEulerForm k Q (gradedVertexSimpleClassBasis k Q i)
        (gradedVertexSimpleClassBasis k Q j) =
      ((gradedCartanMatrix (integerGrade k Q) (gradedVertexProjectiveClassBasis k Q)
        (gradedVertexSimpleClassBasis k Q)).map (invert (R := ℤ)))ᵀ⁻¹ i j := by
  rw [Matrix.inv_eq_right_inv
      (gradedCartanMatrix_map_invert_transpose_mul_one_sub_T_neg_smul_eq_one k Q),
    gradedExtEulerForm_basis, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul]

end TauCeti.PathAlgebra
