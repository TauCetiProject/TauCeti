/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Projective
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedSimple

/-!
# The graded Cartan matrix of a path algebra

Let `Q` be a finite acyclic quiver, so that its path algebra `kQ` is finite-dimensional, and give
`kQ` its path-length grading. The degree-zero piece is spanned by the vertex idempotents `eᵢ`,
so the graded vertex projectives `kQ eᵢ` form a basis of `K₀^gr(proj kQ)` over `ℤ[q,q⁻¹]`
(`TauCeti.gradedIdempotentProjectiveBasis`), just as the graded vertex simples form a basis of
`G₀^gr(mod kQ)`.

In these two bases the graded Cartan matrix is the path-counting matrix: the coefficient of `qⁿ`
in its `(i, j)` entry is the number of paths of length `n` from `j` to `i`, and there are no
negative powers of `q`. Rows are indexed by simples and columns by projectives, following the
left-module convention for Cartan matrices.

## Main definitions

* `TauCeti.PathAlgebra.gradedVertexProjectiveClassBasis`: the basis `[kQ eᵢ]` of
  `K₀^gr(proj kQ)`.

## Main results

* `TauCeti.PathAlgebra.coeff_gradedCartanMatrix_gradedVertexProjectiveClassBasis`: the
  coefficient of `qⁿ` in the `(i, j)` entry of the graded Cartan matrix is the number of
  length-`n` paths `j ⟶ i`.
* `TauCeti.PathAlgebra.coeff_gradedCartanMatrix_gradedVertexProjectiveClassBasis_of_neg`:
  negative-degree coefficients vanish.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Section 3, for the Cartan matrix of a path algebra.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Section 2.2, for the graded
  Cartan matrix over `ℤ[q,q⁻¹]`.
-/

public section

noncomputable section

namespace TauCeti.PathAlgebra

open CategoryTheory

universe u v w

variable (k : Type w) (Q : Type u) [Quiver.{v} Q] [Field k] [Finite Q]
  [FiniteDimensional k (pathAlgebra k Q)]

/-- **The vertex-projective basis of `K₀^gr(proj kQ)`** over `ℤ[q,q⁻¹]`, for a finite acyclic
quiver: its vector at `i` is the class `[kQ eᵢ]` of the graded vertex projective. -/
def gradedVertexProjectiveClassBasis :
    Module.Basis Q (LaurentPolynomial ℤ)
      (LaurentK0.{max u v w}
        (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))) :=
  let _ := integerGradedAlgebra k Q
  let _ := Fintype.ofFinite Q
  gradedIdempotentProjectiveBasis (completeOrthogonalIdempotents_vertexIdempotent k Q)
    (vertexIdempotent_mem_integerGrade_zero k Q) (isHomogeneous_span_vertexIdempotent k Q)
    (fun _ => integerGrade_eq_bot_of_neg k Q)
    (integerGrade_zero_eq_span_range_vertexIdempotent k Q).le vertexIdempotent_ne_zero

/-- The basis vector of `TauCeti.PathAlgebra.gradedVertexProjectiveClassBasis` at `i` is the
class `[kQ eᵢ]`. -/
@[simp]
theorem gradedVertexProjectiveClassBasis_apply (i : Q) :
    gradedVertexProjectiveClassBasis k Q i = gradedVertexProjectiveClass k Q i := by
  let _ := integerGradedAlgebra k Q
  let _ := Fintype.ofFinite Q
  unfold gradedVertexProjectiveClassBasis
  rw [gradedIdempotentProjectiveBasis_apply, gradedVertexProjectiveClass_eq]
  congr 2
  exact (gradedVertexProjective_def k Q i).symm

/-- **The graded Cartan matrix of a path algebra counts paths by length.** In the bases of graded
vertex projectives and graded vertex simples, the coefficient of `qⁿ` in the `(i, j)` entry is
the number of paths of length `n` from `j` to `i`. -/
theorem coeff_gradedCartanMatrix_gradedVertexProjectiveClassBasis [Fintype Q] (i j : Q) (n : ℕ) :
    (gradedCartanMatrix (integerGrade k Q) (gradedVertexProjectiveClassBasis k Q)
        (gradedVertexSimpleClassBasis k Q) i j).coeff n =
      Nat.card (PathBetween Q n j i) := by
  rw [gradedCartanMatrix_apply, gradedVertexSimpleClassBasis_repr_apply,
    gradedVertexProjectiveClassBasis_apply, coeff_gradedCartanMap_gradedVertexProjectiveClass]

/-- The entries of the graded Cartan matrix of a path algebra have no negative powers of `q`. -/
theorem coeff_gradedCartanMatrix_gradedVertexProjectiveClassBasis_of_neg [Fintype Q] (i j : Q)
    (d : ℤ) (hd : d < 0) :
    (gradedCartanMatrix (integerGrade k Q) (gradedVertexProjectiveClassBasis k Q)
        (gradedVertexSimpleClassBasis k Q) i j).coeff d = 0 := by
  rw [gradedCartanMatrix_apply, gradedVertexSimpleClassBasis_repr_apply,
    gradedVertexProjectiveClassBasis_apply,
    coeff_gradedCartanMap_gradedVertexProjectiveClass_of_neg k Q i j d hd]

end TauCeti.PathAlgebra
