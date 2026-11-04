/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import TauCeti.Geometry.Symplectic.ExistsCompatible
public import TauCeti.LinearAlgebra.SesquilinearForm.AdjointPair

/-!
# Eigenvalues and symplectic splitting of the symplectic Lie algebra

Let `(V, ω)` be a finite-dimensional real symplectic vector space and let `A` be an element of
the symplectic Lie algebra `sp(V, ω)`, that is an endomorphism with `ω (A v) w = -ω v (A w)`.
This file records the eigenvalue structure of `A` on which Williamson's normal forms are built.

* The characteristic polynomial of `A` is even, `χ_A(-X) = χ_A(X)`
  (`TauCeti.SymplecticForm.charpoly_comp_neg_X`): the eigenvalues of `A` come in pairs `±μ`
  with equal multiplicities. Here the dimension of `V` is even, so the sign `(-1) ^ dim V` of the
  general skew-adjoint identity disappears.
* For an even real polynomial `p`, `p(-X) = p`, the vectors killed by a power of `p(A)` form a
  symplectic subspace (`TauCeti.SymplecticForm.isSymplectic_maxGenEigenspace_aeval`). The
  polynomials `X² - a²`, `X² + b²` and `(X² - 2aX + a² + b²)(X² + 2aX + a² + b²)` give the
  hyperbolic, elliptic and focus-focus summands. For coprime even polynomials the two summands
  are `ω`-orthogonal (`LinearMap.IsSkewAdjoint.apply_eq_zero_of_mem_maxGenEigenspace_aeval`).
* For a nonzero real `μ`, the generalized `μ`-eigenspace of `A` is isotropic
  (`TauCeti.SymplecticForm.isIsotropic_genEigenspace`), while `ω` pairs the maximal generalized
  `μ`- and `-μ`-eigenspaces nondegenerately
  (`LinearMap.IsSkewAdjoint.nondegenerate_domRestrict₁₂_maxGenEigenspace`).

The general statements for skew-adjoint endomorphisms of a nondegenerate bilinear form are in
`TauCeti.LinearAlgebra.SesquilinearForm.AdjointPair`.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Appendix 6.
-/

public section

open Module Polynomial

-- `sp(V, ω)` is a Lie subalgebra of `Module.End ℝ V` for the commutator bracket, as in Mathlib's
-- `Mathlib.Algebra.Lie.SkewAdjoint`.
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (ω : SymplecticForm V) {A : Module.End ℝ V}

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- An element of the symplectic Lie algebra `sp(V, ω)` has an even characteristic polynomial,
`χ_A(-X) = χ_A(X)`. -/
theorem charpoly_comp_neg_X (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) :
    A.charpoly.comp (-X) = A.charpoly := by
  rw [((LinearMap.mem_skewAdjointSubmodule A).1 hA).charpoly_comp_neg_X ω.nondegenerate,
    ω.even_finrank.neg_one_pow, one_mul]

/-- For an element `A` of `sp(V, ω)` and an even polynomial `p`, `p(-X) = p`, the vectors killed
by a power of `p(A)` form a symplectic subspace. -/
theorem isSymplectic_maxGenEigenspace_aeval (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm)
    {p : ℝ[X]} (hp : p.comp (-X) = p) : ω.IsSymplectic ((aeval A p).maxGenEigenspace 0) := by
  have hA' := (LinearMap.mem_skewAdjointSubmodule A).1 hA
  exact isSymplectic_iff_nondegenerate_restrict.2 <|
    hA'.nondegenerate_domRestrict₁₂_maxGenEigenspace_aeval_of_comp_neg_X_eq ω.nondegenerate hp

end FiniteDimensional

/-- For an element `A` of `sp(V, ω)` and a nonzero real `μ`, every generalized `μ`-eigenspace of
`A` is isotropic. -/
theorem isIsotropic_genEigenspace (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) {μ : ℝ}
    (hμ : μ ≠ 0) (k : ℕ∞) : ω.IsIsotropic (A.genEigenspace μ k) :=
  isIsotropic_iff.2 fun _ hv _ hw ↦
    ((LinearMap.mem_skewAdjointSubmodule A).1 hA).apply_eq_zero_of_mem_genEigenspace_self
      (by simpa using hμ) hv hw

end TauCeti.SymplecticForm
