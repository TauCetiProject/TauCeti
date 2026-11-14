/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FromMatrix
public import TauCeti.Algebra.Coalgebra.Comodule.Schur
public import TauCeti.Algebra.Coalgebra.Comodule.Unitarization
public import TauCeti.Algebra.HopfAlgebra.Integral.Haar
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Conjugate comodules and weighted Schur orthogonality

Let `A` be a star bialgebra over a commutative star ring `R`, and let `M` be a right `A`-comodule
with a finite basis `b` and coefficient matrix `u`. Because comultiplication and the counit of a
star coalgebra commute with `star`, the entrywise conjugate matrix `u.map star` is again a
multiplicative matrix (`TauCeti.Comodule.conjugateMatrixComodule`). Over a commutative ring `R` over
which `A` is projective, coordinatewise conjugation induces an order isomorphism between the
subcomodule lattices of `M` and `conjugateMatrixComodule b`, preserving simplicity, and identifies
the coefficient submodule of `conjugateMatrixComodule b` with the `star`-image of that of `M`.

For left or right invariant integrals `h : A →ₗ[R] R`, contractions of products of entries of `u`
and `star v` assemble into intertwiners between `M` and `N`. Consequently, when there is no nonzero
comodule morphism `N → M`, the matrix coefficients of `M` and `N` are cross-orthogonal under `h`.

Over a complex Hopf star algebra `A`, for a simple comodule `M` with basis `b` whose coefficient
matrix `u` is unitary, any positive definite matrix `G` invariant under `u.map star` normalizes to a
unique positive definite matrix `Ft` with `Ft.trace = Ft⁻¹.trace` satisfying the weighted Schur
orthogonality relations

* `h (star (u i j) * u k l) = if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0`,
* `h (u i j * star (u k l)) = if i = k then Ft j l / Ft.trace else 0`,

and whose transpose intertwines `u` with its double antipode `(u.map S).map S`. When `h` is an
`AlgebraicHaar` functional, the Haar Gram matrix of `conjugateMatrixComodule b` supplies `G`, giving
`Module.Basis.schur_orthogonality` and `TauCeti.Comodule.IsUnitary.schur_orthogonality`.

## Main declarations

* `TauCeti.Comodule.conjugateMatrixComodule`: the right comodule on `ι → R` with coefficient matrix
  `(coefficientMatrix b).map star`.
* `TauCeti.Comodule.conjugateSubcomoduleOrderIso`: order isomorphism between `Subcomodule R A M` and
  `Subcomodule R A (ι → R)` for `conjugateMatrixComodule b`.
* `LinearMap.IsLeftInvariantIntegral.map_coefficientMatrix_mul_star_eq_zero` and
  `LinearMap.IsRightInvariantIntegral.map_star_coefficientMatrix_mul_eq_zero`: cross-orthogonality
  between comodules with no nonzero morphism between them.
* `Module.Basis.existsUnique_posDef_schur_orthogonality_of_conjInvariant`: weighted Schur
  orthogonality from any positive definite conjugate-invariant matrix (without assuming positivity
  of `h` globally on `A`).
* `Module.Basis.schur_orthogonality` and `TauCeti.Comodule.IsUnitary.schur_orthogonality`:
  weighted Schur orthogonality for an `AlgebraicHaar` functional on a complex Hopf star algebra.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Proposition 3.2.9.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Theorem 1.4.2.
* S. L. Woronowicz, *Compact matrix pseudogroups*, Comm. Math. Phys. 111 (1987), 613–665.
-/

public section

open Module Matrix TauCeti TauCeti.Comodule
open scoped TensorProduct ComplexOrder

namespace TauCeti.Comodule

section ConjugateMatrixComodule

variable {R A M ι : Type*} [CommSemiring R] [StarRing R]
  [Semiring A] [StarRing A] [Bialgebra R A] [StarModule R A] [StarCoalgebra R A]
  [AddCommMonoid M] [Module R M] [Comodule R A M] [Fintype ι]

private theorem map_star_coefficientMatrix_comul (b : Basis ι R M) :
    ((coefficientMatrix (C := A) b).map star).map (Bialgebra.comulAlgHom R A) =
      ((coefficientMatrix (C := A) b).map star).map
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        ((coefficientMatrix (C := A) b).map star).map
          (Algebra.TensorProduct.includeRight (R := R)) := by
  rw [map_comul_iff]
  intro i j
  simp [Matrix.map_apply, star_sum]

omit [Fintype ι] in
private theorem map_star_coefficientMatrix_counit [Finite ι] (b : Basis ι R M) :
    ∀ i j, Coalgebra.counit (R := R) (((coefficientMatrix (C := A) b).map star) i j) =
      (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i := by
  classical
  refine counit_basisFun_of_map_counit R _ ?_
  rw [map_counit_iff]
  intro i j
  simp [Matrix.map_apply, apply_ite star]

/-- The **conjugate matrix comodule** associated to a finite basis `b` of a right comodule `M` over
a star bialgebra `A`: the right coaction on `ι → R` whose coefficient matrix in the standard basis
`Pi.basisFun R ι` is `(coefficientMatrix b).map star`. -/
@[instance_reducible]
noncomputable def conjugateMatrixComodule (b : Basis ι R M) : Comodule R A (ι → R) :=
  matrixComodule R ((coefficientMatrix (C := A) b).map star)
    (map_star_coefficientMatrix_comul b) (map_star_coefficientMatrix_counit b)

/-- The coaction of `conjugateMatrixComodule b` is `matrixCoact` of
`(coefficientMatrix b).map star`. -/
theorem conjugateMatrixComodule_coact (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := conjugateMatrixComodule b
    coact (R := R) (C := A) (M := ι → R) =
      matrixCoact R ((coefficientMatrix (C := A) b).map star) :=
  matrixComodule_coact R ((coefficientMatrix (C := A) b).map star)
    (map_star_coefficientMatrix_comul b) (map_star_coefficientMatrix_counit b)

/-- The coefficient matrix of `conjugateMatrixComodule b` in `Pi.basisFun R ι` is the entrywise star
of `coefficientMatrix b`. -/
theorem coefficientMatrix_conjugateMatrixComodule (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := conjugateMatrixComodule b
    coefficientMatrix (C := A) (Pi.basisFun R ι) = (coefficientMatrix (C := A) b).map star :=
  coefficientMatrix_matrixComodule R ((coefficientMatrix (C := A) b).map star)
    (map_star_coefficientMatrix_comul b) (map_star_coefficientMatrix_counit b)

/-- Membership in the matrix-coefficient submodule of `conjugateMatrixComodule b` is equivalent to
`star`-membership in the matrix-coefficient submodule of `M`. -/
theorem mem_matrixCoefficientSubmodule_conjugateMatrixComodule_iff (b : Basis ι R M) {a : A} :
    letI : Comodule R A (ι → R) := conjugateMatrixComodule b
    a ∈ matrixCoefficientSubmodule (R := R) (C := A) (M := ι → R) ↔
      star a ∈ matrixCoefficientSubmodule (R := R) (C := A) (M := M) := by
  let _ : Comodule R A (ι → R) := conjugateMatrixComodule b
  rw [mem_matrixCoefficientSubmodule_iff_exists_matrix (Pi.basisFun R ι),
    mem_matrixCoefficientSubmodule_iff_exists_matrix b, coefficientMatrix_conjugateMatrixComodule]
  constructor
  · rintro ⟨X, rfl⟩
    refine ⟨X.map star, ?_⟩
    simp [star_sum, star_smul]
  · intro ⟨X, hX⟩
    refine ⟨X.map star, ?_⟩
    have := congrArg star hX
    simpa [star_sum, star_smul] using this

end ConjugateMatrixComodule

section ConjugateSubcomodule

variable {R A M ι : Type*} [CommRing R] [StarRing R]
  [Ring A] [StarRing A] [Bialgebra R A] [Module.Projective R A] [StarModule R A] [StarCoalgebra R A]
  [AddCommGroup M] [Module R M] [Comodule R A M] [Fintype ι]

/-- The conjugate-linear equivalence `M ≃ₛₗ[starRingEnd R] (ι → R)` sending a vector to the
entrywise conjugate of its coordinate tuple in the basis `b`. -/
noncomputable def conjugateLinearEquiv (b : Basis ι R M) : M ≃ₛₗ[starRingEnd R] (ι → R) where
  toFun m i := star (b.repr m i)
  invFun x := ∑ i, star (x i) • b i
  left_inv m := by simp
  right_inv x := by
    classical
    ext i
    simp [Finsupp.single_apply]
  map_add' x y := by
    ext i
    simp
  map_smul' r x := by
    ext i
    simp [starRingEnd_apply]

/-- Evaluating `conjugateLinearEquiv b` at a vector returns its conjugated coordinate tuple. -/
@[simp]
theorem conjugateLinearEquiv_apply (b : Basis ι R M) (m : M) (i : ι) :
    conjugateLinearEquiv b m i = star (b.repr m i) :=
  (rfl)

/-- Evaluating `(conjugateLinearEquiv b).symm` reconstructs a vector from conjugated coordinates. -/
theorem conjugateLinearEquiv_symm_apply (b : Basis ι R M) (x : ι → R) :
    (conjugateLinearEquiv b).symm x = ∑ i, star (x i) • b i :=
  (rfl)

/-- `conjugateLinearEquiv b` sends the `j`-th basis vector to the `j`-th standard basis vector. -/
@[simp]
theorem conjugateLinearEquiv_basis (b : Basis ι R M) (j : ι) :
    conjugateLinearEquiv b (b j) = Pi.basisFun R ι j := by
  classical
  ext i
  simp [conjugateLinearEquiv, Pi.basisFun_apply, Pi.single_apply, Finsupp.single_apply,
    apply_ite star, eq_comm]

private def dualStar (f : A →ₗ[R] R) : A →ₗ[R] R where
  toFun a := star (f (star a))
  map_add' x y := by simp
  map_smul' r x := by simp

omit [Module.Projective R A] in
private theorem coactComponent_conjugateLinearEquiv (b : Basis ι R M) (f : A →ₗ[R] R) (m : M) :
    letI : Comodule R A (ι → R) := conjugateMatrixComodule b
    coactComponent (R := R) (C := A) (M := ι → R) f (conjugateLinearEquiv b m) =
      conjugateLinearEquiv b (coactComponent (R := R) (C := A) (M := M) (dualStar f) m) := by
  let _ : Comodule R A (ι → R) := conjugateMatrixComodule b
  conv_lhs => rw [← b.sum_repr m]
  conv_rhs => rw [← b.sum_repr m]
  simp only [map_sum, map_smulₛₗ, conjugateLinearEquiv_basis]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  rw [coactComponent_apply, coactComponent_apply, conjugateMatrixComodule_coact,
    matrixCoact_apply_basisFun, coact_basis_eq_sum_coefficientMatrix b j, map_sum, map_sum,
    map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.tensorComponent_tmul, LinearMap.tensorComponent_tmul, map_smulₛₗ,
    conjugateLinearEquiv_basis]
  simp [dualStar, starRingEnd_apply]

private theorem map_conjugateLinearEquiv_coact_mem (b : Basis ι R M) (S : Subcomodule R A M) :
    letI : Comodule R A (ι → R) := conjugateMatrixComodule b
    ∀ y ∈ S.toSubmodule.map (conjugateLinearEquiv b).toLinearMap,
      coact (R := R) (C := A) y ∈
        LinearMap.range
          (TensorProduct.map (S.toSubmodule.map (conjugateLinearEquiv b).toLinearMap).subtype
            LinearMap.id) := by
  let _ : Comodule R A (ι → R) := conjugateMatrixComodule b
  rintro _ ⟨m, hm, rfl⟩
  rw [Submodule.tensor_mem_range_iff_forall_tensorComponent_mem]
  intro f
  rw [LinearEquiv.coe_toLinearMap, ← coactComponent_apply, coactComponent_conjugateLinearEquiv]
  have hmem : coactComponent (R := R) (C := A) (M := M) (dualStar f) m ∈ S := by
    rw [coactComponent_apply, LinearMap.tensorComponent_def, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap]
    exact S.rid_lTensor_coact_mem (dualStar f) hm
  exact ⟨_, hmem, rfl⟩

private theorem map_conjugateLinearEquiv_symm_coact_mem (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := conjugateMatrixComodule b
    ∀ (T : Subcomodule R A (ι → R)) (m : M),
      m ∈ T.toSubmodule.map (conjugateLinearEquiv b).symm.toLinearMap →
        coact (R := R) (C := A) m ∈
          LinearMap.range
            (TensorProduct.map (T.toSubmodule.map (conjugateLinearEquiv b).symm.toLinearMap).subtype
              LinearMap.id) := by
  let _ : Comodule R A (ι → R) := conjugateMatrixComodule b
  rintro T _ ⟨y, hy, rfl⟩
  rw [Submodule.tensor_mem_range_iff_forall_tensorComponent_mem]
  intro f
  have hds : dualStar (dualStar f) = f := by
    ext a
    simp [dualStar]
  have hcomp : coactComponent (R := R) (C := A) (M := M) f ((conjugateLinearEquiv b).symm y) =
      (conjugateLinearEquiv b).symm
        (coactComponent (R := R) (C := A) (M := ι → R) (dualStar f) y) := by
    calc coactComponent (R := R) (C := A) (M := M) f ((conjugateLinearEquiv b).symm y)
        = (conjugateLinearEquiv b).symm (conjugateLinearEquiv b
            (coactComponent (R := R) (C := A) (M := M) (dualStar (dualStar f))
              ((conjugateLinearEquiv b).symm y))) := by
            rw [hds, (conjugateLinearEquiv b).symm_apply_apply]
      _ = (conjugateLinearEquiv b).symm (coactComponent (R := R) (C := A) (M := ι → R) (dualStar f)
            (conjugateLinearEquiv b ((conjugateLinearEquiv b).symm y))) := by
            rw [← coactComponent_conjugateLinearEquiv]
      _ = (conjugateLinearEquiv b).symm
            (coactComponent (R := R) (C := A) (M := ι → R) (dualStar f) y) := by
            rw [(conjugateLinearEquiv b).apply_symm_apply]
  rw [LinearEquiv.coe_toLinearMap, ← coactComponent_apply, hcomp]
  have hmem : coactComponent (R := R) (C := A) (M := ι → R) (dualStar f) y ∈ T := by
    rw [coactComponent_apply, LinearMap.tensorComponent_def, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap]
    exact T.rid_lTensor_coact_mem (dualStar f) hy
  exact ⟨_, hmem, rfl⟩

/-- Coordinatewise conjugation in a finite basis `b` induces an order isomorphism between the
subcomodule lattice of `M` and that of `conjugateMatrixComodule b`. -/
noncomputable def conjugateSubcomoduleOrderIso (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := conjugateMatrixComodule b
    Subcomodule R A M ≃o Subcomodule R A (ι → R) :=
  letI : Comodule R A (ι → R) := conjugateMatrixComodule b
  { toFun S := Subcomodule.ofSubmodule
      (S.toSubmodule.map (conjugateLinearEquiv b).toLinearMap)
      (map_conjugateLinearEquiv_coact_mem b S)
    invFun T := Subcomodule.ofSubmodule
      (T.toSubmodule.map (conjugateLinearEquiv b).symm.toLinearMap)
      (map_conjugateLinearEquiv_symm_coact_mem b T)
    left_inv S := by
      ext m
      simp
    right_inv T := by
      ext y
      simp
    map_rel_iff' := by
      intro S₁ S₂
      constructor
      · intro h m hm
        obtain ⟨m', hm', heq⟩ := h ⟨m, hm, rfl⟩
        exact (conjugateLinearEquiv b).injective heq ▸ hm'
      · rintro h _ ⟨m, hm, rfl⟩
        exact ⟨m, h hm, rfl⟩ }

omit [Module.Projective R A] in
private theorem mem_map_conjugateLinearEquiv_iff (b : Basis ι R M) (S : Submodule R M)
    (y : ι → R) :
    y ∈ S.map (conjugateLinearEquiv b).toLinearMap ↔ (conjugateLinearEquiv b).symm y ∈ S := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    simpa using hm
  · intro hy
    exact ⟨(conjugateLinearEquiv b).symm y, hy, by simp⟩

/-- Membership in `conjugateSubcomoduleOrderIso b S` reduces to `(conjugateLinearEquiv b).symm`. -/
@[simp]
theorem mem_conjugateSubcomoduleOrderIso_iff (b : Basis ι R M) (S : Subcomodule R A M)
    (y : ι → R) :
    letI : Comodule R A (ι → R) := conjugateMatrixComodule b
    y ∈ conjugateSubcomoduleOrderIso b S ↔ (conjugateLinearEquiv b).symm y ∈ S :=
  mem_map_conjugateLinearEquiv_iff b S.toSubmodule y

/-- Membership in `(conjugateSubcomoduleOrderIso b).symm T` reduces to `conjugateLinearEquiv b`. -/
@[simp]
theorem mem_conjugateSubcomoduleOrderIso_symm_iff (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := conjugateMatrixComodule b
    ∀ (T : Subcomodule R A (ι → R)) (m : M),
      m ∈ (conjugateSubcomoduleOrderIso b).symm T ↔ conjugateLinearEquiv b m ∈ T := by
  let _ : Comodule R A (ι → R) := conjugateMatrixComodule b
  intro T m
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hm
    exact ⟨conjugateLinearEquiv b m, hm, by simp⟩

/-- If `M` is a simple comodule, then `conjugateMatrixComodule b` is also simple. -/
theorem isSimpleOrder_conjugateMatrixComodule [IsSimpleOrder (Subcomodule R A M)]
    (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := conjugateMatrixComodule b
    IsSimpleOrder (Subcomodule R A (ι → R)) := by
  let _ : Comodule R A (ι → R) := conjugateMatrixComodule b
  exact (conjugateSubcomoduleOrderIso b).symm.isSimpleOrder

end ConjugateSubcomodule

end TauCeti.Comodule

section IntertwinersAndCrossOrthogonality

variable {R A M N ι κ : Type*} [CommSemiring R] [StarRing R]
  [Semiring A] [StarRing A] [Bialgebra R A] [StarModule R A] [StarCoalgebra R A]
  [AddCommMonoid M] [Module R M] [Comodule R A M]
  [AddCommMonoid N] [Module R N] [Comodule R A N]

namespace LinearMap

/-- For a left invariant integral `h` and a basis `c` whose coefficient matrix `v` satisfies
`vᴴ * v = 1`, the matrix `E m r := h (u m p * star (v r q))` intertwines `v` and `u`. -/
theorem IsLeftInvariantIntegral.coefficientMatrix_mul_map_mul_star [Fintype ι] [Fintype κ]
    [DecidableEq κ] {h : A →ₗ[R] R} (hh : h.IsLeftInvariantIntegral) (b : Basis ι R M)
    (c : Basis κ R N) (hv : (coefficientMatrix (C := A) c)ᴴ * coefficientMatrix (C := A) c = 1)
    (p : ι) (q : κ) :
    coefficientMatrix (C := A) b *
        (Matrix.of fun m r ↦
          h (coefficientMatrix (C := A) b m p *
            star (coefficientMatrix (C := A) c r q))).map (algebraMap R A) =
      (Matrix.of fun m r ↦
        h (coefficientMatrix (C := A) b m p *
          star (coefficientMatrix (C := A) c r q))).map (algebraMap R A) *
        coefficientMatrix (C := A) c := by
  set u := coefficientMatrix (C := A) b
  set v := coefficientMatrix (C := A) c
  set E : Matrix ι κ R := Matrix.of fun m r ↦ h (u m p * star (v r q))
  let ru (i j : ι) : Coalgebra.Repr R (u i j) ι :=
    ⟨Finset.univ, fun m ↦ u i m, fun m ↦ u m j, (comul_coefficientMatrix_eq_sum b i j).symm⟩
  let rv (k l : κ) : Coalgebra.Repr R (v k l) κ :=
    ⟨Finset.univ, fun r ↦ v k r, fun r ↦ v r l, (comul_coefficientMatrix_eq_sum c k l).symm⟩
  have hconj : u * E.map (algebraMap R A) * vᴴ = E.map (algebraMap R A) := by
    ext i k
    have hsum := hh.sum_sum_mul (ru i p) (rv k q).star
    calc (u * E.map (algebraMap R A) * vᴴ) i k
        = ∑ m, ∑ r, h (u m p * star (v r q)) • (u i m * star (v k r)) := by
          simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, Finset.sum_mul,
            E, Matrix.of_apply, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc,
            mul_one]
          exact Finset.sum_comm
      _ = h (u i p * star (v k q)) • (1 : A) := by
          simpa [ru, rv] using hsum
      _ = (E.map (algebraMap R A)) i k := by
          simp [Matrix.map_apply, E, Algebra.algebraMap_eq_smul_one]
  calc u * E.map (algebraMap R A)
      = u * E.map (algebraMap R A) * (vᴴ * v) := by rw [hv, Matrix.mul_one]
    _ = (u * E.map (algebraMap R A) * vᴴ) * v := by simp only [Matrix.mul_assoc]
    _ = E.map (algebraMap R A) * v := by rw [hconj]

/-- For a right invariant integral `h` and a basis `b` whose coefficient matrix `u` satisfies
`u * uᴴ = 1`, the matrix `B m n := h (star (u i m) * v k n)` intertwines `v` and `u`. -/
theorem IsRightInvariantIntegral.coefficientMatrix_mul_map_star_mul [Fintype ι] [Fintype κ]
    [DecidableEq ι] {h : A →ₗ[R] R} (hh : h.IsRightInvariantIntegral) (b : Basis ι R M)
    (c : Basis κ R N) (hu : coefficientMatrix (C := A) b * (coefficientMatrix (C := A) b)ᴴ = 1)
    (i : ι) (k : κ) :
    coefficientMatrix (C := A) b *
        (Matrix.of fun m n ↦
          h (star (coefficientMatrix (C := A) b i m) *
            coefficientMatrix (C := A) c k n)).map (algebraMap R A) =
      (Matrix.of fun m n ↦
        h (star (coefficientMatrix (C := A) b i m) *
          coefficientMatrix (C := A) c k n)).map (algebraMap R A) *
        coefficientMatrix (C := A) c := by
  set u := coefficientMatrix (C := A) b
  set v := coefficientMatrix (C := A) c
  set B : Matrix ι κ R := Matrix.of fun m n ↦ h (star (u i m) * v k n)
  let ru (p q : ι) : Coalgebra.Repr R (u p q) ι :=
    ⟨Finset.univ, fun m ↦ u p m, fun m ↦ u m q, (comul_coefficientMatrix_eq_sum b p q).symm⟩
  let rv (r s : κ) : Coalgebra.Repr R (v r s) κ :=
    ⟨Finset.univ, fun n ↦ v r n, fun n ↦ v n s, (comul_coefficientMatrix_eq_sum c r s).symm⟩
  have hconj : uᴴ * B.map (algebraMap R A) * v = B.map (algebraMap R A) := by
    ext r s
    have hsum := hh.sum_sum_mul (ru i r).star (rv k s)
    calc (uᴴ * B.map (algebraMap R A) * v) r s
        = ∑ m, ∑ n, h (star (u i m) * v k n) • (star (u m r) * v n s) := by
          simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, Finset.sum_mul,
            B, Matrix.of_apply, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc,
            mul_one]
          exact Finset.sum_comm
      _ = h (star (u i r) * v k s) • (1 : A) := by
          simpa [ru, rv] using hsum
      _ = (B.map (algebraMap R A)) r s := by
          simp [Matrix.map_apply, B, Algebra.algebraMap_eq_smul_one]
  calc u * B.map (algebraMap R A)
      = u * (uᴴ * B.map (algebraMap R A) * v) := by rw [hconj]
    _ = (u * uᴴ) * B.map (algebraMap R A) * v := by simp only [Matrix.mul_assoc]
    _ = B.map (algebraMap R A) * v := by rw [hu, Matrix.one_mul]

/-- **Cross-orthogonality for left invariant integrals.** If `vᴴ * v = 1` and there is no nonzero
comodule morphism `N → M`, then `h (u i p * star (v k q)) = 0` for all basis indices. -/
theorem IsLeftInvariantIntegral.map_coefficientMatrix_mul_star_eq_zero [Finite ι] [Fintype κ]
    [DecidableEq κ] {h : A →ₗ[R] R} (hh : h.IsLeftInvariantIntegral) (b : Basis ι R M)
    (c : Basis κ R N) (hv : (coefficientMatrix (C := A) c)ᴴ * coefficientMatrix (C := A) c = 1)
    (hHom : ∀ g : Comodule.Hom R A N M, g = 0) (i p : ι) (k q : κ) :
    h (coefficientMatrix (C := A) b i p * star (coefficientMatrix (C := A) c k q)) = 0 := by
  classical
  cases nonempty_fintype ι
  let E : Matrix ι κ R := Matrix.of fun m r ↦
    h (coefficientMatrix (C := A) b m p * star (coefficientMatrix (C := A) c r q))
  let g : Comodule.Hom R A N M :=
    { toLinearMap := Matrix.toLin c b E
      map_coact := (c.map_coact_iff_coefficientMatrix b (Matrix.toLin c b E)).mpr (by
        simpa [LinearMap.toMatrix_toLin, E] using
          hh.coefficientMatrix_mul_map_mul_star b c hv p q) }
  have hE : E = 0 := by
    calc E = LinearMap.toMatrix c b g.toLinearMap := (LinearMap.toMatrix_toLin c b E).symm
      _ = LinearMap.toMatrix c b 0 := by rw [hHom g, Comodule.Hom.zero_toLinearMap]
      _ = 0 := map_zero _
  simpa [E] using congrFun (congrFun hE i) k

/-- **Cross-orthogonality for right invariant integrals.** If `u * uᴴ = 1` and there is no nonzero
comodule morphism `N → M`, then `h (star (u i r) * v k s) = 0` for all basis indices. -/
theorem IsRightInvariantIntegral.map_star_coefficientMatrix_mul_eq_zero [Fintype ι] [Finite κ]
    [DecidableEq ι] {h : A →ₗ[R] R} (hh : h.IsRightInvariantIntegral) (b : Basis ι R M)
    (c : Basis κ R N) (hu : coefficientMatrix (C := A) b * (coefficientMatrix (C := A) b)ᴴ = 1)
    (hHom : ∀ g : Comodule.Hom R A N M, g = 0) (i r : ι) (k s : κ) :
    h (star (coefficientMatrix (C := A) b i r) * coefficientMatrix (C := A) c k s) = 0 := by
  classical
  cases nonempty_fintype κ
  let B : Matrix ι κ R := Matrix.of fun m n ↦
    h (star (coefficientMatrix (C := A) b i m) * coefficientMatrix (C := A) c k n)
  let g : Comodule.Hom R A N M :=
    { toLinearMap := Matrix.toLin c b B
      map_coact := (c.map_coact_iff_coefficientMatrix b (Matrix.toLin c b B)).mpr (by
        simpa [LinearMap.toMatrix_toLin, B] using
          hh.coefficientMatrix_mul_map_star_mul b c hu i k) }
  have hB : B = 0 := by
    calc B = LinearMap.toMatrix c b g.toLinearMap := (LinearMap.toMatrix_toLin c b B).symm
      _ = LinearMap.toMatrix c b 0 := by rw [hHom g, Comodule.Hom.zero_toLinearMap]
      _ = 0 := map_zero _
  simpa [B] using congrFun (congrFun hB r) s

/-- Subspace form of left-invariant cross-orthogonality: if `vᴴ * v = 1` and every comodule
morphism `N → M` is zero, then `h (x * star y) = 0` for all `x` in the coefficient submodule of
`M` and `y` in the coefficient submodule of `N`. -/
theorem IsLeftInvariantIntegral.map_mul_star_eq_zero_of_mem_matrixCoefficientSubmodule
    [Finite ι] [Fintype κ] [DecidableEq κ] {h : A →ₗ[R] R} (hh : h.IsLeftInvariantIntegral)
    (b : Basis ι R M) (c : Basis κ R N)
    (hv : (coefficientMatrix (C := A) c)ᴴ * coefficientMatrix (C := A) c = 1)
    (hHom : ∀ g : Comodule.Hom R A N M, g = 0)
    {x y : A} (hx : x ∈ matrixCoefficientSubmodule (R := R) (C := A) (M := M))
    (hy : y ∈ matrixCoefficientSubmodule (R := R) (C := A) (M := N)) :
    h (x * star y) = 0 := by
  cases nonempty_fintype ι
  obtain ⟨X, rfl⟩ := (mem_matrixCoefficientSubmodule_iff_exists_matrix b).mp hx
  obtain ⟨Y, rfl⟩ := (mem_matrixCoefficientSubmodule_iff_exists_matrix c).mp hy
  simp only [star_sum, star_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    map_sum, map_smul, hh.map_coefficientMatrix_mul_star_eq_zero b c hv hHom, smul_zero,
    Finset.sum_const_zero]

/-- Subspace form of right-invariant cross-orthogonality: if `u * uᴴ = 1` and every comodule
morphism `N → M` is zero, then `h (star x * y) = 0` for all `x` in the coefficient submodule of
`M` and `y` in the coefficient submodule of `N`. -/
theorem IsRightInvariantIntegral.map_star_mul_eq_zero_of_mem_matrixCoefficientSubmodule
    [Fintype ι] [Finite κ] [DecidableEq ι] {h : A →ₗ[R] R} (hh : h.IsRightInvariantIntegral)
    (b : Basis ι R M) (c : Basis κ R N)
    (hu : coefficientMatrix (C := A) b * (coefficientMatrix (C := A) b)ᴴ = 1)
    (hHom : ∀ g : Comodule.Hom R A N M, g = 0)
    {x y : A} (hx : x ∈ matrixCoefficientSubmodule (R := R) (C := A) (M := M))
    (hy : y ∈ matrixCoefficientSubmodule (R := R) (C := A) (M := N)) :
    h (star x * y) = 0 := by
  cases nonempty_fintype κ
  obtain ⟨X, rfl⟩ := (mem_matrixCoefficientSubmodule_iff_exists_matrix b).mp hx
  obtain ⟨Y, rfl⟩ := (mem_matrixCoefficientSubmodule_iff_exists_matrix c).mp hy
  simp only [star_sum, star_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    map_sum, map_smul, hh.map_star_coefficientMatrix_mul_eq_zero b c hu hHom, smul_zero,
    Finset.sum_const_zero]

end LinearMap

end IntertwinersAndCrossOrthogonality

section DoubleAntipode

variable {R A M ι : Type*} [CommSemiring R]
  [Semiring A] [StarRing A] [HopfAlgebra R A]
  [AddCommMonoid M] [Module R M] [Comodule R A M] [Fintype ι] [DecidableEq ι]

/-- If the coefficient matrix `u` of `b` is unitary and `G` is invariant under `u.map star`, then
`Gᵀ` intertwines `u` with its double antipode `(u.map S).map S`. -/
theorem TauCeti.Comodule.map_antipode_map_antipode_mul_transpose_of_conjInvariant
    (b : Basis ι R M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {G : Matrix ι ι R}
    (hG : ((coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap R A) *
      (coefficientMatrix (C := A) b).map star = G.map (algebraMap R A)) :
    (((coefficientMatrix (C := A) b).map (HopfAlgebra.antipode R)).map (HopfAlgebra.antipode R)) *
        Gᵀ.map (algebraMap R A) =
      Gᵀ.map (algebraMap R A) * coefficientMatrix (C := A) b := by
  set u := coefficientMatrix (C := A) b
  have huS : u.map (HopfAlgebra.antipode R) = uᴴ :=
    left_inv_eq_right_inv (map_antipode_mul_coefficientMatrix b) (Unitary.mem_iff.mp hu).2
  have hmulS (X Y : Matrix ι ι A) :
      ((X * Y).map (HopfAlgebra.antipode R))ᵀ =
        (Y.map (HopfAlgebra.antipode R))ᵀ * (X.map (HopfAlgebra.antipode R))ᵀ := by
    ext i j
    simp [Matrix.mul_apply, _root_.HopfAlgebra.antipode_mul_antidistrib]
  have h1 : (((u.map star)ᴴ * G.map (algebraMap R A) * u.map star).map
      (HopfAlgebra.antipode R))ᵀ = ((G.map (algebraMap R A)).map (HopfAlgebra.antipode R))ᵀ :=
    congrArg (fun M : Matrix ι ι A ↦ (M.map (HopfAlgebra.antipode R))ᵀ) hG
  rw [hmulS, hmulS] at h1
  have hf1 : ((u.map star).map (HopfAlgebra.antipode R))ᵀ =
      (u.map (HopfAlgebra.antipode R)).map (HopfAlgebra.antipode R) := by
    ext i j
    have hij := congrFun (congrFun huS i) j
    simp only [Matrix.map_apply, conjTranspose_apply] at hij
    simp [Matrix.transpose_apply, Matrix.map_apply, ← hij]
  have hf2 :
      ((G.map (algebraMap R A)).map (HopfAlgebra.antipode R))ᵀ = Gᵀ.map (algebraMap R A) := by
    ext i j
    simp [Algebra.algebraMap_eq_smul_one]
  have hf3 : (((u.map star)ᴴ).map (HopfAlgebra.antipode R))ᵀ = uᴴ := by
    ext i j
    have hij := congrFun (congrFun huS i) j
    simp only [Matrix.map_apply, conjTranspose_apply] at hij
    simp [Matrix.transpose_apply, Matrix.map_apply, conjTranspose_apply, hij]
  rw [hf1, hf2, hf3, ← Matrix.mul_assoc] at h1
  calc (u.map (HopfAlgebra.antipode R)).map (HopfAlgebra.antipode R) * Gᵀ.map (algebraMap R A)
      = (u.map (HopfAlgebra.antipode R)).map (HopfAlgebra.antipode R) *
          Gᵀ.map (algebraMap R A) * (uᴴ * u) := by
          rw [← star_eq_conjTranspose, (Unitary.mem_iff.mp hu).1, Matrix.mul_one]
    _ = ((u.map (HopfAlgebra.antipode R)).map (HopfAlgebra.antipode R) *
          Gᵀ.map (algebraMap R A) * uᴴ) * u := by simp only [Matrix.mul_assoc]
    _ = Gᵀ.map (algebraMap R A) * u := by rw [h1]

end DoubleAntipode

namespace Module.Basis

private theorem index_nonempty_of_isSimpleOrder (A : Type*) [Ring A] [Module ℂ A] [Coalgebra ℂ A]
    {M ι : Type*} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
    [IsSimpleOrder (Subcomodule ℂ A M)] (b : Basis ι ℂ M) : Nonempty ι := by
  let _ := Comodule.convolutionModule (R := ℂ) (C := A) (M := M)
  have := isSimpleModule_convolution_iff.mpr ‹IsSimpleOrder (Subcomodule ℂ A M)›
  have := IsSimpleModule.nontrivial (WithConv (A →ₗ[ℂ] ℂ)) M
  exact b.index_nonempty

section WeightedSchurOrthogonality

variable {A M ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]
  [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M] [IsSimpleOrder (Subcomodule ℂ A M)]
  [Fintype ι] [DecidableEq ι]

omit [IsSimpleOrder (Subcomodule ℂ A M)] in
private theorem map_star_mul_inv_mul_conjTranspose_of_conjInvariant (b : Basis ι ℂ M)
    {G : Matrix ι ι ℂ} (hG : G.PosDef)
    (hGinv : ((coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = G.map (algebraMap ℂ A)) :
    (coefficientMatrix (C := A) b).map star * G⁻¹.map (algebraMap ℂ A) *
      ((coefficientMatrix (C := A) b).map star)ᴴ = G⁻¹.map (algebraMap ℂ A) := by
  set u := coefficientMatrix (C := A) b
  obtain ⟨P, hP⟩ := posSemidef_iff_eq_conjTranspose_mul_self.mp hG.posSemidef
  have hGdet : IsUnit G.det := (isUnit_iff_isUnit_det _).mp hG.isUnit
  have hPdet : IsUnit P.det := isUnit_of_mul_isUnit_right (by rwa [hP, det_mul] at hGdet)
  set f := algebraMap ℂ A
  set Pf := P.map f
  set Qf := P⁻¹.map f
  have hstar : Function.Semiconj f star star := fun z ↦ algebraMap_star_comm z
  have hPQ : Pf * Qf = 1 := by
    rw [← Matrix.map_mul, mul_nonsing_inv _ hPdet, Matrix.map_one _ (map_zero f) (map_one f)]
  have hQP : Qf * Pf = 1 := by
    rw [← Matrix.map_mul, nonsing_inv_mul _ hPdet, Matrix.map_one _ (map_zero f) (map_one f)]
  have hGf : G.map f = Pfᴴ * Pf := by
    rw [hP, Matrix.map_mul, conjTranspose_map _ hstar]
  have hGinv_eq : G⁻¹ = P⁻¹ * (P⁻¹)ᴴ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hP]
    calc P⁻¹ * (P⁻¹)ᴴ * (Pᴴ * P)
        = P⁻¹ * ((P * P⁻¹)ᴴ * P) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by
            rw [mul_nonsing_inv _ hPdet, conjTranspose_one, Matrix.one_mul,
              nonsing_inv_mul _ hPdet]
  have hGinvf : G⁻¹.map f = Qf * Qfᴴ := by
    rw [hGinv_eq, Matrix.map_mul, conjTranspose_map _ hstar]
  set w := Pf * u.map star * Qf
  have hww1 : wᴴ * w = 1 := by
    calc wᴴ * w = Qfᴴ * ((u.map star)ᴴ * (Pfᴴ * Pf) * u.map star) * Qf := by
            simp only [w, conjTranspose_mul, Matrix.mul_assoc]
      _ = (Pf * Qf)ᴴ * (Pf * Qf) := by
            rw [← hGf, hGinv, hGf]
            simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hPQ, conjTranspose_one, Matrix.one_mul]
  let _ : Comodule ℂ A (ι → ℂ) := conjugateMatrixComodule b
  have hubar_inv : u.map star * (u.map star).map (HopfAlgebra.antipode ℂ) = 1 := by
    rw [← coefficientMatrix_conjugateMatrixComodule b]
    exact coefficientMatrix_mul_map_antipode (Pi.basisFun ℂ ι)
  have hw_right : w * (Pf * (u.map star).map (HopfAlgebra.antipode ℂ) * Qf) = 1 := by
    calc Pf * u.map star * Qf * (Pf * (u.map star).map (HopfAlgebra.antipode ℂ) * Qf)
        = Pf * u.map star * (Qf * Pf) * (u.map star).map (HopfAlgebra.antipode ℂ) * Qf := by
            simp only [Matrix.mul_assoc]
      _ = Pf * (u.map star * (u.map star).map (HopfAlgebra.antipode ℂ)) * Qf := by
            rw [hQP, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hubar_inv, Matrix.mul_one, hPQ]
  have hww2 : w * wᴴ = 1 := by
    rw [left_inv_eq_right_inv hww1 hw_right]
    exact hw_right
  calc u.map star * G⁻¹.map f * (u.map star)ᴴ
      = (Qf * Pf) * u.map star * (Qf * Qfᴴ) * (u.map star)ᴴ * (Qf * Pf)ᴴ := by
          rw [hQP, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hGinvf]
    _ = Qf * (w * wᴴ) * Qfᴴ := by simp only [w, conjTranspose_mul, Matrix.mul_assoc]
    _ = G⁻¹.map f := by rw [hww2, Matrix.mul_one, hGinvf]

private theorem exists_pos_smul_trace_eq_inv_trace [Nonempty ι] {G : Matrix ι ι ℂ}
    (hG : G.PosDef) :
    ∃ c : ℂ, 0 < c ∧ (c • G).PosDef ∧ (c • G)⁻¹ = c⁻¹ • G⁻¹ ∧ (c • G).trace = (c • G)⁻¹.trace := by
  have hGtr_re : 0 < G.trace.re ∧ 0 = G.trace.im := Complex.lt_def.mp hG.trace_pos
  have hGinvtr_re : 0 < G⁻¹.trace.re ∧ 0 = G⁻¹.trace.im := Complex.lt_def.mp hG.inv.trace_pos
  have hGtr_eq : (G.trace.re : ℂ) = G.trace := Complex.ext rfl hGtr_re.2
  have hGinvtr_eq : (G⁻¹.trace.re : ℂ) = G⁻¹.trace := Complex.ext rfl hGinvtr_re.2
  set r : ℝ := Real.sqrt (G⁻¹.trace.re / G.trace.re)
  have hr_pos : 0 < r := Real.sqrt_pos_of_pos (div_pos hGinvtr_re.1 hGtr_re.1)
  have hr_sq : r * r = G⁻¹.trace.re / G.trace.re :=
    Real.mul_self_sqrt (div_nonneg hGinvtr_re.1.le hGtr_re.1.le)
  set c : ℂ := (r : ℂ)
  have hc_pos : 0 < c := Complex.zero_lt_real.mpr hr_pos
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hFt_inv : (c • G)⁻¹ = c⁻¹ • G⁻¹ := by
    have hGdet : IsUnit G.det := (isUnit_iff_isUnit_det _).mp hG.isUnit
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc_ne, one_smul,
      nonsing_inv_mul _ hGdet]
  refine ⟨c, hc_pos, hG.smul hc_pos, hFt_inv, ?_⟩
  rw [hFt_inv, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  have h1' : (r : ℂ) * (r : ℂ) * G.trace = G⁻¹.trace := by
    rw [← hGtr_eq, ← hGinvtr_eq]
    exact_mod_cast (calc r * r * G.trace.re
        = (G⁻¹.trace.re / G.trace.re) * G.trace.re := by rw [hr_sq]
      _ = G⁻¹.trace.re := div_mul_cancel₀ _ hGtr_re.1.ne')
  calc c * G.trace = c⁻¹ * (c * c * G.trace) := by
          rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hc_ne, one_mul]
    _ = c⁻¹ * G⁻¹.trace := by rw [h1']

omit [StarModule ℂ A] [StarCoalgebra ℂ A] in
private theorem eq_of_posDef_schur_orthogonality {h : A →ₗ[ℂ] ℂ} (b : Basis ι ℂ M)
    {Ft Ft' : Matrix ι ι ℂ} (hFt_pos : Ft.PosDef) (hFt_tr : Ft.trace = Ft⁻¹.trace)
    (hFt_orth1 : ∀ i j k l,
      h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
        if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0)
    (hFt_orth2 : ∀ i j k l,
      h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
        if i = k then Ft j l / Ft.trace else 0)
    (hFt'_pos : Ft'.PosDef) (hFt'_tr : Ft'.trace = Ft'⁻¹.trace)
    (hFt'_orth1 : ∀ i j k l,
      h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
        if j = l then Ft'⁻¹ i k / Ft'⁻¹.trace else 0)
    (hFt'_orth2 : ∀ i j k l,
      h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
        if i = k then Ft' j l / Ft'.trace else 0) :
    Ft' = Ft := by
  have : Nonempty ι := index_nonempty_of_isSimpleOrder A b
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hFt'_tr_pos : 0 < Ft'.trace := hFt'_pos.trace_pos
  have hFt'_tr_ne : Ft'.trace ≠ 0 := hFt'_tr_pos.ne'
  have hFt_tr_pos : 0 < Ft.trace := hFt_pos.trace_pos
  set α : ℂ := Ft'.trace / Ft.trace
  have hFt'_eq : Ft' = α • Ft := by
    ext j l
    have hjl := (hFt'_orth2 i₀ j i₀ l).symm.trans (hFt_orth2 i₀ j i₀ l)
    simp only [↓reduceIte] at hjl
    rw [div_eq_iff hFt'_tr_ne] at hjl
    rw [Matrix.smul_apply, smul_eq_mul, hjl]
    dsimp [α]
    ring
  have hFt'_inv_eq : Ft'⁻¹ = α • Ft⁻¹ := by
    ext i k
    have hik := (hFt'_orth1 i i₀ k i₀).symm.trans (hFt_orth1 i i₀ k i₀)
    simp only [↓reduceIte] at hik
    rw [div_eq_iff (hFt'_tr ▸ hFt'_tr_ne)] at hik
    rw [Matrix.smul_apply, smul_eq_mul, hik, ← hFt'_tr, ← hFt_tr]
    dsimp [α]
    ring
  have hα_sq : α * α = 1 := by
    have hFt'_det : IsUnit Ft'.det := (isUnit_iff_isUnit_det _).mp hFt'_pos.isUnit
    have hFt_det : IsUnit Ft.det := (isUnit_iff_isUnit_det _).mp hFt_pos.isUnit
    have hmul : Ft' * Ft'⁻¹ = 1 := mul_nonsing_inv _ hFt'_det
    rw [hFt'_inv_eq, hFt'_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_nonsing_inv _ hFt_det] at hmul
    simpa using congrFun (congrFun hmul i₀) i₀
  have hα_pos : 0 < α := by
    have h1re : 0 < Ft'.trace.re ∧ 0 = Ft'.trace.im := Complex.lt_def.mp hFt'_tr_pos
    have h2re : 0 < Ft.trace.re ∧ 0 = Ft.trace.im := Complex.lt_def.mp hFt_tr_pos
    have h1eq : Ft'.trace = (Ft'.trace.re : ℂ) :=
      Complex.ext (Complex.ofReal_re _).symm h1re.2.symm
    have h2eq : Ft.trace = (Ft.trace.re : ℂ) :=
      Complex.ext (Complex.ofReal_re _).symm h2re.2.symm
    have hαeq : α = ((Ft'.trace.re / Ft.trace.re : ℝ) : ℂ) :=
      calc α = (Ft'.trace.re : ℂ) / (Ft.trace.re : ℂ) := congrArg₂ (· / ·) h1eq h2eq
        _ = ((Ft'.trace.re / Ft.trace.re : ℝ) : ℂ) := (Complex.ofReal_div _ _).symm
    rw [hαeq, Complex.zero_lt_real]
    exact div_pos h1re.1 h2re.1
  have hα_one : α = 1 := by
    rcases mul_self_eq_one_iff.mp hα_sq with h1 | hm1
    · exact h1
    · exfalso
      rw [hm1] at hα_pos
      have : (0 : ℝ) < (-1 : ℂ).re := (Complex.lt_def.mp hα_pos).1
      norm_num at this
  rw [hFt'_eq, hα_one, one_smul]

/-- **Weighted Schur orthogonality from a conjugate-invariant positive definite matrix.** Let `h`
be a normalized two-sided invariant integral on a complex Hopf star algebra `A` (with no global
positivity hypothesis on `h`), `b` a finite basis of a simple comodule `M` with unitary coefficient
matrix `u`, and `G` a positive definite matrix satisfying `(u.map star)ᴴ * G * u.map star = G`.
Then there exists a unique positive definite matrix `Ft` with `Ft.trace = Ft⁻¹.trace` satisfying
both weighted Schur orthogonality relations. -/
theorem existsUnique_posDef_schur_orthogonality_of_conjInvariant
    {h : A →ₗ[ℂ] ℂ} (hl : h.IsLeftInvariantIntegral) (hr : h.IsRightInvariantIntegral)
    (h1 : h 1 = 1) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {G : Matrix ι ι ℂ} (hG : G.PosDef)
    (hGinv : ((coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = G.map (algebraMap ℂ A)) :
    ∃! Ft : Matrix ι ι ℂ,
      Ft.PosDef ∧
      Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) := by
  set u := coefficientMatrix (C := A) b
  have hu1 : uᴴ * u = 1 := by rw [← star_eq_conjTranspose]; exact (Unitary.mem_iff.mp hu).1
  have hu2 : u * uᴴ = 1 := by rw [← star_eq_conjTranspose]; exact (Unitary.mem_iff.mp hu).2
  have : Nonempty ι := index_nonempty_of_isSimpleOrder A b
  have hC (j l : ι) : ∃ c : ℂ, ∀ i k, h (u i j * star (u k l)) = if i = k then c else 0 := by
    obtain ⟨c, hc⟩ := b.exists_eq_smul_one_of_commute_coefficientMatrix
      (Matrix.of fun i k ↦ h (u i j * star (u k l)))
      (hl.coefficientMatrix_mul_map_mul_star b b hu1 j l)
    exact ⟨c, fun i k ↦ by simpa [Matrix.one_apply] using congrFun (congrFun hc i) k⟩
  choose C hC using hC
  have hD (i k : ι) : ∃ d : ℂ, ∀ j l, h (star (u i j) * u k l) = if j = l then d else 0 := by
    obtain ⟨d, hd⟩ := b.exists_eq_smul_one_of_commute_coefficientMatrix
      (Matrix.of fun j l ↦ h (star (u i j) * u k l))
      (hr.coefficientMatrix_mul_map_star_mul b b hu2 i k)
    exact ⟨d, fun j l ↦ by simpa [Matrix.one_apply] using congrFun (congrFun hd j) l⟩
  choose D hD using hD
  have hCG (j l : ι) : G.trace * C j l = G j l := by
    have hjl := congrArg h (congrFun (congrFun hGinv j) l)
    simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, star_star,
      Finset.sum_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
      map_sum, map_smul, smul_eq_mul, hC, h1] at hjl
    simpa [Matrix.trace, Matrix.diag, Finset.sum_mul] using hjl
  have hGinv_dual : u.map star * G⁻¹.map (algebraMap ℂ A) * (u.map star)ᴴ =
      G⁻¹.map (algebraMap ℂ A) :=
    b.map_star_mul_inv_mul_conjTranspose_of_conjInvariant hG hGinv
  have hDG (i k : ι) : G⁻¹.trace * D i k = G⁻¹ i k := by
    have hik := congrArg h (congrFun (congrFun hGinv_dual i) k)
    simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, star_star,
      Finset.sum_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
      map_sum, map_smul, smul_eq_mul, hD, h1] at hik
    simpa [Matrix.trace, Matrix.diag, Finset.sum_mul] using hik
  obtain ⟨c, hc_pos, hFt_pos, hFt_inv, hFt_tr⟩ := exists_pos_smul_trace_eq_inv_trace hG
  have hc_ne : c ≠ 0 := hc_pos.ne'
  set Ft : Matrix ι ι ℂ := c • G
  have hFt_orth1 (i j k l : ι) :
      h (star (u i j) * u k l) = if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0 := by
    rw [hD i k j l]
    split_ifs with hjl
    · have hDval : D i k = G⁻¹ i k / G⁻¹.trace :=
        eq_div_of_mul_eq hG.inv.trace_pos.ne' (by rw [mul_comm, hDG i k])
      have hentry : Ft⁻¹ i k = c⁻¹ * G⁻¹ i k := by simp [hFt_inv]
      have htr : Ft⁻¹.trace = c⁻¹ * G⁻¹.trace := by simp [hFt_inv]
      rw [hDval, hentry, htr, mul_div_mul_left _ _ (inv_ne_zero hc_ne)]
    · rfl
  have hFt_orth2 (i j k l : ι) :
      h (u i j * star (u k l)) = if i = k then Ft j l / Ft.trace else 0 := by
    rw [hC j l i k]
    split_ifs with hik
    · have hCval : C j l = G j l / G.trace :=
        eq_div_of_mul_eq hG.trace_pos.ne' (by rw [mul_comm, hCG j l])
      have hentry : Ft j l = c * G j l := rfl
      have htr : Ft.trace = c * G.trace := by simp [Ft]
      rw [hCval, hentry, htr, mul_div_mul_left _ _ hc_ne]
    · rfl
  refine ⟨Ft, ⟨hFt_pos, hFt_tr, hFt_orth1, hFt_orth2⟩, ?_⟩
  rintro Ft' ⟨hFt'_pos, hFt'_tr, hFt'_orth1, hFt'_orth2⟩
  exact eq_of_posDef_schur_orthogonality b hFt_pos hFt_tr hFt_orth1 hFt_orth2
    hFt'_pos hFt'_tr hFt'_orth1 hFt'_orth2

/-- Under the hypotheses of `existsUnique_posDef_schur_orthogonality_of_conjInvariant`, the
functional `h` is nonnegative on `star x * x` for every `x` in the matrix-coefficient submodule of
`M`. -/
theorem map_star_mul_self_nonneg_of_conjInvariant
    {h : A →ₗ[ℂ] ℂ} (hl : h.IsLeftInvariantIntegral) (hr : h.IsRightInvariantIntegral)
    (h1 : h 1 = 1) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {G : Matrix ι ι ℂ} (hG : G.PosDef)
    (hGinv : ((coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = G.map (algebraMap ℂ A))
    {x : A} (hx : x ∈ matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M)) :
    0 ≤ h (star x * x) := by
  obtain ⟨Ft, ⟨hFt_pos, -, hFt_orth1, -⟩, -⟩ :=
    b.existsUnique_posDef_schur_orthogonality_of_conjInvariant hl hr h1 hu hG hGinv
  have : Nonempty ι := index_nonempty_of_isSimpleOrder A b
  have hFtinv_pos : Ft⁻¹.PosDef := hFt_pos.inv
  have htr_pos : 0 < Ft⁻¹.trace := hFtinv_pos.trace_pos
  have htr_inv_nonneg : 0 ≤ (Ft⁻¹.trace)⁻¹ := by
    have hre : 0 < Ft⁻¹.trace.re ∧ 0 = Ft⁻¹.trace.im := Complex.lt_def.mp htr_pos
    have heq : ((Ft⁻¹.trace.re : ℝ) : ℂ) = Ft⁻¹.trace := Complex.ext rfl hre.2
    rw [← heq, ← Complex.ofReal_inv, Complex.zero_le_real]
    exact inv_nonneg.mpr hre.1.le
  obtain ⟨X, rfl⟩ := (mem_matrixCoefficientSubmodule_iff_exists_matrix b).mp hx
  have hexp : h (star (∑ i, ∑ j, X i j • coefficientMatrix (C := A) b i j) *
      ∑ k, ∑ l, X k l • coefficientMatrix (C := A) b k l) =
      (Ft⁻¹.trace)⁻¹ * ∑ j, star (fun i ↦ X i j) ⬝ᵥ (Ft⁻¹ *ᵥ fun k ↦ X k j) := by
    calc h (star (∑ i, ∑ j, X i j • coefficientMatrix (C := A) b i j) *
          ∑ k, ∑ l, X k l • coefficientMatrix (C := A) b k l)
        = ∑ i, ∑ j, ∑ k, ∑ l,
            star (X i j) * (X k l *
              h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l)) := by
            simp only [star_sum, star_smul]
            simp only [Finset.sum_mul]
            simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_sum, map_smul,
              smul_eq_mul]
            refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
              Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
            ring
      _ = ∑ i, ∑ j, ∑ k, star (X i j) * (X k j * (Ft⁻¹ i k / Ft⁻¹.trace)) := by
            refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
              Finset.sum_congr rfl fun k _ ↦ ?_
            rw [Finset.sum_eq_single j]
            · simp [hFt_orth1]
            · intro l _ hlj
              simp [hFt_orth1, Ne.symm hlj]
            · simp
      _ = ∑ j, ∑ i, ∑ k, star (X i j) * (X k j * (Ft⁻¹ i k / Ft⁻¹.trace)) := Finset.sum_comm
      _ = (Ft⁻¹.trace)⁻¹ * ∑ j, star (fun i ↦ X i j) ⬝ᵥ (Ft⁻¹ *ᵥ fun k ↦ X k j) := by
            simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, div_eq_mul_inv]
            refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦
              Finset.sum_congr rfl fun k _ ↦ ?_
            ring
  rw [hexp]
  exact mul_nonneg htr_inv_nonneg
    (Finset.sum_nonneg fun j _ ↦ hFtinv_pos.posSemidef.dotProduct_mulVec_nonneg _)

/-- **Weighted Schur orthogonality** for a basis `b` of a simple comodule `M` whose coefficient
matrix `u` is unitary: for an `AlgebraicHaar` functional `h` on a complex Hopf star algebra `A`,
there exists a unique positive definite matrix `Ft` with `Ft.trace = Ft⁻¹.trace` satisfying both
weighted Schur orthogonality relations. -/
theorem schur_orthogonality (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃! Ft : Matrix ι ι ℂ,
      Ft.PosDef ∧
      Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) := by
  let _ : Comodule ℂ A (ι → ℂ) := conjugateMatrixComodule b
  let G : Matrix ι ι ℂ := haarGramMatrix h.toLinearMap (Pi.basisFun ℂ ι)
  have hG : G.PosDef :=
    posDef_haarGramMatrix (fun a ha ↦ h.map_star_mul_self_pos ha) (Pi.basisFun ℂ ι)
  have hGinv : ((coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = G.map (algebraMap ℂ A) := by
    simpa [G, coefficientMatrix_conjugateMatrixComodule] using
      conjTranspose_coefficientMatrix_mul_haarGramMatrix_mul h.isRightInvariantIntegral
        (Pi.basisFun ℂ ι)
  exact b.existsUnique_posDef_schur_orthogonality_of_conjInvariant h.isLeftInvariantIntegral
    h.isRightInvariantIntegral h.map_one hu hG hGinv

/-- If `Ft` satisfies the right-handed Schur orthogonality relation for a right invariant integral
`h`, then `Ft` is invariant under `u.map star`, and consequently `Ftᵀ` intertwines `u` with its
double antipode `(u.map S).map S`. -/
theorem conjInvariant_of_schur_orthogonality {h : A →ₗ[ℂ] ℂ}
    (hr : h.IsRightInvariantIntegral) (b : Basis ι ℂ M)
    {Ft : Matrix ι ι ℂ} (hFt_tr : Ft.trace ≠ 0)
    (horth : ∀ i j k l,
      h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
        if i = k then Ft j l / Ft.trace else 0) :
    ((coefficientMatrix (C := A) b).map star)ᴴ * Ft.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = Ft.map (algebraMap ℂ A) := by
  have : Nonempty ι := index_nonempty_of_isSimpleOrder A b
  let _ : Comodule ℂ A (ι → ℂ) := conjugateMatrixComodule b
  let G : Matrix ι ι ℂ := haarGramMatrix h (Pi.basisFun ℂ ι)
  have hGinv : ((coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = G.map (algebraMap ℂ A) := by
    simpa [G, coefficientMatrix_conjugateMatrixComodule] using
      conjTranspose_coefficientMatrix_mul_haarGramMatrix_mul hr (Pi.basisFun ℂ ι)
  have hFtG : Ft = (Ft.trace / (Fintype.card ι : ℂ)) • G := by
    ext j l
    have hGjl : G j l = (Fintype.card ι : ℂ) * (Ft j l / Ft.trace) := by
      simp [G, haarGramMatrix_apply, horth]
    have hcard : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [Matrix.smul_apply, smul_eq_mul, hGjl]
    field_simp
  have hmap : Ft.map (algebraMap ℂ A) =
      (Ft.trace / (Fintype.card ι : ℂ)) • G.map (algebraMap ℂ A) := by
    conv_lhs => rw [hFtG]
    ext p q
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.smul_apply,
      Matrix.map_apply, Algebra.smul_def]
  rw [hmap, Matrix.mul_smul, Matrix.smul_mul, hGinv]

end WeightedSchurOrthogonality

end Module.Basis

namespace TauCeti.Comodule.IsUnitary

variable {A H ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [Comodule ℂ A H] [IsSimpleOrder (Subcomodule ℂ A H)]
  [Fintype ι] [DecidableEq ι]

/-- **Weighted Schur orthogonality** for a finite-dimensional simple unitary comodule `H` in any
orthonormal basis `b`. -/
theorem schur_orthogonality (hH : IsUnitary ℂ A H) (h : AlgebraicHaar A)
    (b : OrthonormalBasis ι ℂ H) :
    ∃! Ft : Matrix ι ι ℂ,
      Ft.PosDef ∧
      Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b.toBasis i j) *
          coefficientMatrix (C := A) b.toBasis k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b.toBasis i j *
          star (coefficientMatrix (C := A) b.toBasis k l)) =
          if i = k then Ft j l / Ft.trace else 0) :=
  b.toBasis.schur_orthogonality h (hH.coefficientMatrix_mem_unitary b)

end TauCeti.Comodule.IsUnitary
