/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FromMatrix
public import TauCeti.Algebra.Coalgebra.Star
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
public import TauCeti.LinearAlgebra.Basis.Semilinear
import Mathlib.Algebra.Star.LinearMap
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Conjugate comodules over star bialgebras

Let `A` be a star bialgebra over a commutative star semiring `R`, and let `M` be a right
`A`-comodule with a finite basis `b` and coefficient matrix `u`. Because comultiplication and the
counit of a star coalgebra commute with `star`, the entrywise conjugate matrix `u.map star` is
again a multiplicative matrix (`Module.Basis.conjugateMatrixComodule`), whose matrix-coefficient
submodule is the `star`-preimage of that of `M`
(`Module.Basis.mem_matrixCoefficientSubmodule_conjugateMatrixComodule_iff`).

Over a commutative star ring `R` over which `A` is projective, coordinatewise conjugation
(`Module.Basis.conjEquivFun`) induces an order isomorphism between the subcomodule lattices of `M`
and `b.conjugateMatrixComodule` (`Module.Basis.conjugateSubcomoduleOrderIso`), and hence preserves
simplicity (`Module.Basis.isSimpleOrder_conjugateMatrixComodule`).

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.1.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Section 1.3.
-/

public section

open Module Matrix WithConv TauCeti TauCeti.Comodule
open scoped TensorProduct

namespace Module.Basis

section ConjugateMatrixComodule

variable {R A M ι : Type*} [CommSemiring R] [StarRing R]
  [Semiring A] [StarRing A] [Bialgebra R A] [StarModule R A] [StarCoalgebra R A]
  [AddCommMonoid M] [Module R M] [Comodule R A M] [Fintype ι]

private theorem map_star_coefficientMatrix_comul (b : Basis ι R M) :
    ((coefficientMatrix (C := A) b).map star).map (Bialgebra.comulAlgHom R A) =
      ((coefficientMatrix (C := A) b).map star).map (Algebra.TensorProduct.includeLeft (S := R)) *
        ((coefficientMatrix (C := A) b).map star).map Algebra.TensorProduct.includeRight :=
  (Comodule.map_comul_iff R _).mpr fun _ _ ↦ by simp [Matrix.map_apply, star_sum]

omit [Fintype ι] in
private theorem map_star_coefficientMatrix_counit [Finite ι] (b : Basis ι R M) (i j : ι) :
    Coalgebra.counit (R := R) (((coefficientMatrix (C := A) b).map star) i j) =
      (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i := by
  classical
  refine counit_basisFun_of_map_counit R _ ((Comodule.map_counit_iff R _).mpr fun _ _ ↦ ?_) i j
  simp [Matrix.map_apply, apply_ite star]

/-- The **conjugate matrix comodule** associated to a finite basis `b` of a right comodule `M` over
a star bialgebra `A`: the right coaction on `ι → R` whose coefficient matrix in `Pi.basisFun R ι`
is `(coefficientMatrix b).map star`. -/
@[instance_reducible]
noncomputable def conjugateMatrixComodule (b : Basis ι R M) : Comodule R A (ι → R) :=
  matrixComodule R ((coefficientMatrix (C := A) b).map star)
    (map_star_coefficientMatrix_comul b) (map_star_coefficientMatrix_counit b)

/-- The coaction of `b.conjugateMatrixComodule` is `matrixCoact` of
`(coefficientMatrix b).map star`. -/
theorem conjugateMatrixComodule_coact (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    coact (R := R) (C := A) (M := ι → R) =
      matrixCoact R ((coefficientMatrix (C := A) b).map star) :=
  matrixComodule_coact R ((coefficientMatrix (C := A) b).map star)
    (map_star_coefficientMatrix_comul b) (map_star_coefficientMatrix_counit b)

/-- The coefficient matrix of `b.conjugateMatrixComodule` in `Pi.basisFun R ι` is the entrywise star
of `coefficientMatrix b`. -/
theorem coefficientMatrix_conjugateMatrixComodule (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    coefficientMatrix (C := A) (Pi.basisFun R ι) = (coefficientMatrix (C := A) b).map star :=
  coefficientMatrix_matrixComodule R ((coefficientMatrix (C := A) b).map star)
    (map_star_coefficientMatrix_comul b) (map_star_coefficientMatrix_counit b)

/-- Membership in the matrix-coefficient submodule of `b.conjugateMatrixComodule` is equivalent to
`star`-membership in the matrix-coefficient submodule of `M`. -/
theorem mem_matrixCoefficientSubmodule_conjugateMatrixComodule_iff (b : Basis ι R M) {a : A} :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    a ∈ matrixCoefficientSubmodule (R := R) (C := A) (M := ι → R) ↔
      star a ∈ matrixCoefficientSubmodule (R := R) (C := A) (M := M) := by
  let _ : Comodule R A (ι → R) := b.conjugateMatrixComodule
  rw [(Pi.basisFun R ι).mem_matrixCoefficientSubmodule_iff_exists_matrix,
    b.mem_matrixCoefficientSubmodule_iff_exists_matrix, b.coefficientMatrix_conjugateMatrixComodule]
  refine ⟨fun ⟨X, hX⟩ ↦ ⟨X.map star, by simp [hX, star_sum, star_smul]⟩,
    fun ⟨X, hX⟩ ↦ ⟨X.map star, by simpa [star_sum, star_smul] using congrArg star hX⟩⟩

end ConjugateMatrixComodule

section ConjugateSubcomodule

variable {R A M ι : Type*} [CommRing R] [StarRing R]
  [Ring A] [StarRing A] [Bialgebra R A] [Module.Projective R A] [StarModule R A] [StarCoalgebra R A]
  [AddCommGroup M] [Module R M] [Comodule R A M] [Fintype ι]

omit [Module.Projective R A] in
private theorem coactComponent_conjEquivFun (b : Basis ι R M) (f : WithConv (A →ₗ[R] R)) (m : M) :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    coactComponent (R := R) (C := A) (M := ι → R) f.ofConv (b.conjEquivFun m) =
      b.conjEquivFun (coactComponent (R := R) (C := A) (M := M) (star f).ofConv m) := by
  let _ : Comodule R A (ι → R) := b.conjugateMatrixComodule
  conv_lhs => rw [← b.sum_repr m]
  conv_rhs => rw [← b.sum_repr m]
  simp only [map_sum, map_smulₛₗ, b.conjEquivFun_self]
  refine Finset.sum_congr rfl fun j _ ↦ congrArg _ ?_
  rw [coactComponent_apply, coactComponent_apply, b.conjugateMatrixComodule_coact,
    matrixCoact_apply_basisFun, coact_basis_eq_sum_coefficientMatrix b j, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [LinearMap.tensorComponent_tmul, map_smulₛₗ, b.conjEquivFun_self,
    LinearMap.intrinsicStar_apply, starRingEnd_apply]

private theorem map_conjEquivFun_coact_mem (b : Basis ι R M) (S : Subcomodule R A M) :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    ∀ y ∈ S.toSubmodule.map b.conjEquivFun.toLinearMap, coact (R := R) (C := A) y ∈
      LinearMap.range (TensorProduct.map
        (S.toSubmodule.map b.conjEquivFun.toLinearMap).subtype LinearMap.id) := by
  let _ : Comodule R A (ι → R) := b.conjugateMatrixComodule
  rintro _ ⟨m, hm, rfl⟩
  refine (Submodule.tensor_mem_range_iff_forall_tensorComponent_mem _ _).mpr fun f ↦ ?_
  rw [LinearEquiv.coe_toLinearMap, ← coactComponent_apply, coactComponent_conjEquivFun b (toConv f)]
  exact ⟨_, by simpa [coactComponent_apply, LinearMap.tensorComponent_def] using
    S.rid_lTensor_coact_mem (star (toConv f)).ofConv hm, rfl⟩

private theorem map_conjEquivFun_symm_coact_mem (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    ∀ (T : Subcomodule R A (ι → R)) (m : M),
      m ∈ T.toSubmodule.map b.conjEquivFun.symm.toLinearMap → coact (R := R) (C := A) m ∈
        LinearMap.range (TensorProduct.map
          (T.toSubmodule.map b.conjEquivFun.symm.toLinearMap).subtype LinearMap.id) := by
  let _ : Comodule R A (ι → R) := b.conjugateMatrixComodule
  rintro T _ ⟨y, hy, rfl⟩
  refine (Submodule.tensor_mem_range_iff_forall_tensorComponent_mem _ _).mpr fun f ↦ ?_
  have hcomp : coactComponent (R := R) (C := A) (M := M) f (b.conjEquivFun.symm y) =
      b.conjEquivFun.symm
        (coactComponent (R := R) (C := A) (M := ι → R) (star (toConv f)).ofConv y) :=
    b.conjEquivFun.injective <| by
      rw [LinearEquiv.apply_symm_apply, ← b.conjEquivFun.apply_symm_apply y,
        coactComponent_conjEquivFun b (star (toConv f)), star_star, LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.coe_toLinearMap, ← coactComponent_apply, hcomp]
  exact ⟨_, by simpa [coactComponent_apply, LinearMap.tensorComponent_def] using
    T.rid_lTensor_coact_mem (star (toConv f)).ofConv hy, rfl⟩

/-- Coordinatewise conjugation in a finite basis `b` induces an order isomorphism between the
subcomodule lattice of `M` and that of `b.conjugateMatrixComodule`. -/
noncomputable def conjugateSubcomoduleOrderIso (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    Subcomodule R A M ≃o Subcomodule R A (ι → R) :=
  letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
  { toFun S := Subcomodule.ofSubmodule (S.toSubmodule.map b.conjEquivFun.toLinearMap)
      (map_conjEquivFun_coact_mem b S)
    invFun T := Subcomodule.ofSubmodule (T.toSubmodule.map b.conjEquivFun.symm.toLinearMap)
      (map_conjEquivFun_symm_coact_mem b T)
    left_inv S := Subcomodule.ext fun _ ↦ by simp
    right_inv T := Subcomodule.ext fun _ ↦ by simp
    map_rel_iff' := ⟨fun h m hm ↦ by obtain ⟨_, hm', heq⟩ := h ⟨m, hm, rfl⟩
                                     exact b.conjEquivFun.injective heq ▸ hm',
      fun h _ ⟨m, hm, heq⟩ ↦ ⟨m, h hm, heq⟩⟩ }

/-- Membership in `b.conjugateSubcomoduleOrderIso S` reduces to `b.conjEquivFun.symm`. -/
@[simp]
theorem mem_conjugateSubcomoduleOrderIso_iff (b : Basis ι R M) (S : Subcomodule R A M) (y : ι → R) :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    y ∈ b.conjugateSubcomoduleOrderIso S ↔ b.conjEquivFun.symm y ∈ S :=
  ⟨fun ⟨_, hm, h⟩ ↦ h ▸ by simpa using hm, fun hy ↦ ⟨_, hy, by simp⟩⟩

/-- Membership in `(b.conjugateSubcomoduleOrderIso).symm T` reduces to `b.conjEquivFun`. -/
@[simp]
theorem mem_conjugateSubcomoduleOrderIso_symm_iff (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    ∀ (T : Subcomodule R A (ι → R)) (m : M),
      m ∈ b.conjugateSubcomoduleOrderIso.symm T ↔ b.conjEquivFun m ∈ T :=
  letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
  fun _ _ ↦ ⟨fun ⟨_, hy, h⟩ ↦ h ▸ by simpa using hy, fun hm ↦ ⟨_, hm, by simp⟩⟩

/-- If `M` is a simple comodule, then `b.conjugateMatrixComodule` is also simple. -/
theorem isSimpleOrder_conjugateMatrixComodule [IsSimpleOrder (Subcomodule R A M)]
    (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    IsSimpleOrder (Subcomodule R A (ι → R)) :=
  letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
  b.conjugateSubcomoduleOrderIso.symm.isSimpleOrder

end ConjugateSubcomodule

end Module.Basis
