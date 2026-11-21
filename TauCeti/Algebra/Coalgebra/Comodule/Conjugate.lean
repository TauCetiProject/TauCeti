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

/-!
# Conjugate comodules over star bialgebras

Let `A` be a star bialgebra over a commutative star semiring `R`, and let `M` be a right
`A`-comodule with a finite basis `b` and coefficient matrix `u`. Because comultiplication and the
counit of a star coalgebra commute with `star`, the entrywise conjugate matrix `u.map star` is
again a multiplicative matrix (`Module.Basis.conjugateMatrixComodule`), whose matrix-coefficient
submodule is the `star`-preimage of that of `M`
(`Module.Basis.mem_matrixCoefficientSubmodule_conjugateMatrixComodule_iff`).

Coordinatewise conjugation (`Module.Basis.conjEquivFun`) intertwines the coaction of `M` with that
of `b.conjugateMatrixComodule` via `star` on `A`, inducing an order isomorphism between their
subcomodule lattices (`Module.Basis.conjugateSubcomoduleOrderIso`) and preserving simplicity
(`Module.Basis.isSimpleOrder_conjugateMatrixComodule`).

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.1.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Section 1.3.
-/

public section

open Module Matrix TauCeti TauCeti.Comodule
open scoped TensorProduct

namespace Module.Basis

section SemilinearSubcomodule

variable {R A M' N' : Type*} [CommSemiring R] [StarRing R]
  [AddCommMonoid A] [StarAddMonoid A] [Module R A] [StarModule R A] [Coalgebra R A]
  [AddCommMonoid M'] [Module R M'] [Comodule R A M']
  [AddCommMonoid N'] [Module R N'] [Comodule R A N']

private noncomputable def mapSemilinearSubcomodule (e : M' ≃ₛₗ[starRingEnd R] N')
    (he : ∀ m, coact (R := R) (C := A) (e m) = TensorProduct.map e.toLinearMap
      (starLinearEquiv R (A := A)).toLinearMap (coact (R := R) (C := A) m))
    (S : Subcomodule R A M') : Subcomodule R A N' :=
  let f : M' →ₛₗ[starRingEnd R] N' := e
  let s : A →ₛₗ[starRingEnd R] A := (starLinearEquiv R (A := A)).toLinearMap
  Subcomodule.ofSubmodule (S.toSubmodule.map f) fun n hn ↦ by
    rw [S.toSubmodule_carrier] at hn ⊢
    rcases Submodule.mem_map.mp hn with ⟨m, hm, rfl⟩
    rcases S.coact_mem hm with ⟨t, ht⟩
    refine ⟨TensorProduct.map (f.submoduleMap S.carrier) s t, ?_⟩
    have h1 : (S.carrier.map f).subtype ∘ₛₗ f.submoduleMap S.carrier = f ∘ₛₗ S.carrier.subtype := by
      ext; simp
    have h2 : (LinearMap.id : A →ₗ[R] A) ∘ₛₗ s = s ∘ₛₗ (LinearMap.id : A →ₗ[R] A) := by ext; simp
    have hcomp := congrArg (fun g ↦ g t) (TensorProduct.map_comp (σ₁₃ := starRingEnd R)
      (S.carrier.map f).subtype (LinearMap.id : A →ₗ[R] A) (f.submoduleMap S.carrier) s).symm
    rw [LinearMap.comp_apply] at hcomp
    rw [hcomp, h1, h2, TensorProduct.map_comp (σ₁₃ := starRingEnd R), LinearMap.comp_apply, ht]
    exact (he m).symm

@[simp]
private theorem mapSemilinearSubcomodule_toSubmodule (e : M' ≃ₛₗ[starRingEnd R] N')
    (he : ∀ m, coact (R := R) (C := A) (e m) = TensorProduct.map e.toLinearMap
      (starLinearEquiv R (A := A)).toLinearMap (coact (R := R) (C := A) m))
    (S : Subcomodule R A M') :
    (mapSemilinearSubcomodule e he S).toSubmodule =
      S.toSubmodule.map (e : M' →ₛₗ[starRingEnd R] N') := (rfl)

end SemilinearSubcomodule

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

private theorem coact_conjEquivFun (b : Basis ι R M) (m : M) :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    coact (R := R) (C := A) (M := ι → R) (b.conjEquivFun m) =
      TensorProduct.map b.conjEquivFun.toLinearMap (starLinearEquiv R (A := A)).toLinearMap
        (coact (R := R) (C := A) (M := M) m) := by
  let _ : Comodule R A (ι → R) := b.conjugateMatrixComodule
  conv_lhs => rw [← b.sum_repr m]
  conv_rhs => rw [← b.sum_repr m]
  simp only [map_sum, map_smulₛₗ, RingHom.id_apply, b.conjEquivFun_self]
  refine Finset.sum_congr rfl fun j _ ↦ congrArg _ ?_
  rw [b.conjugateMatrixComodule_coact, matrixCoact_apply_basisFun,
    coact_basis_eq_sum_coefficientMatrix b j, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by simp [b.conjEquivFun_self]

private theorem coact_conjEquivFun_symm (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    ∀ y : ι → R, coact (R := R) (C := A) (M := M) (b.conjEquivFun.symm y) =
      TensorProduct.map b.conjEquivFun.symm.toLinearMap (starLinearEquiv R (A := A)).toLinearMap
        (coact (R := R) (C := A) (M := ι → R) y) := by
  let _ : Comodule R A (ι → R) := b.conjugateMatrixComodule
  let s := (starLinearEquiv R (A := A)).toLinearMap
  intro y
  have hy := congrArg (TensorProduct.map b.conjEquivFun.symm.toLinearMap s)
    (coact_conjEquivFun b (b.conjEquivFun.symm y))
  have hcomp := congrArg (fun f ↦ f (coact (R := R) (C := A) (M := M) (b.conjEquivFun.symm y)))
    (TensorProduct.map_comp (σ₁₃ := RingHom.id R) b.conjEquivFun.symm.toLinearMap s
      b.conjEquivFun.toLinearMap s)
  rw [LinearMap.comp_apply] at hcomp
  rw [b.conjEquivFun.apply_symm_apply, ← hcomp] at hy
  have h1 : (b.conjEquivFun.symm.toLinearMap ∘ₛₗ b.conjEquivFun.toLinearMap : M →ₗ[R] M) =
      LinearMap.id := LinearMap.ext b.conjEquivFun.symm_apply_apply
  have h2 : (s ∘ₛₗ s : A →ₗ[R] A) = LinearMap.id := LinearMap.ext star_star
  simpa [s, h1, h2] using hy.symm

/-- Coordinatewise conjugation in a finite basis `b` induces an order isomorphism between the
subcomodule lattice of `M` and that of `b.conjugateMatrixComodule`. -/
noncomputable def conjugateSubcomoduleOrderIso (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    Subcomodule R A M ≃o Subcomodule R A (ι → R) :=
  letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
  { toFun := mapSemilinearSubcomodule b.conjEquivFun (coact_conjEquivFun b)
    invFun := mapSemilinearSubcomodule b.conjEquivFun.symm (coact_conjEquivFun_symm b)
    left_inv S := Subcomodule.ext fun _ ↦ by
      simp [← Subcomodule.mem_toSubmodule, Submodule.mem_map_equiv]
    right_inv T := Subcomodule.ext fun _ ↦ by
      simp [← Subcomodule.mem_toSubmodule, Submodule.mem_map_equiv]
    map_rel_iff' := fun {S₁ S₂} ↦ by
      simp [← Subcomodule.toSubmodule_le_toSubmodule,
        Submodule.map_le_map_iff_of_injective b.conjEquivFun.injective] }

/-- Membership in `b.conjugateSubcomoduleOrderIso S` reduces to `b.conjEquivFun.symm`. -/
@[simp]
theorem mem_conjugateSubcomoduleOrderIso_iff (b : Basis ι R M) (S : Subcomodule R A M) (y : ι → R) :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    y ∈ b.conjugateSubcomoduleOrderIso S ↔ b.conjEquivFun.symm y ∈ S := by
  let _ : Comodule R A (ι → R) := b.conjugateMatrixComodule
  simp [← Subcomodule.mem_toSubmodule, conjugateSubcomoduleOrderIso, Submodule.mem_map_equiv]

/-- Membership in `(b.conjugateSubcomoduleOrderIso).symm T` reduces to `b.conjEquivFun`. -/
@[simp]
theorem mem_conjugateSubcomoduleOrderIso_symm_iff (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    ∀ (T : Subcomodule R A (ι → R)) (m : M),
      m ∈ b.conjugateSubcomoduleOrderIso.symm T ↔ b.conjEquivFun m ∈ T := by
  let _ : Comodule R A (ι → R) := b.conjugateMatrixComodule
  intro T m
  simp [← Subcomodule.mem_toSubmodule, conjugateSubcomoduleOrderIso, OrderIso.symm,
    Submodule.mem_map_equiv]

/-- If `M` is a simple comodule, then `b.conjugateMatrixComodule` is also simple. -/
theorem isSimpleOrder_conjugateMatrixComodule [IsSimpleOrder (Subcomodule R A M)]
    (b : Basis ι R M) :
    letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
    IsSimpleOrder (Subcomodule R A (ι → R)) :=
  letI : Comodule R A (ι → R) := b.conjugateMatrixComodule
  b.conjugateSubcomoduleOrderIso.symm.isSimpleOrder

end ConjugateMatrixComodule

end Module.Basis
