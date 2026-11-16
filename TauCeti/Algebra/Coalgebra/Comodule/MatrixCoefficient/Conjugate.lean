/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Unitary
public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Module
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FromMatrix
public import TauCeti.Algebra.Coalgebra.Comodule.Transport
public import TauCeti.Algebra.Coalgebra.Star
public import TauCeti.Algebra.Coalgebra.Subcomodule.Transport

/-!
# Conjugate matrix comodules over star bialgebras

Over a star bialgebra, entrywise conjugation of a multiplicative matrix `Y` yields a second
multiplicative matrix `Y.map star`, whose comodule is the conjugate corepresentation. Entrywise
conjugation of vectors intertwines the convolution-dual actions of `Y` and `Y.map star` through
the conjugate dual functional `f ↦ (a ↦ star (f (star a)))`, giving an order isomorphism between
their subcomodule lattices. In particular `Y.map star` is simple if and only if `Y` is simple.

Over a Hopf star algebra, if the coefficient matrix `u` of a finite basis is unitary, then
`S(u) = uᴴ` and `S(u.map star) = (S²(u))ᵀ`, so `(S²(u))ᵀ` is a two-sided inverse of `u.map star`.

## Main declarations

* `TauCeti.Comodule.map_comul_map_star` and `TauCeti.Comodule.map_counit_map_star`: entrywise
  star preserves the matrix comultiplication and counit equations.
* `TauCeti.Comodule.subcomoduleMatrixStarOrderIso`: order isomorphism between the subcomodule
  lattices of `matrixComodule R Y` and `matrixComodule R (Y.map star)`.
* `TauCeti.Comodule.isSimpleOrder_matrixComodule_map_star_iff`: `Y.map star` is simple iff `Y` is.
* `TauCeti.Comodule.isSimpleOrder_matrixComodule_coefficientMatrix_map_star`: the conjugate
  comodule of a simple comodule with a finite basis is simple.
* `TauCeti.Comodule.map_antipode_coefficientMatrix_eq_conjTranspose`: for a unitary coefficient
  matrix `u`, `u.map S = uᴴ`.
* `TauCeti.Comodule.map_antipode_map_star_coefficientMatrix`: for a unitary coefficient matrix
  `u`, `(u.map star).map S = (u.map (S ∘ S))ᵀ`.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.2.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*,
  SMF, 2013, Section 1.4.
-/

public noncomputable section

open Module Matrix
open scoped TensorProduct

namespace TauCeti.Comodule

section StarBialgebra

variable {R S ι : Type*} [CommSemiring R] [StarRing R]
  [Semiring S] [Bialgebra R S] [StarRing S] [StarModule R S] [StarCoalgebra R S]

/-- Entrywise `star` preserves the matrix comultiplication equation over a star bialgebra. -/
theorem map_comul_map_star [Fintype ι] (Y : Matrix ι ι S)
    (hcomul : Y.map (Bialgebra.comulAlgHom R S) =
      Y.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        Y.map (Algebra.TensorProduct.includeRight (R := R))) :
    (Y.map star).map (Bialgebra.comulAlgHom R S) =
      (Y.map star).map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        (Y.map star).map (Algebra.TensorProduct.includeRight (R := R)) := by
  rw [map_comul_iff] at hcomul ⊢
  intro i j
  simp [hcomul i j, star_sum]

/-- Entrywise `star` preserves the matrix counit equation over a star bialgebra. -/
theorem map_counit_map_star [DecidableEq ι] (Y : Matrix ι ι S)
    (hcounit : Y.map (Bialgebra.counitAlgHom R S) = 1) :
    (Y.map star).map (Bialgebra.counitAlgHom R S) = 1 := by
  rw [map_counit_iff] at hcounit ⊢
  intro i j
  simp only [Matrix.map_apply, StarCoalgebra.counit_star, hcounit i j]
  split_ifs <;> simp

/-- Entrywise `star` preserves the basis-coordinate counit condition for `matrixComodule`. -/
theorem counit_basisFun_map_star [Finite ι] (Y : Matrix ι ι S)
    (hcounit : ∀ i j, Coalgebra.counit (R := R) (Y i j) =
      (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i) :
    ∀ i j, Coalgebra.counit (R := R) ((Y.map star) i j) =
      (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i := by
  classical
  intro i j
  simp only [Matrix.map_apply, StarCoalgebra.counit_star, hcounit i j, Basis.repr_self_apply]
  split_ifs <;> simp

end StarBialgebra

section CoefficientMatrix

variable {R S M ι : Type*} [CommSemiring R] [Semiring S] [Bialgebra R S]
  [AddCommMonoid M] [Module R M] [Comodule R S M]

/-- The coefficient matrix of a finite basis satisfies the basis-coordinate counit condition. -/
theorem coefficientMatrix_counit_basisFun [Finite ι] (b : Basis ι R M) :
    ∀ i j, Coalgebra.counit (R := R) (coefficientMatrix (C := S) b i j) =
      (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i := by
  classical
  intro i j
  rw [counit_coefficientMatrix, Basis.repr_self_apply]
  simp only [eq_comm]

variable [Fintype ι]

/-- The coefficient matrix of a finite basis satisfies the matrix comultiplication equation. -/
theorem coefficientMatrix_map_comul (b : Basis ι R M) :
    (coefficientMatrix (C := S) b).map (Bialgebra.comulAlgHom R S) =
      (coefficientMatrix (C := S) b).map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        (coefficientMatrix (C := S) b).map (Algebra.TensorProduct.includeRight (R := R)) := by
  rw [map_comul_iff]
  intro i j
  exact comul_coefficientMatrix_eq_sum b i j

/-- Transporting a comodule along `b.equivFun` produces the matrix comodule of its coefficient
matrix. -/
theorem transport_equivFun_eq_matrixComodule (b : Basis ι R M) :
    Transport (R := R) (C := S) b.equivFun =
      matrixComodule R (coefficientMatrix (C := S) b)
        (coefficientMatrix_map_comul (S := S) b)
        (coefficientMatrix_counit_basisFun (S := S) b) := by
  rw [transport_eq_iff]
  apply b.ext
  intro j
  have hb_apply (k : ι) : b.equivFun (b k) = Pi.basisFun R ι k := by
    classical
    ext i
    simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]
  simp only [LinearMap.coe_comp, Function.comp_apply, coact_basis_eq_sum_coefficientMatrix b,
    map_sum, TensorProduct.map_tmul, LinearEquiv.coe_coe, LinearMap.id_apply,
    matrixComodule_coact, hb_apply, matrixCoact_apply_basisFun]

end CoefficientMatrix

section MatrixCoactHelper

variable {R S ι : Type*} [CommRing R] [AddCommMonoid S] [Module R S] [Fintype ι]

private theorem tensorComponent_matrixCoact_apply (Y : Matrix ι ι S) (f : S →ₗ[R] R)
    (v : ι → R) (i : ι) :
    LinearMap.tensorComponent f (matrixCoact R Y v) i = ∑ j, v j * f (Y i j) := by
  classical
  have hv : v = ∑ j, v j • Pi.basisFun R ι j := by
    ext k
    simp [Pi.basisFun_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, matrixCoact_apply_basisFun, LinearMap.tensorComponent_tmul]
  simp [Pi.basisFun_apply, Pi.single_apply, Finset.sum_apply, smul_eq_mul]

variable [StarRing R] [StarAddMonoid S] [StarModule R S]

/-- The conjugate-linear dual functional `a ↦ star (f (star a))`, which is `R`-linear. -/
private def starDual (f : S →ₗ[R] R) : S →ₗ[R] R where
  toFun a := star (f (star a))
  map_add' a b := by simp
  map_smul' r a := by simp

private theorem starDual_starDual (f : S →ₗ[R] R) : starDual (starDual f) = f := by
  ext a
  simp [starDual]

private theorem star_tensorComponent_matrixCoact (Y : Matrix ι ι S) (f : S →ₗ[R] R)
    (v : ι → R) :
    star (LinearMap.tensorComponent f (matrixCoact R Y v)) =
      LinearMap.tensorComponent (starDual f) (matrixCoact R (Y.map star) (star v)) := by
  ext i
  rw [Pi.star_apply, tensorComponent_matrixCoact_apply, tensorComponent_matrixCoact_apply,
    star_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [starDual]

end MatrixCoactHelper

section Simplicity

variable {R S ι : Type*} [CommRing R] [Ring S] [Bialgebra R S] [Fintype ι]

private theorem tensorComponent_mem_of_convolutionSubmodule (Y : Matrix ι ι S)
    (hcomul : Y.map (Bialgebra.comulAlgHom R S) =
      Y.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        Y.map (Algebra.TensorProduct.includeRight (R := R)))
    (hcounit : ∀ i j, Coalgebra.counit (R := R) (Y i j) =
      (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i)
    (W : letI := matrixComodule R Y hcomul hcounit
      letI := convolutionModule (R := R) (C := S) (M := ι → R)
      Submodule (WithConv (S →ₗ[R] R)) (ι → R))
    (f : S →ₗ[R] R) {v : ι → R} (hv : v ∈ W) :
    LinearMap.tensorComponent f (matrixCoact R Y v) ∈ W := by
  let _ : Comodule R S (ι → R) := matrixComodule R Y hcomul hcounit
  let _ : Module (WithConv (S →ₗ[R] R)) (ι → R) := convolutionModule (R := R) (C := S)
  simpa only [Comodule.convolutionModule_smul, matrixComodule_coact, WithConv.ofConv_toConv] using
    W.smul_mem (WithConv.toConv f) hv

variable [StarRing R] [StarRing S] [StarModule R S]

/-- Entrywise conjugation sends a convolution-dual submodule of `matrixComodule R Y₁` to one of
`matrixComodule R Y₂` whenever `Y₁.map star = Y₂`. -/
private def starConvSubmodule {Y₁ Y₂ : Matrix ι ι S} (hstar : Y₁.map star = Y₂)
    (hcomul₁ : Y₁.map (Bialgebra.comulAlgHom R S) =
      Y₁.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        Y₁.map (Algebra.TensorProduct.includeRight (R := R)))
    (hcounit₁ : ∀ i j, Coalgebra.counit (R := R) (Y₁ i j) =
      (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i)
    (hcomul₂ : Y₂.map (Bialgebra.comulAlgHom R S) =
      Y₂.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        Y₂.map (Algebra.TensorProduct.includeRight (R := R)))
    (hcounit₂ : ∀ i j, Coalgebra.counit (R := R) (Y₂ i j) =
      (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i)
    (W : letI := matrixComodule R Y₁ hcomul₁ hcounit₁
      letI := convolutionModule (R := R) (C := S) (M := ι → R)
      Submodule (WithConv (S →ₗ[R] R)) (ι → R)) :
    letI := matrixComodule R Y₂ hcomul₂ hcounit₂
    letI := convolutionModule (R := R) (C := S) (M := ι → R)
    Submodule (WithConv (S →ₗ[R] R)) (ι → R) :=
  letI : Comodule R S (ι → R) := matrixComodule R Y₂ hcomul₂ hcounit₂
  letI : Module (WithConv (S →ₗ[R] R)) (ι → R) := convolutionModule (R := R) (C := S)
  { carrier := {v | star v ∈ W}
    zero_mem' := by
      simp only [Set.mem_ofPred_eq, star_zero]
      exact W.zero_mem
    add_mem' := fun hx hy ↦ by
      simp only [Set.mem_ofPred_eq, star_add]
      exact W.add_mem hx hy
    smul_mem' := fun f v hv ↦ by
      simp only [Set.mem_ofPred_eq, Comodule.convolutionModule_smul, matrixComodule_coact]
      have hact := star_tensorComponent_matrixCoact (Y := Y₁) (starDual f.ofConv) (star v)
      rw [starDual_starDual, star_star, hstar] at hact
      have hact' : star (LinearMap.tensorComponent f.ofConv (matrixCoact R Y₂ v)) =
          LinearMap.tensorComponent (starDual f.ofConv) (matrixCoact R Y₁ (star v)) := by
        simpa using congrArg star hact.symm
      rw [hact']
      exact tensorComponent_mem_of_convolutionSubmodule Y₁ hcomul₁ hcounit₁ W
        (starDual f.ofConv) hv }

variable [Module.Projective R S] [StarCoalgebra R S]

/-- **Subcomodule lattice isomorphism for conjugate matrix comodules.** Entrywise `star` induces
an order isomorphism between the subcomodules of `matrixComodule R Y` and those of
`matrixComodule R (Y.map star)`. -/
def subcomoduleMatrixStarOrderIso (Y : Matrix ι ι S)
    (hcomul : Y.map (Bialgebra.comulAlgHom R S) =
      Y.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        Y.map (Algebra.TensorProduct.includeRight (R := R)))
    (hcounit : ∀ i j, Coalgebra.counit (R := R) (Y i j) =
      (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i) :
    (letI := matrixComodule R Y hcomul hcounit; Subcomodule R S (ι → R)) ≃o
    (letI := matrixComodule R (Y.map star) (map_comul_map_star Y hcomul)
        (counit_basisFun_map_star Y hcounit); Subcomodule R S (ι → R)) := by
  let c₁ : Comodule R S (ι → R) := matrixComodule R Y hcomul hcounit
  let c₂ : Comodule R S (ι → R) :=
    matrixComodule R (Y.map star) (map_comul_map_star Y hcomul)
      (counit_basisFun_map_star Y hcounit)
  let e₁ := @Subcomodule.convolutionSubmoduleOrderIso R S (ι → R) _ _ _ _ _ _ _ c₁
  let e₂ := @Subcomodule.convolutionSubmoduleOrderIso R S (ι → R) _ _ _ _ _ _ _ c₂
  have hYY : (Y.map star).map star = Y := by ext i j; simp
  have hcomul' := map_comul_map_star Y hcomul
  have hcounit' := counit_basisFun_map_star Y hcounit
  let φ :
      (letI := c₁; letI := convolutionModule (R := R) (C := S) (M := ι → R);
        Submodule (WithConv (S →ₗ[R] R)) (ι → R)) ≃o
      (letI := c₂; letI := convolutionModule (R := R) (C := S) (M := ι → R);
        Submodule (WithConv (S →ₗ[R] R)) (ι → R)) :=
    { toFun := starConvSubmodule rfl hcomul hcounit hcomul' hcounit'
      invFun := starConvSubmodule hYY hcomul' hcounit' hcomul hcounit
      left_inv := fun W ↦ by
        apply SetLike.ext
        intro v
        simp only [starConvSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
          AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, star_star]
      right_inv := fun W ↦ by
        apply SetLike.ext
        intro v
        simp only [starConvSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
          AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, star_star]
      map_rel_iff' := fun {W₁ W₂} ↦ by
        constructor
        · intro h v hv
          have hv' : star (star v) ∈ W₁ := by simpa using hv
          have hmem : star v ∈ starConvSubmodule rfl hcomul hcounit hcomul' hcounit' W₂ := h hv'
          have hmem' : star (star v) ∈ W₂ := hmem
          simpa using hmem'
        · intro h v hv
          exact h hv }
  exact (e₁.trans φ).trans e₂.symm

/-- A conjugate matrix comodule `Y.map star` is simple if and only if `Y` is simple. -/
theorem isSimpleOrder_matrixComodule_map_star_iff (Y : Matrix ι ι S)
    (hcomul : Y.map (Bialgebra.comulAlgHom R S) =
      Y.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        Y.map (Algebra.TensorProduct.includeRight (R := R)))
    (hcounit : ∀ i j, Coalgebra.counit (R := R) (Y i j) =
      (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i) :
    (letI := matrixComodule R (Y.map star) (map_comul_map_star Y hcomul)
        (counit_basisFun_map_star Y hcounit); IsSimpleOrder (Subcomodule R S (ι → R))) ↔
    (letI := matrixComodule R Y hcomul hcounit; IsSimpleOrder (Subcomodule R S (ι → R))) :=
  (subcomoduleMatrixStarOrderIso Y hcomul hcounit).symm.isSimpleOrder_iff

/-- The conjugate matrix comodule of a simple comodule with a finite basis is simple. -/
theorem isSimpleOrder_matrixComodule_coefficientMatrix_map_star {M : Type*}
    [AddCommGroup M] [Module R M] [Comodule R S M] [IsSimpleOrder (Subcomodule R S M)]
    (b : Basis ι R M) :
    letI := matrixComodule R ((coefficientMatrix (C := S) b).map star)
      (map_comul_map_star _ (coefficientMatrix_map_comul (S := S) b))
      (counit_basisFun_map_star _ (coefficientMatrix_counit_basisFun (S := S) b))
    IsSimpleOrder (Subcomodule R S (ι → R)) := by
  rw [isSimpleOrder_matrixComodule_map_star_iff (coefficientMatrix (C := S) b)
    (coefficientMatrix_map_comul (S := S) b) (coefficientMatrix_counit_basisFun (S := S) b)]
  rw [← transport_equivFun_eq_matrixComodule b]
  exact (Subcomodule.transportOrderIso (R := R) (C := S) b.equivFun).isSimpleOrder_iff.mp
    inferInstance

end Simplicity

section HopfUnitary

variable {R S M ι : Type*} [CommSemiring R]
  [Semiring S] [HopfAlgebra R S] [StarRing S]
  [AddCommMonoid M] [Module R M] [Comodule R S M] [Fintype ι] [DecidableEq ι]

/-- For a finite basis with unitary coefficient matrix `u`, the entrywise antipode of `u` is its
conjugate transpose `uᴴ`. -/
theorem map_antipode_coefficientMatrix_eq_conjTranspose (b : Basis ι R M)
    (hu : coefficientMatrix (C := S) b ∈ unitary (Matrix ι ι S)) :
    (coefficientMatrix (C := S) b).map (HopfAlgebra.antipode R) =
      (coefficientMatrix (C := S) b)ᴴ :=
  left_inv_eq_right_inv (map_antipode_mul_coefficientMatrix b) hu.2

/-- For a finite basis with unitary coefficient matrix `u`, the entrywise antipode of the
conjugate matrix `u.map star` is `(u.map (S ∘ S))ᵀ`. -/
theorem map_antipode_map_star_coefficientMatrix (b : Basis ι R M)
    (hu : coefficientMatrix (C := S) b ∈ unitary (Matrix ι ι S)) :
    ((coefficientMatrix (C := S) b).map star).map (HopfAlgebra.antipode R) =
      ((coefficientMatrix (C := S) b).map
        (fun a ↦ HopfAlgebra.antipode R (HopfAlgebra.antipode R a)))ᵀ := by
  have hS := map_antipode_coefficientMatrix_eq_conjTranspose b hu
  ext i j
  have hji : HopfAlgebra.antipode R (coefficientMatrix (C := S) b j i) =
      star (coefficientMatrix (C := S) b i j) := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hS j) i
  simp [hji]

variable [StarRing R] [StarModule R S] [StarCoalgebra R S]

/-- For a unitary coefficient matrix `u` over a Hopf star algebra, `(S²(u))ᵀ` is a right inverse
of the conjugate matrix `u.map star`. -/
theorem map_star_coefficientMatrix_mul_transpose_antipode_antipode (b : Basis ι R M)
    (hu : coefficientMatrix (C := S) b ∈ unitary (Matrix ι ι S)) :
    (coefficientMatrix (C := S) b).map star *
      ((coefficientMatrix (C := S) b).map
        (fun a ↦ HopfAlgebra.antipode R (HopfAlgebra.antipode R a)))ᵀ = 1 := by
  let _ : Comodule R S (ι → R) :=
    matrixComodule R ((coefficientMatrix (C := S) b).map star)
      (map_comul_map_star _ (coefficientMatrix_map_comul (S := S) b))
      (counit_basisFun_map_star _ (coefficientMatrix_counit_basisFun (S := S) b))
  have h := coefficientMatrix_mul_map_antipode (C := S) (Pi.basisFun R ι)
  rw [coefficientMatrix_matrixComodule, map_antipode_map_star_coefficientMatrix b hu] at h
  exact h

/-- For a unitary coefficient matrix `u` over a Hopf star algebra, `(S²(u))ᵀ` is a left inverse
of the conjugate matrix `u.map star`. -/
theorem transpose_antipode_antipode_mul_map_star_coefficientMatrix (b : Basis ι R M)
    (hu : coefficientMatrix (C := S) b ∈ unitary (Matrix ι ι S)) :
    ((coefficientMatrix (C := S) b).map
        (fun a ↦ HopfAlgebra.antipode R (HopfAlgebra.antipode R a)))ᵀ *
      (coefficientMatrix (C := S) b).map star = 1 := by
  let _ : Comodule R S (ι → R) :=
    matrixComodule R ((coefficientMatrix (C := S) b).map star)
      (map_comul_map_star _ (coefficientMatrix_map_comul (S := S) b))
      (counit_basisFun_map_star _ (coefficientMatrix_counit_basisFun (S := S) b))
  have h := map_antipode_mul_coefficientMatrix (C := S) (Pi.basisFun R ι)
  rw [coefficientMatrix_matrixComodule, map_antipode_map_star_coefficientMatrix b hu] at h
  exact h

end HopfUnitary

end TauCeti.Comodule
