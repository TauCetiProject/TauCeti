/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.LinearMap
public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Module
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FromMatrix
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Transport
public import TauCeti.Algebra.Coalgebra.Star
public import TauCeti.Algebra.Coalgebra.Subcomodule.Transport

/-!
# Conjugate matrix comodules over star bialgebras

Over a star bialgebra, entrywise conjugation of a multiplicative matrix `Y` yields a second
multiplicative matrix `Y.map star`, whose comodule is the conjugate corepresentation. Over a
commutative ring with a projective coefficient star bialgebra `S`, entrywise conjugation of vectors
intertwines the convolution-dual actions of `Y` and `Y.map star` through Mathlib's intrinsic star
`LinearMap.intrinsicStar` on `WithConv (S →ₗ[R] R)`, giving an order isomorphism between their
subcomodule lattices (`Matrix.subcomoduleMatrixStarOrderIso`). In particular `Y.map star` is simple
if and only if `Y` is simple, and the named conjugate comodule
`Module.Basis.conjugateMatrixComodule` of a simple comodule with a finite basis is simple.

Over a Hopf star algebra, if the coefficient matrix `u` of a finite basis is unitary, then
`S(u) = uᴴ` and `S(u.map star) = (S²(u))ᵀ`, so `(S²(u))ᵀ` is a two-sided inverse of `u.map star`.

## Main declarations

* `Matrix.map_comul_map_star`, `Matrix.map_counit_map_star`, and
  `Matrix.counit_basisFun_map_star`: entrywise star preserves the matrix comultiplication and
  counit equations.
* `Matrix.subcomoduleMatrixStarOrderIso`, `Matrix.mem_subcomoduleMatrixStarOrderIso`, and
  `Matrix.mem_subcomoduleMatrixStarOrderIso_symm`: order isomorphism between the subcomodule
  lattices of `matrixComodule R Y` and `matrixComodule R (Y.map star)`.
* `Matrix.isSimpleOrder_matrixComodule_map_star_iff`: `Y.map star` is simple iff `Y` is.
* `Module.Basis.conjugateMatrixComodule`, `Module.Basis.conjugateMatrixComodule_coact`,
  `Module.Basis.coefficientMatrix_conjugateMatrixComodule`, and
  `Module.Basis.isSimpleOrder_conjugateMatrixComodule`: the conjugate matrix comodule of a finite
  basis and its simplicity.
* `Module.Basis.map_antipode_coefficientMatrix_eq_conjTranspose`: for a unitary coefficient
  matrix `u`, `u.map S = uᴴ`.
* `Module.Basis.map_antipode_map_star_coefficientMatrix`: for a unitary coefficient matrix `u`,
  `(u.map star).map S = (u.map (S ∘ S))ᵀ`.
* `Module.Basis.map_star_coefficientMatrix_mul_transpose_antipode_antipode` and
  `Module.Basis.transpose_antipode_antipode_mul_map_star_coefficientMatrix`: `(S²(u))ᵀ` is a
  two-sided inverse of `u.map star`.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.2.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*,
  SMF, 2013, Section 1.4.
-/

public noncomputable section

open Module TauCeti TauCeti.Comodule
open scoped Matrix TensorProduct

namespace Matrix

section StarCoalgebra

variable {R S ι : Type*} [CommSemiring R] [StarRing R]
  [AddCommMonoid S] [StarAddMonoid S] [Module R S] [StarModule R S]
  [Coalgebra R S] [StarCoalgebra R S]

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

end StarCoalgebra

section StarBialgebra

variable {R S ι : Type*} [CommSemiring R] [StarRing R]
  [Semiring S] [Bialgebra R S] [StarAddMonoid S] [StarModule R S] [StarCoalgebra R S]

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

end StarBialgebra

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

private theorem star_tensorComponent_matrixCoact (Y : Matrix ι ι S) (f : WithConv (S →ₗ[R] R))
    (v : ι → R) :
    star (LinearMap.tensorComponent f.ofConv (matrixCoact R Y v)) =
      LinearMap.tensorComponent (star f).ofConv (matrixCoact R (Y.map star) (star v)) := by
  ext i
  rw [Pi.star_apply, tensorComponent_matrixCoact_apply, tensorComponent_matrixCoact_apply,
    star_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hf : (star f).ofConv (star (Y i j)) = star (f.ofConv (Y i j)) := by
    simp [star_star]
  simp [hf]

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

variable [StarRing R] [StarAddMonoid S] [StarModule R S]

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
      have hact := star_tensorComponent_matrixCoact (Y := Y₁) (star f) (star v)
      rw [star_star, star_star, hstar] at hact
      have hact' : star (LinearMap.tensorComponent f.ofConv (matrixCoact R Y₂ v)) =
          LinearMap.tensorComponent (star f).ofConv (matrixCoact R Y₁ (star v)) := by
        simpa using congrArg star hact.symm
      rw [hact']
      exact tensorComponent_mem_of_convolutionSubmodule Y₁ hcomul₁ hcounit₁ W (star f).ofConv hv }

@[simp]
private theorem mem_starConvSubmodule {Y₁ Y₂ : Matrix ι ι S} (hstar : Y₁.map star = Y₂)
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
      Submodule (WithConv (S →ₗ[R] R)) (ι → R)) (v : ι → R) :
    v ∈ starConvSubmodule hstar hcomul₁ hcounit₁ hcomul₂ hcounit₂ W ↔ star v ∈ W :=
  Iff.rfl

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
    (letI := matrixComodule R (Y.map star) (Y.map_comul_map_star hcomul)
        (Y.counit_basisFun_map_star hcounit); Subcomodule R S (ι → R)) := by
  let c₁ : Comodule R S (ι → R) := matrixComodule R Y hcomul hcounit
  let c₂ : Comodule R S (ι → R) :=
    matrixComodule R (Y.map star) (Y.map_comul_map_star hcomul)
      (Y.counit_basisFun_map_star hcounit)
  let e₁ := @Subcomodule.convolutionSubmoduleOrderIso R S (ι → R) _ _ _ _ _ _ _ c₁
  let e₂ := @Subcomodule.convolutionSubmoduleOrderIso R S (ι → R) _ _ _ _ _ _ _ c₂
  have hYY : (Y.map star).map star = Y := by ext i j; simp
  have hcomul' := Y.map_comul_map_star hcomul
  have hcounit' := Y.counit_basisFun_map_star hcounit
  let φ :
      (letI := c₁; letI := convolutionModule (R := R) (C := S) (M := ι → R);
        Submodule (WithConv (S →ₗ[R] R)) (ι → R)) ≃o
      (letI := c₂; letI := convolutionModule (R := R) (C := S) (M := ι → R);
        Submodule (WithConv (S →ₗ[R] R)) (ι → R)) :=
    { toFun := starConvSubmodule rfl hcomul hcounit hcomul' hcounit'
      invFun := starConvSubmodule hYY hcomul' hcounit' hcomul hcounit
      left_inv := fun W ↦ SetLike.ext fun v ↦ by simp
      right_inv := fun W ↦ SetLike.ext fun v ↦ by simp
      map_rel_iff' := fun {W₁ W₂} ↦ by
        simp only [Equiv.coe_fn_mk, IsConcreteLE.le_iff, mem_starConvSubmodule]
        exact ⟨fun h v hv ↦ by simpa using h (x := star v) (by simpa using hv),
          fun h v hv ↦ h hv⟩ }
  exact (e₁.trans φ).trans e₂.symm

/-- Membership in the image of a subcomodule under `Matrix.subcomoduleMatrixStarOrderIso` is
tested by entrywise conjugation. -/
@[simp]
theorem mem_subcomoduleMatrixStarOrderIso (Y : Matrix ι ι S)
    (hcomul : Y.map (Bialgebra.comulAlgHom R S) =
      Y.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        Y.map (Algebra.TensorProduct.includeRight (R := R)))
    (hcounit : ∀ i j, Coalgebra.counit (R := R) (Y i j) =
      (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i)
    (W : letI := matrixComodule R Y hcomul hcounit; Subcomodule R S (ι → R)) (v : ι → R) :
    v ∈ Y.subcomoduleMatrixStarOrderIso hcomul hcounit W ↔ star v ∈ W := by
  simp [subcomoduleMatrixStarOrderIso, Subcomodule.mem_toConvolutionSubmodule,
    Submodule.mem_toSubcomodule]

/-- Membership in the preimage of a subcomodule under `Matrix.subcomoduleMatrixStarOrderIso` is
tested by entrywise conjugation. -/
@[simp]
theorem mem_subcomoduleMatrixStarOrderIso_symm (Y : Matrix ι ι S)
    (hcomul : Y.map (Bialgebra.comulAlgHom R S) =
      Y.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        Y.map (Algebra.TensorProduct.includeRight (R := R)))
    (hcounit : ∀ i j, Coalgebra.counit (R := R) (Y i j) =
      (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i)
    (W :
      letI := matrixComodule R (Y.map star) (Y.map_comul_map_star hcomul)
        (Y.counit_basisFun_map_star hcounit)
      Subcomodule R S (ι → R)) (v : ι → R) :
    v ∈ (Y.subcomoduleMatrixStarOrderIso hcomul hcounit).symm W ↔ star v ∈ W := by
  simp [subcomoduleMatrixStarOrderIso, Subcomodule.mem_toConvolutionSubmodule,
    Submodule.mem_toSubcomodule]

/-- A conjugate matrix comodule `Y.map star` is simple if and only if `Y` is simple. -/
theorem isSimpleOrder_matrixComodule_map_star_iff (Y : Matrix ι ι S)
    (hcomul : Y.map (Bialgebra.comulAlgHom R S) =
      Y.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        Y.map (Algebra.TensorProduct.includeRight (R := R)))
    (hcounit : ∀ i j, Coalgebra.counit (R := R) (Y i j) =
      (Pi.basisFun R ι).repr ((Pi.basisFun R ι) j) i) :
    (letI := matrixComodule R (Y.map star) (Y.map_comul_map_star hcomul)
        (Y.counit_basisFun_map_star hcounit); IsSimpleOrder (Subcomodule R S (ι → R))) ↔
    (letI := matrixComodule R Y hcomul hcounit; IsSimpleOrder (Subcomodule R S (ι → R))) :=
  (Y.subcomoduleMatrixStarOrderIso hcomul hcounit).symm.isSimpleOrder_iff

end Simplicity

end Matrix

namespace Module.Basis

section ConjugateMatrixComodule

variable {R C M ι : Type*} [CommSemiring R] [StarRing R]
  [Semiring C] [Bialgebra R C] [StarAddMonoid C] [StarModule R C] [StarCoalgebra R C]
  [AddCommMonoid M] [Module R M] [Comodule R C M] [Fintype ι]

/-- The conjugate matrix comodule on `ι → R` associated with a finite basis `b`, whose coefficient
matrix in the standard basis `Pi.basisFun R ι` is `(coefficientMatrix b).map star`. -/
@[instance_reducible]
def conjugateMatrixComodule (b : Basis ι R M) : Comodule R C (ι → R) :=
  matrixComodule R ((coefficientMatrix (C := C) b).map star)
    ((coefficientMatrix (C := C) b).map_comul_map_star (b.coefficientMatrix_map_comul (C := C)))
    ((coefficientMatrix (C := C) b).counit_basisFun_map_star
      (b.coefficientMatrix_counit_basisFun (C := C)))

/-- The coaction of `conjugateMatrixComodule` is given by `matrixCoact` of the entrywise starred
coefficient matrix. -/
theorem conjugateMatrixComodule_coact (b : Basis ι R M) :
    letI : Comodule R C (ι → R) := b.conjugateMatrixComodule (C := C)
    coact (R := R) (C := C) (M := ι → R) =
      matrixCoact R ((coefficientMatrix (C := C) b).map star) := by
  exact matrixComodule_coact _ _ _ _

/-- The coefficient matrix of `conjugateMatrixComodule` in the standard basis is
`(coefficientMatrix b).map star`. -/
theorem coefficientMatrix_conjugateMatrixComodule (b : Basis ι R M) :
    letI : Comodule R C (ι → R) := b.conjugateMatrixComodule (C := C)
    coefficientMatrix (C := C) (Pi.basisFun R ι) = (coefficientMatrix (C := C) b).map star := by
  exact coefficientMatrix_matrixComodule _ _ _ _

end ConjugateMatrixComodule

section ConjugateSimplicity

variable {R C M ι : Type*} [CommRing R] [StarRing R]
  [Ring C] [Bialgebra R C] [Module.Projective R C]
  [StarAddMonoid C] [StarModule R C] [StarCoalgebra R C]
  [AddCommGroup M] [Module R M] [Comodule R C M] [Fintype ι]

/-- The conjugate matrix comodule of a simple comodule with a finite basis is simple. -/
theorem isSimpleOrder_conjugateMatrixComodule [IsSimpleOrder (Subcomodule R C M)]
    (b : Basis ι R M) :
    letI := b.conjugateMatrixComodule (C := C)
    IsSimpleOrder (Subcomodule R C (ι → R)) := by
  rw [conjugateMatrixComodule, Matrix.isSimpleOrder_matrixComodule_map_star_iff
    (coefficientMatrix (C := C) b) (b.coefficientMatrix_map_comul (C := C))
    (b.coefficientMatrix_counit_basisFun (C := C)),
    ← b.transport_equivFun_eq_matrixComodule]
  exact (Subcomodule.transportOrderIso (R := R) (C := C) b.equivFun).isSimpleOrder_iff.mp
    inferInstance

end ConjugateSimplicity

section HopfUnitary

variable {R C M ι : Type*} [CommSemiring R]
  [Semiring C] [HopfAlgebra R C] [StarRing C]
  [AddCommMonoid M] [Module R M] [Comodule R C M] [Fintype ι] [DecidableEq ι]

/-- For a finite basis with unitary coefficient matrix `u`, the entrywise antipode of `u` is its
conjugate transpose `uᴴ`. -/
theorem map_antipode_coefficientMatrix_eq_conjTranspose (b : Basis ι R M)
    (hu : coefficientMatrix (C := C) b ∈ unitary (Matrix ι ι C)) :
    (coefficientMatrix (C := C) b).map (HopfAlgebra.antipode R) =
      (coefficientMatrix (C := C) b)ᴴ :=
  left_inv_eq_right_inv (map_antipode_mul_coefficientMatrix b) hu.2

/-- For a finite basis with unitary coefficient matrix `u`, the entrywise antipode of the
conjugate matrix `u.map star` is `(u.map (S ∘ S))ᵀ`. -/
theorem map_antipode_map_star_coefficientMatrix (b : Basis ι R M)
    (hu : coefficientMatrix (C := C) b ∈ unitary (Matrix ι ι C)) :
    ((coefficientMatrix (C := C) b).map star).map (HopfAlgebra.antipode R) =
      ((coefficientMatrix (C := C) b).map
        (fun a ↦ HopfAlgebra.antipode R (HopfAlgebra.antipode R a)))ᵀ := by
  have hS := b.map_antipode_coefficientMatrix_eq_conjTranspose hu
  ext i j
  have hji : HopfAlgebra.antipode R (coefficientMatrix (C := C) b j i) =
      star (coefficientMatrix (C := C) b i j) := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hS j) i
  simp [hji]

variable [StarRing R] [StarModule R C] [StarCoalgebra R C]

/-- For a unitary coefficient matrix `u` over a Hopf star algebra, `(S²(u))ᵀ` is a right inverse
of the conjugate matrix `u.map star`. -/
theorem map_star_coefficientMatrix_mul_transpose_antipode_antipode (b : Basis ι R M)
    (hu : coefficientMatrix (C := C) b ∈ unitary (Matrix ι ι C)) :
    (coefficientMatrix (C := C) b).map star *
      ((coefficientMatrix (C := C) b).map
        (fun a ↦ HopfAlgebra.antipode R (HopfAlgebra.antipode R a)))ᵀ = 1 := by
  let _ : Comodule R C (ι → R) := b.conjugateMatrixComodule (C := C)
  have h := coefficientMatrix_mul_map_antipode (C := C) (Pi.basisFun R ι)
  rw [b.coefficientMatrix_conjugateMatrixComodule,
    b.map_antipode_map_star_coefficientMatrix hu] at h
  exact h

/-- For a unitary coefficient matrix `u` over a Hopf star algebra, `(S²(u))ᵀ` is a left inverse
of the conjugate matrix `u.map star`. -/
theorem transpose_antipode_antipode_mul_map_star_coefficientMatrix (b : Basis ι R M)
    (hu : coefficientMatrix (C := C) b ∈ unitary (Matrix ι ι C)) :
    ((coefficientMatrix (C := C) b).map
        (fun a ↦ HopfAlgebra.antipode R (HopfAlgebra.antipode R a)))ᵀ *
      (coefficientMatrix (C := C) b).map star = 1 := by
  let _ : Comodule R C (ι → R) := b.conjugateMatrixComodule (C := C)
  have h := map_antipode_mul_coefficientMatrix (C := C) (Pi.basisFun R ι)
  rw [b.coefficientMatrix_conjugateMatrixComodule,
    b.map_antipode_map_star_coefficientMatrix hu] at h
  exact h

end HopfUnitary

end Module.Basis
