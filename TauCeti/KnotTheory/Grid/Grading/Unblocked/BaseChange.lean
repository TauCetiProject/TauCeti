/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import TauCeti.KnotTheory.Grid.Grading.Unblocked.MonomialDegree

/-!
# Base change for the unblocked grid chain module `GC⁻`

Extending scalars from a commutative semiring `F` to an `F`-algebra `R` identifies `R ⊗[F] GC⁻(F)`
with `GC⁻(R)` (`GridChainMinus.baseChangeChainEquiv`), mapping polynomial coefficients along
`algebraMap F R` and scaling by the left tensor factor. The same scalar extension restricts to each
monomial-degree supported submodule (`GridChainMinus.baseChangeSupportedEquiv`), independently of
the base ring. Because it intertwines the unblocked differentials
(`GridDiagram.baseChangeChainEquiv_comp_baseChange_unblockedDifferential`), the cycle-finiteness
results in `TauCeti.KnotTheory.Grid.Grading.Unblocked.Finite` transfer from `ZMod 2` to every
commutative ring of characteristic two.

## Main definitions

* `TauCeti.GridChainMinus.baseChangeChainEquiv`: scalar extension of `GC⁻` along `F →+* R`.
* `TauCeti.GridChainMinus.baseChangeSupportedEquiv`: scalar extension of `monomialDegreeSupported`
  along `F →+* R`.

## Main results

* `TauCeti.GridChainMinus.baseChangeChainEquiv_tmul`,
  `TauCeti.GridChainMinus.baseChangeChainEquiv_symm_single_monomial`: evaluation of
  `baseChangeChainEquiv` on pure tensors and of its inverse on monomial generators.
* `TauCeti.GridChainMinus.baseChangeSupportedEquiv_tmul_basis`,
  `TauCeti.GridChainMinus.baseChangeSupportedEquiv_symm_basis`,
  `TauCeti.GridChainMinus.coe_baseChangeSupportedEquiv_apply`: evaluation of
  `baseChangeSupportedEquiv` and its inverse on basis elements, and compatibility with
  `baseChangeChainEquiv` under coercion to `GC⁻`.
* `TauCeti.GridDiagram.baseChangeChainEquiv_comp_baseChange_unblockedDifferential`: scalar
  extension on `GC⁻` intertwines the unblocked differentials.
-/

public section

namespace TauCeti

open MvPolynomial
open scoped TensorProduct

namespace GridChainMinus

section Semiring

variable (n : ℕ) (F R : Type*) [CommSemiring F] [CommSemiring R] [Algebra F R]

/-- Scalar extension of the unblocked chain module `GC⁻` along an algebra map `F →+* R`,
identifying `R ⊗[F] GC⁻(F)` with `GC⁻(R)` by mapping polynomial coefficients along `algebraMap F R`
and scaling by the left tensor factor. -/
noncomputable def baseChangeChainEquiv :
    R ⊗[F] GridChainMinus F n ≃ₗ[R] GridChainMinus R n :=
  (TensorProduct.finsuppRight F R R (MvPolynomial (Fin n) F) (GridState n)).trans
    (Finsupp.mapRange.linearEquiv (MvPolynomial.algebraTensorAlgEquiv F R).toLinearEquiv)

/-- Scalar extension on `GC⁻` sends a pure tensor `r ⊗ₜ[F] c` to `r` times the chain obtained by
mapping every polynomial coefficient along `algebraMap F R`. -/
@[simp]
theorem baseChangeChainEquiv_tmul {n : ℕ} {F R : Type*} [CommSemiring F] [CommSemiring R]
    [Algebra F R] (r : R) (c : GridChainMinus F n) :
    baseChangeChainEquiv n F R (r ⊗ₜ[F] c) =
      r • c.mapRange (MvPolynomial.map (algebraMap F R)) (map_zero _) := by
  ext x
  simp [baseChangeChainEquiv]

/-- The inverse scalar extension on `GC⁻` sends a monomial generator `V^e · x` over `R` to
`1 ⊗ₜ[F]` of the same generator over `F`. -/
@[simp]
theorem baseChangeChainEquiv_symm_single_monomial {n : ℕ} {F R : Type*} [CommSemiring F]
    [CommSemiring R] [Algebra F R] (x : GridState n) (e : Fin n →₀ ℕ) :
    (baseChangeChainEquiv n F R).symm (Finsupp.single x (monomial e 1) : GridChainMinus R n) =
      1 ⊗ₜ[F] (Finsupp.single x (monomial e 1) : GridChainMinus F n) := by
  simp [LinearEquiv.symm_apply_eq]

/-- Scalar extension of the supported submodule `monomialDegreeSupported F deg S` along an
algebra map `F →+* R`, sending each monomial basis element to the corresponding basis element over
`R`. -/
noncomputable def baseChangeSupportedEquiv {n : ℕ} (F R : Type*) [CommSemiring F] [CommSemiring R]
    [Algebra F R] {ι : Type*} (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι) :
    R ⊗[F] monomialDegreeSupported F deg S ≃ₗ[R] monomialDegreeSupported R deg S :=
  ((monomialDegreeSupportedBasis F deg S).baseChange R).equiv
    (monomialDegreeSupportedBasis R deg S) (Equiv.refl _)

/-- Scalar extension of a supported submodule sends `r ⊗ₜ[F]` of a supported basis element to
`r` times the corresponding supported basis element over `R`. -/
@[simp]
theorem baseChangeSupportedEquiv_tmul_basis {n : ℕ} {F R : Type*}
    [CommSemiring F] [CommSemiring R] [Algebra F R] {ι : Type*}
    (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι) (r : R)
    (i : {ix : Σ _ : GridState n, Fin n →₀ ℕ // deg ix.fst ix.snd ∈ S}) :
    baseChangeSupportedEquiv F R deg S (r ⊗ₜ[F] monomialDegreeSupportedBasis F deg S i) =
      r • monomialDegreeSupportedBasis R deg S i := by
  rw [show r ⊗ₜ[F] monomialDegreeSupportedBasis F deg S i =
      r • ((1 : R) ⊗ₜ[F] monomialDegreeSupportedBasis F deg S i) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul, baseChangeSupportedEquiv, ← Module.Basis.baseChange_apply,
    Module.Basis.equiv_apply, Equiv.refl_apply]

/-- The inverse scalar extension of a supported submodule sends a supported basis element over `R`
to `1 ⊗ₜ[F]` of the corresponding supported basis element over `F`. -/
@[simp]
theorem baseChangeSupportedEquiv_symm_basis {n : ℕ} {F R : Type*}
    [CommSemiring F] [CommSemiring R] [Algebra F R] {ι : Type*}
    (deg : GridState n → (Fin n →₀ ℕ) → ι) (S : Set ι)
    (i : {ix : Σ _ : GridState n, Fin n →₀ ℕ // deg ix.fst ix.snd ∈ S}) :
    (baseChangeSupportedEquiv F R deg S).symm (monomialDegreeSupportedBasis R deg S i) =
      1 ⊗ₜ[F] monomialDegreeSupportedBasis F deg S i := by
  simp [LinearEquiv.symm_apply_eq]

/-- Extending scalars on a supported submodule agrees with extending scalars on `GC⁻` under the
submodule inclusion. -/
theorem coe_baseChangeSupportedEquiv_comp_eq {n : ℕ} (F R : Type*) [CommSemiring F]
    [CommSemiring R] [Algebra F R] {ι : Type*} (deg : GridState n → (Fin n →₀ ℕ) → ι)
    (S : Set ι) :
    (monomialDegreeSupported R deg S).subtype.comp
        (baseChangeSupportedEquiv F R deg S).toLinearMap =
      (baseChangeChainEquiv n F R).toLinearMap.comp
        ((monomialDegreeSupported F deg S).subtype.baseChange R) := by
  refine ((monomialDegreeSupportedBasis F deg S).baseChange R).ext fun i ↦ ?_
  simp

/-- Coercing `baseChangeSupportedEquiv F R deg S x` into `GC⁻` agrees with applying
`baseChangeChainEquiv` to the inclusion of `x`. -/
@[simp]
theorem coe_baseChangeSupportedEquiv_apply {n : ℕ} {F R : Type*} [CommSemiring F]
    [CommSemiring R] [Algebra F R] {ι : Type*} (deg : GridState n → (Fin n →₀ ℕ) → ι)
    (S : Set ι) (x : R ⊗[F] monomialDegreeSupported F deg S) :
    ((baseChangeSupportedEquiv F R deg S x : monomialDegreeSupported R deg S) :
        GridChainMinus R n) =
      baseChangeChainEquiv n F R (((monomialDegreeSupported F deg S).subtype.baseChange R) x) :=
  LinearMap.congr_fun (coe_baseChangeSupportedEquiv_comp_eq F R deg S) x

end Semiring

end GridChainMinus

namespace GridDiagram

/-- Scalar extension on `GC⁻` intertwines the base-changed unblocked differential over `F` with
the unblocked differential over `R`. -/
theorem baseChangeChainEquiv_comp_baseChange_unblockedDifferential {n : ℕ} (G : GridDiagram n)
    (F R : Type*) [CommSemiring F] [CommSemiring R] [Algebra F R] :
    (GridChainMinus.baseChangeChainEquiv n F R).toLinearMap.comp
        (((G.unblockedDifferential F).restrictScalars F).baseChange R) =
      ((G.unblockedDifferential R).restrictScalars R).comp
        (GridChainMinus.baseChangeChainEquiv n F R).toLinearMap := by
  refine ((GridChainMinus.monomialChainBasis (n := n) F).baseChange R).ext fun i ↦ ?_
  simp

end GridDiagram

end TauCeti
