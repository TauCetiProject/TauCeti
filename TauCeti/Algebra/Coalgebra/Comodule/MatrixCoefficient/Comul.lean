/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Basic

/-!
# Comultiplication of matrix coefficients

The comultiplication of a matrix coefficient is controlled by the coaction:

```text
Δ(c(φ, m)) = (c(φ, ·) ⊗ id)(ρ(m)).
```

For a basis `(eᵢ)`, expanding the coaction in that basis gives the familiar formula

```text
Δ(c(φ, m)) = ∑ᶠ i, c(φ, eᵢ) ⊗ c(eⁱ, m),
```

a finite sum since only finitely many `c(eⁱ, m)` are nonzero. Both formulas are basic facts
about matrix coefficients; the basis expansion is what makes the coefficient submodule of a free
comodule stable under comultiplication in
`TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Subcoalgebra`.

## Main declarations

* `TauCeti.Comodule.comul_matrixCoefficient`: the basis-free comultiplication formula.
* `TauCeti.Comodule.comul_matrixCoefficient_eq_finsum`: its expansion in a basis, and
  `TauCeti.Comodule.comul_matrixCoefficient_eq_sum` for a finite basis.
* `TauCeti.Comodule.coact_eq_finsum_basis_matrixCoefficient`: the expansion of the coaction
  itself in a basis, and `TauCeti.Comodule.coact_eq_sum_basis_matrixCoefficient` for a finite
  basis.

## References

This is the standard coefficient-coalgebra computation; see Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct
open TensorProduct Module

namespace TauCeti.Comodule

universe u v w x

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- Comultiplication of a matrix coefficient is obtained by applying its coefficient map to
the vector factor of the coaction. -/
@[simp]
theorem comul_matrixCoefficient (φ : Module.Dual R M) (m : M) :
    Coalgebra.comul (R := R) (A := C)
        (matrixCoefficient (R := R) (C := C) φ m) =
      TensorProduct.map
        (matrixCoefficientLinear (R := R) (C := C) φ) LinearMap.id
        (coact (R := R) (C := C) (M := M) m) := by
  -- Expose matrix coefficients as composite linear maps so `coassoc_simps` can rewrite
  -- coassociativity without tensor induction.
  change (Coalgebra.comul ∘ₗ (TensorProduct.lid R C).toLinearMap ∘ₗ
          TensorProduct.map φ LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := M)) m =
        (TensorProduct.map
            ((TensorProduct.lid R C).toLinearMap ∘ₗ
              TensorProduct.map φ LinearMap.id ∘ₗ
              coact (R := R) (C := C) (M := M))
            LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := M)) m
  apply LinearMap.congr_fun ?_ m
  calc
    _ = (TensorProduct.lid R (C ⊗[R] C)).toLinearMap ∘ₗ
        TensorProduct.map φ LinearMap.id ∘ₗ
        TensorProduct.map LinearMap.id Coalgebra.comul ∘ₗ
        coact (R := R) (C := C) (M := M) := by
          simp only [coassoc_simps]
    _ = (TensorProduct.lid R (C ⊗[R] C)).toLinearMap ∘ₗ
        TensorProduct.map φ LinearMap.id ∘ₗ
        (TensorProduct.assoc R M C C).toLinearMap ∘ₗ
        TensorProduct.map (coact (R := R) (C := C) (M := M)) LinearMap.id ∘ₗ
        coact (R := R) (C := C) (M := M) := by
          simpa only [coassoc_simps] using congrArg
            (fun f : M →ₗ[R] M ⊗[R] (C ⊗[R] C) =>
              (TensorProduct.lid R (C ⊗[R] C)).toLinearMap ∘ₗ
                TensorProduct.map φ LinearMap.id ∘ₗ f)
            (coact_coassoc (R := R) (C := C) (M := M)).symm
    _ = TensorProduct.map
          ((TensorProduct.lid R C).toLinearMap ∘ₗ
            TensorProduct.map φ LinearMap.id)
          LinearMap.id ∘ₗ
        TensorProduct.map (coact (R := R) (C := C) (M := M)) LinearMap.id ∘ₗ
        coact (R := R) (C := C) (M := M) := by
          simp only [TensorProduct.lid_tensor, coassoc_simps]
    _ = _ := by
      simp only [coassoc_simps]

omit [Coalgebra R C] [Comodule R C M] in
/-- The `i`-th coordinate of a tensor in `M ⊗ C`, for a basis of `M`, is its contraction
against the `i`-th coordinate functional. -/
private theorem equivFinsuppOfBasisLeft_apply_eq_lid {ι : Type x} [DecidableEq ι] (b : Basis ι R M)
    (x : M ⊗[R] C) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft (N := C) b x i =
      TensorProduct.lid R C (TensorProduct.map (b.coord i) LinearMap.id x) := by
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply]
  simp only [LinearMap.rTensor]

omit [Coalgebra R C] [Comodule R C M] in
/-- A family of tensors `vᵢ ⊗ fᵢ` vanishes wherever its right factors do. -/
private theorem support_tmul_subset {ι : Type x} (v : ι → M) (f : ι → C) :
    Function.support (fun i => v i ⊗ₜ[R] f i) ⊆ Function.support f :=
  Function.support_subset_iff'.2 fun i hi => by
    rw [Function.notMem_support.1 hi, TensorProduct.tmul_zero]

omit [Coalgebra R C] [Comodule R C M] in
private theorem tensor_eq_finsum_basis_tmul {ι : Type x} (b : Basis ι R M) (x : M ⊗[R] C) :
    x =
      ∑ᶠ i, b i ⊗ₜ[R]
        TensorProduct.lid R C
          (TensorProduct.map (b.coord i) LinearMap.id x) := by
  classical
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := C) b
  calc
    x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = ∑ i ∈ (e x).support, b i ⊗ₜ[R] (e x i) :=
      TensorProduct.equivFinsuppOfBasisLeft_symm_apply b (e x)
    _ = ∑ᶠ i, b i ⊗ₜ[R] (e x i) :=
      (finsum_eq_sum_of_support_subset _
        ((support_tmul_subset _ _).trans (Finsupp.fun_support_eq _).subset)).symm
    _ = _ := by simp only [e, equivFinsuppOfBasisLeft_apply_eq_lid]

/-- For a basis `(eᵢ)`, only finitely many matrix coefficients `c(eⁱ, m)` are nonzero. -/
theorem finite_support_matrixCoefficient_coord {ι : Type x} (b : Basis ι R M) (m : M) :
    (Function.support fun i =>
      matrixCoefficient (R := R) (C := C) (b.coord i) m).Finite := by
  classical
  have h : (fun i => matrixCoefficient (R := R) (C := C) (b.coord i) m) =
      ⇑(TensorProduct.equivFinsuppOfBasisLeft (N := C) b (coact (R := R) (C := C) (M := M) m)) :=
    funext fun i => by rw [equivFinsuppOfBasisLeft_apply_eq_lid, matrixCoefficient_def]
  rw [h, Finsupp.fun_support_eq]
  exact Finset.finite_toSet _

/-- The coaction of a comodule with a basis `(eᵢ)` expands as the finite sum
`ρ(m) = ∑ᶠ i, eᵢ ⊗ c(eⁱ, m)` in matrix coefficients. -/
theorem coact_eq_finsum_basis_matrixCoefficient {ι : Type x} (b : Basis ι R M) (m : M) :
    coact (R := R) (C := C) (M := M) m =
      ∑ᶠ i, b i ⊗ₜ[R]
        matrixCoefficient (R := R) (C := C) (b.coord i) m := by
  simpa only [matrixCoefficient_def] using
    tensor_eq_finsum_basis_tmul (C := C) b
      (coact (R := R) (C := C) (M := M) m)

/-- The coaction of a comodule with a finite basis `(eᵢ)` expands as
`ρ(m) = ∑ i, eᵢ ⊗ c(eⁱ, m)` in matrix coefficients. -/
theorem coact_eq_sum_basis_matrixCoefficient {ι : Type x} [Fintype ι] (b : Basis ι R M) (m : M) :
    coact (R := R) (C := C) (M := M) m =
      ∑ i, b i ⊗ₜ[R]
        matrixCoefficient (R := R) (C := C) (b.coord i) m := by
  rw [coact_eq_finsum_basis_matrixCoefficient (C := C) b, finsum_eq_sum_of_fintype]

/-- The comultiplication of a matrix coefficient, expanded in a basis as a finite sum. -/
theorem comul_matrixCoefficient_eq_finsum {ι : Type x}
    (b : Basis ι R M) (φ : Module.Dual R M) (m : M) :
    Coalgebra.comul (R := R) (A := C)
        (matrixCoefficient (R := R) (C := C) φ m) =
      ∑ᶠ i, matrixCoefficient (R := R) (C := C) φ (b i) ⊗ₜ[R]
        matrixCoefficient (R := R) (C := C) (b.coord i) m := by
  rw [comul_matrixCoefficient, coact_eq_finsum_basis_matrixCoefficient (C := C) b,
    map_finsum _ ((finite_support_matrixCoefficient_coord (C := C) b m).subset
      (support_tmul_subset _ _))]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply,
    matrixCoefficientLinear_apply]

/-- The comultiplication of a matrix coefficient, expanded in a finite basis. -/
theorem comul_matrixCoefficient_eq_sum {ι : Type x} [Fintype ι]
    (b : Basis ι R M) (φ : Module.Dual R M) (m : M) :
    Coalgebra.comul (R := R) (A := C)
        (matrixCoefficient (R := R) (C := C) φ m) =
      ∑ i, matrixCoefficient (R := R) (C := C) φ (b i) ⊗ₜ[R]
        matrixCoefficient (R := R) (C := C) (b.coord i) m := by
  rw [comul_matrixCoefficient_eq_finsum (C := C) b, finsum_eq_sum_of_fintype]

end TauCeti.Comodule
