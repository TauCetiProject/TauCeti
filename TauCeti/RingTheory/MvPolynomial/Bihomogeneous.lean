/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import TauCeti.RingTheory.MvPolynomial.MultiHomogeneous
import TauCeti.RingTheory.MvPolynomial.Decomposition

/-!
# Tensor products of forms as bihomogeneous polynomials

The tensor square of a polynomial ring is the polynomial ring in two copies of its variables:
`MvPolynomial.tensorEquivFinTwoProd` identifies `R[X_ι] ⊗[R] R[X_ι]` with the polynomials in the
variables `X (h, i)` for `h : Fin 2` and `i : ι`, sending `p ⊗ q` to the product of `p` written in
the variables `X (0, i)` and `q` written in the variables `X (1, i)`. It is Mathlib's
`MvPolynomial.tensorEquivSum` followed by the relabelling `ι ⊕ ι ≃ Fin 2 × ι`.

Under this identification the tensor product of the forms of degree `m` with the forms of degree
`n` is the space of polynomials that are multihomogeneous of bidegree `(m, n)`, that is,
homogeneous of degree `m` in the first pair of variables and of degree `n` in the second
(`MvPolynomial.homogeneousTensorEquiv`, valued in `MvPolynomial.multiHomogeneousSubmodule`). For
two variables this is the classical model of the tensor product `Symᵐ(R²) ⊗ Symⁿ(R²)` of two
symmetric powers as bihomogeneous polynomials in two pairs of variables, in which the highest
weight vectors of the tensor product are explicit products of powers.

## Main definitions

* `MvPolynomial.tensorEquivFinTwoProd`: the algebra isomorphism
  `R[X_ι] ⊗[R] R[X_ι] ≃ₐ[R] R[X_(Fin 2 × ι)]`.
* `MvPolynomial.homogeneousTensorEquiv`: the linear isomorphism between the tensor product of the
  forms of degrees `m` and `n` and the polynomials that are multihomogeneous of bidegree `(m, n)`.

## Main results

* `MvPolynomial.tensorEquivFinTwoProd_tmul`: `p ⊗ q` goes to `p(X (0, ·)) * q(X (1, ·))`.
* `MvPolynomial.IsHomogeneous.isMultiHomogeneous_tensorEquivFinTwoProd_tmul`: the tensor product of
  forms of degrees `i` and `j` is multihomogeneous of bidegree `(i, j)`.
* `MvPolynomial.tensorEquivFinTwoProd_map_homogeneousComponent`: the identification intertwines
  the tensor product of two homogeneous components with the multihomogeneous component.
* `MvPolynomial.coe_homogeneousTensorEquiv_tmul`: the value of `homogeneousTensorEquiv` on a pure
  tensor.

## References

* P. Etingof, *Lie Groups and Lie Algebras*, arXiv:2201.09397v5, §11.4, pp. 62–65: tensor products
  of the representations of `SL₂` on binary forms.
-/

public section

open scoped TensorProduct

namespace MvPolynomial

section TensorEquiv

variable (ι R : Type*) [CommSemiring R]

/-- The tensor square of the polynomial ring `R[X_ι]` is the polynomial ring in the variables
`X (h, i)` for `h : Fin 2` and `i : ι`: the isomorphism sends `X i ⊗ 1` to `X (0, i)` and
`1 ⊗ X i` to `X (1, i)`. -/
noncomputable def tensorEquivFinTwoProd :
    MvPolynomial ι R ⊗[R] MvPolynomial ι R ≃ₐ[R] MvPolynomial (Fin 2 × ι) R :=
  (tensorEquivSum R ι ι R).trans
    (renameEquiv R ((Equiv.boolProdEquivSum ι).symm.trans (finTwoEquiv.symm.prodCongr (.refl ι))))

variable {ι R}

theorem tensorEquivFinTwoProd_X_tmul_one (i : ι) :
    tensorEquivFinTwoProd ι R (X i ⊗ₜ 1) = X (0, i) := by
  simp [tensorEquivFinTwoProd, finTwoEquiv]

theorem tensorEquivFinTwoProd_one_tmul_X (i : ι) :
    tensorEquivFinTwoProd ι R (1 ⊗ₜ X i) = X (1, i) := by
  simp [tensorEquivFinTwoProd, finTwoEquiv]

/-- `p ⊗ 1` goes to `p` written in the variables `X (0, i)`. -/
theorem tensorEquivFinTwoProd_tmul_one (p : MvPolynomial ι R) :
    tensorEquivFinTwoProd ι R (p ⊗ₜ 1) = rename (Prod.mk 0) p := by
  have : ((tensorEquivFinTwoProd ι R).toAlgHom.comp Algebra.TensorProduct.includeLeft :
      MvPolynomial ι R →ₐ[R] MvPolynomial (Fin 2 × ι) R) = rename (Prod.mk 0) := by
    ext i
    simp [tensorEquivFinTwoProd_X_tmul_one]
  exact congr($this p)

/-- `1 ⊗ q` goes to `q` written in the variables `X (1, i)`. -/
theorem tensorEquivFinTwoProd_one_tmul (q : MvPolynomial ι R) :
    tensorEquivFinTwoProd ι R (1 ⊗ₜ q) = rename (Prod.mk 1) q := by
  have : ((tensorEquivFinTwoProd ι R).toAlgHom.comp Algebra.TensorProduct.includeRight :
      MvPolynomial ι R →ₐ[R] MvPolynomial (Fin 2 × ι) R) = rename (Prod.mk 1) := by
    ext i
    simp [tensorEquivFinTwoProd_one_tmul_X]
  exact congr($this q)

/-- `p ⊗ q` goes to the product of `p` written in the variables `X (0, i)` and `q` written in the
variables `X (1, i)`. -/
@[simp]
theorem tensorEquivFinTwoProd_tmul (p q : MvPolynomial ι R) :
    tensorEquivFinTwoProd ι R (p ⊗ₜ q) = rename (Prod.mk 0) p * rename (Prod.mk 1) q := by
  rw [← tensorEquivFinTwoProd_tmul_one, ← tensorEquivFinTwoProd_one_tmul, ← map_mul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

@[simp]
theorem tensorEquivFinTwoProd_symm_X_zero (i : ι) :
    (tensorEquivFinTwoProd ι R).symm (X (0, i)) = X i ⊗ₜ 1 := by
  rw [AlgEquiv.symm_apply_eq, tensorEquivFinTwoProd_X_tmul_one]

@[simp]
theorem tensorEquivFinTwoProd_symm_X_one (i : ι) :
    (tensorEquivFinTwoProd ι R).symm (X (1, i)) = 1 ⊗ₜ X i := by
  rw [AlgEquiv.symm_apply_eq, tensorEquivFinTwoProd_one_tmul_X]

/-- The tensor product of a form of degree `i` and a form of degree `j` is multihomogeneous of
bidegree `(i, j)`. -/
theorem IsHomogeneous.isMultiHomogeneous_tensorEquivFinTwoProd_tmul {p q : MvPolynomial ι R}
    {i j : ℕ} (hp : p.IsHomogeneous i) (hq : q.IsHomogeneous j) :
    IsMultiHomogeneous ![i, j] (tensorEquivFinTwoProd ι R (p ⊗ₜ q)) := by
  have hd : (Pi.single 0 i + Pi.single 1 j : Fin 2 → ℕ) = ![i, j] := by
    ext h; fin_cases h <;> simp
  rw [tensorEquivFinTwoProd_tmul, ← hd]
  exact (hp.isMultiHomogeneous_rename 0).mul (hq.isMultiHomogeneous_rename 1)

/-- Taking the homogeneous components of degrees `m` and `n` of the two tensor factors
corresponds to taking the component that is homogeneous of degree `m` in the variables `X (0, i)`
and of degree `n` in the variables `X (1, i)`. -/
theorem tensorEquivFinTwoProd_map_homogeneousComponent (m n : ℕ)
    (x : MvPolynomial ι R ⊗[R] MvPolynomial ι R) :
    tensorEquivFinTwoProd ι R
        (TensorProduct.map (homogeneousComponent m) (homogeneousComponent n) x) =
      weightedHomogeneousComponent (fun p : Fin 2 × ι ↦ if p.1 = 0 then 1 else 0) m
        (weightedHomogeneousComponent (fun p : Fin 2 × ι ↦ if p.1 = 1 then 1 else 0) n
          (tensorEquivFinTwoProd ι R x)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p q =>
    rw [TensorProduct.map_tmul]
    induction p using MvPolynomial.induction_on' with
    | add p p' hp hp' => simp only [map_add, TensorProduct.add_tmul, hp, hp']
    | monomial a c =>
      induction q using MvPolynomial.induction_on' with
      | add q q' hq hq' => simp only [map_add, TensorProduct.tmul_add, hq, hq']
      | monomial b c' =>
        have H := IsHomogeneous.isMultiHomogeneous_tensorEquivFinTwoProd_tmul (ι := ι)
          (isHomogeneous_monomial (n := a.degree) c rfl)
          (isHomogeneous_monomial (n := b.degree) c' rfl)
        have H0 := H.isWeightedHomogeneous 0
        have H1 := H.isWeightedHomogeneous 1
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at H0 H1
        rw [homogeneousComponent_of_mem (isHomogeneous_monomial c rfl),
          homogeneousComponent_of_mem (isHomogeneous_monomial c' rfl),
          weightedHomogeneousComponent_of_mem H1]
        by_cases hn : n = b.degree <;> by_cases hm : m = a.degree <;>
          simp only [hn, hm, ↓reduceIte, TensorProduct.zero_tmul,
            TensorProduct.tmul_zero, map_zero, weightedHomogeneousComponent_of_mem H0]

attribute [local instance] MvPolynomial.decomposition

/-- The tensor product of the forms of degree `m` and of degree `n`, mapped into the polynomials
in two blocks of variables. -/
private noncomputable def homogeneousTensorMap (m n : ℕ) :
    homogeneousSubmodule ι R m ⊗[R] homogeneousSubmodule ι R n →ₗ[R]
      MvPolynomial (Fin 2 × ι) R :=
  (tensorEquivFinTwoProd ι R).toLinearMap ∘ₗ
    TensorProduct.map (homogeneousSubmodule ι R m).subtype (homogeneousSubmodule ι R n).subtype

private theorem homogeneousTensorMap_injective (m n : ℕ) :
    Function.Injective (homogeneousTensorMap (ι := ι) (R := R) m n) := by
  refine (tensorEquivFinTwoProd ι R).injective.comp (Function.LeftInverse.injective
    (g := TensorProduct.map (TauCeti.homogeneousProj (homogeneousSubmodule ι R) m)
      (TauCeti.homogeneousProj (homogeneousSubmodule ι R) n)) fun x ↦ ?_)
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, TauCeti.homogeneousProj_comp_subtype,
    TauCeti.homogeneousProj_comp_subtype, TensorProduct.map_id, LinearMap.id_apply]

private theorem range_homogeneousTensorMap (m n : ℕ) :
    LinearMap.range (homogeneousTensorMap (ι := ι) (R := R) m n) =
      multiHomogeneousSubmodule R ι ![m, n] := by
  apply le_antisymm
  · rw [LinearMap.range_le_iff_comap, eq_top_iff]
    rintro x -
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul p q =>
      simpa [homogeneousTensorMap] using
        p.property.isMultiHomogeneous_tensorEquivFinTwoProd_tmul q.property
  · intro P hP
    refine ⟨TensorProduct.map (TauCeti.homogeneousProj (homogeneousSubmodule ι R) m)
      (TauCeti.homogeneousProj (homogeneousSubmodule ι R) n)
      ((tensorEquivFinTwoProd ι R).symm P), ?_⟩
    rw [homogeneousTensorMap, LinearMap.comp_apply, ← LinearMap.comp_apply (TensorProduct.map _ _),
      ← TensorProduct.map_comp, subtype_comp_homogeneousProj, subtype_comp_homogeneousProj,
      AlgEquiv.toLinearMap_apply, tensorEquivFinTwoProd_map_homogeneousComponent,
      AlgEquiv.apply_symm_apply]
    have h0 := (mem_multiHomogeneousSubmodule.mp hP).isWeightedHomogeneous 0
    have h1 := (mem_multiHomogeneousSubmodule.mp hP).isWeightedHomogeneous 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    simp only [weightedHomogeneousComponent_of_mem h1, weightedHomogeneousComponent_of_mem h0,
      ↓reduceIte]

variable (ι R)

/-- **Tensor products of forms are bihomogeneous polynomials.** The tensor product of the forms of
degree `m` with the forms of degree `n` in the variables `X_ι` is isomorphic to the polynomials in
the variables `X (h, i)` (`h : Fin 2`, `i : ι`) that are homogeneous of degree `m` in the variables
`X (0, i)` and of degree `n` in the variables `X (1, i)`. -/
noncomputable def homogeneousTensorEquiv (m n : ℕ) :
    homogeneousSubmodule ι R m ⊗[R] homogeneousSubmodule ι R n ≃ₗ[R]
      multiHomogeneousSubmodule R ι ![m, n] :=
  (LinearEquiv.ofInjective _ (homogeneousTensorMap_injective m n)).trans
    (LinearEquiv.ofEq _ _ (range_homogeneousTensorMap m n))

variable {ι R}

/-- `homogeneousTensorEquiv` is the restriction of `tensorEquivFinTwoProd`. -/
theorem coe_homogeneousTensorEquiv_apply (m n : ℕ)
    (x : homogeneousSubmodule ι R m ⊗[R] homogeneousSubmodule ι R n) :
    (homogeneousTensorEquiv ι R m n x : MvPolynomial (Fin 2 × ι) R) =
      tensorEquivFinTwoProd ι R (TensorProduct.map (homogeneousSubmodule ι R m).subtype
        (homogeneousSubmodule ι R n).subtype x) := by
  rw [homogeneousTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply, homogeneousTensorMap, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply]

@[simp]
theorem coe_homogeneousTensorEquiv_tmul {m n : ℕ} (p : homogeneousSubmodule ι R m)
    (q : homogeneousSubmodule ι R n) :
    (homogeneousTensorEquiv ι R m n (p ⊗ₜ q) : MvPolynomial (Fin 2 × ι) R) =
      rename (Prod.mk 0) (p : MvPolynomial ι R) * rename (Prod.mk 1) (q : MvPolynomial ι R) := by
  rw [coe_homogeneousTensorEquiv_apply, TensorProduct.map_tmul, tensorEquivFinTwoProd_tmul,
    Submodule.subtype_apply, Submodule.subtype_apply]

end TensorEquiv

end MvPolynomial
