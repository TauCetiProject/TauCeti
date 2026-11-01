/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.RingTheory.Morita.ModuleEnd

import TauCeti.LinearAlgebra.Eigenspace.TensorProduct

/-!
# Eigenspaces of modules over an algebra acting on `S` as all of `End S`

Let `k` be a commutative ring and `A` a `k`-algebra acting on a finite projective `k`-module `S`
as the whole endomorphism algebra `End_k S`. Every `A`-module `M` is then `S` tensored with its
multiplicity space, by the evaluation isomorphism
`TauCeti.isotypicTensorEquivOfBijective : S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] M`. An element `a ∈ A` acts on
`S ⊗[k] X` through the left factor, as `(a • ·) ⊗ id`
(`TensorProduct.AlgebraTensorModule.smul_eq_lsmul_rTensor`), so its eigenspaces in `M` are read
off from its eigenspaces in `S`: evaluation restricts to an isomorphism

`Eig(a, μ; S) ⊗[k] (S →ₗ[A] M) ≃ₗ[k] Eig(a, μ; M)`,  `s ⊗ T ↦ T s`,

whenever the multiplicity space `S →ₗ[A] M` is flat over `k`, for instance whenever `k` is a
field. Flatness is what makes the kernel of `(a - μ) ⊗ id` the image of `ker (a - μ) ⊗ X`, and it
cannot be dropped: for `A = S = k` and a non-zero-divisor `r ∈ k`, the `0`-eigenspace of `r` is
zero in `S` but is the `r`-torsion of `M`. The flat exactness statement is
`Module.End.exact_rTensor_eigenspace`.

The case in view is the spinor module `S` of an even-dimensional complex Clifford algebra, where
`a` is the chirality element: the eigenspaces of an arbitrary Clifford module `E` are then
`S⁺ ⊗ Hom_Cl(S, E)` and `S⁻ ⊗ Hom_Cl(S, E)`.

## Main definitions

* `TauCeti.eigenspaceTensorEquivOfBijective`: evaluation
  `Eig(a, μ; S) ⊗[k] (S →ₗ[A] M) ≃ₗ[k] Eig(a, μ; M)`.

## Main results

* `TauCeti.coe_eigenspaceTensorEquivOfBijective_tmul`: the equivalence is `s ⊗ T ↦ T s`.
* `TauCeti.finrank_eigenspace_eq_finrank_mul_finrank_linearMap_of_bijective_lsmul`: over a field,
  `dim Eig(a, μ; M) = dim Eig(a, μ; S) · dim (S →ₗ[A] M)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

namespace TauCeti

open Module TensorProduct

section CommRing

variable {k A S M : Type*} [CommRing k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable (h : Function.Bijective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))

variable [Module.Finite k S] [Module.Projective k S] [Module.Flat k (S →ₗ[A] M)]

/-- Evaluation restricted to the `μ`-eigenspace of `a` on `S`, tensored with the multiplicity
space. -/
private noncomputable def eigenspaceEval (a : A) (μ : k) :
    (Algebra.lsmul k k S a).eigenspace μ ⊗[k] (S →ₗ[A] M) →ₗ[k] M :=
  ((isotypicTensorEquivOfBijective h).restrictScalars k).toLinearMap ∘ₗ
    ((Algebra.lsmul k k S a).eigenspace μ).subtype.rTensor (S →ₗ[A] M)

private theorem eigenspaceEval_injective (a : A) (μ : k) :
    Function.Injective (eigenspaceEval (M := M) h a μ) :=
  ((isotypicTensorEquivOfBijective h).restrictScalars k).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _))

private theorem range_eigenspaceEval (a : A) (μ : k) :
    LinearMap.range (eigenspaceEval (M := M) h a μ) = (Algebra.lsmul k k M a).eigenspace μ := by
  set e := (isotypicTensorEquivOfBijective h (M := M)).restrictScalars k
  ext y
  rw [eigenspaceEval, LinearMap.range_comp, Submodule.mem_map_equiv,
    ← (Module.End.exact_rTensor_eigenspace _ μ (S →ₗ[A] M)).linearMap_ker_eq, LinearMap.mem_ker,
    rTensor_lsmul_sub_smul_apply, Module.End.mem_eigenspace_iff, Algebra.lsmul_coe]
  -- `e⁻¹` is linear for both `A` and `k`, so it carries `a • y - μ • y` to the same expression.
  have he : a • e.symm y - μ • e.symm y = e.symm (a • y - μ • y) := by
    have ha : e.symm (a • y) = a • e.symm y := (isotypicTensorEquivOfBijective h).symm.map_smul a y
    rw [map_sub, ha, map_smul]
  rw [he, LinearEquiv.map_eq_zero_iff, sub_eq_zero]

/-- **Eigenspaces through the Morita evaluation.** When `A` acts on the finite projective module
`S` as all of `End_k S`, evaluation `s ⊗ T ↦ T s` identifies the `μ`-eigenspace of `a ∈ A` on
`M` with the `μ`-eigenspace of `a` on `S` tensored with the multiplicity space `S →ₗ[A] M`, as
long as the latter is flat over `k`. -/
noncomputable def eigenspaceTensorEquivOfBijective (a : A) (μ : k) :
    (Algebra.lsmul k k S a).eigenspace μ ⊗[k] (S →ₗ[A] M) ≃ₗ[k]
      (Algebra.lsmul k k M a).eigenspace μ :=
  (LinearEquiv.ofInjective _ (eigenspaceEval_injective h a μ)).trans
    (LinearEquiv.ofEq _ _ (range_eigenspaceEval h a μ))

/-- The eigenspace equivalence is evaluation, `s ⊗ T ↦ T s`. -/
@[simp]
theorem coe_eigenspaceTensorEquivOfBijective_tmul (a : A) (μ : k)
    (s : (Algebra.lsmul k k S a).eigenspace μ) (T : S →ₗ[A] M) :
    (eigenspaceTensorEquivOfBijective h a μ (s ⊗ₜ T) : M) = T s := by
  rw [eigenspaceTensorEquivOfBijective, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply]
  simp [eigenspaceEval]

end CommRing

section Field

variable {k A S M : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [FiniteDimensional k S]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- **The dimension of an eigenspace of a module over `A ≅ End_k S`** is the dimension of the
corresponding eigenspace on `S` times that of the multiplicity space. -/
theorem finrank_eigenspace_eq_finrank_mul_finrank_linearMap_of_bijective_lsmul
    (h : Function.Bijective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S)) (a : A) (μ : k) :
    finrank k ((Algebra.lsmul k k M a).eigenspace μ) =
      finrank k ((Algebra.lsmul k k S a).eigenspace μ) * finrank k (S →ₗ[A] M) := by
  rw [← (eigenspaceTensorEquivOfBijective h a μ).finrank_eq, finrank_tensorProduct]

end Field

end TauCeti
