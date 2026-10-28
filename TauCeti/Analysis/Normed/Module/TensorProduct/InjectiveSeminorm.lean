/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Module.TensorProduct.ProjectiveSeminorm

/-!
# The injective seminorm on a binary tensor product

A tensor `u : E ⊗[𝕜] F` defines a bounded operator `StrongDual 𝕜 E →L[𝕜] F`, sending `f` to
`∑ i, f (x i) • y i` for any decomposition `u = ∑ i, x i ⊗ₜ y i`. The injective seminorm of `u`
is the operator norm of this map. Over `ℝ` and `ℂ` it is the supremum of
`‖∑ i, f (x i) * g (y i)‖` over continuous linear functionals `f` on `E` and `g` on `F` of norm
at most one, which is the classical definition of the injective norm.

This file proves that the injective seminorm is bounded by the projective seminorm. Over `ℝ`
and `ℂ`, both agree with `‖x‖ * ‖y‖` on a pure tensor `x ⊗ₜ y` and are norms when `E` and `F`
are normed spaces. Definiteness follows, via Hahn–Banach, from the injectivity of the map from
tensors to operators on the dual.

The type `TauCeti.InjectiveTensor 𝕜 E F` is a copy of `E ⊗[𝕜] F` carrying the injective
seminorm, and the identity of the underlying tensors is a contraction from
`TauCeti.ProjectiveTensor 𝕜 E F` to it.

Mathlib's `PiTensorProduct.injectiveSeminorm` is a different seminorm on finite
families of factors, defined by duality against all normed target spaces rather than against the
scalar field; it is not the classical injective norm used here.

## Main definitions

* `TensorProduct.contractStrongDual 𝕜 E F`: the bounded operator on the dual of `E` induced by
  a tensor.
* `TensorProduct.injectiveSeminorm 𝕜 E F`: the injective seminorm on `E ⊗[𝕜] F`.
* `TauCeti.InjectiveTensor 𝕜 E F`: the algebraic tensor product with the injective seminorm.
* `TauCeti.ProjectiveTensor.toInjectiveTensor`: the contraction from the projective to the
  injective tensor product.

## Main results

* `TensorProduct.injectiveSeminorm_le_projectiveSeminorm`: `ε ≤ π`.
* `TensorProduct.injectiveSeminorm_le_iff_forall_norm_le_one`: the classical
  description of the injective seminorm over `ℝ` and `ℂ`.
* `TensorProduct.injectiveSeminorm_tmul` and
  `TensorProduct.projectiveSeminorm_tmul`: both seminorms are cross norms.
* `TensorProduct.contractStrongDual_injective`: over `ℝ` and `ℂ`, a tensor is determined by the
  operator it induces on the dual of a normed left factor.
* `TensorProduct.injectiveSeminorm_eq_zero_iff` and
  `TensorProduct.projectiveSeminorm_eq_zero_iff`: both seminorms are definite.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, §§2.1, 3.1.
-/

public section

open scoped TensorProduct

namespace TensorProduct

section NontriviallyNormedField

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The bounded operator `StrongDual 𝕜 E →L[𝕜] F` induced by a tensor in `E ⊗[𝕜] F`: the pure
tensor `x ⊗ₜ y` gives `f ↦ f x • y`. -/
noncomputable def contractStrongDual : E ⊗[𝕜] F →ₗ[𝕜] StrongDual 𝕜 E →L[𝕜] F :=
  _root_.TensorProduct.lift
    ((ContinuousLinearMap.smulRightLₗ 𝕜 (StrongDual 𝕜 E) F).comp
      (NormedSpace.inclusionInDoubleDual 𝕜 E).toLinearMap)

variable {𝕜 E F}

/-- The operator induced by `x ⊗ₜ y` sends `f` to `f x • y`. -/
@[simp]
theorem contractStrongDual_tmul (x : E) (y : F) (f : StrongDual 𝕜 E) :
    contractStrongDual 𝕜 E F (x ⊗ₜ y) f = f x • y := by
  simp [contractStrongDual]

/-- The operator induced by a tensor sends `f` to the image of the tensor under `f ⊗ id`,
followed by `𝕜 ⊗[𝕜] F ≃ F`. -/
theorem contractStrongDual_apply (u : E ⊗[𝕜] F) (f : StrongDual 𝕜 E) :
    contractStrongDual 𝕜 E F u f =
      _root_.TensorProduct.lid 𝕜 F ((f : E →ₗ[𝕜] 𝕜).rTensor F u) := by
  induction u with
  | tmul x y => simp
  | add u v hu hv => simp [hu, hv]

variable (𝕜 E F) in
/-- The **injective seminorm** on `E ⊗[𝕜] F`: the operator norm of the operator on the dual of
`E` induced by a tensor. Over `ℝ` and `ℂ` it is the supremum of `‖∑ i, f (x i) * g (y i)‖` over
continuous linear functionals `f` and `g` of norm at most one, for any decomposition
`u = ∑ i, x i ⊗ₜ y i`; see `injectiveSeminorm_le_iff_forall_norm_le_one`. -/
noncomputable def injectiveSeminorm : Seminorm 𝕜 (E ⊗[𝕜] F) :=
  (normSeminorm 𝕜 (StrongDual 𝕜 E →L[𝕜] F)).comp (contractStrongDual 𝕜 E F)

/-- The injective seminorm is the operator norm of the induced operator on the dual. -/
theorem injectiveSeminorm_apply (u : E ⊗[𝕜] F) :
    injectiveSeminorm 𝕜 E F u = ‖contractStrongDual 𝕜 E F u‖ :=
  (rfl)

/-- The operator induced by a tensor is bounded by its injective seminorm. -/
theorem norm_contractStrongDual_apply_le (u : E ⊗[𝕜] F) (f : StrongDual 𝕜 E) :
    ‖contractStrongDual 𝕜 E F u f‖ ≤ injectiveSeminorm 𝕜 E F u * ‖f‖ :=
  (contractStrongDual 𝕜 E F u).le_opNorm f

/-- On a pure tensor `x ⊗ₜ y`, the injective seminorm is the norm of `x` in the double dual
times the norm of `y`. -/
private theorem injectiveSeminorm_tmul_eq (x : E) (y : F) :
    injectiveSeminorm 𝕜 E F (x ⊗ₜ y) = ‖NormedSpace.inclusionInDoubleDual 𝕜 E x‖ * ‖y‖ := by
  rw [injectiveSeminorm_apply]
  have h : contractStrongDual 𝕜 E F (x ⊗ₜ y) =
      ContinuousLinearMap.smulRight (NormedSpace.inclusionInDoubleDual 𝕜 E x) y := by
    ext f
    simp only [contractStrongDual_tmul, ContinuousLinearMap.smulRight_apply, NormedSpace.dual_def]
  rw [h, ContinuousLinearMap.norm_smulRight_apply]

/-- The injective seminorm of a pure tensor is at most the product of the norms. -/
theorem injectiveSeminorm_tmul_le (x : E) (y : F) :
    injectiveSeminorm 𝕜 E F (x ⊗ₜ y) ≤ ‖x‖ * ‖y‖ := by
  rw [injectiveSeminorm_tmul_eq]
  gcongr
  exact NormedSpace.double_dual_bound 𝕜 E x

/-- The injective seminorm is bounded by the projective seminorm. -/
theorem injectiveSeminorm_le_projectiveSeminorm :
    injectiveSeminorm 𝕜 E F ≤ projectiveSeminorm 𝕜 E F :=
  le_projectiveSeminorm injectiveSeminorm_tmul_le

end NontriviallyNormedField

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
  [NormedSpace 𝕜 F]

/-- Over `ℝ` and `ℂ`, the injective seminorm is the supremum of
`‖g (contractStrongDual 𝕜 E F u f)‖ = ‖∑ i, f (x i) * g (y i)‖` over the closed unit balls of
the duals of `E` and `F`. -/
theorem injectiveSeminorm_le_iff_forall_norm_le_one {u : E ⊗[𝕜] F} {C : ℝ} (hC : 0 ≤ C) :
    injectiveSeminorm 𝕜 E F u ≤ C ↔
      ∀ (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F), ‖f‖ ≤ 1 → ‖g‖ ≤ 1 →
        ‖g (contractStrongDual 𝕜 E F u f)‖ ≤ C := by
  refine ⟨fun h f g hf hg ↦ ?_, fun h ↦ ?_⟩
  · calc ‖g (contractStrongDual 𝕜 E F u f)‖ ≤ ‖g‖ * (injectiveSeminorm 𝕜 E F u * ‖f‖) :=
          g.le_of_opNorm_le_of_le le_rfl (norm_contractStrongDual_apply_le u f)
      _ ≤ 1 * (C * 1) := by gcongr
      _ = C := by ring
  · rw [injectiveSeminorm_apply]
    refine ContinuousLinearMap.opNorm_le_of_unit_norm hC fun f hf ↦ ?_
    have hev : ‖NormedSpace.inclusionInDoubleDual 𝕜 F (contractStrongDual 𝕜 E F u f)‖ ≤ C :=
      ContinuousLinearMap.opNorm_le_of_unit_norm hC fun g hg ↦ by
        rw [NormedSpace.dual_def]
        exact h f g hf.le hg.le
    refine NormedSpace.norm_le_dual_bound 𝕜 _ hC fun g ↦ ?_
    simpa only [NormedSpace.dual_def] using ContinuousLinearMap.le_of_opNorm_le _ hev g

/-- The injective seminorm is a cross norm: its value on `x ⊗ₜ y` is `‖x‖ * ‖y‖`. -/
@[simp]
theorem injectiveSeminorm_tmul (x : E) (y : F) :
    injectiveSeminorm 𝕜 E F (x ⊗ₜ y) = ‖x‖ * ‖y‖ := by
  -- `inclusionInDoubleDualLi 𝕜 x` is `inclusionInDoubleDual 𝕜 E x` bundled as an isometry.
  rw [injectiveSeminorm_tmul_eq]
  exact congrArg (· * ‖y‖) ((NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map x)

/-- The projective seminorm is a cross norm: its value on `x ⊗ₜ y` is `‖x‖ * ‖y‖`. -/
@[simp]
theorem projectiveSeminorm_tmul (x : E) (y : F) :
    projectiveSeminorm 𝕜 E F (x ⊗ₜ y) = ‖x‖ * ‖y‖ :=
  le_antisymm (projectiveSeminorm_tmul_le x y)
    ((injectiveSeminorm_tmul x y).symm.le.trans (injectiveSeminorm_le_projectiveSeminorm _))

end Seminormed

/-- Over `ℝ` and `ℂ`, a tensor whose left factor is a normed space is determined by the operator
it induces on the dual of that factor. -/
theorem contractStrongDual_injective [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    Function.Injective (contractStrongDual 𝕜 E F) := by
  -- The tensor lies in `E₀ ⊗[𝕜] F` for a finite-dimensional subspace `E₀ ≤ E`; its coordinates
  -- in a basis of `E₀` are recovered by Hahn–Banach extensions of the coordinate functionals.
  refine (injective_iff_map_eq_zero _).2 fun u hu ↦ ?_
  obtain ⟨E₀, _, hE₀⟩ := _root_.TensorProduct.exists_finite_submodule_left_of_setFinite
    {u} (Set.finite_singleton u)
  obtain ⟨u₀, rfl⟩ := hE₀ rfl
  let b := Module.finBasis 𝕜 E₀
  suffices u₀ = 0 by simp [this]
  refine (_root_.TensorProduct.equivFinsuppOfBasisLeft b).injective (Finsupp.ext fun i ↦ ?_)
  rw [_root_.TensorProduct.equivFinsuppOfBasisLeft_apply, map_zero, Finsupp.coe_zero,
    Pi.zero_apply]
  -- Extend the `i`-th coordinate functional of `E₀` to `E` by the Hahn–Banach theorem.
  obtain ⟨f, hf, -⟩ := exists_extension_norm_eq E₀ (LinearMap.toContinuousLinearMap (b.coord i))
  have hcoord : b.coord i = (f : E →ₗ[𝕜] 𝕜) ∘ₗ E₀.subtype := by
    ext x
    simp [hf]
  rw [hcoord, LinearMap.rTensor_comp_apply, ← contractStrongDual_apply, hu, zero_apply]

section Normed

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over `ℝ` and `ℂ`, the injective seminorm on a tensor product of normed spaces is definite. -/
@[simp]
theorem injectiveSeminorm_eq_zero_iff {u : E ⊗[𝕜] F} : injectiveSeminorm 𝕜 E F u = 0 ↔ u = 0 := by
  rw [injectiveSeminorm_apply, ContinuousLinearMap.opNorm_zero_iff,
    contractStrongDual_injective.eq_iff' (map_zero _)]

/-- Over `ℝ` and `ℂ`, the projective seminorm on a tensor product of normed spaces is
definite. -/
@[simp]
theorem projectiveSeminorm_eq_zero_iff {u : E ⊗[𝕜] F} :
    projectiveSeminorm 𝕜 E F u = 0 ↔ u = 0 := by
  refine ⟨fun h ↦ injectiveSeminorm_eq_zero_iff.1 ?_, fun h ↦ h ▸ map_zero _⟩
  exact le_antisymm (h ▸ injectiveSeminorm_le_projectiveSeminorm u) (apply_nonneg _ _)

end Normed

end RCLike

end TensorProduct

namespace TauCeti

section InjectiveTensor

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The algebraic tensor product `E ⊗[𝕜] F` carrying the injective seminorm.

This wrapper distinguishes the injective seminorm from other norms on the same algebraic tensor
product, such as the projective norm or the Hilbert-space norm of inner product spaces. -/
structure InjectiveTensor where
  /-- The underlying element of the algebraic tensor product. -/
  toTensorProduct : E ⊗[𝕜] F

namespace InjectiveTensor

/-- Forget the injective seminorm. -/
def equiv : InjectiveTensor 𝕜 E F ≃ E ⊗[𝕜] F where
  toFun := toTensorProduct
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (InjectiveTensor 𝕜 E F) := (equiv 𝕜 E F).addCommGroup

/-- Forget the injective seminorm and retain the additive structure. -/
def addEquiv : InjectiveTensor 𝕜 E F ≃+ E ⊗[𝕜] F where
  toEquiv := equiv 𝕜 E F
  map_add' _ _ := rfl

instance : Module 𝕜 (InjectiveTensor 𝕜 E F) := (addEquiv 𝕜 E F).module 𝕜

/-- The injective tensor product is linearly equivalent to the algebraic tensor product. -/
def linearEquiv : InjectiveTensor 𝕜 E F ≃ₗ[𝕜] E ⊗[𝕜] F where
  toAddEquiv := addEquiv 𝕜 E F
  map_smul' _ _ := rfl

variable {𝕜 E F}

/-- The equivalence with `E ⊗[𝕜] F` forgets the wrapper. -/
@[simp]
theorem equiv_apply (u : InjectiveTensor 𝕜 E F) : equiv 𝕜 E F u = u.toTensorProduct :=
  (rfl)

/-- The inverse equivalence wraps an algebraic tensor. -/
@[simp]
theorem equiv_symm_apply (u : E ⊗[𝕜] F) : (equiv 𝕜 E F).symm u = mk u :=
  (rfl)

/-- The additive equivalence with `E ⊗[𝕜] F` forgets the wrapper. -/
@[simp]
theorem addEquiv_apply (u : InjectiveTensor 𝕜 E F) : addEquiv 𝕜 E F u = u.toTensorProduct :=
  (rfl)

/-- The inverse additive equivalence wraps an algebraic tensor. -/
@[simp]
theorem addEquiv_symm_apply (u : E ⊗[𝕜] F) : (addEquiv 𝕜 E F).symm u = mk u :=
  (rfl)

/-- The linear equivalence with `E ⊗[𝕜] F` forgets the wrapper. -/
@[simp]
theorem linearEquiv_apply (u : InjectiveTensor 𝕜 E F) : linearEquiv 𝕜 E F u = u.toTensorProduct :=
  (rfl)

/-- The inverse linear equivalence wraps an algebraic tensor. -/
@[simp]
theorem linearEquiv_symm_apply (u : E ⊗[𝕜] F) : (linearEquiv 𝕜 E F).symm u = ⟨u⟩ :=
  (rfl)

/-- The underlying tensor of `0` is `0`. -/
@[simp]
theorem toTensorProduct_zero : (0 : InjectiveTensor 𝕜 E F).toTensorProduct = 0 :=
  (rfl)

/-- The underlying tensor of a sum is the sum of the underlying tensors. -/
@[simp]
theorem toTensorProduct_add (u v : InjectiveTensor 𝕜 E F) :
    (u + v).toTensorProduct = u.toTensorProduct + v.toTensorProduct :=
  (rfl)

/-- The underlying tensor of a negation is the negated underlying tensor. -/
@[simp]
theorem toTensorProduct_neg (u : InjectiveTensor 𝕜 E F) :
    (-u).toTensorProduct = -u.toTensorProduct :=
  (rfl)

/-- The underlying tensor of a difference is the difference of the underlying tensors. -/
@[simp]
theorem toTensorProduct_sub (u v : InjectiveTensor 𝕜 E F) :
    (u - v).toTensorProduct = u.toTensorProduct - v.toTensorProduct :=
  (rfl)

/-- The underlying tensor of a scalar multiple is the scalar multiple of the underlying tensor.
-/
@[simp]
theorem toTensorProduct_smul (a : 𝕜) (u : InjectiveTensor 𝕜 E F) :
    (a • u).toTensorProduct = a • u.toTensorProduct :=
  (rfl)

/-- Wrapping `0` gives `0`. -/
@[simp]
theorem mk_zero : (mk 0 : InjectiveTensor 𝕜 E F) = 0 :=
  (rfl)

/-- Wrapping a sum gives the sum of the wrapped tensors. -/
@[simp]
theorem mk_add (u v : E ⊗[𝕜] F) : (mk (u + v) : InjectiveTensor 𝕜 E F) = mk u + mk v :=
  (rfl)

/-- Wrapping a negation gives the negation of the wrapped tensor. -/
@[simp]
theorem mk_neg (u : E ⊗[𝕜] F) : (mk (-u) : InjectiveTensor 𝕜 E F) = -mk u :=
  (rfl)

/-- Wrapping a difference gives the difference of the wrapped tensors. -/
@[simp]
theorem mk_sub (u v : E ⊗[𝕜] F) : (mk (u - v) : InjectiveTensor 𝕜 E F) = mk u - mk v :=
  (rfl)

/-- Wrapping a scalar multiple gives the scalar multiple of the wrapped tensor. -/
@[simp]
theorem mk_smul (a : 𝕜) (u : E ⊗[𝕜] F) : (mk (a • u) : InjectiveTensor 𝕜 E F) = a • mk u :=
  (rfl)

/-- Two injective tensors are equal when their underlying algebraic tensors are equal. -/
@[ext]
theorem ext {u v : InjectiveTensor 𝕜 E F} (h : u.toTensorProduct = v.toTensorProduct) :
    u = v :=
  (equiv 𝕜 E F).injective h

noncomputable instance : SeminormedAddCommGroup (InjectiveTensor 𝕜 E F) :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    ((TensorProduct.injectiveSeminorm 𝕜 E F).comp
      (linearEquiv 𝕜 E F).toLinearMap).toAddGroupSeminorm

/-- The norm of an injective tensor is the injective seminorm of its underlying tensor. -/
theorem norm_def (u : InjectiveTensor 𝕜 E F) :
    ‖u‖ = TensorProduct.injectiveSeminorm 𝕜 E F u.toTensorProduct :=
  (rfl)

noncomputable instance : NormedSpace 𝕜 (InjectiveTensor 𝕜 E F) where
  norm_smul_le a u := by
    simp only [norm_def]
    exact (map_smul_eq_mul _ a u.toTensorProduct).le

end InjectiveTensor

/-- The identity of the underlying tensors, from the projective to the injective tensor product.
It is a contraction because the injective seminorm is bounded by the projective seminorm. -/
noncomputable def ProjectiveTensor.toInjectiveTensor :
    ProjectiveTensor 𝕜 E F →L[𝕜] InjectiveTensor 𝕜 E F :=
  LinearMap.mkContinuous
    ((InjectiveTensor.linearEquiv 𝕜 E F).symm.toLinearMap ∘ₗ
      (ProjectiveTensor.linearEquiv 𝕜 E F).toLinearMap) 1 fun u ↦ by
    simpa [InjectiveTensor.norm_def, ProjectiveTensor.norm_def] using
      TensorProduct.injectiveSeminorm_le_projectiveSeminorm u.toTensorProduct

variable {𝕜 E F}

/-- The contraction to the injective tensor product keeps the underlying tensor. -/
@[simp]
theorem ProjectiveTensor.toInjectiveTensor_apply (u : ProjectiveTensor 𝕜 E F) :
    ProjectiveTensor.toInjectiveTensor 𝕜 E F u = ⟨u.toTensorProduct⟩ := by
  simp [ProjectiveTensor.toInjectiveTensor]

/-- The identity from the projective to the injective tensor product is a contraction. -/
theorem ProjectiveTensor.norm_toInjectiveTensor_le :
    ‖ProjectiveTensor.toInjectiveTensor 𝕜 E F‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end InjectiveTensor

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

noncomputable instance : NormedAddCommGroup (ProjectiveTensor 𝕜 E F) :=
  NormedAddCommGroup.ofSeparation fun _ hu ↦
    (ProjectiveTensor.linearEquiv 𝕜 E F).map_eq_zero_iff.1 <|
      TensorProduct.projectiveSeminorm_eq_zero_iff.1 hu

noncomputable instance : NormedAddCommGroup (InjectiveTensor 𝕜 E F) :=
  NormedAddCommGroup.ofSeparation fun _ hu ↦
    (InjectiveTensor.linearEquiv 𝕜 E F).map_eq_zero_iff.1 <|
      TensorProduct.injectiveSeminorm_eq_zero_iff.1 hu

end RCLike

section RCLikeSeminormed

variable {𝕜 E F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over `ℝ` and `ℂ`, the norm of a pure projective tensor is the product of the norms. -/
@[simp]
theorem ProjectiveTensor.norm_mk_tmul (x : E) (y : F) :
    ‖(⟨x ⊗ₜ y⟩ : ProjectiveTensor 𝕜 E F)‖ = ‖x‖ * ‖y‖ :=
  (ProjectiveTensor.norm_def _).trans (TensorProduct.projectiveSeminorm_tmul x y)

/-- Over `ℝ` and `ℂ`, the norm of a pure injective tensor is the product of the norms. -/
@[simp]
theorem InjectiveTensor.norm_mk_tmul (x : E) (y : F) :
    ‖(⟨x ⊗ₜ y⟩ : InjectiveTensor 𝕜 E F)‖ = ‖x‖ * ‖y‖ :=
  (InjectiveTensor.norm_def _).trans (TensorProduct.injectiveSeminorm_tmul x y)

end RCLikeSeminormed

end TauCeti
