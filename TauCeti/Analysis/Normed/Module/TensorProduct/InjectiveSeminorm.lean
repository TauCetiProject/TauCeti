/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.HahnBanach
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

This file proves that the injective seminorm is bounded by the projective seminorm, that over
`ℝ` and `ℂ` both agree with `‖x‖ * ‖y‖` on a pure tensor `x ⊗ₜ y`, and that both are norms when
`E` and `F` are normed spaces. Definiteness rests on the injectivity of the map from tensors to
operators on the dual: a tensor lies in `E₀ ⊗[𝕜] F` for a finite-dimensional subspace `E₀ ≤ E`,
and the coordinate functionals of a basis of `E₀` extend to `E` by the Hahn–Banach theorem.

The type `TauCeti.InjectiveTensor 𝕜 E F` is a copy of `E ⊗[𝕜] F` carrying the injective
seminorm, and the identity of the underlying tensors is a contraction from
`TauCeti.ProjectiveTensor 𝕜 E F` to it.

Mathlib's `PiTensorProduct.injectiveSeminorm` is a different seminorm on finite
families of factors, defined by duality against all normed target spaces rather than against the
scalar field; it is not the classical injective norm used here.

## Main definitions

* `TauCeti.TensorProduct.toDualMap 𝕜 E F`: the bounded operator on the dual of `E` induced by a
  tensor.
* `TauCeti.TensorProduct.injectiveSeminorm 𝕜 E F`: the injective seminorm on `E ⊗[𝕜] F`.
* `TauCeti.InjectiveTensor 𝕜 E F`: the algebraic tensor product with the injective seminorm.
* `TauCeti.ProjectiveTensor.toInjectiveTensor`: the contraction from the projective to the
  injective tensor product.

## Main results

* `TauCeti.TensorProduct.injectiveSeminorm_le_projectiveSeminorm`: `ε ≤ π`.
* `TauCeti.TensorProduct.injectiveSeminorm_le_iff_forall_norm_le_one`: the classical
  description of the injective seminorm over `ℝ` and `ℂ`.
* `TauCeti.TensorProduct.injectiveSeminorm_tmul` and
  `TauCeti.TensorProduct.projectiveSeminorm_tmul`: both seminorms are cross norms.
* `TauCeti.TensorProduct.toDualMap_injective`: over `ℝ` and `ℂ`, a tensor is determined by the
  operator it induces on the dual of a normed left factor.
* `TauCeti.TensorProduct.injectiveSeminorm_eq_zero_iff` and
  `TauCeti.TensorProduct.projectiveSeminorm_eq_zero_iff`: both seminorms are definite.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, §§2.1, 3.1.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace TensorProduct

section NontriviallyNormedField

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The bounded operator `StrongDual 𝕜 E →L[𝕜] F` induced by a tensor in `E ⊗[𝕜] F`: the pure
tensor `x ⊗ₜ y` gives `f ↦ f x • y`. -/
noncomputable def toDualMap : E ⊗[𝕜] F →ₗ[𝕜] StrongDual 𝕜 E →L[𝕜] F :=
  _root_.TensorProduct.lift <| LinearMap.mk₂ 𝕜
    (fun x y ↦ (NormedSpace.inclusionInDoubleDual 𝕜 E x).smulRight y)
    (fun x x' y ↦ by ext f; simp [add_smul])
    (fun c x y ↦ by ext f; simp [mul_smul])
    (fun x y y' ↦ by ext f; simp)
    (fun c x y ↦ by ext f; simp [smul_comm c])

variable {𝕜 E F}

/-- The operator induced by `x ⊗ₜ y` sends `f` to `f x • y`. -/
@[simp]
theorem toDualMap_tmul (x : E) (y : F) (f : StrongDual 𝕜 E) :
    toDualMap 𝕜 E F (x ⊗ₜ y) f = f x • y := by
  simp [toDualMap]

/-- The operator induced by a tensor sends `f` to the image of the tensor under `f ⊗ id`,
followed by `𝕜 ⊗[𝕜] F ≃ F`. -/
theorem toDualMap_apply (u : E ⊗[𝕜] F) (f : StrongDual 𝕜 E) :
    toDualMap 𝕜 E F u f = _root_.TensorProduct.lid 𝕜 F ((f : E →ₗ[𝕜] 𝕜).rTensor F u) := by
  induction u with
  | tmul x y => simp
  | add u v hu hv => simp [hu, hv]

variable (𝕜 E F) in
/-- The **injective seminorm** on `E ⊗[𝕜] F`: the operator norm of the operator on the dual of
`E` induced by a tensor. Over `ℝ` and `ℂ` it is the supremum of `‖∑ i, f (x i) * g (y i)‖` over
continuous linear functionals `f` and `g` of norm at most one, for any decomposition
`u = ∑ i, x i ⊗ₜ y i`; see `injectiveSeminorm_le_iff_forall_norm_le_one`. -/
noncomputable def injectiveSeminorm : Seminorm 𝕜 (E ⊗[𝕜] F) :=
  (normSeminorm 𝕜 (StrongDual 𝕜 E →L[𝕜] F)).comp (toDualMap 𝕜 E F)

/-- The injective seminorm is the operator norm of the induced operator on the dual. -/
theorem injectiveSeminorm_apply (u : E ⊗[𝕜] F) :
    injectiveSeminorm 𝕜 E F u = ‖toDualMap 𝕜 E F u‖ :=
  (rfl)

/-- The operator induced by a tensor is bounded by its injective seminorm. -/
theorem norm_toDualMap_apply_le (u : E ⊗[𝕜] F) (f : StrongDual 𝕜 E) :
    ‖toDualMap 𝕜 E F u f‖ ≤ injectiveSeminorm 𝕜 E F u * ‖f‖ :=
  (toDualMap 𝕜 E F u).le_opNorm f

/-- A nonnegative constant bounds the injective seminorm of a tensor if and only if it bounds
the operator the tensor induces on the dual. -/
theorem injectiveSeminorm_le_iff {u : E ⊗[𝕜] F} {C : ℝ} (hC : 0 ≤ C) :
    injectiveSeminorm 𝕜 E F u ≤ C ↔ ∀ f, ‖toDualMap 𝕜 E F u f‖ ≤ C * ‖f‖ :=
  ⟨fun h f ↦ (norm_toDualMap_apply_le u f).trans (by gcongr),
    fun h ↦ (toDualMap 𝕜 E F u).opNorm_le_bound hC h⟩

/-- The injective seminorm of a pure tensor is at most the product of the norms. -/
theorem injectiveSeminorm_tmul_le (x : E) (y : F) :
    injectiveSeminorm 𝕜 E F (x ⊗ₜ y) ≤ ‖x‖ * ‖y‖ := by
  refine (injectiveSeminorm_le_iff (by positivity)).2 fun f ↦ ?_
  rw [toDualMap_tmul, norm_smul]
  calc ‖f x‖ * ‖y‖ ≤ (‖f‖ * ‖x‖) * ‖y‖ := by gcongr; exact f.le_opNorm x
    _ = ‖x‖ * ‖y‖ * ‖f‖ := by ring

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
`‖g (toDualMap 𝕜 E F u f)‖ = ‖∑ i, f (x i) * g (y i)‖` over the closed unit balls of the duals
of `E` and `F`. -/
theorem injectiveSeminorm_le_iff_forall_norm_le_one {u : E ⊗[𝕜] F} {C : ℝ} (hC : 0 ≤ C) :
    injectiveSeminorm 𝕜 E F u ≤ C ↔
      ∀ (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F), ‖f‖ ≤ 1 → ‖g‖ ≤ 1 →
        ‖g (toDualMap 𝕜 E F u f)‖ ≤ C := by
  refine ⟨fun h f g hf hg ↦ ?_, fun h ↦ ?_⟩
  · calc ‖g (toDualMap 𝕜 E F u f)‖ ≤ ‖g‖ * (injectiveSeminorm 𝕜 E F u * ‖f‖) :=
          g.le_of_opNorm_le_of_le le_rfl (norm_toDualMap_apply_le u f)
      _ ≤ 1 * (C * 1) := by gcongr
      _ = C := by ring
  · rw [injectiveSeminorm_apply]
    refine ContinuousLinearMap.opNorm_le_of_unit_norm hC fun f hf ↦ ?_
    rw [← (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map]
    exact ContinuousLinearMap.opNorm_le_of_unit_norm hC fun g hg ↦ h f g hf.le hg.le

/-- The injective seminorm is a cross norm: its value on `x ⊗ₜ y` is `‖x‖ * ‖y‖`. -/
@[simp]
theorem injectiveSeminorm_tmul (x : E) (y : F) :
    injectiveSeminorm 𝕜 E F (x ⊗ₜ y) = ‖x‖ * ‖y‖ := by
  refine le_antisymm (injectiveSeminorm_tmul_le x y) ?_
  obtain ⟨f, hf, hfx⟩ := exists_dual_vector'' 𝕜 x
  calc ‖x‖ * ‖y‖ = ‖toDualMap 𝕜 E F (x ⊗ₜ y) f‖ := by simp [hfx, norm_smul]
    _ ≤ injectiveSeminorm 𝕜 E F (x ⊗ₜ y) * ‖f‖ := norm_toDualMap_apply_le _ f
    _ ≤ injectiveSeminorm 𝕜 E F (x ⊗ₜ y) * 1 := by gcongr
    _ = injectiveSeminorm 𝕜 E F (x ⊗ₜ y) := mul_one _

/-- The projective seminorm is a cross norm: its value on `x ⊗ₜ y` is `‖x‖ * ‖y‖`. -/
@[simp]
theorem projectiveSeminorm_tmul (x : E) (y : F) :
    projectiveSeminorm 𝕜 E F (x ⊗ₜ y) = ‖x‖ * ‖y‖ :=
  le_antisymm (projectiveSeminorm_tmul_le x y)
    ((injectiveSeminorm_tmul x y).symm.le.trans (injectiveSeminorm_le_projectiveSeminorm _))

end Seminormed

/-- Over `ℝ` and `ℂ`, a tensor whose left factor is a normed space is determined by the operator
it induces on the dual of that factor. -/
theorem toDualMap_injective [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 F] : Function.Injective (toDualMap 𝕜 E F) := by
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
  rw [hcoord, LinearMap.rTensor_comp_apply, ← toDualMap_apply, hu,
    zero_apply]

section Normed

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over `ℝ` and `ℂ`, the injective seminorm on a tensor product of normed spaces is definite. -/
@[simp]
theorem injectiveSeminorm_eq_zero_iff {u : E ⊗[𝕜] F} : injectiveSeminorm 𝕜 E F u = 0 ↔ u = 0 := by
  rw [injectiveSeminorm_apply, ContinuousLinearMap.opNorm_zero_iff,
    toDualMap_injective.eq_iff' (map_zero _)]

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

/-- The linear equivalence with `E ⊗[𝕜] F` forgets the wrapper. -/
@[simp]
theorem linearEquiv_apply (u : InjectiveTensor 𝕜 E F) : linearEquiv 𝕜 E F u = u.toTensorProduct :=
  (rfl)

/-- The inverse linear equivalence wraps an algebraic tensor. -/
@[simp]
theorem linearEquiv_symm_apply (u : E ⊗[𝕜] F) : (linearEquiv 𝕜 E F).symm u = ⟨u⟩ :=
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
