/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# The projective seminorm on a binary tensor product

For seminormed spaces `E` and `F` over a normed field `𝕜`, the projective seminorm of
`u : E ⊗[𝕜] F` is the infimum of `∑ i, ‖x i‖ * ‖y i‖` over all finite decompositions
`u = ∑ i, x i ⊗ₜ y i`. It is the largest seminorm on `E ⊗[𝕜] F` that is bounded on pure tensors
by the product of the norms of the factors. Over a nontrivially normed field, every bounded
bilinear map out of `E × F` induces a linear map on `E ⊗[𝕜] F` bounded by its operator norm for
this seminorm. On `TauCeti.ProjectiveTensor 𝕜 E F` this gives the norm-preserving universal
property on algebraic tensors: bounded bilinear maps `E →L[𝕜] F →L[𝕜] G` correspond
isometrically to bounded operators `ProjectiveTensor 𝕜 E F →L[𝕜] G`.

Mathlib's binary tensor product carries no norm of its own for general normed spaces, while for
inner product spaces it carries the Hilbert-space norm. The type `TauCeti.ProjectiveTensor 𝕜 E F`
is therefore a separate copy of `E ⊗[𝕜] F` carrying the projective seminorm; its completion is
the completed projective tensor product. That the projective seminorm is a norm over `ℝ` and `ℂ`
is proved with the injective seminorm in
`TauCeti.Analysis.Normed.Module.TensorProduct.InjectiveSeminorm`.

The finite-family analogue is Mathlib's `PiTensorProduct.projectiveSeminorm`, whose arguments
this file adapts to two factors indexed by `Fin n` decompositions. The construction of
`TauCeti.ProjectiveTensor.liftIsometry` follows Mathlib's `PiTensorProduct.liftIsometry`.

## Main definitions

* `TensorProduct.projectiveSeminorm 𝕜 E F`: the projective seminorm on `E ⊗[𝕜] F`.
* `TauCeti.ProjectiveTensor 𝕜 E F`: the algebraic tensor product with the projective seminorm.
* `TauCeti.ProjectiveTensor.tmulL`: the bounded bilinear map `(x, y) ↦ x ⊗ₜ y`.
* `TauCeti.ProjectiveTensor.liftIsometry`: the isometric universal property of the projective
  tensor product.

## Main results

* `TensorProduct.projectiveSeminorm_sum_tmul_le` and
  `TensorProduct.exists_sum_tmul_eq_of_projectiveSeminorm_lt`: the projective seminorm is
  the infimum of the costs of finite decompositions.
* `TensorProduct.apply_le_mul_projectiveSeminorm`: a seminorm bounded by `C ‖x‖ ‖y‖` on
  pure tensors is bounded by `C` times the projective seminorm.
* `TensorProduct.norm_lift_le_projectiveSeminorm`: over a nontrivially normed field, the linear
  map induced by a bounded bilinear map `B` is bounded by `‖B‖` times the projective seminorm.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, §2.1.
-/

public section

open scoped TensorProduct

namespace TensorProduct

section NormedField

variable (𝕜 E F : Type*) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The costs `∑ i, ‖x i‖ * ‖y i‖` of the finite decompositions `u = ∑ i, x i ⊗ₜ y i`. -/
private def costs (u : E ⊗[𝕜] F) : Set ℝ :=
  {c | ∃ (n : ℕ) (x : Fin n → E) (y : Fin n → F),
    ∑ i, x i ⊗ₜ[𝕜] y i = u ∧ ∑ i, ‖x i‖ * ‖y i‖ = c}

variable {𝕜 E F}

private theorem costs_nonempty (u : E ⊗[𝕜] F) : (costs 𝕜 E F u).Nonempty := by
  obtain ⟨n, x, y, hu⟩ := _root_.TensorProduct.exists_sum_tmul_eq u
  exact ⟨_, n, x, y, hu.symm, rfl⟩

private theorem costs_bddBelow (u : E ⊗[𝕜] F) : BddBelow (costs 𝕜 E F u) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, x, y, -, rfl⟩
  exact Finset.sum_nonneg fun _ _ ↦ by positivity

private theorem sInf_costs_le {n : ℕ} (x : Fin n → E) (y : Fin n → F) :
    sInf (costs 𝕜 E F (∑ i, x i ⊗ₜ[𝕜] y i)) ≤ ∑ i, ‖x i‖ * ‖y i‖ :=
  csInf_le (costs_bddBelow _) ⟨n, x, y, rfl, rfl⟩

private theorem sInf_costs_zero : sInf (costs 𝕜 E F 0) = 0 := by
  refine le_antisymm ?_ (le_csInf (costs_nonempty 0) ?_)
  · simpa using sInf_costs_le (𝕜 := 𝕜) (Fin.elim0 : Fin 0 → E) (Fin.elim0 : Fin 0 → F)
  · rintro _ ⟨n, x, y, -, rfl⟩
    exact Finset.sum_nonneg fun _ _ ↦ by positivity

private theorem sInf_costs_add_le (u v : E ⊗[𝕜] F) :
    sInf (costs 𝕜 E F (u + v)) ≤ sInf (costs 𝕜 E F u) + sInf (costs 𝕜 E F v) := by
  rw [← sub_le_iff_le_add]
  refine le_csInf (costs_nonempty u) ?_
  rintro _ ⟨n, x, y, rfl, rfl⟩
  rw [sub_le_comm]
  refine le_csInf (costs_nonempty v) ?_
  rintro _ ⟨m, x', y', rfl, rfl⟩
  rw [sub_le_iff_le_add']
  simpa [Fin.sum_univ_add] using
    sInf_costs_le (𝕜 := 𝕜) (Fin.append x x') (Fin.append y y')

private theorem sInf_costs_smul_le (a : 𝕜) (u : E ⊗[𝕜] F) :
    sInf (costs 𝕜 E F (a • u)) ≤ ‖a‖ * sInf (costs 𝕜 E F u) := by
  rw [← smul_eq_mul, ← Real.sInf_smul_of_nonneg (norm_nonneg a)]
  refine csInf_le_csInf (costs_bddBelow _) ((costs_nonempty u).smul_set) ?_
  rintro _ ⟨_, ⟨n, x, y, rfl, rfl⟩, rfl⟩
  refine ⟨n, fun i ↦ a • x i, y, ?_, ?_⟩
  · simp [Finset.smul_sum, TensorProduct.smul_tmul']
  · simp [norm_smul, Finset.mul_sum, mul_assoc]

variable (𝕜 E F) in
/-- The **projective seminorm** on `E ⊗[𝕜] F`: the infimum of `∑ i, ‖x i‖ * ‖y i‖` over all
finite decompositions `u = ∑ i, x i ⊗ₜ y i`. -/
noncomputable def projectiveSeminorm : Seminorm 𝕜 (E ⊗[𝕜] F) :=
  .ofSMulLE (fun u ↦ sInf (costs 𝕜 E F u)) sInf_costs_zero sInf_costs_add_le sInf_costs_smul_le

private theorem projectiveSeminorm_apply (u : E ⊗[𝕜] F) :
    projectiveSeminorm 𝕜 E F u = sInf (costs 𝕜 E F u) :=
  rfl

/-- The projective seminorm of a finite sum of pure tensors is at most its cost. -/
theorem projectiveSeminorm_sum_tmul_le {ι : Type*} (s : Finset ι) (x : ι → E) (y : ι → F) :
    projectiveSeminorm 𝕜 E F (∑ i ∈ s, x i ⊗ₜ y i) ≤ ∑ i ∈ s, ‖x i‖ * ‖y i‖ := by
  let e := s.equivFin
  rw [projectiveSeminorm_apply]
  have key := sInf_costs_le (𝕜 := 𝕜) (fun j ↦ x (e.symm j)) (fun j ↦ y (e.symm j))
  rw [← Finset.sum_coe_sort s, ← Finset.sum_coe_sort s, ← e.symm.sum_comp,
    ← e.symm.sum_comp (fun i : s ↦ ‖x i‖ * ‖y i‖)]
  exact key

/-- A strict upper bound on the projective seminorm is beaten by the cost of some finite
decomposition. -/
theorem exists_sum_tmul_eq_of_projectiveSeminorm_lt {u : E ⊗[𝕜] F} {c : ℝ}
    (h : projectiveSeminorm 𝕜 E F u < c) :
    ∃ (n : ℕ) (x : Fin n → E) (y : Fin n → F),
      ∑ i, x i ⊗ₜ[𝕜] y i = u ∧ ∑ i, ‖x i‖ * ‖y i‖ < c := by
  obtain ⟨_, ⟨n, x, y, hu, rfl⟩, hc⟩ := exists_lt_of_csInf_lt (costs_nonempty u) <| by
    rwa [← projectiveSeminorm_apply]
  exact ⟨n, x, y, hu, hc⟩

/-- The projective seminorm of a pure tensor is at most the product of the norms. -/
theorem projectiveSeminorm_tmul_le (x : E) (y : F) :
    projectiveSeminorm 𝕜 E F (x ⊗ₜ y) ≤ ‖x‖ * ‖y‖ := by
  simpa using projectiveSeminorm_sum_tmul_le {()} (fun _ ↦ x) (fun _ ↦ y)

/-- A seminorm bounded on the images of pure tensors by `C * (‖x‖ * ‖y‖)` is bounded on the
image of every tensor by `C` times the projective seminorm. -/
theorem apply_le_mul_projectiveSeminorm {G : Type*} [AddCommGroup G] [Module 𝕜 G]
    {p : Seminorm 𝕜 G} {f : E ⊗[𝕜] F →ₗ[𝕜] G} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, p (f (x ⊗ₜ y)) ≤ C * (‖x‖ * ‖y‖)) (u : E ⊗[𝕜] F) :
    p (f u) ≤ C * projectiveSeminorm 𝕜 E F u := by
  rw [projectiveSeminorm_apply, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg hC]
  refine le_csInf (costs_nonempty u).smul_set ?_
  rintro _ ⟨_, ⟨n, x, y, rfl, rfl⟩, rfl⟩
  calc p (f (∑ i, x i ⊗ₜ y i)) ≤ ∑ i, p (f (x i ⊗ₜ y i)) := by
        rw [map_sum]; exact Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
    _ ≤ ∑ i, C * (‖x i‖ * ‖y i‖) := Finset.sum_le_sum fun i _ ↦ h (x i) (y i)
    _ = C • ∑ i, ‖x i‖ * ‖y i‖ := by rw [smul_eq_mul, Finset.mul_sum]

/-- The projective seminorm is the largest seminorm on `E ⊗[𝕜] F` bounded on pure tensors by
the product of the norms. -/
theorem le_projectiveSeminorm {p : Seminorm 𝕜 (E ⊗[𝕜] F)}
    (h : ∀ x y, p (x ⊗ₜ y) ≤ ‖x‖ * ‖y‖) : p ≤ projectiveSeminorm 𝕜 E F := fun u ↦ by
  simpa using apply_le_mul_projectiveSeminorm (p := p) (f := LinearMap.id) zero_le_one
    (by simpa using h) u

end NormedField

section NontriviallyNormedField

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup G]
  [NormedSpace 𝕜 G]

/-- The linear map on `E ⊗[𝕜] F` induced by a bounded bilinear map `B` is bounded by
`‖B‖` times the projective seminorm. -/
theorem norm_lift_le_projectiveSeminorm (B : E →L[𝕜] F →L[𝕜] G) (u : E ⊗[𝕜] F) :
    ‖_root_.TensorProduct.lift (B.toLinearMap₁₂) u‖ ≤ ‖B‖ * projectiveSeminorm 𝕜 E F u :=
  apply_le_mul_projectiveSeminorm (p := normSeminorm 𝕜 G) (norm_nonneg B)
    (fun x y ↦ by simpa [mul_assoc] using B.le_opNorm₂ x y) u

end NontriviallyNormedField

end TensorProduct

namespace TauCeti

variable (𝕜 E F : Type*) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The algebraic tensor product `E ⊗[𝕜] F` carrying the projective seminorm.

This wrapper distinguishes the projective seminorm from other norms on the same algebraic tensor
product, such as the injective norm or the Hilbert-space norm of inner product spaces. -/
structure ProjectiveTensor where
  /-- The underlying element of the algebraic tensor product. -/
  toTensorProduct : E ⊗[𝕜] F

namespace ProjectiveTensor

/-- Forget the projective seminorm. -/
def equiv : ProjectiveTensor 𝕜 E F ≃ E ⊗[𝕜] F where
  toFun := toTensorProduct
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (ProjectiveTensor 𝕜 E F) := (equiv 𝕜 E F).addCommGroup

/-- Forget the projective seminorm and retain the additive structure. -/
def addEquiv : ProjectiveTensor 𝕜 E F ≃+ E ⊗[𝕜] F where
  toEquiv := equiv 𝕜 E F
  map_add' _ _ := rfl

instance : Module 𝕜 (ProjectiveTensor 𝕜 E F) := (addEquiv 𝕜 E F).module 𝕜

/-- The projective tensor product is linearly equivalent to the algebraic tensor product. -/
def linearEquiv : ProjectiveTensor 𝕜 E F ≃ₗ[𝕜] E ⊗[𝕜] F where
  toAddEquiv := addEquiv 𝕜 E F
  map_smul' _ _ := rfl

variable {𝕜 E F}

/-- The equivalence with `E ⊗[𝕜] F` forgets the wrapper. -/
@[simp]
theorem equiv_apply (u : ProjectiveTensor 𝕜 E F) : equiv 𝕜 E F u = u.toTensorProduct :=
  (rfl)

/-- The inverse equivalence wraps an algebraic tensor. -/
@[simp]
theorem equiv_symm_apply (u : E ⊗[𝕜] F) : (equiv 𝕜 E F).symm u = mk u :=
  (rfl)

/-- The additive equivalence with `E ⊗[𝕜] F` forgets the wrapper. -/
@[simp]
theorem addEquiv_apply (u : ProjectiveTensor 𝕜 E F) : addEquiv 𝕜 E F u = u.toTensorProduct :=
  (rfl)

/-- The inverse additive equivalence wraps an algebraic tensor. -/
@[simp]
theorem addEquiv_symm_apply (u : E ⊗[𝕜] F) : (addEquiv 𝕜 E F).symm u = mk u :=
  (rfl)

/-- The linear equivalence with `E ⊗[𝕜] F` forgets the wrapper. -/
@[simp]
theorem linearEquiv_apply (u : ProjectiveTensor 𝕜 E F) : linearEquiv 𝕜 E F u = u.toTensorProduct :=
  (rfl)

/-- The inverse linear equivalence wraps an algebraic tensor. -/
@[simp]
theorem linearEquiv_symm_apply (u : E ⊗[𝕜] F) : (linearEquiv 𝕜 E F).symm u = ⟨u⟩ :=
  (rfl)

/-- The underlying tensor of `0` is `0`. -/
@[simp]
theorem toTensorProduct_zero : (0 : ProjectiveTensor 𝕜 E F).toTensorProduct = 0 :=
  (rfl)

/-- The underlying tensor of a sum is the sum of the underlying tensors. -/
@[simp]
theorem toTensorProduct_add (u v : ProjectiveTensor 𝕜 E F) :
    (u + v).toTensorProduct = u.toTensorProduct + v.toTensorProduct :=
  (rfl)

/-- The underlying tensor of a negation is the negated underlying tensor. -/
@[simp]
theorem toTensorProduct_neg (u : ProjectiveTensor 𝕜 E F) :
    (-u).toTensorProduct = -u.toTensorProduct :=
  (rfl)

/-- The underlying tensor of a difference is the difference of the underlying tensors. -/
@[simp]
theorem toTensorProduct_sub (u v : ProjectiveTensor 𝕜 E F) :
    (u - v).toTensorProduct = u.toTensorProduct - v.toTensorProduct :=
  (rfl)

/-- The underlying tensor of a scalar multiple is the scalar multiple of the underlying tensor.
-/
@[simp]
theorem toTensorProduct_smul (a : 𝕜) (u : ProjectiveTensor 𝕜 E F) :
    (a • u).toTensorProduct = a • u.toTensorProduct :=
  (rfl)

/-- Wrapping `0` gives `0`. -/
@[simp]
theorem mk_zero : (mk 0 : ProjectiveTensor 𝕜 E F) = 0 :=
  (rfl)

/-- Wrapping a sum gives the sum of the wrapped tensors. -/
@[simp]
theorem mk_add (u v : E ⊗[𝕜] F) : (mk (u + v) : ProjectiveTensor 𝕜 E F) = mk u + mk v :=
  (rfl)

/-- Wrapping a negation gives the negation of the wrapped tensor. -/
@[simp]
theorem mk_neg (u : E ⊗[𝕜] F) : (mk (-u) : ProjectiveTensor 𝕜 E F) = -mk u :=
  (rfl)

/-- Wrapping a difference gives the difference of the wrapped tensors. -/
@[simp]
theorem mk_sub (u v : E ⊗[𝕜] F) : (mk (u - v) : ProjectiveTensor 𝕜 E F) = mk u - mk v :=
  (rfl)

/-- Wrapping a scalar multiple gives the scalar multiple of the wrapped tensor. -/
@[simp]
theorem mk_smul (a : 𝕜) (u : E ⊗[𝕜] F) : (mk (a • u) : ProjectiveTensor 𝕜 E F) = a • mk u :=
  (rfl)

/-- Two projective tensors are equal when their underlying algebraic tensors are equal. -/
@[ext]
theorem ext {u v : ProjectiveTensor 𝕜 E F} (h : u.toTensorProduct = v.toTensorProduct) :
    u = v :=
  (equiv 𝕜 E F).injective h

noncomputable instance : SeminormedAddCommGroup (ProjectiveTensor 𝕜 E F) :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    ((TensorProduct.projectiveSeminorm 𝕜 E F).comp
      (linearEquiv 𝕜 E F).toLinearMap).toAddGroupSeminorm

/-- The norm of a projective tensor is the projective seminorm of its underlying tensor. -/
theorem norm_def (u : ProjectiveTensor 𝕜 E F) :
    ‖u‖ = TensorProduct.projectiveSeminorm 𝕜 E F u.toTensorProduct :=
  (rfl)

noncomputable instance : NormedSpace 𝕜 (ProjectiveTensor 𝕜 E F) where
  norm_smul_le a u := by
    simp only [norm_def]
    exact (map_smul_eq_mul _ a u.toTensorProduct).le

/-- Two bounded operators out of the projective tensor product agree when they agree on pure
tensors. -/
@[ext]
theorem continuousLinearMap_ext {M : Type*} [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M]
    {l l' : ProjectiveTensor 𝕜 E F →L[𝕜] M}
    (h : ∀ x y, l ⟨x ⊗ₜ y⟩ = l' ⟨x ⊗ₜ y⟩) : l = l' := by
  ext ⟨u⟩
  induction u with
  | tmul x y => exact h x y
  | add u v hu hv => simp only [mk_add, map_add, hu, hv]

end ProjectiveTensor

end TauCeti

namespace TauCeti.ProjectiveTensor

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup G]
  [NormedSpace 𝕜 G]

variable (𝕜 E F) in
/-- The canonical bounded bilinear map `(x, y) ↦ x ⊗ₜ y` into the projective tensor product. -/
noncomputable def tmulL : E →L[𝕜] F →L[𝕜] ProjectiveTensor 𝕜 E F :=
  LinearMap.mkContinuous₂ ((_root_.TensorProduct.mk 𝕜 E F).compr₂
    (linearEquiv 𝕜 E F).symm.toLinearMap) 1 fun x y ↦ by
      simpa [norm_def, mul_assoc] using TensorProduct.projectiveSeminorm_tmul_le x y

/-- The canonical bilinear map sends `(x, y)` to the pure tensor `x ⊗ₜ y`. -/
@[simp]
theorem tmulL_apply (x : E) (y : F) : tmulL 𝕜 E F x y = ⟨x ⊗ₜ y⟩ := by
  simp [tmulL]

/-- The canonical bilinear map into the projective tensor product has norm at most one. -/
theorem norm_tmulL_le : ‖tmulL 𝕜 E F‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

variable (𝕜 E F G) in
/-- The **universal property** of the projective tensor product: bounded bilinear maps
`E →L[𝕜] F →L[𝕜] G` correspond isometrically to bounded operators on `ProjectiveTensor 𝕜 E F`.
The operator induced by `B` sends `x ⊗ₜ y` to `B x y`. -/
noncomputable def liftIsometry :
    (E →L[𝕜] F →L[𝕜] G) ≃ₗᵢ[𝕜] (ProjectiveTensor 𝕜 E F →L[𝕜] G) :=
  LinearIsometryEquiv.ofBounds
    { toFun B := LinearMap.mkContinuous
        (_root_.TensorProduct.lift B.toLinearMap₁₂ ∘ₗ (linearEquiv 𝕜 E F).toLinearMap) ‖B‖
        fun u ↦ by simpa [norm_def] using TensorProduct.norm_lift_le_projectiveSeminorm B _
      map_add' B B' := continuousLinearMap_ext fun x y ↦ by simp
      map_smul' a B := continuousLinearMap_ext fun x y ↦ by simp
      invFun l := (ContinuousLinearMap.compL 𝕜 F (ProjectiveTensor 𝕜 E F) G l).comp (tmulL 𝕜 E F)
      left_inv B := by ext x y; simp
      right_inv l := continuousLinearMap_ext fun x y ↦ by simp }
    (fun B ↦ LinearMap.mkContinuous_norm_le _ (norm_nonneg B) fun u ↦ by
      simpa [norm_def] using TensorProduct.norm_lift_le_projectiveSeminorm B _)
    (fun l ↦ by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      calc _ ≤ ‖l‖ * 1 := by
            gcongr
            · simpa using ContinuousLinearMap.le_of_opNorm_le _
                (ContinuousLinearMap.norm_compL_le 𝕜 F _ G) l
            · exact norm_tmulL_le
        _ = ‖l‖ := mul_one _)

/-- The operator induced by a bounded bilinear map acts on the underlying tensor by
`TensorProduct.lift`. -/
theorem liftIsometry_apply (B : E →L[𝕜] F →L[𝕜] G) (u : ProjectiveTensor 𝕜 E F) :
    liftIsometry 𝕜 E F G B u = _root_.TensorProduct.lift B.toLinearMap₁₂ u.toTensorProduct := by
  simp [liftIsometry, LinearIsometryEquiv.ofBounds]

/-- The operator induced by a bounded bilinear map `B` sends `x ⊗ₜ y` to `B x y`. -/
@[simp]
theorem liftIsometry_apply_tmul (B : E →L[𝕜] F →L[𝕜] G) (x : E) (y : F) :
    liftIsometry 𝕜 E F G B ⟨x ⊗ₜ y⟩ = B x y := by
  simp [liftIsometry_apply]

/-- The bilinear map corresponding to an operator `l` on the projective tensor product is
`(x, y) ↦ l (x ⊗ₜ y)`. -/
@[simp]
theorem liftIsometry_symm_apply_apply (l : ProjectiveTensor 𝕜 E F →L[𝕜] G) (x : E) (y : F) :
    (liftIsometry 𝕜 E F G).symm l x y = l ⟨x ⊗ₜ y⟩ :=
  congrArg l (tmulL_apply x y)

/-- The canonical bilinear map induces the identity of the projective tensor product. -/
@[simp]
theorem liftIsometry_tmulL :
    liftIsometry 𝕜 E F _ (tmulL 𝕜 E F) = ContinuousLinearMap.id 𝕜 (ProjectiveTensor 𝕜 E F) :=
  continuousLinearMap_ext fun x y ↦ by simp

end TauCeti.ProjectiveTensor
