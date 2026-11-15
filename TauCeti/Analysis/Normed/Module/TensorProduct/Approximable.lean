/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.TensorProduct.Completion
public import Mathlib.Algebra.Module.LinearMap.FiniteRange

/-!
# Injective tensors and approximable operators

The algebraic tensor product `E* ⊗ F` identifies with the finite-rank bounded operators
`E →L[𝕜] F`, by sending `f ⊗ y` to `x ↦ f x • y`. Its injective norm is exactly the
operator norm. Consequently, when `F` is complete, the completed injective tensor product
identifies isometrically with the operator-norm closure of the finite-rank operators.
Neither completeness nor reflexivity of `E` is needed.

The map `TauCeti.InjectiveTensor.toOperator` gives the algebraic identification, and
`TauCeti.CompletedInjectiveTensor.toOperator` is its isometric extension. The range
statements characterize their images without introducing another operator carrier. On the
projective tensor product, `TauCeti.ProjectiveTensor.toOperator` gives the corresponding bounded
contraction `E* ⊗π F →L[𝕜] E →L[𝕜] F` over any nontrivially normed field.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, §3.1.
-/

public section

open scoped TensorProduct
open UniformSpace

namespace TensorProduct

section NontriviallyNormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A tensor in `E* ⊗ F` acts on `E` by evaluation in its first factor. -/
noncomputable def toOperator : StrongDual 𝕜 E ⊗[𝕜] F →ₗ[𝕜] E →L[𝕜] F :=
  TensorProduct.lift (ContinuousLinearMap.smulRightLₗ 𝕜 E F)

/-- A pure tensor acts as the corresponding rank-one operator. -/
@[simp]
theorem toOperator_tmul (f : StrongDual 𝕜 E) (y : F) :
    toOperator (f ⊗ₜ y) = f.smulRight y := by
  simp [toOperator]

/-- The action on `E` is the restriction of contraction on `E**` to the canonical image of `E`. -/
theorem toOperator_apply (u : StrongDual 𝕜 E ⊗[𝕜] F) (x : E) :
    toOperator u x = contractStrongDual 𝕜 (StrongDual 𝕜 E) F u
      (NormedSpace.inclusionInDoubleDual 𝕜 E x) := by
  induction u with
  | tmul f y => simp [NormedSpace.dual_def]
  | add u v hu hv => simp [hu, hv]

/-- Pairing a contracted tensor with `g` is evaluation of the bidual vector on `g ∘ T`. -/
theorem apply_contractStrongDual_eq_apply_comp_toOperator (u : StrongDual 𝕜 E ⊗[𝕜] F)
    (Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) (g : StrongDual 𝕜 F) :
    g (contractStrongDual 𝕜 (StrongDual 𝕜 E) F u Φ) = Φ (g ∘L toOperator u) := by
  induction u with
  | tmul f y =>
    have h : g ∘L f.smulRight y = (g y) • f := by ext x; simp [mul_comm]
    simp [h, mul_comm]
  | add u v hu hv => simp [hu, hv, ContinuousLinearMap.comp_add]

end NontriviallyNormedField

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The injective norm of a tensor in `E* ⊗ F` is the norm of its operator on `E`. -/
@[simp]
theorem injectiveSeminorm_eq_norm_toOperator (u : StrongDual 𝕜 E ⊗[𝕜] F) :
    injectiveSeminorm 𝕜 (StrongDual 𝕜 E) F u = ‖toOperator u‖ := by
  refine le_antisymm ?_ ?_
  · refine (injectiveSeminorm_le_iff_forall_norm_le_one (norm_nonneg _)).2 ?_
    intro Φ g hΦ hg
    rw [apply_contractStrongDual_eq_apply_comp_toOperator]
    calc
      ‖Φ (g ∘L toOperator u)‖ ≤ ‖Φ‖ * ‖g ∘L toOperator u‖ := Φ.le_opNorm _
      _ ≤ 1 * (1 * ‖toOperator u‖) := by
        gcongr
        exact (g.opNorm_comp_le _).trans (by gcongr)
      _ = ‖toOperator u‖ := by ring
  · refine ContinuousLinearMap.opNorm_le_bound _ (apply_nonneg _ _) fun x ↦ ?_
    rw [toOperator_apply]
    exact (norm_contractStrongDual_apply_le u _).trans (by
      gcongr
      exact NormedSpace.double_dual_bound 𝕜 E x)

end TensorProduct

namespace TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace InjectiveTensor

variable (𝕜 E F) in
/-- The canonical isometric embedding of `E* ⊗ε F` into the bounded operators `E →L[𝕜] F`. -/
noncomputable def toOperator : InjectiveTensor 𝕜 (StrongDual 𝕜 E) F →ₗᵢ[𝕜] E →L[𝕜] F where
  toLinearMap := TensorProduct.toOperator ∘ₗ (linearEquiv 𝕜 (StrongDual 𝕜 E) F).toLinearMap
  norm_map' u := by
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, linearEquiv_apply, norm_def] using
      (TensorProduct.injectiveSeminorm_eq_norm_toOperator u.toTensorProduct).symm

/-- The embedding sends a wrapped algebraic tensor to its evaluation operator. -/
@[simp]
theorem toOperator_mk (u : StrongDual 𝕜 E ⊗[𝕜] F) :
    toOperator 𝕜 E F ⟨u⟩ = TensorProduct.toOperator u := by
  simp [toOperator]

/-- Every tensor induces an operator with finitely generated range. -/
theorem hasFiniteRange_toOperator (u : InjectiveTensor 𝕜 (StrongDual 𝕜 E) F) :
    (toOperator 𝕜 E F u).toLinearMap.HasFiniteRange := by
  obtain ⟨u⟩ := u
  induction u with
  | tmul f y =>
    have h : (toOperator 𝕜 E F ⟨f ⊗ₜ y⟩).toLinearMap =
        (ContinuousLinearMap.toSpanSingleton 𝕜 y).toLinearMap ∘ₗ f.toLinearMap := by
      ext x
      simp
    rw [h]
    exact LinearMap.HasFiniteRange.of_finite_dom.comp_right _
  | add u v hu hv =>
    simpa using hu.add hv

/-- Every finite-rank bounded operator has an algebraic tensor representation. -/
theorem mem_range_toOperator_iff (T : E →L[𝕜] F) :
    T ∈ (toOperator 𝕜 E F).toLinearMap.range ↔ T.toLinearMap.HasFiniteRange := by
  constructor
  · rintro ⟨u, rfl⟩
    exact hasFiniteRange_toOperator u
  · intro hT
    have : Module.Finite 𝕜 T.toLinearMap.range := Module.Finite.iff_fg.mpr hT
    let b := Module.finBasis 𝕜 T.toLinearMap.range
    let f (i : Fin (Module.finrank 𝕜 T.toLinearMap.range)) : StrongDual 𝕜 E :=
      (LinearMap.toContinuousLinearMap (b.coord i)) ∘L T.rangeRestrict
    refine ⟨⟨∑ i, f i ⊗ₜ (b i : F)⟩, ?_⟩
    apply ContinuousLinearMap.ext
    intro x
    simp only [LinearIsometry.coe_toLinearMap, toOperator_mk, map_sum, sum_apply,
      TensorProduct.toOperator_tmul, ContinuousLinearMap.smulRight_apply]
    simp only [f, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply]
    simpa only [Submodule.coe_sum, Submodule.coe_smul,
      ContinuousLinearMap.coe_codRestrict_apply] using
      congrArg Subtype.val (b.sum_repr (T.rangeRestrict x))

/-- The range of the algebraic embedding is exactly the finite-rank bounded operators. -/
theorem range_toOperator :
    Set.range (toOperator 𝕜 E F) = {T : E →L[𝕜] F | T.toLinearMap.HasFiniteRange} := by
  ext T
  exact mem_range_toOperator_iff T

end InjectiveTensor

namespace CompletedInjectiveTensor

variable [CompleteSpace F]

variable (𝕜 E F) in
/-- The canonical isometric embedding of `E* ⊗̂ε F` into bounded operators, obtained by
extending the finite-rank tensor representation in operator norm. -/
noncomputable def toOperator :
    CompletedInjectiveTensor 𝕜 (StrongDual 𝕜 E) F →ₗᵢ[𝕜] E →L[𝕜] F :=
  (InjectiveTensor.toOperator 𝕜 E F).toLinearMap.extendOfIsometry
    (σ₁₂ := RingHom.id 𝕜)
    (e := (Completion.toComplₗᵢ : InjectiveTensor 𝕜 (StrongDual 𝕜 E) F →ₗᵢ[𝕜]
      CompletedInjectiveTensor 𝕜 (StrongDual 𝕜 E) F).toLinearMap)
    Completion.denseRange_coe (fun u ↦ by simp)

/-- The completed embedding agrees with the algebraic one on algebraic tensors. -/
@[simp]
theorem toOperator_coe (u : InjectiveTensor 𝕜 (StrongDual 𝕜 E) F) :
    toOperator 𝕜 E F u = InjectiveTensor.toOperator 𝕜 E F u :=
  LinearMap.extendOfIsometry_eq _ _ _ _

/-- The completed injective tensor product represents exactly the operator-norm closure of
the finite-rank operators. -/
theorem range_toOperator :
    Set.range (toOperator 𝕜 E F) =
      closure {T : E →L[𝕜] F | T.toLinearMap.HasFiniteRange} := by
  rw [← InjectiveTensor.range_toOperator]
  have hrange : Set.range (InjectiveTensor.toOperator 𝕜 E F) =
      (toOperator 𝕜 E F) '' Set.range
        (Completion.toComplₗᵢ : InjectiveTensor 𝕜 (StrongDual 𝕜 E) F →ₗᵢ[𝕜]
          CompletedInjectiveTensor 𝕜 (StrongDual 𝕜 E) F) := by
    rw [← Set.range_comp]
    congr 1
    funext u
    exact (toOperator_coe u).symm
  have hd : DenseRange
      (Completion.toComplₗᵢ : InjectiveTensor 𝕜 (StrongDual 𝕜 E) F →ₗᵢ[𝕜]
        CompletedInjectiveTensor 𝕜 (StrongDual 𝕜 E) F) := Completion.denseRange_coe
  rw [hrange, (toOperator 𝕜 E F).isometry.isClosedEmbedding.closure_image_eq,
    hd.closure_range, Set.image_univ]

end CompletedInjectiveTensor

end TauCeti

namespace TauCeti.ProjectiveTensor

section ToOperator

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
/-- Canonical contraction from the projective tensor product `StrongDual 𝕜 E ⊗π F` to bounded
operators `E →L[𝕜] F`, sending `⟨f ⊗ₜ y⟩` to `x ↦ f x • y`. -/
noncomputable def toOperator : ProjectiveTensor 𝕜 (StrongDual 𝕜 E) F →L[𝕜] E →L[𝕜] F :=
  liftIsometry 𝕜 (StrongDual 𝕜 E) F (E →L[𝕜] F) (ContinuousLinearMap.smulRightL 𝕜 E F)

/-- On wrapped algebraic tensors, `ProjectiveTensor.toOperator` agrees with
`TensorProduct.toOperator`. -/
@[simp] theorem toOperator_mk (u : StrongDual 𝕜 E ⊗[𝕜] F) :
    toOperator 𝕜 E F ⟨u⟩ = TensorProduct.toOperator u := by
  rw [toOperator, liftIsometry_apply, TensorProduct.toOperator]; rfl

/-- `ProjectiveTensor.toOperator` sends a pure tensor `⟨f ⊗ₜ y⟩` to the rank-one operator
`f.smulRight y`. -/
theorem toOperator_tmul (f : StrongDual 𝕜 E) (y : F) :
    toOperator 𝕜 E F ⟨f ⊗ₜ y⟩ = f.smulRight y := by simp

/-- The canonical operator `StrongDual 𝕜 E ⊗π F →L[𝕜] E →L[𝕜] F` is a contraction. -/
theorem norm_toOperator_le : ‖toOperator 𝕜 E F‖ ≤ 1 := by
  -- `ContinuousLinearMap.norm_smulRightL_le` assumes `NormedAddCommGroup`.
  rw [toOperator, LinearIsometryEquiv.norm_map]
  exact ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one fun _ _ ↦ by simp

end ToOperator

end TauCeti.ProjectiveTensor
