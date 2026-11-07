/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Analysis.Normed.Module.TensorProduct.Approximable

/-!
# Finite-dimensional normed tensor products and dual-tensor operator equivalences

Over a complete nontrivially normed field `𝕜`, finite dimensionality of `E` makes
`TensorProduct.contractStrongDual 𝕜 E F` a linear equivalence onto `StrongDual 𝕜 E →L[𝕜] F`
(`TensorProduct.contractStrongDualEquiv`), so both the injective and projective tensor seminorms on
`E ⊗[𝕜] F` are definite norms. Evaluating pure tensors as rank-one operators gives
`TauCeti.ProjectiveTensor.toOperator 𝕜 E F` and, when `E` is finite-dimensional, the continuous
linear equivalence `TauCeti.ProjectiveTensor.toOperatorEquiv`, as well as
`TauCeti.ProjectiveTensor.toInjectiveTensorEquiv` when both factors are finite-dimensional.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, §§2.1, 3.1.
* F. Trèves, *Topological Vector Spaces, Distributions and Kernels*, Academic Press, 1967, §43.
-/

public section

open scoped TensorProduct

namespace TensorProduct

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

section SeminormedRight

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
/-- When `E` is finite-dimensional over a complete nontrivially normed field `𝕜`, the contraction
`contractStrongDual 𝕜 E F` is a linear equivalence `E ⊗[𝕜] F ≃ₗ[𝕜] StrongDual 𝕜 E →L[𝕜] F`,
with no finite-dimensionality assumption on `F`. -/
noncomputable def contractStrongDualEquiv : E ⊗[𝕜] F ≃ₗ[𝕜] StrongDual 𝕜 E →L[𝕜] F :=
  let c : Module.Dual 𝕜 E ≃ₗ[𝕜] StrongDual 𝕜 E := LinearMap.toContinuousLinearMap
  have : FiniteDimensional 𝕜 (StrongDual 𝕜 E) := LinearEquiv.finiteDimensional c
  let evalStrong : E ≃ₗ[𝕜] Module.Dual 𝕜 (StrongDual 𝕜 E) :=
    (Module.evalEquiv 𝕜 E).trans (c.arrowCongr (LinearEquiv.refl 𝕜 𝕜))
  (TensorProduct.congr evalStrong (LinearEquiv.refl 𝕜 F)).trans <|
    (dualTensorHomEquiv 𝕜 (StrongDual 𝕜 E) F).trans LinearMap.toContinuousLinearMap

@[simp] theorem contractStrongDualEquiv_toLinearMap :
    (contractStrongDualEquiv 𝕜 E F).toLinearMap = contractStrongDual 𝕜 E F := by
  refine TensorProduct.ext' fun x y ↦ ?_; ext f
  simp [contractStrongDualEquiv, LinearEquiv.arrowCongr_apply]

@[simp] theorem contractStrongDualEquiv_apply (u : E ⊗[𝕜] F) :
    contractStrongDualEquiv 𝕜 E F u = contractStrongDual 𝕜 E F u :=
  LinearMap.congr_fun contractStrongDualEquiv_toLinearMap u

theorem contractStrongDual_bijective_of_finiteDimensional :
    Function.Bijective (contractStrongDual 𝕜 E F) :=
  contractStrongDualEquiv_toLinearMap (𝕜 := 𝕜) (E := E) (F := F) ▸
    (contractStrongDualEquiv 𝕜 E F).bijective

end SeminormedRight

section Normed

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem injectiveSeminorm_eq_zero_iff_of_finiteDimensional_left [FiniteDimensional 𝕜 E]
    {u : E ⊗[𝕜] F} : injectiveSeminorm 𝕜 E F u = 0 ↔ u = 0 := by
  rw [injectiveSeminorm_apply, ContinuousLinearMap.opNorm_zero_iff]
  exact LinearMap.map_eq_zero_iff _
    (contractStrongDual_bijective_of_finiteDimensional (𝕜 := 𝕜) (E := E) (F := F)).injective

theorem projectiveSeminorm_eq_zero_iff_of_finiteDimensional_left [FiniteDimensional 𝕜 E]
    {u : E ⊗[𝕜] F} : projectiveSeminorm 𝕜 E F u = 0 ↔ u = 0 :=
  ⟨fun hu ↦ injectiveSeminorm_eq_zero_iff_of_finiteDimensional_left.1 <|
    le_antisymm ((injectiveSeminorm_le_projectiveSeminorm u).trans_eq hu) (apply_nonneg _ u),
    fun hu ↦ by simp [hu]⟩

theorem projectiveSeminorm_eq_zero_iff_of_finiteDimensional_right [FiniteDimensional 𝕜 F]
    {u : E ⊗[𝕜] F} : projectiveSeminorm 𝕜 E F u = 0 ↔ u = 0 := by
  rw [← projectiveSeminorm_comm, projectiveSeminorm_eq_zero_iff_of_finiteDimensional_left,
    LinearEquiv.map_eq_zero_iff]

end Normed

end TensorProduct

namespace TauCeti

instance ProjectiveTensor.instModuleFinite {𝕜 E F : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [Module.Finite 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [Module.Finite 𝕜 F] :
    Module.Finite 𝕜 (ProjectiveTensor 𝕜 E F) :=
  Module.Finite.equiv (ProjectiveTensor.linearEquiv 𝕜 E F).symm

instance InjectiveTensor.instModuleFinite {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [Module.Finite 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [Module.Finite 𝕜 F] :
    Module.Finite 𝕜 (InjectiveTensor 𝕜 E F) :=
  Module.Finite.equiv (InjectiveTensor.linearEquiv 𝕜 E F).symm

section NormedFiniteDimensional

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

noncomputable instance ProjectiveTensor.instNormedAddCommGroupOfFiniteDimensionalLeft
    [FiniteDimensional 𝕜 E] : NormedAddCommGroup (ProjectiveTensor 𝕜 E F) :=
  NormedAddCommGroup.ofSeparation fun _ hu ↦
    (ProjectiveTensor.linearEquiv 𝕜 E F).map_eq_zero_iff.1 <|
      TensorProduct.projectiveSeminorm_eq_zero_iff_of_finiteDimensional_left.1 hu

noncomputable instance InjectiveTensor.instNormedAddCommGroupOfFiniteDimensionalLeft
    [FiniteDimensional 𝕜 E] : NormedAddCommGroup (InjectiveTensor 𝕜 E F) :=
  NormedAddCommGroup.ofSeparation fun _ hu ↦
    (InjectiveTensor.linearEquiv 𝕜 E F).map_eq_zero_iff.1 <|
      TensorProduct.injectiveSeminorm_eq_zero_iff_of_finiteDimensional_left.1 hu

example {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
    (ProjectiveTensor.instNormedAddCommGroupOfFiniteDimensionalLeft :
      NormedAddCommGroup (ProjectiveTensor 𝕜 E F)) =
      inferInstanceAs (NormedAddCommGroup (ProjectiveTensor 𝕜 E F)) := rfl

section BothFiniteDimensional

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- Between finite-dimensional normed spaces over a complete nontrivially normed field, the
contraction from the projective to the injective tensor product is a continuous linear
equivalence. -/
noncomputable def ProjectiveTensor.toInjectiveTensorEquiv :
    ProjectiveTensor 𝕜 E F ≃L[𝕜] InjectiveTensor 𝕜 E F :=
  LinearEquiv.toContinuousLinearEquiv
    ((ProjectiveTensor.linearEquiv 𝕜 E F).trans (InjectiveTensor.linearEquiv 𝕜 E F).symm)

@[simp] theorem ProjectiveTensor.toInjectiveTensorEquiv_toContinuousLinearMap :
    (ProjectiveTensor.toInjectiveTensorEquiv (𝕜 := 𝕜) (E := E) (F := F)).toContinuousLinearMap =
      ProjectiveTensor.toInjectiveTensor 𝕜 E F := by
  ext u; simp [ProjectiveTensor.toInjectiveTensorEquiv]

@[simp] theorem ProjectiveTensor.toInjectiveTensorEquiv_apply (u : ProjectiveTensor 𝕜 E F) :
    ProjectiveTensor.toInjectiveTensorEquiv u = ⟨u.toTensorProduct⟩ := by
  simp [ProjectiveTensor.toInjectiveTensorEquiv]

@[simp] theorem ProjectiveTensor.toInjectiveTensorEquiv_symm_apply (u : InjectiveTensor 𝕜 E F) :
    (ProjectiveTensor.toInjectiveTensorEquiv (𝕜 := 𝕜) (E := E) (F := F)).symm u =
      ⟨u.toTensorProduct⟩ := by simp [ProjectiveTensor.toInjectiveTensorEquiv]

end BothFiniteDimensional

end NormedFiniteDimensional

namespace ProjectiveTensor

section ToOperator

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
/-- Canonical contraction from the projective tensor product `StrongDual 𝕜 E ⊗π F` to bounded
operators `E →L[𝕜] F`, sending `⟨f ⊗ₜ y⟩` to `x ↦ f x • y`. -/
noncomputable def toOperator : ProjectiveTensor 𝕜 (StrongDual 𝕜 E) F →L[𝕜] E →L[𝕜] F :=
  LinearMap.mkContinuous
    (TensorProduct.toOperator ∘ₗ (linearEquiv 𝕜 (StrongDual 𝕜 E) F).toLinearMap) 1 fun u ↦ by
      simpa [norm_def] using TensorProduct.apply_le_mul_projectiveSeminorm
        (p := normSeminorm 𝕜 (E →L[𝕜] F)) (f := TensorProduct.toOperator) zero_le_one
        (fun f y ↦ by simp) u.toTensorProduct

@[simp] theorem toOperator_mk (u : StrongDual 𝕜 E ⊗[𝕜] F) :
    toOperator 𝕜 E F ⟨u⟩ = TensorProduct.toOperator u := by simp [toOperator]

theorem toOperator_tmul (f : StrongDual 𝕜 E) (y : F) :
    toOperator 𝕜 E F ⟨f ⊗ₜ y⟩ = f.smulRight y := by simp

theorem norm_toOperator_le : ‖toOperator 𝕜 E F‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end ToOperator

section ToOperatorEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
/-- When `E` is a finite-dimensional normed space over a complete nontrivially normed field `𝕜`,
`ProjectiveTensor.toOperator 𝕜 E F` is a continuous linear equivalence onto `E →L[𝕜] F` for any
seminormed `𝕜`-module `F`. -/
noncomputable def toOperatorEquiv : ProjectiveTensor 𝕜 (StrongDual 𝕜 E) F ≃L[𝕜] E →L[𝕜] F := by
  let b := Module.Basis.ofVectorSpace 𝕜 E
  letI := FiniteDimensional.fintypeBasisIndex b
  let inv : (E →L[𝕜] F) →L[𝕜] ProjectiveTensor 𝕜 (StrongDual 𝕜 E) F :=
    ∑ i, (tmulL 𝕜 (StrongDual 𝕜 E) F (LinearMap.toContinuousLinearMap (b.coord i))).comp
      (ContinuousLinearMap.apply 𝕜 F (b i))
  have hleft : inv.comp (toOperator 𝕜 E F) = ContinuousLinearMap.id 𝕜 _ := by
    refine continuousLinearMap_ext fun f y ↦ (linearEquiv 𝕜 (StrongDual 𝕜 E) F).injective ?_
    simp only [inv, ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.id_apply,
      toOperator_tmul, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.smulRight_apply, map_sum, map_smul, tmulL_apply, linearEquiv_apply,
      TensorProduct.smul_tmul', ← TensorProduct.sum_tmul]
    refine congrArg (fun g : StrongDual 𝕜 E ↦ g ⊗ₜ[𝕜] y) ?_; ext x
    simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.sum_apply, LinearMap.smul_apply,
      Module.Basis.coord_apply, smul_eq_mul, mul_comm (f _), ← map_smul, ← map_sum]
    simpa only [map_sum, map_smul, smul_eq_mul] using congrArg f (b.sum_repr x)
  refine ContinuousLinearEquiv.equivOfInverse (toOperator 𝕜 E F) inv
    (fun u ↦ DFunLike.congr_fun hleft u) fun T ↦ ?_
  simp only [inv, sum_apply, map_sum]; ext x
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.apply_apply, tmulL_apply, toOperator_tmul,
    ContinuousLinearMap.smulRight_apply, LinearMap.coe_toContinuousLinearMap',
    Module.Basis.coord_apply, ← map_smul, ← map_sum]
  exact congrArg T (b.sum_repr x)

@[simp] theorem toOperatorEquiv_toContinuousLinearMap :
    (toOperatorEquiv 𝕜 E F).toContinuousLinearMap = toOperator 𝕜 E F := (rfl)

@[simp] theorem toOperatorEquiv_mk (u : StrongDual 𝕜 E ⊗[𝕜] F) :
    toOperatorEquiv 𝕜 E F ⟨u⟩ = TensorProduct.toOperator u := toOperator_mk u

theorem toOperatorEquiv_tmul (f : StrongDual 𝕜 E) (y : F) :
    toOperatorEquiv 𝕜 E F ⟨f ⊗ₜ y⟩ = f.smulRight y := toOperator_tmul f y

@[simp] theorem toOperatorEquiv_symm_smulRight (f : StrongDual 𝕜 E) (y : F) :
    (toOperatorEquiv 𝕜 E F).symm (f.smulRight y) = ⟨f ⊗ₜ y⟩ :=
  (toOperatorEquiv 𝕜 E F).symm_apply_eq.2 (toOperatorEquiv_tmul f y).symm

end ToOperatorEquiv

end ProjectiveTensor

end TauCeti
