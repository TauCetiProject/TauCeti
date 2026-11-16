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
`E ⊗[𝕜] F` are definite norms, and `TauCeti.ProjectiveTensor.toOperator 𝕜 E F` upgrades to a
continuous linear equivalence `TauCeti.ProjectiveTensor.toOperatorEquiv`.

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

/-- When `E` is finite-dimensional over a complete nontrivially normed field `𝕜`,
`contractStrongDual 𝕜 E F` is bijective. -/
theorem contractStrongDual_bijective_of_finiteDimensional :
    Function.Bijective (contractStrongDual 𝕜 E F) :=
  contractStrongDualEquiv_toLinearMap (𝕜 := 𝕜) (E := E) (F := F) ▸
    (contractStrongDualEquiv 𝕜 E F).bijective

/-- Under the finite-dimensional identification `Module.Dual 𝕜 E ≃ₗ[𝕜] StrongDual 𝕜 E`,
`TensorProduct.toOperator` recovers the algebraic contraction `dualTensorHom 𝕜 E F`. -/
theorem toLinearMap_toOperator_congr (v : Module.Dual 𝕜 E ⊗[𝕜] F) :
    (toOperator (TensorProduct.congr
      (LinearMap.toContinuousLinearMap : Module.Dual 𝕜 E ≃ₗ[𝕜] StrongDual 𝕜 E)
      (LinearEquiv.refl 𝕜 F) v)).toLinearMap = dualTensorHom 𝕜 E F v := by
  induction v with
  | tmul φ y => ext x; simp
  | add _ _ hv₁ hv₂ => simp [hv₁, hv₂]

end SeminormedRight

section Normed

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- When `E` is finite-dimensional over a complete nontrivially normed field `𝕜`, the injective
tensor seminorm on `E ⊗[𝕜] F` vanishes only at `0`. -/
theorem injectiveSeminorm_eq_zero_iff_of_finiteDimensional_left [FiniteDimensional 𝕜 E]
    {u : E ⊗[𝕜] F} : injectiveSeminorm 𝕜 E F u = 0 ↔ u = 0 := by
  rw [injectiveSeminorm_apply, ContinuousLinearMap.opNorm_zero_iff]
  exact LinearMap.map_eq_zero_iff _
    (contractStrongDual_bijective_of_finiteDimensional (𝕜 := 𝕜) (E := E) (F := F)).injective

/-- When `E` is finite-dimensional over a complete nontrivially normed field `𝕜`, the projective
tensor seminorm on `E ⊗[𝕜] F` vanishes only at `0`. -/
theorem projectiveSeminorm_eq_zero_iff_of_finiteDimensional_left [FiniteDimensional 𝕜 E]
    {u : E ⊗[𝕜] F} : projectiveSeminorm 𝕜 E F u = 0 ↔ u = 0 :=
  ⟨fun hu ↦ injectiveSeminorm_eq_zero_iff_of_finiteDimensional_left.1 <|
    le_antisymm ((injectiveSeminorm_le_projectiveSeminorm u).trans_eq hu) (apply_nonneg _ u),
    fun hu ↦ by simp [hu]⟩

end Normed

end TensorProduct

namespace TauCeti

/-- The projective tensor product of finitely generated seminormed `𝕜`-modules is finitely
generated. -/
instance ProjectiveTensor.instModuleFinite {𝕜 E F : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [Module.Finite 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [Module.Finite 𝕜 F] :
    Module.Finite 𝕜 (ProjectiveTensor 𝕜 E F) :=
  Module.Finite.equiv (ProjectiveTensor.linearEquiv 𝕜 E F).symm

section NormedFiniteDimensional

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- When `E` is finite-dimensional over a complete nontrivially normed field `𝕜`, the projective
tensor seminorm on `ProjectiveTensor 𝕜 E F` is definite, giving a `NormedAddCommGroup` structure. -/
noncomputable instance ProjectiveTensor.instNormedAddCommGroupOfFiniteDimensionalLeft
    [FiniteDimensional 𝕜 E] : NormedAddCommGroup (ProjectiveTensor 𝕜 E F) :=
  NormedAddCommGroup.ofSeparation fun _ hu ↦
    (ProjectiveTensor.linearEquiv 𝕜 E F).map_eq_zero_iff.1 <|
      TensorProduct.projectiveSeminorm_eq_zero_iff_of_finiteDimensional_left.1 hu

example {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
    (inferInstance : NormedAddCommGroup (ProjectiveTensor 𝕜 E F)) =
      ProjectiveTensor.instNormedAddCommGroupOfFiniteDimensionalLeft := rfl

end NormedFiniteDimensional

namespace ProjectiveTensor

section ToOperatorEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

private noncomputable def toOperatorInvOfBasis {ι : Type*} [Fintype ι]
    (b : Module.Basis ι 𝕜 E) : (E →L[𝕜] F) →L[𝕜] ProjectiveTensor 𝕜 (StrongDual 𝕜 E) F :=
  ∑ i, (tmulL 𝕜 (StrongDual 𝕜 E) F (LinearMap.toContinuousLinearMap (b.coord i))).comp
    (ContinuousLinearMap.apply 𝕜 F (b i))

private theorem toTensorProduct_toOperatorInvOfBasis {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι 𝕜 E) (T : E →L[𝕜] F) :
    (toOperatorInvOfBasis b T).toTensorProduct = _root_.TensorProduct.congr
      (LinearMap.toContinuousLinearMap : Module.Dual 𝕜 E ≃ₗ[𝕜] StrongDual 𝕜 E) (.refl 𝕜 F)
      ((dualTensorHomEquivOfBasis b).symm T.toLinearMap) := by
  rw [← linearEquiv_apply]; simp [toOperatorInvOfBasis, dualTensorHomEquivOfBasis]

variable (𝕜 E F) in
/-- When `E` is a finite-dimensional normed space over a complete nontrivially normed field `𝕜`,
`ProjectiveTensor.toOperator 𝕜 E F` is a continuous linear equivalence onto `E →L[𝕜] F` for any
seminormed `𝕜`-module `F`. -/
noncomputable def toOperatorEquiv : ProjectiveTensor 𝕜 (StrongDual 𝕜 E) F ≃L[𝕜] E →L[𝕜] F :=
  let b := Module.Basis.ofVectorSpace 𝕜 E
  letI := FiniteDimensional.fintypeBasisIndex b
  letI : DecidableEq (Module.Basis.ofVectorSpaceIndex 𝕜 E) := Classical.decEq _
  let c : Module.Dual 𝕜 E ⊗[𝕜] F ≃ₗ[𝕜] StrongDual 𝕜 E ⊗[𝕜] F :=
    _root_.TensorProduct.congr LinearMap.toContinuousLinearMap (LinearEquiv.refl 𝕜 F)
  ContinuousLinearEquiv.equivOfInverse (toOperator 𝕜 E F) (toOperatorInvOfBasis b)
    (fun ⟨u⟩ ↦ (linearEquiv 𝕜 (StrongDual 𝕜 E) F).injective <| by
      obtain ⟨v, rfl⟩ := c.surjective u
      rw [linearEquiv_apply, linearEquiv_apply, toTensorProduct_toOperatorInvOfBasis b,
        toOperator_mk, TensorProduct.toLinearMap_toOperator_congr,
        dualTensorHomEquivOfBasis_symm_cancel_left])
    (fun T ↦ ContinuousLinearMap.coe_injective <| DFunLike.coe_injective <| by
      rcases hv : toOperatorInvOfBasis b T with ⟨w⟩
      have h : w = c ((dualTensorHomEquivOfBasis (N := F) b).symm T.toLinearMap) := by
        simpa [hv] using toTensorProduct_toOperatorInvOfBasis b T
      have hr := congrArg DFunLike.coe
        (dualTensorHomEquivOfBasis_symm_cancel_right b T.toLinearMap)
      rwa [← TensorProduct.toLinearMap_toOperator_congr, ← h, ← toOperator_mk] at hr)

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
