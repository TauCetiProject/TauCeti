/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Bounded scalar actions and derivatives of pullbacks of alternating maps

A bounded scalar action on the coefficients induces a bounded scalar action on continuous
alternating maps, by the corresponding operator-norm estimate for multilinear maps.

For `f : F' [⋀^ι]→L[𝕜] G` and `A : F →L[𝕜] F'`, Mathlib's
`ContinuousAlternatingMap.fderivCompContinuousLinearMap f A` is the derivative of
`h ↦ f.compContinuousLinearMap h` at `A`. This derivative is natural under precomposition with
`g : E →L[𝕜] F`: at `A ∘ g`, in the direction `B ∘ g`, it is the pullback along `g` of the
derivative at `A` in the direction `B`,

`f.fderivCompContinuousLinearMap (A ∘ g) (B ∘ g) = (f.fderivCompContinuousLinearMap A B) ∘ g`.

For `A` the identity of `F`, the right-hand side pulls back along `g` the action of the endomorphism
`B` of `F` on `f` as a derivation. This is the form in which the derivation action of the
derivative of a vector field, the second term of the Lie derivative of a differential form,
appears when a pullback along a flow is differentiated in time.
-/

public section

namespace ContinuousAlternatingMap

/-- A bounded scalar action on the coefficients induces one on continuous alternating maps. -/
instance instIsBoundedSMul {𝕜 R E F ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [SeminormedRing R] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [Module R F] [IsBoundedSMul R F]
    [SMulCommClass 𝕜 R F] : IsBoundedSMul R (E [⋀^ι]→L[𝕜] F) :=
  .of_norm_smul_le fun c f ↦ f.toContinuousMultilinearMap.opNorm_smul_le c

variable {𝕜 E F F' G ι : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup F']
  [NormedSpace 𝕜 F'] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [Fintype ι] [DecidableEq ι]

/-- The derivative of the pullback is natural under precomposition: at `A ∘ g`, in the direction
`B ∘ g`, it is the pullback along `g` of the derivative at `A` in the direction `B`. -/
theorem fderivCompContinuousLinearMap_comp_comp (f : F' [⋀^ι]→L[𝕜] G) (A B : F →L[𝕜] F')
    (g : E →L[𝕜] F) :
    f.fderivCompContinuousLinearMap (A ∘L g) (B ∘L g) =
      (f.fderivCompContinuousLinearMap A B).compContinuousLinearMap g := by
  ext v
  simp only [fderivCompContinuousLinearMap_apply, compContinuousLinearMap_apply]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg f (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [Function.update_of_ne hj]

/-- The derivative of the pullback at `g` in the direction `B ∘ g` is the pullback along `g` of the
derivative at the identity in the direction `B`: the case `A = id` of
`fderivCompContinuousLinearMap_comp_comp`. -/
theorem fderivCompContinuousLinearMap_comp (f : F [⋀^ι]→L[𝕜] G) (g : E →L[𝕜] F)
    (B : F →L[𝕜] F) :
    f.fderivCompContinuousLinearMap g (B ∘L g) =
      (f.fderivCompContinuousLinearMap (.id 𝕜 F) B).compContinuousLinearMap g := by
  simpa using f.fderivCompContinuousLinearMap_comp_comp (.id 𝕜 F) B g

end ContinuousAlternatingMap
