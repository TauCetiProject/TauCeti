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

For `f : F [⋀^ι]→L[𝕜] G` and `g : E →L[𝕜] F`, Mathlib's
`ContinuousAlternatingMap.fderivCompContinuousLinearMap f g` is the derivative of
`h ↦ f.compContinuousLinearMap h` at `g`. In the direction `B ∘ g` of a composite with an
endomorphism `B` of `F`, it is the pullback along `g` of the same derivative at the identity, which
is the action of `B` on `f` as a derivation:

`f.fderivCompContinuousLinearMap g (B ∘ g) = (f.fderivCompContinuousLinearMap id B) ∘ g`.

This is the form in which the derivation action of the derivative of a vector field, the second
term of the Lie derivative of a differential form, appears when a pullback along a flow is
differentiated in time.
-/

public section

namespace ContinuousAlternatingMap

/-- A bounded scalar action on the coefficients induces one on continuous alternating maps. -/
instance instIsBoundedSMul {𝕜 R E F ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [SeminormedRing R] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [Module R F] [IsBoundedSMul R F]
    [SMulCommClass 𝕜 R F] : IsBoundedSMul R (E [⋀^ι]→L[𝕜] F) :=
  .of_norm_smul_le fun c f ↦ f.toContinuousMultilinearMap.opNorm_smul_le c

variable {𝕜 E F G ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] [Fintype ι] [DecidableEq ι]

/-- The derivative of the pullback at `g` in the direction `B ∘ g` is the pullback along `g` of the
derivative at the identity in the direction `B`. -/
theorem fderivCompContinuousLinearMap_comp (f : F [⋀^ι]→L[𝕜] G) (g : E →L[𝕜] F)
    (B : F →L[𝕜] F) :
    f.fderivCompContinuousLinearMap g (B ∘L g) =
      (f.fderivCompContinuousLinearMap (.id 𝕜 F) B).compContinuousLinearMap g := by
  ext v
  simp only [fderivCompContinuousLinearMap_apply, compContinuousLinearMap_apply]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg f (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [Function.update_of_ne hj]

end ContinuousAlternatingMap
