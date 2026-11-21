/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar

/-!
# Comparison of bounded and continuous-functional-calculus polar decompositions

For an invertible bounded endomorphism `g : (E →L[𝕜] E)ˣ` on a Hilbert space over `RCLike 𝕜`,
this file compares the abstract continuous-functional-calculus polar unitary `g.polarUnitary`
(`TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar`) with the Hilbert-space
polar factor `(g : E →L[𝕜] E).polarFactor` (`TauCeti.Analysis.InnerProductSpace.Polar.Bounded`).

## Main declarations

* `Units.coe_polarUnitary_eq_polarFactor`: `g.polarUnitary` agrees with
  `(g : E →L[𝕜] E).polarFactor` under any compatible real algebra structure on `E →L[𝕜] E`.
-/

public section

namespace Units

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- For an invertible endomorphism `g : (E →L[𝕜] E)ˣ`, the continuous-functional-calculus polar
unitary `g.polarUnitary` agrees with the Hilbert-space polar factor `(g : E →L[𝕜] E).polarFactor`,
under any compatible real algebra structure on `E →L[𝕜] E`. -/
theorem coe_polarUnitary_eq_polarFactor [Algebra ℝ (E →L[𝕜] E)]
    [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)] (g : (E →L[𝕜] E)ˣ) :
    (g.polarUnitary : E →L[𝕜] E) = (g : E →L[𝕜] E).polarFactor := by
  have hg : (g : E →L[𝕜] E).IsInvertible :=
    ContinuousLinearMap.isInvertible_iff_isUnit.2 g.isUnit
  let v : unitary (E →L[𝕜] E) :=
    ⟨(g : E →L[𝕜] E).polarFactor,
      ContinuousLinearMap.polarFactor_mem_unitary hg.injective hg.surjective.denseRange⟩
  exact congrArg Subtype.val <|
    g.polarUnitary_eq_of_mul_eq' (g : E →L[𝕜] E).modulus_nonneg (v := v)
      (g : E →L[𝕜] E).polarFactor_comp_modulus

end Units
