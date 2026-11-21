/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Dilation of Schwartz functions by units

Let `𝕜` be a commutative ring acting continuously and `ℝ`-linearly on a real normed space `E`,
for instance `ℝ` or `ℂ` acting on a normed space over it. A unit `a ∈ 𝕜ˣ` acts on Schwartz
functions on `E` by dilation of the variable,

`r(a) f (x) = f (a • x)`,

and this is a continuous linear map of Schwartz space (`SchwartzMap.compSMulCLM`). Since `𝕜` is
commutative, `r(a b) = r(a) ∘ r(b)`, so `r` is a homomorphism from `𝕜ˣ` to the monoid of
continuous linear endomorphisms of `𝓢(E, F)`: a group action of `𝕜ˣ` on Schwartz space by
continuous linear automorphisms. For `E = 𝕜 = ℝ` or `ℂ` this is the action `r(a) f (x) = f (x a)`
of `Fˣ` on the Schwartz–Bruhat space of an archimedean local field `F` in Tate's thesis, which
underlies the eigendistributions of Tate's local theory. Its transpose acts on tempered
distributions (`TemperedDistribution.contragredientSMul`).

## Main definitions

* `SchwartzMap.compSMulCLM`: the action `r(a) f = f (a • ·)` of `𝕜ˣ` on `𝓢(E, F)`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, §2.2.
* S. S. Kudla, *Tate's thesis*, in *An introduction to the Langlands program*, §3.
-/

public noncomputable section

namespace SchwartzMap

variable (𝕜' : Type*) {𝕜 E F : Type*} [CommRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module 𝕜 E] [ContinuousConstSMul 𝕜 E] [SMulCommClass 𝕜 ℝ E]
  [RCLike 𝕜'] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜' F]

/-- The **dilation action** of the units of `𝕜` on Schwartz functions,
`r(a) f (x) = f (a • x)`, as a homomorphism from `𝕜ˣ` to the monoid of continuous linear
endomorphisms of `𝓢(E, F)`. -/
def compSMulCLM : 𝕜ˣ →* (𝓢(E, F) →L[𝕜'] 𝓢(E, F)) where
  toFun a := compCLMOfContinuousLinearEquiv 𝕜' (ContinuousLinearEquiv.smulLeft a : E ≃L[ℝ] E)
  map_one' := by
    ext f x
    simp only [compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.smulLeft_apply_apply, one_smul, one_apply_eq_self]
  map_mul' a b := by
    ext f x
    simp only [compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.smulLeft_apply_apply, mul_apply_eq_comp, mul_comm a b,
      mul_smul]

/-- The dilation action evaluates as `r(a) f (x) = f (a • x)`. -/
@[simp]
theorem compSMulCLM_apply (a : 𝕜ˣ) (f : 𝓢(E, F)) (x : E) :
    compSMulCLM 𝕜' a f x = f (a • x) :=
  (rfl)

end SchwartzMap
