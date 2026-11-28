/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Dilation of Schwartz functions by a commutative group

Let `G` be a commutative group acting continuously and `ℝ`-linearly on a real normed space `E`,
for instance the units of `ℝ` or `ℂ` acting on a normed space over it. An element `a ∈ G` acts on
Schwartz functions on `E` by dilation of the variable,

`r(a) f (x) = f (a • x)`,

and this is a continuous linear map of Schwartz space (`SchwartzMap.compSMulCLM`). Since `G` is
commutative, `r(a b) = r(a) ∘ r(b)`, so `r` is a homomorphism from `G` to the monoid of
continuous linear endomorphisms of `𝓢(E, F)`: a group action of `G` on Schwartz space by
continuous linear automorphisms. For `G = Fˣ` and `E = F = ℝ` or `ℂ` this is the action
`r(a) f (x) = f (x a)` of `Fˣ` on the Schwartz–Bruhat space of an archimedean local field `F` in
Tate's thesis, which underlies the eigendistributions of Tate's local theory. Its transpose acts
on tempered distributions (`TemperedDistribution.contragredientSMul`).

## Main definitions

* `SchwartzMap.compSMulCLM`: the action `r(a) f = f (a • ·)` of `G` on `𝓢(E, F)`.
* `SchwartzMap.dilate`: the specialization of this action to nonzero real scalars.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, §2.2.
* S. S. Kudla, *Tate's thesis*, in *An introduction to the Langlands program*, §3.
-/

public noncomputable section

namespace SchwartzMap

section

variable (𝕜' : Type*) {G E F : Type*} [CommGroup G] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DistribMulAction G E] [ContinuousConstSMul G E] [SMulCommClass G ℝ E]
  [RCLike 𝕜'] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜' F]

/-- The **dilation action** of a commutative group `G` on Schwartz functions,
`r(a) f (x) = f (a • x)`, as a homomorphism from `G` to the monoid of continuous linear
endomorphisms of `𝓢(E, F)`. -/
def compSMulCLM : G →* (𝓢(E, F) →L[𝕜'] 𝓢(E, F)) where
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
theorem compSMulCLM_apply (a : G) (f : 𝓢(E, F)) (x : E) :
    compSMulCLM 𝕜' a f x = f (a • x) :=
  (rfl)

end

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Precompose a Schwartz function with multiplication by a nonzero real scalar. -/
def dilate (f : 𝓢(E, F)) {c : ℝ} (hc : c ≠ 0) : 𝓢(E, F) :=
  compSMulCLM ℝ (Units.mk0 c hc) f

/-- A dilated Schwartz function is evaluated at the rescaled argument. -/
@[simp]
theorem dilate_apply (f : 𝓢(E, F)) {c : ℝ} (hc : c ≠ 0) (x : E) : f.dilate hc x = f (c • x) := by
  rw [dilate, compSMulCLM_apply, Units.smul_def, Units.val_mk0]

/-- As a function, dilation is precomposition by scalar multiplication. -/
theorem coe_dilate (f : 𝓢(E, F)) {c : ℝ} (hc : c ≠ 0) : (f.dilate hc : E → F) = fun x ↦ f (c • x) :=
  funext (f.dilate_apply hc)

/-- Dilation by `1` fixes every Schwartz function. -/
@[simp]
theorem dilate_one (f : 𝓢(E, F)) : f.dilate (c := 1) one_ne_zero = f := by
  ext x
  simp only [dilate_apply, one_smul]

/-- Successive dilations multiply their scales. -/
@[simp]
theorem dilate_dilate (f : 𝓢(E, F)) {c d : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) :
    (f.dilate hc).dilate hd = f.dilate (mul_ne_zero hc hd) := by
  ext x
  simp only [dilate_apply, mul_smul]

end SchwartzMap
