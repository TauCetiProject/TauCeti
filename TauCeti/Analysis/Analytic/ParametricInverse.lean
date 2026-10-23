/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Inverse
public import TauCeti.Analysis.Calculus.ParametricInverse

/-!
# The analytic implicit function theorem with a varying level

Let `f : E₁ × E₂ → F` be strictly differentiable at `u`, with invertible partial derivative in
the second variable. The map `HasStrictFDerivAt.localInverseOfProdDomain` of
`TauCeti.Analysis.Calculus.ParametricInverse` solves `f (z, v) = w` for `v` jointly in the
parameter `z` and the level `w`. This file shows that it is jointly analytic at `(u.1, f u)` when
`f` is analytic at `u`, over any complete nontrivially normed field. The proof reads it off
`ImplicitFunctionData.analyticAt_implicitFunction`, which is joint in both arguments of the
implicit function.

## Main results

* `HasStrictFDerivAt.analyticAt_uncurry_localInverseOfProdDomain`: the **analytic implicit
  function theorem with a varying level**.

## References

* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Prentice-Hall
  (1965), Chapter I (the holomorphic inverse and implicit function theorems).
-/

public section

open Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

namespace HasStrictFDerivAt

variable {u : E₁ × E₂} {f : E₁ × E₂ → F} {f'u : E₁ × E₂ →L[𝕜] F}
  (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible)

/-- **The analytic implicit function theorem with a varying level.** If `f` is analytic at `u`,
then `localInverseOfProdDomain` is jointly analytic in the parameter and the level at
`(u.1, f u)`. -/
theorem analyticAt_uncurry_localInverseOfProdDomain (hf : AnalyticAt 𝕜 f u) :
    AnalyticAt 𝕜 (uncurry (dfu.localInverseOfProdDomain if₂u)) (u.1, f u) := by
  set φ : ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁ := dfu.implicitFunctionDataOfProdDomain if₂u
  have h : AnalyticAt 𝕜 (uncurry φ.implicitFunction) (u.1, f u).swap := by
    have hpt : φ.prodFun φ.pt = (u.1, f u).swap := by simp [φ]
    rw [← hpt]
    exact φ.analyticAt_implicitFunction (by simpa [φ] using hf) (by simpa [φ] using analyticAt_fst)
  rw [uncurry_localInverseOfProdDomain]
  exact analyticAt_snd.comp (h.comp (analyticAt_snd.prod analyticAt_fst))

end HasStrictFDerivAt

end
