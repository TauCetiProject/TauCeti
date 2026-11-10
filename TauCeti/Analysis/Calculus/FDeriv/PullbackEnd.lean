/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# Pulling back endomorphism fields along open partial homeomorphisms

For an open partial homeomorphism `e : E → F` and a field `J : F → (F →L[𝕜] F)` of
endomorphisms, the pullback `(e^* J) p = (De_p)⁻¹ ∘ J (e p) ∘ De_p` is a field of endomorphisms
on the source of `e`. The inverse of `De_p` is written as the derivative of `e.symm` at `e p`,
so no inversion of operators is involved. When `J` is an almost complex structure, `e^* J` is
the structure that makes `e` complex linear, also written `(e⁻¹)_* J`.

Differentiating `e` and `e.symm` costs one derivative: if both are `C^(n+1)` and `J` is `C^n`,
the pullback is `C^n`.

## Main declarations

* `OpenPartialHomeomorph.pullbackEnd`: the pulled-back endomorphism field.
* `OpenPartialHomeomorph.contDiffOn_pullbackEnd`: the pullback costs one derivative.
* `OpenPartialHomeomorph.fderiv_comp_pullbackEnd`: the derivative of `e` intertwines the
  pullback with `J`.
* `OpenPartialHomeomorph.pullbackEnd_apply_pullbackEnd_apply`: the pullback of a field squaring
  to `-1` squares to `-1`.
-/

public noncomputable section

open scoped ContDiff

namespace OpenPartialHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {e : OpenPartialHomeomorph E F}

/-- The pullback `(e^* J) p = (De_p)⁻¹ ∘ J (e p) ∘ De_p` of an endomorphism field along an open
partial homeomorphism, as a field on its source. The inverse of `De_p` is written as the
derivative of `e.symm`, so no inversion of operators is involved. -/
def pullbackEnd (e : OpenPartialHomeomorph E F) (J : F → F →L[𝕜] F) (p : E) : E →L[𝕜] E :=
  (fderiv 𝕜 e.symm (e p)).comp ((J (e p)).comp (fderiv 𝕜 e p))

/-- Evaluate a pulled-back endomorphism field. -/
@[simp]
theorem pullbackEnd_apply (J : F → F →L[𝕜] F) (p v : E) :
    e.pullbackEnd J p v = fderiv 𝕜 e.symm (e p) (J (e p) (fderiv 𝕜 e p v)) := by
  simp only [pullbackEnd, ContinuousLinearMap.comp_apply]

/-- **Pulling back costs one derivative.** If an open partial homeomorphism and its inverse are
`C^ℓ` and the field `J` is `C^n` on the target with `n + 1 ≤ ℓ`, the pulled-back field is
`C^n` on the source. -/
theorem contDiffOn_pullbackEnd {J : F → F →L[𝕜] F} {ℓ n : ℕ∞ω}
    (he : ContDiffOn 𝕜 ℓ e e.source) (hes : ContDiffOn 𝕜 ℓ e.symm e.target)
    (hJ : ContDiffOn 𝕜 n J e.target) (hn : n + 1 ≤ ℓ) :
    ContDiffOn 𝕜 n (e.pullbackEnd J) e.source := by
  have he' := he.of_le (le_self_add.trans hn)
  exact ((hes.fderiv_of_isOpen e.open_target hn).comp he' e.mapsTo).clm_comp
    ((hJ.comp he' e.mapsTo).clm_comp (he.fderiv_of_isOpen e.open_source hn))

/-- The derivative of `e` intertwines the pulled-back field with `J`. -/
theorem fderiv_comp_pullbackEnd (J : F → F →L[𝕜] F) {p : E} (hp : p ∈ e.source)
    (he : DifferentiableAt 𝕜 e p) (hs : DifferentiableAt 𝕜 e.symm (e p)) :
    (fderiv 𝕜 e p).comp (e.pullbackEnd J p) = (J (e p)).comp (fderiv 𝕜 e p) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have h := e.fderiv_apply_fderiv_symm_apply (e.map_source hp) (by rwa [e.left_inv hp]) hs
    (J (e p) (fderiv 𝕜 e p v))
  rw [e.left_inv hp] at h
  simpa only [ContinuousLinearMap.comp_apply, pullbackEnd_apply] using h

/-- **The pullback of an almost complex structure is an almost complex structure.** If
`J (e p)` squares to `-1`, so does the pulled-back endomorphism at `p`. -/
theorem pullbackEnd_apply_pullbackEnd_apply {J : F → F →L[𝕜] F} {p : E} (hp : p ∈ e.source)
    (he : DifferentiableAt 𝕜 e p) (hs : DifferentiableAt 𝕜 e.symm (e p))
    (hsq : ∀ w, J (e p) (J (e p) w) = -w) (v : E) :
    e.pullbackEnd J p (e.pullbackEnd J p v) = -v := by
  have hd : DifferentiableAt 𝕜 e (e.symm (e p)) := by rwa [e.left_inv hp]
  have hright := e.fderiv_apply_fderiv_symm_apply (e.map_source hp) hd hs
  have hleft := e.fderiv_symm_apply_fderiv_apply (e.map_source hp) hd hs
  rw [e.left_inv hp] at hright hleft
  rw [pullbackEnd_apply, pullbackEnd_apply, hright, hsq, map_neg, hleft]

end OpenPartialHomeomorph
