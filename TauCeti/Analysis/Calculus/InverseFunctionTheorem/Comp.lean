/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Regularity read through a local diffeomorphism

Let `φ` be a `Cᵐ` map, `m ≠ 0`, whose derivative at `a` is invertible. If `f ∘ φ` is `Cⁿ` at `a`
for some `n ≤ m`, then `f` is `Cⁿ` at `φ a` (`ContDiffAt.of_comp_right`): near `φ a`, `f` is
`f ∘ φ` composed with the local inverse of `φ`, which is `Cᵐ` by the inverse function theorem
(`ContDiffAt.to_localInverse`). This is how smoothness of a map defined on a surface is read off in
a chart that covers its domain only up to a periodicity, such as the cylindrical chart of an end.
Together with the chain rule, `f ∘ φ` is then `Cⁿ` at `a` exactly when `f` is `Cⁿ` at `φ a`
(`ContDiffAt.contDiffAt_comp_iff`).
-/

public section

namespace ContDiffAt

variable {𝕂 : Type*} [RCLike 𝕂]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕂 G]

/-- **Regularity read through a local diffeomorphism.** If `φ` is `Cᵐ` at `a`, `m ≠ 0`, with an
invertible derivative there, and `f ∘ φ` is `Cⁿ` at `a` for some `n ≤ m`, then `f` is `Cⁿ` at
`φ a`. -/
theorem of_comp_right {f : F → G} {φ : E → F} {L : E ≃L[𝕂] F} {a : E} {m n : WithTop ℕ∞}
    (hf : ContDiffAt 𝕂 n (f ∘ φ) a) (hφ : ContDiffAt 𝕂 m φ a)
    (hφ' : HasFDerivAt φ (L : E →L[𝕂] F) a) (hm : m ≠ 0) (hnm : n ≤ m) :
    ContDiffAt 𝕂 n f (φ a) := by
  rw [← hφ.localInverse_apply_image hφ' hm] at hf
  refine (hf.comp _ ((hφ.to_localInverse hφ' hm).of_le hnm)).congr_of_eventuallyEq ?_
  filter_upwards [(hφ.hasStrictFDerivAt hφ' hm).eventually_right_inverse] with w hw
  exact congrArg f hw.symm

/-- **Precomposition with a local diffeomorphism.** If `φ` is `Cⁿ` at `a`, `n ≠ 0`, with an
invertible derivative there, then `f ∘ φ` is `Cⁿ` at `a` exactly when `f` is `Cⁿ` at `φ a`. -/
theorem contDiffAt_comp_iff {f : F → G} {φ : E → F} {L : E ≃L[𝕂] F} {a : E} {n : WithTop ℕ∞}
    (hφ : ContDiffAt 𝕂 n φ a) (hφ' : HasFDerivAt φ (L : E →L[𝕂] F) a) (hn : n ≠ 0) :
    ContDiffAt 𝕂 n (f ∘ φ) a ↔ ContDiffAt 𝕂 n f (φ a) :=
  ⟨fun hf ↦ hf.of_comp_right hφ hφ' hn le_rfl, fun hf ↦ hf.comp a hφ⟩

end ContDiffAt
