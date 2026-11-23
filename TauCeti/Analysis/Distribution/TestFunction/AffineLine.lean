/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Divergence
public import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Restricting a test function to an affine line

For a test function `ψ` on an open set `Ω` of a real normed space `E`, a point `y` and a nonzero
direction `e`, the restriction `t ↦ ψ (y + t • e)` is a test function on the open set of
parameters `{t | y + t • e ∈ Ω}` of the line (`TauCeti.lineTestFunction`), of the same smoothness.
For a scalar test function its derivative, the divergence on `ℝ`, is the directional derivative
`∂_e ψ` along the line (`TauCeti.divergenceCLM_lineTestFunction`).
-/

public section

open TopologicalSpace TestFunction LineDeriv
open scoped Distributions ContDiff

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {Ω : Opens E} {n : ℕ∞}

/-- The restriction `t ↦ ψ (y + t • e)` of a test function on `Ω` to the line through `y` in a
nonzero direction `e`, as a test function on the open set of parameters of the line lying in
`Ω`. -/
noncomputable def lineTestFunction (ψ : 𝓓^{n}(Ω, F)) (y e : E) (he : e ≠ 0) :
    𝓓^{n}(Opens.comap ⟨fun t : ℝ => y + t • e, by fun_prop⟩ Ω, F) :=
  ⟨fun t => ψ (y + t • e), ψ.contDiff.comp (contDiff_const.add (contDiff_id.smul contDiff_const)),
    ψ.hasCompactSupport.comp_isClosedEmbedding
      ((Homeomorph.addLeft y).isClosedEmbedding.comp (isClosedEmbedding_smul_left he)),
    (tsupport_comp_subset_preimage (ψ : E → F) (by fun_prop : Continuous fun t : ℝ => y + t • e))
      |>.trans fun _ ht => ψ.tsupport_subset ht⟩

/-- Evaluating the restriction of a test function to a line. -/
@[simp]
theorem lineTestFunction_apply (ψ : 𝓓^{n}(Ω, F)) (y e : E) (he : e ≠ 0) (t : ℝ) :
    lineTestFunction ψ y e he t = ψ (y + t • e) :=
  (rfl)

/-- The divergence of the restriction of a scalar test function `ψ` to a line is the derivative
`∂_e ψ` along it. -/
theorem divergenceCLM_lineTestFunction (ψ : 𝓓(Ω, ℝ)) (y e : E) (he : e ≠ 0) (t : ℝ) :
    divergenceCLM (lineTestFunction ψ y e he) t = ∂_{e} ψ (y + t • e) := by
  rw [divergenceCLM_apply_eq_deriv, lineDerivOp_apply_eq_fderiv]
  have hl : HasDerivAt (fun s : ℝ => y + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add y
  exact ((ψ.contDiff.differentiable (by simp) (y + t • e)).hasFDerivAt.comp_hasDerivAt t hl).deriv

end TauCeti
