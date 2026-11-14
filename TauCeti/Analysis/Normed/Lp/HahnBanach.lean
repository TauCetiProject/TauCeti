/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Hahn–Banach extension into scalar-valued `ℓ∞`

An operator from a subspace into scalar-valued `ℓ∞` extends to the whole space without changing
its norm (`Submodule.exists_extension_lpInfty_norm_eq`). This is the extension property of `ℓ∞`
over `ℝ` or `ℂ`: apply Mathlib's scalar extension theorem `exists_extension_norm_eq` to each
coordinate and assemble the resulting functionals with `ContinuousLinearMap.piLpInfty`.
-/

public section

open scoped ENNReal

namespace Submodule

variable {𝕜 X ι : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- An operator into scalar-valued `ℓ∞` extends from any subspace with the same norm. -/
theorem exists_extension_lpInfty_norm_eq (M : Submodule 𝕜 X)
    (f : M →L[𝕜] lp (fun _ : ι ↦ 𝕜) ∞) :
    ∃ g : X →L[𝕜] lp (fun _ : ι ↦ 𝕜) ∞, g ∘L M.subtypeL = f ∧ ‖g‖ = ‖f‖ := by
  have h (i : ι) : ∃ g : StrongDual 𝕜 X, (∀ x : M, g x = f x i) ∧ ‖g‖ ≤ ‖f‖ := by
    obtain ⟨g, hg, hnorm⟩ := _root_.exists_extension_norm_eq M
      (lp.evalCLM 𝕜 (fun _ : ι ↦ 𝕜) ∞ i ∘L f)
    refine ⟨g, fun x ↦ by simpa using hg x, hnorm ▸ ?_⟩
    exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun x ↦ by
      simpa using (lp.norm_apply_le_norm (by simp) (f x) i).trans (f.le_opNorm x)
  choose g hg hnorm using h
  let G := ContinuousLinearMap.piLpInfty g (bddAbove_def.2 ⟨‖f‖, Set.forall_mem_range.2 hnorm⟩)
  have hG : G ∘L M.subtypeL = f := by
    ext x i
    simpa [G] using hg i x
  refine ⟨G, hG, (ContinuousLinearMap.norm_piLpInfty_le _ (norm_nonneg f) hnorm).antisymm ?_⟩
  calc
    ‖f‖ = ‖G ∘L M.subtypeL‖ := by rw [hG]
    _ ≤ ‖G‖ * ‖M.subtypeL‖ := G.opNorm_comp_le M.subtypeL
    _ ≤ ‖G‖ := mul_le_of_le_one_right (norm_nonneg G) M.norm_subtypeL_le

end Submodule
