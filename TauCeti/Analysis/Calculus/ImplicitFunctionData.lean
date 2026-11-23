/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Implicit
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Charts on level sets from implicit-function data

Mathlib's `ImplicitFunctionData` packages two strictly differentiable maps `leftFun : E → F` and
`rightFun : E → G` at a point `pt` whose derivatives are surjective with complementary kernels,
and `ImplicitFunctionData.toOpenPartialHomeomorph` is the local homeomorphism
`x ↦ (leftFun x, rightFun x)` near `pt`. Restricting it to the level set `{x | leftFun x = c}`
through `pt` shows that `rightFun` is a chart of that level set at `pt`
(`ImplicitFunctionData.exists_openPartialHomeomorph_levelSet`).

## Main results

* `ImplicitFunctionData.exists_openPartialHomeomorph_levelSet`: on a level set of the left
  function of implicit-function data, the right function is a local homeomorphism at the base
  point.
-/

public section

namespace ImplicitFunctionData

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

/-- **Implicit function theorem on a level set.** On the level set of the left function of
implicit-function data through the base point, the right function agrees with an open partial
homeomorphism onto an open subset of `G` whose source contains the base point. -/
theorem exists_openPartialHomeomorph_levelSet (φ : ImplicitFunctionData 𝕜 E F G) {c : F}
    (hc : φ.leftFun φ.pt = c) :
    ∃ e : OpenPartialHomeomorph {x | φ.leftFun x = c} G,
      ⟨φ.pt, hc⟩ ∈ e.source ∧ ∀ x, e x = φ.rightFun x.val := by
  let Φ := φ.toOpenPartialHomeomorph
  have hΦ (x : E) : Φ x = (φ.leftFun x, φ.rightFun x) := φ.toOpenPartialHomeomorph_apply x
  have hinv : Set.LeftInvOn Prod.snd (fun g : G ↦ (c, g)) ((fun g ↦ (c, g)) ⁻¹' Φ.target) :=
    fun _ _ ↦ rfl
  refine ⟨Φ.subtypeCoord {x | φ.leftFun x = c} ⟨⟨φ.pt, hc⟩⟩ (fun g ↦ (c, g)) Prod.snd
    (fun {g} hg ↦ ?_) (fun {x} _ hx ↦ ?_) hinv
    (continuous_const.prodMk continuous_id) continuous_snd.continuousOn,
    ?_, fun x ↦ ?_⟩
  · have h := congrArg Prod.fst (Φ.right_inv hg)
    rwa [hΦ] at h
  · rw [hΦ, hx.out]
  · rw [OpenPartialHomeomorph.subtypeCoord_source]
    exact φ.pt_mem_toOpenPartialHomeomorph_source
  · rw [OpenPartialHomeomorph.subtypeCoord_apply, hΦ]

end ImplicitFunctionData
