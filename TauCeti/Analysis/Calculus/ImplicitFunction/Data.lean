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
(`ImplicitFunctionData.levelSetChart`).

## Main declarations

* `ImplicitFunctionData.levelSetChart`: on a level set of the left function of implicit-function
  data, the right function as an open partial homeomorphism whose source contains the base point.
-/

public section

namespace ImplicitFunctionData

/-- `Prod.snd` undoes inserting a constant first coordinate. -/
private theorem leftInvOn_snd_mk {F G : Type*} (c : F) (s : Set G) :
    Set.LeftInvOn (Prod.snd : F × G → G) (fun g ↦ (c, g)) s :=
  fun _ _ ↦ rfl

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  (φ : ImplicitFunctionData 𝕜 E F G) {c : F} (hc : φ.leftFun φ.pt = c)

/-- A point of the slice `{c} × G` of the target is the image of a point of the level set. -/
private theorem leftFun_symm_mk {g : G} (hg : (c, g) ∈ φ.toOpenPartialHomeomorph.target) :
    φ.toOpenPartialHomeomorph.symm (c, g) ∈ {x | φ.leftFun x = c} := by
  have h := congrArg Prod.fst (φ.toOpenPartialHomeomorph.right_inv hg)
  rwa [φ.toOpenPartialHomeomorph_apply] at h

/-- On the level set, reinserting the constant first coordinate recovers the value of
`ImplicitFunctionData.toOpenPartialHomeomorph`. -/
private theorem mk_snd_toOpenPartialHomeomorph {x : E} (hx : x ∈ {x | φ.leftFun x = c}) :
    (c, (φ.toOpenPartialHomeomorph x).2) = φ.toOpenPartialHomeomorph x := by
  rw [φ.toOpenPartialHomeomorph_apply, hx.out]

/-- **Implicit function theorem on a level set.** The chart of the level set
`{x | φ.leftFun x = c}` through the base point given by the right function: Mathlib's
`ImplicitFunctionData.toOpenPartialHomeomorph`, `x ↦ (leftFun x, rightFun x)`, restricted to the
level set, on which its first component is constantly `c`. -/
noncomputable def levelSetChart : OpenPartialHomeomorph {x | φ.leftFun x = c} G :=
  φ.toOpenPartialHomeomorph.subtypeCoord {x | φ.leftFun x = c} ⟨⟨φ.pt, hc⟩⟩ (fun g ↦ (c, g))
    Prod.snd φ.leftFun_symm_mk (fun _ hx ↦ φ.mk_snd_toOpenPartialHomeomorph hx)
    (leftInvOn_snd_mk c _) (continuous_const.prodMk continuous_id) continuous_snd.continuousOn

/-- The source of the level-set chart is the source of
`ImplicitFunctionData.toOpenPartialHomeomorph`, seen inside the level set. -/
theorem levelSetChart_source :
    (φ.levelSetChart hc).source = Subtype.val ⁻¹' φ.toOpenPartialHomeomorph.source := by
  unfold levelSetChart
  apply OpenPartialHomeomorph.subtypeCoord_source

/-- The target of the level-set chart is the slice `{c} × G` of the target of
`ImplicitFunctionData.toOpenPartialHomeomorph`, read in `G`. -/
theorem levelSetChart_target :
    (φ.levelSetChart hc).target = (fun g ↦ (c, g)) ⁻¹' φ.toOpenPartialHomeomorph.target := by
  unfold levelSetChart
  apply OpenPartialHomeomorph.subtypeCoord_target

/-- The level-set chart is the right function. -/
@[simp]
theorem levelSetChart_apply (x : {x | φ.leftFun x = c}) :
    φ.levelSetChart hc x = φ.rightFun x.val := by
  unfold levelSetChart
  rw [OpenPartialHomeomorph.subtypeCoord_apply, φ.toOpenPartialHomeomorph_apply]

/-- On its target, the inverse of the level-set chart is the inverse of
`ImplicitFunctionData.toOpenPartialHomeomorph`, read on the slice `{c} × G`. -/
theorem coe_levelSetChart_symm_apply {g : G} (hg : g ∈ (φ.levelSetChart hc).target) :
    ((φ.levelSetChart hc).symm g : E) = φ.toOpenPartialHomeomorph.symm (c, g) := by
  rw [levelSetChart_target] at hg
  unfold levelSetChart
  rw [OpenPartialHomeomorph.coe_subtypeCoord_symm_apply _ _ _ _ _ _ _ _ _ _ hg]

/-- The base point lies in the source of the level-set chart. -/
theorem mem_levelSetChart_source : ⟨φ.pt, hc⟩ ∈ (φ.levelSetChart hc).source := by
  rw [levelSetChart_source]
  exact φ.pt_mem_toOpenPartialHomeomorph_source

end ImplicitFunctionData
