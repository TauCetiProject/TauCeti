/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Bornology.BoundedOperation
import Mathlib.Topology.Algebra.GroupWithZero
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.Topology.Separation.InvFunOn

/-!
# Reading a map of the closed unit disc back through the inversion `w ↦ w⁻¹`

Let `G` be a map of the unit disc with `G 0 = 0` which does not vanish on the punctured disc, and
`p` a point of the plane. The map `w ↦ p + (G w⁻¹)⁻¹` is then defined on the exterior of the closed
unit disc. This file records the elementary properties of this map that are used to pass between a
Riemann map of a domain `W` and the Riemann map of the exterior of the inverted domain.

## Main results

* `TauCeti.differentiableOn_add_inv_comp_inv`: the map is holomorphic off the closed unit disc if
  `G` is holomorphic on the punctured open disc.
* `TauCeti.tendsto_add_inv_comp_inv`: the map tends to infinity at infinity if `G` is continuous at
  `0`.
* `TauCeti.exists_homeomorph_compl_ball_add_inv_comp_inv`: if `G` is a bijection of the closed disc
  onto a set `K` whose punctured copy is the inversion of `S`, the map is a homeomorphism of the
  closed exterior onto `S`.
-/

public section

open Bornology Filter Function Metric Set Topology

namespace TauCeti

/-- The map `w ↦ p + (G w⁻¹)⁻¹` is holomorphic off the closed unit disc when `G` is holomorphic on
the punctured open disc and does not vanish there. -/
theorem differentiableOn_add_inv_comp_inv {G : ℂ → ℂ} (p : ℂ)
    (hGd : DifferentiableOn ℂ G (ball 0 1 \ {0}))
    (hne : ∀ x ∈ ball (0 : ℂ) 1, x ≠ 0 → G x ≠ 0) :
    DifferentiableOn ℂ (fun w : ℂ => p + (G w⁻¹)⁻¹) (closedBall 0 1)ᶜ := by
  have hI := bijOn_inv_compl_closedBall_one (𝕜 := ℂ)
  have hw0 : (closedBall (0 : ℂ) 1)ᶜ ⊆ {x | x ≠ 0} := fun w hw h =>
    hw (h ▸ mem_closedBall_self zero_le_one)
  exact (differentiableOn_const p).add ((hGd.comp (differentiableOn_inv.mono hw0)
    fun w hw => hI.mapsTo hw).inv fun w hw => hne _ (hI.mapsTo hw).1 (hI.mapsTo hw).2)

/-- The map `w ↦ p + (G w⁻¹)⁻¹` tends to infinity at infinity when `G` is continuous at `0` with
`G 0 = 0` and does not vanish on a punctured neighbourhood of `0`. -/
theorem tendsto_add_inv_comp_inv {G : ℂ → ℂ} (p : ℂ)
    (hGc : ContinuousAt G 0) (hG0 : G 0 = 0)
    (hne : ∀ᶠ x in 𝓝[≠] (0 : ℂ), G x ≠ 0) :
    Tendsto (fun w : ℂ => p + (G w⁻¹)⁻¹) (cobounded ℂ) (cobounded ℂ) := by
  have hG0t : Tendsto G (𝓝 0) (𝓝 0) := by
    have := hGc.tendsto
    rwa [hG0] at this
  exact (tendsto_const_add_cobounded p).comp (tendsto_inv₀_nhdsNE_zero.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hG0t.comp tendsto_inv₀_cobounded,
      tendsto_inv₀_cobounded'.eventually hne⟩))

/-- **Reading a Riemann map of an inverted set back.** Let `K` be a set whose punctured copy
`K \ {0}` is the inversion `z ↦ (z - p)⁻¹` of a set `S`, and `G` a bijection of the closed unit disc
onto `K` with `G 0 = 0`, continuous on the closed disc. Then `w ↦ p + (G w⁻¹)⁻¹` is continuous on
the closed exterior `(ball 0 1)ᶜ` and restricts to a homeomorphism of it onto `S`. -/
theorem exists_homeomorph_compl_ball_add_inv_comp_inv {G : ℂ → ℂ} {K S : Set ℂ} {p : ℂ}
    (hG0 : G 0 = 0) (hGc : ContinuousOn G (closedBall 0 1))
    (hGcl : BijOn G (closedBall 0 1) K)
    (hK : K \ {0} = (fun z : ℂ => (z - p)⁻¹) '' S) :
    ContinuousOn (fun w : ℂ => p + (G w⁻¹)⁻¹) (ball 0 1)ᶜ ∧
      ∃ e : ((ball (0 : ℂ) 1)ᶜ : Set ℂ) ≃ₜ S, ∀ z, (e z : ℂ) = p + (G (z : ℂ)⁻¹)⁻¹ := by
  have hp : p ∉ S := fun h =>
    ((hK ▸ mem_image_of_mem (fun z : ℂ => (z - p)⁻¹) h : (p - p)⁻¹ ∈ K \ {0}).2) (by simp)
  set Ginv := invFunOn G (closedBall 0 1) with hGinv
  have hGinvc : ContinuousOn Ginv (K) :=
    hGcl.image_eq ▸ hGc.continuousOn_invFunOn_image_of_isCompact (isCompact_closedBall 0 1)
      subset_rfl hGcl.injOn (by simp)
  have hI1 := bijOn_inv_compl_ball_one (𝕜 := ℂ)
  have hG1 : BijOn G (closedBall 0 1 \ {0}) (K \ {0}) := by
    simpa only [hG0] using hGcl.sdiff_singleton (mem_closedBall_self zero_le_one)
  set h : ℂ → ℂ := fun w => p + (G w⁻¹)⁻¹ with hh
  have hbij : BijOn h (ball 0 1)ᶜ S :=
    (bijOn_add_inv_image_inv_sub _).comp ((hK ▸ hG1).comp hI1)
  have hne {w : ℂ} (hw : w ∈ (ball (0 : ℂ) 1)ᶜ) : G w⁻¹ ≠ 0 := (hG1.mapsTo (hI1.mapsTo hw)).2
  have hhc : ContinuousOn h (ball 0 1)ᶜ := by
    have hw0 : (ball (0 : ℂ) 1)ᶜ ⊆ {0}ᶜ := fun w hw (h : w = 0) => hw (h ▸ mem_ball_self one_pos)
    exact continuousOn_const.add (((hGc.comp (continuousOn_inv₀.mono hw0)
      fun w hw => (hI1.mapsTo hw).1).inv₀ fun w hw => hne hw))
  have hιW {y : ℂ} (hy : y ∈ S) : (y - p)⁻¹ ∈ K \ {0} := by
    rw [hK]
    exact mem_image_of_mem _ hy
  set k : ℂ → ℂ := fun y => (Ginv (y - p)⁻¹)⁻¹ with hk
  have hleft : LeftInvOn k h (ball 0 1)ᶜ := fun w hw => by
    simp only [hk, hh, add_sub_cancel_left, inv_inv]
    rw [hGinv, hGcl.injOn.leftInvOn_invFunOn (hI1.mapsTo hw).1, inv_inv]
  have hkmaps : MapsTo k S (ball 0 1)ᶜ := hleft.mapsTo hbij.surjOn
  have hright : RightInvOn k h S := hbij.surjOn.leftInvOn_of_rightInvOn hleft
  have hinvc : ContinuousOn (fun y : ℂ => (y - p)⁻¹) S :=
    ContinuousOn.inv₀ (by fun_prop) fun y hy hyp => hp (by rwa [sub_eq_zero.mp hyp] at hy)
  have hkc : ContinuousOn k S :=
    (hGinvc.comp hinvc fun y hy => (hιW hy).1).inv₀ fun y hy h0 =>
      hkmaps hy (by rw [Function.comp_apply] at h0; simp [hk, h0])
  exact ⟨hhc, ⟨⟨hbij.mapsTo.restrict h _ _, hkmaps.restrict k _ _, fun w => Subtype.ext (hleft w.2),
    fun y => Subtype.ext (hright y.2)⟩, hhc.mapsToRestrict hbij.mapsTo,
    hkc.mapsToRestrict hkmaps⟩, fun _ => rfl⟩

end TauCeti
