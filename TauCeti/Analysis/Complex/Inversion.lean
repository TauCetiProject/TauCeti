/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import TauCeti.Topology.FilledHull
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Bornology.BoundedOperation
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Geometry.Manifold.Connected
import TauCeti.LinearAlgebra.Complex.Finrank
import TauCeti.Topology.Separation.InvFunOn

/-!
# Reading a map of the closed unit disc back through the inversion `w ↦ w⁻¹`

Let `G` be a map of the unit disc with `G 0 = 0` which does not vanish on the punctured disc, and
`p` a point of the plane. The map `w ↦ p + (G w⁻¹)⁻¹` is then defined on the exterior of the closed
unit disc. This file records the elementary properties of this map that are used to pass between a
Riemann map of a domain `W` and the Riemann map of the exterior of the inverted domain, together
with the transport of the unbounded complementary component of a closed set `K` under
`z ↦ (z - a₀)⁻¹`.

## Main results

* `TauCeti.differentiableOn_add_inv_comp_inv`: the map is holomorphic off the closed unit disc if
  `G` is holomorphic on the punctured open disc.
* `TauCeti.tendsto_add_inv_comp_inv`: the map tends to infinity at infinity if `G` is continuous at
  `0`.
* `TauCeti.exists_homeomorph_compl_ball_add_inv_comp_inv`: if `G` is a bijection of the closed disc
  onto a set `K` whose punctured copy is the inversion of `S`, the map is a homeomorphism of the
  closed exterior onto `S`.
* `IsClosed.notMem_filledHull_inv_sub_image`: inverting a closed set `K` about a point `a₀` outside
  its filled hull sends the punctured unbounded component of `Kᶜ` into the component of `0`, so `0`
  lies outside the filled hull of the image.
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
  exact ⟨hhc, ⟨⟨hbij.mapsTo.restrict h _ _, hkmaps.restrict k _ _, fun w => Subtype.ext
      (hleft w.property),
    fun y => Subtype.ext (hright y.property)⟩, hhc.mapsToRestrict hbij.mapsTo,
    hkc.mapsToRestrict hkmaps⟩, fun _ => rfl⟩

/-- Under inversion `z ↦ (z - a₀)⁻¹` about a point `a₀` in the unbounded complementary component of
a closed set `K ⊆ ℂ`, the image of `connectedComponentIn Kᶜ a₀ \ {a₀}` lies in the unbounded
component of `((fun z ↦ (z - a₀)⁻¹) '' K)ᶜ`, which also contains `0`; hence
`0 ∉ filledHull ((fun z ↦ (z - a₀)⁻¹) '' K)`. -/
theorem _root_.IsClosed.notMem_filledHull_inv_sub_image {K : Set ℂ} {a₀ : ℂ} (hK : IsClosed K)
    (ha₀ : a₀ ∉ filledHull K) :
    0 ∉ filledHull ((fun z ↦ (z - a₀)⁻¹) '' K) ∧
      (fun z ↦ (z - a₀)⁻¹) '' (connectedComponentIn Kᶜ a₀ \ {a₀}) ⊆
        connectedComponentIn ((fun z ↦ (z - a₀)⁻¹) '' K)ᶜ 0 := by
  let φ : ℂ → ℂ := fun z ↦ (z - a₀)⁻¹
  set D := connectedComponentIn Kᶜ a₀
  have hφ_inj : Function.Injective φ := inv_injective.comp (sub_left_injective (b := a₀))
  have hφ_cont : ContinuousOn φ {a₀}ᶜ :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun z hz h ↦ hz (sub_eq_zero.mp h)
  have ha₀K : a₀ ∉ K := fun h ↦ ha₀ (subset_filledHull h)
  have h0K' : (0 : ℂ) ∉ φ '' K := by
    rintro ⟨z, hzK, h0⟩
    exact inv_ne_zero (sub_ne_zero.mpr fun h : z = a₀ ↦ ha₀K (h ▸ hzK)) h0
  have hD_open : IsOpen D := hK.isOpen_compl.connectedComponentIn
  have hD_sdiff_preconn : IsPreconnected (D \ {a₀}) :=
    isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank Complex.one_lt_rank_real hD_open
      isPreconnected_connectedComponentIn isClosed_singleton (Set.finite_singleton a₀).isDiscrete
  have hImg_sub : φ '' (D \ {a₀}) ⊆ (φ '' K)ᶜ :=
    Set.subset_compl_iff_disjoint_right.mpr <| (Set.disjoint_image_iff hφ_inj).mpr <|
      Set.subset_compl_iff_disjoint_right.mp
        (sdiff_subset.trans (connectedComponentIn_subset Kᶜ a₀))
  have hD_sdiff_unbdd : ¬ IsBounded (D \ {a₀}) := fun hbd ↦
    (mem_filledHull_iff.not.mp ha₀) <| (hbd.insert a₀).subset fun z hz ↦ by
      by_cases hza : z = a₀
      · simp [hza]
      · exact Or.inr ⟨hz, hza⟩
  have h0_cl : (0 : ℂ) ∈ closure (φ '' (D \ {a₀})) := by
    rw [closure_image_inv_sub hD_sdiff_unbdd]
    exact mem_insert 0 _
  have hD_sub : φ '' (D \ {a₀}) ⊆ connectedComponentIn (φ '' K)ᶜ 0 :=
    (subset_insert 0 _).trans <|
      ((hD_sdiff_preconn.image φ (hφ_cont.mono fun _ hz ↦ hz.2)).subset_closure
        (subset_insert _ _) (insert_subset h0_cl subset_closure)).subset_connectedComponentIn
        (mem_insert 0 _) (insert_subset h0K' hImg_sub)
  have ha₀_cl : a₀ ∈ closure (D \ {a₀}) := mem_closure_iff_nhds.mpr fun U hU ↦ by
    obtain ⟨z, ⟨hzU, hzD⟩, hza⟩ :=
      (inferInstance : (𝓝[≠] a₀).NeBot).nonempty_of_mem <|
        Filter.inter_mem
          (nhdsWithin_le_nhds
            (Filter.inter_mem hU (hD_open.mem_nhds (mem_connectedComponentIn ha₀K))))
          self_mem_nhdsWithin
    exact ⟨z, hzU, hzD, hza⟩
  have hImg_unbdd : ¬ IsBounded (φ '' (D \ {a₀})) :=
    fun hb ↦ (isBounded_image_inv_sub_iff (U := D \ {a₀}) fun h ↦ h.2 rfl).mp hb ha₀_cl
  exact ⟨mem_filledHull_iff.not.mpr fun hbd ↦ hImg_unbdd (hbd.subset hD_sub), hD_sub⟩

end TauCeti
