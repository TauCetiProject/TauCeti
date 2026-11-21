/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CellularSet.Basic
import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
import TauCeti.Analysis.Normed.Module.Ball.Radial.OrderIso
import TauCeti.Topology.Separation.InvFunOn

/-!
# The only inverse set of a map of a cell between spaces of the same dimension is cellular

Let `E` and `F` be finite-dimensional real normed spaces of the same dimension, and let
`f : E → F` be continuous on the closed unit ball `B` of `E` and injective on `B` away from the
fibre `M = B ∩ f⁻¹{p}` of a single point `p`. In M. Brown's language, `M` is the only inverse set
of `f` on `B`.

This file proves Brown's Theorem 3: if `M` is nonempty, that is `p ∈ f '' B`, and lies in the
open unit ball, then `M` is cellular
(`TauCeti.isCellularSet_closedBall_inter_preimage_of_finrank_eq`). Given an open `U ⊇ M`, the set
`f '' (U ∩ ball 0 1)` is open by the one-inverse-set case of Brown's Theorem 0
(`IsOpen.image_of_continuousOn_of_injOn_sdiff`, in
`TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain`). Choose a homeomorphism `h` of `F` which
fixes a neighbourhood of `p` and pulls the compact set `f '' B` into this open set. Then
`g = f⁻¹ ∘ h ∘ f` on `B \ M`, extended by the identity on `M`, is a continuous injection of `B`
into `U` which is the identity near `M`, so its image is a closed cell in `U` with `M` in its
interior
(`TauCeti.exists_continuousOn_injOn_image_closedBall_subset_of_injOn_closedBall_sdiff`).

Maps of an `n`-cell into the unit sphere `Sⁿ` of a space of dimension `n + 1` reduce to this case
through a stereographic projection
(`TauCeti.isCellularSet_closedBall_inter_preimage` in
`TauCeti.Topology.CellularSet.InverseSet.Sphere`).

These are steps in Brown's proof of the generalized Schoenflies theorem. There, the map of the
sphere `Sⁿ` collapsing the two outer pieces of a bicollar has exactly two inverse sets, and
Theorem 4 applies Theorem 3 to recognize both of them as cellular.

## Main results

* `TauCeti.exists_continuousOn_injOn_image_closedBall_subset_of_injOn_closedBall_sdiff`: every
  neighbourhood of a nonempty only inverse set contains a closed cell with the inverse set in its
  interior.
* `TauCeti.isCellularSet_closedBall_inter_preimage_of_finrank_eq`: a nonempty only inverse set is
  cellular (Brown's Theorem 3).

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorems 0 and 3.
-/

public section

open Set Metric Filter Topology Function Module

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : E → F} {p : F}

namespace TauCeti

/-- **Cell neighbourhoods of the only inverse set.** Let `E` and `F` be finite-dimensional real
normed spaces of the same dimension and `f : E → F` a map continuous on the closed unit ball,
injective on it away from the nonempty fibre `M = closedBall 0 1 ∩ f ⁻¹' {p}`, which lies in the
open unit ball. Then every open `U ⊇ M` contains a closed cell, the image of the closed unit ball
under a map `g` continuous and injective on it, whose open cell contains `M` in its interior. -/
theorem exists_continuousOn_injOn_image_closedBall_subset_of_injOn_closedBall_sdiff
    (hEF : finrank ℝ E = finrank ℝ F) (hf : ContinuousOn f (closedBall 0 1))
    (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {p})) (hM : closedBall 0 1 ∩ f ⁻¹' {p} ⊆ ball 0 1)
    (hp : p ∈ f '' closedBall 0 1) {U : Set E} (hU : IsOpen U)
    (hMU : closedBall 0 1 ∩ f ⁻¹' {p} ⊆ U) :
    ∃ g : E → E, ContinuousOn g (closedBall 0 1) ∧ InjOn g (closedBall 0 1) ∧
      closedBall 0 1 ∩ f ⁻¹' {p} ⊆ interior (g '' ball 0 1) ∧ g '' closedBall 0 1 ⊆ U := by
  /- The map is `g = f⁻¹ ∘ h ∘ f` away from `M` and the identity on `M`, where `h` is a
  homeomorphism of `F` fixing a neighbourhood of `p` and pulling `f '' closedBall 0 1` into
  `f '' (U ∩ ball 0 1)`, which is open by Brown's Theorem 0. Then `g` is continuous and injective
  on the closed ball and maps it into `U`, by
  `ContinuousOn.exists_continuousOn_injOn_mapsTo_of_mapsTo_image`, and it is the identity near
  `M`. -/
  set B := closedBall (0 : E) 1
  set M := B ∩ f ⁻¹' {p}
  have hUB : U ∩ ball 0 1 ⊆ B := inter_subset_right.trans ball_subset_closedBall
  have hUM : (U ∩ ball 0 1) ∩ f ⁻¹' {p} = M :=
    Subset.antisymm (fun z hz ↦ ⟨hUB hz.1, hz.2⟩) fun z hz ↦ ⟨⟨hMU hz, hM hz⟩, hz.2⟩
  have hMc : IsCompact M := (isCompact_closedBall 0 1).of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton) inter_subset_left
  -- A ball `ball p ε` lies in the image of `U ∩ ball 0 1`, which is open by Theorem 0.
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1
    ((hU.inter isOpen_ball).image_of_continuousOn_of_injOn_sdiff (hf.mono hUB)
      (hinj.mono (sdiff_subset_sdiff_left hUB)) (by rwa [hUM]) hEF) p
    (by obtain ⟨m, hmB, hmp⟩ := hp; exact ⟨m, ⟨hMU ⟨hmB, hmp⟩, hM ⟨hmB, hmp⟩⟩, hmp⟩)
  -- The homeomorphism `h` of `F` fixing `closedBall p (ε / 2)` and pulling `f '' B` into
  -- `ball p ε`.
  obtain ⟨R, hR⟩ := ((isCompact_closedBall (0 : E) 1).image_of_continuousOn hf).isBounded
    |>.subset_closedBall p
  have hε34 : ε / 2 < 3 * ε / 4 := by linarith
  obtain ⟨ρ, hρ_fix, hρ_maps⟩ := exists_homeomorph_eqOn_closedBall_mapsTo_closedBall (E := F)
    (r := R) (half_pos hε).le hε34
  set h : F ≃ₜ F := (Homeomorph.subRight p).trans (ρ.trans (Homeomorph.addRight p))
  have hh_fix : EqOn h id (closedBall p (ε / 2)) := fun y hy ↦ by
    have hy' : y - p ∈ closedBall (0 : F) (ε / 2) := by
      rwa [mem_closedBall_zero_iff, ← mem_closedBall_iff_norm]
    simp [h, hρ_fix hy']
  have hh_maps : MapsTo h (closedBall p R) (ball p ε) := fun y hy ↦ by
    have hyR : y - p ∈ closedBall (0 : F) R := by
      rwa [mem_closedBall_zero_iff, ← mem_closedBall_iff_norm]
    have hy' := hρ_maps hyR
    rw [mem_closedBall_zero_iff] at hy'
    rw [mem_ball_iff_norm]
    simp only [h, Homeomorph.trans_apply, Homeomorph.coe_subRight, Homeomorph.coe_addRight,
      add_sub_cancel_right]
    linarith
  have hh_mapsU : MapsTo h (f '' B) (f '' (B ∩ (U ∩ ball 0 1))) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, hfu⟩ := hεU (hh_maps (hR ⟨x, hx, rfl⟩))
    exact ⟨u, ⟨ball_subset_closedBall hu.2, hu⟩, hfu⟩
  obtain ⟨g, hgc, hgi, hgU, -, hg_id⟩ := hf.exists_continuousOn_injOn_mapsTo_of_mapsTo_image
    (isCompact_closedBall 0 1) hinj (subset_inter hMU hM) h.continuous.continuousOn
    h.injective.injOn
    (eventuallyEq_of_mem (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds p (half_pos hε)))
      hh_fix) hh_mapsU
  refine ⟨g, hgc, hgi, ?_, hgU.image_subset.trans (inter_subset_right.trans inter_subset_left)⟩
  -- `g` is the identity on the open neighbourhood `ball 0 1 ∩ f ⁻¹' ball p (ε / 2)` of `M`.
  have hNo : IsOpen (ball (0 : E) 1 ∩ f ⁻¹' ball p (ε / 2)) :=
    (hf.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_ball
  have hMN : M ⊆ ball (0 : E) 1 ∩ f ⁻¹' ball p (ε / 2) := fun m hm ↦
    ⟨hM hm, by rw [mem_preimage, mem_singleton_iff.1 hm.2]; exact mem_ball_self (by positivity)⟩
  have hNg : ball (0 : E) 1 ∩ f ⁻¹' ball p (ε / 2) ⊆ g '' ball 0 1 := fun y hy ↦
    ⟨y, hy.1, hg_id y (ball_subset_closedBall hy.1) (hh_fix (ball_subset_closedBall hy.2))⟩
  exact hMN.trans (interior_maximal hNg hNo)

/-- **Brown's Theorem 3: the only inverse set of a map of a cell is cellular.** Let `E` and `F`
be finite-dimensional real normed spaces of the same dimension and `f : E → F` a map continuous on
the closed unit ball, injective on it away from the nonempty fibre
`M = closedBall 0 1 ∩ f ⁻¹' {p}`, which lies in the open unit ball. Then `M` is cellular. -/
theorem isCellularSet_closedBall_inter_preimage_of_finrank_eq (hEF : finrank ℝ E = finrank ℝ F)
    (hf : ContinuousOn f (closedBall 0 1)) (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {p}))
    (hM : closedBall 0 1 ∩ f ⁻¹' {p} ⊆ ball 0 1) (hp : p ∈ f '' closedBall 0 1) :
    IsCellularSet E (closedBall (0 : E) 1 ∩ f ⁻¹' {p}) :=
  isCellularSet_of_forall_isOpen
    (hf.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton) fun _ hU hMU ↦
      exists_continuousOn_injOn_image_closedBall_subset_of_injOn_closedBall_sdiff hEF hf hinj hM
        hp hU hMU

end TauCeti
