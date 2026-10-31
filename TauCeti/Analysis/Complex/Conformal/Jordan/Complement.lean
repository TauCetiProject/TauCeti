/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.Domain
import TauCeti.Analysis.Complex.Conformal.Jordan.Approach
import TauCeti.Analysis.Complex.PlaneSeparation.Inside
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.Analysis.Normed.Module.FilledHull

/-!
# Carathéodory's theorem for both complementary domains of a Jordan curve

A Jordan curve `C ⊆ ℂ` has exactly two complementary components: its inside `filledHull C \ C`
and its outside `(filledHull C)ᶜ`. This file shows that the inside is a conformal image of the open
unit disc and the outside a conformal image of the exterior `(closedBall 0 1)ᶜ` of the closed unit
disc, and that these maps extend to homeomorphisms of the closed disc onto `filledHull C`, the
closure of the inside, and of the closed exterior `(ball 0 1)ᶜ` onto `(filledHull C \ C)ᶜ`, the
closure of the outside, the unit circle going onto `C` in both cases.

* For the inside, the closed unit disc is homeomorphic to `filledHull C`, the closure of the inside,
  by a map that is holomorphic on the open disc and sends its centre to any prescribed point of the
  inside. This is Carathéodory's theorem for the Jordan domain `filledHull C \ C`, and in
  particular the closed-disc form of the Schoenflies theorem.
* For the outside, the closed exterior `(ball 0 1)ᶜ` of the unit disc is homeomorphic to
  `(filledHull C \ C)ᶜ`, the closure of the outside, by a map that is holomorphic off the closed
  disc and tends to infinity at infinity. Inverting the outside about a point `p` of the inside,
  `z ↦ (z - p)⁻¹`, and adding `0`, the image of infinity, gives a bounded Jordan domain bounded by
  the inverted curve
  (`TauCeti.IsJordanCurve.isJordanDomain_insert_zero_image_inv_sub_compl_filledHull`); the
  exterior map is read back from its Riemann map normalized at `0`.

## Main results

* `TauCeti.IsJordanCurve.exists_homeomorph_closedBall_filledHull` — the inside of a Jordan curve
  is the image of the disc under a holomorphic bijection that extends to a homeomorphism of the
  closed disc onto `filledHull C`, carrying the circle onto `C`.
* `TauCeti.IsJordanCurve.exists_homeomorph_compl_ball_compl_filledHull_sdiff` — the outside of a
  Jordan curve is the image of the exterior of the disc under a holomorphic bijection that tends to
  infinity at infinity and extends to a homeomorphism of the closed exterior onto the complement
  of the inside, carrying the circle onto `C`.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Theorem 2.6.
-/

public section

open Bornology Filter Function Metric Set Topology

namespace TauCeti

variable {C : Set ℂ} {p : ℂ}

/-! ## The inside -/

/-- **Carathéodory's theorem for the inside of a Jordan curve.** For a Jordan curve `C ⊆ ℂ` and a
point `p` of its inside `filledHull C \ C`, there is a map `g`, holomorphic on the open unit disc
with `g 0 = p`, carrying the disc bijectively onto the inside and the unit circle bijectively onto
`C`, which restricts to a homeomorphism of the closed disc onto `filledHull C`. -/
theorem IsJordanCurve.exists_homeomorph_closedBall_filledHull (hC : IsJordanCurve C)
    (hp : p ∈ filledHull C \ C) :
    ∃ g : ℂ → ℂ, ContinuousOn g (closedBall 0 1) ∧ DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn g (ball 0 1) (filledHull C \ C) ∧ BijOn g (sphere 0 1) C ∧ g 0 = p ∧
      ∃ e : closedBall (0 : ℂ) 1 ≃ₜ filledHull C,
        ∀ z : closedBall (0 : ℂ) 1, (e z : ℂ) = g z := by
  have hJ := hC.isJordanDomain_filledHull_sdiff
  obtain ⟨g, hgc, hgd, hgbij, hg0, e, he⟩ :=
    exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier_of_mem hJ.isOpen
      hJ.isConnected hJ.isBounded hJ.isJordanCurve_frontier hp
  have hgi : InjOn g (closedBall 0 1) := fun x hx y hy hxy => congrArg Subtype.val
    (e.injective (Subtype.ext ((he ⟨x, hx⟩).trans (hxy.trans (he ⟨y, hy⟩).symm))))
  have hcl : closure (ball (0 : ℂ) 1) = closedBall 0 1 := closure_ball 0 one_ne_zero
  -- the circle, the frontier of the disc, goes onto the frontier `C` of the inside
  have himg : g '' sphere 0 1 = C := by
    rw [← frontier_ball (0 : ℂ) one_ne_zero, image_frontier_eq_frontier_image isOpen_ball
      isBounded_ball hgd hgbij.injOn (by rwa [hcl]) fun _ _ => rfl, hgbij.image_eq,
      hC.frontier_filledHull_sdiff]
  exact ⟨g, hgc, hgd, hgbij, himg ▸ (hgi.mono sphere_subset_closedBall).bijOn_image, hg0,
    e.trans (Homeomorph.setCongr hC.closure_filledHull_sdiff), he⟩

/-! ## The outside -/

/-- **Carathéodory's theorem for the outside of a Jordan curve.** For a Jordan curve `C ⊆ ℂ` there
is a map `h`, holomorphic off the closed unit disc and tending to infinity at infinity, carrying the
exterior of the closed disc bijectively onto the outside `(filledHull C)ᶜ` and the unit circle
bijectively onto `C`, which restricts to a homeomorphism of the closed exterior `(ball 0 1)ᶜ` onto
the complement of the inside, the closure of the outside
(`TauCeti.IsJordanCurve.closure_compl_filledHull`). -/
theorem IsJordanCurve.exists_homeomorph_compl_ball_compl_filledHull_sdiff (hC : IsJordanCurve C) :
    ∃ h : ℂ → ℂ, ContinuousOn h (ball 0 1)ᶜ ∧ DifferentiableOn ℂ h (closedBall 0 1)ᶜ ∧
      BijOn h (closedBall 0 1)ᶜ (filledHull C)ᶜ ∧ BijOn h (sphere 0 1) C ∧
      Tendsto h (cobounded ℂ) (cobounded ℂ) ∧
      ∃ e : ((ball (0 : ℂ) 1)ᶜ : Set ℂ) ≃ₜ ((filledHull C \ C)ᶜ : Set ℂ),
        ∀ z : ((ball (0 : ℂ) 1)ᶜ : Set ℂ), (e z : ℂ) = h z := by
  -- Invert the outside about a point `p` of the inside, take the Riemann map `G` of the resulting
  -- Jordan domain `W` normalized by `G 0 = 0`, and read it back: `h w = p + (G w⁻¹)⁻¹`.
  obtain ⟨p, hp⟩ := hC.nonempty_filledHull_sdiff
  have hJ := hC.isJordanDomain_insert_zero_image_inv_sub_compl_filledHull hp
  set W := insert 0 ((fun z : ℂ => (z - p)⁻¹) '' (filledHull C)ᶜ) with hW
  obtain ⟨G, hGc, hGd, hGbij, hG0, E, hE⟩ :=
    exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier_of_mem hJ.isOpen
      hJ.isConnected hJ.isBounded hJ.isJordanCurve_frontier (mem_insert 0 _)
  have h0 {S : Set ℂ} (hS : p ∉ S) : (0 : ℂ) ∉ (fun z : ℂ => (z - p)⁻¹) '' S := by
    rintro ⟨z, hz, hz0⟩
    rw [inv_eq_zero, sub_eq_zero] at hz0
    exact hS (hz0 ▸ hz)
  /- The pieces of `W` and of its closure, away from `0`, are the inverted pieces of the closed
  outside. -/
  have hclW : closure W \ {0} = (fun z : ℂ => (z - p)⁻¹) '' (filledHull C \ C)ᶜ := by
    rw [hW, closure_insert_zero_image_inv_sub, hC.closure_compl_filledHull,
      insert_sdiff_self_of_notMem (h0 (not_not_intro hp))]
  have hW0 : W \ {0} = (fun z : ℂ => (z - p)⁻¹) '' (filledHull C)ᶜ :=
    insert_sdiff_self_of_notMem (h0 fun h => h hp.1)
  /- The extension `G` is a bijection of the closed disc onto `closure W`, and of the circle onto
  `frontier W`. -/
  have hGi : InjOn G (closedBall 0 1) := fun x hx y hy hxy => congrArg Subtype.val
    (E.injective (Subtype.ext ((hE ⟨x, hx⟩).trans (hxy.trans (hE ⟨y, hy⟩).symm))))
  have hcl : closure (ball (0 : ℂ) 1) = closedBall 0 1 := closure_ball 0 one_ne_zero
  have hGcl : BijOn G (closedBall 0 1) (closure W) := by
    have := bijOn_closure_closure_image isBounded_ball (by rwa [hcl]) (fun _ _ => rfl)
      (by rwa [hcl] : InjOn G (closure (ball (0 : ℂ) 1)))
    rwa [hcl, hGbij.image_eq] at this
  have hGS : BijOn G (sphere 0 1) ((fun z : ℂ => (z - p)⁻¹) '' C) := by
    have himg : G '' sphere 0 1 = (fun z : ℂ => (z - p)⁻¹) '' C := by
      rw [← frontier_ball (0 : ℂ) one_ne_zero, image_frontier_eq_frontier_image isOpen_ball
        isBounded_ball hGd hGbij.injOn (by rwa [hcl]) fun _ _ => rfl, hGbij.image_eq,
        hC.frontier_insert_zero_image_inv_sub_compl_filledHull hp]
    exact himg ▸ (hGi.mono sphere_subset_closedBall).bijOn_image
  have hG1 : BijOn G (closedBall 0 1 \ {0}) (closure W \ {0}) := by
    simpa only [hG0] using hGcl.sdiff_singleton (mem_closedBall_self zero_le_one)
  have hG2 : BijOn G (ball 0 1 \ {0}) (W \ {0}) := by
    simpa only [hG0] using hGbij.sdiff_singleton (mem_ball_self one_pos)
  /- Inversion exchanges the closed exterior, the open exterior and the circle with the punctured
  closed disc, the punctured open disc and the circle. -/
  have hinv {s t : Set ℂ} (h : ∀ w, w ∈ s ↔ w⁻¹ ∈ t) : BijOn (fun w : ℂ => w⁻¹) s t :=
    ⟨fun w hw => (h w).1 hw, inv_injective.injOn,
      fun y hy => ⟨y⁻¹, (h _).2 (by rwa [inv_inv]), inv_inv y⟩⟩
  have hmem1 (w : ℂ) : w ∈ (ball (0 : ℂ) 1)ᶜ ↔ w⁻¹ ∈ closedBall (0 : ℂ) 1 \ {0} := by
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · simp [hw, inv_le_one₀ (norm_pos_iff.mpr hw)]
  have hI1 := hinv hmem1
  have hI2 : BijOn (fun w : ℂ => w⁻¹) (closedBall 0 1)ᶜ (ball 0 1 \ {0}) := hinv fun w => by
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · simp [hw, inv_lt_one₀ (norm_pos_iff.mpr hw)]
  have hI3 : BijOn (fun w : ℂ => w⁻¹) (sphere 0 1) (sphere 0 1) := hinv fun w => by simp
  /- The exterior map and its three bijections. -/
  set h : ℂ → ℂ := fun w => p + (G w⁻¹)⁻¹ with hh
  have hbij : BijOn h (ball 0 1)ᶜ (filledHull C \ C)ᶜ :=
    (bijOn_add_inv_image_inv_sub _).comp ((hclW ▸ hG1).comp hI1)
  have hne {w : ℂ} (hw : w ∈ (ball (0 : ℂ) 1)ᶜ) : G w⁻¹ ≠ 0 := (hG1.mapsTo (hI1.mapsTo hw)).2
  have hhc : ContinuousOn h (ball 0 1)ᶜ := by
    have hw0 : (ball (0 : ℂ) 1)ᶜ ⊆ {0}ᶜ := fun w hw (h : w = 0) => hw (h ▸ mem_ball_self one_pos)
    exact continuousOn_const.add (((hGc.comp (continuousOn_inv₀.mono hw0)
      fun w hw => (hI1.mapsTo hw).1).inv₀ fun w hw => hne hw))
  /- The inverse `k y = (G⁻¹ (y - p)⁻¹)⁻¹`, continuous because the inverse of `G` on `closure W` is
  the inverse homeomorphism `E.symm`. -/
  set Ginv := invFunOn G (closedBall 0 1) with hGinv
  have hGinvE (y : closure W) : Ginv y = E.symm y :=
    hGi (invFunOn_mem (hGcl.surjOn y.2)) (E.symm y).2
      (by rw [invFunOn_eq (hGcl.surjOn y.2), ← hE, E.apply_symm_apply])
  have hGinvc : ContinuousOn Ginv (closure W) := by
    rw [continuousOn_iff_continuous_domRestrict,
      (funext hGinvE : (closure W).domRestrict Ginv = fun y => (E.symm y : ℂ))]
    exact continuous_subtype_val.comp E.symm.continuous
  have hιW {y : ℂ} (hy : y ∈ (filledHull C \ C)ᶜ) : (y - p)⁻¹ ∈ closure W \ {0} := by
    rw [hclW]
    exact mem_image_of_mem _ hy
  have hGinvW {y : ℂ} (hy : y ∈ (filledHull C \ C)ᶜ) :
      Ginv (y - p)⁻¹ ∈ closedBall (0 : ℂ) 1 \ {0} ∧ G (Ginv (y - p)⁻¹) = (y - p)⁻¹ := by
    have hs := hGcl.surjOn (hιW hy).1
    refine ⟨⟨invFunOn_mem hs, fun h0' => (hιW hy).2 ?_⟩, invFunOn_eq hs⟩
    have hGy := invFunOn_eq hs
    rw [← hGinv, mem_singleton_iff.mp h0', hG0] at hGy
    exact hGy.symm
  set k : ℂ → ℂ := fun y => (Ginv (y - p)⁻¹)⁻¹ with hk
  have hkmaps : MapsTo k (filledHull C \ C)ᶜ (ball 0 1)ᶜ := fun y hy =>
    (hmem1 _).2 (by rw [hk, inv_inv]; exact (hGinvW hy).1)
  have hkc : ContinuousOn k (filledHull C \ C)ᶜ :=
    (hGinvc.comp (ContinuousOn.inv₀ (by fun_prop) fun y hy =>
      sub_ne_zero.mpr fun hyp => (mem_compl_iff _ _).mp hy (hyp ▸ hp))
      fun y hy => (hιW hy).1).inv₀ fun y hy => (hGinvW hy).1.2
  have hleft : LeftInvOn k h (ball 0 1)ᶜ := fun w hw => by
    simp only [hk, hh, add_sub_cancel_left, inv_inv]
    rw [hGinv, hGcl.injOn.leftInvOn_invFunOn ((hmem1 w).1 hw).1, inv_inv]
  have hright : RightInvOn k h (filledHull C \ C)ᶜ := fun y hy => by
    simp only [hk, hh, inv_inv]
    rw [(hGinvW hy).2, inv_inv, add_sub_cancel]
  refine ⟨h, hhc, ?_, (bijOn_add_inv_image_inv_sub _).comp ((hW0 ▸ hG2).comp hI2),
    (bijOn_add_inv_image_inv_sub _).comp (hGS.comp hI3), ?_,
    ⟨⟨hbij.mapsTo.restrict h _ _, hkmaps.restrict k _ _, fun w => Subtype.ext (hleft w.2),
      fun y => Subtype.ext (hright y.2)⟩, hhc.mapsToRestrict hbij.mapsTo,
      hkc.mapsToRestrict hkmaps⟩, fun _ => rfl⟩
  · -- `h` is holomorphic off the closed disc, where `G w⁻¹` is defined and nonzero
    have hw0 : (closedBall (0 : ℂ) 1)ᶜ ⊆ {x | x ≠ 0} := fun w hw h =>
      hw (h ▸ mem_closedBall_self zero_le_one)
    exact (differentiableOn_const p).add ((hGd.comp (differentiableOn_inv.mono hw0)
      fun w hw => (hI2.mapsTo hw).1).inv fun w hw => (hG2.mapsTo (hI2.mapsTo hw)).2)
  · -- `G w⁻¹ → G 0 = 0` through nonzero values as `w → ∞`
    have hG0t : Tendsto G (𝓝 0) (𝓝 0) := by
      have := (hGd.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))).tendsto
      rwa [hG0] at this
    have hev : ∀ᶠ w in cobounded ℂ, G w⁻¹ ∈ ({0} : Set ℂ)ᶜ :=
      Filter.mem_of_superset (isBounded_def.mp (isBounded_closedBall (x := (0 : ℂ)) (r := 1)))
        fun w hw => (hG2.mapsTo (hI2.mapsTo hw)).2
    exact (tendsto_const_add_cobounded p).comp (tendsto_inv₀_nhdsNE_zero.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hG0t.comp tendsto_inv₀_cobounded, hev⟩))

end TauCeti
