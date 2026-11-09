/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Hemisphere
public import TauCeti.Topology.CellularSet

/-!
# Preimages of closed hemispheres under a map with a cellular inverse set

Let `S` be the unit sphere of a finite-dimensional real inner product space, let `p ∈ S`, and let
`g : S → S` be a continuous surjection which is injective over the closed hemisphere
`{y | 0 ≤ ⟪y, p⟫}` except on the inverse set `g⁻¹(p)`, collapsed to the pole. If `g⁻¹(p)` is
cellular, then the preimage `g⁻¹{y | 0 ≤ ⟪y, p⟫}` is a closed disc: it is homeomorphic to the
closed unit ball of the hyperplane `(ℝ ∙ p)ᗮ`, by a homeomorphism which agrees with `g` on the
preimage of the equator and carries that preimage exactly onto the boundary sphere of the ball
(`TauCeti.IsCellularSet.exists_homeomorph_preimage_hemisphere`).

This is the step of M. Brown's proof of the generalized Schoenflies theorem which recognizes the
closures of the two complementary domains of a bicollared sphere `Σ ⊆ S` as discs. There `g`
collapses each of the two components of the complement of the open bicollar to a pole and sends
`Σ` onto the equator, and its two inverse sets over the poles are cellular; the preimages of the
two closed hemispheres are the closures of the two complementary domains of `Σ`, with frontier
`Σ`. The homeomorphism is `g` corrected by the collapse of the cellular inverse set
(`TauCeti.IsCellularSet.exists_homeomorph_image`), followed by the projection of the closed
hemisphere onto the ball (`TauCeti.hemisphereHomeomorph`).

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, proof of Theorem 5.
-/

public section

open Metric Set Function
open scoped RealInnerProductSpace

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E (sphere (0 : F) 1)]

/-- **A map of the sphere with a cellular inverse set over a pole is a disc over the closed
hemisphere.** Let `g` be a continuous surjection of the unit sphere `S` of a finite-dimensional real
inner product space `F` onto itself, modelled as a topological manifold on `E`, and let `p ∈ S`.
Suppose that over the closed hemisphere `{y | 0 ≤ ⟪y, p⟫}` the map `g` is injective except on the
cellular set `g⁻¹(p)`. Then `{x | 0 ≤ ⟪g x, p⟫}` is homeomorphic to the closed unit ball of
`(ℝ ∙ p)ᗮ`, by a homeomorphism `h` with `h x = g x` whenever `g x` is on the equator, and which
sends `x` to the boundary sphere of the ball exactly when `g x` is on the equator. -/
theorem IsCellularSet.exists_homeomorph_preimage_hemisphere
    {g : sphere (0 : F) 1 → sphere (0 : F) 1} {p : sphere (0 : F) 1}
    (hA : IsCellularSet E (g ⁻¹' {p})) (hg : Continuous g) (hgs : Surjective g)
    (hinj : ∀ x y, 0 ≤ ⟪(g x : F), (p : F)⟫ → g x = g y → x = y ∨ g x = p) :
    ∃ h : g ⁻¹' {y | 0 ≤ ⟪(y : F), (p : F)⟫} ≃ₜ closedBall (0 : (ℝ ∙ (p : F))ᗮ) 1,
      (∀ x : g ⁻¹' {y | 0 ≤ ⟪(y : F), (p : F)⟫},
        ⟪(g x : F), (p : F)⟫ = 0 → ((h x : (ℝ ∙ (p : F))ᗮ) : F) = g x) ∧
      ∀ x : g ⁻¹' {y | 0 ≤ ⟪(y : F), (p : F)⟫},
        ‖(h x : (ℝ ∙ (p : F))ᗮ)‖ = 1 ↔ ⟪(g x : F), (p : F)⟫ = 0 := by
  have hgp : Continuous fun x : sphere (0 : F) 1 ↦ ⟪(g x : F), (p : F)⟫ := by fun_prop
  have hpp : ⟪(p : F), (p : F)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  -- `h₀` identifies the preimage of the closed hemisphere with the closed hemisphere; the
  -- cellular set `g⁻¹(p)` lies in the preimage of the open hemisphere.
  obtain ⟨h₀, hoff, hin⟩ := hA.exists_homeomorph_image hg
    (K := g ⁻¹' {y | 0 ≤ ⟪(y : F), (p : F)⟫}) (U := g ⁻¹' {y | 0 < ⟪(y : F), (p : F)⟫})
    (isClosed_le continuous_const hgp).isCompact (isOpen_lt continuous_const hgp)
    (fun x hx ↦ by
      rw [mem_preimage, mem_singleton_iff] at hx
      rw [mem_preimage, mem_ofPred_eq, hx, hpp]
      exact one_pos)
    (preimage_mono fun _ hy ↦ by
      rw [mem_ofPred_eq] at hy ⊢
      exact hy.le)
    fun x hx y _ ↦ by
      simp only [mem_preimage, mem_singleton_iff]
      exact ⟨fun hxy ↦ (hinj x y hx hxy).imp_right fun hxp ↦ ⟨hxp, hxy.symm.trans hxp⟩,
        by rintro (rfl | ⟨hxp, hyp⟩); exacts [rfl, hxp.trans hyp.symm]⟩
  have hH := image_preimage_eq {y : sphere (0 : F) 1 | 0 ≤ ⟪(y : F), (p : F)⟫} hgs
  have hH' := image_preimage_eq {y : sphere (0 : F) 1 | 0 < ⟪(y : F), (p : F)⟫} hgs
  -- The image of the preimage of the closed hemisphere is the closed hemisphere itself.
  let e := (Homeomorph.refl (sphere (0 : F) 1)).subtype
    (p := (· ∈ g '' (g ⁻¹' {y : sphere (0 : F) 1 | 0 ≤ ⟪(y : F), (p : F)⟫})))
    (q := fun y : sphere (0 : F) 1 ↦ 0 ≤ ⟪(y : F), (p : F)⟫) fun y ↦ by
      rw [hH, Homeomorph.refl_apply, id_eq, mem_ofPred_eq]
  have he (x) : ((e (h₀ x) : sphere (0 : F) 1) : F) = ((h₀ x : sphere (0 : F) 1) : F) := by
    simp only [e, Homeomorph.subtype_apply_coe, Homeomorph.refl_apply, id_eq]
  refine ⟨h₀.trans (e.trans (hemisphereHomeomorph p)), fun x hx ↦ ?_,
    fun x ↦ (norm_hemisphereHomeomorph_apply_eq_one_iff p (e (h₀ x))).trans ?_⟩
  · have h₀x : ((h₀ x : sphere (0 : F) 1) : F) = g x :=
      congrArg Subtype.val <| hoff x fun hxU ↦ by
        rw [mem_preimage, mem_ofPred_eq, hx] at hxU
        exact lt_irrefl 0 hxU
    simp only [Homeomorph.trans_apply, coe_hemisphereHomeomorph_apply, he, h₀x, hx, zero_smul,
      sub_zero]
  · -- Over the open hemisphere `h₀` stays over the open hemisphere, and off it `h₀` is `g`.
    have hlt : 0 < ⟪((h₀ x : sphere (0 : F) 1) : F), (p : F)⟫ ↔ 0 < ⟪(g x : F), (p : F)⟫ := by
      simpa only [hH', mem_ofPred_eq, mem_preimage] using hin x
    have h₀H : 0 ≤ ⟪((h₀ x : sphere (0 : F) 1) : F), (p : F)⟫ := by
      simpa only [hH, mem_ofPred_eq] using (h₀ x).2
    have hxH : 0 ≤ ⟪(g x : F), (p : F)⟫ := x.2
    rw [he]
    simpa only [h₀H.lt_iff_ne', hxH.lt_iff_ne', ne_eq, not_iff_not] using hlt

end TauCeti
