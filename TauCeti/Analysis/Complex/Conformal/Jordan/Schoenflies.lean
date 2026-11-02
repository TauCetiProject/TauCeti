/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import TauCeti.Analysis.Complex.Conformal.Jordan.Complement
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve
import TauCeti.Analysis.InnerProductSpace.Sphere.Stereographic
import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone
import TauCeti.Logic.Equiv.Set

/-!
# The Schoenflies theorem

**Every Jordan curve in the plane is ambiently a round circle**: for a Jordan curve `C ⊆ ℂ` there
is a homeomorphism of `ℂ` carrying the unit circle onto `C`, the open unit disc onto the inside
`filledHull C \ C` of `C` and the closed unit disc onto its closure `filledHull C`
(`TauCeti.IsJordanCurve.exists_homeomorph_image_sphere`). The centre may be sent to any prescribed
point of the inside (`TauCeti.IsJordanCurve.exists_homeomorph_image_sphere_of_mem`). The Jordan
curve theorem only says that `C` separates the plane into two components with frontier `C`; the
Schoenflies theorem says in addition that the pair `(ℂ, C)` is standard.

The proof assembles the two halves of Carathéodory's theorem for the complementary domains of `C`.
The inside half `g` is a homeomorphism of the closed unit disc onto `filledHull C`
(`TauCeti.IsJordanCurve.exists_homeomorph_closedBall_filledHull`), and the outside half `h` is a
homeomorphism of the closed exterior `(ball 0 1)ᶜ` onto the closure `(filledHull C \ C)ᶜ` of the
outside (`TauCeti.IsJordanCurve.exists_homeomorph_compl_ball_compl_filledHull_sdiff`); both carry
the unit circle onto `C`, but they need not agree there. Their discrepancy `σ = h⁻¹ ∘ g` on the
circle is a homeomorphism of the circle, and its cone `Homeomorph.sphereCone σ` is a
norm-preserving homeomorphism of `ℂ`. So `g` on the closed disc and `h ∘ sphereCone σ` on the
closed exterior agree on the circle and glue to a continuous bijection of `ℂ`. It is proper, since
`h` tends to infinity at infinity, hence closed, hence a homeomorphism.

On the unit sphere `S²` of a three-dimensional real inner product space the same holds with a great
circle as the round model: for a Jordan curve `C ⊆ S²` and a point `v ∉ C`, a homeomorphism of `S²`
fixing `v` carries the great circle `⟪x, v⟫ = 0` onto `C`
(`TauCeti.IsJordanCurve.exists_homeomorph_image_inner_eq_zero`). Stereographic projection from `v`
identifies `S²` with the one-point compactification of `ℂ`, the great circle going to the unit
circle (`TauCeti.exists_onePoint_homeomorph_sphere_preimage_inner_eq_zero`), and the planar
homeomorphism extends to the point at infinity.

## Main results

* `TauCeti.IsJordanCurve.exists_homeomorph_image_sphere_of_mem`: a homeomorphism of `ℂ` sending
  `0` to a given point of the inside of `C` and the unit circle, open disc and closed disc onto
  `C`, its inside and its closure.
* `TauCeti.IsJordanCurve.exists_homeomorph_image_sphere`: **the Schoenflies theorem**.
* `TauCeti.IsJordanCurve.exists_homeomorph_image_inner_eq_zero`: the Schoenflies theorem on the
  2-sphere.

## References

* A. Schoenflies, *Beiträge zur Theorie der Punktmengen. III*, Math. Ann. 62 (1906), 286–328.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer (1992), Chapter 2, for
  Carathéodory's theorem, from which the Schoenflies theorem follows.
* E. E. Moise, *Geometric Topology in Dimensions 2 and 3*, Springer GTM 47 (1977), for the
  Schoenflies theorem in the plane.
-/

public section

open Bornology Filter Function Metric Set Topology

namespace TauCeti

variable {C : Set ℂ} {p : ℂ}

/-- **The Schoenflies theorem, centred at a point of the inside.** For a Jordan curve `C ⊆ ℂ` and a
point `p` of its inside `filledHull C \ C`, there is a homeomorphism `e` of `ℂ` with `e 0 = p`
carrying the unit circle onto `C`, the open unit disc onto the inside of `C`, and the closed unit
disc onto `filledHull C`. -/
theorem IsJordanCurve.exists_homeomorph_image_sphere_of_mem (hC : IsJordanCurve C)
    (hp : p ∈ filledHull C \ C) :
    ∃ e : ℂ ≃ₜ ℂ, e 0 = p ∧ e '' sphere 0 1 = C ∧ e '' ball 0 1 = filledHull C \ C ∧
      e '' closedBall 0 1 = filledHull C := by
  obtain ⟨g, hgc, -, hgb, hgs, hg0, e₁, he₁⟩ := hC.exists_homeomorph_closedBall_filledHull hp
  obtain ⟨h, hhc, -, hhb, hhs, hht, -⟩ := hC.exists_homeomorph_compl_ball_compl_filledHull_sdiff
  have hg : BijOn g (closedBall 0 1) (filledHull C) := BijOn.of_equiv_coe e₁.toEquiv he₁
  have hsph : sphere (0 : ℂ) 1 ⊆ (ball 0 1)ᶜ := fun z hz => by
    simp [mem_sphere_zero_iff_norm.1 hz]
  /- The circle homeomorphism `σ = h⁻¹ ∘ g` comparing the two parametrizations of `C`. -/
  let Φg : sphere (0 : ℂ) 1 ≃ₜ C := Continuous.homeoOfEquivCompactToT2 (f := hgs.equiv g)
    ((hgc.mono sphere_subset_closedBall).mapsToRestrict hgs.mapsTo)
  let Φh : sphere (0 : ℂ) 1 ≃ₜ C := Continuous.homeoOfEquivCompactToT2 (f := hhs.equiv h)
    ((hhc.mono hsph).mapsToRestrict hhs.mapsTo)
  let σ : sphere (0 : ℂ) 1 ≃ₜ sphere (0 : ℂ) 1 := Φg.trans Φh.symm
  have hσ (u : sphere (0 : ℂ) 1) : h (σ u) = g u := by
    have : Φh (σ u) = Φg u := Φh.apply_symm_apply (Φg u)
    exact congrArg Subtype.val this
  /- Its cone `R` is a norm-preserving homeomorphism of `ℂ`, which on the circle is `σ`. -/
  let R : ℂ ≃ₜ ℂ := σ.sphereCone
  have hR (z : ℂ) : ‖R z‖ = ‖z‖ := σ.norm_sphereCone_apply z
  have hRs (z : ℂ) : ‖R.symm z‖ = ‖z‖ := by
    simp only [R, Homeomorph.sphereCone_symm, Homeomorph.norm_sphereCone_apply]
  have hagree (z : ℂ) (hz : ‖z‖ = 1) : g z = h (R z) := by
    have hu : z ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.2 hz
    have : R z = σ ⟨z, hu⟩ := σ.sphereCone_apply_coe ⟨z, hu⟩
    rw [this, hσ]
  /- The glued map `H`: `g` on the closed disc, `h ∘ R` on the closed exterior. -/
  let H : ℂ → ℂ := fun z => if ‖z‖ ≤ 1 then g z else h (R z)
  have hHc : Continuous H := by
    refine continuous_if_le continuous_norm continuous_const
      (hgc.mono fun z hz => mem_closedBall_zero_iff.2 hz) ?_ fun z hz => hagree z hz
    refine hhc.comp R.continuous.continuousOn fun z (hz : 1 ≤ ‖z‖) => ?_
    simpa [hR] using hz
  have hRb : BijOn R (closedBall 0 1)ᶜ (closedBall 0 1)ᶜ := by
    refine ⟨fun z hz => by simpa [hR] using hz, R.injective.injOn, fun w hw => ?_⟩
    exact ⟨R.symm w, by simpa [hRs] using hw, R.apply_symm_apply w⟩
  have hHg : EqOn g H (closedBall 0 1) := fun z hz => by
    simp [H, mem_closedBall_zero_iff.1 hz]
  have hHh : EqOn (h ∘ R) H (closedBall 0 1)ᶜ := fun z hz => by
    have : ¬ ‖z‖ ≤ 1 := by simpa using hz
    simp [H, this]
  /- `H` is a bijection: `g` fills `filledHull C` from the closed disc, and `h ∘ R` fills its
  complement from the exterior of the disc. -/
  have hbij : Bijective H := by
    have h₁ : BijOn H (closedBall 0 1) (filledHull C) := hg.congr hHg
    have h₂ : BijOn H (closedBall 0 1)ᶜ (filledHull C)ᶜ := (hhb.comp hRb).congr hHh
    have hinj : InjOn H (closedBall 0 1 ∪ (closedBall 0 1)ᶜ) := by
      rw [injOn_union disjoint_compl_right]
      exact ⟨h₁.injOn, h₂.injOn, fun x hx y hy hxy => h₂.mapsTo hy (hxy ▸ h₁.mapsTo hx)⟩
    have := h₁.union h₂ hinj
    rw [union_compl_self, union_compl_self] at this
    exact bijOn_univ.1 this
  /- `H` tends to infinity at infinity, so it is proper and hence closed. -/
  have hHt : Tendsto H (cocompact ℂ) (cocompact ℂ) := by
    rw [← cobounded_eq_cocompact]
    have hRt : Tendsto R (cobounded ℂ) (cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      simpa [hR] using tendsto_norm_cobounded_atTop
    refine (hht.comp hRt).congr' ?_
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 1] with z hz
    exact hHh (by simpa using hz)
  have hHom : IsHomeomorph H := isHomeomorph_iff_continuous_isClosedMap_bijective.2
    ⟨hHc, (isProperMap_iff_tendsto_cocompact.2 ⟨hHc, hHt⟩).isClosedMap, hbij⟩
  have hcoe : ⇑(hHom.homeomorph H) = H := by
    ext z
    simp
  refine ⟨hHom.homeomorph H, ?_, ?_, ?_, ?_⟩
  · simpa [H] using hg0
  · rw [hcoe, ← (hHg.mono sphere_subset_closedBall).image_eq, hgs.image_eq]
  · rw [hcoe, ← (hHg.mono ball_subset_closedBall).image_eq, hgb.image_eq]
  · rw [hcoe, ← hHg.image_eq, hg.image_eq]

/-- **The Schoenflies theorem.** For every Jordan curve `C ⊆ ℂ` there is a homeomorphism of `ℂ`
carrying the unit circle onto `C`, the open unit disc onto the inside `filledHull C \ C` of `C`, and
the closed unit disc onto `filledHull C`. -/
theorem IsJordanCurve.exists_homeomorph_image_sphere (hC : IsJordanCurve C) :
    ∃ e : ℂ ≃ₜ ℂ, e '' sphere 0 1 = C ∧ e '' ball 0 1 = filledHull C \ C ∧
      e '' closedBall 0 1 = filledHull C := by
  obtain ⟨p, hp⟩ := hC.nonempty_filledHull_sdiff
  obtain ⟨e, -, he⟩ := hC.exists_homeomorph_image_sphere_of_mem hp
  exact ⟨e, he⟩

/-! ### The Schoenflies theorem on the 2-sphere -/

section Sphere

open scoped InnerProductSpace

open Module OnePoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 3)]

/-- **The Schoenflies theorem on the 2-sphere.** Let `C` be a Jordan curve in the unit sphere of a
three-dimensional real inner product space, and `v` a point of the sphere off `C`. Then some
homeomorphism of the sphere fixing `v` carries the great circle `⟪x, v⟫ = 0` onto `C`. -/
theorem IsJordanCurve.exists_homeomorph_image_inner_eq_zero {C : Set (sphere (0 : E) 1)}
    (hC : IsJordanCurve C) {v : sphere (0 : E) 1} (hv : v ∉ C) :
    ∃ e : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1, e v = v ∧
      e '' {x | ⟪(x : E), (v : E)⟫_ℝ = 0} = C := by
  obtain ⟨K, hKinf, hpre⟩ := exists_onePoint_homeomorph_sphere_preimage_inner_eq_zero v
  /- The curve, read in the plane, is a Jordan curve. -/
  set C' : Set ℂ := (↑) ⁻¹' (K ⁻¹' C) with hC'
  have himg : ((↑) : ℂ → OnePoint ℂ) '' C' = K.symm '' C := by
    rw [hC', image_preimage_eq_inter_range, K.image_symm]
    refine inter_eq_left.2 fun q hq => ?_
    induction q using OnePoint.rec with
    | infty => exact absurd (hKinf ▸ hq : v ∈ C) hv
    | coe z => exact mem_range_self z
  have hC'J : IsJordanCurve C' := by
    have hJ := hC.image_homeomorph K.symm
    have hcl : IsClosed (((↑) : ℂ → OnePoint ℂ) '' C') := himg ▸ hJ.isCompact.isClosed
    refine IsJordanCurve.of_image (isClosed_image_coe.1 hcl).2 continuous_coe.continuousOn
      coe_injective.injOn ?_
    rwa [himg]
  /- The Schoenflies homeomorphism of the plane, extended to the point at infinity. -/
  obtain ⟨e, he, -, -⟩ := hC'J.exists_homeomorph_image_sphere
  refine ⟨K.symm.trans (e.onePointCongr.trans K), ?_, ?_⟩
  · simp only [Homeomorph.trans_apply, ← hKinf, Homeomorph.symm_apply_apply,
      Homeomorph.onePointCongr_apply, map_infty]
  · have hcomp (S : Set (sphere (0 : E) 1)) :
        K.symm.trans (e.onePointCongr.trans K) '' S = K '' (e.onePointCongr '' (K.symm '' S)) := by
      rw [image_image, image_image]
      exact image_congr fun x _ => Homeomorph.trans_apply _ _ x
    have hext : e.onePointCongr '' ((↑) '' sphere (0 : ℂ) 1) = (↑) '' (e '' sphere 0 1) := by
      rw [image_image, image_image]
      simp
    rw [hcomp, K.image_symm, hpre, hext, he, himg, K.image_symm, K.image_preimage]

end Sphere

end TauCeti
