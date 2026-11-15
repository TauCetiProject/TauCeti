/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import TauCeti.Analysis.Complex.Conformal.Jordan.Complement
import TauCeti.AlgebraicTopology.Sphere.CircleEmbedding
import TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve
import TauCeti.Analysis.InnerProductSpace.Sphere.Stereographic
import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone
import TauCeti.Logic.Equiv.Set
import TauCeti.Topology.Homeomorph.Piecewise

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
closed exterior agree on the circle, and since `h` tends to infinity at infinity they glue to a
homeomorphism of `ℂ` (`TauCeti.exists_homeomorph_of_bijOn_closedBall_compl`).

On the unit sphere `S²` of a three-dimensional real inner product space the same holds with a great
circle as the round model: for a Jordan curve `C ⊆ S²` and a point `v ∉ C`, a homeomorphism of `S²`
fixing `v` carries the great circle `⟪x, v⟫ = 0` onto `C`
(`TauCeti.IsJordanCurve.exists_homeomorph_image_inner_eq_zero`). Stereographic projection from `v`
identifies `S²` with the one-point compactification of `ℂ`, the great circle going to the unit
circle (`TauCeti.exists_onePoint_homeomorph_sphere_preimage_inner_eq_zero`), and the planar
homeomorphism extends to the point at infinity.
Since an embedded circle misses a point of `S²`
(`TauCeti.not_surjective_of_continuous_injective_circle_sphere`), every embedding `γ` of the unit
circle into `S²` is `H ∘ L ∘ τ` for a homeomorphism `H` of `S²`, a linear isometric embedding `L`
of `ℂ` restricted to its unit circle, and a homeomorphism `τ` of the circle
(`TauCeti.exists_homeomorph_comp_eq_of_continuous_injective`).

## Main results

* `TauCeti.IsJordanCurve.exists_homeomorph_image_sphere_of_mem`: a homeomorphism of `ℂ` sending
  `0` to a given point of the inside of `C` and the unit circle, open disc and closed disc onto
  `C`, its inside and its closure.
* `TauCeti.IsJordanCurve.exists_homeomorph_image_sphere`: **the Schoenflies theorem**.
* `TauCeti.IsJordanCurve.exists_homeomorph_image_inner_eq_zero`: the Schoenflies theorem on the
  2-sphere.
* `TauCeti.exists_homeomorph_comp_eq_of_continuous_injective`: an embedded circle in the 2-sphere
  is a reparametrized great circle composed with a homeomorphism of the sphere.

## References

* A. Schoenflies, *Beiträge zur Theorie der Punktmengen. III*, Math. Ann. 62 (1906), 286–328.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer (1992), Chapter 2, for
  Carathéodory's theorem, from which the Schoenflies theorem follows.
* E. E. Moise, *Geometric Topology in Dimensions 2 and 3*, Springer GTM 47 (1977), for the
  Schoenflies theorem in the plane.
-/

public section

open Function Metric Set

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
  have hg : BijOn g (closedBall 0 1) (filledHull C) := Equiv.bijOn_of_coe_eq e₁.toEquiv he₁
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
  have hagree : EqOn g (h ∘ R) (sphere 0 1) := fun z hz => by
    have : R z = σ ⟨z, hz⟩ := σ.sphereCone_apply_coe ⟨z, hz⟩
    rw [comp_apply, this, hσ]
  /- Gluing `g` on the closed disc with `h ∘ R` on the closed exterior. -/
  have hRc : MapsTo R (ball 0 1)ᶜ (ball 0 1)ᶜ := fun z hz => by simpa [R] using hz
  obtain ⟨e, heg, -⟩ := exists_homeomorph_of_bijOn_closedBall_compl hgc hg
    (hhc.comp R.continuous.continuousOn hRc)
    (hhb.comp ((σ.bijOn_sphereCone_closedBall 1).compl R.bijective)) hagree
    (hht.comp σ.tendsto_sphereCone_cobounded)
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · rw [heg (mem_closedBall_self zero_le_one), hg0]
  · rw [(heg.mono sphere_subset_closedBall).image_eq, hgs.image_eq]
  · rw [(heg.mono ball_subset_closedBall).image_eq, hgb.image_eq]
  · rw [heg.image_eq, hg.image_eq]

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

/-- **Every embedded circle in the 2-sphere is a reparametrized great circle, up to a homeomorphism
of the sphere.** For an embedding `γ` of the unit circle into the unit sphere of a
three-dimensional real inner product space `E`, there are a linear isometric embedding
`L : ℂ → E`, a homeomorphism `H` of the sphere and a homeomorphism `τ` of the circle with
`H⁻¹ ∘ γ = L ∘ τ`. -/
theorem exists_homeomorph_comp_eq_of_continuous_injective
    {γ : sphere (0 : ℂ) 1 → sphere (0 : E) 1} (hγ : Continuous γ) (hγi : Injective γ) :
    ∃ (L : ℂ →ₗᵢ[ℝ] E) (H : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1)
      (τ : sphere (0 : ℂ) 1 ≃ₜ sphere (0 : ℂ) 1),
      Subtype.val ∘ H.symm ∘ γ = L ∘ Subtype.val ∘ τ := by
  have : Fact (finrank ℝ E = 2 + 1) := ⟨Fact.out (p := finrank ℝ E = 3)⟩
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 2
  /- A homeomorphism `H` of the sphere carrying the great circle `vᗮ` onto the curve, for a point
  `v` off the curve. -/
  have hrank : 2 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank, Fact.out (p := finrank ℝ E = 3)]
    norm_num
  obtain ⟨v, hv⟩ : ∃ v, v ∉ range γ := by
    simpa [Surjective] using not_surjective_of_continuous_injective_circle_sphere hrank hγ hγi
  have hJ : IsJordanCurve (range γ) := by
    have h0 : IsJordanCurve (univ : Set (sphere (0 : ℂ) 1)) :=
      isJordanCurve_iff.2 ⟨(Homeomorph.Set.univ _).trans (sphereCircleHomeomorph 0 one_pos)⟩
    simpa [image_univ] using h0.image hγ.continuousOn hγi.injOn
  obtain ⟨H, -, hH⟩ := hJ.exists_homeomorph_image_inner_eq_zero hv
  /- The plane `vᗮ`, parametrized isometrically by `ℂ`. -/
  let L₀ : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (v : E))ᗮ :=
    complexIsometryOrthogonalSpanSingleton (ne_zero_of_mem_unit_sphere v)
  let L : ℂ →ₗᵢ[ℝ] E := (ℝ ∙ (v : E))ᗮ.subtypeₗᵢ.comp L₀.toLinearIsometry
  /- The reparametrization `τ` of the circle with `H⁻¹ ∘ γ = L ∘ τ` on the circle. -/
  have hmem (u : sphere (0 : ℂ) 1) : (H.symm (γ u) : E) ∈ (ℝ ∙ (v : E))ᗮ := by
    obtain ⟨x, hx, hxu⟩ : γ u ∈ H '' {x : sphere (0 : E) 1 | ⟪(x : E), (v : E)⟫_ℝ = 0} :=
      hH ▸ mem_range_self u
    rw [← hxu, H.symm_apply_apply]
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.2 hx
  let τ₀ : sphere (0 : ℂ) 1 → ℂ := fun u => L₀.symm ⟨H.symm (γ u), hmem u⟩
  have hτ₀ (u : sphere (0 : ℂ) 1) : L (τ₀ u) = H.symm (γ u) := by
    simp [L, τ₀]
  have hτ₀n (u : sphere (0 : ℂ) 1) : τ₀ u ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, ← L₀.norm_map]
    simp [τ₀]
  let τ₁ : sphere (0 : ℂ) 1 → sphere (0 : ℂ) 1 := fun u => ⟨τ₀ u, hτ₀n u⟩
  have hτc : Continuous τ₁ := by
    refine Continuous.subtype_mk ?_ _
    exact L₀.symm.continuous.comp ((H.symm.continuous.comp hγ).subtype_val.subtype_mk _)
  have hτb : Bijective τ₁ := by
    refine ⟨fun u u' huu' => hγi (H.symm.injective (Subtype.ext ?_)), fun w => ?_⟩
    · have := congrArg (fun z : sphere (0 : ℂ) 1 => L z) huu'
      simpa [τ₁, hτ₀] using this
    · have hx : (L₀ w : E) ∈ sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm]
        exact (L₀.norm_map w).trans (norm_eq_of_mem_sphere w)
      have hxe : (⟨(L₀ w : E), hx⟩ : sphere (0 : E) 1) ∈ {x : sphere (0 : E) 1 |
          ⟪(x : E), (v : E)⟫_ℝ = 0} :=
        Submodule.mem_orthogonal_singleton_iff_inner_left.1 (L₀ w).2
      obtain ⟨u, hu⟩ : H ⟨(L₀ w : E), hx⟩ ∈ range γ := hH ▸ mem_image_of_mem H hxe
      refine ⟨u, Subtype.ext (L₀.injective ?_)⟩
      apply Subtype.ext
      simp [τ₁, τ₀, hu]
  let τ : sphere (0 : ℂ) 1 ≃ₜ sphere (0 : ℂ) 1 :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective τ₁ hτb) hτc
  exact ⟨L, H, τ, funext fun u => (hτ₀ u).symm⟩

end Sphere

end TauCeti
