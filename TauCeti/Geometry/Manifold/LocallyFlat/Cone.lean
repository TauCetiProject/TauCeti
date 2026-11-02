/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
import TauCeti.AlgebraicTopology.Sphere.CircleEmbedding
import TauCeti.Analysis.Complex.Conformal.Jordan.Schoenflies
import TauCeti.Analysis.InnerProductSpace.Sphere.Stereographic
import TauCeti.Geometry.Manifold.LocallyFlat.Linear

/-!
# Cones over Jordan curves in the 2-sphere are locally flat

Let `γ` be an embedding of the unit circle into the unit sphere `S²` of a three-dimensional real
inner product space `E`. The cone over `γ`, the map `r • u ↦ r • γ u` of the plane `ℂ` into `E`
(`TauCeti.sphereCone`), is a **locally flat** embedding with complementary model `ℝ`
(`TauCeti.isLocallyFlat_sphereCone`): around every point of its image, including the cone point
`0`, some chart of `E` carries the image onto the coordinate plane `ℂ × {0}`. Away from the cone
point this is the local flatness of the curve itself, but at the cone point it is a global
statement about the curve, which is where the Schoenflies theorem enters.

By the Schoenflies theorem on the 2-sphere
(`TauCeti.IsJordanCurve.exists_homeomorph_image_inner_eq_zero`), some homeomorphism `H` of `S²`
carries a great circle onto the image of `γ`; a point of `S²` off the curve exists since `S²` is
simply connected and the circle is not
(`TauCeti.not_surjective_of_continuous_injective_circle_sphere`). Reparametrizing the great circle
by a homeomorphism `τ` of the circle, `γ` is `H` composed with a linear isometric embedding `ι` of
the unit circle of `ℂ` as a great circle, precomposed with `τ`. Taking cones
(`Homeomorph.sphereCone`), the cone over `γ` is the homeomorphism `sphereCone H` of `E` applied to
the linear embedding `ι` of the plane, precomposed with the homeomorphism `sphereCone τ` of the
plane, and a linear plane in `E` is flat (`LinearMap.isLocallyFlat_of_injective`).

This is the local model of a piecewise-linear surface in a `3`-manifold: near a vertex such a
surface is the cone over a polygonal Jordan curve in a small sphere around the vertex. The analogue
fails one dimension up, which is why piecewise-linear embeddings need not be locally flat in
codimension two: the cone over a knotted circle in `S³` is a piecewise-linear disc in `ℝ⁴` that is
not locally flat at its cone point.

## Main results

* `TauCeti.isLocallyFlat_sphereCone`: the cone over an embedded circle in the 2-sphere is a locally
  flat embedding of the plane into three-space.

## References

* E. E. Moise, *Geometric Topology in Dimensions 2 and 3*, Springer GTM 47 (1977), for the
  Schoenflies theorem and for tame surfaces in `3`-manifolds.
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1, for stars and links of points of polyhedra.
-/

public section

open scoped InnerProductSpace

open Function Metric Module Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 3)]

/-- **The cone over a Jordan curve in the 2-sphere is locally flat.** For an embedding `γ` of the
unit circle into the unit sphere of a three-dimensional real inner product space `E`, the cone
`r • u ↦ r • γ u` is a locally flat embedding of the plane `ℂ` into `E`, with complementary model
`ℝ`. -/
theorem isLocallyFlat_sphereCone {γ : sphere (0 : ℂ) 1 → sphere (0 : E) 1} (hγ : Continuous γ)
    (hγi : Injective γ) : IsLocallyFlat ℂ ℝ (sphereCone fun u => (γ u : E)) := by
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
  let L : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (v : E))ᗮ :=
    complexIsometryOrthogonalSpanSingleton (ne_zero_of_mem_unit_sphere v)
  let ι : ℂ → E := fun z => (L z : E)
  /- The reparametrization `τ` of the circle with `γ = H ∘ ι ∘ τ` on the circle. -/
  have hmem (u : sphere (0 : ℂ) 1) : (H.symm (γ u) : E) ∈ (ℝ ∙ (v : E))ᗮ := by
    obtain ⟨x, hx, hxu⟩ : γ u ∈ H '' {x : sphere (0 : E) 1 | ⟪(x : E), (v : E)⟫_ℝ = 0} :=
      hH ▸ mem_range_self u
    rw [← hxu, H.symm_apply_apply]
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.2 hx
  let τ₀ : sphere (0 : ℂ) 1 → ℂ := fun u => L.symm ⟨H.symm (γ u), hmem u⟩
  have hτ₀ (u : sphere (0 : ℂ) 1) : ι (τ₀ u) = H.symm (γ u) := by
    simp [ι, τ₀]
  have hτ₀n (u : sphere (0 : ℂ) 1) : τ₀ u ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, ← L.norm_map]
    simp [τ₀]
  let τ₁ : sphere (0 : ℂ) 1 → sphere (0 : ℂ) 1 := fun u => ⟨τ₀ u, hτ₀n u⟩
  have hτc : Continuous τ₁ := by
    refine Continuous.subtype_mk ?_ _
    exact L.symm.continuous.comp ((H.symm.continuous.comp hγ).subtype_val.subtype_mk _)
  have hτb : Bijective τ₁ := by
    refine ⟨fun u u' huu' => hγi (H.symm.injective (Subtype.ext ?_)), fun w => ?_⟩
    · have := congrArg (fun z : sphere (0 : ℂ) 1 => ι z) huu'
      simpa [τ₁, hτ₀] using this
    · have hx : (L w : E) ∈ sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm]
        exact (L.norm_map w).trans (norm_eq_of_mem_sphere w)
      have hxe : (⟨(L w : E), hx⟩ : sphere (0 : E) 1) ∈ {x : sphere (0 : E) 1 |
          ⟪(x : E), (v : E)⟫_ℝ = 0} :=
        Submodule.mem_orthogonal_singleton_iff_inner_left.1 (L w).2
      obtain ⟨u, hu⟩ : H ⟨(L w : E), hx⟩ ∈ range γ := hH ▸ mem_image_of_mem H hxe
      refine ⟨u, Subtype.ext (L.injective ?_)⟩
      apply Subtype.ext
      simp [τ₁, τ₀, hu]
  let τ : sphere (0 : ℂ) 1 ≃ₜ sphere (0 : ℂ) 1 :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective τ₁ hτb) hτc
  /- Taking cones, the cone over `γ` is `sphereCone H ∘ ι ∘ sphereCone τ`. -/
  have key : (sphereCone fun u => (γ u : E)) = H.sphereCone ∘ ι ∘ τ.sphereCone := by
    funext z
    rcases eq_zero_or_exists_eq_smul_coe_sphere z with rfl | ⟨r, hr, u, rfl⟩
    · simp [ι]
    have hτu : ι (τ u) = H.symm (γ u) := hτ₀ u
    have hιs : ι (r • (τ u : ℂ)) = r • ι (τ u) := by
      simp only [ι, map_smul, Submodule.coe_smul]
    simp only [comp_apply, Homeomorph.coe_sphereCone, sphereCone_smul_coe hr.le]
    rw [hιs, hτu, sphereCone_smul_coe hr.le]
    simp
  /- The plane `ι` is flat, being linear. -/
  have hι : IsLocallyFlat ℂ ℝ ι := by
    refine LinearMap.isLocallyFlat_of_injective
      ((ℝ ∙ (v : E))ᗮ.subtype ∘ₗ L.toLinearEquiv.toLinearMap)
      (Subtype.val_injective.comp L.injective) ?_
    rw [Complex.finrank_real_complex, Module.finrank_self, Fact.out (p := finrank ℝ E = 3)]
  rw [key]
  exact (hι.comp_homeomorph τ.sphereCone).homeomorph_comp H.sphereCone

end TauCeti
