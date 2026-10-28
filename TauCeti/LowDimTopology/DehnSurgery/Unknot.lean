/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Sphere.HemisphereGraph
public import TauCeti.LowDimTopology.DehnSurgery.Filling
public import TauCeti.LowDimTopology.DehnSurgery.SeifertFraming
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Unknot

/-!
# Surgery on the unknot

The standard solid torus neighbourhood `TauCeti.unknotSolidTorus` of the unknot in `S³` has the
complementary solid torus as exterior (`TauCeti.unknotExteriorHomeomorph`), and on the common
boundary torus the two framings exchange meridian and longitude. This file computes the first two
surgeries on the unknot, which pin the slope convention of Dehn filling against the preferred
framing.

* **The framing is the preferred one.** The longitude `z ↦ Φ (1, z)` of `Φ = unknotSolidTorus`
  is the boundary of a meridian disc of the exterior solid torus, so it is null-homologous in the
  knot complement: the framing number of `Φ` is `0`
  (`TauCeti.framingNumber_unknotSolidTorus`), and the preferred framing of the boundary torus is
  the framing by `Φ` (`TauCeti.preferredFramedBoundaryTorus_unknotSolidTorus`). So slope values
  read in the framing of `Φ` are the surgery coefficients.
* **`∞`-surgery gives `S³`.** This is the trivial filling of any knot,
  `TauCeti.IsSolidTorusNeighborhood.meridianDehnFilling`.
* **`0`-surgery gives `S¹ × S²`** (`TauCeti.unknotZeroDehnFilling`). Write `S² ⊆ ℝ³` as the union
  of its closed upper and lower hemispheres, each a disc `D²` through `(x₀, x₁, x₂) ↦ x₀ + i x₁`
  (`TauCeti.hemisphereGraph`).
  Then `S¹ × S²` is the union of the solid tori `S¹ × D²₊` and `S¹ × D²₋`, glued along
  `S¹ × S¹` by the identity. The first is the exterior of the unknot, through
  `TauCeti.unknotExteriorHomeomorph`; since that identification exchanges the two circle factors
  on the boundary, the meridian of the second solid torus is glued to the longitude of `Φ`, the
  slope `0`.

## Main definitions

* `TauCeti.unknotZeroDehnFilling`: `S¹ × S²` as the Dehn filling of the exterior of the unknot
  along the longitude, the `0`-surgery on the unknot.

## Main results

* `TauCeti.framingNumber_unknotSolidTorus`: the standard solid torus neighbourhood of the unknot
  has framing number `0`.
* `TauCeti.preferredFramedBoundaryTorus_unknotSolidTorus`: its framing is the preferred framing.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Section 2E (the preferred framing,
  whose longitude is null-homologous in the exterior) and Chapter 9 (surgery on the unknot:
  `∞`-surgery gives `S³`, `0`-surgery gives `S¹ × S²`, and `p / q`-surgery gives the lens space
  `L(p, q)`).
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology TauCeti.HurewiczOne
open ContinuousMap (singularHomologyMap singularHomologyMap_comp singularHomologyMap_torusClass)

namespace TauCeti

/-! ### The preferred framing of the unknot -/

section Framing

variable
  (h₁ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 1).obj
    (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))))
  (h₂ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 2).obj
    (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))))

/-- The meridian discs `w ↦ (w, 1)` of the exterior of the unknot, as a map into the knot
complement. -/
private def exteriorMeridianDisc : C(closedBall (0 : ℂ) 1, ↥(range unknot)ᶜ) where
  toFun w := ⟨unknotExteriorHomeomorph.symm (w, 1), unknotExteriorHomeomorph_symm_notMem_range _⟩
  continuous_toFun := by fun_prop

/-- The boundary circle of the unit disc, as a loop in the closed disc. -/
private def diskBoundaryLoop :
    Path (SolidTorus.boundaryInclusion (1, 1)).1 (SolidTorus.boundaryInclusion (1, 1)).1 :=
  (torusCurve 1 0).map (continuous_fst.comp SolidTorus.isEmbedding_boundaryInclusion.continuous)

/-- **The standard framing of the unknot is the preferred framing.** The longitude
`z ↦ Φ (1, z)` of `Φ = TauCeti.unknotSolidTorus` bounds the meridian disc `w ↦ (w, 1)` of the
exterior solid torus, so it is null-homologous in the complement of the unknot, and the framing
number of `Φ` is `0`. -/
theorem framingNumber_unknotSolidTorus :
    isSolidTorusNeighborhood_unknotSolidTorus.framingNumber h₁ h₂ = 0 := by
  have hU := isSolidTorusNeighborhood_unknotSolidTorus
  have hmap (x) : hU.boundaryHomologyMap x =
      singularHomologyMap ℤ 1 (ContinuousMap.inclusion hU.frontier_subset_compl_range) x := by
    -- `singularHomologyMap` is an abbreviation for the induced map on homology.
    rw [IsSolidTorusNeighborhood.boundaryHomologyMap_def]
    rfl
  rw [IsSolidTorusNeighborhood.framingNumber_eq_iff, zero_smul, hmap,
    FramedBoundaryTorus.ofHomeomorph_basis_one,
    FramedBoundaryTorus.torusCurveClass_eq_singularHomologyMap, ← singularHomologyMap_comp,
    singularHomologyMap_torusClass]
  -- The longitude is the boundary of a meridian disc of the exterior, which is contractible.
  have : ContractibleSpace (closedBall (0 : ℂ) 1) :=
    (convex_closedBall 0 1).contractibleSpace ⟨0, by simp⟩
  have hdisc := (SimplyConnectedSpace.paths_homotopic diskBoundaryLoop (Path.refl _)).map
    exteriorMeridianDisc
  rw [loopClass_eq_of_apply_eq _ (diskBoundaryLoop.map exteriorMeridianDisc.continuous) fun t ↦ ?_,
    (loopClass_eq_iff _ _).2 (pathChain_sub_mem_boundaries₁_of_homotopy hdisc.some),
    loopClass_eq_of_apply_eq ((Path.refl _).map exteriorMeridianDisc.continuous) (Path.refl _)
      fun _ ↦ rfl, loopClass_refl, map_zero]
  -- Pointwise, the longitude is the boundary of the meridian disc, read through the exchange of
  -- the circle factors on the boundary torus.
  have hp : ((SolidTorus.boundaryInclusion (torusCurve 1 0 t)).1, (1 : Circle)) =
      SolidTorus.boundaryInclusion (torusCurve 0 1 t).swap := by
    ext <;> simp
  apply Subtype.ext
  calc _ = unknotSolidTorus (SolidTorus.boundaryInclusion (torusCurve 0 1 t)) :=
        IsSolidTorusNeighborhood.coe_exteriorFrontierHomeomorph_apply _ _
    _ = unknotExteriorHomeomorph.symm ((SolidTorus.boundaryInclusion (torusCurve 1 0 t)).1, 1) := by
        rw [hp, unknotExteriorHomeomorph_symm_boundaryInclusion, Prod.swap_swap]
    -- The loop on the right evaluates to this point by the definitions of the private disc map
    -- and loop above.
    _ = _ := (rfl)

/-- The preferred framing of the boundary torus of the exterior of the unknot is its framing by
the standard solid torus neighbourhood `TauCeti.unknotSolidTorus`. -/
theorem preferredFramedBoundaryTorus_unknotSolidTorus :
    isSolidTorusNeighborhood_unknotSolidTorus.preferredFramedBoundaryTorus h₁ h₂ =
      isSolidTorusNeighborhood_unknotSolidTorus.framedBoundaryTorus := by
  rw [IsSolidTorusNeighborhood.preferredFramedBoundaryTorus, framingNumber_unknotSolidTorus,
    neg_zero, FramedBoundaryTorus.shiftLongitude_zero]

end Framing

/-! ### `0`-surgery on the unknot -/

section ZeroSurgery

/-- The solid torus `D² × S¹` carried onto the solid torus `S¹ × D²₊` or `S¹ × D²₋` of `S¹ × S²`,
according to the sign `c`. -/
private def capProd {c : ℝ} (hc : c ^ 2 = 1) (p : SolidTorus) :
    Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  (p.2, hemisphereGraph hc p.1)

private theorem isClosedEmbedding_capProd {c : ℝ} (hc : c ^ 2 = 1) :
    IsClosedEmbedding (capProd hc) :=
  (continuous_snd.prodMk ((continuous_hemisphereGraph hc).comp continuous_fst)).isClosedEmbedding
    fun _ _ h ↦ Prod.ext (eq_of_hemisphereGraph_eq (hc := hc) (hc' := hc) (congrArg Prod.snd h))
      (congrArg Prod.fst h)

/-- **`0`-surgery on the unknot is `S¹ × S²`.** The product `S¹ × S²` is the Dehn filling of the
exterior of the unknot along the longitude of its standard solid torus neighbourhood, the slope
`0` in the preferred framing (`TauCeti.preferredFramedBoundaryTorus_unknotSolidTorus`,
`TauCeti.FramedBoundaryTorus.value_longitude`). The exterior is the solid torus `S¹ × D²₊` over
the upper hemisphere and the filling solid torus is `S¹ × D²₋` over the lower one. -/
def unknotZeroDehnFilling :
    DehnFilling isSolidTorusNeighborhood_unknotSolidTorus
      isSolidTorusNeighborhood_unknotSolidTorus.framedBoundaryTorus.longitude
      (Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) where
  exteriorEmbedding := capProd (c := 1) (one_pow 2) ∘ unknotExteriorHomeomorph
  isClosedEmbedding_exteriorEmbedding :=
    (isClosedEmbedding_capProd _).comp unknotExteriorHomeomorph.isClosedEmbedding
  solidTorusEmbedding := capProd (c := -1) (by norm_num)
  isClosedEmbedding_solidTorusEmbedding := isClosedEmbedding_capProd _
  gluing := Homeomorph.prodComm Circle Circle
  exteriorEmbedding_exteriorBoundaryInclusion q := by
    -- On the boundary torus the exterior exchanges the two circle factors.
    have hq : isSolidTorusNeighborhood_unknotSolidTorus.exteriorBoundaryInclusion
        (Homeomorph.prodComm Circle Circle q) =
          unknotExteriorHomeomorph.symm (SolidTorus.boundaryInclusion q) :=
      Subtype.ext (by
        rw [IsSolidTorusNeighborhood.coe_exteriorBoundaryInclusion_apply,
          unknotExteriorHomeomorph_symm_boundaryInclusion, Homeomorph.coe_prodComm])
    rw [Function.comp_apply, hq, Homeomorph.apply_symm_apply]
    exact Prod.ext rfl (hemisphereGraph_eq_of_norm_eq_one (one_pow 2) (by norm_num) (by simp))
  range_union_range := by
    refine eq_univ_of_forall fun y ↦ ?_
    rcases le_total 0 ((y.2 : EuclideanSpace ℝ (Fin 3)) 2) with hy | hy
    · obtain ⟨u, hu⟩ := exists_hemisphereGraph_eq (c := 1) (one_pow 2) y.2 (by simpa using hy)
      exact Or.inl ⟨unknotExteriorHomeomorph.symm (u, y.1), by simp [capProd, hu]⟩
    · obtain ⟨u, hu⟩ := exists_hemisphereGraph_eq (c := -1) (by norm_num) y.2 (by simpa using hy)
      exact Or.inr ⟨(u, y.1), by simp [capProd, hu]⟩
  range_inter_range_subset := by
    rintro _ ⟨⟨x, rfl⟩, ⟨p, hp⟩⟩
    have hnorm := norm_eq_one_of_hemisphereGraph_eq (by norm_num) (congrArg Prod.snd hp).symm
    refine ⟨(⟨p.1, mem_sphere_zero_iff_norm.mpr hnorm⟩, p.2), ?_⟩
    rw [Function.comp_apply, ← hp]
    exact congrArg _ (Prod.ext (Subtype.ext (SolidTorus.coe_boundaryInclusion_fst _))
      (SolidTorus.boundaryInclusion_snd _))
  fillingSlope_gluing := isSolidTorusNeighborhood_unknotSolidTorus.fillingSlope_prodComm

/-- The `0`-surgery on the unknot embeds its exterior as the solid torus `S¹ × D²₊` over the upper
hemisphere, through `TauCeti.unknotExteriorHomeomorph`. -/
@[simp]
theorem unknotZeroDehnFilling_exteriorEmbedding_apply
    (x : knotExterior (Φ := unknotSolidTorus)) :
    unknotZeroDehnFilling.exteriorEmbedding x =
      ((unknotExteriorHomeomorph x).2,
        hemisphereGraph (one_pow 2) (unknotExteriorHomeomorph x).1) :=
  (rfl)

/-- The filling solid torus of the `0`-surgery on the unknot is the solid torus `S¹ × D²₋` over
the lower hemisphere. -/
@[simp]
theorem unknotZeroDehnFilling_solidTorusEmbedding_apply (p : SolidTorus) :
    unknotZeroDehnFilling.solidTorusEmbedding p =
      (p.2, hemisphereGraph (c := -1) (by norm_num) p.1) :=
  (rfl)

/-- The `0`-surgery on the unknot glues the boundary tori by exchanging the circle factors. -/
@[simp]
theorem unknotZeroDehnFilling_gluing :
    unknotZeroDehnFilling.gluing = Homeomorph.prodComm Circle Circle :=
  (rfl)

end ZeroSurgery

end TauCeti
