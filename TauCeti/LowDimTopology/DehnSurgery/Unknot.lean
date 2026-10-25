/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
  of its closed upper and lower hemispheres, each a disc `D²` through `(x₀, x₁, x₂) ↦ x₀ + i x₁`.
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

/-- The exterior of the unknot misses the unknot. -/
private theorem unknotExteriorHomeomorph_symm_notMem_range (p : SolidTorus) :
    (unknotExteriorHomeomorph.symm p : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∉ range unknot :=
  fun hp ↦ (mem_knotExterior.mp (unknotExteriorHomeomorph.symm p).2)
    (isSolidTorusNeighborhood_unknotSolidTorus.range_subset_image hp)

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

/-- The point `(Re u, Im u, c √(1 - ‖u‖²))` of `ℝ³`; for `c = 1` and `c = -1` this is the upper and
the lower hemisphere of `S²` over the closed unit disc. -/
private def capPoint (c : ℝ) (u : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[u.re, u.im, c * √(1 - ‖u‖ ^ 2)]

private theorem capPoint_mem_sphere {c : ℝ} (hc : c ^ 2 = 1) (u : closedBall (0 : ℂ) 1) :
    capPoint c u ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  have hu : ‖(u : ℂ)‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp u.2)
  rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [capPoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_pow, hc, one_mul]
  rw [Real.sq_sqrt (sub_nonneg.mpr hu), Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The hemisphere of `S²` over the closed unit disc on the side of the sign `c`. -/
private def cap {c : ℝ} (hc : c ^ 2 = 1) (u : closedBall (0 : ℂ) 1) :
    sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨capPoint c u, capPoint_mem_sphere hc u⟩

private theorem continuous_cap {c : ℝ} (hc : c ^ 2 = 1) : Continuous (cap hc) := by
  refine Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp ?_) _
  fun_prop

/-- The first two coordinates of a point of a hemisphere recover the point of the disc. -/
private theorem coe_eq_of_cap_eq {c c' : ℝ} {hc : c ^ 2 = 1} {hc' : c' ^ 2 = 1}
    {u v : closedBall (0 : ℂ) 1} (h : cap hc u = cap hc' v) : u = v := by
  have hi (i : Fin 3) := congrArg
    (fun x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (x : EuclideanSpace ℝ (Fin 3)) i) h
  refine Subtype.ext (Complex.ext ?_ ?_)
  · simpa [cap, capPoint] using hi 0
  · simpa [cap, capPoint] using hi 1

/-- The two hemispheres agree on the equator. -/
private theorem cap_eq_cap_of_norm_eq_one {c c' : ℝ} (hc : c ^ 2 = 1) (hc' : c' ^ 2 = 1)
    {u : closedBall (0 : ℂ) 1} (hu : ‖(u : ℂ)‖ = 1) : cap hc u = cap hc' u := by
  ext i
  fin_cases i <;> simp [cap, capPoint, hu]

/-- The upper and the lower hemisphere meet only over the boundary of the disc. -/
private theorem norm_eq_one_of_cap_eq {u v : closedBall (0 : ℂ) 1}
    (h : cap (c := 1) (one_pow 2) u = cap (c := -1) (by norm_num) v) : ‖(v : ℂ)‖ = 1 := by
  have huv := coe_eq_of_cap_eq h
  subst huv
  have h2 :=
    congrArg (fun x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (x : EuclideanSpace ℝ (Fin 3)) 2) h
  simp only [cap, capPoint, PiLp.toLp_apply, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, one_mul, neg_one_mul] at h2
  have hs : √(1 - ‖(u : ℂ)‖ ^ 2) = 0 := by linarith
  rw [Real.sqrt_eq_zero', sub_nonpos] at hs
  exact le_antisymm (mem_closedBall_zero_iff.mp u.2) ((one_le_sq_iff₀ (norm_nonneg _)).mp hs)

/-- Every point of `S²` with nonnegative last coordinate `c x₂` lies on the hemisphere of sign
`c`, over the point `x₀ + i x₁` of the disc. -/
private theorem exists_cap_eq {c : ℝ} (hc : c ^ 2 = 1) (x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hx : 0 ≤ c * (x : EuclideanSpace ℝ (Fin 3)) 2) : ∃ u, cap hc u = x := by
  have hx2 : (x : EuclideanSpace ℝ (Fin 3)) 0 ^ 2 + (x : EuclideanSpace ℝ (Fin 3)) 1 ^ 2 +
      (x : EuclideanSpace ℝ (Fin 3)) 2 ^ 2 = 1 := by
    rw [← Fin.sum_univ_three (fun i ↦ (x : EuclideanSpace ℝ (Fin 3)) i ^ 2),
      ← EuclideanSpace.real_norm_sq_eq, norm_eq_of_mem_sphere x, one_pow]
  have hnorm : ‖(⟨(x : EuclideanSpace ℝ (Fin 3)) 0, (x : EuclideanSpace ℝ (Fin 3)) 1⟩ : ℂ)‖ ^ 2 =
      1 - (x : EuclideanSpace ℝ (Fin 3)) 2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mk]
    linarith
  have hu : ‖(⟨(x : EuclideanSpace ℝ (Fin 3)) 0, (x : EuclideanSpace ℝ (Fin 3)) 1⟩ : ℂ)‖ ≤ 1 :=
    (sq_le_one_iff₀ (norm_nonneg _)).mp (by rw [hnorm]; nlinarith)
  refine ⟨⟨_, mem_closedBall_zero_iff.mpr hu⟩, Subtype.ext ?_⟩
  ext i
  fin_cases i
  · simp [cap, capPoint]
  · simp [cap, capPoint]
  · simp only [cap, capPoint, Fin.reduceFinMk, PiLp.toLp_apply, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    rw [hnorm, sub_sub_cancel, Real.sqrt_sq_eq_abs]
    rcases mul_self_eq_one_iff.mp ((sq c).symm.trans hc) with rfl | rfl
    · rw [one_mul, abs_of_nonneg (by linarith)]
    · rw [neg_one_mul, abs_of_nonpos (by linarith), neg_neg]

/-- The solid torus `D² × S¹` carried onto the solid torus `S¹ × D²₊` or `S¹ × D²₋` of `S¹ × S²`,
according to the sign `c`. -/
private def capProd {c : ℝ} (hc : c ^ 2 = 1) (p : SolidTorus) :
    Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  (p.2, cap hc p.1)

private theorem isClosedEmbedding_capProd {c : ℝ} (hc : c ^ 2 = 1) :
    IsClosedEmbedding (capProd hc) :=
  (continuous_snd.prodMk ((continuous_cap hc).comp continuous_fst)).isClosedEmbedding
    fun _ _ h ↦ Prod.ext (coe_eq_of_cap_eq (hc := hc) (hc' := hc) (congrArg Prod.snd h))
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
    exact Prod.ext rfl (cap_eq_cap_of_norm_eq_one (one_pow 2) (by norm_num) (by simp))
  range_union_range := by
    refine eq_univ_of_forall fun y ↦ ?_
    rcases le_total 0 ((y.2 : EuclideanSpace ℝ (Fin 3)) 2) with hy | hy
    · obtain ⟨u, hu⟩ := exists_cap_eq (c := 1) (one_pow 2) y.2 (by simpa using hy)
      exact Or.inl ⟨unknotExteriorHomeomorph.symm (u, y.1), by simp [capProd, hu]⟩
    · obtain ⟨u, hu⟩ := exists_cap_eq (c := -1) (by norm_num) y.2 (by simpa using hy)
      exact Or.inr ⟨(u, y.1), by simp [capProd, hu]⟩
  range_inter_range_subset := by
    rintro _ ⟨⟨x, rfl⟩, ⟨p, hp⟩⟩
    have hnorm := norm_eq_one_of_cap_eq (congrArg Prod.snd hp).symm
    refine ⟨(⟨p.1, mem_sphere_zero_iff_norm.mpr hnorm⟩, p.2), ?_⟩
    rw [Function.comp_apply, ← hp]
    exact congrArg _ (Prod.ext (Subtype.ext (SolidTorus.coe_boundaryInclusion_fst _))
      (SolidTorus.boundaryInclusion_snd _))
  fillingSlope_gluing := isSolidTorusNeighborhood_unknotSolidTorus.fillingSlope_prodComm

end ZeroSurgery

end TauCeti
