/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Analysis.Complex.EuclideanFour
public import TauCeti.Analysis.Normed.Lp.ProdLp.Sphere
public import TauCeti.Geometry.Sphere.LinearIsometry
public import TauCeti.KnotTheory.SmoothCircle
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Exterior

/-!
# The exterior of the unknot is a solid torus

Write `ℝ⁴ = ℂ²` through `(z, w) ↦ (Re z, Im z, Re w, Im w)`
(`TauCeti.complexProdToEuclideanFour`). The unknot `TauCeti.unknot` is the great circle
`ζ ↦ (ζ, 0)` of the unit sphere `S³`. It has the explicit solid torus neighbourhood
`(w, ζ) ↦ (ζ, w) / √(1 + ‖w‖ ^ 2)` (`TauCeti.unknotSolidTorus`), whose image is the solid torus
`‖w‖ ≤ ‖z‖` of the genus-one Heegaard splitting of `S³`. Its knot exterior is the complementary
solid torus `‖z‖ ≤ ‖w‖` (`TauCeti.knotExterior_unknotSolidTorus`), which is homeomorphic to
`D² × S¹` through `(z, w) ↦ (z / ‖w‖, w / ‖w‖)` (`TauCeti.unknotExteriorHomeomorph`).

On the common boundary torus this homeomorphism exchanges the two circle factors
(`TauCeti.unknotExteriorHomeomorph_symm_boundaryInclusion`): the point `(a, b)` of the boundary
torus of the exterior is the point `(b, a)` of the boundary torus of the neighbourhood. So the
meridian `a ↦ (a, 1)` of the exterior solid torus is the longitude `a ↦ (1, a)` of the unknot,
and the longitude of the exterior solid torus is the meridian of the unknot. The preferred
(`0`-) framing of a knot is the one whose longitude is null-homologous in the knot exterior. For
the unknot more is true: the longitude of `TauCeti.unknotSolidTorus` bounds a meridian disc of
the exterior, so in particular it is null-homologous there and is the preferred longitude.

This is the geometric input to the surgery descriptions of the unknot: Dehn filling the exterior
of the unknot along a slope glues a second solid torus to this one along their boundary tori,
which gives `S³` for the slope `∞`, `S¹ × S²` for the slope `0`, and lens spaces for the other
slopes.

## Main definitions

* `TauCeti.unknotSolidTorus`: the standard solid torus neighbourhood of the unknot.
* `TauCeti.unknotExteriorHomeomorph`: the exterior of the unknot is a solid torus.

## Main results

* `TauCeti.isSolidTorusNeighborhood_unknotSolidTorus`: `TauCeti.unknotSolidTorus` is a solid
  torus neighbourhood of `TauCeti.unknot`.
* `TauCeti.knotExterior_unknotSolidTorus`: the exterior of the unknot is the solid torus
  `x₀² + x₁² ≤ x₂² + x₃²`.
* `TauCeti.unknotExteriorHomeomorph_symm_boundaryInclusion`: on the boundary torus, the
  identification of the exterior with a solid torus exchanges meridian and longitude.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Section 2E (solid tori, meridians and
  longitudes) and Chapter 9 (the decomposition of `S³` into two solid tori, and surgery on the
  unknot).
-/

public section

noncomputable section

open Metric Set Topology

namespace TauCeti

/-! ### The standard solid torus neighbourhood of the unknot -/

/-- The standard solid torus neighbourhood of the unknot: `(w, ζ) ↦ (ζ, w) / √(1 + ‖w‖ ^ 2)` in
the coordinates `ℝ⁴ = ℂ²` of `TauCeti.complexProdToEuclideanFour`. Its image is the solid torus
`‖w‖ ≤ ‖z‖`, its meridian discs are `w ↦ (ζ, w) / √(1 + ‖w‖ ^ 2)` and its longitude is
`ζ ↦ (ζ, 1) / √2`. -/
def unknotSolidTorus (p : SolidTorus) : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  LinearIsometryEquiv.unitSphereIsometryEquiv complexProdToEuclideanFour
    ((sphereProdSndLeHomeomorph ℂ ℂ).symm (Circle.homeomorphSphere p.2, p.1))

@[simp]
theorem coe_unknotSolidTorus_apply (p : SolidTorus) :
    (unknotSolidTorus p : EuclideanSpace ℝ (Fin 4)) =
      complexProdToEuclideanFour (WithLp.toLp 2
        ((√(1 + ‖(p.1 : ℂ)‖ ^ 2))⁻¹ • (p.2 : ℂ), (√(1 + ‖(p.1 : ℂ)‖ ^ 2))⁻¹ • (p.1 : ℂ))) := by
  simp [unknotSolidTorus]

/-- The coordinates in `ℂ²` of a point of the unit sphere of `ℝ⁴`, as a point of the unit sphere
of `ℂ²`. -/
private abbrev toComplexProd : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ≃ₜ
    sphere (0 : WithLp 2 (ℂ × ℂ)) 1 :=
  (LinearIsometryEquiv.unitSphereIsometryEquiv complexProdToEuclideanFour.symm).toHomeomorph

/-- The solid torus `D² × S¹` is `S¹ × D²` with its factors exchanged. -/
private abbrev solidTorusSwap : SolidTorus ≃ₜ sphere (0 : ℂ) 1 × closedBall (0 : ℂ) 1 :=
  (Homeomorph.prodComm _ _).trans (Circle.homeomorphSphere.prodCongr (Homeomorph.refl _))

private theorem toComplexProd_unknotSolidTorus (p : SolidTorus) :
    toComplexProd (unknotSolidTorus p) =
      ((sphereProdSndLeHomeomorph ℂ ℂ).symm (solidTorusSwap p)).1 := by
  ext1
  -- Keep `complexProdToEuclideanFour` folded so that it cancels against its inverse.
  simp [unknotSolidTorus, toComplexProd, -complexProdToEuclideanFour_apply]

/-- The image of the open solid torus under `TauCeti.unknotSolidTorus` is the open solid torus
`‖w‖ < ‖z‖`. -/
private theorem image_unknotSolidTorus :
    unknotSolidTorus '' {p | ‖(p.1 : ℂ)‖ < 1} =
      {x | ‖(toComplexProd x : WithLp 2 (ℂ × ℂ)).snd‖ <
        ‖(toComplexProd x : WithLp 2 (ℂ × ℂ)).fst‖} := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hc : 0 < (√(1 + ‖(p.1 : ℂ)‖ ^ 2))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by positivity))
    simp only [mem_ofPred_eq] at hp
    simp only [mem_ofPred_eq, toComplexProd_unknotSolidTorus,
      coe_sphereProdSndLeHomeomorph_symm_apply, WithLp.toLp_fst, WithLp.toLp_snd, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa using mul_lt_mul_of_pos_left hp hc
  · intro hx
    have hle : toComplexProd x ∈ {y : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 |
        ‖(y : WithLp 2 (ℂ × ℂ)).snd‖ ≤ ‖(y : WithLp 2 (ℂ × ℂ)).fst‖} := by
      simp only [mem_ofPred_eq]
      exact le_of_lt hx
    refine ⟨solidTorusSwap.symm (sphereProdSndLeHomeomorph ℂ ℂ ⟨_, hle⟩), ?_, ?_⟩
    · have hfst : 0 < ‖(toComplexProd x : WithLp 2 (ℂ × ℂ)).fst‖ :=
        (norm_nonneg _).trans_lt hx
      simp only [mem_ofPred_eq]
      simpa [norm_smul] using (inv_mul_lt_one₀ hfst).2 hx
    · apply toComplexProd.injective
      rw [toComplexProd_unknotSolidTorus, Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]

/-- `TauCeti.unknotSolidTorus` is a solid torus neighbourhood of `TauCeti.unknot`. -/
theorem isSolidTorusNeighborhood_unknotSolidTorus :
    IsSolidTorusNeighborhood unknot unknotSolidTorus where
  isEmbedding := by
    rw [← toComplexProd.isEmbedding.of_comp_iff]
    have h : toComplexProd ∘ unknotSolidTorus =
        Subtype.val ∘ (sphereProdSndLeHomeomorph ℂ ℂ).symm ∘ solidTorusSwap :=
      funext toComplexProd_unknotSolidTorus
    rw [h]
    exact IsEmbedding.subtypeVal.comp
      ((sphereProdSndLeHomeomorph ℂ ℂ).symm.isEmbedding.comp solidTorusSwap.isEmbedding)
  apply_zero z := by
    ext1
    rw [coe_unknot_apply, ← complexToEuclideanFour_apply, ← complexProdToEuclideanFour_toLp_zero]
    simp
  isOpen_image := by
    rw [image_unknotSolidTorus]
    exact isOpen_lt (by fun_prop) (by fun_prop)

/-! ### The exterior of the unknot -/

private theorem mem_knotExterior_unknotSolidTorus_iff
    {x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1} :
    x ∈ knotExterior (Φ := unknotSolidTorus) ↔
      ‖(toComplexProd x : WithLp 2 (ℂ × ℂ)).fst‖ ≤
        ‖(toComplexProd x : WithLp 2 (ℂ × ℂ)).snd‖ := by
  rw [mem_knotExterior, image_unknotSolidTorus, mem_ofPred_eq, not_lt]

/-- **The exterior of the unknot** for its standard solid torus neighbourhood is the solid torus
`x₀² + x₁² ≤ x₂² + x₃²` of the unit sphere of `ℝ⁴`. -/
theorem knotExterior_unknotSolidTorus :
    knotExterior (Φ := unknotSolidTorus) =
      {x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 |
        (x : EuclideanSpace ℝ (Fin 4)) 0 ^ 2 + (x : EuclideanSpace ℝ (Fin 4)) 1 ^ 2 ≤
          (x : EuclideanSpace ℝ (Fin 4)) 2 ^ 2 + (x : EuclideanSpace ℝ (Fin 4)) 3 ^ 2} := by
  ext x
  rw [mem_knotExterior_unknotSolidTorus_iff, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [Complex.norm_mul_self_eq_normSq, sq]

/-- **The exterior of the unknot is a solid torus.** The exterior of the standard solid torus
neighbourhood of the unknot, the solid torus `‖z‖ ≤ ‖w‖` in the coordinates `ℝ⁴ = ℂ²`, is
homeomorphic to `D² × S¹` through `(z, w) ↦ (z / ‖w‖, w / ‖w‖)`. -/
def unknotExteriorHomeomorph : knotExterior (Φ := unknotSolidTorus) ≃ₜ SolidTorus :=
  ((toComplexProd.subtype fun _ ↦ mem_knotExterior_unknotSolidTorus_iff).trans
    (sphereProdFstLeHomeomorph ℂ ℂ)).trans
    ((Homeomorph.refl _).prodCongr Circle.homeomorphSphere.symm)

/- In the next three proofs `mem_ofPred_eq` is excluded: it rewrites the set-builder subtype of
`TauCeti.sphereProdFstLeHomeomorph`, after which its coordinate simp lemmas no longer match. -/

@[simp]
theorem coe_unknotExteriorHomeomorph_apply_fst (x : knotExterior (Φ := unknotSolidTorus)) :
    ((unknotExteriorHomeomorph x).1 : ℂ) =
      ‖(complexProdToEuclideanFour.symm (x : EuclideanSpace ℝ (Fin 4))).snd‖⁻¹ •
        (complexProdToEuclideanFour.symm (x : EuclideanSpace ℝ (Fin 4))).fst := by
  simp [unknotExteriorHomeomorph, -mem_ofPred_eq]

@[simp]
theorem coe_unknotExteriorHomeomorph_apply_snd (x : knotExterior (Φ := unknotSolidTorus)) :
    ((unknotExteriorHomeomorph x).2 : ℂ) =
      ‖(complexProdToEuclideanFour.symm (x : EuclideanSpace ℝ (Fin 4))).snd‖⁻¹ •
        (complexProdToEuclideanFour.symm (x : EuclideanSpace ℝ (Fin 4))).snd := by
  simp [unknotExteriorHomeomorph, -mem_ofPred_eq]

@[simp]
theorem coe_unknotExteriorHomeomorph_symm_apply (p : SolidTorus) :
    ((unknotExteriorHomeomorph.symm p : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
        EuclideanSpace ℝ (Fin 4)) =
      complexProdToEuclideanFour (WithLp.toLp 2
        ((√(1 + ‖(p.1 : ℂ)‖ ^ 2))⁻¹ • (p.1 : ℂ), (√(1 + ‖(p.1 : ℂ)‖ ^ 2))⁻¹ • (p.2 : ℂ))) := by
  simp [unknotExteriorHomeomorph, -mem_ofPred_eq]

/-- **The exterior of the unknot exchanges meridian and longitude.** On the boundary torus, the
identification `TauCeti.unknotExteriorHomeomorph` of the exterior of the unknot with `D² × S¹`
exchanges the two circle factors: the point `(a, b)` of the boundary torus of the exterior is
the point `(b, a)` of the boundary torus of `TauCeti.unknotSolidTorus`. So the boundary
`a ↦ (a, 1)` of the meridian disc `w ↦ (w, 1)` of the exterior is the longitude `a ↦ (1, a)` of
the unknot, and the longitude `b ↦ (1, b)` of the exterior is the meridian `b ↦ (b, 1)` of the
unknot. -/
theorem unknotExteriorHomeomorph_symm_boundaryInclusion (q : Circle × Circle) :
    (unknotExteriorHomeomorph.symm (SolidTorus.boundaryInclusion q) :
        sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) =
      unknotSolidTorus (SolidTorus.boundaryInclusion q.swap) := by
  ext1
  simp

end TauCeti
