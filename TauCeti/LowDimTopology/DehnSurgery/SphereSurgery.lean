/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Circle
public import TauCeti.LowDimTopology.DehnSurgery.Filling
public import TauCeti.Topology.Surgery.Basic

/-!
# Surgery on a framed knot is a Dehn filling

A solid torus neighbourhood `Φ : D² × S¹ → X` of a knot is a framed circle: read as
`(x, y) ↦ Φ (y, x)` on `S¹ × D²` (`TauCeti.solidTorusFramedSphere`), it is a framed sphere in the
sense of `TauCeti.SphereSurgery`, with `k = 1` and `q = 2`. Its exterior is the knot exterior
(`TauCeti.sphereExterior_solidTorusFramedSphere`). Surgery along it glues in `D² × S¹` by
`(x, y) ↦ Φ (y, x)` on the boundary torus, which sends the meridian `∂D² × {y}` of the glued-in
solid torus to the longitude `x ↦ Φ (y, x)` of `Φ`. So a surgery along this framed
circle is a Dehn filling of the knot exterior along the longitude of `Φ`, glued by the exchange
of the two circle factors (`TauCeti.SphereSurgery.toDehnFilling`). This is how general-dimension
surgery specializes to integral Dehn surgery on a framed knot in a `3`-manifold.

## Main definitions

* `TauCeti.solidTorusFramedSphere Φ`: the framed circle `S¹ × D² → X` of a solid torus
  neighbourhood.
* `TauCeti.SphereSurgery.toDehnFilling`: a surgery along it, as a Dehn filling along the longitude
  of `Φ`.

## Main results

* `TauCeti.sphereExterior_solidTorusFramedSphere`: the exterior of the framed circle is the knot
  exterior.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9, Sections 9F and 9G (integral
  surgery along a framed knot is the Dehn filling along the framing curve).
-/

public section

noncomputable section

open Set Topology Metric

namespace TauCeti

section FramedSphere

variable {X : Type*}

/-- The framed circle `S¹ × D² → X` of a solid torus neighbourhood `Φ : D² × S¹ → X`:
`(x, y) ↦ Φ (y, x)`. -/
def solidTorusFramedSphere (Φ : SolidTorus → X)
    (p : sphere (0 : ℂ) 1 × closedBall (0 : ℂ) 1) : X :=
  Φ (p.2, Circle.homeomorphSphere.symm p.1)

/-- The framed circle of `Φ` is `(x, y) ↦ Φ (y, x)`. -/
@[simp]
theorem solidTorusFramedSphere_apply (Φ : SolidTorus → X)
    (p : sphere (0 : ℂ) 1 × closedBall (0 : ℂ) 1) :
    solidTorusFramedSphere Φ p = Φ (p.2, Circle.homeomorphSphere.symm p.1) :=
  (rfl)

variable {Φ : SolidTorus → X}

/-- The framed circle of an injective map of the solid torus is injective. -/
theorem solidTorusFramedSphere_injective (hΦ : Function.Injective Φ) :
    Function.Injective (solidTorusFramedSphere Φ) := fun p p' hp ↦ by
  have h' := hΦ hp
  exact Prod.ext (Circle.homeomorphSphere.symm.injective (congrArg Prod.snd h'))
    (congrArg Prod.fst h')

/-- The exterior of the framed circle of a map of the solid torus is its knot exterior. -/
theorem sphereExterior_solidTorusFramedSphere :
    sphereExterior (solidTorusFramedSphere Φ) = knotExterior (Φ := Φ) := by
  refine Set.ext fun x ↦ ?_
  rw [mem_sphereExterior, mem_knotExterior, not_iff_not]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p.2, Circle.homeomorphSphere.symm p.1), hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(Circle.homeomorphSphere p.2, p.1), hp, by simp⟩

end FramedSphere

/-- On the boundary torus, the identification of the solid torus with `D² × S¹ ⊆ ℂ × ℂ` is the
boundary inclusion of `D² × S¹`. -/
theorem SolidTorus.homeomorphBallSphere_boundaryInclusion (q : Circle × Circle) :
    SolidTorus.homeomorphBallSphere (SolidTorus.boundaryInclusion q) =
      ballSphereBoundaryInclusion (Circle.homeomorphSphere q.1, Circle.homeomorphSphere q.2) :=
  Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))

namespace SphereSurgery

variable {X : Type} [TopologicalSpace X] [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}
  {Y : Type*} [TopologicalSpace Y]

/-- **Surgery on a framed knot is a Dehn filling.** A surgery along the framed circle of a solid
torus neighbourhood `Φ` is a Dehn filling of the knot exterior along the longitude of `Φ`: the
glued-in `D² × S¹` is the filling solid torus, glued by the exchange of the two circle factors,
which carries its meridian to the longitude of `Φ`. -/
def toDehnFilling (h : IsSolidTorusNeighborhood f Φ)
    (S : SphereSurgery (solidTorusFramedSphere_injective h.isEmbedding.injective) Y) :
    DehnFilling h h.framedBoundaryTorus.longitude Y where
  exteriorEmbedding :=
    S.exteriorEmbedding ∘ Homeomorph.setCongr sphereExterior_solidTorusFramedSphere.symm
  isClosedEmbedding_exteriorEmbedding := S.isClosedEmbedding_exteriorEmbedding.comp
    (Homeomorph.setCongr sphereExterior_solidTorusFramedSphere.symm).isClosedEmbedding
  solidTorusEmbedding := S.ballSphereEmbedding ∘ SolidTorus.homeomorphBallSphere
  isClosedEmbedding_solidTorusEmbedding :=
    S.isClosedEmbedding_ballSphereEmbedding.comp SolidTorus.homeomorphBallSphere.isClosedEmbedding
  gluing := Homeomorph.prodComm Circle Circle
  exteriorEmbedding_exteriorBoundaryInclusion q := by
    -- The boundary point `Φ (q.2, q.1)` of the knot exterior is the boundary point
    -- `φ (q.1, q.2)` of the exterior of the framed circle; `Homeomorph.setCongr` does not move
    -- points, so the underlying points are compared directly.
    have hx : Homeomorph.setCongr sphereExterior_solidTorusFramedSphere.symm
        (h.exteriorBoundaryInclusion (Homeomorph.prodComm Circle Circle q)) =
          sphereExteriorBoundaryInclusion (solidTorusFramedSphere_injective h.isEmbedding.injective)
            (Circle.homeomorphSphere q.1, Circle.homeomorphSphere q.2) :=
      Subtype.ext <| (h.coe_exteriorBoundaryInclusion_apply _).trans <| by
        rw [coe_sphereExteriorBoundaryInclusion_apply, solidTorusFramedSphere_apply]
        exact congrArg Φ (Prod.ext (Subtype.ext (by simp)) (by simp))
    rw [Function.comp_apply, hx, S.exteriorEmbedding_sphereExteriorBoundaryInclusion,
      Function.comp_apply, SolidTorus.homeomorphBallSphere_boundaryInclusion]
  range_union_range := by
    rw [range_comp, range_comp, Homeomorph.range_coe, Homeomorph.range_coe, image_univ, image_univ,
      S.range_union_range]
  range_inter_range_subset := by
    rw [range_comp, range_comp, Homeomorph.range_coe, Homeomorph.range_coe, image_univ, image_univ]
    refine S.range_inter_range_subset.trans ?_
    rintro _ ⟨q, rfl⟩
    refine ⟨(Circle.homeomorphSphere.symm q.1, Circle.homeomorphSphere.symm q.2), ?_⟩
    simp only [Function.comp_apply, SolidTorus.homeomorphBallSphere_boundaryInclusion,
      Homeomorph.apply_symm_apply]
  fillingSlope_gluing := h.fillingSlope_prodComm

/-- The Dehn filling of a surgery embeds the knot exterior as the exterior of the framed
circle. -/
@[simp]
theorem toDehnFilling_exteriorEmbedding_apply (h : IsSolidTorusNeighborhood f Φ)
    (S : SphereSurgery (solidTorusFramedSphere_injective h.isEmbedding.injective) Y)
    (x : knotExterior (Φ := Φ)) :
    (S.toDehnFilling h).exteriorEmbedding x =
      S.exteriorEmbedding ⟨x, sphereExterior_solidTorusFramedSphere.symm ▸ x.2⟩ :=
  (rfl)

/-- The filling solid torus of the Dehn filling of a surgery is its glued-in `D² × S¹`. -/
@[simp]
theorem toDehnFilling_solidTorusEmbedding_apply (h : IsSolidTorusNeighborhood f Φ)
    (S : SphereSurgery (solidTorusFramedSphere_injective h.isEmbedding.injective) Y)
    (p : SolidTorus) :
    (S.toDehnFilling h).solidTorusEmbedding p =
      S.ballSphereEmbedding (p.1, Circle.homeomorphSphere p.2) := by
  simp only [toDehnFilling, Function.comp_apply, SolidTorus.homeomorphBallSphere_apply]

/-- The Dehn filling of a surgery glues the boundary tori by exchanging the circle factors. -/
@[simp]
theorem toDehnFilling_gluing (h : IsSolidTorusNeighborhood f Φ)
    (S : SphereSurgery (solidTorusFramedSphere_injective h.isEmbedding.injective) Y) :
    (S.toDehnFilling h).gluing = Homeomorph.prodComm Circle Circle :=
  (rfl)

end SphereSurgery

end TauCeti
