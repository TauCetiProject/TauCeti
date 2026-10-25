/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.DehnSurgery.Framing
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Exterior

/-!
# Dehn fillings of knot exteriors

Let `Φ : D² × S¹ → X` be a solid torus neighbourhood of a knot `f` in a Hausdorff space `X`, with
knot exterior `E` (`TauCeti.knotExterior`) and boundary torus `∂E`, parametrized through `Φ` by
`S¹ × S¹`. A *Dehn filling* of `E` glues a solid torus `V = D² × S¹` to `E` along a homeomorphism
of the boundary tori. Up to homeomorphism the result depends only on the *slope* of the gluing,
the class in `H₁(∂E; ℤ)` modulo sign of the image of the meridian `∂D² × {1}` of `V`
(Rolfsen, *Knots and Links*, Chapter 9); this slope is the datum of the filling.

Here a filling is recorded inside the filled space, without a gluing construction, in the same way
as `TauCeti.HeegaardSplitting`: a `TauCeti.DehnFilling h s Y` consists of closed embeddings of `E`
and of `V` into `Y` whose images cover `Y` and meet only along the boundary torus of `V`, which is
glued to `∂E` by a homeomorphism `g` of `S¹ × S¹` read in the two framings, and whose filling slope
(`TauCeti.IsSolidTorusNeighborhood.fillingSlope`) is `s`. The two pieces being closed, `Y` is then
homeomorphic to the space obtained from `E` and `V` by gluing along `g`. That the homeomorphism
type of such a `Y` depends only on `s` is the classical well-definedness of Dehn filling, through
the mapping class group of the torus; it is not formalized here.

The slope of the gluing is computed from where `g` sends the meridian curve
(`TauCeti.IsSolidTorusNeighborhood.fillingSlope_eq_of_apply_torusCurve`): the identity gives the
meridian of `Φ` and the exchange of the two circle factors gives its longitude. Every knot
exterior has the *trivial filling* along the meridian, the ambient space itself with `V` the solid
torus neighbourhood (`TauCeti.IsSolidTorusNeighborhood.meridianDehnFilling`); since the framing
of `Φ` and the preferred framing share the meridian, this is the `∞`-surgery on the knot.

## Main definitions

* `TauCeti.IsSolidTorusNeighborhood.fillingSlope`: the slope on `∂E` of the meridian of a solid
  torus glued along a homeomorphism `g` of `S¹ × S¹`.
* `TauCeti.DehnFilling h s Y`: a Dehn filling of the exterior along the slope `s`, inside `Y`.
* `TauCeti.DehnFilling.transHomeomorph`: transport of a filling along a homeomorphism.
* `TauCeti.IsSolidTorusNeighborhood.meridianDehnFilling`: the trivial filling along the meridian.

## Main results

* `TauCeti.IsSolidTorusNeighborhood.fillingSlope_refl`,
  `TauCeti.IsSolidTorusNeighborhood.fillingSlope_prodComm`: gluing by the identity has the
  meridian as slope, and gluing by the exchange of factors has the longitude.
* `TauCeti.DehnFilling.ext`: a filling is determined by its two embeddings.
* `TauCeti.DehnFilling.range_inter_range`: the two pieces meet exactly in the boundary torus of
  the filling solid torus.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9, Section 9F (Dehn surgery
  along a solid torus: the filled manifold depends only on the curve to which the meridian of the
  filling solid torus is sent).
-/

public section

noncomputable section

open Set Topology

namespace TauCeti

namespace IsSolidTorusNeighborhood

variable {X : Type} [TopologicalSpace X] [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}

/-- The **filling slope** of a gluing `g` of a solid torus `V = D² × S¹` to the knot exterior, the
point `q` of the boundary torus of `V` being glued to the point `g q` of the boundary torus of the
exterior, both parametrized by `S¹ × S¹`: the slope on the boundary torus of the exterior of the
image `t ↦ Φ (g (exp (2πit), 1))` of the meridian of `V`. -/
def fillingSlope (h : IsSolidTorusNeighborhood f Φ) (g : Circle × Circle ≃ₜ Circle × Circle) :
    Slope h.framedBoundaryTorus.H :=
  Slope.mk (FramedBoundaryTorus.torusCurveClass (g.trans h.exteriorFrontierHomeomorph) 1 0)
    ((FramedBoundaryTorus.isPrimitive_torusCurveClass_iff _ 1 0).2 isCoprime_one_left)

/-- **The filling slope from the image of the meridian.** If the gluing `g` carries the meridian
curve `t ↦ (exp (2πit), 1)` of the filling solid torus to the `(p, q)` curve of `S¹ × S¹`, then
the filling slope is the slope of the `(p, q)` curve on the boundary torus of the exterior, of
value `p / q` in the framing of `Φ`
(`TauCeti.FramedBoundaryTorus.value_mk_torusCurveClass`). -/
theorem fillingSlope_eq_of_apply_torusCurve (h : IsSolidTorusNeighborhood f Φ)
    {g : Circle × Circle ≃ₜ Circle × Circle} {p q : ℤ} (hpq : IsCoprime p q)
    (hg : ∀ t, g (torusCurve 1 0 t) = torusCurve p q t) :
    h.fillingSlope g =
      Slope.mk (FramedBoundaryTorus.torusCurveClass h.exteriorFrontierHomeomorph p q)
        ((FramedBoundaryTorus.isPrimitive_torusCurveClass_iff _ p q).2 hpq) := by
  refine Slope.mk_eq_mk _ _ (Or.inl ?_)
  rw [FramedBoundaryTorus.torusCurveClass_def, FramedBoundaryTorus.torusCurveClass_def]
  exact congrArg _ (HurewiczOne.loopClass_eq_of_apply_eq _ _ fun t ↦
    congrArg h.exteriorFrontierHomeomorph (hg t))

/-- Gluing by the identity has the meridian of `Φ` as filling slope. -/
@[simp]
theorem fillingSlope_refl (h : IsSolidTorusNeighborhood f Φ) :
    h.fillingSlope (Homeomorph.refl _) = h.framedBoundaryTorus.meridian := by
  apply h.framedBoundaryTorus.slopeEquiv.injective
  rw [h.fillingSlope_eq_of_apply_torusCurve (p := 1) (q := 0) isCoprime_one_left fun _ ↦ rfl,
    FramedBoundaryTorus.slopeEquiv_apply, FramedBoundaryTorus.slopeEquiv_apply,
    FramedBoundaryTorus.value_mk_torusCurveClass _ isCoprime_one_left,
    FramedBoundaryTorus.value_meridian]
  exact slopeValue_of_snd_eq_zero rfl

/-- Gluing by the exchange of the two circle factors has the longitude of `Φ` as filling
slope. -/
@[simp]
theorem fillingSlope_prodComm (h : IsSolidTorusNeighborhood f Φ) :
    h.fillingSlope (Homeomorph.prodComm Circle Circle) = h.framedBoundaryTorus.longitude := by
  apply h.framedBoundaryTorus.slopeEquiv.injective
  rw [h.fillingSlope_eq_of_apply_torusCurve (p := 0) (q := 1) isCoprime_one_right
      fun _ ↦ by simp,
    FramedBoundaryTorus.slopeEquiv_apply, FramedBoundaryTorus.slopeEquiv_apply,
    FramedBoundaryTorus.value_mk_torusCurveClass _ isCoprime_one_right,
    FramedBoundaryTorus.value_longitude,
    slopeValue_of_snd_ne_zero one_ne_zero]
  norm_num

end IsSolidTorusNeighborhood

variable {X : Type} [TopologicalSpace X] [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}

/-- A **Dehn filling** of the exterior `E` of a knot along the slope `s`, recorded inside the
filled space `Y`: closed embeddings of `E` and of the filling solid torus `V = D² × S¹` into `Y`,
whose images cover `Y` and meet only along the boundary torus of `V`, glued to the boundary torus
of `E` by a homeomorphism `gluing` of `S¹ × S¹` whose filling slope is `s`. The two images being
closed, `Y` is homeomorphic to the space obtained by gluing `V` to `E` along `gluing`. -/
structure DehnFilling (h : IsSolidTorusNeighborhood f Φ) (s : Slope h.framedBoundaryTorus.H)
    (Y : Type*) [TopologicalSpace Y] where
  /-- The embedding of the knot exterior into the filled space. -/
  exteriorEmbedding : knotExterior (Φ := Φ) → Y
  isClosedEmbedding_exteriorEmbedding : IsClosedEmbedding exteriorEmbedding
  /-- The embedding of the filling solid torus into the filled space. -/
  solidTorusEmbedding : SolidTorus → Y
  isClosedEmbedding_solidTorusEmbedding : IsClosedEmbedding solidTorusEmbedding
  /-- The gluing of the two boundary tori, both parametrized by `S¹ × S¹`: the point `q` of the
  boundary torus of the filling solid torus is the point `gluing q` of the boundary torus of the
  exterior. -/
  gluing : Circle × Circle ≃ₜ Circle × Circle
  exteriorEmbedding_exteriorBoundaryInclusion (q : Circle × Circle) :
    exteriorEmbedding (h.exteriorBoundaryInclusion (gluing q)) =
      solidTorusEmbedding (SolidTorus.boundaryInclusion q)
  range_union_range : range exteriorEmbedding ∪ range solidTorusEmbedding = univ
  range_inter_range_subset : range exteriorEmbedding ∩ range solidTorusEmbedding ⊆
    range (solidTorusEmbedding ∘ SolidTorus.boundaryInclusion)
  fillingSlope_gluing : h.fillingSlope gluing = s

namespace DehnFilling

variable {h : IsSolidTorusNeighborhood f Φ} {s : Slope h.framedBoundaryTorus.H}
  {Y : Type*} [TopologicalSpace Y]

/-- A Dehn filling is determined by its two embeddings: the gluing is the identification of the
boundary tori they induce. -/
@[ext]
theorem ext {F G : DehnFilling h s Y} (hext : F.exteriorEmbedding = G.exteriorEmbedding)
    (hsol : F.solidTorusEmbedding = G.solidTorusEmbedding) : F = G := by
  have hglue : F.gluing = G.gluing := by
    ext1 q
    refine h.exteriorBoundaryInclusion_injective
      (F.isClosedEmbedding_exteriorEmbedding.injective ?_)
    rw [F.exteriorEmbedding_exteriorBoundaryInclusion, hext,
      G.exteriorEmbedding_exteriorBoundaryInclusion, hsol]
  cases F
  cases G
  cases hext
  cases hsol
  cases hglue
  rfl

/-- **The two pieces of a Dehn filling meet in the boundary torus** of the filling solid torus,
which is the image of the boundary torus of the exterior. -/
theorem range_inter_range (F : DehnFilling h s Y) :
    range F.exteriorEmbedding ∩ range F.solidTorusEmbedding =
      range (F.solidTorusEmbedding ∘ SolidTorus.boundaryInclusion) := by
  refine F.range_inter_range_subset.antisymm ?_
  rintro _ ⟨q, rfl⟩
  exact ⟨⟨_, F.exteriorEmbedding_exteriorBoundaryInclusion q⟩, mem_range_self _⟩

/-- A point of the exterior is sent into the filling solid torus only on the boundary torus. -/
theorem exteriorEmbedding_eq_solidTorusEmbedding_iff {F : DehnFilling h s Y}
    {x : knotExterior (Φ := Φ)} {p : SolidTorus} :
    F.exteriorEmbedding x = F.solidTorusEmbedding p ↔
      ∃ q, p = SolidTorus.boundaryInclusion q ∧ x = h.exteriorBoundaryInclusion (F.gluing q) := by
  constructor
  · intro hxp
    obtain ⟨q, hq⟩ := F.range_inter_range_subset ⟨⟨x, hxp⟩, ⟨p, rfl⟩⟩
    have hp := F.isClosedEmbedding_solidTorusEmbedding.injective hq
    refine ⟨q, hp.symm, F.isClosedEmbedding_exteriorEmbedding.injective ?_⟩
    rw [hxp, F.exteriorEmbedding_exteriorBoundaryInclusion, ← hp]
  · rintro ⟨q, rfl, rfl⟩
    exact F.exteriorEmbedding_exteriorBoundaryInclusion q

/-- A Dehn filling is carried along a homeomorphism of the filled space. -/
def transHomeomorph (F : DehnFilling h s Y) {Y' : Type*} [TopologicalSpace Y'] (e : Y ≃ₜ Y') :
    DehnFilling h s Y' where
  exteriorEmbedding := e ∘ F.exteriorEmbedding
  isClosedEmbedding_exteriorEmbedding :=
    e.isClosedEmbedding.comp F.isClosedEmbedding_exteriorEmbedding
  solidTorusEmbedding := e ∘ F.solidTorusEmbedding
  isClosedEmbedding_solidTorusEmbedding :=
    e.isClosedEmbedding.comp F.isClosedEmbedding_solidTorusEmbedding
  gluing := F.gluing
  exteriorEmbedding_exteriorBoundaryInclusion q :=
    congrArg e (F.exteriorEmbedding_exteriorBoundaryInclusion q)
  range_union_range := by
    rw [range_comp, range_comp, ← image_union, F.range_union_range, image_univ, e.range_coe]
  range_inter_range_subset := by
    rw [range_comp, range_comp, ← image_inter e.injective, Function.comp_assoc, range_comp]
    exact image_mono F.range_inter_range_subset
  fillingSlope_gluing := F.fillingSlope_gluing

/-- The exterior embedding of a transported filling is the composite with the homeomorphism. -/
@[simp]
theorem transHomeomorph_exteriorEmbedding (F : DehnFilling h s Y) {Y' : Type*}
    [TopologicalSpace Y'] (e : Y ≃ₜ Y') :
    (F.transHomeomorph e).exteriorEmbedding = e ∘ F.exteriorEmbedding :=
  (rfl)

/-- The solid torus embedding of a transported filling is the composite with the
homeomorphism. -/
@[simp]
theorem transHomeomorph_solidTorusEmbedding (F : DehnFilling h s Y) {Y' : Type*}
    [TopologicalSpace Y'] (e : Y ≃ₜ Y') :
    (F.transHomeomorph e).solidTorusEmbedding = e ∘ F.solidTorusEmbedding :=
  (rfl)

/-- Transport along a homeomorphism of the filled space keeps the gluing. -/
@[simp]
theorem transHomeomorph_gluing (F : DehnFilling h s Y) {Y' : Type*} [TopologicalSpace Y']
    (e : Y ≃ₜ Y') : (F.transHomeomorph e).gluing = F.gluing :=
  (rfl)

end DehnFilling

namespace IsSolidTorusNeighborhood

/-- **The trivial Dehn filling.** Gluing the solid torus neighbourhood `Φ` back into the exterior
by the identity recovers the ambient space: `X` is the Dehn filling of the knot exterior along the
meridian slope of `Φ`, the `∞`-surgery on the knot. -/
def meridianDehnFilling (h : IsSolidTorusNeighborhood f Φ) :
    DehnFilling h h.framedBoundaryTorus.meridian X where
  exteriorEmbedding := Subtype.val
  isClosedEmbedding_exteriorEmbedding := h.isClosed_exterior.isClosedEmbedding_subtypeVal
  solidTorusEmbedding := Φ
  isClosedEmbedding_solidTorusEmbedding := h.isClosedEmbedding
  gluing := Homeomorph.refl _
  exteriorEmbedding_exteriorBoundaryInclusion q := h.coe_exteriorBoundaryInclusion_apply q
  range_union_range := by
    rw [Subtype.range_coe, eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ knotExterior (Φ := Φ)
    · exact Or.inl hx
    · rw [mem_knotExterior, not_not] at hx
      exact Or.inr (image_subset_range _ _ hx)
  range_inter_range_subset := by
    rintro _ ⟨hx, p, rfl⟩
    rw [Subtype.range_coe, mem_knotExterior] at hx
    have hp : ‖(p.1 : ℂ)‖ = 1 :=
      le_antisymm (mem_closedBall_zero_iff.mp p.1.2) (not_lt.mp fun hp ↦ hx ⟨p, hp, rfl⟩)
    rw [range_comp, SolidTorus.range_boundaryInclusion]
    exact mem_image_of_mem _ hp
  fillingSlope_gluing := h.fillingSlope_refl

/-- The trivial filling embeds the exterior by its inclusion. -/
@[simp]
theorem meridianDehnFilling_exteriorEmbedding (h : IsSolidTorusNeighborhood f Φ) :
    h.meridianDehnFilling.exteriorEmbedding = Subtype.val :=
  (rfl)

/-- The filling solid torus of the trivial filling is the solid torus neighbourhood. -/
@[simp]
theorem meridianDehnFilling_solidTorusEmbedding (h : IsSolidTorusNeighborhood f Φ) :
    h.meridianDehnFilling.solidTorusEmbedding = Φ :=
  (rfl)

/-- The trivial filling glues the boundary tori by the identity. -/
@[simp]
theorem meridianDehnFilling_gluing (h : IsSolidTorusNeighborhood f Φ) :
    h.meridianDehnFilling.gluing = Homeomorph.refl _ :=
  (rfl)

end IsSolidTorusNeighborhood

end TauCeti
