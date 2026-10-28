/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.DehnSurgery.Filling
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Link.Exterior
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Dehn fillings of link exteriors

Let `Φ i : D² × S¹ → X` be pairwise disjoint solid torus neighbourhoods of the components `f i` of
a link in a Hausdorff space `X` (`TauCeti.IsSolidTorusLinkNeighborhood`), with link exterior `E`
(`TauCeti.linkExterior`), whose boundary consists of one torus `Φ i (S¹ × S¹)` for each component.
A *Dehn filling* of `E` glues a solid torus `Vᵢ = D² × S¹` to each boundary torus of `E`. Up to
homeomorphism the result depends only on the family of *slopes* `sᵢ` of the gluings, the classes
in `H₁` of the boundary tori, modulo sign, of the images of the meridians of the `Vᵢ`; this
classical well-definedness is not formalized here. Rational surgery on a link is such a filling,
the slope of the `i`-th component being read in its preferred framing (Rolfsen, *Knots and Links*,
Chapter 9).

As for knots (`TauCeti.DehnFilling`), a filling is recorded inside the filled space `Y`: a
`TauCeti.LinkDehnFilling h s Y` consists of a closed embedding of `E` and closed embeddings of the
solid tori `Vᵢ` into `Y`, with pairwise disjoint images, which cover `Y`, and such that `Vᵢ` meets
`E` only along its boundary torus, glued to the `i`-th boundary torus of `E` by a homeomorphism
`gᵢ` of `S¹ × S¹` of filling slope `sᵢ` (`TauCeti.IsSolidTorusNeighborhood.fillingSlope`). For a
link with finitely many components, `Y` is then the space obtained from `E` and the `Vᵢ` by gluing
along the `gᵢ`: continuous maps on the pieces which agree along the gluings descend uniquely to
`Y` (`TauCeti.LinkDehnFilling.desc`, `TauCeti.LinkDehnFilling.desc_unique`).

Every link exterior has the *trivial filling* along the meridians of all components, the ambient
space itself (`TauCeti.IsSolidTorusLinkNeighborhood.meridianDehnFilling`), and a Dehn filling of
the exterior of a one-component link, in the sense of `TauCeti.DehnFilling`, is a Dehn filling of
its link exterior (`TauCeti.DehnFilling.toLinkDehnFilling`).

## Main definitions

* `TauCeti.LinkDehnFilling h s Y`: a Dehn filling of the link exterior along the slopes `s`,
  inside `Y`.
* `TauCeti.LinkDehnFilling.desc`: for finitely many components, the continuous map on the filled
  space glued from compatible continuous maps on the pieces.
* `TauCeti.LinkDehnFilling.transHomeomorph`: transport of a filling along a homeomorphism.
* `TauCeti.IsSolidTorusLinkNeighborhood.meridianDehnFilling`: the trivial filling along the
  meridians.
* `TauCeti.DehnFilling.toLinkDehnFilling`: a Dehn filling of a knot exterior as a Dehn filling of
  the exterior of the corresponding one-component link.

## Main results

* `TauCeti.LinkDehnFilling.ext`: a filling is determined by its embeddings.
* `TauCeti.LinkDehnFilling.range_inter_range`: each filling solid torus meets the exterior exactly
  in its boundary torus.
* `TauCeti.LinkDehnFilling.solidTorusEmbedding_eq_solidTorusEmbedding_iff`: the filling solid tori
  are embedded with disjoint images.
* `TauCeti.LinkDehnFilling.hom_ext`, `TauCeti.LinkDehnFilling.desc_unique`: a continuous map on the
  filled space is determined by its restrictions to the pieces, so for finitely many components
  the filled space is their gluing.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9, Sections 9F and 9G (Dehn
  surgery on a link: a solid torus is sewn back along each boundary torus of the link exterior,
  and the filled manifold depends only on the curves to which their meridians are sent).
-/

public section

noncomputable section

open Set Topology Function

namespace TauCeti

variable {ι : Type*} {X : Type} [TopologicalSpace X] [T2Space X] {f : ι → Circle → X}
  {Φ : ι → SolidTorus → X}

/-- A **Dehn filling** of the exterior `E` of a link along the slopes `s i`, recorded inside the
filled space `Y`: a closed embedding of `E` and closed embeddings of filling solid tori
`Vᵢ = D² × S¹`, one for each component, into `Y`, whose images cover `Y`, the `Vᵢ` having pairwise
disjoint images, each meeting `E` only along its boundary torus. That boundary torus is glued to
the `i`-th boundary torus of `E` by a homeomorphism `gluing i` of `S¹ × S¹` whose filling slope is
`s i`. For finitely many components, the images being closed, `Y` is homeomorphic to the space
obtained by gluing the `Vᵢ` to `E` along the `gluing i` (`TauCeti.LinkDehnFilling.desc_unique`). -/
structure LinkDehnFilling (h : IsSolidTorusLinkNeighborhood f Φ)
    (s : ∀ i, Slope (h.neighborhood i).framedBoundaryTorus.H) (Y : Type*) [TopologicalSpace Y] where
  /-- The embedding of the link exterior into the filled space. -/
  exteriorEmbedding : linkExterior Φ → Y
  isClosedEmbedding_exteriorEmbedding : IsClosedEmbedding exteriorEmbedding
  /-- The embedding of the filling solid torus of the `i`-th component into the filled space. -/
  solidTorusEmbedding : ι → SolidTorus → Y
  isClosedEmbedding_solidTorusEmbedding (i : ι) : IsClosedEmbedding (solidTorusEmbedding i)
  /-- The gluing of the boundary tori of the `i`-th component, both parametrized by `S¹ × S¹`: the
  point `q` of the boundary torus of the `i`-th filling solid torus is the point `gluing i q` of
  the `i`-th boundary torus of the exterior. -/
  gluing : ι → Circle × Circle ≃ₜ Circle × Circle
  exteriorEmbedding_exteriorBoundaryInclusion (i : ι) (q : Circle × Circle) :
    exteriorEmbedding (h.exteriorBoundaryInclusion i (gluing i q)) =
      solidTorusEmbedding i (SolidTorus.boundaryInclusion q)
  range_union_iUnion_range : range exteriorEmbedding ∪ ⋃ i, range (solidTorusEmbedding i) = univ
  range_inter_range_subset (i : ι) : range exteriorEmbedding ∩ range (solidTorusEmbedding i) ⊆
    range (solidTorusEmbedding i ∘ SolidTorus.boundaryInclusion)
  pairwiseDisjoint_range : Pairwise (Disjoint on fun i ↦ range (solidTorusEmbedding i))
  fillingSlope_gluing (i : ι) : (h.neighborhood i).fillingSlope (gluing i) = s i

namespace LinkDehnFilling

variable {h : IsSolidTorusLinkNeighborhood f Φ}
  {s : ∀ i, Slope (h.neighborhood i).framedBoundaryTorus.H} {Y : Type*} [TopologicalSpace Y]

/-- A Dehn filling of a link exterior is determined by its embeddings: the gluings are the
identifications of the boundary tori they induce. -/
@[ext]
theorem ext {F G : LinkDehnFilling h s Y} (hext : F.exteriorEmbedding = G.exteriorEmbedding)
    (hsol : F.solidTorusEmbedding = G.solidTorusEmbedding) : F = G := by
  have hglue : F.gluing = G.gluing := by
    funext i
    ext1 q
    refine h.exteriorBoundaryInclusion_injective i
      (F.isClosedEmbedding_exteriorEmbedding.injective ?_)
    rw [F.exteriorEmbedding_exteriorBoundaryInclusion, hext,
      G.exteriorEmbedding_exteriorBoundaryInclusion, hsol]
  cases F
  cases G
  cases hext
  cases hsol
  cases hglue
  rfl

/-- **Each filling solid torus meets the exterior in its boundary torus**, which is the image of
the corresponding boundary torus of the exterior. -/
theorem range_inter_range (F : LinkDehnFilling h s Y) (i : ι) :
    range F.exteriorEmbedding ∩ range (F.solidTorusEmbedding i) =
      range (F.solidTorusEmbedding i ∘ SolidTorus.boundaryInclusion) := by
  refine (F.range_inter_range_subset i).antisymm ?_
  rintro _ ⟨q, rfl⟩
  exact ⟨⟨_, F.exteriorEmbedding_exteriorBoundaryInclusion i q⟩, mem_range_self _⟩

/-- A point of the exterior is sent into the `i`-th filling solid torus only on its boundary
torus, through the `i`-th gluing. -/
theorem exteriorEmbedding_eq_solidTorusEmbedding_iff {F : LinkDehnFilling h s Y}
    {x : linkExterior Φ} {i : ι} {p : SolidTorus} :
    F.exteriorEmbedding x = F.solidTorusEmbedding i p ↔
      ∃ q, p = SolidTorus.boundaryInclusion q ∧
        x = h.exteriorBoundaryInclusion i (F.gluing i q) := by
  constructor
  · intro hxp
    obtain ⟨q, hq⟩ := F.range_inter_range_subset i ⟨⟨x, hxp⟩, ⟨p, rfl⟩⟩
    have hp := (F.isClosedEmbedding_solidTorusEmbedding i).injective hq
    refine ⟨q, hp.symm, F.isClosedEmbedding_exteriorEmbedding.injective ?_⟩
    rw [hxp, F.exteriorEmbedding_exteriorBoundaryInclusion, ← hp]
  · rintro ⟨q, rfl, rfl⟩
    exact F.exteriorEmbedding_exteriorBoundaryInclusion i q

/-- **The filling solid tori are embedded with disjoint images**: points of two filling solid tori
coincide in the filled space only if they are the same point of the same solid torus. -/
theorem solidTorusEmbedding_eq_solidTorusEmbedding_iff {F : LinkDehnFilling h s Y} {i j : ι}
    {p p' : SolidTorus} :
    F.solidTorusEmbedding i p = F.solidTorusEmbedding j p' ↔ i = j ∧ p = p' := by
  refine ⟨fun hpp' ↦ ?_, fun ⟨hij, hp⟩ ↦ hij ▸ hp ▸ rfl⟩
  obtain rfl : i = j := by
    by_contra hij
    exact (F.pairwiseDisjoint_range hij).ne_of_mem (mem_range_self p) (mem_range_self p') hpp'
  exact ⟨rfl, (F.isClosedEmbedding_solidTorusEmbedding i).injective hpp'⟩

section desc

variable {Z : Type*}

/-- A point of the filled space outside the exterior lies in one of the filling solid tori. -/
private theorem exists_solidTorusEmbedding_eq_of_notMem (F : LinkDehnFilling h s Y) {y : Y}
    (hy : y ∉ range F.exteriorEmbedding) :
    ∃ x : ι × SolidTorus, F.solidTorusEmbedding x.1 x.2 = y := by
  obtain ⟨i, p, hp⟩ :=
    mem_iUnion.1 ((eq_univ_iff_forall.1 F.range_union_iUnion_range y).resolve_left hy)
  exact ⟨(i, p), hp⟩

open Classical in
/-- The function underlying `TauCeti.LinkDehnFilling.desc`: `a` on the exterior and `b i` on the
rest of the `i`-th filling solid torus. -/
private def descFun (F : LinkDehnFilling h s Y) (a : linkExterior Φ → Z)
    (b : ι → SolidTorus → Z) (y : Y) : Z :=
  if hy : y ∈ range F.exteriorEmbedding then a hy.choose
  else b (F.exists_solidTorusEmbedding_eq_of_notMem hy).choose.1
    (F.exists_solidTorusEmbedding_eq_of_notMem hy).choose.2

private theorem descFun_exteriorEmbedding (F : LinkDehnFilling h s Y) (a : linkExterior Φ → Z)
    (b : ι → SolidTorus → Z) (x : linkExterior Φ) :
    descFun F a b (F.exteriorEmbedding x) = a x := by
  have hx : F.exteriorEmbedding x ∈ range F.exteriorEmbedding := mem_range_self x
  rw [descFun, dite_eq_left hx, F.isClosedEmbedding_exteriorEmbedding.injective hx.choose_spec]

private theorem descFun_solidTorusEmbedding (F : LinkDehnFilling h s Y) {a : linkExterior Φ → Z}
    {b : ι → SolidTorus → Z}
    (hab : ∀ i q, a (h.exteriorBoundaryInclusion i (F.gluing i q)) =
      b i (SolidTorus.boundaryInclusion q))
    (i : ι) (p : SolidTorus) : descFun F a b (F.solidTorusEmbedding i p) = b i p := by
  by_cases hp : F.solidTorusEmbedding i p ∈ range F.exteriorEmbedding
  · obtain ⟨x, hx⟩ := hp
    obtain ⟨q, rfl, rfl⟩ := exteriorEmbedding_eq_solidTorusEmbedding_iff.1 hx
    rw [← hx, descFun_exteriorEmbedding, hab]
  · obtain ⟨hi, hp'⟩ := solidTorusEmbedding_eq_solidTorusEmbedding_iff.1
      (F.exists_solidTorusEmbedding_eq_of_notMem hp).choose_spec
    rw [descFun, dite_eq_right hp, hi, hp']

variable [TopologicalSpace Z]

/-- **Maps out of a Dehn filling of a link exterior.** For finitely many components, continuous
maps `a` on the link exterior and `b i` on the filling solid tori that agree along the gluings of
the boundary tori descend to a continuous map on the filled space, which is the gluing of its
closed pieces (`TauCeti.LinkDehnFilling.desc_unique`). -/
def desc [Finite ι] (F : LinkDehnFilling h s Y) (a : C(linkExterior Φ, Z))
    (b : ι → C(SolidTorus, Z))
    (hab : ∀ i q, a (h.exteriorBoundaryInclusion i (F.gluing i q)) =
      b i (SolidTorus.boundaryInclusion q)) :
    C(Y, Z) where
  toFun := descFun F a fun i ↦ ⇑(b i)
  continuous_toFun := by
    -- The exterior and the filling solid tori are finitely many closed pieces covering `Y`.
    let piece : Option ι → Set Y := fun o ↦
      o.elim (range F.exteriorEmbedding) fun i ↦ range (F.solidTorusEmbedding i)
    refine (locallyFinite_of_finite piece).continuous ?_ ?_ ?_
    · rw [iUnion_option]
      exact F.range_union_iUnion_range
    · rintro (_ | i)
      exacts [F.isClosedEmbedding_exteriorEmbedding.isClosed_range,
        (F.isClosedEmbedding_solidTorusEmbedding i).isClosed_range]
    · rintro (_ | i)
      · simp only [piece, Option.elim_none]
        rw [← image_univ, F.isClosedEmbedding_exteriorEmbedding.isInducing.continuousOn_image_iff]
        exact (continuous_congr (descFun_exteriorEmbedding F a _)).2 a.continuous |>.continuousOn
      · simp only [piece, Option.elim_some]
        rw [← image_univ,
          (F.isClosedEmbedding_solidTorusEmbedding i).isInducing.continuousOn_image_iff]
        exact (continuous_congr (descFun_solidTorusEmbedding F hab i)).2 (b i).continuous
          |>.continuousOn

/-- The map descended from `a` and `b` restricts to `a` on the link exterior. -/
@[simp]
theorem desc_exteriorEmbedding [Finite ι] (F : LinkDehnFilling h s Y) (a : C(linkExterior Φ, Z))
    (b : ι → C(SolidTorus, Z))
    (hab : ∀ i q, a (h.exteriorBoundaryInclusion i (F.gluing i q)) =
      b i (SolidTorus.boundaryInclusion q))
    (x : linkExterior Φ) : F.desc a b hab (F.exteriorEmbedding x) = a x :=
  descFun_exteriorEmbedding F a (fun i ↦ ⇑(b i)) x

/-- The map descended from `a` and `b` restricts to `b i` on the `i`-th filling solid torus. -/
@[simp]
theorem desc_solidTorusEmbedding [Finite ι] (F : LinkDehnFilling h s Y)
    (a : C(linkExterior Φ, Z)) (b : ι → C(SolidTorus, Z))
    (hab : ∀ i q, a (h.exteriorBoundaryInclusion i (F.gluing i q)) =
      b i (SolidTorus.boundaryInclusion q))
    (i : ι) (p : SolidTorus) : F.desc a b hab (F.solidTorusEmbedding i p) = b i p :=
  descFun_solidTorusEmbedding F hab i p

/-- **Maps out of a Dehn filling of a link exterior are determined by their restrictions** to the
pieces. -/
theorem hom_ext (F : LinkDehnFilling h s Y) {φ ψ : C(Y, Z)}
    (hE : ∀ x, φ (F.exteriorEmbedding x) = ψ (F.exteriorEmbedding x))
    (hS : ∀ i p, φ (F.solidTorusEmbedding i p) = ψ (F.solidTorusEmbedding i p)) : φ = ψ := by
  ext y
  obtain ⟨x, rfl⟩ | hy := F.range_union_iUnion_range.symm ▸ mem_univ y
  · exact hE x
  · obtain ⟨i, p, rfl⟩ := mem_iUnion.1 hy
    exact hS i p

/-- **Uniqueness of the descended map**: a continuous map on the filled space restricting to `a`
on the link exterior and to `b i` on the `i`-th filling solid torus is
`TauCeti.LinkDehnFilling.desc`. -/
theorem desc_unique [Finite ι] (F : LinkDehnFilling h s Y) {a : C(linkExterior Φ, Z)}
    {b : ι → C(SolidTorus, Z)}
    (hab : ∀ i q, a (h.exteriorBoundaryInclusion i (F.gluing i q)) =
      b i (SolidTorus.boundaryInclusion q))
    {φ : C(Y, Z)} (hE : ∀ x, φ (F.exteriorEmbedding x) = a x)
    (hS : ∀ i p, φ (F.solidTorusEmbedding i p) = b i p) : φ = F.desc a b hab :=
  F.hom_ext (by simpa using hE) (by simpa using hS)

end desc

/-- A Dehn filling of a link exterior is carried along a homeomorphism of the filled space. -/
def transHomeomorph (F : LinkDehnFilling h s Y) {Y' : Type*} [TopologicalSpace Y']
    (e : Y ≃ₜ Y') : LinkDehnFilling h s Y' where
  exteriorEmbedding := e ∘ F.exteriorEmbedding
  isClosedEmbedding_exteriorEmbedding :=
    e.isClosedEmbedding.comp F.isClosedEmbedding_exteriorEmbedding
  solidTorusEmbedding i := e ∘ F.solidTorusEmbedding i
  isClosedEmbedding_solidTorusEmbedding i :=
    e.isClosedEmbedding.comp (F.isClosedEmbedding_solidTorusEmbedding i)
  gluing := F.gluing
  exteriorEmbedding_exteriorBoundaryInclusion i q :=
    congrArg e (F.exteriorEmbedding_exteriorBoundaryInclusion i q)
  range_union_iUnion_range := by
    simp_rw [range_comp]
    rw [← image_iUnion, ← image_union, F.range_union_iUnion_range, image_univ, e.range_coe]
  range_inter_range_subset i := by
    rw [range_comp, range_comp, ← image_inter e.injective, Function.comp_assoc, range_comp]
    exact image_mono (F.range_inter_range_subset i)
  pairwiseDisjoint_range _ _ hij := by
    simp only [Function.onFun, range_comp]
    exact (disjoint_image_iff e.injective).2 (F.pairwiseDisjoint_range hij)
  fillingSlope_gluing := F.fillingSlope_gluing

/-- The exterior embedding of a transported filling is the composite with the homeomorphism. -/
@[simp]
theorem transHomeomorph_exteriorEmbedding (F : LinkDehnFilling h s Y) {Y' : Type*}
    [TopologicalSpace Y'] (e : Y ≃ₜ Y') :
    (F.transHomeomorph e).exteriorEmbedding = e ∘ F.exteriorEmbedding :=
  (rfl)

/-- The solid torus embeddings of a transported filling are the composites with the
homeomorphism. -/
@[simp]
theorem transHomeomorph_solidTorusEmbedding (F : LinkDehnFilling h s Y) {Y' : Type*}
    [TopologicalSpace Y'] (e : Y ≃ₜ Y') (i : ι) :
    (F.transHomeomorph e).solidTorusEmbedding i = e ∘ F.solidTorusEmbedding i :=
  (rfl)

/-- Transport along a homeomorphism of the filled space keeps the gluings. -/
@[simp]
theorem transHomeomorph_gluing (F : LinkDehnFilling h s Y) {Y' : Type*} [TopologicalSpace Y']
    (e : Y ≃ₜ Y') : (F.transHomeomorph e).gluing = F.gluing :=
  (rfl)

end LinkDehnFilling

namespace IsSolidTorusLinkNeighborhood

/-- **The trivial Dehn filling of a link exterior.** Gluing every solid torus neighbourhood `Φ i`
back into the exterior by the identity recovers the ambient space: `X` is the Dehn filling of the
link exterior along the meridian slopes of all the `Φ i`, the `∞`-surgery on every component. -/
def meridianDehnFilling (h : IsSolidTorusLinkNeighborhood f Φ) :
    LinkDehnFilling h (fun i ↦ (h.neighborhood i).framedBoundaryTorus.meridian) X where
  exteriorEmbedding := Subtype.val
  isClosedEmbedding_exteriorEmbedding := h.isClosed_linkExterior.isClosedEmbedding_subtypeVal
  solidTorusEmbedding := Φ
  isClosedEmbedding_solidTorusEmbedding i := (h.neighborhood i).isClosedEmbedding
  gluing _ := Homeomorph.refl _
  exteriorEmbedding_exteriorBoundaryInclusion i q := h.coe_exteriorBoundaryInclusion_apply i q
  range_union_iUnion_range := by
    rw [Subtype.range_coe, eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ linkExterior Φ
    · exact Or.inl hx
    · obtain ⟨i, hi⟩ := not_forall.1 (mt mem_linkExterior.2 hx)
      exact Or.inr (mem_iUnion.2 ⟨i, image_subset_range _ _ (not_not.1 hi)⟩)
  range_inter_range_subset i := by
    rintro _ ⟨hx, p, rfl⟩
    rw [Subtype.range_coe, mem_linkExterior] at hx
    have hp : ‖(p.1 : ℂ)‖ = 1 :=
      le_antisymm (mem_closedBall_zero_iff.mp p.1.2)
        (not_lt.mp fun hp ↦ hx i ⟨p, hp, rfl⟩)
    rw [range_comp, SolidTorus.range_boundaryInclusion]
    exact mem_image_of_mem _ hp
  pairwiseDisjoint_range := h.pairwiseDisjoint_range
  fillingSlope_gluing i := (h.neighborhood i).fillingSlope_refl

/-- The trivial filling of a link exterior embeds the exterior by its inclusion. -/
@[simp]
theorem meridianDehnFilling_exteriorEmbedding (h : IsSolidTorusLinkNeighborhood f Φ) :
    h.meridianDehnFilling.exteriorEmbedding = Subtype.val :=
  (rfl)

/-- The filling solid tori of the trivial filling are the solid torus neighbourhoods. -/
@[simp]
theorem meridianDehnFilling_solidTorusEmbedding (h : IsSolidTorusLinkNeighborhood f Φ) :
    h.meridianDehnFilling.solidTorusEmbedding = Φ :=
  (rfl)

/-- The trivial filling glues every pair of boundary tori by the identity. -/
@[simp]
theorem meridianDehnFilling_gluing (h : IsSolidTorusLinkNeighborhood f Φ) (i : ι) :
    h.meridianDehnFilling.gluing i = Homeomorph.refl _ :=
  (rfl)

end IsSolidTorusLinkNeighborhood

namespace DehnFilling

variable [Unique ι] (h : IsSolidTorusLinkNeighborhood f Φ)
  {s : ∀ i, Slope (h.neighborhood i).framedBoundaryTorus.H} {Y : Type*} [TopologicalSpace Y]

/-- **A Dehn filling of a knot exterior is a Dehn filling of a one-component link exterior.** The
exterior of the only component is the link exterior (`TauCeti.linkExterior_unique`), and the
filling solid torus of the knot is that of the only component. -/
def toLinkDehnFilling (F : DehnFilling (h.neighborhood default) (s default) Y) :
    LinkDehnFilling h s Y where
  exteriorEmbedding := F.exteriorEmbedding ∘ Homeomorph.setCongr (linkExterior_unique Φ)
  isClosedEmbedding_exteriorEmbedding :=
    F.isClosedEmbedding_exteriorEmbedding.comp (Homeomorph.setCongr _).isClosedEmbedding
  solidTorusEmbedding _ := F.solidTorusEmbedding
  isClosedEmbedding_solidTorusEmbedding _ := F.isClosedEmbedding_solidTorusEmbedding
  gluing _ := F.gluing
  exteriorEmbedding_exteriorBoundaryInclusion i q := by
    obtain rfl := Subsingleton.elim i default
    rw [← F.exteriorEmbedding_exteriorBoundaryInclusion q, comp_apply]
    congr 1
    ext1
    simp
  range_union_iUnion_range := by
    rw [range_comp, Homeomorph.range_coe, image_univ, iUnion_const, F.range_union_range]
  range_inter_range_subset _ := by
    rw [range_comp, Homeomorph.range_coe, image_univ]
    exact F.range_inter_range_subset
  pairwiseDisjoint_range i j hij := (hij (Subsingleton.elim i j)).elim
  fillingSlope_gluing i := by
    obtain rfl := Subsingleton.elim i default
    exact F.fillingSlope_gluing

/-- The filling solid torus of the only component is the filling solid torus of the knot. -/
@[simp]
theorem toLinkDehnFilling_solidTorusEmbedding
    (F : DehnFilling (h.neighborhood default) (s default) Y) (i : ι) :
    (F.toLinkDehnFilling h).solidTorusEmbedding i = F.solidTorusEmbedding :=
  (rfl)

/-- The gluing of the only component is the gluing of the knot filling. -/
@[simp]
theorem toLinkDehnFilling_gluing (F : DehnFilling (h.neighborhood default) (s default) Y)
    (i : ι) : (F.toLinkDehnFilling h).gluing i = F.gluing :=
  (rfl)

/-- The link exterior is embedded as the knot exterior, which is the same subset of `X`. -/
@[simp]
theorem toLinkDehnFilling_exteriorEmbedding_apply
    (F : DehnFilling (h.neighborhood default) (s default) Y) (x : linkExterior Φ) :
    (F.toLinkDehnFilling h).exteriorEmbedding x =
      F.exteriorEmbedding ⟨x, linkExterior_unique Φ ▸ x.2⟩ :=
  (rfl)

end DehnFilling

end TauCeti
