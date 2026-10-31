/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Shrink
public import TauCeti.LowDimTopology.DehnSurgery.Link.Filling
public import TauCeti.LowDimTopology.DehnSurgery.Uniqueness
public import TauCeti.Topology.CWComplex.Abstract.Hausdorff

/-!
# Existence of Dehn fillings

A Dehn filling of a knot exterior `E` along a slope `s` (`TauCeti.DehnFilling h s Y`) is recorded
inside the filled space `Y`. This file constructs such a space for every slope, and likewise for
the exteriors of links with finitely many components (`TauCeti.LinkDehnFilling`). So every Dehn
surgery on a knot, or on a link with finitely many components (such as the rational surgeries
on links in `S³`, `TauCeti.IsSolidTorusLinkNeighborhood.surgerySlope`), exists.

The filled space is the space obtained from the exterior by attaching solid tori `V = D² × S¹`
along homeomorphisms `g` of their boundary tori: the pushout in `TopCat` of the boundary
inclusions `S¹ × S¹ → D² × S¹` and of the parametrized boundary tori of the exterior, precomposed
with the gluings (`TauCeti.IsSolidTorusNeighborhood.dehnFillingSpace`,
`TauCeti.IsSolidTorusLinkNeighborhood.linkDehnFillingSpace`). Its properties are those of the
cobase change of a closed embedding in `TopCat`:

* both maps into the pushout are closed embeddings
  (`TauCeti.TopCat.isClosedEmbedding_of_isPushout`), the boundary torus of the exterior and the
  boundary tori of the solid tori being compact and embedded;
* the pushout is Hausdorff, as an attachment of cells `D² × S¹` along their boundary tori
  (`HomotopicalAlgebra.AttachCells.t2Space`), since the boundary inclusion extends disjoint open
  sets (`TauCeti.SolidTorus.extendsDisjointOpens_boundaryInclusion`);
* it is compact when the ambient space is.

Every slope is the filling slope of a gluing induced by an invertible integral matrix
(`TauCeti.IsSolidTorusNeighborhood.exists_fillingSlope_torusHomeomorph_eq`): a primitive class
with coordinates `(p, q)` extends to a basis, by a matrix `[[p, -b], [q, a]]` with `a p + b q = 1`.

## Main definitions

* `TauCeti.IsSolidTorusNeighborhood.dehnFillingSpace h g`: the knot exterior with a solid torus
  attached along the gluing `g`.
* `TauCeti.IsSolidTorusNeighborhood.dehnFillingOfGluing h g`: the Dehn filling of the knot exterior
  in that space, along the filling slope of `g`.
* `TauCeti.IsSolidTorusLinkNeighborhood.linkDehnFillingSpace h g`,
  `TauCeti.IsSolidTorusLinkNeighborhood.linkDehnFillingOfGluing h g`: the same for the exterior of
  a link with finitely many components, with one gluing `g i` for each component.

## Main results

* `TauCeti.IsSolidTorusNeighborhood.exists_dehnFilling`: a knot exterior has a Dehn filling along
  every slope.
* `TauCeti.IsSolidTorusLinkNeighborhood.exists_linkDehnFilling`: the exterior of a link with
  finitely many components has a Dehn filling along every family of slopes.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9, Sections 9F and 9G (Dehn
  surgery: a solid torus is sewn to each boundary torus of the exterior, its meridian going to the
  chosen slope).
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Function

namespace TauCeti

/-! ### Attaching solid tori along their boundary tori -/

section Attach

variable {ι : Type} {E : Type} [TopologicalSpace E]

/-- The boundary inclusion `S¹ × S¹ → D² × S¹` of a solid torus, as a map of `TopCat`. -/
private abbrev boundaryInclusionHom : TopCat.of (Circle × Circle) ⟶ TopCat.of SolidTorus :=
  TopCat.ofHom ⟨SolidTorus.boundaryInclusion, SolidTorus.isEmbedding_boundaryInclusion.continuous⟩

private theorem isClosedEmbedding_boundaryInclusionHom :
    IsClosedEmbedding boundaryInclusionHom :=
  boundaryInclusionHom.hom.continuous.isClosedEmbedding
    SolidTorus.isEmbedding_boundaryInclusion.injective

/-- The boundary inclusions `S¹ × S¹ → D² × S¹` of a family of solid tori, as a map of `TopCat`. -/
private def sigmaBoundaryInclusion (ι : Type) :
    TopCat.of (Σ _ : ι, Circle × Circle) ⟶ TopCat.of (Σ _ : ι, SolidTorus) :=
  TopCat.ofHom ⟨Sigma.map id fun _ ↦ SolidTorus.boundaryInclusion,
    Continuous.sigma_map fun _ ↦ SolidTorus.isEmbedding_boundaryInclusion.continuous⟩

/-- Attaching maps `e i` of the boundary tori of a family of solid tori, as a map of `TopCat`. -/
private def sigmaAttach (e : ι → C(Circle × Circle, E)) :
    TopCat.of (Σ _ : ι, Circle × Circle) ⟶ TopCat.of E :=
  TopCat.ofHom ⟨fun p ↦ e p.1 p.2, continuous_sigma fun i ↦ (e i).continuous⟩

/-- The space obtained from `E` by attaching a solid torus along the map `e i` of its boundary
torus, for every `i`. -/
private abbrev attach (e : ι → C(Circle × Circle, E)) : TopCat :=
  pushout (sigmaAttach e) (sigmaBoundaryInclusion ι)

private theorem isPushout_attach (e : ι → C(Circle × Circle, E)) :
    IsPushout (sigmaAttach e) (sigmaBoundaryInclusion ι)
      (pushout.inl (sigmaAttach e) (sigmaBoundaryInclusion ι))
      (pushout.inr (sigmaAttach e) (sigmaBoundaryInclusion ι)) :=
  .of_hasPushout _ _

private theorem range_inl_union_range_inr (e : ι → C(Circle × Circle, E)) :
    range (pushout.inl (sigmaAttach e) (sigmaBoundaryInclusion ι)) ∪
      range (pushout.inr (sigmaAttach e) (sigmaBoundaryInclusion ι)) = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  obtain ⟨y, rfl⟩ | ⟨p, rfl, -⟩ :=
    Types.eq_or_eq_of_isPushout' ((forget TopCat).map_isPushout (isPushout_attach e)) x
  · exact Or.inl ⟨y, rfl⟩
  · exact Or.inr ⟨p, rfl⟩

private theorem inl_apply_eq_inr (e : ι → C(Circle × Circle, E)) (i : ι) (q : Circle × Circle) :
    pushout.inl (sigmaAttach e) (sigmaBoundaryInclusion ι) (e i q) =
      pushout.inr (sigmaAttach e) (sigmaBoundaryInclusion ι) ⟨i, SolidTorus.boundaryInclusion q⟩ :=
  ConcreteCategory.congr_hom (isPushout_attach e).w ⟨i, q⟩

/-- When the attaching maps are jointly injective, a point of `E` and a point of a solid torus are
identified exactly when the latter is a point of the boundary torus attached to the former. -/
private theorem inl_eq_inr_iff {e : ι → C(Circle × Circle, E)}
    (he : Injective fun p : Σ _ : ι, Circle × Circle ↦ e p.1 p.2) (x : E)
    (p : Σ _ : ι, SolidTorus) :
    pushout.inl (sigmaAttach e) (sigmaBoundaryInclusion ι) x =
        pushout.inr (sigmaAttach e) (sigmaBoundaryInclusion ι) p ↔
      ∃ q : Σ _ : ι, Circle × Circle, e q.1 q.2 = x ∧
        (⟨q.1, SolidTorus.boundaryInclusion q.2⟩ : Σ _ : ι, SolidTorus) = p :=
  Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
    ((forget TopCat).map_isPushout (isPushout_attach e)).isColimit he x p

/-- The space obtained by attaching solid tori to `E` along the maps `e i`, as an attachment of
cells `D² × S¹` along their boundary tori. -/
private def attachCells (e : ι → C(Circle × Circle, E)) :
    HomotopicalAlgebra.AttachCells.{0} (fun _ : Unit ↦ boundaryInclusionHom)
      (pushout.inl (sigmaAttach e) (sigmaBoundaryInclusion ι)) where
  ι := ι
  π _ := ()
  cofan₁ := TopCat.sigmaCofan fun _ ↦ TopCat.of (Circle × Circle)
  cofan₂ := TopCat.sigmaCofan fun _ ↦ TopCat.of SolidTorus
  isColimit₁ := TopCat.sigmaCofanIsColimit _
  isColimit₂ := TopCat.sigmaCofanIsColimit _
  m := sigmaBoundaryInclusion ι
  hm _ := rfl
  g₁ := sigmaAttach e
  g₂ := pushout.inr (sigmaAttach e) (sigmaBoundaryInclusion ι)
  isPushout := isPushout_attach e

/-- The boundary inclusions of a family of solid tori form a closed embedding, as a coproduct of
closed embeddings. -/
private theorem isClosedEmbedding_sigmaBoundaryInclusion :
    IsClosedEmbedding (sigmaBoundaryInclusion ι) :=
  (TopCat.isClosedEmbedding_iff _).1 <|
    MorphismProperty.IsStableUnderColimitsOfShape.condition
      (Discrete.functor fun _ : ι ↦ TopCat.of (Circle × Circle))
      (Discrete.functor fun _ : ι ↦ TopCat.of SolidTorus) _ _
      (TopCat.sigmaCofanIsColimit _) (TopCat.sigmaCofanIsColimit _)
      (Discrete.natTrans fun _ ↦ boundaryInclusionHom)
      (fun _ ↦ (TopCat.isClosedEmbedding_iff _).2 isClosedEmbedding_boundaryInclusionHom) _
      fun _ ↦ rfl

private theorem isClosedEmbedding_inl (e : ι → C(Circle × Circle, E)) :
    IsClosedEmbedding (pushout.inl (sigmaAttach e) (sigmaBoundaryInclusion ι)) :=
  TopCat.isClosedEmbedding_of_isPushout (isPushout_attach e)
    isClosedEmbedding_sigmaBoundaryInclusion

/-- The space obtained by attaching solid tori to a Hausdorff space is Hausdorff. -/
private theorem t2Space_attach [T2Space E] (e : ι → C(Circle × Circle, E)) :
    T2Space (attach e) :=
  (attachCells e).t2Space (fun _ ↦ SolidTorus.extendsDisjointOpens_boundaryInclusion)
    fun _ ↦ isClosedEmbedding_boundaryInclusionHom

variable [Finite ι]

/-- The space obtained by attaching finitely many solid tori to a compact space is compact. -/
private theorem compactSpace_attach [CompactSpace E] (e : ι → C(Circle × Circle, E)) :
    CompactSpace (attach e) := by
  refine ⟨?_⟩
  rw [← range_inl_union_range_inr e]
  exact (isCompact_range (pushout.inl (sigmaAttach e) _).hom.continuous).union
    (isCompact_range (pushout.inr _ (sigmaBoundaryInclusion ι)).hom.continuous)

/-- When the attaching maps are jointly injective, the solid tori are embedded in the space
obtained by attaching them to a Hausdorff space. -/
private theorem isClosedEmbedding_inr [T2Space E] {e : ι → C(Circle × Circle, E)}
    (he : Injective fun p : Σ _ : ι, Circle × Circle ↦ e p.1 p.2) :
    IsClosedEmbedding (pushout.inr (sigmaAttach e) (sigmaBoundaryInclusion ι)) :=
  TopCat.isClosedEmbedding_of_isPushout (isPushout_attach e).flip
    ((sigmaAttach e).hom.continuous.isClosedEmbedding he)

end Attach

/-! ### Dehn fillings of knot exteriors -/

namespace IsSolidTorusNeighborhood

variable {X : Type} [TopologicalSpace X] [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}

/-- The attaching map of the filling solid torus of a knot exterior along a gluing `g`: the point
`q` of the boundary torus of the solid torus goes to the point `Φ (g q)` of the boundary torus of
the exterior. -/
private def fillingAttach (h : IsSolidTorusNeighborhood f Φ)
    (g : Circle × Circle ≃ₜ Circle × Circle) : Unit → C(Circle × Circle, knotExterior (Φ := Φ)) :=
  fun _ ↦ ⟨h.exteriorBoundaryInclusion ∘ g,
    h.isEmbedding_exteriorBoundaryInclusion.continuous.comp g.continuous⟩

omit [T2Space X] in
private theorem injective_fillingAttach (h : IsSolidTorusNeighborhood f Φ)
    (g : Circle × Circle ≃ₜ Circle × Circle) :
    Injective fun p : Σ _ : Unit, Circle × Circle ↦ h.fillingAttach g p.1 p.2 := by
  rintro ⟨⟨⟩, q⟩ ⟨⟨⟩, q'⟩ hq
  obtain rfl := g.injective (h.exteriorBoundaryInclusion_injective hq)
  rfl

/-- **The Dehn filling space** of a knot exterior along a gluing `g` of the boundary tori: the
exterior with a solid torus `D² × S¹` attached, the point `q` of the boundary torus of the solid
torus being identified with the point `Φ (g q)` of the boundary torus of the exterior. The Dehn
filling it carries is `TauCeti.IsSolidTorusNeighborhood.dehnFillingOfGluing`. -/
def dehnFillingSpace (h : IsSolidTorusNeighborhood f Φ) (g : Circle × Circle ≃ₜ Circle × Circle) :
    TopCat :=
  attach (h.fillingAttach g)

/-- A Dehn filling space of a knot exterior in a Hausdorff space is Hausdorff. -/
instance (h : IsSolidTorusNeighborhood f Φ) (g : Circle × Circle ≃ₜ Circle × Circle) :
    T2Space (h.dehnFillingSpace g) :=
  t2Space_attach (h.fillingAttach g)

/-- A Dehn filling space of a knot exterior in a compact space is compact. -/
instance [CompactSpace X] (h : IsSolidTorusNeighborhood f Φ)
    (g : Circle × Circle ≃ₜ Circle × Circle) : CompactSpace (h.dehnFillingSpace g) :=
  have : CompactSpace (knotExterior (Φ := Φ)) := isCompact_iff_compactSpace.1 h.isCompact_exterior
  compactSpace_attach (h.fillingAttach g)

/-- **The Dehn filling along a gluing.** The knot exterior and the solid torus are closed subsets
of the Dehn filling space `TauCeti.IsSolidTorusNeighborhood.dehnFillingSpace h g`, glued along
`g`, so that space is a Dehn filling of the exterior along the filling slope of `g`. -/
def dehnFillingOfGluing (h : IsSolidTorusNeighborhood f Φ)
    (g : Circle × Circle ≃ₜ Circle × Circle) :
    DehnFilling h (h.fillingSlope g) (h.dehnFillingSpace g) where
  exteriorEmbedding := pushout.inl (sigmaAttach (h.fillingAttach g)) (sigmaBoundaryInclusion Unit)
  isClosedEmbedding_exteriorEmbedding := isClosedEmbedding_inl _
  solidTorusEmbedding p :=
    pushout.inr (sigmaAttach (h.fillingAttach g)) (sigmaBoundaryInclusion Unit) ⟨(), p⟩
  isClosedEmbedding_solidTorusEmbedding :=
    (isClosedEmbedding_inr (h.injective_fillingAttach g)).comp IsClosedEmbedding.sigmaMk
  gluing := g
  exteriorEmbedding_exteriorBoundaryInclusion q := inl_apply_eq_inr (h.fillingAttach g) () q
  range_union_range := by
    refine eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, hx⟩ | ⟨⟨⟨⟩, p⟩, hp⟩ :=
      eq_univ_iff_forall.1 (range_inl_union_range_inr (h.fillingAttach g)) y
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨p, hp⟩
  range_inter_range_subset := by
    rintro _ ⟨⟨x, rfl⟩, p, hp⟩
    obtain ⟨⟨⟨⟩, q⟩, -, hq⟩ :=
      (inl_eq_inr_iff (h.injective_fillingAttach g) x ⟨(), p⟩).1 hp.symm
    obtain rfl : SolidTorus.boundaryInclusion q = p := eq_of_heq (Sigma.mk.inj_iff.1 hq).2
    exact ⟨q, hp⟩
  fillingSlope_gluing := rfl

/-- The Dehn filling along a gluing glues the boundary tori by that gluing. -/
@[simp]
theorem dehnFillingOfGluing_gluing (h : IsSolidTorusNeighborhood f Φ)
    (g : Circle × Circle ≃ₜ Circle × Circle) : (h.dehnFillingOfGluing g).gluing = g :=
  (rfl)

/-- **Existence of Dehn fillings.** A knot exterior has a Dehn filling along every slope, with a
gluing induced by an invertible integral matrix. -/
theorem exists_dehnFilling (h : IsSolidTorusNeighborhood f Φ) (s : Slope h.framedBoundaryTorus.H) :
    ∃ A : GL (Fin 2) ℤ, Nonempty (DehnFilling h s (h.dehnFillingSpace A.torusHomeomorph)) := by
  obtain ⟨A, rfl⟩ := h.exists_fillingSlope_torusHomeomorph_eq s
  exact ⟨A, ⟨h.dehnFillingOfGluing _⟩⟩

end IsSolidTorusNeighborhood

/-! ### Dehn fillings of link exteriors -/

namespace IsSolidTorusLinkNeighborhood

variable {ι : Type*} {X : Type} [TopologicalSpace X] [T2Space X] {f : ι → Circle → X}
  {Φ : ι → SolidTorus → X}

section Small

variable [Small.{0} ι]

/-- The attaching maps of the filling solid tori of a link exterior along gluings `g i`, indexed by
a copy `Shrink.{0} ι` of the components in `Type`: the point `q` of the boundary torus of the
`i`-th solid torus goes to the point `Φ i (g i q)` of the `i`-th boundary torus of the exterior. -/
private def fillingAttach (h : IsSolidTorusLinkNeighborhood f Φ)
    (g : ι → Circle × Circle ≃ₜ Circle × Circle) :
    Shrink.{0} ι → C(Circle × Circle, linkExterior Φ) :=
  fun i ↦ ⟨h.exteriorBoundaryInclusion ((equivShrink.{0} ι).symm i) ∘
      g ((equivShrink.{0} ι).symm i),
    (h.isEmbedding_exteriorBoundaryInclusion _).continuous.comp (g _).continuous⟩

omit [T2Space X] in
private theorem fillingAttach_equivShrink (h : IsSolidTorusLinkNeighborhood f Φ)
    (g : ι → Circle × Circle ≃ₜ Circle × Circle) (i : ι) (q : Circle × Circle) :
    h.fillingAttach g (equivShrink.{0} ι i) q = h.exteriorBoundaryInclusion i (g i q) := by
  simp [fillingAttach]

omit [T2Space X] in
/-- The boundary tori of distinct components are disjoint, so the attaching maps are jointly
injective. -/
private theorem injective_fillingAttach (h : IsSolidTorusLinkNeighborhood f Φ)
    (g : ι → Circle × Circle ≃ₜ Circle × Circle) :
    Injective fun p : Σ _ : Shrink.{0} ι, Circle × Circle ↦ h.fillingAttach g p.1 p.2 := by
  rintro ⟨i, q⟩ ⟨j, q'⟩ hq
  obtain ⟨i, rfl⟩ := (equivShrink.{0} ι).surjective i
  obtain ⟨j, rfl⟩ := (equivShrink.{0} ι).surjective j
  simp only [fillingAttach_equivShrink] at hq
  obtain rfl : i = j := by
    by_contra hij
    have hx : Φ i (SolidTorus.boundaryInclusion (g i q)) =
        Φ j (SolidTorus.boundaryInclusion (g j q')) := by
      simpa using congrArg Subtype.val hq
    exact (h.pairwiseDisjoint_range hij).ne_of_mem (mem_range_self _) (mem_range_self _) hx
  obtain rfl := (g i).injective (h.exteriorBoundaryInclusion_injective i hq)
  rfl

/-- **The Dehn filling space** of the exterior of a link with finitely many components along
gluings `g i` of the boundary tori: the exterior with a solid torus `D² × S¹` attached for each
component `i`, the point `q` of its boundary torus being identified with the point `Φ i (g i q)`
of the `i`-th boundary torus of the exterior. The Dehn filling it carries is
`TauCeti.IsSolidTorusLinkNeighborhood.linkDehnFillingOfGluing`. -/
def linkDehnFillingSpace (h : IsSolidTorusLinkNeighborhood f Φ)
    (g : ι → Circle × Circle ≃ₜ Circle × Circle) : TopCat :=
  attach (h.fillingAttach g)

/-- A Dehn filling space of a link exterior in a Hausdorff space is Hausdorff. -/
instance (h : IsSolidTorusLinkNeighborhood f Φ) (g : ι → Circle × Circle ≃ₜ Circle × Circle) :
    T2Space (h.linkDehnFillingSpace g) :=
  t2Space_attach (h.fillingAttach g)

end Small

variable [Finite ι]

/-- A Dehn filling space of the exterior of a link with finitely many components in a compact
space is compact. -/
instance [CompactSpace X] (h : IsSolidTorusLinkNeighborhood f Φ)
    (g : ι → Circle × Circle ≃ₜ Circle × Circle) : CompactSpace (h.linkDehnFillingSpace g) :=
  have : CompactSpace (linkExterior Φ) := isCompact_iff_compactSpace.1 h.isCompact_linkExterior
  compactSpace_attach (h.fillingAttach g)

/-- **The Dehn filling of a link exterior along gluings.** The link exterior and the solid tori are
closed subsets of the Dehn filling space `TauCeti.IsSolidTorusLinkNeighborhood.linkDehnFillingSpace
h g`, the `i`-th solid torus being glued along `g i`, so that space is a Dehn filling of the
exterior along the filling slopes of the `g i`. -/
def linkDehnFillingOfGluing (h : IsSolidTorusLinkNeighborhood f Φ)
    (g : ι → Circle × Circle ≃ₜ Circle × Circle) :
    LinkDehnFilling h (fun i ↦ (h.neighborhood i).fillingSlope (g i))
      (h.linkDehnFillingSpace g) where
  exteriorEmbedding :=
    pushout.inl (sigmaAttach (h.fillingAttach g)) (sigmaBoundaryInclusion (Shrink.{0} ι))
  isClosedEmbedding_exteriorEmbedding := isClosedEmbedding_inl _
  solidTorusEmbedding i p :=
    pushout.inr (sigmaAttach (h.fillingAttach g)) (sigmaBoundaryInclusion (Shrink.{0} ι))
      ⟨equivShrink.{0} ι i, p⟩
  isClosedEmbedding_solidTorusEmbedding _ :=
    (isClosedEmbedding_inr (h.injective_fillingAttach g)).comp IsClosedEmbedding.sigmaMk
  gluing := g
  exteriorEmbedding_exteriorBoundaryInclusion i q := by
    rw [← fillingAttach_equivShrink h g i q]
    exact inl_apply_eq_inr (h.fillingAttach g) (equivShrink.{0} ι i) q
  range_union_iUnion_range := by
    refine eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, hx⟩ | ⟨⟨i, p⟩, hp⟩ :=
      eq_univ_iff_forall.1 (range_inl_union_range_inr (h.fillingAttach g)) y
    · exact Or.inl ⟨x, hx⟩
    · obtain ⟨i, rfl⟩ := (equivShrink.{0} ι).surjective i
      exact Or.inr (mem_iUnion.2 ⟨i, p, hp⟩)
  range_inter_range_subset i := by
    rintro _ ⟨⟨x, rfl⟩, p, hp⟩
    obtain ⟨⟨j, q⟩, -, hq⟩ :=
      (inl_eq_inr_iff (h.injective_fillingAttach g) x ⟨equivShrink.{0} ι i, p⟩).1 hp.symm
    cases hq
    exact ⟨q, hp⟩
  pairwiseDisjoint_range i j hij := by
    refine disjoint_left.2 ?_
    rintro _ ⟨p, rfl⟩ ⟨p', hp'⟩
    exact hij ((equivShrink.{0} ι).injective (congrArg Sigma.fst
      ((isClosedEmbedding_inr (h.injective_fillingAttach g)).injective hp')).symm)
  fillingSlope_gluing _ := rfl

/-- The Dehn filling of a link exterior along gluings glues the boundary tori by those
gluings. -/
@[simp]
theorem linkDehnFillingOfGluing_gluing (h : IsSolidTorusLinkNeighborhood f Φ)
    (g : ι → Circle × Circle ≃ₜ Circle × Circle) : (h.linkDehnFillingOfGluing g).gluing = g :=
  (rfl)

/-- **Existence of Dehn fillings of link exteriors.** The exterior of a link with finitely many
components has a Dehn filling along every family of slopes, one on each boundary torus, with
gluings induced by invertible integral matrices. In particular every rational surgery on a link in
`S³` with finitely many components (`TauCeti.IsSolidTorusLinkNeighborhood.surgerySlope`) exists. -/
theorem exists_linkDehnFilling (h : IsSolidTorusLinkNeighborhood f Φ)
    (s : ∀ i, Slope (h.neighborhood i).framedBoundaryTorus.H) :
    ∃ A : ι → GL (Fin 2) ℤ,
      Nonempty (LinkDehnFilling h s (h.linkDehnFillingSpace fun i ↦ (A i).torusHomeomorph)) := by
  choose A hA using fun i ↦ (h.neighborhood i).exists_fillingSlope_torusHomeomorph_eq (s i)
  obtain rfl : (fun i ↦ (h.neighborhood i).fillingSlope (A i).torusHomeomorph) = s := funext hA
  exact ⟨A, ⟨h.linkDehnFillingOfGluing _⟩⟩

end IsSolidTorusLinkNeighborhood

end TauCeti
