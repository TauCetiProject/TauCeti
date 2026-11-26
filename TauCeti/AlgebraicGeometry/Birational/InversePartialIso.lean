/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import TauCeti.AlgebraicGeometry.Birational.Composition

/-!
# Rational maps with a two-sided inverse are partial isomorphisms

Let `X` and `Y` be integral separated schemes, `F : X.PartialMap Y` and `G : Y.PartialMap X`
dominant partial maps whose composites are the identity as rational maps. On the domain
`U₀ = F⁻¹(dom G)` of `F.comp G`, the composite `G ∘ F` is then the inclusion of `U₀`, not only on
a smaller dense open: two morphisms from a reduced scheme to a separated scheme that agree on a
dense open agree (`PartialMap.equiv_toPartialMap_iff_of_isSeparated`). So `F` maps `U₀` into the
domain `V₀ = G⁻¹(dom F)` of `G.comp F`, `G` maps `V₀` into `U₀`, and the two restrictions are
inverse isomorphisms `U₀ ≅ V₀`: a partial isomorphism whose rational map is that of `F`
(`AlgebraicGeometry.Scheme.PartialMap.partialIsoOfComp`).

For rational maps this says that a dominant rational map `f : X ⤏ Y` with a dominant two-sided
inverse is the rational map of a partial isomorphism
(`AlgebraicGeometry.Scheme.RationalMap.exists_partialIso_toRationalMap_eq`), so `f` is
birational.

## Main definitions

* `AlgebraicGeometry.Scheme.PartialMap.partialIsoOfComp`: the partial isomorphism of partial maps
  `F` and `G` whose composites are the identity as rational maps.

## Main results

* `AlgebraicGeometry.Scheme.PartialMap.toRationalMap_partialIsoOfComp`: the rational map of
  `partialIsoOfComp h h'` is that of `F`.
* `AlgebraicGeometry.Scheme.PartialMap.symm_partialIsoOfComp`: the inverse of
  `partialIsoOfComp h h'` is `partialIsoOfComp h' h`.
* `AlgebraicGeometry.Scheme.RationalMap.exists_partialIso_toRationalMap_eq`: a dominant rational
  map with a dominant two-sided inverse is the rational map of a partial isomorphism.
* `AlgebraicGeometry.Scheme.RationalMap.exists_partialIso_isOver_toRationalMap_eq`: the same over
  a base `S`, with the partial isomorphism over `S`.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

namespace PartialMap

variable {F : X.PartialMap Y} [IsDominant F.hom] {G : Y.PartialMap X} [IsDominant G.hom]

/-- If `F.comp G` is the identity rational map, `F` maps the domain of `F.comp G` into the domain
of `G.comp F`. -/
private theorem range_compDomainRestrict_ι_subset [X.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X) :
    Set.range (compDomainRestrict F G ≫ G.domain.ι) ⊆ Set.range (G.comp F).domain.ι := by
  rintro _ ⟨x, rfl⟩
  rw [Opens.range_ι, comp_domain]
  refine ⟨compDomainRestrict F G x, ?_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rw [SetLike.mem_coe, Hom.mem_preimage]
  have hx : G.hom (compDomainRestrict F G x) = (F.comp G).domain.ι x := by
    rw [← Scheme.Hom.comp_apply, compDomainRestrict_hom, comp_hom_eq_ι F G h]
  have hmem : (F.comp G).domain.ι x ∈ Set.range (F.comp G).domain.ι := ⟨x, rfl⟩
  rw [Opens.range_ι] at hmem
  rw [hx]
  exact comp_domain_le F G hmem

/-- The morphism from the domain of `F.comp G` to the domain of `G.comp F` given by `F`. -/
private noncomputable def partialIsoHom [X.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X) :
    (F.comp G).domain.toScheme ⟶ (G.comp F).domain.toScheme :=
  IsOpenImmersion.lift (G.comp F).domain.ι (compDomainRestrict F G ≫ G.domain.ι)
    (range_compDomainRestrict_ι_subset h)

/-- `partialIsoHom h`, read in `Y`, is `F` on the domain of `F.comp G`. -/
private theorem partialIsoHom_ι [X.IsSeparated] (h : (F.comp G).toRationalMap = RationalMap.id X) :
    partialIsoHom h ≫ (G.comp F).domain.ι = compDomainRestrict F G ≫ G.domain.ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- `partialIsoHom h`, read in the domain of `G`, is `compDomainRestrict F G`. -/
private theorem partialIsoHom_homOfLE [X.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X) :
    partialIsoHom h ≫ Y.homOfLE (comp_domain_le G F) = compDomainRestrict F G := by
  rw [← cancel_mono G.domain.ι, Category.assoc, homOfLE_ι, partialIsoHom_ι]

/-- The restrictions of `F` and `G` are mutually inverse. -/
private theorem partialIsoHom_partialIsoHom_id [X.IsSeparated] [Y.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X)
    (h' : (G.comp F).toRationalMap = RationalMap.id Y) :
    partialIsoHom h ≫ partialIsoHom h' = 𝟙 _ := by
  rw [← cancel_mono (F.comp G).domain.ι, Category.assoc, partialIsoHom_ι, compDomainRestrict_ι,
    ← Category.assoc, partialIsoHom_homOfLE, compDomainRestrict_hom, comp_hom_eq_ι F G h,
    Category.id_comp]

/-- **The partial isomorphism of mutually inverse partial maps.** If `F.comp G` and `G.comp F` are
the identity rational maps, `F` restricts to an isomorphism from the domain of `F.comp G` onto the
domain of `G.comp F`, with inverse the restriction of `G`. -/
noncomputable def partialIsoOfComp [X.IsSeparated] [Y.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X)
    (h' : (G.comp F).toRationalMap = RationalMap.id Y) : X.PartialIso Y where
  source := (F.comp G).domain
  dense_source := (F.comp G).dense_domain
  target := (G.comp F).domain
  dense_target := (G.comp F).dense_domain
  iso :=
    { hom := partialIsoHom h
      inv := partialIsoHom h'
      hom_inv_id := partialIsoHom_partialIsoHom_id h h'
      inv_hom_id := partialIsoHom_partialIsoHom_id h' h }

/-- The source of `partialIsoOfComp h h'` is the domain of `F.comp G`. -/
@[simp]
theorem partialIsoOfComp_source [X.IsSeparated] [Y.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X)
    (h' : (G.comp F).toRationalMap = RationalMap.id Y) :
    (partialIsoOfComp h h').source = (F.comp G).domain :=
  (rfl)

/-- The target of `partialIsoOfComp h h'` is the domain of `G.comp F`. -/
@[simp]
theorem partialIsoOfComp_target [X.IsSeparated] [Y.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X)
    (h' : (G.comp F).toRationalMap = RationalMap.id Y) :
    (partialIsoOfComp h h').target = (G.comp F).domain :=
  (rfl)

/-- The inverse of `partialIsoOfComp h h'` is `partialIsoOfComp h' h`: its inverse map is the
restriction of `G`. -/
@[simp]
theorem symm_partialIsoOfComp [X.IsSeparated] [Y.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X)
    (h' : (G.comp F).toRationalMap = RationalMap.id Y) :
    (partialIsoOfComp h h').symm = partialIsoOfComp h' h :=
  (rfl)

/-- The morphism of the partial map of `partialIsoOfComp h h'` is `F` on the domain of
`F.comp G`. Its statement needs the source of `partialIsoOfComp h h'` to unfold to that domain,
so it is private; `toPartialMap_partialIsoOfComp` is the public form. -/
private theorem toPartialMap_partialIsoOfComp_hom [X.IsSeparated] [Y.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X)
    (h' : (G.comp F).toRationalMap = RationalMap.id Y) :
    (partialIsoOfComp h h').toPartialMap.hom = X.homOfLE (comp_domain_le F G) ≫ F.hom := by
  rw [PartialIso.toPartialMap_hom]
  exact (partialIsoHom_ι h).trans (compDomainRestrict_ι F G)

/-- The partial map of `partialIsoOfComp h h'` is `F` restricted to the domain of `F.comp G`. -/
theorem toPartialMap_partialIsoOfComp [X.IsSeparated] [Y.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X)
    (h' : (G.comp F).toRationalMap = RationalMap.id Y) :
    (partialIsoOfComp h h').toPartialMap =
      F.restrict (F.comp G).domain (F.comp G).dense_domain (comp_domain_le F G) :=
  PartialMap.ext _ _
    (by rw [PartialIso.toPartialMap_domain, partialIsoOfComp_source, restrict_domain]) (by
      rw [toPartialMap_partialIsoOfComp_hom, restrict_hom]
      exact (X.homOfLE_homOfLE_assoc le_rfl _ _).symm)

/-- **The rational map of `partialIsoOfComp h h'` is that of `F`.** -/
@[simp]
theorem toRationalMap_partialIsoOfComp [X.IsSeparated] [Y.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X)
    (h' : (G.comp F).toRationalMap = RationalMap.id Y) :
    (partialIsoOfComp h h').toRationalMap = F.toRationalMap := by
  rw [PartialIso.toRationalMap, toPartialMap_partialIsoOfComp, restrict_toRationalMap]

/-- **`partialIsoOfComp h h'` is over `S`** when `F` is: its morphism is `F` on the domain of
`F.comp G`. -/
theorem isOver_partialIsoOfComp [X.IsSeparated] [Y.IsSeparated] {S : Scheme.{u}} {sX : X ⟶ S}
    {sY : Y ⟶ S} [F.IsOver sX sY] (h : (F.comp G).toRationalMap = RationalMap.id X)
    (h' : (G.comp F).toRationalMap = RationalMap.id Y) :
    (partialIsoOfComp h h').IsOver sX sY := by
  rw [PartialIso.IsOver, ← Category.assoc, ← PartialIso.toPartialMap_hom,
    toPartialMap_partialIsoOfComp_hom]
  -- the source of `partialIsoOfComp h h'` is the domain of `F.comp G` only up to unfolding, so
  -- the motive of a `Category.assoc` rewrite is not type-correct: apply it as a term instead
  refine (Category.assoc _ _ _).trans ?_
  rw [F.over sX sY]
  exact X.homOfLE_ι_assoc _ _

end PartialMap

/-- **A dominant rational map with a dominant two-sided inverse is the rational map of a partial
isomorphism.** If `f : X ⤏ Y` and `g : Y ⤏ X` are dominant rational maps of integral separated
schemes with `f.comp g = id` and `g.comp f = id`, some partial isomorphism of `X` with `Y` has
rational map `f`. -/
theorem RationalMap.exists_partialIso_toRationalMap_eq [X.IsSeparated] [Y.IsSeparated]
    (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ X)
    [g.IsDominant] (h : f.comp g = RationalMap.id X) (h' : g.comp f = RationalMap.id Y) :
    ∃ e : X.PartialIso Y, e.toRationalMap = f :=
  ⟨PartialMap.partialIsoOfComp ((f.toRationalMap_representative_comp_representative g).trans h)
    ((g.toRationalMap_representative_comp_representative f).trans h'), by simp⟩

/-- **A dominant rational map over `S` with a dominant two-sided inverse is the rational map of a
partial isomorphism over `S`.** -/
theorem RationalMap.exists_partialIso_isOver_toRationalMap_eq [X.IsSeparated] [Y.IsSeparated]
    {S : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S} (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver sX sY] (g : Y ⤏ X) [g.IsDominant] (h : f.comp g = RationalMap.id X)
    (h' : g.comp f = RationalMap.id Y) :
    ∃ e : X.PartialIso Y, e.IsOver sX sY ∧ e.toRationalMap = f := by
  obtain ⟨F, hF, rfl⟩ := f.exists_partialMap_over sX sY
  have : IsDominant F.hom := F.isDominant_toRationalMap_iff.1 ‹_›
  have hFg : (F.comp g.representative).toRationalMap = RationalMap.id X := by
    rw [← RationalMap.toRationalMap_comp, g.toRationalMap_representative, h]
  have hgF : (g.representative.comp F).toRationalMap = RationalMap.id Y :=
    (RationalMap.comp_def g F).symm.trans h'
  exact ⟨PartialMap.partialIsoOfComp hFg hgF, PartialMap.isOver_partialIsoOfComp hFg hgF, by simp⟩

end AlgebraicGeometry.Scheme
