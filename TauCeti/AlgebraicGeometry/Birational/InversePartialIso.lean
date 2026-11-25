/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Birational.Composition
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

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
(`AlgebraicGeometry.Scheme.RationalMap.exists_partialIso_toRationalMap_eq`): `f` is birational
in the sense of the DynamicalDegreesOfRationalMaps roadmap.

## Main definitions

* `AlgebraicGeometry.Scheme.PartialMap.partialIsoOfComp`: the partial isomorphism of partial maps
  `F` and `G` whose composites are the identity as rational maps.

## Main results

* `AlgebraicGeometry.Scheme.PartialMap.comp_hom_eq_ι`: if `F.comp G` is the identity as a rational
  map, its underlying morphism is the inclusion of its domain.
* `AlgebraicGeometry.Scheme.PartialMap.toRationalMap_partialIsoOfComp`: the rational map of
  `partialIsoOfComp F G` is that of `F`.
* `AlgebraicGeometry.Scheme.RationalMap.exists_partialIso_toRationalMap_eq`: a dominant rational
  map with a dominant two-sided inverse is the rational map of a partial isomorphism.
* `AlgebraicGeometry.Scheme.RationalMap.exists_partialIso_isOver_toRationalMap_eq`: the same over
  a separated base `S`, with the partial isomorphism over `S`.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

namespace PartialMap

/-- **A composite that is the identity rational map is the inclusion of its domain.** If
`F.comp G` is the identity as a rational map, its underlying morphism is the inclusion of its
domain: morphisms from a reduced scheme to a separated scheme agreeing on a dense open agree. -/
theorem comp_hom_eq_ι [X.IsSeparated] (F : X.PartialMap Y) [IsDominant F.hom] (G : Y.PartialMap X)
    (h : (F.comp G).toRationalMap = RationalMap.id X) :
    (F.comp G).hom = (F.comp G).domain.ι := by
  rw [RationalMap.id, toRationalMap_eq_iff] at h
  simpa using (equiv_toPartialMap_iff_of_isSeparated (terminal.from X) (terminal.from X)
    (g := 𝟙 X) (by simp)).1 h

/-- The restriction of `F` to the domain of `F.comp G`, as a morphism into the domain of `G`. -/
noncomputable def compLeft (F : X.PartialMap Y) [IsDominant F.hom] (G : Y.PartialMap X) :
    (F.comp G).domain.toScheme ⟶ G.domain.toScheme :=
  (F.domain.ι.isoImage (F.hom ⁻¹ᵁ G.domain)).inv ≫ F.hom ∣_ G.domain

/-- `compLeft F G` followed by `G` is the composite `F.comp G`. -/
theorem compLeft_hom (F : X.PartialMap Y) [IsDominant F.hom] (G : Y.PartialMap X) :
    compLeft F G ≫ G.hom = (F.comp G).hom :=
  Category.assoc _ _ _

/-- The domain of `F.comp G` lies in the domain of `F`. -/
theorem comp_domain_le (F : X.PartialMap Y) [IsDominant F.hom] (G : Y.PartialMap X) :
    (F.comp G).domain ≤ F.domain :=
  F.domain.ι_image_le _

/-- `compLeft F G`, read in `Y`, is `F` on the domain of `F.comp G`. -/
theorem compLeft_ι (F : X.PartialMap Y) [IsDominant F.hom] (G : Y.PartialMap X) :
    compLeft F G ≫ G.domain.ι = X.homOfLE (comp_domain_le F G) ≫ F.hom := by
  refine (Category.assoc _ _ _).trans ?_
  simp only [morphismRestrict_ι]
  exact Opens.isoImage_ι_inv_ι_assoc _ _ _

variable {F : X.PartialMap Y} [IsDominant F.hom] {G : Y.PartialMap X} [IsDominant G.hom]

/-- If `F.comp G` is the identity rational map, `F` maps the domain of `F.comp G` into the domain
of `G.comp F`. -/
theorem range_compLeft_ι_subset [X.IsSeparated] (h : (F.comp G).toRationalMap = RationalMap.id X) :
    Set.range (compLeft F G ≫ G.domain.ι) ⊆ Set.range (G.comp F).domain.ι := by
  rintro _ ⟨x, rfl⟩
  rw [Opens.range_ι, comp_domain]
  refine ⟨compLeft F G x, ?_, rfl⟩
  change G.hom (compLeft F G x) ∈ F.domain
  have hx : G.hom (compLeft F G x) = (F.comp G).domain.ι x := by
    rw [← Scheme.Hom.comp_apply, compLeft_hom, comp_hom_eq_ι F G h]
  have hmem : (F.comp G).domain.ι x ∈ Set.range (F.comp G).domain.ι := ⟨x, rfl⟩
  rw [Opens.range_ι] at hmem
  rw [hx]
  exact comp_domain_le F G hmem

/-- The morphism from the domain of `F.comp G` to the domain of `G.comp F` given by `F`. -/
noncomputable def partialIsoHom [X.IsSeparated] (h : (F.comp G).toRationalMap = RationalMap.id X) :
    (F.comp G).domain.toScheme ⟶ (G.comp F).domain.toScheme :=
  IsOpenImmersion.lift (G.comp F).domain.ι (compLeft F G ≫ G.domain.ι)
    (range_compLeft_ι_subset h)

/-- `partialIsoHom h`, read in `Y`, is `F` on the domain of `F.comp G`. -/
theorem partialIsoHom_ι [X.IsSeparated] (h : (F.comp G).toRationalMap = RationalMap.id X) :
    partialIsoHom h ≫ (G.comp F).domain.ι = compLeft F G ≫ G.domain.ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- `partialIsoHom h`, read in the domain of `G`, is `compLeft F G`. -/
theorem partialIsoHom_homOfLE [X.IsSeparated] (h : (F.comp G).toRationalMap = RationalMap.id X) :
    partialIsoHom h ≫ Y.homOfLE (comp_domain_le G F) = compLeft F G := by
  rw [← cancel_mono G.domain.ι, Category.assoc, homOfLE_ι, partialIsoHom_ι]

/-- The restrictions of `F` and `G` are mutually inverse. -/
theorem partialIsoHom_partialIsoHom [X.IsSeparated] [Y.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X)
    (h' : (G.comp F).toRationalMap = RationalMap.id Y) :
    partialIsoHom h ≫ partialIsoHom h' = 𝟙 _ := by
  rw [← cancel_mono (F.comp G).domain.ι, Category.assoc, partialIsoHom_ι, compLeft_ι,
    ← Category.assoc, partialIsoHom_homOfLE, compLeft_hom, comp_hom_eq_ι F G h, Category.id_comp]

/-- **The partial isomorphism of mutually inverse partial maps.** If `F.comp G` and `G.comp F` are
the identity rational maps, `F` restricts to an isomorphism from the domain of `F.comp G` onto the
domain of `G.comp F`, with inverse the restriction of `G`. -/
@[expose] noncomputable def partialIsoOfComp [X.IsSeparated] [Y.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X)
    (h' : (G.comp F).toRationalMap = RationalMap.id Y) : X.PartialIso Y where
  source := (F.comp G).domain
  dense_source := (F.comp G).dense_domain
  target := (G.comp F).domain
  dense_target := (G.comp F).dense_domain
  iso :=
    { hom := partialIsoHom h
      inv := partialIsoHom h'
      hom_inv_id := partialIsoHom_partialIsoHom h h'
      inv_hom_id := partialIsoHom_partialIsoHom h' h }

/-- The morphism of the partial map of `partialIsoOfComp F G` is `F` on the domain of
`F.comp G`. -/
theorem toPartialMap_partialIsoOfComp_hom [X.IsSeparated] [Y.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X)
    (h' : (G.comp F).toRationalMap = RationalMap.id Y) :
    (partialIsoOfComp h h').toPartialMap.hom = X.homOfLE (comp_domain_le F G) ≫ F.hom :=
  (partialIsoHom_ι h).trans (compLeft_ι F G)

/-- The partial map of `partialIsoOfComp F G` is `F` restricted to the domain of `F.comp G`. -/
theorem toPartialMap_partialIsoOfComp [X.IsSeparated] [Y.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X)
    (h' : (G.comp F).toRationalMap = RationalMap.id Y) :
    (partialIsoOfComp h h').toPartialMap =
      F.restrict (F.comp G).domain (F.comp G).dense_domain (comp_domain_le F G) :=
  PartialMap.ext _ _ (by rfl) (by
    rw [toPartialMap_partialIsoOfComp_hom, restrict_hom]
    exact (X.homOfLE_homOfLE_assoc le_rfl _ _).symm)

/-- **The rational map of `partialIsoOfComp F G` is that of `F`.** -/
@[simp]
theorem toRationalMap_partialIsoOfComp [X.IsSeparated] [Y.IsSeparated]
    (h : (F.comp G).toRationalMap = RationalMap.id X)
    (h' : (G.comp F).toRationalMap = RationalMap.id Y) :
    (partialIsoOfComp h h').toRationalMap = F.toRationalMap := by
  rw [PartialIso.toRationalMap, toPartialMap_partialIsoOfComp, restrict_toRationalMap]

/-- **The partial isomorphism is over `S`** when `F` is: its morphism is `F` on the domain of
`F.comp G`. -/
theorem isOver_partialIsoOfComp [X.IsSeparated] [Y.IsSeparated] {S : Scheme.{u}} {sX : X ⟶ S}
    {sY : Y ⟶ S} [F.IsOver sX sY] (h : (F.comp G).toRationalMap = RationalMap.id X)
    (h' : (G.comp F).toRationalMap = RationalMap.id Y) :
    (partialIsoOfComp h h').IsOver sX sY := by
  have e := congrArg (· ≫ sY) (toPartialMap_partialIsoOfComp_hom h h')
  refine (Category.assoc _ _ _).symm.trans (e.trans ?_)
  exact (Category.assoc _ _ _).trans ((congrArg (X.homOfLE (comp_domain_le F G) ≫ ·)
    (F.over sX sY)).trans (X.homOfLE_ι_assoc _ _))

end PartialMap

/-- **A dominant rational map with a dominant two-sided inverse is the rational map of a partial
isomorphism.** If `f : X ⤏ Y` and `g : Y ⤏ X` are dominant rational maps of integral separated
schemes with `f.comp g = id` and `g.comp f = id`, some partial isomorphism of `X` with `Y` has
rational map `f`. -/
theorem RationalMap.exists_partialIso_toRationalMap_eq [X.IsSeparated] [Y.IsSeparated]
    (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ X)
    [g.IsDominant] (h : f.comp g = RationalMap.id X) (h' : g.comp f = RationalMap.id Y) :
    ∃ e : X.PartialIso Y, e.toRationalMap = f := by
  have hfg : (f.representative.comp g.representative).toRationalMap = RationalMap.id X := by
    rw [← RationalMap.comp_def, g.toRationalMap_representative, h]
  have hgf : (g.representative.comp f.representative).toRationalMap = RationalMap.id Y := by
    rw [← RationalMap.comp_def, f.toRationalMap_representative, h']
  exact ⟨PartialMap.partialIsoOfComp hfg hgf, by simp⟩

/-- **A dominant rational map over `S` with a dominant two-sided inverse is the rational map of a
partial isomorphism over `S`**, for a separated base `S`. -/
theorem RationalMap.exists_partialIso_isOver_toRationalMap_eq [X.IsSeparated] [Y.IsSeparated]
    {S : Scheme.{u}} [S.IsSeparated] {sX : X ⟶ S} {sY : Y ⟶ S} (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver sX sY] (g : Y ⤏ X) [g.IsDominant] (h : f.comp g = RationalMap.id X)
    (h' : g.comp f = RationalMap.id Y) :
    ∃ e : X.PartialIso Y, e.IsOver sX sY ∧ e.toRationalMap = f := by
  have hfg : (f.representative.comp g.representative).toRationalMap = RationalMap.id X := by
    rw [← RationalMap.comp_def, g.toRationalMap_representative, h]
  have hgf : (g.representative.comp f.representative).toRationalMap = RationalMap.id Y := by
    rw [← RationalMap.comp_def, f.toRationalMap_representative, h']
  have : f.representative.IsOver sX sY := PartialMap.isOver_toRationalMap_iff_of_isSeparated.1
    (by rw [f.toRationalMap_representative]; infer_instance)
  exact ⟨PartialMap.partialIsoOfComp hfg hgf, PartialMap.isOver_partialIsoOfComp hfg hgf, by simp⟩

end AlgebraicGeometry.Scheme
