/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import TauCeti.AlgebraicGeometry.GroupAction.InvariantOpen
public import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.UniversalProperty

/-!
# Quotients of schemes by finite groups with an invariant affine open cover

Let a finite group `G` act on a scheme `X` by automorphisms, `σ : G →* Aut X`. This file
constructs the quotient `X/G` (`TauCeti.InvariantQuotient.quotient σ`) by gluing the affine
invariant quotients `Spec Γ(X, U)ᴳ` of the invariant affine opens `U` of `X`, and shows that, when
the invariant affine opens cover `X`, the glued projection `X ⟶ X/G` is a categorical quotient in
the category of all schemes, integral and surjective, and over the chart of each invariant affine
open `U` it is the affine invariant quotient `Spec Γ(X, U) ⟶ Spec Γ(X, U)ᴳ`.

For invariant affine opens `V ≤ U`, restriction of invariant sections induces a morphism
`Spec Γ(X, V)ᴳ ⟶ Spec Γ(X, U)ᴳ`; these form the diagram `TauCeti.InvariantQuotient.chartDiagram σ`.
Its transition maps are open immersions. Since the affine projection `Spec Γ(X, U) ⟶ Spec Γ(X, U)ᴳ`
is a topological quotient map whose fibres are the orbits, every point of an invariant open inside
`U` has a neighbourhood `X.basicOpen r` inside it with `r` an invariant section over `U`
(`TauCeti.InvariantQuotient.exists_basicOpen_le`). Invariants commute with localization at such
an `r` (`TauCeti.InvariantQuotient.isLocalization_resFixedPoints`), so near every point the
transition map is the localization `Spec (Γ(X, U)ᴳ)_r ⟶ Spec Γ(X, U)ᴳ`; it is injective because
points of both sides are orbits. The same neighbourhoods make the diagram locally directed, so its
colimit is the gluing of the charts (Mathlib's `AlgebraicGeometry.Scheme.IsLocallyDirected`). No
separatedness is assumed: the intersection of two invariant affine opens need not be affine, and is
only covered by invariant basic opens.

The projection is glued from the affine projections along the locally directed cover of `X` by the
spectra of its invariant affine opens. A `G`-invariant morphism `f : X ⟶ Z` descends on each chart
by the universal property of the affine invariant quotient,
`TauCeti.AffineInvariantQuotient.existsUnique_desc_of_finite`, and these descents form a cocone on
the chart diagram.

The covering hypothesis `TauCeti.InvariantQuotient.HasInvariantAffineCover σ` holds when `X` is
affine and when `G` acts over a base along an affine morphism; in the latter case the quotient is
also constructed relatively in `TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Relative.Basic`.

## Main definitions

* `TauCeti.InvariantQuotient.InvariantAffineOpens σ`: the invariant affine opens of `X`, ordered
  by inclusion.
* `TauCeti.InvariantQuotient.chartDiagram σ`: the diagram of affine invariant quotients.
* `TauCeti.InvariantQuotient.quotient σ`: the quotient `X/G`, the colimit of the chart diagram, with
  the open immersions `TauCeti.InvariantQuotient.chartι σ U : Spec Γ(X, U)ᴳ ⟶ X/G`.
* `TauCeti.InvariantQuotient.HasInvariantAffineCover σ`: the invariant affine opens cover `X`.
* `TauCeti.InvariantQuotient.projection σ hσ`: the quotient projection `X ⟶ X/G`.
* `TauCeti.InvariantQuotient.desc σ f hf`: the morphism `X/G ⟶ Z` induced by a `G`-invariant
  morphism `f : X ⟶ Z`.

## Main results

* `TauCeti.InvariantQuotient.isOpenImmersion_chartDiagram_map`: the transition maps of the chart
  diagram are open immersions.
* `TauCeti.InvariantQuotient.isPullback_projection_fromSpec`: over the chart of an invariant affine
  open `U`, the projection is the affine invariant quotient projection of `Γ(X, U)`.
* `TauCeti.InvariantQuotient.projection_iff`: a property local on the target holds for the
  projection exactly when it holds for all affine invariant quotient projections.
* The projection is `G`-invariant (`TauCeti.InvariantQuotient.asIso_hom_projection`), surjective,
  integral, and an epimorphism.
* `TauCeti.InvariantQuotient.existsUnique_projection_comp_eq`: the universal property of the
  quotient for arbitrary target schemes.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental (SGA 1)*, Exposé V, Proposition 1.8.
* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §1.
* D. Mumford, *Abelian Varieties*, §7, Theorem 1.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace

namespace TauCeti.InvariantQuotient

universe u v

variable {X : Scheme.{u}} {G : Type v} [Group G] {σ : G →* Aut X}

open AffineInvariantQuotient in
/-- On the chart `Spec Γ(X, U)` of an invariant affine open `U`, the action of `g` on the spectrum
of the sections is the automorphism `σ g`. -/
@[reassoc]
lemma specAction_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (hσ : U.IsInvariant σ) (g : G) :
    letI := Scheme.sectionsMulSemiringAction σ hσ
    (specAction Γ(X, U) G g).asIso.hom ≫ hU.fromSpec = hU.fromSpec ≫ (σ g).asIso.hom := by
  let := Scheme.sectionsMulSemiringAction σ hσ
  rw [specAction_asIso_hom, specComap_def, ← IsAffineOpen.SpecMap_appLE_fromSpec _ hU hU
    (hσ.preimage_eq g).ge]
  congr 2
  ext a
  exact (Scheme.appLE_apply_eq_inv_smul hσ g a).symm

open AffineInvariantQuotient in
/-- On the chart `Spec Γ(X, U)` of an invariant affine open `U`, the contravariant spectrum map of
`g` is the automorphism `σ g⁻¹`. -/
@[reassoc]
lemma specComap_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (hσ : U.IsInvariant σ) (g : G) :
    letI := Scheme.sectionsMulSemiringAction σ hσ
    specComap Γ(X, U) G g ≫ hU.fromSpec = hU.fromSpec ≫ (σ g⁻¹).asIso.hom := by
  let := Scheme.sectionsMulSemiringAction σ hσ
  rw [← specAction_fromSpec hU hσ, specAction_asIso_hom, inv_inv]

variable (σ) in
/-- The invariant affine opens of `X`, ordered by inclusion. The quotient of `X` is glued from the
affine invariant quotients of the sections over them. -/
abbrev InvariantAffineOpens : Type u :=
  {U : X.Opens // IsAffineOpen U ∧ U.IsInvariant σ}

section Charts

open AffineInvariantQuotient

section Points

variable [Finite G]

/-- Two points of the chart `Spec Γ(X, U)` of an invariant affine open have the same image in the
affine invariant quotient exactly when their images in `X` lie in the same `G`-orbit. -/
lemma affineProjection_eq_iff_exists_fromSpec_eq (U : InvariantAffineOpens σ)
    (p q : Spec Γ(X, U.1)) :
    letI := Scheme.sectionsMulSemiringAction σ U.2.2
    projection Γ(X, U.1) G p = projection Γ(X, U.1) G q ↔
      ∃ g : G, U.2.1.fromSpec q = (σ g).asIso.hom (U.2.1.fromSpec p) := by
  let := Scheme.sectionsMulSemiringAction σ U.2.2
  refine (projection_eq_iff_exists_smul Γ(X, U.1) G p q).trans (exists_congr fun g ↦ ?_)
  rw [← Scheme.Hom.comp_apply, ← specAction_fromSpec U.2.1 U.2.2, Scheme.Hom.comp_apply]
  exact ⟨fun h ↦ by rw [h]; exact congrArg _ (specAction_apply _ _ g p).symm,
    fun h ↦ (U.2.1.fromSpec.isOpenEmbedding.injective h).trans (specAction_apply _ _ g p)⟩

omit [Finite G] in
/-- A point of the chart `Spec Γ(X, U)` lies over the basic open `D(r)` of an invariant section `r`
in the affine invariant quotient exactly when its image in `X` lies in `X.basicOpen r`. -/
lemma affineProjection_mem_basicOpen_iff (U : InvariantAffineOpens σ)
    (r : letI := Scheme.sectionsMulSemiringAction σ U.2.2; FixedPoints.subring Γ(X, U.1) G)
    (p : Spec Γ(X, U.1)) :
    letI := Scheme.sectionsMulSemiringAction σ U.2.2
    projection Γ(X, U.1) G p ∈ PrimeSpectrum.basicOpen r ↔
      U.2.1.fromSpec p ∈ X.basicOpen (r : Γ(X, U.1)) := by
  let := Scheme.sectionsMulSemiringAction σ U.2.2
  rw [← Scheme.Hom.mem_preimage, IsAffineOpen.fromSpec_preimage_basicOpen]
  -- `projection_base_apply` is stated for points of `PrimeSpectrum`, not of the scheme `Spec`.
  erw [projection_base_apply]
  -- Both sides say that `r` does not lie in the prime `p`: membership in a basic open is
  -- non-membership in the prime ideal, and the ideal of `PrimeSpectrum.comap` is `Ideal.comap`.
  exact not_congr Ideal.mem_comap

/-- **Invariant basic opens form a basis of the invariant opens.** A point `x` of an invariant
affine open `U` lying in an invariant open `W` has a neighbourhood `X.basicOpen r ≤ W` with `r` an
invariant section over `U`. -/
theorem exists_basicOpen_le (U : InvariantAffineOpens σ) {W : X.Opens} (hW : W.IsInvariant σ)
    {x : X} (hxU : x ∈ U.1) (hxW : x ∈ W) :
    letI := Scheme.sectionsMulSemiringAction σ U.2.2
    ∃ r : FixedPoints.subring Γ(X, U.1) G,
      x ∈ X.basicOpen (r : Γ(X, U.1)) ∧ X.basicOpen (r : Γ(X, U.1)) ≤ W := by
  let := Scheme.sectionsMulSemiringAction σ U.2.2
  set π := projection Γ(X, U.1) G
  set p := U.2.1.fromSpec
  -- The image `S` of the preimage of `W` is open, as the projection is a quotient map.
  set S : Set (quotient Γ(X, U.1) G) := π '' (p ⁻¹' W)
  have hsat (y : Spec Γ(X, U.1)) (hy : π y ∈ S) : p y ∈ W := by
    obtain ⟨w, hw, hwy⟩ := hy
    obtain ⟨g, hg⟩ := (affineProjection_eq_iff_exists_fromSpec_eq U w y).mp hwy
    rw [hg, hW.apply_mem_iff]
    exact hw
  have hS : IsOpen S := by
    rw [← (isQuotientMap_projection Γ(X, U.1) G).isOpen_preimage]
    convert (W.isOpen.preimage p.continuous) using 1
    exact Set.Subset.antisymm (fun y hy ↦ hsat y hy) (Set.subset_preimage_image _ _)
  obtain ⟨x, rfl⟩ : x ∈ Set.range p := by rwa [U.2.1.range_fromSpec]
  obtain ⟨_, ⟨r, rfl⟩, hxr, hrS⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (Set.mem_image_of_mem π hxW) hS
  have hmem (y : Spec Γ(X, U.1)) := affineProjection_mem_basicOpen_iff U r y
  refine ⟨r, (hmem x).mp hxr, fun y hy ↦ ?_⟩
  obtain ⟨y, rfl⟩ : y ∈ Set.range p := by
    rw [U.2.1.range_fromSpec]
    exact X.basicOpen_le _ hy
  exact hsat y (hrS ((hmem y).mpr hy))

end Points

section Diagram

/-- Restriction of invariant sections along an inclusion `V ≤ U` of invariant opens. -/
noncomputable def resFixedPoints {U V : X.Opens} (hU : U.IsInvariant σ) (hV : V.IsInvariant σ)
    (h : V ≤ U) :
    letI := Scheme.sectionsMulSemiringAction σ hU
    letI := Scheme.sectionsMulSemiringAction σ hV
    FixedPoints.subring Γ(X, U) G →+* FixedPoints.subring Γ(X, V) G :=
  letI := Scheme.sectionsMulSemiringAction σ hU
  letI := Scheme.sectionsMulSemiringAction σ hV
  ((X.presheaf.map (homOfLE h).op).hom.comp (FixedPoints.subring Γ(X, U) G).subtype).codRestrict _
    fun a g ↦ by
      rw [RingHom.comp_apply, Subring.coe_subtype, ← Scheme.presheaf_map_smul hU hV h, a.2 g]

/-- The restriction of an invariant section is its restriction as a section. -/
@[simp]
lemma coe_resFixedPoints {U V : X.Opens} (hU : U.IsInvariant σ) (hV : V.IsInvariant σ)
    (h : V ≤ U) (a : letI := Scheme.sectionsMulSemiringAction σ hU; FixedPoints.subring Γ(X, U) G) :
    letI := Scheme.sectionsMulSemiringAction σ hV
    (resFixedPoints hU hV h a : Γ(X, V)) = (X.presheaf.map (homOfLE h).op).hom a :=
  (rfl)

variable (σ) in
/-- The diagram of affine invariant quotients `Spec Γ(X, U)ᴳ` over the invariant affine opens
`U` of `X`, with the transition maps induced by restriction of invariant sections. It is exposed
and reducible so that its objects are, by definition and for instance search, the affine invariant
quotients, and the affine API applies to them directly. -/
@[expose, reducible] noncomputable def chartDiagram : InvariantAffineOpens σ ⥤ Scheme.{u} where
  obj U := letI := Scheme.sectionsMulSemiringAction σ U.2.2; quotient Γ(X, U.1) G
  map {V U} f := Spec.map (CommRingCat.ofHom (resFixedPoints U.2.2 V.2.2 (leOfHom f)))
  map_id U := by
    rw [← Spec.map_id]
    congr 1
    ext a
    exact congr(($(X.presheaf.map_id (op U.1))).hom a.1)
  map_comp {W V U} f g := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact congr(($(X.presheaf.map_comp (homOfLE (leOfHom g : V.1 ≤ U.1)).op
      (homOfLE (leOfHom f : W.1 ≤ V.1)).op)).hom a.1)

/-- The transition maps of the chart diagram are the spectra of restriction of invariant
sections. -/
lemma chartDiagram_map {U V : InvariantAffineOpens σ} (f : V ⟶ U) :
    (chartDiagram σ).map f =
      Spec.map (CommRingCat.ofHom (resFixedPoints U.2.2 V.2.2 (leOfHom f))) :=
  (rfl)

/-- Restriction of sections commutes with the projections to the affine invariant quotients. -/
@[reassoc]
lemma specMap_map_projection {U V : InvariantAffineOpens σ} (f : V ⟶ U) :
    letI := Scheme.sectionsMulSemiringAction σ U.2.2
    letI := Scheme.sectionsMulSemiringAction σ V.2.2
    Spec.map (X.presheaf.map (homOfLE (leOfHom f)).op) ≫ projection Γ(X, U.1) G =
      projection Γ(X, V.1) G ≫ (chartDiagram σ).map f := by
  let := Scheme.sectionsMulSemiringAction σ U.2.2
  let := Scheme.sectionsMulSemiringAction σ V.2.2
  rw [projection_def, projection_def, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map
    (CommRingCat.hom_ext (RingHom.ext fun a ↦ (coe_resFixedPoints U.2.2 V.2.2 (leOfHom f) a).symm))

/-- The basic open of an invariant section over an invariant affine open, as an invariant affine
open. -/
noncomputable def InvariantAffineOpens.basicOpen (U : InvariantAffineOpens σ)
    (r : letI := Scheme.sectionsMulSemiringAction σ U.2.2; FixedPoints.subring Γ(X, U.1) G) :
    InvariantAffineOpens σ :=
  ⟨X.basicOpen (r : Γ(X, U.1)), U.2.1.basicOpen _, U.2.2.basicOpen _ r.2⟩

/-- The underlying open of `U.basicOpen r` is the basic open of `r`. -/
@[simp]
lemma InvariantAffineOpens.coe_basicOpen (U : InvariantAffineOpens σ)
    (r : letI := Scheme.sectionsMulSemiringAction σ U.2.2; FixedPoints.subring Γ(X, U.1) G) :
    (U.basicOpen r).1 = X.basicOpen (r : Γ(X, U.1)) :=
  (rfl)

/-- The basic open of an invariant section over `U` lies in `U`. -/
lemma InvariantAffineOpens.basicOpen_le (U : InvariantAffineOpens σ)
    (r : letI := Scheme.sectionsMulSemiringAction σ U.2.2; FixedPoints.subring Γ(X, U.1) G) :
    U.basicOpen r ≤ U :=
  X.basicOpen_le _

section BasicOpen

variable [Finite G]

/-- **Invariants commute with localization at an invariant section.** Over the basic open `V` of an
invariant section `r` over an affine open `U`, the invariant sections are the localization away from
`r` of those over `U`. -/
theorem isLocalization_resFixedPoints {U V : X.Opens} (hU : IsAffineOpen U)
    (hUσ : U.IsInvariant σ) (hVσ : V.IsInvariant σ) (h : V ≤ U)
    (r : letI := Scheme.sectionsMulSemiringAction σ hUσ; FixedPoints.subring Γ(X, U) G)
    (hV : V = X.basicOpen (r : Γ(X, U))) :
    letI := Scheme.sectionsMulSemiringAction σ hUσ
    letI := Scheme.sectionsMulSemiringAction σ hVσ
    letI := (resFixedPoints hUσ hVσ h).toAlgebra
    IsLocalization.Away r (FixedPoints.subring Γ(X, V) G) := by
  let := Scheme.sectionsMulSemiringAction σ hUσ
  let := Scheme.sectionsMulSemiringAction σ hVσ
  let := (resFixedPoints hUσ hVσ h).toAlgebra
  let := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, U) (.powers r)) Γ(X, V) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    exact hU.isLocalization_of_eq_basicOpen _ (homOfLE h) hV
  -- The images of the invariant sections are the sections fixed by every `g`.
  have hfix {W : X.Opens} (hW : W.IsInvariant σ) (a : Γ(X, W)) :
      letI := Scheme.sectionsMulSemiringAction σ hW
      a ∈ Set.range (algebraMap (FixedPoints.subring Γ(X, W) G) Γ(X, W)) ↔
        ∀ g : G, MulSemiringAction.toRingHom G Γ(X, W) g a = a :=
    ⟨fun ⟨b, hb⟩ ↦ hb ▸ b.2, fun ha ↦ ⟨⟨a, ha⟩, rfl⟩⟩
  exact TauCeti.FixedPoints.isLocalization_of_mem_range_iff _ (MulSemiringAction.toRingHom G _)
    (MulSemiringAction.toRingHom G _) (fun g a ↦ (Scheme.presheaf_map_smul hUσ hVσ h g a).symm)
    Subtype.val_injective (hfix hUσ) Subtype.val_injective (hfix hVσ) fun _ ↦ rfl

/-- The transition map of the chart diagram along the inclusion of the basic open of an invariant
section is an open immersion. -/
theorem isOpenImmersion_chartDiagram_map_of_eq_basicOpen {U V : InvariantAffineOpens σ}
    (f : V ⟶ U)
    (r : letI := Scheme.sectionsMulSemiringAction σ U.2.2; FixedPoints.subring Γ(X, U.1) G)
    (hV : V.1 = X.basicOpen (r : Γ(X, U.1))) :
    IsOpenImmersion ((chartDiagram σ).map f) := by
  let := (resFixedPoints U.2.2 V.2.2 (leOfHom f)).toAlgebra
  have := isLocalization_resFixedPoints U.2.1 U.2.2 V.2.2 (leOfHom f) r hV
  exact IsOpenImmersion.of_isLocalization r

/-- The image of the transition map along the inclusion of the basic open of an invariant section
`r` is the basic open of `r` in the affine invariant quotient. -/
theorem range_chartDiagram_map_of_eq_basicOpen {U V : InvariantAffineOpens σ} (f : V ⟶ U)
    (r : letI := Scheme.sectionsMulSemiringAction σ U.2.2; FixedPoints.subring Γ(X, U.1) G)
    (hV : V.1 = X.basicOpen (r : Γ(X, U.1))) :
    letI := Scheme.sectionsMulSemiringAction σ U.2.2
    Set.range ((chartDiagram σ).map f) =
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum (FixedPoints.subring Γ(X, U.1) G))) := by
  let := (resFixedPoints U.2.2 V.2.2 (leOfHom f)).toAlgebra
  have := isLocalization_resFixedPoints U.2.1 U.2.2 V.2.2 (leOfHom f) r hV
  exact PrimeSpectrum.localization_away_comap_range _ r

end BasicOpen

/-- The transition maps of the chart diagram send projections of points to projections of their
images under restriction. -/
lemma chartDiagram_map_projection_apply {U V : InvariantAffineOpens σ} (f : V ⟶ U)
    (p : Spec Γ(X, V.1)) :
    letI := Scheme.sectionsMulSemiringAction σ U.2.2
    letI := Scheme.sectionsMulSemiringAction σ V.2.2
    (chartDiagram σ).map f (projection Γ(X, V.1) G p) =
      projection Γ(X, U.1) G (Spec.map (X.presheaf.map (homOfLE (leOfHom f)).op) p) := by
  exact congr($(specMap_map_projection (σ := σ) f) p).symm

variable [Finite G]

/-- Two points of charts `Spec Γ(X, T₁)` and `Spec Γ(X, T₂)` have the same image in the affine
invariant quotient of a larger invariant affine open exactly when their images in `X` lie in the
same `G`-orbit. -/
lemma chartDiagram_map_affineProjection_eq_iff {T₁ T₂ V : InvariantAffineOpens σ} (i : T₁ ⟶ V)
    (j : T₂ ⟶ V) (p : Spec Γ(X, T₁.1)) (q : Spec Γ(X, T₂.1)) :
    letI := Scheme.sectionsMulSemiringAction σ T₁.2.2
    letI := Scheme.sectionsMulSemiringAction σ T₂.2.2
    (chartDiagram σ).map i (projection Γ(X, T₁.1) G p) =
        (chartDiagram σ).map j (projection Γ(X, T₂.1) G q) ↔
      ∃ g : G, T₂.2.1.fromSpec q = (σ g).asIso.hom (T₁.2.1.fromSpec p) := by
  rw [chartDiagram_map_projection_apply, chartDiagram_map_projection_apply,
    affineProjection_eq_iff_exists_fromSpec_eq, V.2.1.map_fromSpec_apply T₂.2.1,
    V.2.1.map_fromSpec_apply T₁.2.1]

/-- The transition maps of the chart diagram are injective on points: the points of the affine
invariant quotients are the orbits in the invariant affine opens. -/
lemma chartDiagram_map_injective {U V : InvariantAffineOpens σ} (f : V ⟶ U) :
    Function.Injective ((chartDiagram σ).map f) := by
  let := Scheme.sectionsMulSemiringAction σ V.2.2
  intro y₁ y₂ hy
  obtain ⟨p₁, rfl⟩ := Surjective.surj (f := projection Γ(X, V.1) G) y₁
  obtain ⟨p₂, rfl⟩ := Surjective.surj (f := projection Γ(X, V.1) G) y₂
  exact (affineProjection_eq_iff_exists_fromSpec_eq V p₁ p₂).mpr
    ((chartDiagram_map_affineProjection_eq_iff f f p₁ p₂).mp hy)

/-- The transition maps of the chart diagram are open immersions. Near a point of `Spec Γ(X, V)ᴳ`,
the inclusion `V ≤ U` restricts to the inclusion of an invariant basic open of `U` lying in `V`,
whose transition map is a localization. -/
instance isOpenImmersion_chartDiagram_map {U V : InvariantAffineOpens σ} (f : V ⟶ U) :
    IsOpenImmersion ((chartDiagram σ).map f) := by
  let := Scheme.sectionsMulSemiringAction σ U.2.2
  let := Scheme.sectionsMulSemiringAction σ V.2.2
  refine IsOpenImmersion.of_forall_source_exists _ (chartDiagram_map_injective f) fun y ↦ ?_
  obtain ⟨p, rfl⟩ := Surjective.surj (f := projection Γ(X, V.1) G) y
  have hpV : V.2.1.fromSpec p ∈ V.1 := V.2.1.range_fromSpec.le ⟨p, rfl⟩
  obtain ⟨r, hpr, hrV⟩ := exists_basicOpen_le U V.2.2 (leOfHom f hpV) hpV
  let fT : U.basicOpen r ⟶ V := homOfLE hrV
  have hT : (U.basicOpen r).1 =
      X.basicOpen (resFixedPoints U.2.2 V.2.2 (leOfHom f) r : Γ(X, V.1)) := by
    rw [coe_resFixedPoints, Scheme.basicOpen_res, InvariantAffineOpens.coe_basicOpen,
      inf_eq_right.mpr hrV]
  refine ⟨_, (chartDiagram σ).map fT, isOpenImmersion_chartDiagram_map_of_eq_basicOpen fT _ hT,
    ?_, ?_⟩
  · -- Membership in `Scheme.Hom.opensRange` is by definition membership in the set-theoretic
    -- range, which `range_chartDiagram_map_of_eq_basicOpen` computes.
    change _ ∈ Set.range _
    rw [range_chartDiagram_map_of_eq_basicOpen fT _ hT]
    exact (affineProjection_mem_basicOpen_iff V _ p).mpr (hT ▸ hpr)
  · rw [← Functor.map_comp]
    exact isOpenImmersion_chartDiagram_map_of_eq_basicOpen _ r rfl

/-- The chart diagram is locally directed: two charts meeting in a chart meet in a third one. -/
instance : (chartDiagram σ ⋙ Scheme.forget).IsLocallyDirected where
  cond {T₁ T₂ V} f₁ f₂ y₁ y₂ hy := by
    let := Scheme.sectionsMulSemiringAction σ T₁.2.2
    let := Scheme.sectionsMulSemiringAction σ T₂.2.2
    obtain ⟨p₁, rfl⟩ := Surjective.surj (f := projection Γ(X, T₁.1) G) y₁
    obtain ⟨p₂, rfl⟩ := Surjective.surj (f := projection Γ(X, T₂.1) G) y₂
    -- The hypothesis is an equation in the underlying types of the charts.
    have hy : (chartDiagram σ).map f₁ (projection Γ(X, T₁.1) G p₁) =
        (chartDiagram σ).map f₂ (projection Γ(X, T₂.1) G p₂) := hy
    obtain ⟨g, hg'⟩ := (chartDiagram_map_affineProjection_eq_iff f₁ f₂ p₁ p₂).mp hy
    -- The image `x` of `p₁` in `X` lies in both `T₁` and `T₂`.
    set x := T₁.2.1.fromSpec p₁
    have hx₁ : x ∈ T₁.1 := T₁.2.1.range_fromSpec.le ⟨p₁, rfl⟩
    have hx₂ : x ∈ T₂.1 :=
      (T₂.2.2.apply_mem_iff g).mp (hg' ▸ T₂.2.1.range_fromSpec.le ⟨p₂, rfl⟩)
    obtain ⟨r, hxr, hrT⟩ := exists_basicOpen_le V (T₁.2.2.inf T₂.2.2)
      (leOfHom f₁ hx₁) ⟨hx₁, hx₂⟩
    let T := V.basicOpen r
    obtain ⟨p, hp⟩ : x ∈ Set.range T.2.1.fromSpec := T.2.1.range_fromSpec.ge hxr
    let := Scheme.sectionsMulSemiringAction σ T.2.2
    let i₁ : T ⟶ T₁ := homOfLE (hrT.trans inf_le_left)
    let i₂ : T ⟶ T₂ := homOfLE (hrT.trans inf_le_right)
    refine ⟨T, i₁, i₂, projection Γ(X, T.1) G p, ?_, ?_⟩
    · refine (chartDiagram_map_projection_apply i₁ p).trans (congrArg _ ?_)
      exact T₁.2.1.fromSpec.isOpenEmbedding.injective
        ((T₁.2.1.map_fromSpec_apply T.2.1 _ p).trans hp)
    · refine (chartDiagram_map_projection_apply i₂ p).trans
        ((affineProjection_eq_iff_exists_fromSpec_eq T₂ _ _).mpr
          ⟨g, hg'.trans (congrArg _ ((T₂.2.1.map_fromSpec_apply T.2.1 _ p).trans hp).symm)⟩)

end Diagram

end Charts

section Quotient

variable [Finite G]

variable (σ) in
/-- The **quotient of `X` by `G`**: the gluing of the affine invariant quotients `Spec Γ(X, U)ᴳ` of
the invariant affine opens `U` of `X` along the open immersions induced by restriction. -/
noncomputable def quotient : Scheme.{u} :=
  colimit (chartDiagram σ)

variable (σ) in
/-- The chart `Spec Γ(X, U)ᴳ ⟶ X/G` of the quotient over an invariant affine open `U`. -/
noncomputable def chartι (U : InvariantAffineOpens σ) : (chartDiagram σ).obj U ⟶ quotient σ :=
  colimit.ι (chartDiagram σ) U

/-- The charts of the quotient are open immersions. -/
instance (U : InvariantAffineOpens σ) : IsOpenImmersion (chartι σ U) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (chartDiagram σ) U))

/-- The charts of the quotient are compatible with the transition maps. -/
@[simp, reassoc]
lemma chartDiagram_map_chartι {U V : InvariantAffineOpens σ} (f : V ⟶ U) :
    (chartDiagram σ).map f ≫ chartι σ U = chartι σ V :=
  colimit.w (chartDiagram σ) f

/-- Two points of charts of the quotient agree exactly when they come from a common point of a
smaller chart. -/
lemma chartι_eq_chartι_iff {U V : InvariantAffineOpens σ} {y : (chartDiagram σ).obj U}
    {z : (chartDiagram σ).obj V} :
    chartι σ U y = chartι σ V z ↔ ∃ (T : InvariantAffineOpens σ) (i : T ⟶ U) (j : T ⟶ V)
      (t : (chartDiagram σ).obj T), (chartDiagram σ).map i t = y ∧ (chartDiagram σ).map j t = z :=
  Scheme.IsLocallyDirected.ι_eq_ι_iff (chartDiagram σ)

variable (σ) in
/-- The invariant affine opens of `X` cover `X`. This is the hypothesis under which `X` maps to its
quotient `quotient σ`; it holds when `X` is affine (`hasInvariantAffineCover_of_isAffine`) and when
`G` acts by automorphisms over a base along an affine morphism
(`hasInvariantAffineCover_of_isAffineHom`). -/
def HasInvariantAffineCover : Prop :=
  ∀ x : X, ∃ U : InvariantAffineOpens σ, x ∈ U.1

omit [Finite G] in
/-- An affine scheme has an invariant affine cover, by the open `⊤`. -/
lemma hasInvariantAffineCover_of_isAffine [IsAffine X] : HasInvariantAffineCover σ :=
  fun _ ↦ ⟨⟨⊤, isAffineOpen_top X, .top σ⟩, trivial⟩

omit [Finite G] in
/-- If `G` acts by automorphisms over a base `S` and the structure morphism is affine, then the
preimages of the affine opens of `S` form an invariant affine cover. -/
lemma hasInvariantAffineCover_of_isAffineHom {S : Scheme.{u}} (π : X ⟶ S) [IsAffineHom π]
    (hπ : ∀ g, (σ g).asIso.hom ≫ π = π) : HasInvariantAffineCover σ := fun x ↦ by
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (π x))
  refine ⟨⟨π ⁻¹ᵁ V, hV.preimage π, Scheme.Opens.isInvariant_iff.mpr fun g ↦ ?_⟩, hx⟩
  rw [← Scheme.Hom.comp_preimage, hπ g]

variable (σ) in
/-- The open cover of `X` by the spectra `Spec Γ(X, U)` of its invariant affine opens. -/
@[expose, simps I₀ X f]
noncomputable def invariantAffineCover (hσ : HasInvariantAffineCover σ) : X.OpenCover where
  I₀ := InvariantAffineOpens σ
  X U := Spec Γ(X, U.1)
  f U := U.2.1.fromSpec
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨U, hU⟩ := hσ x
    exact ⟨U, U.2.1.range_fromSpec.ge hU⟩

/-- A point of the intersection of the charts of two invariant affine opens `U` and `V` comes from
the chart of an invariant affine open contained in both. -/
private lemma exists_pullback_lift_eq (U V : InvariantAffineOpens σ)
    (x : (pullback U.2.1.fromSpec V.2.1.fromSpec : Scheme.{u})) :
    ∃ (T : InvariantAffineOpens σ) (i : T.1 ≤ U.1) (j : T.1 ≤ V.1) (y : Spec Γ(X, T.1)),
      pullback.lift (Spec.map (X.presheaf.map (homOfLE i).op))
        (Spec.map (X.presheaf.map (homOfLE j).op))
        ((IsAffineOpen.map_fromSpec _ T.2.1 _).trans (IsAffineOpen.map_fromSpec _ T.2.1 _).symm) y =
          x := by
  -- The image `z` of `x` in `X` lies in an invariant basic open `T` of `U` contained in `V`.
  set z := (pullback.fst _ _ ≫ U.2.1.fromSpec) x
  have hzU : z ∈ U.1 := U.2.1.range_fromSpec.le ⟨_, rfl⟩
  have hzV : z ∈ V.1 := V.2.1.range_fromSpec.le
    ⟨pullback.snd U.2.1.fromSpec V.2.1.fromSpec x, by
      rw [← Scheme.Hom.comp_apply, ← pullback.condition]⟩
  obtain ⟨r, hzr, hrV⟩ := exists_basicOpen_le U V.2.2 hzU hzV
  let T := U.basicOpen r
  obtain ⟨y, hy⟩ : z ∈ Set.range T.2.1.fromSpec := T.2.1.range_fromSpec.ge hzr
  refine ⟨T, U.basicOpen_le r, hrV, y, ?_⟩
  apply (pullback.fst _ _ ≫ U.2.1.fromSpec).isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc, Scheme.Hom.comp_apply,
    U.2.1.map_fromSpec_apply T.2.1, hy]

/-- The indices of the cover by invariant affine opens are ordered by inclusion. -/
instance (hσ : HasInvariantAffineCover σ) : Preorder (invariantAffineCover σ hσ).I₀ :=
  inferInstanceAs (Preorder (InvariantAffineOpens σ))

/-- The cover of `X` by its invariant affine opens is locally directed, with the transition maps
induced by restriction of sections. -/
noncomputable instance (hσ : HasInvariantAffineCover σ) :
    (invariantAffineCover σ hσ).LocallyDirected where
  trans {V U} f := Spec.map (X.presheaf.map (homOfLE (leOfHom f : V.1 ≤ U.1)).op)
  trans_id U := (congrArg Spec.map (X.presheaf.map_id (op U.1))).trans (Spec.map_id _)
  trans_comp {W V U} f g :=
    (congrArg Spec.map (X.presheaf.map_comp (homOfLE (leOfHom g : V.1 ≤ U.1)).op
      (homOfLE (leOfHom f : W.1 ≤ V.1)).op)).trans (Spec.map_comp _ _)
  w {V U} f := IsAffineOpen.map_fromSpec U.2.1 V.2.1 _
  directed {U V} x := by
    obtain ⟨T, i, j, y, hy⟩ := exists_pullback_lift_eq U V x
    exact ⟨T, homOfLE i, homOfLE j, y, hy⟩
  property_trans {V U} f := U.2.1.isOpenImmersion_SpecMap_presheaf_map V.2.1 _

/-- The projections of the charts of `X` to the charts of the quotient are compatible with the
transition maps. -/
private lemma trans_projection_chartι (hσ : HasInvariantAffineCover σ)
    {V U : (invariantAffineCover σ hσ).I₀} (f : V ⟶ U) :
    letI := Scheme.sectionsMulSemiringAction σ U.2.2
    letI := Scheme.sectionsMulSemiringAction σ V.2.2
    (invariantAffineCover σ hσ).trans f ≫
        AffineInvariantQuotient.projection Γ(X, U.1) G ≫ chartι σ U =
      AffineInvariantQuotient.projection Γ(X, V.1) G ≫ chartι σ V := by
  rw [← chartDiagram_map_chartι f]
  exact specMap_map_projection_assoc f _

variable (σ) in
/-- The **quotient projection** `X ⟶ X/G`, glued from the affine invariant quotient projections
`Spec Γ(X, U) ⟶ Spec Γ(X, U)ᴳ` of the invariant affine opens `U`. -/
noncomputable def projection (hσ : HasInvariantAffineCover σ) : X ⟶ quotient σ :=
  (invariantAffineCover σ hσ).glueMorphismsOfLocallyDirected
    (fun U ↦ letI := Scheme.sectionsMulSemiringAction σ U.2.2
      AffineInvariantQuotient.projection Γ(X, U.1) G ≫ chartι σ U)
    (trans_projection_chartι hσ)

/-- Over the chart of an invariant affine open `U`, the quotient projection is the affine invariant
quotient projection of `Γ(X, U)`. -/
@[reassoc (attr := simp)]
lemma fromSpec_projection (hσ : HasInvariantAffineCover σ) (U : InvariantAffineOpens σ) :
    letI := Scheme.sectionsMulSemiringAction σ U.2.2
    U.2.1.fromSpec ≫ projection σ hσ =
      AffineInvariantQuotient.projection Γ(X, U.1) G ≫ chartι σ U :=
  Scheme.OpenCover.map_glueMorphismsOfLocallyDirected (invariantAffineCover σ hσ) _
    (trans_projection_chartι hσ) U

omit [Finite G] in
/-- Morphisms out of `X` are determined by their restrictions to the charts of the invariant affine
opens. -/
lemma hom_ext_fromSpec (hσ : HasInvariantAffineCover σ) {Z : Scheme.{u}} {f₁ f₂ : X ⟶ Z}
    (h : ∀ U : InvariantAffineOpens σ, U.2.1.fromSpec ≫ f₁ = U.2.1.fromSpec ≫ f₂) : f₁ = f₂ :=
  (invariantAffineCover σ hσ).hom_ext _ _ h

/-- The quotient projection is invariant under the action of `G`. -/
@[reassoc (attr := simp)]
lemma asIso_hom_projection (hσ : HasInvariantAffineCover σ) (g : G) :
    (σ g).asIso.hom ≫ projection σ hσ = projection σ hσ := by
  refine hom_ext_fromSpec hσ fun U ↦ ?_
  let := Scheme.sectionsMulSemiringAction σ U.2.2
  rw [← specAction_fromSpec_assoc U.2.1 U.2.2, fromSpec_projection,
    AffineInvariantQuotient.specAction_asIso_hom,
    AffineInvariantQuotient.specComap_projection_assoc]

/-- The quotient projection is surjective. -/
instance (hσ : HasInvariantAffineCover σ) : Surjective (projection σ hσ) where
  surj z := by
    obtain ⟨U, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (chartDiagram σ) z
    let := Scheme.sectionsMulSemiringAction σ U.2.2
    obtain ⟨p, rfl⟩ := Surjective.surj (f := AffineInvariantQuotient.projection Γ(X, U.1) G) y
    exact ⟨U.2.1.fromSpec p, congr($(fromSpec_projection hσ U) p)⟩

/-- **The charts of the quotient.** Over the chart `Spec Γ(X, U)ᴳ` of an invariant affine open `U`,
the quotient projection `X ⟶ X/G` is the affine invariant quotient projection
`Spec Γ(X, U) ⟶ Spec Γ(X, U)ᴳ`: the square formed with `Spec Γ(X, U) ⟶ X` is a pullback square.
In particular the preimage of the chart is `U`. -/
theorem isPullback_projection_fromSpec (hσ : HasInvariantAffineCover σ)
    (U : InvariantAffineOpens σ) :
    letI := Scheme.sectionsMulSemiringAction σ U.2.2
    IsPullback (AffineInvariantQuotient.projection Γ(X, U.1) G) U.2.1.fromSpec (chartι σ U)
      (projection σ hσ) := by
  let := Scheme.sectionsMulSemiringAction σ U.2.2
  refine IsOpenImmersion.isPullback _ _ _ _ (fromSpec_projection hσ U) ?_
  ext x
  rw [IsAffineOpen.opensRange_fromSpec]
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun hx ↦ ?_⟩
  · -- `x` lies in some invariant affine open `V`, and its image is in the charts of `U` and `V`.
    obtain ⟨V, hxV⟩ := hσ x
    obtain ⟨q, rfl⟩ : x ∈ Set.range V.2.1.fromSpec := V.2.1.range_fromSpec.ge hxV
    let := Scheme.sectionsMulSemiringAction σ V.2.2
    have hq := hy.trans congr($(fromSpec_projection hσ V) q)
    obtain ⟨T, i, j, t, -, ht⟩ := chartι_eq_chartι_iff.mp hq
    let := Scheme.sectionsMulSemiringAction σ T.2.2
    obtain ⟨t, rfl⟩ := Surjective.surj (f := AffineInvariantQuotient.projection Γ(X, T.1) G) t
    obtain ⟨g, hg⟩ := (chartDiagram_map_affineProjection_eq_iff j (𝟙 V) t q).mp
      -- The identity morphism is the identity on points.
      (by rw [CategoryTheory.Functor.map_id]; exact ht)
    have hmem : T.2.1.fromSpec t ∈ U.1 := leOfHom i (T.2.1.range_fromSpec.le ⟨t, rfl⟩)
    rw [hg]
    exact (U.2.2.apply_mem_iff g).mpr hmem
  · obtain ⟨p, rfl⟩ : x ∈ Set.range U.2.1.fromSpec := U.2.1.range_fromSpec.ge hx
    exact ⟨AffineInvariantQuotient.projection Γ(X, U.1) G p,
      congr($(fromSpec_projection hσ U) p).symm⟩

/-- A property of morphisms which is local on the target holds for the quotient projection exactly
when it holds for the affine invariant quotient projections of all invariant affine opens. -/
theorem projection_iff (hσ : HasInvariantAffineCover σ) {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtTarget P] :
    P (projection σ hσ) ↔ ∀ U : InvariantAffineOpens σ,
      letI := Scheme.sectionsMulSemiringAction σ U.2.2
      P (AffineInvariantQuotient.projection Γ(X, U.1) G) := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := P)
    (Scheme.IsLocallyDirected.openCover (chartDiagram σ))).trans (forall_congr' fun U ↦ ?_)
  let := Scheme.sectionsMulSemiringAction σ U.2.2
  have h := (isPullback_projection_fromSpec hσ U).flip
  -- The pullback of the projection along the chart is the affine projection, by the chart square.
  calc _ ↔ P (pullback.snd (projection σ hσ) (chartι σ U)) := Iff.rfl
    _ ↔ P (h.isoPullback.hom ≫ pullback.snd _ _) := (P.cancel_left_of_respectsIso _ _).symm
    _ ↔ _ := by rw [h.isoPullback_hom_snd]

/-- The quotient projection is integral, since sections are integral over invariant sections for
a finite group. -/
instance (hσ : HasInvariantAffineCover σ) : IsIntegralHom (projection σ hσ) := by
  have : IsZariskiLocalAtTarget @IsIntegralHom.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty
  refine (projection_iff hσ (P := @IsIntegralHom)).mpr fun U ↦ ?_
  let := Scheme.sectionsMulSemiringAction σ U.2.2
  infer_instance

/-! ### The universal property of the quotient -/

section UniversalProperty

variable {Z : Scheme.{u}}

omit [Finite G] in
/-- A `G`-invariant morphism restricts on the chart of an invariant affine open to a morphism
invariant under the action on the spectrum of the sections. -/
lemma specComap_fromSpec_comp_eq (f : X ⟶ Z) (hf : ∀ g : G, (σ g).asIso.hom ≫ f = f)
    (U : InvariantAffineOpens σ) (g : G) :
    letI := Scheme.sectionsMulSemiringAction σ U.2.2
    AffineInvariantQuotient.specComap Γ(X, U.1) G g ≫ U.2.1.fromSpec ≫ f = U.2.1.fromSpec ≫ f := by
  rw [specComap_fromSpec_assoc, hf]

/-- The descents of a `G`-invariant morphism to the affine invariant quotients of the invariant
affine opens are compatible with the transition maps of the chart diagram. -/
private lemma chartDiagram_map_descOfFinite (f : X ⟶ Z) (hf : ∀ g : G, (σ g).asIso.hom ≫ f = f)
    {U V : InvariantAffineOpens σ} (i : V ⟶ U) :
    letI := Scheme.sectionsMulSemiringAction σ U.2.2
    letI := Scheme.sectionsMulSemiringAction σ V.2.2
    (chartDiagram σ).map i ≫ AffineInvariantQuotient.descOfFinite (U.2.1.fromSpec ≫ f)
        (specComap_fromSpec_comp_eq f hf U) =
      AffineInvariantQuotient.descOfFinite (V.2.1.fromSpec ≫ f)
        (specComap_fromSpec_comp_eq f hf V) := by
  let := Scheme.sectionsMulSemiringAction σ U.2.2
  let := Scheme.sectionsMulSemiringAction σ V.2.2
  apply AffineInvariantQuotient.hom_ext_of_finite (A := Γ(X, V.1)) (G := G)
  rw [AffineInvariantQuotient.projection_descOfFinite, ← Category.assoc,
    ← specMap_map_projection, Category.assoc, AffineInvariantQuotient.projection_descOfFinite,
    IsAffineOpen.map_fromSpec_assoc]

variable (σ) in
/-- The morphism `X/G ⟶ Z` induced by a `G`-invariant morphism `f : X ⟶ Z`. On the chart of an
invariant affine open `U`, it is the descent of the restriction of `f` to `Spec Γ(X, U)` along the
affine invariant quotient projection. -/
noncomputable def desc (f : X ⟶ Z) (hf : ∀ g : G, (σ g).asIso.hom ≫ f = f) : quotient σ ⟶ Z :=
  colimit.desc (chartDiagram σ)
    { pt := Z
      ι :=
        { app U := letI := Scheme.sectionsMulSemiringAction σ U.2.2
            AffineInvariantQuotient.descOfFinite (U.2.1.fromSpec ≫ f)
              (specComap_fromSpec_comp_eq f hf U)
          naturality _ _ i :=
            (chartDiagram_map_descOfFinite f hf i).trans (Category.comp_id _).symm } }

/-- On the chart of an invariant affine open `U`, the induced morphism is the descent of the
restriction of `f` along the affine invariant quotient projection. -/
@[reassoc (attr := simp)]
lemma chartι_desc (f : X ⟶ Z) (hf : ∀ g : G, (σ g).asIso.hom ≫ f = f)
    (U : InvariantAffineOpens σ) :
    letI := Scheme.sectionsMulSemiringAction σ U.2.2
    chartι σ U ≫ desc σ f hf =
      AffineInvariantQuotient.descOfFinite (U.2.1.fromSpec ≫ f)
        (specComap_fromSpec_comp_eq f hf U) :=
  colimit.ι_desc _ _

/-- The induced morphism factors the given invariant morphism through the quotient projection. -/
@[reassoc (attr := simp)]
lemma projection_desc (hσ : HasInvariantAffineCover σ) (f : X ⟶ Z)
    (hf : ∀ g : G, (σ g).asIso.hom ≫ f = f) : projection σ hσ ≫ desc σ f hf = f := by
  refine hom_ext_fromSpec hσ fun U ↦ ?_
  let := Scheme.sectionsMulSemiringAction σ U.2.2
  rw [fromSpec_projection_assoc, chartι_desc, AffineInvariantQuotient.projection_descOfFinite]

/-- Morphisms out of the quotient are determined by their composition with the quotient
projection. -/
lemma hom_ext (hσ : HasInvariantAffineCover σ) {h₁ h₂ : quotient σ ⟶ Z}
    (e : projection σ hσ ≫ h₁ = projection σ hσ ≫ h₂) : h₁ = h₂ := by
  refine colimit.hom_ext fun U ↦ ?_
  let := Scheme.sectionsMulSemiringAction σ U.2.2
  apply AffineInvariantQuotient.hom_ext_of_finite (A := Γ(X, U.1)) (G := G)
  have := congr(U.2.1.fromSpec ≫ $e)
  rwa [fromSpec_projection_assoc, fromSpec_projection_assoc] at this

/-- The quotient projection is an epimorphism of schemes. -/
instance (hσ : HasInvariantAffineCover σ) : Epi (projection σ hσ) :=
  ⟨fun _ _ e ↦ hom_ext hσ e⟩

/-- **The universal property of the quotient by a finite group.** Every `G`-invariant morphism
from `X` to a scheme factors uniquely through the quotient projection `X ⟶ X/G`. -/
theorem existsUnique_projection_comp_eq (hσ : HasInvariantAffineCover σ) (f : X ⟶ Z)
    (hf : ∀ g : G, (σ g).asIso.hom ≫ f = f) : ∃! h : quotient σ ⟶ Z, projection σ hσ ≫ h = f :=
  ⟨desc σ f hf, projection_desc hσ f hf, fun _ hh ↦
    hom_ext hσ (hh.trans (projection_desc hσ f hf).symm)⟩

/-- Descending the composite of the quotient projection with a morphism out of the quotient
recovers that morphism. -/
@[simp]
lemma desc_projection_comp (hσ : HasInvariantAffineCover σ) (h : quotient σ ⟶ Z) :
    desc σ (projection σ hσ ≫ h) (fun g ↦ by rw [asIso_hom_projection_assoc]) = h :=
  hom_ext hσ (projection_desc hσ _ _)

end UniversalProperty

end Quotient

end TauCeti.InvariantQuotient
