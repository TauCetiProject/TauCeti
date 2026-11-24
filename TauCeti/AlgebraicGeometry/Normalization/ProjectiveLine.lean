/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Limits
public import TauCeti.AlgebraicGeometry.AffineScheme.Basic
public import TauCeti.AlgebraicGeometry.Gluing.Pushout
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.RingTheory.Localization.Away.AdjoinInv

/-!
# The normalization of the projective line in an algebra, glued from two charts

Let `R` be a commutative ring, `B` a commutative `R`-algebra and `u` a unit of `B`. The ring map
`R[t] → B`, `t ↦ u`, gives a morphism `Spec B ⟶ ℙ¹_R`, and since `u` is a unit, the preimage of
each of the two standard affine charts `Spec R[t]` and `Spec R[t⁻¹]` is all of `Spec B`. So over
these charts the normalization of `ℙ¹_R` in `Spec B` is the spectrum of the integral closure in `B`
of `R[u]`, respectively `R[u⁻¹]` (Stacks, Definition 29.54.3 and Lemma 29.54.4). This file builds
that scheme directly from its charts. Write

* `A₀ = projectiveLineNormalization.finiteChart R u`, the integral closure of `R[u]` in `B`;
* `A∞ = projectiveLineNormalization.infinityChart R u`, the integral closure of `R[u⁻¹]` in `B`;
* `A₀∞ = projectiveLineNormalization.overlapChart R u`, the integral closure of `R[u, u⁻¹]`.

Both `A₀` and `A∞` lie in `A₀∞`, and `A₀∞` is the localization of `A₀` away from `u` and of `A∞`
away from `u⁻¹` (`Units.isLocalization_away_integralClosure_adjoin_insert_inv`,
`Units.isLocalization_away_inv_integralClosure_adjoin_insert_inv`). So `Spec A₀∞` is an open
subscheme of `Spec A₀` and of `Spec A∞`, and `projectiveLineNormalization R u` is the pushout of
these two open immersions. It is a quasi-compact scheme over `Spec R`, covered by its two affine
charts, which meet exactly in `Spec A₀∞`. When `B` is a domain it is an integral scheme, and when
moreover `B` is the fraction field of `A₀` its function field is `B`.

For a one-variable function field `F` over the fraction field of a Dedekind domain `R` and a
transcendental `t ∈ F`, this is the model `X_{F,t}` of `F` over `Spec R` obtained by normalizing
`ℙ¹_R` in `F`. The comparison with Mathlib's relative normalization
`AlgebraicGeometry.Scheme.Hom.normalization` and the morphism to `ℙ¹_R` are not part of this file.
Over a field `k`, with `B = F` a function field and `u = x`, the charts are the affine models of
`TauCeti.AlgebraicGeometry.twoChartModel`, which describes them through holomorphy rings of
places; those are not available over a general base.

## Main definitions

* `TauCeti.AlgebraicGeometry.projectiveLineNormalization`: the scheme glued from `Spec A₀` and
  `Spec A∞` along `Spec A₀∞`.
* `TauCeti.AlgebraicGeometry.projectiveLineNormalization.ιFinite` and
  `TauCeti.AlgebraicGeometry.projectiveLineNormalization.ιInfinity`: the two chart open
  immersions.
* the instance `(projectiveLineNormalization R u).Over (Spec R)`, given on each chart by the
  structure map of the integral closure.
* `TauCeti.AlgebraicGeometry.projectiveLineNormalization.finiteChartSectionsEquiv`,
  `TauCeti.AlgebraicGeometry.projectiveLineNormalization.infinityChartSectionsEquiv` and
  `TauCeti.AlgebraicGeometry.projectiveLineNormalization.overlapChartSectionsEquiv`: the functions
  on the two charts and on their intersection are the elements of `A₀`, `A∞` and `A₀∞`, compatibly
  with the inclusions of `A₀` and `A∞` into `A₀∞` and with the functions pulled back from
  `Spec R`.
* `TauCeti.AlgebraicGeometry.projectiveLineNormalization.functionFieldEquiv`: when `B` is a domain
  and the fraction field of `A₀`, the `R`-algebra isomorphism of the function field with `B`.

## Main results

* `TauCeti.AlgebraicGeometry.projectiveLineNormalization.isPushout`: the charts glue along
  `Spec A₀∞`.
* `TauCeti.AlgebraicGeometry.projectiveLineNormalization.isPullback`: the charts meet exactly in
  `Spec A₀∞`.
* `TauCeti.AlgebraicGeometry.projectiveLineNormalization.range_ιFinite_union_range_ιInfinity`:
  the charts cover the scheme.
* the instances `CompactSpace (projectiveLineNormalization R u)` and, for a domain `B`,
  `IsIntegral (projectiveLineNormalization R u)`.
* `TauCeti.AlgebraicGeometry.projectiveLineNormalization.functionFieldEquiv_germToFunctionField`:
  the function field isomorphism sends the germ of a function on the finite chart to that element
  of `A₀ ⊆ B`; its variants `functionFieldEquiv_germToFunctionField_infinity` and
  `functionFieldEquiv_germToFunctionField_overlap` do the same for the chart at infinity and `A∞`,
  and for the intersection of the charts and `A₀∞`.

## References

* The Stacks Project, Definition 29.54.3 (035H) and Lemma 29.54.4 (035I): relative normalization
  and its description over affine opens.
* The Stacks Project, Section 10.36 (finite and integral ring extensions): integral closure
  commutes with localization.
-/

public section

open CategoryTheory Limits _root_.AlgebraicGeometry Algebra

namespace TauCeti.AlgebraicGeometry

universe u

variable (R : Type u) {B : Type u} [CommRing R] [CommRing B] [Algebra R B] (u : Bˣ)

namespace projectiveLineNormalization

/-- The finite chart ring `A₀`: the integral closure of `R[u]` in `B`. -/
abbrev finiteChart : Type u := integralClosure (adjoin R {(u : B)}) B

/-- The chart ring at infinity `A∞`: the integral closure of `R[u⁻¹]` in `B`. -/
abbrev infinityChart : Type u := integralClosure (adjoin R {((u⁻¹ : Bˣ) : B)}) B

/-- The overlap ring `A₀∞`: the integral closure of `R[u, u⁻¹]` in `B`. -/
abbrev overlapChart : Type u := integralClosure (adjoin R {(u : B), ((u⁻¹ : Bˣ) : B)}) B

/-- The inclusion `A₀ ⊆ A₀∞`: an element integral over `R[u]` is integral over `R[u, u⁻¹]`. -/
def finiteChartRestriction : finiteChart R u →ₐ[R] overlapChart R u where
  toFun x :=
    ⟨x, (u.isIntegral_adjoin_insert_inv_iff).2 ⟨0, by rw [pow_zero, one_mul]; exact x.property⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The inclusion `A∞ ⊆ A₀∞`: an element integral over `R[u⁻¹]` is integral over `R[u, u⁻¹]`. -/
def infinityChartRestriction : infinityChart R u →ₐ[R] overlapChart R u where
  toFun x :=
    ⟨x, (u.isIntegral_adjoin_insert_inv_iff_inv).2 ⟨0, by rw [pow_zero, one_mul]; exact x.property⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem coe_finiteChartRestriction (x : finiteChart R u) :
    (finiteChartRestriction R u x : B) = x :=
  (rfl)

@[simp]
theorem coe_infinityChartRestriction (x : infinityChart R u) :
    (infinityChartRestriction R u x : B) = x :=
  (rfl)

/-- `A₀∞` is the localization of `A₀` away from `u`, as an `A₀`-algebra through
`finiteChartRestriction`. -/
theorem isLocalization_away_finiteChartRestriction :
    letI := (finiteChartRestriction R u).toRingHom.toAlgebra
    IsLocalization.Away (u.integralClosureAdjoinGen R) (overlapChart R u) := by
  let := (finiteChartRestriction R u).toRingHom.toAlgebra
  have : IsScalarTower (finiteChart R u) (overlapChart R u) B := .of_algebraMap_eq fun _ ↦ rfl
  exact u.isLocalization_away_integralClosure_adjoin_insert_inv

/-- `A₀∞` is the localization of `A∞` away from `u⁻¹`, as an `A∞`-algebra through
`infinityChartRestriction`. -/
theorem isLocalization_away_infinityChartRestriction :
    letI := (infinityChartRestriction R u).toRingHom.toAlgebra
    IsLocalization.Away (u⁻¹.integralClosureAdjoinGen R) (overlapChart R u) := by
  let := (infinityChartRestriction R u).toRingHom.toAlgebra
  have : IsScalarTower (infinityChart R u) (overlapChart R u) B := .of_algebraMap_eq fun _ ↦ rfl
  exact u.isLocalization_away_inv_integralClosure_adjoin_insert_inv

/-- `Spec A₀∞ → Spec A₀` is an open immersion: `A₀∞` is the localization of `A₀` away from `u`. -/
theorem isOpenImmersion_specMap_finiteChartRestriction :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (finiteChartRestriction R u).toRingHom)) := by
  let := (finiteChartRestriction R u).toRingHom.toAlgebra
  have := isLocalization_away_finiteChartRestriction R u
  exact IsOpenImmersion.of_isLocalization (S := overlapChart R u) (u.integralClosureAdjoinGen R)

/-- `Spec A₀∞ → Spec A∞` is an open immersion: `A₀∞` is the localization of `A∞` away from
`u⁻¹`. -/
theorem isOpenImmersion_specMap_infinityChartRestriction :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (infinityChartRestriction R u).toRingHom)) := by
  let := (infinityChartRestriction R u).toRingHom.toAlgebra
  have := isLocalization_away_infinityChartRestriction R u
  exact IsOpenImmersion.of_isLocalization (S := overlapChart R u)
    (u⁻¹.integralClosureAdjoinGen R)

end projectiveLineNormalization

open projectiveLineNormalization

/-- **The normalization of the projective line `ℙ¹_R` in `B` along the coordinate `u`**: the
pushout of the open immersions `Spec A₀ ← Spec A₀∞ → Spec A∞`, where `A₀`, `A∞` and `A₀∞` are the
integral closures in `B` of `R[u]`, `R[u⁻¹]` and `R[u, u⁻¹]`. -/
noncomputable def projectiveLineNormalization : Scheme.{u} :=
  haveI := isOpenImmersion_specMap_finiteChartRestriction R u
  haveI := isOpenImmersion_specMap_infinityChartRestriction R u
  pushout (Spec.map (CommRingCat.ofHom (finiteChartRestriction R u).toRingHom))
    (Spec.map (CommRingCat.ofHom (infinityChartRestriction R u).toRingHom))

namespace projectiveLineNormalization

/-- The finite chart `Spec A₀` of `projectiveLineNormalization`, where `u` is regular. -/
noncomputable def ιFinite : Spec (.of (finiteChart R u)) ⟶ projectiveLineNormalization R u :=
  haveI := isOpenImmersion_specMap_finiteChartRestriction R u
  haveI := isOpenImmersion_specMap_infinityChartRestriction R u
  pushout.inl _ _

/-- The chart at infinity `Spec A∞` of `projectiveLineNormalization`, where `u⁻¹` is regular. -/
noncomputable def ιInfinity : Spec (.of (infinityChart R u)) ⟶ projectiveLineNormalization R u :=
  haveI := isOpenImmersion_specMap_finiteChartRestriction R u
  haveI := isOpenImmersion_specMap_infinityChartRestriction R u
  pushout.inr _ _

instance : IsOpenImmersion (ιFinite R u) := by
  have := isOpenImmersion_specMap_finiteChartRestriction R u
  have := isOpenImmersion_specMap_infinityChartRestriction R u
  exact inferInstanceAs (IsOpenImmersion (pushout.inl _ _))

instance : IsOpenImmersion (ιInfinity R u) := by
  have := isOpenImmersion_specMap_finiteChartRestriction R u
  have := isOpenImmersion_specMap_infinityChartRestriction R u
  exact inferInstanceAs (IsOpenImmersion (pushout.inr _ _))

/-- **The two charts glue along their overlap**: `projectiveLineNormalization` is the pushout of
`Spec A₀ ← Spec A₀∞ → Spec A∞` along the two chart inclusions. -/
theorem isPushout :
    IsPushout (Spec.map (CommRingCat.ofHom (finiteChartRestriction R u).toRingHom))
      (Spec.map (CommRingCat.ofHom (infinityChartRestriction R u).toRingHom))
      (ιFinite R u) (ιInfinity R u) := by
  have := isOpenImmersion_specMap_finiteChartRestriction R u
  have := isOpenImmersion_specMap_infinityChartRestriction R u
  exact IsPushout.of_hasPushout _ _

/-- The two charts agree on their overlap. -/
@[reassoc]
theorem condition :
    Spec.map (CommRingCat.ofHom (finiteChartRestriction R u).toRingHom) ≫ ιFinite R u =
      Spec.map (CommRingCat.ofHom (infinityChartRestriction R u).toRingHom) ≫ ιInfinity R u :=
  (isPushout R u).w

/-- **The two charts cover `projectiveLineNormalization`.** -/
theorem range_ιFinite_union_range_ιInfinity :
    Set.range (ιFinite R u) ∪ Set.range (ιInfinity R u) = Set.univ := by
  have := isOpenImmersion_specMap_finiteChartRestriction R u
  have := isOpenImmersion_specMap_infinityChartRestriction R u
  exact Scheme.range_pushout_inl_union_range_pushout_inr _ _

/-- **The two charts meet exactly in their overlap**: the square of the gluing is also a pullback,
so `Spec A₀∞` is the intersection of `Spec A₀` and `Spec A∞` in `projectiveLineNormalization`. -/
theorem isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (finiteChartRestriction R u).toRingHom))
      (Spec.map (CommRingCat.ofHom (infinityChartRestriction R u).toRingHom))
      (ιFinite R u) (ιInfinity R u) := by
  have := isOpenImmersion_specMap_finiteChartRestriction R u
  have := isOpenImmersion_specMap_infinityChartRestriction R u
  exact Scheme.isPullback_pushout_of_isOpenImmersion _ _

/-- **`projectiveLineNormalization` is quasi-compact**, as the union of its two affine charts. -/
instance : CompactSpace (projectiveLineNormalization R u) := by
  have := isOpenImmersion_specMap_finiteChartRestriction R u
  have := isOpenImmersion_specMap_infinityChartRestriction R u
  exact inferInstanceAs (CompactSpace ↑(pushout
    (Spec.map (CommRingCat.ofHom (finiteChartRestriction R u).toRingHom))
    (Spec.map (CommRingCat.ofHom (infinityChartRestriction R u).toRingHom))))

/-- **For a domain `B`, `projectiveLineNormalization` is an integral scheme**: its charts are
spectra of subrings of `B`, glued along the nonempty spectrum of `A₀∞`. -/
instance [IsDomain B] : IsIntegral (projectiveLineNormalization R u) := by
  have := isOpenImmersion_specMap_finiteChartRestriction R u
  have := isOpenImmersion_specMap_infinityChartRestriction R u
  have : Nonempty (Spec (.of (overlapChart R u))) := inferInstance
  exact inferInstanceAs (IsIntegral (pushout _ _))

/-! ### The structure morphism to `Spec R` -/

/-- The structure morphism of `projectiveLineNormalization` to `Spec R`, given on each chart by
`Spec` of the structure map of the chart ring. -/
noncomputable instance : (projectiveLineNormalization R u).Over (Spec (.of R)) where
  hom := (isPushout R u).desc
    (Spec.map (CommRingCat.ofHom (algebraMap R (finiteChart R u))))
    (Spec.map (CommRingCat.ofHom (algebraMap R (infinityChart R u))))
    (by
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe,
        AlgHom.comp_algebraMap])

/-- On the finite chart, the structure morphism is `Spec` of the structure map of `A₀`. -/
@[reassoc (attr := simp)]
theorem ιFinite_over : ιFinite R u ≫ (projectiveLineNormalization R u ↘ Spec (.of R)) =
    Spec.map (CommRingCat.ofHom (algebraMap R (finiteChart R u))) :=
  (isPushout R u).inl_desc _ _ _

/-- On the chart at infinity, the structure morphism is `Spec` of the structure map of `A∞`. -/
@[reassoc (attr := simp)]
theorem ιInfinity_over : ιInfinity R u ≫ (projectiveLineNormalization R u ↘ Spec (.of R)) =
    Spec.map (CommRingCat.ofHom (algebraMap R (infinityChart R u))) :=
  (isPushout R u).inr_desc _ _ _

/-! ### The function field -/

/-- The finite chart is an affine open subscheme. -/
theorem isAffineOpen_image_ιFinite_top : IsAffineOpen (ιFinite R u ''ᵁ ⊤) := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact isAffineOpen_opensRange _

instance [Nontrivial B] : Nonempty (ιFinite R u ''ᵁ ⊤) := by
  obtain ⟨p⟩ : Nonempty (Spec (.of (finiteChart R u))) := inferInstance
  exact ⟨⟨ιFinite R u p, p, trivial, rfl⟩⟩

/-- The functions on the finite chart are the elements of `A₀`. -/
noncomputable def finiteChartSectionsEquiv :
    Γ(projectiveLineNormalization R u, ιFinite R u ''ᵁ ⊤) ≃+* finiteChart R u :=
  ((ιFinite R u).appIso ⊤ ≪≫ Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv

/-- `TauCeti.AlgebraicGeometry.projectiveLineNormalization.finiteChartSectionsEquiv` restricts a
function on the finite chart along the chart and reads it as an element of `A₀`. -/
theorem finiteChartSectionsEquiv_apply
    (a : Γ(projectiveLineNormalization R u, ιFinite R u ''ᵁ ⊤)) :
    finiteChartSectionsEquiv R u a = (Scheme.ΓSpecIso _).hom (((ιFinite R u).appIso ⊤).hom a) :=
  (rfl)

/-- On the finite chart, the functions on `Spec R` pulled back along the structure morphism are
the elements of `R` in `A₀`. -/
@[simp]
theorem finiteChartSectionsEquiv_appLE (a : Γ(Spec (.of R), ⊤)) :
    finiteChartSectionsEquiv R u
        ((projectiveLineNormalization R u ↘ Spec (.of R)).appLE ⊤ _ le_top a) =
      algebraMap R _ ((Scheme.ΓSpecIso (.of R)).hom a) :=
  Scheme.ΓSpecIso_appIso_hom_appLE _ _ _ (ιFinite_over R u) a

/-- The chart at infinity is an affine open subscheme. -/
theorem isAffineOpen_image_ιInfinity_top : IsAffineOpen (ιInfinity R u ''ᵁ ⊤) := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact isAffineOpen_opensRange _

instance [Nontrivial B] : Nonempty (ιInfinity R u ''ᵁ ⊤) := by
  obtain ⟨p⟩ : Nonempty (Spec (.of (infinityChart R u))) := inferInstance
  exact ⟨⟨ιInfinity R u p, p, trivial, rfl⟩⟩

/-- The functions on the chart at infinity are the elements of `A∞`. -/
noncomputable def infinityChartSectionsEquiv :
    Γ(projectiveLineNormalization R u, ιInfinity R u ''ᵁ ⊤) ≃+* infinityChart R u :=
  ((ιInfinity R u).appIso ⊤ ≪≫ Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv

/-- `TauCeti.AlgebraicGeometry.projectiveLineNormalization.infinityChartSectionsEquiv` restricts a
function on the chart at infinity along the chart and reads it as an element of `A∞`. -/
theorem infinityChartSectionsEquiv_apply
    (a : Γ(projectiveLineNormalization R u, ιInfinity R u ''ᵁ ⊤)) :
    infinityChartSectionsEquiv R u a =
      (Scheme.ΓSpecIso _).hom (((ιInfinity R u).appIso ⊤).hom a) :=
  (rfl)

/-- On the chart at infinity, the functions on `Spec R` pulled back along the structure morphism
are the elements of `R` in `A∞`. -/
@[simp]
theorem infinityChartSectionsEquiv_appLE (a : Γ(Spec (.of R), ⊤)) :
    infinityChartSectionsEquiv R u
        ((projectiveLineNormalization R u ↘ Spec (.of R)).appLE ⊤ _ le_top a) =
      algebraMap R _ ((Scheme.ΓSpecIso (.of R)).hom a) :=
  Scheme.ΓSpecIso_appIso_hom_appLE _ _ _ (ιInfinity_over R u) a

/-- The intersection of the two charts is the image of `Spec A₀∞`. -/
theorem image_specMap_infinityChartRestriction_comp_ιInfinity_top :
    haveI := isOpenImmersion_specMap_infinityChartRestriction R u
    (Spec.map (CommRingCat.ofHom (infinityChartRestriction R u).toRingHom) ≫ ιInfinity R u) ''ᵁ
      ⊤ = ιFinite R u ''ᵁ ⊤ ⊓ ιInfinity R u ''ᵁ ⊤ := by
  have := isOpenImmersion_specMap_finiteChartRestriction R u
  have := isOpenImmersion_specMap_infinityChartRestriction R u
  have hpre : ιInfinity R u ⁻¹ᵁ (ιFinite R u).opensRange =
      (Spec.map (CommRingCat.ofHom (infinityChartRestriction R u).toRingHom)).opensRange :=
    Scheme.preimage_opensRange_pushout_inl _ _
  simp only [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp, ← hpre,
    Scheme.Hom.image_preimage_eq_opensRange_inf, inf_comm]

instance [Nontrivial B] : Nonempty (ιFinite R u ''ᵁ ⊤ ⊓ ιInfinity R u ''ᵁ ⊤ :) := by
  have := isOpenImmersion_specMap_infinityChartRestriction R u
  rw [← image_specMap_infinityChartRestriction_comp_ιInfinity_top]
  obtain ⟨p⟩ : Nonempty (Spec (.of (overlapChart R u))) := inferInstance
  exact ⟨⟨_, p, trivial, rfl⟩⟩

/-- The functions on the intersection of the two charts are the elements of `A₀∞`. It is
compatible with the chart restriction maps (`finiteChartRestriction_finiteChartSectionsEquiv` and
`infinityChartRestriction_infinityChartSectionsEquiv`). -/
noncomputable def overlapChartSectionsEquiv :
    Γ(projectiveLineNormalization R u, ιFinite R u ''ᵁ ⊤ ⊓ ιInfinity R u ''ᵁ ⊤) ≃+*
      overlapChart R u :=
  haveI := isOpenImmersion_specMap_infinityChartRestriction R u
  ((projectiveLineNormalization R u).presheaf.mapIso
      (eqToIso (image_specMap_infinityChartRestriction_comp_ιInfinity_top R u)).op ≪≫
    (Spec.map (CommRingCat.ofHom (infinityChartRestriction R u).toRingHom) ≫
      ιInfinity R u).appIso ⊤ ≪≫ Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv

/-- `TauCeti.AlgebraicGeometry.projectiveLineNormalization.overlapChartSectionsEquiv` restricts a
function on the intersection of the two charts along `Spec A₀∞` and reads it as an element of
`A₀∞`. -/
theorem overlapChartSectionsEquiv_apply
    (a : Γ(projectiveLineNormalization R u, ιFinite R u ''ᵁ ⊤ ⊓ ιInfinity R u ''ᵁ ⊤)) :
    haveI := isOpenImmersion_specMap_infinityChartRestriction R u
    overlapChartSectionsEquiv R u a = (Scheme.ΓSpecIso _).hom
      (((Spec.map (CommRingCat.ofHom (infinityChartRestriction R u).toRingHom) ≫
        ιInfinity R u).appIso ⊤).hom ((projectiveLineNormalization R u).presheaf.map
          (eqToHom (image_specMap_infinityChartRestriction_comp_ιInfinity_top R u)).op a)) :=
  (rfl)

/-- On the intersection of the two charts, restricting a function on the finite chart and reading
it in `A₀∞` agrees with reading it in `A₀` and including `A₀` into `A₀∞`. -/
theorem finiteChartRestriction_finiteChartSectionsEquiv
    (a : Γ(projectiveLineNormalization R u, ιFinite R u ''ᵁ ⊤)) :
    finiteChartRestriction R u (finiteChartSectionsEquiv R u a) =
      overlapChartSectionsEquiv R u
        ((projectiveLineNormalization R u).presheaf.map (homOfLE inf_le_left).op a) := by
  have := isOpenImmersion_specMap_finiteChartRestriction R u
  have := isOpenImmersion_specMap_infinityChartRestriction R u
  exact Scheme.ΓSpecIso_appIso_hom_map_eq_restrict _ (ιFinite R u) _ (condition R u) inf_le_left
    (image_specMap_infinityChartRestriction_comp_ιInfinity_top R u) a

/-- On the intersection of the two charts, restricting a function on the chart at infinity and
reading it in `A₀∞` agrees with reading it in `A∞` and including `A∞` into `A₀∞`. -/
theorem infinityChartRestriction_infinityChartSectionsEquiv
    (a : Γ(projectiveLineNormalization R u, ιInfinity R u ''ᵁ ⊤)) :
    infinityChartRestriction R u (infinityChartSectionsEquiv R u a) =
      overlapChartSectionsEquiv R u
        ((projectiveLineNormalization R u).presheaf.map (homOfLE inf_le_right).op a) := by
  have := isOpenImmersion_specMap_infinityChartRestriction R u
  exact Scheme.ΓSpecIso_appIso_hom_map_eq_restrict _ (ιInfinity R u) _ rfl inf_le_right
    (image_specMap_infinityChartRestriction_comp_ιInfinity_top R u) a

/-- On the intersection of the two charts, the functions on `Spec R` pulled back along the
structure morphism are the elements of `R` in `A₀∞`. -/
@[simp]
theorem overlapChartSectionsEquiv_appLE (a : Γ(Spec (.of R), ⊤)) :
    overlapChartSectionsEquiv R u
        ((projectiveLineNormalization R u ↘ Spec (.of R)).appLE ⊤ _ le_top a) =
      algebraMap R _ ((Scheme.ΓSpecIso (.of R)).hom a) := by
  have h := finiteChartRestriction_finiteChartSectionsEquiv R u
    ((projectiveLineNormalization R u ↘ Spec (.of R)).appLE ⊤ _ le_top a)
  rw [finiteChartSectionsEquiv_appLE, AlgHom.commutes, ← CommRingCat.comp_apply] at h
  refine Eq.trans ?_ h.symm
  exact congr(overlapChartSectionsEquiv R u ($((Scheme.Hom.appLE_map _ _ _).symm) a))

variable [IsDomain B] [IsFractionRing (finiteChart R u) B]

/-- **The function field of `projectiveLineNormalization` is `B`**, when `B` is a domain and the
fraction field of `A₀`, as an `R`-algebra; for instance when `B` is a field algebraic over
`R[u]`. It identifies the germ of a function on the finite chart with the corresponding element
of `A₀ ⊆ B`
(`TauCeti.AlgebraicGeometry.projectiveLineNormalization.functionFieldEquiv_germToFunctionField`).
-/
noncomputable def functionFieldEquiv :
    (projectiveLineNormalization R u).functionField ≃ₐ[R] B :=
  (ιFinite R u).functionFieldAlgEquivOfIsOpenImmersion (ιFinite_over R u) B

/-- `TauCeti.AlgebraicGeometry.projectiveLineNormalization.functionFieldEquiv` sends the germ of a
function on the finite chart to the corresponding element of `A₀ ⊆ B`. -/
@[simp]
theorem functionFieldEquiv_germToFunctionField
    (a : Γ(projectiveLineNormalization R u, ιFinite R u ''ᵁ ⊤)) :
    functionFieldEquiv R u ((projectiveLineNormalization R u).germToFunctionField _ a) =
      finiteChartSectionsEquiv R u a :=
  Scheme.Hom.functionFieldAlgEquivOfIsOpenImmersion_germToFunctionField _ (ιFinite_over R u) B a

/-- `TauCeti.AlgebraicGeometry.projectiveLineNormalization.functionFieldEquiv` sends the germ of a
function on the intersection of the two charts to the corresponding element of `A₀∞ ⊆ B`. -/
@[simp]
theorem functionFieldEquiv_germToFunctionField_overlap
    (a : Γ(projectiveLineNormalization R u, ιFinite R u ''ᵁ ⊤ ⊓ ιInfinity R u ''ᵁ ⊤)) :
    functionFieldEquiv R u ((projectiveLineNormalization R u).germToFunctionField _ a) =
      overlapChartSectionsEquiv R u a := by
  let := (finiteChartRestriction R u).toRingHom.toAlgebra
  have := isLocalization_away_finiteChartRestriction R u
  -- Both sides are ring maps out of `A₀∞`, the localization of `A₀` away from `u`, and they agree
  -- on `A₀` by `functionFieldEquiv_germToFunctionField`.
  have key := IsLocalization.ringHom_ext (Submonoid.powers (u.integralClosureAdjoinGen R))
    (S := overlapChart R u)
    (j := (functionFieldEquiv R u).toRingHom.comp
      (((projectiveLineNormalization R u).germToFunctionField _).hom.comp
        (overlapChartSectionsEquiv R u).symm.toRingHom))
    (k := algebraMap (overlapChart R u) B) (RingHom.ext fun x ↦ by
      obtain ⟨a, rfl⟩ := (finiteChartSectionsEquiv R u).surjective x
      simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        AlgEquiv.coe_toRingEquiv, Subalgebra.algebraMap_apply, coe_finiteChartRestriction]
      rw [finiteChartRestriction_finiteChartSectionsEquiv, RingEquiv.symm_apply_apply,
        TopCat.Presheaf.germ_res_apply, functionFieldEquiv_germToFunctionField])
  simpa using congr($key (overlapChartSectionsEquiv R u a))

/-- `TauCeti.AlgebraicGeometry.projectiveLineNormalization.functionFieldEquiv` sends the germ of a
function on the chart at infinity to the corresponding element of `A∞ ⊆ B`. -/
@[simp]
theorem functionFieldEquiv_germToFunctionField_infinity
    (a : Γ(projectiveLineNormalization R u, ιInfinity R u ''ᵁ ⊤)) :
    functionFieldEquiv R u ((projectiveLineNormalization R u).germToFunctionField _ a) =
      infinityChartSectionsEquiv R u a := by
  rw [← coe_infinityChartRestriction, infinityChartRestriction_infinityChartSectionsEquiv,
    ← functionFieldEquiv_germToFunctionField_overlap, TopCat.Presheaf.germ_res_apply]

end projectiveLineNormalization

end TauCeti.AlgebraicGeometry
