/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.FieldTheory.FunctionField.HolomorphyRing.Localization

/-!
# The scheme of a function field glued from two affine charts

Let `F / k` be an algebraic function field and `x ∈ F` nonzero. The places of `F / k` at which `x`
is regular and those at which `x⁻¹` is regular cover all places. Their holomorphy rings are

* `𝒪_x = holomorphyRing {P | x ∈ 𝒪_P}`, the integral closure of `k[x]` in `F`, and
* `𝒪_{x⁻¹} = holomorphyRing {P | x⁻¹ ∈ 𝒪_P}`, the integral closure of `k[x⁻¹]` in `F`

(for the integral closures, see `TauCeti.restrictScalars_integralClosure_adjoin_eq_holomorphyRing`).
Both restrict to the holomorphy ring `𝒪_{x, x⁻¹}` of the places at which `x` is a unit, which is
the localization of `𝒪_x` away from `x` and of `𝒪_{x⁻¹}` away from `x⁻¹`
(`TauCeti.isLocalization_away_holomorphyRing_inter`). Hence `Spec 𝒪_{x, x⁻¹}` is an open
subscheme of both `Spec 𝒪_x` and `Spec 𝒪_{x⁻¹}`, and gluing the two charts along it, as the
pushout of these two open immersions, gives the integral scheme
`TauCeti.AlgebraicGeometry.twoChartModel`; this is defined for every nonzero `x`.

When `x` is transcendental over `k`, `Spec 𝒪_x` and `Spec 𝒪_{x⁻¹}` are the two affine charts of a
curve with function field `F`. For `F = k(x)` they are `Spec k[x]` and `Spec k[x⁻¹]`, glued into
the projective line; in general they are the normalizations in `F` of the two standard affine
charts of the projective line, and this is the gluing from which the normalization of the
projective line in `F` is built. (When `x` is algebraic over `k`, `x` and `x⁻¹` are regular at
every place, and the construction does not have this interpretation.)

This file proves that the glued scheme is an integral scheme over `k`, covered by the two charts,
and that for transcendental `x` its function field is `F` as a `k`-algebra.

## Main definitions

* `TauCeti.AlgebraicGeometry.twoChartModel`: the scheme glued from `Spec 𝒪_x` and `Spec 𝒪_{x⁻¹}`
  along `Spec 𝒪_{x, x⁻¹}`.
* `TauCeti.AlgebraicGeometry.twoChartModel.ιFinite` and
  `TauCeti.AlgebraicGeometry.twoChartModel.ιInfinity`: the open immersions of the two charts.
* the instance `(twoChartModel hF hx).Over (Spec k)`, given on each chart by the inclusion of the
  constants.
* `TauCeti.AlgebraicGeometry.twoChartModel.functionFieldEquiv`: for `x` transcendental over `k`,
  the `k`-algebra isomorphism `k(X) ≃ₐ[k] F`.

## Main results

* `TauCeti.AlgebraicGeometry.isOpenImmersion_specMap_inclusion_holomorphyRing`: `Spec` of the
  restriction from the holomorphy ring of `S` to that of `S ∩ {P | x⁻¹ ∈ 𝒪_P}` is an open
  immersion.
* `TauCeti.AlgebraicGeometry.twoChartModel.isPushout`: the two charts glue along their overlap.
* `TauCeti.AlgebraicGeometry.twoChartModel.range_ιFinite_union_range_ιInfinity`: the two charts
  cover the scheme.
* the instance `IsIntegral (twoChartModel hF hx)`: the scheme is integral.
* `TauCeti.AlgebraicGeometry.twoChartModel.functionFieldEquiv_germToFunctionField`: the
  isomorphism `k(X) ≃ F` sends the germ of a function on the finite chart to that function.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.2 and Appendix B.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section I.6 and Exercise II.2.12.
-/

public section

open CategoryTheory Limits _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F]

/-- **`Spec` of an inclusion of holomorphy rings that inverts a single function is an open
immersion**: if `T = S ∩ {P | x⁻¹ ∈ 𝒪_P}` for a nonzero `x ∈ 𝒪_S`, then `Spec 𝒪_T → Spec 𝒪_S` is
an open immersion, the scheme-level form of `TauCeti.isLocalization_away_holomorphyRing_inter`. -/
theorem isOpenImmersion_specMap_inclusion_holomorphyRing (hF : IsFunctionField k F)
    {S T : Set (Place k F)} (x : holomorphyRing S) (hx : (x : F) ≠ 0)
    (hT : T = S ∩ {P : Place k F | (x : F)⁻¹ ∈ P.integers}) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion
      (holomorphyRing_antitone (hT.trans_le Set.inter_subset_left))).toRingHom)) := by
  have h : holomorphyRing S ≤ holomorphyRing T :=
    holomorphyRing_antitone (hT.trans_le Set.inter_subset_left)
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower (holomorphyRing S) (holomorphyRing T) F :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (Subalgebra.coe_inclusion h a).symm
  have := isLocalization_away_holomorphyRing_inter hF x hx hT
  exact IsOpenImmersion.of_isLocalization x

namespace twoChartModel

/-- The restriction of a function regular wherever `x` is to the places at which `x` is a unit. -/
noncomputable abbrev finiteChartRestriction (x : F) :
    holomorphyRing {P : Place k F | x ∈ P.integers} →ₐ[k]
      holomorphyRing ({P : Place k F | x ∈ P.integers} ∩ {P : Place k F | x⁻¹ ∈ P.integers}) :=
  Subalgebra.inclusion (holomorphyRing_antitone Set.inter_subset_left)

/-- The restriction of a function regular wherever `x⁻¹` is to the places at which `x` is a
unit. -/
noncomputable abbrev infinityChartRestriction (x : F) :
    holomorphyRing {P : Place k F | x⁻¹ ∈ P.integers} →ₐ[k]
      holomorphyRing ({P : Place k F | x ∈ P.integers} ∩ {P : Place k F | x⁻¹ ∈ P.integers}) :=
  Subalgebra.inclusion (holomorphyRing_antitone Set.inter_subset_right)

/-- `Spec 𝒪_{x, x⁻¹} → Spec 𝒪_x` is an open immersion: the restriction to the overlap is the
localization away from `x`. -/
theorem isOpenImmersion_specMap_finiteChartRestriction (hF : IsFunctionField k F) {x : F}
    (hx : x ≠ 0) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (finiteChartRestriction (k := k) x).toRingHom)) :=
  isOpenImmersion_specMap_inclusion_holomorphyRing hF
    ⟨x, mem_holomorphyRing_iff.mpr fun _ hP ↦ hP⟩ hx rfl

/-- `Spec 𝒪_{x, x⁻¹} → Spec 𝒪_{x⁻¹}` is an open immersion: the restriction to the overlap is the
localization away from `x⁻¹`. -/
theorem isOpenImmersion_specMap_infinityChartRestriction (hF : IsFunctionField k F) {x : F}
    (hx : x ≠ 0) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (infinityChartRestriction (k := k) x).toRingHom)) :=
  isOpenImmersion_specMap_inclusion_holomorphyRing hF
    (T := {P | x ∈ P.integers} ∩ {P | x⁻¹ ∈ P.integers})
    ⟨x⁻¹, mem_holomorphyRing_iff.mpr fun _ hP ↦ hP⟩ (inv_ne_zero hx)
    (by rw [inv_inv, Set.inter_comm]; rfl)

end twoChartModel

open twoChartModel

/-- **The scheme of `F` glued from the two charts of `x`**: the pushout of the open immersions
`Spec 𝒪_x ← Spec 𝒪_{x, x⁻¹} → Spec 𝒪_{x⁻¹}`, where `𝒪_x`, `𝒪_{x⁻¹}` and `𝒪_{x, x⁻¹}` are the
holomorphy rings of the places at which `x`, `x⁻¹`, and both are regular. -/
noncomputable def twoChartModel (hF : IsFunctionField k F) {x : F} (hx : x ≠ 0) : Scheme.{u} :=
  haveI := isOpenImmersion_specMap_finiteChartRestriction hF hx
  haveI := isOpenImmersion_specMap_infinityChartRestriction hF hx
  pushout (Spec.map (CommRingCat.ofHom (finiteChartRestriction (k := k) x).toRingHom))
    (Spec.map (CommRingCat.ofHom (infinityChartRestriction (k := k) x).toRingHom))

namespace twoChartModel

variable (hF : IsFunctionField k F) {x : F} (hx : x ≠ 0)

/-- The finite chart `Spec 𝒪_x` of `twoChartModel`, on which `x` is regular. -/
noncomputable def ιFinite :
    Spec (.of (holomorphyRing {P : Place k F | x ∈ P.integers})) ⟶ twoChartModel hF hx :=
  haveI := isOpenImmersion_specMap_finiteChartRestriction hF hx
  haveI := isOpenImmersion_specMap_infinityChartRestriction hF hx
  pushout.inl _ _

/-- The chart at infinity `Spec 𝒪_{x⁻¹}` of `twoChartModel`, on which `x⁻¹` is regular. -/
noncomputable def ιInfinity :
    Spec (.of (holomorphyRing {P : Place k F | x⁻¹ ∈ P.integers})) ⟶ twoChartModel hF hx :=
  haveI := isOpenImmersion_specMap_finiteChartRestriction hF hx
  haveI := isOpenImmersion_specMap_infinityChartRestriction hF hx
  pushout.inr _ _

instance : IsOpenImmersion (ιFinite hF hx) := by
  have := isOpenImmersion_specMap_finiteChartRestriction hF hx
  have := isOpenImmersion_specMap_infinityChartRestriction hF hx
  exact inferInstanceAs (IsOpenImmersion (pushout.inl _ _))

instance : IsOpenImmersion (ιInfinity hF hx) := by
  have := isOpenImmersion_specMap_finiteChartRestriction hF hx
  have := isOpenImmersion_specMap_infinityChartRestriction hF hx
  exact inferInstanceAs (IsOpenImmersion (pushout.inr _ _))

/-- **The two charts glue along their overlap**: `twoChartModel` is the pushout of
`Spec 𝒪_x ← Spec 𝒪_{x, x⁻¹} → Spec 𝒪_{x⁻¹}` along the two chart inclusions. -/
theorem isPushout :
    IsPushout (Spec.map (CommRingCat.ofHom (finiteChartRestriction (k := k) x).toRingHom))
      (Spec.map (CommRingCat.ofHom (infinityChartRestriction (k := k) x).toRingHom))
      (ιFinite hF hx) (ιInfinity hF hx) := by
  have := isOpenImmersion_specMap_finiteChartRestriction hF hx
  have := isOpenImmersion_specMap_infinityChartRestriction hF hx
  exact IsPushout.of_hasPushout _ _

/-- The two charts agree on their overlap. -/
@[reassoc]
theorem condition :
    Spec.map (CommRingCat.ofHom (finiteChartRestriction (k := k) x).toRingHom) ≫ ιFinite hF hx =
      Spec.map (CommRingCat.ofHom (infinityChartRestriction (k := k) x).toRingHom) ≫
        ιInfinity hF hx :=
  (isPushout hF hx).w

/-- **The two charts cover `twoChartModel`.** -/
theorem range_ιFinite_union_range_ιInfinity :
    Set.range (ιFinite hF hx) ∪ Set.range (ιInfinity hF hx) = Set.univ := by
  have := isOpenImmersion_specMap_finiteChartRestriction hF hx
  have := isOpenImmersion_specMap_infinityChartRestriction hF hx
  refine Set.eq_univ_of_forall fun p ↦ ?_
  -- Every point of a locally directed colimit comes from one of the three pieces of the span,
  -- and the overlap maps through the finite chart.
  obtain ⟨i, q, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span _ _) p
  rcases i with _ | _ | _
  · refine Or.inl
      ⟨Spec.map (CommRingCat.ofHom (finiteChartRestriction (k := k) x).toRingHom) q, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← colimit.w (span _ _) (WidePushoutShape.Hom.init .left)]
    -- `ιFinite` is `pushout.inl`, the colimit inclusion of the left piece of the span.
    rfl
  · exact Or.inl ⟨q, rfl⟩
  · exact Or.inr ⟨q, rfl⟩

/-- **The two charts meet.** The overlap `Spec 𝒪_{x, x⁻¹}` is nonempty, and its image lies in
both charts. -/
theorem range_ιInfinity_inter_range_ιFinite_nonempty :
    (Set.range (ιInfinity hF hx) ∩ Set.range (ιFinite hF hx)).Nonempty := by
  obtain ⟨p⟩ : Nonempty (Spec (.of (holomorphyRing
      ({P : Place k F | x ∈ P.integers} ∩ {P : Place k F | x⁻¹ ∈ P.integers})))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  refine ⟨ιFinite hF hx
      (Spec.map (CommRingCat.ofHom (finiteChartRestriction (k := k) x).toRingHom) p),
    ⟨Spec.map (CommRingCat.ofHom (infinityChartRestriction (k := k) x).toRingHom) p, ?_⟩,
    ⟨_, rfl⟩⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, condition]

instance : IsReduced (twoChartModel hF hx) := by
  -- Every stalk is a stalk of one of the two charts, which are spectra of domains.
  have (p : twoChartModel hF hx) : _root_.IsReduced ((twoChartModel hF hx).presheaf.stalk p) := by
    rcases (Set.ext_iff.mp (range_ιFinite_union_range_ιInfinity hF hx) p).mpr trivial with
      ⟨q, rfl⟩ | ⟨q, rfl⟩
    · exact isReduced_of_injective _
        (asIso ((ιFinite hF hx).stalkMap q)).commRingCatIsoToRingEquiv.injective
    · exact isReduced_of_injective _
        (asIso ((ιInfinity hF hx).stalkMap q)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

instance : IrreducibleSpace (twoChartModel hF hx) := by
  -- Both charts are spectra of domains, so their images are irreducible.
  have isIrreducible_range {R : CommRingCat.{u}} [IsDomain R] (f : Spec R ⟶ twoChartModel hF hx) :
      IsIrreducible (Set.range f) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ _).image _ f.continuous.continuousOn
  -- The finite chart is dense: it meets the irreducible chart at infinity in a nonempty open set,
  -- which is dense there.
  have hdense : closure (Set.range (ιFinite hF hx)) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← range_ιFinite_union_range_ιInfinity hF hx]
    refine Set.union_subset subset_closure ((subset_closure_inter_of_isPreirreducible_of_isOpen
      (isIrreducible_range (ιInfinity hF hx)).isPreirreducible
      (ιFinite hF hx).isOpenEmbedding.isOpen_range
      (range_ιInfinity_inter_range_ιFinite_nonempty hF hx)).trans
      (closure_mono Set.inter_subset_right))
  rw [irreducibleSpace_def, Set.top_eq_univ, ← hdense]
  exact (isIrreducible_range (ιFinite hF hx)).closure

/-- **`twoChartModel` is an integral scheme.** -/
instance : IsIntegral (twoChartModel hF hx) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-! ### The structure morphism to `Spec k` -/

/-- The structure morphism of `twoChartModel` to `Spec k`, given on each chart by the inclusion of
the constants. -/
noncomputable instance : (twoChartModel hF hx).Over (Spec (.of k)) where
  hom := (isPushout hF hx).desc
    (Spec.map
      (CommRingCat.ofHom (algebraMap k (holomorphyRing {P : Place k F | x ∈ P.integers}))))
    (Spec.map
      (CommRingCat.ofHom (algebraMap k (holomorphyRing {P : Place k F | x⁻¹ ∈ P.integers}))))
    (by
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe,
        AlgHom.comp_algebraMap])

/-- On the finite chart, the structure morphism is `Spec` of the inclusion of the constants. -/
@[reassoc (attr := simp)]
theorem ιFinite_over : ιFinite hF hx ≫ (twoChartModel hF hx ↘ Spec (.of k)) =
    Spec.map (CommRingCat.ofHom (algebraMap k (holomorphyRing {P : Place k F | x ∈ P.integers}))) :=
  (isPushout hF hx).inl_desc _ _ _

/-- On the chart at infinity, the structure morphism is `Spec` of the inclusion of the constants. -/
@[reassoc (attr := simp)]
theorem ιInfinity_over : ιInfinity hF hx ≫ (twoChartModel hF hx ↘ Spec (.of k)) =
    Spec.map
      (CommRingCat.ofHom (algebraMap k (holomorphyRing {P : Place k F | x⁻¹ ∈ P.integers}))) :=
  (isPushout hF hx).inr_desc _ _ _

/-! ### The function field -/

instance : Nonempty (ιFinite hF hx ''ᵁ ⊤) := by
  obtain ⟨p⟩ : Nonempty (Spec (.of (holomorphyRing {P : Place k F | x ∈ P.integers}))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  exact ⟨⟨ιFinite hF hx p, p, trivial, rfl⟩⟩

/-- The finite chart is an affine open subscheme. -/
theorem isAffineOpen_image_ιFinite_top : IsAffineOpen (ιFinite hF hx ''ᵁ ⊤) := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact isAffineOpen_opensRange _

/-- The functions on the finite chart are the functions of `F` regular wherever `x` is. -/
noncomputable def finiteChartSectionsEquiv :
    Γ(twoChartModel hF hx, ιFinite hF hx ''ᵁ ⊤) ≃+*
      holomorphyRing {P : Place k F | x ∈ P.integers} :=
  ((ιFinite hF hx).appIso ⊤ ≪≫ Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv

/-- On the finite chart, the functions on `Spec k` pulled back along the structure morphism are
the constants of `𝒪_x`. -/
@[simp]
theorem finiteChartSectionsEquiv_appLE (a : Γ(Spec (.of k), ⊤)) :
    finiteChartSectionsEquiv hF hx ((twoChartModel hF hx ↘ Spec (.of k)).appLE ⊤ _ le_top a) =
      algebraMap k _ ((Scheme.ΓSpecIso (.of k)).hom a) := by
  suffices h : (twoChartModel hF hx ↘ Spec (.of k)).appLE ⊤ _ le_top ≫
        ((ιFinite hF hx).appIso ⊤).hom ≫ (Scheme.ΓSpecIso _).hom =
      (Scheme.ΓSpecIso (.of k)).hom ≫
        CommRingCat.ofHom (algebraMap k (holomorphyRing {P : Place k F | x ∈ P.integers})) from
    congr($h a)
  rw [← cancel_epi (Scheme.ΓSpecIso (.of k)).inv, Iso.inv_hom_id_assoc, Scheme.Hom.appIso_hom',
    reassoc_of% Scheme.Hom.appLE_comp_appLE (ιFinite hF hx)
    (twoChartModel hF hx ↘ Spec (.of k)) ⊤ (ιFinite hF hx ''ᵁ ⊤) ⊤ le_top
    (Scheme.Hom.preimage_image_eq _ _).ge]
  -- The composite of the chart with the structure morphism is `Spec` of the inclusion of `k`;
  -- the proof that `⊤` lies over `⊤` has to be generalized before rewriting it.
  generalize_proofs e
  revert e
  rw [ιFinite_over]
  intro e
  rw [show Scheme.Hom.appLE _ ⊤ ⊤ e = Scheme.Hom.appTop _ from Scheme.Hom.appLE_eq_app _,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

variable {hF hx}

/-- **The function field of `twoChartModel` is `F`**, as a `k`-algebra, for `x` transcendental
over `k`. It identifies the germ of a function on the finite chart with that function of `F`
(`TauCeti.AlgebraicGeometry.twoChartModel.functionFieldEquiv_germToFunctionField`). -/
noncomputable def functionFieldEquiv (hxt : Transcendental k x) :
    (twoChartModel hF hx).functionField ≃ₐ[k] F :=
  haveI := functionField_isFractionRing_of_isAffineOpen _ _ (isAffineOpen_image_ιFinite_top hF hx)
  haveI := isFractionRing_holomorphyRing_setOf_mem hF hxt
  AlgEquiv.ofRingEquiv (f := IsFractionRing.ringEquivOfRingEquiv (finiteChartSectionsEquiv hF hx))
    fun c ↦ by
      rw [Scheme.algebraMap_functionField_eq_baseRingToFunctionField,
        Scheme.baseRingToFunctionField_eq_comp_appLE k _ (ιFinite hF hx ''ᵁ ⊤),
        RingHom.comp_apply]
      -- `germToFunctionField` is by definition the algebra map of `Γ(X, U)` to `k(X)`.
      refine (IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _).trans ?_
      rw [CommRingCat.comp_apply, finiteChartSectionsEquiv_appLE, Iso.inv_hom_id_apply]
      exact (IsScalarTower.algebraMap_apply k _ F c).symm

/-- `TauCeti.AlgebraicGeometry.twoChartModel.functionFieldEquiv` sends the germ of a function on
the finite chart to the corresponding function of `F`. -/
@[simp]
theorem functionFieldEquiv_germToFunctionField (hxt : Transcendental k x)
    (a : Γ(twoChartModel hF hx, ιFinite hF hx ''ᵁ ⊤)) :
    functionFieldEquiv hxt ((twoChartModel hF hx).germToFunctionField _ a) =
      finiteChartSectionsEquiv hF hx a := by
  have := functionField_isFractionRing_of_isAffineOpen _ _ (isAffineOpen_image_ιFinite_top hF hx)
  have := isFractionRing_holomorphyRing_setOf_mem hF hxt
  -- `germToFunctionField` is by definition the algebra map of `Γ(X, U)` to `k(X)`.
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

end twoChartModel

end TauCeti.AlgebraicGeometry
