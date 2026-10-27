/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.RingTheory.Etale.Locus

/-!
# Unramified and étale at a point, read off from the stalk map

For a morphism of schemes `f : X ⟶ Y` and a point `x : X`, the Stacks Project calls `f`
*unramified at `x`* (Definition 29.36.1 (02G4)) if `x` has an open neighbourhood `U` such that
`U.ι ≫ f` is locally of finite type and formally unramified, and *étale at `x`* (Definition
29.37.1 (02GI)) if `x` has an open neighbourhood `U` such that `U.ι ≫ f` is étale. This file
shows that both conditions only depend on the stalk map `f.stalkMap x`:

* for `f` locally of finite type, `f` is unramified at `x` iff `f.stalkMap x` is formally
  unramified (`AlgebraicGeometry.Scheme.Hom.unramifiedAt_iff_stalkMap`);
* for `f` locally of finite presentation, `f` is étale at `x` iff `f.stalkMap x` is flat and
  formally unramified (`AlgebraicGeometry.Scheme.Hom.etaleAt_iff_stalkMap`, Stacks, Lemma
  29.37.15 (02GU), conditions (1) and (4)).

These are compared with Mathlib's affine pointwise notions: on affine opens `V ⊆ f⁻¹ U`, the stalk
map at `x` is formally unramified (resp. flat) iff `Γ(X, V)` is unramified over `Γ(Y, U)` at the
prime of `x` (resp. the localization there is flat), in parallel with Mathlib's
`AlgebraicGeometry.formallySmooth_stalkMap_iff`. For `Spec S ⟶ Spec R` this gives
`AlgebraicGeometry.Scheme.Hom.etaleAt_spec_iff` and
`AlgebraicGeometry.Scheme.Hom.unramifiedAt_spec_iff`: `Spec S ⟶ Spec R` is étale (resp.
unramified) at `q` exactly when `Algebra.IsEtaleAt R q` (resp. `Algebra.IsUnramifiedAt R q`).

The passage from the stalk to a neighbourhood follows Mathlib's
`AlgebraicGeometry.exists_smooth_of_formallySmooth_stalk`: Mathlib's
`Algebra.exists_formallyUnramified_of_isUnramifiedAt` and `Algebra.exists_etale_of_isEtaleAt`
spread the condition from the prime of `x` to a basic open `D(r)`. For étaleness the stalk
condition is first turned into `Algebra.IsEtaleAt` by
`Algebra.isEtaleAt_iff_flat_and_isUnramifiedAt`.

## References

* [The Stacks Project, Definition 29.36.1 (02G4)](https://stacks.math.columbia.edu/tag/02G4)
* [The Stacks Project, Definition 29.37.1 (02GI)](https://stacks.math.columbia.edu/tag/02GI)
* [The Stacks Project, Lemma 29.37.15 (02GU)](https://stacks.math.columbia.edu/tag/02GU)
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- On affine opens `x ∈ V ⊆ f⁻¹ U`, the stalk map of `f` at `x` is flat iff the localization of
`Γ(X, V)` at the prime of `x` is flat over `Γ(Y, U)`. -/
theorem flat_stalkMap_iff {f : X ⟶ Y} {x : X} (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens)
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.Flat ↔
      Module.Flat Γ(Y, U) (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  algebraize [(f.appLE U V hVU).hom]
  rw [RingHom.Flat.respectsIso.arrow_mk_iso_iff
    (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)]
  exact Localization.flat_localRingHom_iff _ _
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm

/-- On affine opens `x ∈ V ⊆ f⁻¹ U`, the stalk map of `f` at `x` is formally unramified iff
`Γ(X, V)` is unramified over `Γ(Y, U)` at the prime of `x`. -/
theorem formallyUnramified_stalkMap_iff {f : X ⟶ Y} {x : X} (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyUnramified ↔
      Algebra.IsUnramifiedAt Γ(Y, U) (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  algebraize [(f.appLE U V hVU).hom]
  rw [RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
    (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)]
  exact Localization.formallyUnramified_localRingHom_iff _ _
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The stalk map of `Spec S ⟶ Spec R` at `q` is flat iff `S_q` is flat over `R`. -/
theorem flat_stalkMap_specMap_iff (q : PrimeSpectrum S) :
    ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap q).hom.Flat ↔
      Module.Flat R (Localization.AtPrime q.asIdeal) := by
  have h := RingHom.Flat.respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap R S)) q)
  simp only [CommRingCat.hom_ofHom] at h
  exact h.trans (Localization.flat_localRingHom_iff _ _ _)

/-- The stalk map of `Spec S ⟶ Spec R` at `q` is formally unramified iff `S` is unramified over
`R` at `q`. -/
theorem formallyUnramified_stalkMap_specMap_iff (q : PrimeSpectrum S) :
    ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap q).hom.FormallyUnramified ↔
      Algebra.IsUnramifiedAt R q.asIdeal := by
  have h := RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap R S)) q)
  simp only [CommRingCat.hom_ofHom] at h
  exact h.trans (Localization.formallyUnramified_localRingHom_iff _ _ _)

/-- For an open immersion `i`, a ring-hom property `Q` stable under isomorphisms holds for the
stalk map of `i ≫ f` at `x` iff it holds for the stalk map of `f` at `i x`. -/
theorem _root_.RingHom.RespectsIso.stalkMap_comp_isOpenImmersion_iff
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQ : RingHom.RespectsIso Q) {U : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (f : X ⟶ Y)
    (x : U) : Q ((i ≫ f).stalkMap x).hom ↔ Q (f.stalkMap (i x)).hom := by
  refine Iff.trans ?_ (hQ.cancel_right_isIso _ (i.stalkMap x))
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
  -- The stalks at `(i ≫ f) x` and `f (i x)` agree definitionally, but not reducibly.
  exact Iff.rfl

/-- On an affine open `V`, a point `x ∈ V` lies in the basic open of a section `r` iff `r` is not
in the prime ideal of `Γ(X, V)` corresponding to `x`. -/
theorem IsAffineOpen.mem_basicOpen_iff_notMem_primeIdealOf {x : X} {V : X.Opens}
    (hV : IsAffineOpen V) (hx : x ∈ V) (r : Γ(X, V)) :
    x ∈ X.basicOpen r ↔ r ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  exact (X.mem_basicOpen r x hx).trans
    (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) _ r)

/-- Let `x ∈ V ⊆ f⁻¹ U` with `U` and `V` affine, and let `P` be a morphism property attached to
the ring-hom property `Q`. If `Q` holds for `Γ(Y, U) → Γ(X, V)_r`, then `P` holds for the
restriction `D(r) ⟶ U` of `f`. -/
theorem HasRingHomProperty.resLE_basicOpen (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q]
    {f : X ⟶ Y} {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (r : Γ(X, V))
    (H : letI := (f.appLE U V hVU).hom.toAlgebra
      Q (algebraMap Γ(Y, U) (Localization.Away r))) :
    P (f.resLE U (X.basicOpen r) ((X.basicOpen_le r).trans hVU)) := by
  algebraize [(f.appLE U V hVU).hom]
  have : IsAffine U := hU
  have : IsAffine (X.basicOpen r) := hV.basicOpen r
  have hQ := (HasRingHomProperty.isLocal_ringHomProperty P).respectsIso
  rw [HasRingHomProperty.iff_of_isAffine (P := P)]
  refine (hQ.arrow_mk_iso_iff (arrowResLEAppIso f U _ _)).mpr ?_
  have := hV.isLocalization_basicOpen r
  -- Transport `H` along `Γ(X, V)_r ≃ Γ(X, D(r))` and identify the composite with `f.appLE`.
  convert hQ.1 _ (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv H
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply,
    IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization.Away r),
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
    AlgEquiv.commutes, RingHom.algebraMap_toAlgebra]
  rw [← f.appLE_map hVU (homOfLE (X.basicOpen_le r)).op, CommRingCat.comp_apply]

namespace Scheme.Hom

/-- A morphism locally of finite type is unramified at `x` in the sense of Stacks, Definition
29.36.1 (02G4), iff its stalk map at `x` is formally unramified. -/
@[stacks 02G4 "equivalence with the stalk form"]
theorem unramifiedAt_iff_stalkMap (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) :
    (∃ U : X.Opens, x ∈ U ∧ LocallyOfFiniteType (U.ι ≫ f) ∧ FormallyUnramified (U.ι ≫ f)) ↔
      (f.stalkMap x).hom.FormallyUnramified := by
  refine ⟨fun ⟨U, hxU, _, _⟩ ↦ ?_, fun H ↦ ?_⟩
  · exact (RingHom.FormallyUnramified.respectsIso.stalkMap_comp_isOpenImmersion_iff U.ι f
      ⟨x, hxU⟩).mp (FormallyUnramified.stalkMap _ _)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finiteType_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have := (formallyUnramified_stalkMap_iff U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := Γ(Y, U))
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have := HasRingHomProperty.resLE_basicOpen @FormallyUnramified hU hV hVU r
    (RingHom.formallyUnramified_algebraMap.mpr hr)
  refine ⟨X.basicOpen r, (hV.mem_basicOpen_iff_notMem_primeIdealOf hxV r).mpr hrx,
    inferInstance, ?_⟩
  rw [← f.resLE_comp_ι ((X.basicOpen_le r).trans hVU)]
  exact MorphismProperty.comp_mem _ _ _ ‹_› inferInstance

/-- A morphism locally of finite presentation is étale at `x` in the sense of Stacks, Definition
29.37.1 (02GI), iff its stalk map at `x` is flat and formally unramified. -/
@[stacks 02GU "(1) ⇔ (4)"]
theorem etaleAt_iff_stalkMap (f : X ⟶ Y) [LocallyOfFinitePresentation f] (x : X) :
    (∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f)) ↔
      (f.stalkMap x).hom.Flat ∧ (f.stalkMap x).hom.FormallyUnramified := by
  refine ⟨fun ⟨U, hxU, _⟩ ↦ ⟨?_, ?_⟩, fun ⟨hflat, hfu⟩ ↦ ?_⟩
  · exact (RingHom.Flat.respectsIso.stalkMap_comp_isOpenImmersion_iff U.ι f
      ⟨x, hxU⟩).mp (Flat.stalkMap _ _)
  · exact (RingHom.FormallyUnramified.respectsIso.stalkMap_comp_isOpenImmersion_iff U.ι f
      ⟨x, hxU⟩).mp (FormallyUnramified.stalkMap _ _)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : Algebra.IsEtaleAt Γ(Y, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    (Algebra.isEtaleAt_iff_flat_and_isUnramifiedAt _).mpr
      ⟨(flat_stalkMap_iff U hU V hV hVU hxV).mp hflat,
        (formallyUnramified_stalkMap_iff U hU V hV hVU hxV).mp hfu⟩
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_etale_of_isEtaleAt (R := Γ(Y, U))
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have := HasRingHomProperty.resLE_basicOpen @Etale hU hV hVU r (RingHom.etale_algebraMap.mpr hr)
  refine ⟨X.basicOpen r, (hV.mem_basicOpen_iff_notMem_primeIdealOf hxV r).mpr hrx, ?_⟩
  rw [← f.resLE_comp_ι ((X.basicOpen_le r).trans hVU)]
  infer_instance

/-- For a finitely presented `R`-algebra `S`, the morphism `Spec S ⟶ Spec R` is étale at `q` in
the sense of Stacks, Definition 29.37.1 (02GI), iff `S` is étale over `R` at `q` in Mathlib's
sense `Algebra.IsEtaleAt`. -/
theorem etaleAt_spec_iff [Algebra.FinitePresentation R S] (q : PrimeSpectrum S) :
    (∃ U : (Spec (.of S)).Opens,
        q ∈ U ∧ Etale (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))) ↔
      Algebra.IsEtaleAt R q.asIdeal := by
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finitePresentation_algebraMap.mpr ‹_›)
  rw [Algebra.isEtaleAt_iff_flat_and_isUnramifiedAt]
  exact (etaleAt_iff_stalkMap (Spec.map (CommRingCat.ofHom (algebraMap R S))) q).trans <|
    and_congr (flat_stalkMap_specMap_iff q) (formallyUnramified_stalkMap_specMap_iff q)

/-- For a finite type `R`-algebra `S`, the morphism `Spec S ⟶ Spec R` is unramified at `q` in
the sense of Stacks, Definition 29.36.1 (02G4), iff `S` is unramified over `R` at `q` in
Mathlib's sense `Algebra.IsUnramifiedAt`. -/
theorem unramifiedAt_spec_iff [Algebra.FiniteType R S] (q : PrimeSpectrum S) :
    (∃ U : (Spec (.of S)).Opens, q ∈ U ∧
        LocallyOfFiniteType (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) ∧
        FormallyUnramified (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))) ↔
      Algebra.IsUnramifiedAt R q.asIdeal := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr ‹_›)
  exact (unramifiedAt_iff_stalkMap (Spec.map (CommRingCat.ofHom (algebraMap R S))) q).trans
    (formallyUnramified_stalkMap_specMap_iff q)

end Scheme.Hom

end AlgebraicGeometry
