/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import TauCeti.AlgebraicGeometry.AffineScheme
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
public import TauCeti.AlgebraicGeometry.Restrict
public import TauCeti.RingTheory.Etale.Locus
public import TauCeti.RingTheory.QuasiFinite.Localization
public import TauCeti.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Unramified, étale and quasi-finite at a point, read off from the stalk map

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

When the local ring of `Y` at `f x` is a Dedekind domain, for instance a discrete valuation ring,
and the local ring of `X` at `x` is a domain but not a field, flatness of the stalk map is
automatic, so `f` is étale at `x` as soon as its stalk map is formally unramified
(`AlgebraicGeometry.Scheme.Hom.exists_etale_of_formallyUnramified_stalkMap_of_isDedekindDomain`).
This is purity of the branch locus in dimension one, the case from which the proof of Stacks,
Lemma 58.21.4 (0BMB) starts.

These are compared with Mathlib's affine pointwise notions: on affine opens `V ⊆ f⁻¹ U`, the stalk
map at `x` is formally unramified iff `Γ(X, V)` is unramified over `Γ(Y, U)` at the prime of `x`
(`AlgebraicGeometry.formallyUnramified_stalkMap_iff`), in parallel with Mathlib's
`AlgebraicGeometry.formallySmooth_stalkMap_iff` and with the flat analogue
`AlgebraicGeometry.flat_stalkMap_iff`. For `Spec S ⟶ Spec R` this gives
`AlgebraicGeometry.Scheme.Hom.etaleAt_spec_iff` and
`AlgebraicGeometry.Scheme.Hom.unramifiedAt_spec_iff`: `Spec S ⟶ Spec R` is étale (resp.
unramified) at `q` exactly when `Algebra.IsEtaleAt R q` (resp. `Algebra.IsUnramifiedAt R q`).

Mathlib defines quasi-finiteness at `x` in stalk form, `f.QuasiFiniteAt x`, and shows that it
implies quasi-finiteness of `Γ(X, V)` over `Γ(Y, U)` at the prime of `x` for affine opens
`x ∈ V ⊆ f⁻¹ U` (`AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt.quasiFiniteAt`). The converse is
`AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_of_appLE`. With both directions,
`AlgebraicGeometry.Scheme.Hom.exists_appLE_quasiFiniteAt_iff` shows that `f` is quasi-finite at
`x` in the sense of the Stacks Project, Tag 01TD, iff `f` is locally of finite type near `x` and
`f.QuasiFiniteAt x`. For `Spec S ⟶ Spec R`,
`AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_spec_iff` identifies quasi-finiteness at `q` with
`Algebra.QuasiFiniteAt R q`.

The passage from the stalk to a neighbourhood follows Mathlib's
`AlgebraicGeometry.exists_smooth_of_formallySmooth_stalk`: Mathlib's
`Algebra.exists_formallyUnramified_of_isUnramifiedAt` and `Algebra.exists_etale_of_isEtaleAt`
spread the condition from the prime of `x` to a basic open `D(r)`, and
`AlgebraicGeometry.HasRingHomProperty.exists_ι_comp_of_away` turns this into an open
neighbourhood of `x`. For étaleness the stalk condition is first turned into `Algebra.IsEtaleAt` by
`Algebra.isEtaleAt_iff_flat_and_isUnramifiedAt`.

## References

* [The Stacks Project, Tag 01TD](https://stacks.math.columbia.edu/tag/01TD)
* [The Stacks Project, Definition 29.36.1 (02G4)](https://stacks.math.columbia.edu/tag/02G4)
* [The Stacks Project, Definition 29.37.1 (02GI)](https://stacks.math.columbia.edu/tag/02GI)
* [The Stacks Project, Lemma 29.37.15 (02GU)](https://stacks.math.columbia.edu/tag/02GU)
* [The Stacks Project, Lemma 58.21.4 (0BMB)](https://stacks.math.columbia.edu/tag/0BMB)
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

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

/-- Let `V ⊆ f⁻¹ U` with `U` and `V` affine, and let `P` be a morphism property attached to the
ring-hom property `Q`. If `Q` holds for `Γ(Y, U) → Γ(X, V)_r`, then `P` holds for the restriction
`D(r) ⟶ U` of `f`. -/
theorem HasRingHomProperty.resLE_basicOpen (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q]
    {f : X ⟶ Y} {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (r : Γ(X, V))
    (H : Q ((algebraMap Γ(X, V) (Localization.Away r)).comp (f.appLE U V hVU).hom)) :
    P (f.resLE U (X.basicOpen r) ((X.basicOpen_le r).trans hVU)) := by
  have hQ := (HasRingHomProperty.isLocal_ringHomProperty P).respectsIso
  refine (resLE_iff P hU (hV.basicOpen r) _).mpr ?_
  have := hV.isLocalization_basicOpen r
  -- Transport `H` along `Γ(X, V)_r ≃ Γ(X, D(r))` and identify the composite with `f.appLE`.
  convert hQ.1 _ (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv H
  ext a
  simp [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply]

/-- Let `x ∈ V ⊆ f⁻¹ U` with `U` and `V` affine, and let `P` be a morphism property attached to
the ring-hom property `Q`, stable under composition and containing identities. If `Q` holds for
`Γ(Y, U) → Γ(X, V)_r` for some `r` not in the prime of `x`, then `x` has an open neighbourhood
`W` with `P (W.ι ≫ f)`, namely `W = D(r)`. -/
theorem HasRingHomProperty.exists_ι_comp_of_away (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q]
    [P.IsMultiplicative] {f : X ⟶ Y} {x : X} {U : Y.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V)
    (r : Γ(X, V)) (hr : r ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal)
    (H : Q ((algebraMap Γ(X, V) (Localization.Away r)).comp (f.appLE U V hVU).hom)) :
    ∃ W : X.Opens, x ∈ W ∧ P (W.ι ≫ f) := by
  refine ⟨X.basicOpen r, (hV.mem_basicOpen_iff_notMem_primeIdealOf hx r).mpr hr, ?_⟩
  rw [← f.resLE_comp_ι ((X.basicOpen_le r).trans hVU)]
  exact P.comp_mem _ _ (resLE_basicOpen P hU hV hVU r H)
    (IsZariskiLocalAtSource.of_isOpenImmersion _)

namespace Scheme.Hom

/-- If `i ≫ f` is formally unramified for an open immersion `i`, the stalk map of `f` at `i x` is
formally unramified. -/
theorem formallyUnramified_stalkMap_of_isOpenImmersion_comp (f : X ⟶ Y) {U : Scheme.{u}}
    (i : U ⟶ X) [IsOpenImmersion i] (x : U) [FormallyUnramified (i ≫ f)] :
    (f.stalkMap (i x)).hom.FormallyUnramified :=
  (RingHom.FormallyUnramified.respectsIso.stalkMap_comp_isOpenImmersion_iff i f x).mp
    (FormallyUnramified.stalkMap _ _)

/-- A morphism locally of finite type is unramified at `x` in the sense of Stacks, Definition
29.36.1 (02G4), iff its stalk map at `x` is formally unramified. -/
@[stacks 02G4 "equivalence with the stalk form"]
theorem unramifiedAt_iff_stalkMap (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) :
    (∃ U : X.Opens, x ∈ U ∧ LocallyOfFiniteType (U.ι ≫ f) ∧ FormallyUnramified (U.ι ≫ f)) ↔
      (f.stalkMap x).hom.FormallyUnramified := by
  refine ⟨fun ⟨U, hxU, _, _⟩ ↦ ?_, fun H ↦ ?_⟩
  · exact formallyUnramified_stalkMap_of_isOpenImmersion_comp f U.ι ⟨x, hxU⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finiteType_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have := (formallyUnramified_stalkMap_iff U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := Γ(Y, U))
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  obtain ⟨W, hxW, hW⟩ := HasRingHomProperty.exists_ι_comp_of_away @FormallyUnramified hU hV hVU
    hxV r hrx (RingHom.formallyUnramified_algebraMap.mpr hr)
  exact ⟨W, hxW, inferInstance, hW⟩

/-- A morphism locally of finite presentation is étale at `x` in the sense of Stacks, Definition
29.37.1 (02GI), iff its stalk map at `x` is flat and formally unramified. -/
@[stacks 02GU "(1) ⇔ (4)"]
theorem etaleAt_iff_stalkMap (f : X ⟶ Y) [LocallyOfFinitePresentation f] (x : X) :
    (∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f)) ↔
      (f.stalkMap x).hom.Flat ∧ (f.stalkMap x).hom.FormallyUnramified := by
  refine ⟨fun ⟨U, hxU, _⟩ ↦ ⟨?_, ?_⟩, fun ⟨hflat, hfu⟩ ↦ ?_⟩
  · exact (RingHom.Flat.respectsIso.stalkMap_comp_isOpenImmersion_iff U.ι f
      ⟨x, hxU⟩).mp (Flat.stalkMap _ _)
  · exact formallyUnramified_stalkMap_of_isOpenImmersion_comp f U.ι ⟨x, hxU⟩
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
  exact HasRingHomProperty.exists_ι_comp_of_away @Etale hU hV hVU hxV r hrx
    (RingHom.etale_algebraMap.mpr hr)

/-- **Purity in dimension one.** Let `f` be locally of finite presentation, for instance locally
of finite type with `Y` locally Noetherian, and let `x : X` be a point at which the local ring of
`X` is a domain but not a field (so `x` is not the generic point of an irreducible component of
`X`), while the local ring of `Y` at `f x` is a Dedekind domain, for instance a discrete valuation
ring. If the stalk map of `f` at `x` is formally unramified, then `f` is étale on an open
neighbourhood of `x`. -/
theorem exists_etale_of_formallyUnramified_stalkMap_of_isDedekindDomain (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (x : X) [IsDedekindDomain (Y.presheaf.stalk (f x))]
    [IsDomain (X.presheaf.stalk x)] (hx : ¬IsField (X.presheaf.stalk x))
    (hfu : (f.stalkMap x).hom.FormallyUnramified) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  refine (etaleAt_iff_stalkMap f x).mpr ⟨?_, hfu⟩
  have := LocallyOfFiniteType.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  -- The algebra structure is that of the stalk map, which is a local homomorphism.
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  -- The stalk at `x` is torsion-free over the Dedekind domain `𝒪_{Y, f x}`, hence flat over it.
  have := Algebra.FormallyUnramified.faithfulSMul_of_not_isField
    (R := Y.presheaf.stalk (f x)) hx
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

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

/-- Let `x ∈ V ⊆ f⁻¹ U` with `U` and `V` affine. If `Γ(X, V)` is quasi-finite over `Γ(Y, U)` at
the prime of `x`, then `f` is quasi-finite at `x`. This is the converse of Mathlib's
`AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt.quasiFiniteAt`. -/
theorem quasiFiniteAt_of_appLE {f : X ⟶ Y} {x : X} {V : X.Opens} (hV : IsAffineOpen V)
    {U : Y.Opens} (hU : IsAffineOpen U) (hVU : V ≤ f ⁻¹ᵁ U) (hxV : x ∈ V)
    (h : (f.appLE U V hVU).hom.QuasiFiniteAt (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) :
    f.QuasiFiniteAt x := by
  algebraize [(f.appLE U V hVU).hom]
  rw [QuasiFiniteAt, RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff
    (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hxV)]
  exact (Localization.quasiFinite_localRingHom_iff _ _
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV).1).symm).mpr h

/-- The morphism `Spec S ⟶ Spec R` is quasi-finite at `q` iff `S` is quasi-finite over `R` at
`q` in Mathlib's sense `Algebra.QuasiFiniteAt`. -/
theorem quasiFiniteAt_spec_iff (q : PrimeSpectrum S) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).QuasiFiniteAt q ↔
      Algebra.QuasiFiniteAt R q.asIdeal := by
  have h := RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap R S)) q)
  simp only [CommRingCat.hom_ofHom] at h
  exact h.trans (Localization.quasiFinite_localRingHom_iff _ _ _)

/-- A morphism `f` is quasi-finite at `x` in the sense of the Stacks Project, Tag 01TD, that is,
there are affine opens `x ∈ V ⊆ f⁻¹ U` such that `Γ(X, V)` is of finite type over `Γ(Y, U)` and
quasi-finite over it at the prime of `x`, iff `f` is locally of finite type on an open
neighbourhood of `x` and quasi-finite at `x` in Mathlib's stalk form `Scheme.Hom.QuasiFiniteAt`.

Quasi-finiteness at a prime is Mathlib's `Algebra.QuasiFiniteAt`; for algebras of finite type it
agrees with the Stacks Project's notion (the prime is isolated in its fibre) by Mathlib's
`Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`. -/
@[stacks 01TD "equivalence with the stalk form"]
theorem exists_appLE_quasiFiniteAt_iff (f : X ⟶ Y) (x : X) :
    (∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
        (hVU : V ≤ f ⁻¹ᵁ U) (hxV : x ∈ V), (f.appLE U V hVU).hom.FiniteType ∧
          (f.appLE U V hVU).hom.QuasiFiniteAt (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) ↔
      (∃ W : X.Opens, x ∈ W ∧ LocallyOfFiniteType (W.ι ≫ f)) ∧ f.QuasiFiniteAt x := by
  refine ⟨fun ⟨U, hU, V, hV, hVU, hxV, hft, hqf⟩ ↦
    ⟨⟨V, hxV, ?_⟩, quasiFiniteAt_of_appLE hV hU hVU hxV hqf⟩, fun ⟨⟨W, hxW, _⟩, hqf⟩ ↦ ?_⟩
  · have := (HasRingHomProperty.resLE_iff @LocallyOfFiniteType hU hV hVU).mpr hft
    rw [← f.resLE_comp_ι hVU]
    infer_instance
  obtain ⟨_, ⟨U : Y.Opens, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, hVWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_inter hxW hxU) (W.2.inter (U.2.preimage f.continuous))
  have hVU : V ≤ f ⁻¹ᵁ U := fun _ hy ↦ (hVWU hy).2
  -- `V.ι ≫ f` factors through `W.ι ≫ f`, hence so does the restriction `V ⟶ U` of `f`.
  have : LocallyOfFiniteType (f.resLE U V hVU ≫ U.ι) := by
    rw [f.resLE_comp_ι hVU, ← X.homOfLE_ι fun _ hy ↦ (hVWU hy).1, Category.assoc]
    infer_instance
  have := locallyOfFiniteType_of_comp (f.resLE U V hVU) U.ι
  exact ⟨U, hU, V, hV, hVU, hxV, (HasRingHomProperty.resLE_iff @LocallyOfFiniteType hU hV hVU).mp
    this, hqf.quasiFiniteAt hV hU hVU hxV⟩

end Scheme.Hom

end AlgebraicGeometry
