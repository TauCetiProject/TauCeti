/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import TauCeti.AlgebraicGeometry.AffineScheme.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
public import TauCeti.AlgebraicGeometry.Pullback.SpecMap
public import TauCeti.AlgebraicGeometry.Restrict
public import TauCeti.RingTheory.Etale.Locus
public import TauCeti.RingTheory.QuasiFinite.Localization
public import TauCeti.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Unramified.Field
import TauCeti.RingTheory.Flat.Noetherian
import TauCeti.RingTheory.Unramified.BaseChange
import TauCeti.RingTheory.Unramified.Normal

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

Both stalk conditions descend along flat morphisms: for `g : X' ⟶ X` with flat stalk map at
`x'`, if the stalk map of `g ≫ f` at `x'` is flat (resp. formally unramified, with `f` and
`g ≫ f` locally of finite type), then so is the stalk map of `f` at `g x'`; the flat case is
`AlgebraicGeometry.Scheme.Hom.flat_stalkMap_of_comp`. Hence if `f` is locally of finite
presentation, `g` is flat and surjective and `g ≫ f` is étale, then `f` is étale
(`AlgebraicGeometry.Etale.of_comp_surjective`), because a morphism étale on an open
neighbourhood of every point is étale
(`AlgebraicGeometry.IsZariskiLocalAtSource.of_forall_exists_ι_comp`). For
an étale surjective `g` this is the statement of Stacks, Lemma 35.31.1 (036W), that étaleness is
étale local on the source, for `f` locally of finite presentation.
Similarly, if `g` is flat and surjective, `f` and `g ≫ f` are locally of finite type and `g ≫ f`
is formally unramified, then `f` is formally unramified
(`AlgebraicGeometry.FormallyUnramified.of_comp_surjective`). No quasi-compactness assumption on
`g` is needed for either descent statement.

In a commutative square with étale vertical maps, the horizontal maps are étale at
corresponding points simultaneously, provided the bottom map is locally of finite presentation
(`AlgebraicGeometry.Scheme.Hom.exists_etale_iff_of_etale_square`). Neither a cartesian square nor
surjective vertical maps are needed. This permits passage to finite local models in purity of
the branch locus (Stacks, Lemma 58.21.4 (0BMB)).

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

For `f` locally of finite type over a locally Noetherian `Y` whose local ring at `f x` is a normal
domain, a formally unramified stalk map at `x` already makes `f` étale near `x` as soon as
`dim 𝒪_{Y, f x} ≤ dim 𝒪_{X, x}`
(`AlgebraicGeometry.Scheme.Hom.exists_etale_of_formallyUnramified_stalkMap_of_ringKrullDim_le`,
the scheme form of `Algebra.IsEtaleAt.of_isUnramifiedAt_of_height_le`).

Mathlib defines quasi-finiteness at `x` in stalk form, `f.QuasiFiniteAt x`, and shows that it
implies quasi-finiteness of `Γ(X, V)` over `Γ(Y, U)` at the prime of `x` for affine opens
`x ∈ V ⊆ f⁻¹ U` (`AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt.quasiFiniteAt`). The converse is
`AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_of_appLE`. With both directions,
`AlgebraicGeometry.Scheme.Hom.exists_appLE_quasiFiniteAt_iff` shows that `f` is quasi-finite at
`x` in the sense of the Stacks Project, Tag 01TD, iff `f` is locally of finite type near `x` and
`f.QuasiFiniteAt x`. For `Spec S ⟶ Spec R`,
`AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_spec_iff` identifies quasi-finiteness at `q` with
`Algebra.QuasiFiniteAt R q`.

Viewing the stalk map as an algebra `𝒪_{Y, f x} → 𝒪_{X, x}`, it is local
(`AlgebraicGeometry.Scheme.Hom.isLocalHom_stalkMap_toAlgebra`), essentially of finite type when `f`
is locally of finite type (`AlgebraicGeometry.Scheme.Hom.essFiniteType_stalkMap_toAlgebra`), and
formally unramified when `f` is
(`AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_toAlgebra`). When `f` is moreover flat,
the stalk map is faithfully flat, so `𝒪_{Y, f x}` is Noetherian exactly when `𝒪_{X, x}` is
(`AlgebraicGeometry.Scheme.Hom.isNoetherianRing_stalk_iff_of_flat_of_locallyOfFiniteType`).
For `f` formally unramified and locally of finite type, the maximal ideal of `𝒪_{Y, f x}`
generates the maximal ideal of `𝒪_{X, x}` along the stalk map
(`AlgebraicGeometry.Scheme.Hom.map_maximalIdeal_stalkMap_of_formallyUnramified`).

Formal unramifiedness of stalk maps is also preserved under arbitrary pullback
(`AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_of_isPullback`), descends along flat
stalk maps and flat base change
(`AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_iff_of_isPullback_of_flat_stalkMap`,
`AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_iff_of_isPullback`), and holds at the
generic point of a dominant morphism between integral schemes whenever the induced function-field
extension is separable
(`AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_genericPoint_of_isSeparable`).

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
* [The Stacks Project, Lemma 35.31.1 (036W)](https://stacks.math.columbia.edu/tag/036W)
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
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).asIdeal).symm

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

/-- For an open immersion `j`, a ring-hom property `Q` stable under isomorphisms holds for the
stalk map of `h ≫ j` at `q` iff it holds for the stalk map of `h` at `q`. -/
theorem _root_.RingHom.RespectsIso.stalkMap_comp_isOpenImmersion_right_iff
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQ : RingHom.RespectsIso Q) {X₀ Y₀ Y : Scheme.{u}} (h : X₀ ⟶ Y₀) (j : Y₀ ⟶ Y)
    [IsOpenImmersion j] (q : X₀) :
    Q ((h ≫ j).stalkMap q).hom ↔ Q (h.stalkMap q).hom :=
  Iff.trans (by rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]; exact Iff.rfl)
    (hQ.cancel_left_isIso (j.stalkMap (h q)) (h.stalkMap q))

/-- In a commutative square `ι ≫ f' = h ≫ j` with open immersions `ι` and `j`, any
isomorphism-invariant ring-hom property holds for `f'.stalkMap (ι q)` iff it holds for
`h.stalkMap q`. -/
theorem _root_.RingHom.RespectsIso.stalkMap_iff_of_isOpenImmersion_square
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQ : RingHom.RespectsIso Q) {X₀ Y₀ X' Y' : Scheme.{u}} (ι : X₀ ⟶ X') (f' : X' ⟶ Y')
    (h : X₀ ⟶ Y₀) (j : Y₀ ⟶ Y') [IsOpenImmersion ι] [IsOpenImmersion j]
    (e : ι ≫ f' = h ≫ j) (q : X₀) :
    Q (f'.stalkMap (ι q)).hom ↔ Q (h.stalkMap q).hom :=
  (hQ.stalkMap_comp_isOpenImmersion_iff ι f' q).symm.trans <|
    (iff_of_eq (congrArg (fun k : X₀ ⟶ Y' ↦ Q (k.stalkMap q).hom) e)).trans
      (hQ.stalkMap_comp_isOpenImmersion_right_iff h j q)

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
  refine ⟨X.basicOpen r, (hV.mem_basicOpen_iff_notMem_primeIdealOf ⟨x, hx⟩ r).mpr hr, ?_⟩
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
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.is_open'.preimage f.continuous)
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
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.is_open'.preimage f.continuous)
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

/-- Formal unramifiedness of stalk maps descends along flat morphisms: for `f` and `g ≫ f` locally
of finite type, if `g` has flat stalk map at `x'` and `g ≫ f` has formally unramified stalk map at
`x'`, then `f` has formally unramified stalk map at `g x'`. -/
theorem formallyUnramified_stalkMap_of_comp {X' : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyOfFiniteType (g ≫ f)] (x' : X')
    (hg : (g.stalkMap x').hom.Flat) (h : ((g ≫ f).stalkMap x').hom.FormallyUnramified) :
    (f.stalkMap (g x')).hom.FormallyUnramified := by
  have h' : ((g.stalkMap x').hom.comp (f.stalkMap (g x')).hom).FormallyUnramified := by
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
    -- The stalks at `(g ≫ f) x'` and `f (g x')` agree definitionally, but not reducibly.
    exact h
  have he : ((g.stalkMap x').hom.comp (f.stalkMap (g x')).hom).EssFiniteType := by
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
    -- As above, the two stalks of `Y` agree definitionally.
    exact LocallyOfFiniteType.stalkMap (g ≫ f) x'
  have := LocallyOfFiniteType.stalkMap f (g x')
  algebraize [(f.stalkMap (g x')).hom, (g.stalkMap x').hom,
    (g.stalkMap x').hom.comp (f.stalkMap (g x')).hom]
  -- The algebra structures are those of the stalk maps, which are local homomorphisms.
  have : IsLocalHom (algebraMap (X.presheaf.stalk (g x')) (X'.presheaf.stalk x')) :=
    inferInstanceAs (IsLocalHom (g.stalkMap x').hom)
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f (g x'))) (X.presheaf.stalk (g x'))) :=
    inferInstanceAs (IsLocalHom (f.stalkMap (g x')).hom)
  exact Algebra.FormallyUnramified.of_flat_of_formallyUnramified (C := X'.presheaf.stalk x')

/-- In a commutative square with flat, formally unramified source map and formally
unramified target map, formal unramifiedness of the horizontal stalk maps is equivalent at
corresponding points. The source map and bottom horizontal map are locally of finite type;
no finite-type assumption is needed on the top horizontal map or the target map. -/
theorem formallyUnramified_stalkMap_iff_of_flat_square {X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (e : X' ⟶ X) (b : Y' ⟶ Y)
    [LocallyOfFiniteType f] [LocallyOfFiniteType e] [Flat e]
    [FormallyUnramified e] [FormallyUnramified b]
    (w : e ≫ f = f' ≫ b) (x' : X') :
    (f'.stalkMap x').hom.FormallyUnramified ↔
      (f.stalkMap (e x')).hom.FormallyUnramified := by
  -- Transport the predicate, including its source stalk, along the equality of composites.
  have hw := congrArg (fun k : X' ⟶ Y ↦ (k.stalkMap x').hom.FormallyUnramified) w
  constructor
  · intro h
    have hc := (FormallyUnramified.stalkMap b (f' x')).comp h
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp] at hc
    exact formallyUnramified_stalkMap_of_comp e f x' (Flat.stalkMap e x') (hw.mpr hc)
  · intro h
    have hc := h.comp (FormallyUnramified.stalkMap e x')
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp] at hc
    have hc' := hw.mp hc
    rw [Scheme.Hom.stalkMap_comp] at hc'
    exact RingHom.FormallyUnramified.of_comp hc'

/-- **Étaleness descends along flat morphisms.** Let `f` be locally of finite presentation and
`g : X' ⟶ X` a morphism with flat stalk map at `x'` such that `g ≫ f` is étale. Then `f` is étale
on an open neighbourhood of `g x'`. -/
theorem exists_etale_of_etale_comp {X' : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [Etale (g ≫ f)] (x' : X') (hg : (g.stalkMap x').hom.Flat) :
    ∃ U : X.Opens, g x' ∈ U ∧ Etale (U.ι ≫ f) :=
  (etaleAt_iff_stalkMap f (g x')).mpr
    ⟨flat_stalkMap_of_comp g f x' hg (Flat.stalkMap _ _),
      formallyUnramified_stalkMap_of_comp g f x' hg (FormallyUnramified.stalkMap _ _)⟩

/-- In a commutative square with étale vertical maps, the horizontal maps are étale
at corresponding points simultaneously. No cartesian or surjectivity hypothesis is needed. -/
theorem exists_etale_iff_of_etale_square {X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (e : X' ⟶ X) (b : Y' ⟶ Y)
    [LocallyOfFinitePresentation f] [Etale e] [Etale b]
    (w : e ≫ f = f' ≫ b) (x' : X') :
    (∃ U : X.Opens, e x' ∈ U ∧ Etale (U.ι ≫ f)) ↔
      (∃ U' : X'.Opens, x' ∈ U' ∧ Etale (U'.ι ≫ f')) := by
  constructor
  · rintro ⟨U, hxU, _⟩
    refine ⟨e ⁻¹ᵁ U, hxU, ?_⟩
    have hcomp : ((e ⁻¹ᵁ U).ι ≫ f') ≫ b = (e ∣_ U) ≫ U.ι ≫ f := by
      rw [Category.assoc, ← w, morphismRestrict_ι_assoc]
    have : Etale (((e ⁻¹ᵁ U).ι ≫ f') ≫ b) := by
      rw [hcomp]
      infer_instance
    exact Etale.of_comp _ b
  · rintro ⟨U', hxU', _⟩
    have hcomp : (U'.ι ≫ e) ≫ f = (U'.ι ≫ f') ≫ b := by
      simp only [Category.assoc, w]
    have : Etale ((U'.ι ≫ e) ≫ f) := by
      rw [hcomp]
      infer_instance
    exact exists_etale_of_etale_comp (U'.ι ≫ e) f ⟨x', hxU'⟩
      (Flat.stalkMap _ _)

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

/-- **Unramified over a normal base of the same dimension implies étale** (compare SGA 1,
Exposé I, Théorème 9.5 (ii)). Let `f` be locally of finite type over a locally Noetherian
`Y`, with formally unramified stalk map at `x`. If the local ring of `Y` at `f x` is a normal
domain of dimension at most that of the local ring of `X` at `x`, then `f` is étale on an open
neighbourhood of `x`. -/
theorem exists_etale_of_formallyUnramified_stalkMap_of_ringKrullDim_le (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] {x : X}
    [IsDomain (Y.presheaf.stalk (f x))] [IsIntegrallyClosed (Y.presheaf.stalk (f x))]
    (hfu : (f.stalkMap x).hom.FormallyUnramified)
    (hdim : ringKrullDim (Y.presheaf.stalk (f x)) ≤ ringKrullDim (X.presheaf.stalk x)) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.is_open'.preimage f.continuous)
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have := f.finiteType_appLE hU hV hVU
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  -- Transport the hypotheses on the stalks to the localizations of `Γ(Y, U) → Γ(X, V)`.
  set q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  set p := (hU.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal
  have : q.LiesOver p :=
    ⟨(congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV)).symm⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  let := Y.presheaf.algebra_section_stalk ⟨f x, hVU hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  have := hU.isLocalization_stalk ⟨f x, hVU hxV⟩
  let e := IsLocalization.algEquiv p.primeCompl (Y.presheaf.stalk (f x)) (Localization.AtPrime p)
  have : IsDomain (Localization.AtPrime p) := e.symm.toMulEquiv.isDomain _
  have : IsIntegrallyClosed (Localization.AtPrime p) := .of_equiv e.toRingEquiv
  have : Algebra.IsUnramifiedAt Γ(Y, U) q :=
    (formallyUnramified_stalkMap_iff U hU V hV hVU hxV).mp hfu
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (X.presheaf.stalk x),
    IsLocalization.AtPrime.ringKrullDim_eq_height p (Y.presheaf.stalk (f x))] at hdim
  have := Algebra.IsEtaleAt.of_isUnramifiedAt_of_height_le p q (by exact_mod_cast hdim)
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_etale_of_isEtaleAt (R := Γ(Y, U)) q
  exact HasRingHomProperty.exists_ι_comp_of_away @Etale hU hV hVU hxV r hrx
    (RingHom.etale_algebraMap.mpr hr)

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
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV).asIdeal).symm).mpr h

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
    (Set.mem_inter hxW hxU) (W.is_open'.inter (U.is_open'.preimage f.continuous))
  have hVU : V ≤ f ⁻¹ᵁ U := fun _ hy ↦ (hVWU hy).2
  -- `V.ι ≫ f` factors through `W.ι ≫ f`, hence so does the restriction `V ⟶ U` of `f`.
  have : LocallyOfFiniteType (f.resLE U V hVU ≫ U.ι) := by
    rw [f.resLE_comp_ι hVU, ← X.homOfLE_ι fun _ hy ↦ (hVWU hy).1, Category.assoc]
    infer_instance
  have := locallyOfFiniteType_of_comp (f.resLE U V hVU) U.ι
  exact ⟨U, hU, V, hV, hVU, hxV, (HasRingHomProperty.resLE_iff @LocallyOfFiniteType hU hV hVU).mp
    this, hqf.quasiFiniteAt hV hU hVU hxV⟩

section StalkAlgebra

open IsLocalRing

variable (f : X ⟶ Y) (x : X)

/-- The stalk map at `x` of a morphism `f : X ⟶ Y`, as an algebra, is local. -/
theorem isLocalHom_stalkMap_toAlgebra :
    letI := (f.stalkMap x).hom.toAlgebra
    IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
  inferInstanceAs <| IsLocalHom (f.stalkMap x).hom

/-- The stalk map at `x` of a morphism `f : X ⟶ Y` locally of finite type, as an algebra, is
essentially of finite type. -/
theorem essFiniteType_stalkMap_toAlgebra [LocallyOfFiniteType f] :
    letI := (f.stalkMap x).hom.toAlgebra
    Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
  exact LocallyOfFiniteType.stalkMap f x

/-- A flat morphism `f : X ⟶ Y` locally of finite type preserves and reflects Noetherian local
rings: the local ring of `Y` at `f x` is Noetherian exactly when the local ring of `X` at `x` is. -/
theorem isNoetherianRing_stalk_iff_of_flat_of_locallyOfFiniteType [Flat f]
    [LocallyOfFiniteType f] :
    IsNoetherianRing (Y.presheaf.stalk (f x)) ↔ IsNoetherianRing (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_toAlgebra f x
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have := essFiniteType_stalkMap_toAlgebra f x
  refine ⟨fun _ ↦
    Algebra.EssFiniteType.isNoetherianRing (Y.presheaf.stalk (f x)) (X.presheaf.stalk x),
    fun _ ↦ ?_⟩
  -- a flat local homomorphism is faithfully flat, and Noetherianity descends along it
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    .of_flat_of_isLocalHom
  exact .of_faithfullyFlat (X.presheaf.stalk x)

/-- The stalk map at `x` of a formally unramified morphism `f : X ⟶ Y`, as an algebra, is formally
unramified. -/
theorem formallyUnramified_stalkMap_toAlgebra [FormallyUnramified f] :
    letI := (f.stalkMap x).hom.toAlgebra
    Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
  exact FormallyUnramified.stalkMap f x

/-- Along the stalk map at `x` of a morphism `f : X ⟶ Y` that is formally unramified and locally of
finite type, the maximal ideal of the local ring of `Y` at `f x` generates the maximal ideal of the
local ring of `X` at `x`. -/
theorem map_maximalIdeal_stalkMap_of_formallyUnramified [FormallyUnramified f]
    [LocallyOfFiniteType f] :
    (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      maximalIdeal (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_toAlgebra f x
  have := essFiniteType_stalkMap_toAlgebra f x
  have := formallyUnramified_stalkMap_toAlgebra f x
  exact Algebra.FormallyUnramified.map_maximalIdeal

end StalkAlgebra

section Pullback

open Limits
open scoped TensorProduct

variable {X' Y' : Scheme.{u}} {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}

/-- Extract an affine tensor-product chart around `x' : X'`, reducing the horizontal stalk maps at
`x'` and `gX x'` and flatness of `gX.stalkMap x'` to an affine pushout `S ⊗[R] A`. -/
private theorem exists_isPushout_stalkMap_iff_of_isPullback
    (H : IsPullback gX f' f gY) (x' : X') :
    ∃ (R S A : Type u) (_ : CommRing R) (_ : CommRing S) (_ : CommRing A)
      (_ : Algebra R S) (_ : Algebra R A) (q : PrimeSpectrum (S ⊗[R] A)),
      letI : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
      ((f'.stalkMap x').hom.FormallyUnramified ↔ Algebra.IsUnramifiedAt S q.asIdeal) ∧
      ((f.stalkMap (gX x')).hom.FormallyUnramified ↔
        Algebra.IsUnramifiedAt R (q.asIdeal.under A)) ∧
      ((gX.stalkMap x').hom.Flat ↔ Module.Flat A (Localization.AtPrime q.asIdeal)) := by
  have hcomm : gY (f' x') = f (gX x') := by
    rw [← Scheme.Hom.comp_apply, ← H.w, Scheme.Hom.comp_apply]
  obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (gX x'))) isOpen_univ
  have hx'U : gY (f' x') ∈ U := hcomm ▸ hxU
  obtain ⟨_, ⟨U', hU' : IsAffineOpen U', rfl⟩, hx'U', hU'U⟩ :=
    Y'.isBasis_affineOpens.exists_subset_of_mem_open hx'U (U.is_open'.preimage gY.continuous)
  obtain ⟨_, ⟨V, hV : IsAffineOpen V, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.is_open'.preimage f.continuous)
  algebraize [(gY.appLE U U' hU'U).hom, (f.appLE U V hVU).hom]
  let _ : Algebra Γ(X, V) (Γ(Y', U') ⊗[Γ(Y, U)] Γ(X, V)) := Algebra.TensorProduct.rightAlgebra
  have := hU.isOpenImmersion_fromSpec
  have := hU'.isOpenImmersion_fromSpec
  have := hV.isOpenImmersion_fromSpec
  obtain ⟨ι, hι, q, qA, rfl, h₁, h₂, hgx, hqA⟩ :=
    TauCeti.AlgebraicGeometry.exists_isOpenImmersion_spec_tensorProduct_at_of_isPullback H
      (iY := hU.fromSpec) (iY' := hU'.fromSpec) (iX := hV.fromSpec)
      (hU.SpecMap_appLE_fromSpec gY hU' hU'U) (hU.SpecMap_appLE_fromSpec f hV hVU)
      (hU'.range_fromSpec ▸ hx'U') (hV.range_fromSpec ▸ hxV)
  refine ⟨Γ(Y, U), Γ(Y', U'), Γ(X, V), inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, q,
    (RingHom.FormallyUnramified.respectsIso.stalkMap_iff_of_isOpenImmersion_square
      ι f' _ hU'.fromSpec h₁ q).trans (formallyUnramified_stalkMap_specMap_iff q), ?_,
    (RingHom.Flat.respectsIso.stalkMap_iff_of_isOpenImmersion_square
      ι gX _ hV.fromSpec h₂ q).trans (flat_stalkMap_specMap_iff q)⟩
  rw [hgx]
  simpa only [hqA] using
    (RingHom.FormallyUnramified.respectsIso.stalkMap_iff_of_isOpenImmersion_square
      hV.fromSpec f (Spec.map (f.appLE U V hVU)) hU.fromSpec
      (hU.SpecMap_appLE_fromSpec f hV hVU).symm qA).trans
      (formallyUnramified_stalkMap_specMap_iff qA)

/-- **Formal unramifiedness of stalk maps is preserved under arbitrary pullback** (no flatness
or finite-type hypothesis). -/
theorem formallyUnramified_stalkMap_of_isPullback (H : IsPullback gX f' f gY) (x' : X')
    (h : (f.stalkMap (gX x')).hom.FormallyUnramified) :
    (f'.stalkMap x').hom.FormallyUnramified := by
  obtain ⟨R, S, A, _, _, _, _, _, q, hf', hf, -⟩ := exists_isPushout_stalkMap_iff_of_isPullback H x'
  let _ : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  have : Algebra.IsUnramifiedAt R (q.asIdeal.under A) := hf.mp h
  exact hf'.mpr (Algebra.IsUnramifiedAt.of_isPushout R A q.asIdeal)

/-- If `gX` has a flat stalk map at `x'`, then `f'` is formally unramified on stalks at `x'` iff
`f` is at `gX x'`. -/
theorem formallyUnramified_stalkMap_iff_of_isPullback_of_flat_stalkMap
    (H : IsPullback gX f' f gY) (x' : X') (hflat : (gX.stalkMap x').hom.Flat) :
    (f'.stalkMap x').hom.FormallyUnramified ↔ (f.stalkMap (gX x')).hom.FormallyUnramified := by
  obtain ⟨R, S, A, _, _, _, _, _, q, hf', hf, hfl⟩ :=
    exists_isPushout_stalkMap_iff_of_isPullback H x'
  let _ : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let _ := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under A) q.asIdeal
  have : Module.Flat A (Localization.AtPrime q.asIdeal) := hfl.mp hflat
  have hloc : Module.Flat (Localization.AtPrime (q.asIdeal.under A))
      (Localization.AtPrime q.asIdeal) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.asIdeal.under A))
      (q.asIdeal.under A).primeCompl (Localization.AtPrime q.asIdeal)).mpr inferInstance
  exact hf'.trans <| (Algebra.isUnramifiedAt_iff_of_isPushout_of_flat (R := R) (S := S) (A := A)
    q.asIdeal hloc).trans hf.symm

/-- **Flat base change of unramified stalk maps.** For flat `gY`, `f'` is formally unramified on
stalks at `x'` iff `f` is at `gX x'`. -/
theorem formallyUnramified_stalkMap_iff_of_isPullback (H : IsPullback gX f' f gY) [Flat gY]
    (x' : X') :
    (f'.stalkMap x').hom.FormallyUnramified ↔ (f.stalkMap (gX x')).hom.FormallyUnramified :=
  haveI : Flat gX := MorphismProperty.of_isPullback (P := @Flat) H.flip inferInstance
  formallyUnramified_stalkMap_iff_of_isPullback_of_flat_stalkMap H x' (Flat.stalkMap gX x')

end Pullback

/-- A dominant morphism of integral schemes whose induced function-field extension is separable is
formally unramified at the generic point of the source. -/
theorem formallyUnramified_stalkMap_genericPoint_of_isSeparable
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (hsep : letI := f.functionFieldMap.hom.toAlgebra;
      Algebra.IsSeparable Y.functionField X.functionField) :
    (f.stalkMap (genericPoint X)).hom.FormallyUnramified := by
  let _ : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
  let e : Y.presheaf.stalk (genericPoint Y) ≅ Y.presheaf.stalk (f (genericPoint X)) :=
    ⟨Y.presheaf.stalkSpecializes (specializes_of_eq f.genericPoint_eq_of_isDominant),
      Y.presheaf.stalkSpecializes (specializes_of_eq f.genericPoint_eq_of_isDominant.symm),
      by simp, by simp⟩
  have heq : e.hom ≫ f.stalkMap (genericPoint X) = f.functionFieldMap := by
    rw [f.eq_functionFieldMap_iff, Spec.map_comp_assoc, SpecMap_stalkSpecializes_fromSpecStalk,
      SpecMap_stalkMap_fromSpecStalk]
  have : IsIso e.hom := e.isIso_hom
  refine (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso
    e.hom (f.stalkMap (genericPoint X))).mp ?_
  rw [← CommRingCat.hom_comp, heq]
  exact Algebra.FormallyUnramified.of_isSeparable Y.functionField X.functionField

end Scheme.Hom

/-- **Étaleness descends along flat surjections.** Let `f` be locally of finite presentation and
`g` flat and surjective. If `g ≫ f` is étale, then `f` is étale. For an étale surjective `g`, this
is Stacks, Lemma 35.31.1 (036W) for `f` locally of finite presentation. -/
@[stacks 036W "for `f` locally of finite presentation, with `g` flat and surjective"]
theorem Etale.of_comp_surjective {X' : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) [Flat g]
    [Surjective g] [LocallyOfFinitePresentation f] [Etale (g ≫ f)] : Etale f := by
  -- Instance search does not derive this from `HasRingHomProperty @Etale RingHom.Etale` by itself.
  have : IsZariskiLocalAtSource @Etale.{u} := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_forall_exists_ι_comp fun x ↦ ?_
  obtain ⟨x', rfl⟩ := g.surjective x
  exact g.exists_etale_of_etale_comp f x' (Flat.stalkMap g x')

/-- Formal unramifiedness of a morphism locally of finite type descends along a flat
surjection of its source. The composite is also assumed locally of finite type. -/
theorem FormallyUnramified.of_comp_surjective {X' : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Flat g] [Surjective g] [LocallyOfFiniteType f] [LocallyOfFiniteType (g ≫ f)]
    [FormallyUnramified (g ≫ f)] : FormallyUnramified f := by
  apply HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime
  intro x
  obtain ⟨x', rfl⟩ := g.surjective x
  exact g.formallyUnramified_stalkMap_of_comp f x' (Flat.stalkMap g x')
    (FormallyUnramified.stalkMap (g ≫ f) x')

end AlgebraicGeometry
