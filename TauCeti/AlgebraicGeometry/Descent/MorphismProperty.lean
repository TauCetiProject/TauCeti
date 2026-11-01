/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import Mathlib.Tactic.Observe
public import TauCeti.AlgebraicGeometry.Descent.Affine
public import TauCeti.AlgebraicGeometry.Descent.AffineMorphism

/-!
# Affine morphisms satisfy fpqc descent

A morphism `g : Y ⟶ S` whose base change along a surjective, flat and quasi-compact morphism
`p : S' ⟶ S` is affine is itself affine. Being affine is local on the target, so it suffices to
treat a faithfully flat morphism `p : S' ⟶ S` of affine schemes with `S' ×_S Y` affine, and show
that `Y` is affine. The canonical descent datum on `S' ×_S Y` relative to `p` is a descent datum
on an affine scheme, so effective descent for affine schemes
(`TauCeti.DescentDatum.exists_isAffine_baseChange_hom_isIso`) gives an affine scheme `Y₀` over `S`
with the same canonical descent datum. Since base change along `p` is fully faithful into descent
data, `Y₀` is isomorphic to `Y` (`TauCeti.DescentDatum.Hom.descendIso`), so `Y` is affine.

Once affineness descends, so does every property of morphisms defined on affine targets by an
affine source and a property of the ring map on global sections which codescends along faithfully
flat ring maps. In particular closed immersions and finite morphisms satisfy fpqc descent.

For a descent datum `D` on a scheme `X` affine over `S'`, relative to an affine flat `p`, the
cartesian square `TauCeti.DescentDatum.isPullback_toDescended` exhibits `X ⟶ S'` as a base change
of the descended scheme `D.descended ⟶ S`. So when `p` is also surjective, every property of
`X ⟶ S'` which satisfies fpqc descent holds for `D.descended ⟶ S`. Thus a descent datum on a
closed subscheme of `S'`, over an arbitrary base `S`, descends to a closed subscheme of `S`, and
one on a finite `S'`-scheme descends to a finite `S`-scheme.

## Main results

* `AlgebraicGeometry.IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasiCompact`: affine
  morphisms satisfy fpqc descent.
* `AlgebraicGeometry.HasAffineProperty.descendsAlong_surjective_inf_flat_inf_quasiCompact`: a
  property of morphisms given by `affineAnd Q`, for `Q` codescending along faithfully flat ring
  maps, satisfies fpqc descent.
* `AlgebraicGeometry.IsClosedImmersion.descendsAlong_surjective_inf_flat_inf_quasiCompact` and
  `AlgebraicGeometry.IsFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact`: closed
  immersions and finite morphisms satisfy fpqc descent.
* `TauCeti.DescentDatum.descended_hom_mem`: for `p` affine, flat and surjective, the descended
  scheme of a descent datum on `X` affine over `S'` has every property of `X ⟶ S'` satisfying
  fpqc descent; for instance it is a closed subscheme of `S` if `X` is one of `S'`
  (`TauCeti.DescentDatum.isClosedImmersion_descended_hom`), and finite over `S` if `X` is finite
  over `S'` (`TauCeti.DescentDatum.isFinite_descended_hom`).

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII,
  Théorème 2.1 (effective descent for affine morphisms, the input used here).
* The Stacks Project, Chapter *Descent*, Section 35.23 (properties of morphisms local in the fpqc
  topology on the target), for affine morphisms, closed immersions and finite morphisms.
* The proof of `HasAffineProperty.descendsAlong_surjective_inf_flat_inf_quasiCompact` follows
  Mathlib's `AlgebraicGeometry.HasAffineProperty.descendsAlong_of_affineAnd` (Christian Merten),
  whose hypothesis that affine morphisms descend is supplied here.
-/

public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/-! Mathlib proves the stability of `Surjective ⊓ Flat` and the target-locality of affine morphisms
under `backward.isDefEq.respectTransparency`, so instance search does not find them here; they are
supplied by name, as local instances. -/

private theorem isStableUnderBaseChange_surjective_inf_flat :
    IsStableUnderBaseChange (@Surjective.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u}) :=
  IsStableUnderBaseChange.inf

private theorem isStableUnderComposition_surjective_inf_flat :
    IsStableUnderComposition (@Surjective.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u}) :=
  have : IsStableUnderComposition @Surjective.{u} := IsMultiplicative.toIsStableUnderComposition
  IsStableUnderComposition.inf

private theorem isZariskiLocalAtTarget_isAffineHom : IsZariskiLocalAtTarget @IsAffineHom.{u} :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine

attribute [local instance] isStableUnderBaseChange_surjective_inf_flat
  isStableUnderComposition_surjective_inf_flat isZariskiLocalAtTarget_isAffineHom

/-- Surjective local isomorphisms are surjective and flat: the condition under which
`IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact` reduces fpqc descent to affine bases. -/
private theorem isLocalIso_inf_surjective_le :
    (@IsLocalIso.{u} ⊓ @Surjective.{u} : MorphismProperty Scheme.{u}) ≤
      (@Surjective ⊓ @Flat : MorphismProperty Scheme.{u}) := by
  have : IsZariskiLocalAtSource @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat)
  have : ContainsIdentities @Flat.{u} :=
    (inferInstance : IsMultiplicative @Flat.{u}).toContainsIdentities
  exact fun _ _ f ⟨hf, hs⟩ ↦ ⟨hs, IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ f hf⟩

/-- The affine case of the descent of affineness: if `p : S' ⟶ S` is a flat surjective morphism of
affine schemes and the base change `S' ×_S Y` of `g : Y ⟶ S` is affine, then `Y` is affine. -/
private theorem isAffine_of_isAffine_pullback {S S' Y : Scheme.{u}} [IsAffine S] [IsAffine S']
    (p : S' ⟶ S) [Flat p] [Surjective p] (g : Y ⟶ S) [IsAffine (pullback p g)] : IsAffine Y := by
  let X : Over S := Over.mk g
  have : IsAffine ((Over.pullback p).obj X).left := .of_isIso (pullbackSymmetry g p).hom
  -- The canonical descent datum on `Y ×_S S'` is effective with an affine descended scheme `Y₀`.
  obtain ⟨Y₀, _, f, _⟩ :=
    TauCeti.DescentDatum.exists_isAffine_baseChange_hom_isIso (TauCeti.DescentDatum.baseChange p X)
  have : IsIso (TauCeti.DescentDatum.Hom.id (TauCeti.DescentDatum.baseChange p X)).hom := by
    rw [TauCeti.DescentDatum.Hom.id_hom]
    infer_instance
  -- By uniqueness of effective descent, `Y₀ ≅ Y` over `S`.
  exact .of_isIso (f.descendIso (TauCeti.DescentDatum.Hom.id _)).inv.left

/-- **Affine morphisms satisfy fpqc descent.** A morphism whose base change along a surjective,
flat and quasi-compact morphism is affine is affine. -/
instance IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong @IsAffineHom.{u} (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ isLocalIso_inf_surjective_le ?_
  intro R S Y φ g ⟨_, _⟩ _
  have : IsAffine (pullback (Spec.map φ) g) := isAffine_of_isAffineHom (pullback.fst _ g)
  have : IsAffine Y := isAffine_of_isAffine_pullback (Spec.map φ) g
  infer_instance

/-- **fpqc descent of properties defined on affine targets by global sections.** Let `P` be a
property of morphisms which, over an affine target, holds exactly for morphisms with affine source
whose ring map on global sections satisfies `Q`. If `Q` codescends along faithfully flat ring maps,
then `P` satisfies fpqc descent. -/
theorem HasAffineProperty.descendsAlong_surjective_inf_flat_inf_quasiCompact
    {P : MorphismProperty Scheme.{u}}
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [P.IsStableUnderBaseChange] (hP : HasAffineProperty P (affineAnd Q))
    (hQ : RingHom.RespectsIso Q) (hQQ' : RingHom.CodescendsAlong Q RingHom.FaithfullyFlat) :
    P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  -- Make `hP` available to instance search, for the target-locality of `P`.
  have : HasAffineProperty P (affineAnd Q) := hP
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ isLocalIso_inf_surjective_le ?_
  intro R S Y φ g ⟨_, _⟩ hg
  -- The source `Y` is affine, by descent of affineness.
  have : IsAffine Y := by
    have : IsAffineHom (pullback.fst (Spec.map φ) g) :=
      HasAffineProperty.affineAnd_le_isAffineHom P hP _ hg
    have : IsAffineHom g := of_pullback_fst_of_descendsAlong
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
      this
    exact isAffine_of_isAffineHom g
  -- Present `Y` as a spectrum, and conclude by codescent of `Q` on global sections.
  rw [← P.cancel_left_of_respectsIso Y.isoSpec.inv]
  have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
      pullback.map _ _ _ _ (𝟙 _) Y.isoSpec.inv (𝟙 _) (by simp) (by simp) ≫
        pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
  refine of_pullback_fst_Spec_of_codescendsAlong P (@Surjective ⊓ @Flat : MorphismProperty Scheme)
    hQQ' (fun h ↦ (flat_and_surjective_SpecMap_iff _).mp ⟨h.2, h.1⟩)
    (HasAffineProperty.SpecMap_iff_of_affineAnd hP hQ _) (f := Spec.map φ)
    ⟨inferInstance, inferInstance⟩ ?_
  rwa [heq, P.cancel_left_of_respectsIso]

/-- **Closed immersions satisfy fpqc descent.** A morphism whose base change along a surjective,
flat and quasi-compact morphism is a closed immersion is a closed immersion. -/
instance IsClosedImmersion.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong @IsClosedImmersion.{u} (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasAffineProperty.descendsAlong_surjective_inf_flat_inf_quasiCompact
    (Q := fun f ↦ Function.Surjective f) IsClosedImmersion.hasAffineProperty
    RingHom.surjective_respectsIso RingHom.FaithfullyFlat.codescendsAlong_surjective

/-- **Finite morphisms satisfy fpqc descent.** A morphism whose base change along a surjective,
flat and quasi-compact morphism is finite is finite. -/
instance IsFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong @IsFinite.{u} (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  -- Mathlib's affine description of finite morphisms is an unnamed instance which instance search
  -- does not find here, as above.
  observe hP : HasAffineProperty @IsFinite.{u}
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom)
  exact HasAffineProperty.descendsAlong_surjective_inf_flat_inf_quasiCompact (Q := RingHom.Finite)
    hP RingHom.finite_respectsIso RingHom.Finite.codescendsAlong_faithfullyFlat

end AlgebraicGeometry

namespace TauCeti.DescentDatum

universe u

variable {S S' : Scheme.{u}} {p : S' ⟶ S} [IsAffineHom p] [Flat p] [Surjective p] {X : Over S'}
  (D : DescentDatum p X)

/-- **Properties of the descended scheme.** Let `p : S' ⟶ S` be affine, flat and surjective, and
`D` a descent datum relative to `p` on a scheme `X` affine over `S'`. Every property of `X ⟶ S'`
satisfying fpqc descent holds for the descended scheme `D.descended ⟶ S`. -/
theorem descended_hom_mem [IsAffineHom X.hom] {P : MorphismProperty Scheme.{u}}
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] (hX : P X.hom) :
    P D.descended.hom :=
  of_isPullback_of_descendsAlong (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    D.isPullback_toDescended.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hX

/-- A descent datum on a closed subscheme of `S'`, relative to an affine, flat and surjective
`p : S' ⟶ S`, descends to a closed subscheme of `S`. -/
instance isClosedImmersion_descended_hom [IsClosedImmersion X.hom] :
    IsClosedImmersion D.descended.hom :=
  D.descended_hom_mem (P := @IsClosedImmersion) inferInstance

/-- A descent datum on a finite `S'`-scheme, relative to an affine, flat and surjective
`p : S' ⟶ S`, descends to a finite `S`-scheme. -/
instance isFinite_descended_hom [IsFinite X.hom] : IsFinite D.descended.hom :=
  D.descended_hom_mem (P := @IsFinite) inferInstance

end TauCeti.DescentDatum
