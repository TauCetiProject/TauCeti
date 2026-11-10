/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Henselian
public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum

/-!
# Extending finite étale covers from a henselian section

Let `A → A'` be a homomorphism of local rings such that the closed point is the only point of
`Spec A'` over the closed point of `Spec A`, so that the punctured spectrum `U'` of `A'` maps to
the punctured spectrum `U` of `A`. Restricting a finite étale scheme over `Spec A` to `U` and then
pulling back to `U'` agrees with pulling back to `Spec A'` and then restricting to `U'`
(`TauCeti.IsLocalRing.restrictPuncturedCompPullbackIso`).

Suppose every finite étale scheme over `Spec A'` comes from `Spec A`, and pullback of finite étale
covers from `U` to `U'` is fully faithful. Then a finite étale cover `V` of `U` extends across the
closed point of `Spec A` as soon as its pullback to `U'` extends across the closed point of
`Spec A'`. Indeed, if `Y'` over `Spec A'` extends the pullback of `V`, choose `Y` over `Spec A`
whose pullback is `Y'`; the restriction of `Y` to `U` and `V` have isomorphic pullbacks to `U'`,
so they are isomorphic.

The main case is the quotient `A' = A ⧸ I` by an ideal for which `(A, I)` is a henselian pair,
where every finite étale scheme over `Spec (A ⧸ I)` lifts
(`TauCeti.FiniteEtaleScheme.essSurj_pullback_quotient`). For `I = (f)` this is the reduction, in
the proof of the local Lefschetz extension theorem (Stacks, Lemma 58.20.7 (0BLM)), of the
extension of a cover `V` whose restriction to the hypersurface section extends, to the full
faithfulness of restriction to the punctured spectrum of `A ⧸ (f)` (Stacks, Lemma 58.19.7 (0BLJ),
for depth at least three). The same argument shows that purity (`TauCeti.IsLocalRing.PurityHolds`)
passes from `A ⧸ I` to `A` under the full faithfulness hypothesis; for a henselian pair `(A, (f))`
this is the shape of the inductive step in the proof of purity for regular local rings (Stacks,
Lemma 58.21.3 (0BMA)).

## Main definitions

* `TauCeti.IsLocalRing.pullbackPunctured`: pullback of finite étale covers from the punctured
  spectrum of `A` to the punctured spectrum of `A'`.
* `TauCeti.IsLocalRing.restrictPuncturedCompPullbackIso`: restriction to the punctured spectrum
  commutes with this pullback.
* `TauCeti.IsLocalRing.restrictPuncturedQuotient`: the case `A' = A ⧸ I`, restriction to the
  punctured spectrum of `A ⧸ I`.

## Main results

* `TauCeti.IsLocalRing.extends_iff_extends_pullback`: if pullback of finite étale schemes from
  `Spec A` to `Spec A'` is essentially surjective and `pullbackPunctured` is fully faithful, a
  finite étale cover of `U` extends to `Spec A` if and only if its pullback to `U'` extends to
  `Spec A'`.
* `TauCeti.IsLocalRing.extends_iff_extends_quotient`: the case of a henselian pair `(A, I)`.
* `TauCeti.IsLocalRing.purityHolds_of_purityHolds_quotient`: for a henselian pair `(A, I)` such
  that restriction from `U` to the punctured spectrum of `A ⧸ I` is fully faithful, purity for
  `A ⧸ I` implies purity for `A`.

## References

* [The Stacks Project, Lemma 58.20.7](https://stacks.math.columbia.edu/tag/0BLM), the local
  Lefschetz extension theorem.
* [The Stacks Project, Lemma 58.19.7](https://stacks.math.columbia.edu/tag/0BLJ), full
  faithfulness of restriction to the punctured spectrum of a hypersurface section.
* [The Stacks Project, Lemma 15.13.2](https://stacks.math.columbia.edu/tag/09ZL), finite étale
  algebras over a henselian pair.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace TauCeti.IsLocalRing

section Pullback

variable {A A' : Type u} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
  [Algebra A A'] (h : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A')

/-- Pullback of finite étale covers from the punctured spectrum of `A` to the punctured spectrum
of `A'`, along the restriction of `Spec A' ⟶ Spec A`. This requires the closed point to be the
only point of `Spec A'` over the closed point of `Spec A`. -/
abbrev pullbackPunctured :
    FiniteEtaleScheme (puncturedSpectrum A).toScheme ⥤
      FiniteEtaleScheme (puncturedSpectrum A').toScheme :=
  FiniteEtaleScheme.pullback ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
    (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge)

/-- Restriction to the punctured spectrum commutes with pullback along `Spec A' ⟶ Spec A`: both
composites are pullback along the inclusion of the punctured spectrum of `A'` into `Spec A`. -/
def restrictPuncturedCompPullbackIso :
    restrictPunctured A ⋙ pullbackPunctured h ≅
      FiniteEtaleScheme.pullback (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ⋙
        restrictPunctured A' :=
  (FiniteEtaleScheme.pullbackComp _ _).symm ≪≫
    eqToIso (congrArg FiniteEtaleScheme.pullback (Scheme.Hom.resLE_comp_ι _ _)) ≪≫
    FiniteEtaleScheme.pullbackComp _ _

/-- If a finite étale cover of the punctured spectrum of `A` extends across the closed point,
then so does its pullback to the punctured spectrum of `A'`. -/
theorem extends_pullbackPunctured_of_extends
    {V : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    (hV : ∃ Y : FiniteEtaleScheme (Spec (.of A)), Nonempty ((restrictPunctured A).obj Y ≅ V)) :
    ∃ Y' : FiniteEtaleScheme (Spec (.of A')),
      Nonempty ((restrictPunctured A').obj Y' ≅ (pullbackPunctured h).obj V) := by
  obtain ⟨Y, ⟨e⟩⟩ := hV
  exact ⟨(FiniteEtaleScheme.pullback (Spec.map (CommRingCat.ofHom (algebraMap A A')))).obj Y,
    ⟨((restrictPuncturedCompPullbackIso h).app Y).symm ≪≫ (pullbackPunctured h).mapIso e⟩⟩

variable [(FiniteEtaleScheme.pullback (Spec.map (CommRingCat.ofHom (algebraMap A A')))).EssSurj]
  [(pullbackPunctured h).Full] [(pullbackPunctured h).Faithful]

/-- Suppose every finite étale scheme over `Spec A'` is a pullback from `Spec A`, and pullback of
finite étale covers from the punctured spectrum of `A` to that of `A'` is fully faithful. If the
pullback of a finite étale cover of the punctured spectrum of `A` extends across the closed point
of `Spec A'`, then the cover extends across the closed point of `Spec A`. -/
theorem extends_of_extends_pullbackPunctured
    {V : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    (hV : ∃ Y' : FiniteEtaleScheme (Spec (.of A')),
      Nonempty ((restrictPunctured A').obj Y' ≅ (pullbackPunctured h).obj V)) :
    ∃ Y : FiniteEtaleScheme (Spec (.of A)), Nonempty ((restrictPunctured A).obj Y ≅ V) := by
  obtain ⟨Y', ⟨e⟩⟩ := hV
  let F := FiniteEtaleScheme.pullback (Spec.map (CommRingCat.ofHom (algebraMap A A')))
  refine ⟨F.objPreimage Y', ⟨(pullbackPunctured h).preimageIso ?_⟩⟩
  exact (restrictPuncturedCompPullbackIso h).app _ ≪≫
    (restrictPunctured A').mapIso (F.objObjPreimageIso Y') ≪≫ e

/-- Suppose every finite étale scheme over `Spec A'` is a pullback from `Spec A`, and pullback of
finite étale covers from the punctured spectrum of `A` to that of `A'` is fully faithful. Then a
finite étale cover of the punctured spectrum of `A` extends across the closed point if and only if
its pullback to the punctured spectrum of `A'` extends across the closed point. -/
theorem extends_iff_extends_pullback (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (∃ Y : FiniteEtaleScheme (Spec (.of A)), Nonempty ((restrictPunctured A).obj Y ≅ V)) ↔
      ∃ Y' : FiniteEtaleScheme (Spec (.of A')),
        Nonempty ((restrictPunctured A').obj Y' ≅ (pullbackPunctured h).obj V) :=
  ⟨extends_pullbackPunctured_of_extends h, extends_of_extends_pullbackPunctured h⟩

include h in
/-- Suppose every finite étale scheme over `Spec A'` is a pullback from `Spec A`, and pullback of
finite étale covers from the punctured spectrum of `A` to that of `A'` is fully faithful. Then
purity for `A'` implies purity for `A`. -/
theorem purityHolds_of_purityHolds_of_fullyFaithful (hA' : PurityHolds A') : PurityHolds A :=
  (purityHolds_iff A).mpr fun _ ↦
    extends_of_extends_pullbackPunctured h ((purityHolds_iff A').mp hA' _)

end Pullback

section Quotient

/-- For a surjection of local rings `A → A'`, the closed point is the only point of `Spec A'`
over the closed point of `Spec A`. -/
theorem radical_map_maximalIdeal_of_surjective {A A' : Type u} [CommRing A] [IsLocalRing A]
    [CommRing A'] [IsLocalRing A'] [Algebra A A'] (hf : Function.Surjective (algebraMap A A')) :
    ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A' := by
  rw [map_maximalIdeal_of_surjective _ hf]
  exact (maximalIdeal.isMaximal _).isPrime.radical

variable {A : Type u} [CommRing A] [IsLocalRing A] (I : Ideal A) [IsLocalRing (A ⧸ I)]

/-- Restriction of finite étale covers from the punctured spectrum of `A` to the punctured
spectrum of `A ⧸ I`, which is its intersection with `Spec (A ⧸ I)`. For `I = (f)`, this is
restriction to the punctured spectrum of the hypersurface section `f = 0`. -/
abbrev restrictPuncturedQuotient :
    FiniteEtaleScheme (puncturedSpectrum A).toScheme ⥤
      FiniteEtaleScheme (puncturedSpectrum (A ⧸ I)).toScheme :=
  pullbackPunctured (radical_map_maximalIdeal_of_surjective Ideal.Quotient.mk_surjective)

variable [HenselianRing A I] [(restrictPuncturedQuotient I).Full]
  [(restrictPuncturedQuotient I).Faithful]

/-- **Extension from a henselian section.** Let `(A, I)` be a henselian pair with `A` local, and
suppose restriction of finite étale covers from the punctured spectrum of `A` to that of `A ⧸ I`
is fully faithful. Then a finite étale cover of the punctured spectrum of `A` extends across the
closed point if and only if its restriction to the punctured spectrum of `A ⧸ I` extends across
the closed point of `Spec (A ⧸ I)`. For `I = (f)`, full faithfulness is Stacks, Lemma 58.19.7
(0BLJ), and the statement is then Stacks, Lemma 58.20.7 (0BLM) for henselian pairs. -/
theorem extends_iff_extends_quotient (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (∃ Y : FiniteEtaleScheme (Spec (.of A)), Nonempty ((restrictPunctured A).obj Y ≅ V)) ↔
      ∃ Y₀ : FiniteEtaleScheme (Spec (.of (A ⧸ I))),
        Nonempty ((restrictPunctured (A ⧸ I)).obj Y₀ ≅
          (restrictPuncturedQuotient I).obj V) :=
  have : (FiniteEtaleScheme.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))))).EssSurj :=
    FiniteEtaleScheme.essSurj_pullback_quotient A I
  extends_iff_extends_pullback _ V

/-- **Purity from a henselian section.** Let `(A, I)` be a henselian pair with `A` local, and
suppose restriction of finite étale covers from the punctured spectrum of `A` to that of `A ⧸ I`
is fully faithful. If purity holds for `A ⧸ I`, then purity holds for `A`. -/
theorem purityHolds_of_purityHolds_quotient (hI : PurityHolds (A ⧸ I)) : PurityHolds A :=
  have : (FiniteEtaleScheme.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))))).EssSurj :=
    FiniteEtaleScheme.essSurj_pullback_quotient A I
  purityHolds_of_purityHolds_of_fullyFaithful _ hI

end Quotient

end TauCeti.IsLocalRing
