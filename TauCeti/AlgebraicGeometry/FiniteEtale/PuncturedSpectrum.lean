/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.PuncturedSpectrum
public import Mathlib.AlgebraicGeometry.Restrict
public import TauCeti.RingTheory.LocalRing.RingHom
import TauCeti.Algebra.Algebra.Pi
import TauCeti.AlgebraicGeometry.FiniteEtale.MorphismProperty

/-!
# Finite étale covers of a punctured local spectrum

For a local ring, the punctured spectrum is the complement of the closed point. Pullback along
its inclusion restricts finite étale schemes. Purity of the local ring means that this functor is
essentially surjective.

Restriction is faithful exactly when the ring has positive Krull dimension. In that case the
punctured spectrum is dense, and pullback of finite étale schemes along a dominant morphism is
faithful. In dimension zero the punctured spectrum is empty, so restriction identifies the two
projections `R × R → R`, viewed as morphisms of finite étale schemes over `Spec R`.

## Main results

* `TauCeti.IsLocalRing.restrictPunctured_faithful_iff`: restriction to the punctured spectrum is
  faithful if and only if `0 < ringKrullDim R`.
* `TauCeti.IsLocalRing.restrictPunctured_faithful_of_one_le_depth`: restriction is faithful for a
  Noetherian local ring of positive depth.
* `TauCeti.IsLocalRing.restrictPuncturedCompPullbackIso`: for a homomorphism of local rings
  `A → A'` whose only point over the closed point is the closed point, restriction to the
  punctured spectrum commutes with the pullback `TauCeti.IsLocalRing.pullbackPunctured` of finite
  étale covers from the punctured spectrum of `A` to that of `A'`.
* `TauCeti.IsLocalRing.extends_iff_extends_pullback`: if moreover pullback of finite étale
  schemes from `Spec A` to `Spec A'` is essentially surjective and `pullbackPunctured` is fully
  faithful, a finite étale cover of the punctured spectrum of `A` extends across the closed point
  if and only if its pullback to the punctured spectrum of `A'` does.
* `TauCeti.IsLocalRing.purityHolds_of_purityHolds_of_fullyFaithful`: under the same hypotheses,
  purity for `A'` implies purity for `A`.

## References

* The Stacks Project, Section 58.20 (Tag 0BM7).
* Ported from Taylor Dupuy, Thomas Tucker and Zhuoran Wang, pcfawd-formalization at commit
  `9a20b3f` (Apache 2.0), `Pcf/Stacks/Purity/PuncturedSpectrum.lean` and
  `Pcf/Stacks/Purity/Hartogs.lean`.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace TauCeti.IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Pullback of finite étale schemes along the punctured-spectrum inclusion. Its underlying
functor is `Over.pullback` by `TauCeti.FiniteEtaleScheme.pullback_comp_ι`. -/
noncomputable abbrev restrictPunctured :
    TauCeti.FiniteEtaleScheme (Spec (.of R)) ⥤
      TauCeti.FiniteEtaleScheme (puncturedSpectrum R).toScheme :=
  TauCeti.FiniteEtaleScheme.pullback (puncturedSpectrum R).ι

/-- Purity holds if every finite étale cover of the punctured spectrum extends across the
closed point. -/
@[stacks 0BM7 "definition of purity"]
def PurityHolds : Prop := (restrictPunctured R).EssSurj

/-- Purity is, by definition, essential surjectivity of the restriction functor. -/
theorem purityHolds_iff_essSurj : PurityHolds R ↔ (restrictPunctured R).EssSurj :=
  Iff.rfl

/-- Purity is equivalent to the extension of every finite étale cover of the puncture. -/
theorem purityHolds_iff :
    PurityHolds R ↔
      ∀ cover : TauCeti.FiniteEtaleScheme (puncturedSpectrum R).toScheme,
        ∃ extension : TauCeti.FiniteEtaleScheme (Spec (.of R)),
          Nonempty ((restrictPunctured R).obj extension ≅ cover) := by
  constructor
  · intro h cover
    let : (restrictPunctured R).EssSurj := h
    exact Functor.EssSurj.mem_essImage (restrictPunctured R) cover
  · intro h
    exact ⟨h⟩

/-- Restriction of finite étale schemes to the punctured spectrum is faithful when the local ring
has positive Krull dimension: the punctured spectrum is then dense. -/
theorem restrictPunctured_faithful (h : 0 < ringKrullDim R) : (restrictPunctured R).Faithful := by
  have := Opens.isDominant_ι (U := puncturedSpectrum R)
    ((coe_puncturedSpectrum R).symm ▸ dense_compl_singleton_closedPoint_iff.mpr h)
  infer_instance

/-- Restriction of finite étale schemes to the punctured spectrum is faithful exactly when the
local ring has positive Krull dimension. In dimension zero the punctured spectrum is empty, while
the two projections `R × R → R` give distinct morphisms of finite étale schemes over `Spec R`. -/
theorem restrictPunctured_faithful_iff :
    (restrictPunctured R).Faithful ↔ 0 < ringKrullDim R := by
  refine ⟨fun _ ↦ ?_, restrictPunctured_faithful R⟩
  by_contra hdim
  have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr (not_lt.mp hdim)
  have := Ring.KrullDimLE.subsingleton_primeSpectrum R
  have : IsEmpty (puncturedSpectrum R).toScheme :=
    ⟨fun x ↦ (mem_puncturedSpectrum_iff R x.1).mp x.2 (Subsingleton.elim _ _)⟩
  -- Over the empty punctured spectrum all finite étale schemes are empty, so any two parallel
  -- morphisms agree.
  have hsub {X Y : TauCeti.FiniteEtaleScheme (puncturedSpectrum R).toScheme} (a b : X ⟶ Y) :
      a = b := by
    have : IsEmpty X.obj.left := Function.isEmpty X.obj.hom
    exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext (isInitialOfIsEmpty.hom_ext _ _))
  -- Over `Spec R`, the two projections `R × R → R`, written as evaluations on `Fin 2 → R`, give
  -- distinct morphisms, since the finite étale spectrum functor is an anti-equivalence.
  let e := TauCeti.FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of R)
  let A := CommAlgCat.FiniteEtale.of (CommRingCat.of R) (Fin 2 → R)
  let B := CommAlgCat.FiniteEtale.of (CommRingCat.of R) R
  let f (i : Fin 2) : A ⟶ B := CommAlgCat.FiniteEtale.ofHom (Pi.evalAlgHom R (fun _ ↦ R) i)
  have h01 := congrArg (fun g : A ⟶ B ↦ g.hom.hom) (Quiver.Hom.op_inj
    (e.functor.map_injective ((restrictPunctured R).map_injective (hsub _ _)) :
      (f 0).op = (f 1).op))
  exact zero_ne_one (Pi.evalAlgHom_injective R (Fin 2) h01)

/-- Restriction of finite étale schemes to the punctured spectrum is faithful for a Noetherian
local ring of positive depth, including nonreduced rings. -/
theorem restrictPunctured_faithful_of_one_le_depth [IsNoetherianRing R]
    (hdepth : 1 ≤ _root_.IsLocalRing.depth (ModuleCat.of R R)) :
    (restrictPunctured R).Faithful := by
  apply restrictPunctured_faithful
  apply dense_compl_singleton_closedPoint_iff.mp
  exact dense_compl_singleton_closedPoint_of_one_le_depth hdepth

section Pullback

variable {A A' : Type u} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
  [Algebra A A']
  (h : ((_root_.IsLocalRing.maximalIdeal A).map (algebraMap A A')).radical =
    _root_.IsLocalRing.maximalIdeal A')

/-- Pullback of finite étale covers from the punctured spectrum of `A` to the punctured spectrum
of `A'`, along the restriction of `Spec A' ⟶ Spec A`. This requires the closed point to be the
only point of `Spec A'` over the closed point of `Spec A`. -/
abbrev pullbackPunctured :
    TauCeti.FiniteEtaleScheme (puncturedSpectrum A).toScheme ⥤
      TauCeti.FiniteEtaleScheme (puncturedSpectrum A').toScheme :=
  TauCeti.FiniteEtaleScheme.pullback ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
    (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge)

/-- Restriction to the punctured spectrum commutes with pullback along `Spec A' ⟶ Spec A`: both
composites are pullback along the inclusion of the punctured spectrum of `A'` into `Spec A`. -/
def restrictPuncturedCompPullbackIso :
    restrictPunctured A ⋙ pullbackPunctured h ≅
      TauCeti.FiniteEtaleScheme.pullback (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ⋙
        restrictPunctured A' :=
  (TauCeti.FiniteEtaleScheme.pullbackComp _ _).symm ≪≫
    eqToIso (congrArg TauCeti.FiniteEtaleScheme.pullback (Scheme.Hom.resLE_comp_ι _ _)) ≪≫
    TauCeti.FiniteEtaleScheme.pullbackComp _ _

/-- If a finite étale cover of the punctured spectrum of `A` extends across the closed point,
then so does its pullback to the punctured spectrum of `A'`. -/
theorem extends_pullbackPunctured_of_extends
    {V : TauCeti.FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    (hV : ∃ Y : TauCeti.FiniteEtaleScheme (Spec (.of A)),
      Nonempty ((restrictPunctured A).obj Y ≅ V)) :
    ∃ Y' : TauCeti.FiniteEtaleScheme (Spec (.of A')),
      Nonempty ((restrictPunctured A').obj Y' ≅ (pullbackPunctured h).obj V) := by
  obtain ⟨Y, ⟨e⟩⟩ := hV
  exact ⟨(TauCeti.FiniteEtaleScheme.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap A A')))).obj Y,
    ⟨((restrictPuncturedCompPullbackIso h).app Y).symm ≪≫ (pullbackPunctured h).mapIso e⟩⟩

variable [(TauCeti.FiniteEtaleScheme.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap A A')))).EssSurj]
  [(pullbackPunctured h).Full] [(pullbackPunctured h).Faithful]

/-- Suppose every finite étale scheme over `Spec A'` is a pullback from `Spec A`, and pullback of
finite étale covers from the punctured spectrum of `A` to that of `A'` is fully faithful. If the
pullback of a finite étale cover of the punctured spectrum of `A` extends across the closed point
of `Spec A'`, then the cover extends across the closed point of `Spec A`. -/
theorem extends_of_extends_pullbackPunctured
    {V : TauCeti.FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    (hV : ∃ Y' : TauCeti.FiniteEtaleScheme (Spec (.of A')),
      Nonempty ((restrictPunctured A').obj Y' ≅ (pullbackPunctured h).obj V)) :
    ∃ Y : TauCeti.FiniteEtaleScheme (Spec (.of A)),
      Nonempty ((restrictPunctured A).obj Y ≅ V) := by
  obtain ⟨Y', ⟨e⟩⟩ := hV
  let F := TauCeti.FiniteEtaleScheme.pullback (Spec.map (CommRingCat.ofHom (algebraMap A A')))
  refine ⟨F.objPreimage Y', ⟨(pullbackPunctured h).preimageIso ?_⟩⟩
  exact (restrictPuncturedCompPullbackIso h).app _ ≪≫
    (restrictPunctured A').mapIso (F.objObjPreimageIso Y') ≪≫ e

/-- Suppose every finite étale scheme over `Spec A'` is a pullback from `Spec A`, and pullback of
finite étale covers from the punctured spectrum of `A` to that of `A'` is fully faithful. Then a
finite étale cover of the punctured spectrum of `A` extends across the closed point if and only if
its pullback to the punctured spectrum of `A'` extends across the closed point. -/
theorem extends_iff_extends_pullback
    (V : TauCeti.FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (∃ Y : TauCeti.FiniteEtaleScheme (Spec (.of A)),
        Nonempty ((restrictPunctured A).obj Y ≅ V)) ↔
      ∃ Y' : TauCeti.FiniteEtaleScheme (Spec (.of A')),
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

/-- Restriction of finite étale covers from the punctured spectrum of `A` to the punctured
spectrum of `A ⧸ I`, which is its intersection with `Spec (A ⧸ I)`. For `I = (f)`, this is
restriction to the punctured spectrum of the hypersurface section `f = 0`. -/
abbrev restrictPuncturedQuotient {A : Type u} [CommRing A] [IsLocalRing A] (I : Ideal A)
    [IsLocalRing (A ⧸ I)] :
    TauCeti.FiniteEtaleScheme (puncturedSpectrum A).toScheme ⥤
      TauCeti.FiniteEtaleScheme (puncturedSpectrum (A ⧸ I)).toScheme :=
  pullbackPunctured (radical_map_maximalIdeal_of_surjective
    (Ideal.Quotient.algebraMap_eq I ▸ Ideal.Quotient.mk_surjective))

end TauCeti.IsLocalRing
