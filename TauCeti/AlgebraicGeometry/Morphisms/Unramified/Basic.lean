/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Unramified morphisms

A morphism of schemes is unramified when it is locally of finite type and formally
unramified. This packages the two conditions as a morphism property, so geometric
constructions such as the singular subscheme of a nodal family can state the usual
unramifiedness condition directly. Since the diagonal of an unramified morphism is an open
immersion, open immersions cancel against unramified morphisms on the right
(`TauCeti.AlgebraicGeometry.Unramified.isOpenImmersion_hasOfPostcompProperty`). In particular, in
a pullback square along an unramified morphism, the lift of an open immersion is an open immersion
(`TauCeti.AlgebraicGeometry.isOpenImmersion_lift_of_isPullback`). Both conditions satisfy fpqc
descent, hence so does unramifiedness
(`TauCeti.AlgebraicGeometry.Unramified.descendsAlong_surjective_inf_flat_inf_quasicompact`).

## Main definition

* `TauCeti.AlgebraicGeometry.Unramified f`: `f` is locally of finite type and formally
  unramified.
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

variable {X Y : Scheme.{u}}

namespace TauCeti.AlgebraicGeometry

/-- A morphism of schemes is unramified if it is locally of finite type and formally
unramified. -/
@[mk_iff]
class Unramified (f : X ⟶ Y) : Prop extends LocallyOfFiniteType f, FormallyUnramified f

lemma unramified_eq : @Unramified =
    (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme) := by
  ext X Y f
  rw [unramified_iff]
  rfl

namespace Unramified

instance : HasRingHomProperty @Unramified
    (fun f ↦ f.FiniteType ∧ f.FormallyUnramified) := by
  rw [unramified_eq]
  exact HasRingHomProperty.inf

/-- The affine criterion for an unramified morphism. -/
theorem Spec_iff {R S : CommRingCat.{u}} {φ : R ⟶ S} :
    Unramified (Spec.map φ) ↔
      letI := φ.hom.toAlgebra
      Algebra.Unramified R S := by
  rw [HasRingHomProperty.Spec_iff (P := @Unramified)]
  algebraize [φ.hom]
  constructor
  · rintro ⟨hft, hfu⟩
    exact ⟨hfu, hft⟩
  · intro h
    exact ⟨h.finiteType, h.formallyUnramified⟩

/-- If a composite is unramified, then its first map is unramified. -/
theorem of_comp {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Unramified (f ≫ g)] : Unramified f :=
  { toLocallyOfFiniteType := locallyOfFiniteType_of_comp f g
    toFormallyUnramified := FormallyUnramified.of_comp f g }

instance : MorphismProperty.IsStableUnderComposition @Unramified := by
  rw [unramified_eq]
  exact MorphismProperty.IsStableUnderComposition.inf

instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @Unramified := by
  rw [unramified_eq]
  exact MorphismProperty.IsStableUnderBaseChange.inf

instance : MorphismProperty.IsMultiplicative @Unramified := by
  rw [unramified_eq]
  exact MorphismProperty.IsMultiplicative.inf

instance unramified_comp {Z : Scheme.{u}} (g : Y ⟶ Z)
    [Unramified f] [Unramified g] : Unramified (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹Unramified f› ‹Unramified g›

instance {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [Unramified g] :
    Unramified (pullback.fst f g) :=
  isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g).flip inferInstance

instance {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [Unramified f] :
    Unramified (pullback.snd f g) :=
  isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g) inferInstance

/-- A monomorphism locally of finite type is unramified. -/
instance (priority := 900) of_mono (f : X ⟶ Y) [Mono f] [LocallyOfFiniteType f] :
    Unramified f := ⟨⟩

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [Etale f] : Unramified f := by
  exact ⟨⟩

/-- If `f ≫ g` is an open immersion and `g` is unramified, then `f` is an open immersion, since
the diagonal of an unramified morphism is an open immersion. In particular, a section of an
unramified morphism is an open immersion. -/
instance isOpenImmersion_hasOfPostcompProperty :
    MorphismProperty.HasOfPostcompProperty @IsOpenImmersion @Unramified :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr fun _ _ f (_ : Unramified f) ↦
    inferInstanceAs (IsOpenImmersion (pullback.diagonal f))

instance (f : X ⟶ Y) (V : Y.Opens) [Unramified f] : Unramified (f ∣_ V) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict f V).flip ‹Unramified f›

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [Unramified f] :
    Unramified (f.resLE V U e) := by
  delta Scheme.Hom.resLE
  infer_instance

/-- **Unramified morphisms satisfy fpqc descent**, since both being locally of finite type and
being formally unramified do. -/
instance descendsAlong_surjective_inf_flat_inf_quasicompact :
    MorphismProperty.DescendsAlong @Unramified.{u} (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [unramified_eq]
  exact MorphismProperty.DescendsAlong.inf (P := @LocallyOfFiniteType) (W := @FormallyUnramified)

end Unramified

/-- In a pullback square along an unramified morphism `f : Y ⟶ S`, the lift of an open immersion
`ι : W ⟶ Z` together with a compatible `j : W ⟶ Y` is an open immersion: it is a section over `W`
of the projection `p : Z' ⟶ Z`, which is unramified as a base change of `f`. -/
theorem isOpenImmersion_lift_of_isPullback {Z S Z' W : Scheme.{u}} {g : Z ⟶ S} {f : Y ⟶ S}
    [Unramified f] {p : Z' ⟶ Z} {g' : Z' ⟶ Y} (H : IsPullback p g' g f) {ι : W ⟶ Z}
    [IsOpenImmersion ι] {j : W ⟶ Y} (hcomm : ι ≫ g = j ≫ f) :
    IsOpenImmersion (H.lift ι j hcomm) := by
  have : Unramified p := MorphismProperty.of_isPullback (P := @Unramified) H.flip inferInstance
  have : IsOpenImmersion (H.lift ι j hcomm ≫ p) := by rwa [H.lift_fst]
  exact MorphismProperty.of_postcomp @IsOpenImmersion (W' := @Unramified) _ p ‹_› ‹_›

end TauCeti.AlgebraicGeometry
