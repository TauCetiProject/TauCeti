/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import TauCeti.AlgebraicGeometry.Morphisms.Epi
import TauCeti.CategoryTheory.MorphismProperty.Limits
import TauCeti.FieldTheory.IsSepClosed
import TauCeti.RingTheory.Unramified.Fiber

/-!
# The fibre criterion for formal unramifiedness, and equalizers

A morphism locally of finite type is formally unramified exactly when its residue-field fibres
are formally unramified. Thus relative unramifiedness can be established by calculations over
fields, even over a nonreduced or nonnoetherian base and without flatness.

The affine case uses `Algebra.FormallyUnramified.of_formallyUnramified_baseChange_field`.
The passage between arbitrary field-valued points and residue-field fibres uses Mathlib's
factorization of a field-valued point through the residue field of its image.

Dually to Mathlib's `isClosedImmersion_equalizer_ι_left` for separated targets, the equalizer of
two morphisms over `S` into a scheme formally unramified and locally of finite type over `S` is an
open subscheme of their source (`isOpenImmersion_equalizer_ι_left`): it is a base change of the
diagonal, which is an open immersion by Mathlib's `FormallyUnramified.isOpenImmersion_diagonal`.
In particular two sections of an unramified morphism agree on an open subscheme, and two
morphisms into an unramified scheme that agree after a surjective morphism are equal
(`ext_of_surjective_of_formallyUnramified`).

If the target is also separated, two morphisms that agree after a dominant morphism are
equal (`ext_of_isDominant_of_isSeparated_of_formallyUnramified`). Unlike Mathlib's
`ext_of_isDominant_of_isSeparated`, whose equalizer argument this follows, this does not
require a reduced source: the equalizer is open as well as closed.

For the same reason, a morphism formally unramified and locally of finite type is a monomorphism
exactly when it is universally injective
(`AlgebraicGeometry.FormallyUnramified.mono_iff_universallyInjective`): its diagonal is an open
immersion, which is an isomorphism exactly when it is surjective.

Formally unramified morphisms respect isomorphisms (`TauCeti.formallyUnramified_respectsIso`).

The residue field extensions of a morphism formally unramified and locally of finite type are
finite separable, so their embeddings into an extension `Ω'` of a separably closed field `Ω` all
land in `Ω`. Hence lifts of an `Ω`-valued point along such a morphism do not change under extension
of `Ω` (`AlgebraicGeometry.Scheme.Hom.bijective_comp_of_formallyUnramified`); this is why stalks of
étale sheaves at separably closed points do not change under extension of the field. For the same
reason, a point over a separably closed point of the target has a separably closed residue field
(`AlgebraicGeometry.Scheme.Hom.isSepClosed_residueField_of_formallyUnramified`).

## References

* The Stacks Project, Tag 02G8 (the fibre criterion for unramified morphisms).
* The Stacks Project, Tag 05VH (an unramified universally injective morphism is a
  monomorphism).
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace TauCeti

open AlgebraicGeometry

/-- Formally unramified morphisms of schemes respect isomorphisms. -/
instance formallyUnramified_respectsIso :
    MorphismProperty.RespectsIso (@FormallyUnramified : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

end TauCeti

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A morphism locally of finite type is formally unramified if its base change along every
field-valued point of the target is formally unramified. -/
theorem Scheme.Hom.formallyUnramified_of_formallyUnramified_baseChange_field
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ Y),
      FormallyUnramified (pullback.snd f s)) : FormallyUnramified f := by
  -- Instance search needs the scheme universe and ring-hom property fixed explicitly here.
  have : IsZariskiLocalAtTarget @FormallyUnramified.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget @FormallyUnramified.{u}
      (Q := @RingHom.FormallyUnramified)
  have : IsZariskiLocalAtSource @FormallyUnramified.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @FormallyUnramified.{u})
      (Q := @RingHom.FormallyUnramified)
  wlog hY : ∃ R, Y = Spec R generalizing X Y with H
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @FormallyUnramified) Y.affineCover]
    intro i
    refine H (pullback.snd f (Y.affineCover.f i)) (fun K _ s ↦ ?_) ⟨_, rfl⟩
    exact MorphismProperty.pullback_snd_pullback_snd (P := @FormallyUnramified) f _ _ _
      (𝟙 _) (by simp) (h K (s ≫ Y.affineCover.f i))
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S generalizing X with H
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @FormallyUnramified) X.affineCover]
    intro i
    refine H (X.affineCover.f i ≫ f) (fun K _ s ↦ ?_) ⟨_, rfl⟩
    exact MorphismProperty.pullback_snd_comp_left (P := @FormallyUnramified) f s _
      inferInstance (h K s)
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have hft : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp ‹LocallyOfFiniteType _›
  algebraize [φ.hom]
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified),
    ← RingHom.algebraMap_toAlgebra φ.hom, RingHom.formallyUnramified_algebraMap]
  refine Algebra.FormallyUnramified.of_formallyUnramified_baseChange_field fun K _ _ ↦ ?_
  have hK := h K (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  have hφ : φ = CommRingCat.ofHom (algebraMap R S) := by
    ext
    simp [RingHom.algebraMap_toAlgebra]
  rw [hφ, ← pullbackSpecIso_hom_snd R S K] at hK
  have hmap := (MorphismProperty.cancel_left_of_respectsIso (P := @FormallyUnramified.{u})
    (pullbackSpecIso R S K).hom _).mp hK
  let : Algebra K (S ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified),
    CommRingCat.hom_ofHom, ← Algebra.TensorProduct.algebraMap_eq_includeRight,
    RingHom.formallyUnramified_algebraMap] at hmap
  let e : S ⊗[R] K ≃ₐ[K] K ⊗[R] S :=
    { __ := Algebra.TensorProduct.comm R S K, commutes' _ := by
        simp [Algebra.TensorProduct.algebraMap_eq_includeRight] }
  exact Algebra.FormallyUnramified.of_equiv e

/-- A morphism locally of finite type is formally unramified if all its residue-field fibres
are formally unramified. -/
theorem FormallyUnramified.of_formallyUnramified_fiberToSpecResidueField
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (h : ∀ y : Y, FormallyUnramified (f.fiberToSpecResidueField y)) :
    FormallyUnramified f := by
  refine f.formallyUnramified_of_formallyUnramified_baseChange_field fun K _ s ↦ ?_
  rw [← Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y s]
  exact MorphismProperty.pullback_snd_comp (P := @FormallyUnramified) f _ _ (h _)

/-- A morphism locally of finite type is formally unramified exactly when all its residue-field
fibres are formally unramified. -/
theorem FormallyUnramified.iff_formallyUnramified_fiberToSpecResidueField
    (f : X ⟶ Y) [LocallyOfFiniteType f] :
    FormallyUnramified f ↔ ∀ y : Y, FormallyUnramified (f.fiberToSpecResidueField y) := by
  constructor
  · intro hf y
    exact MorphismProperty.of_isPullback (P := @FormallyUnramified.{u})
      (.of_hasPullback f (Y.fromSpecResidueField y)) hf
  · exact FormallyUnramified.of_formallyUnramified_fiberToSpecResidueField f

/-- **Equalizers into an unramified scheme are open.** If `Y` is formally unramified and locally
of finite type over `S`, the equalizer of two morphisms `X ⟶ Y` over `S` is an open subscheme of
`X`: it is the base change of the diagonal of `Y ⟶ S`, which is an open immersion. -/
instance isOpenImmersion_equalizer_ι_left {S : Scheme} {X Y : Over S} [FormallyUnramified Y.hom]
    [LocallyOfFiniteType Y.hom] (f g : X ⟶ Y) : IsOpenImmersion (equalizer.ι f g).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod f g).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert! (inferInstance : IsOpenImmersion (pullback.diagonal Y.hom))
  ext1 <;> simp [← Over.comp_left]

/-- Morphisms into a separated unramified scheme agree if they agree after precomposition
with a dominant morphism. The source may be nonreduced. -/
theorem ext_of_isDominant_of_isSeparated_of_formallyUnramified {W Z : Scheme.{u}}
    {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] [FormallyUnramified s]
    [LocallyOfFiniteType s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹IsSeparated s›
  have : FormallyUnramified Y'.hom := ‹FormallyUnramified s›
  have : LocallyOfFiniteType Y'.hom := ‹LocallyOfFiniteType s›
  have : IsDominant (equalizer.ι f' g').left := by
    apply +allowSynthFailures IsDominant.of_comp (equalizer.lift ι' (by ext1; exact hU)).left
    simpa only [← Over.comp_left, equalizer.lift_ι, ι', Over.homMk_left] using
      (inferInstance : IsDominant ι)
  have : Surjective (equalizer.ι f' g').left :=
    surjective_of_isDominant_of_isClosed_range _ (Scheme.Hom.isClosedEmbedding _).isClosed_range
  have : IsIso (equalizer.ι f' g').left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congrArg (fun k ↦ k.left) (equalizer.condition f' g')

/-- Morphisms into an unramified scheme agree if they agree after precomposition with a
surjective morphism. Neither a reduced source nor a separated target is needed. -/
theorem ext_of_surjective_of_formallyUnramified {W Z : Scheme.{u}} {f g : X ⟶ Y} (s : Y ⟶ Z)
    [FormallyUnramified s] [LocallyOfFiniteType s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [Surjective ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  let ι' : U' ⟶ X' := Over.homMk ι
  have : FormallyUnramified Y'.hom := ‹FormallyUnramified s›
  have : LocallyOfFiniteType Y'.hom := ‹LocallyOfFiniteType s›
  let e := equalizer.lift ι' (f := f') (g := g') (by ext1; exact hU)
  have : Surjective (e.left ≫ (equalizer.ι f' g').left) := by
    simpa only [← Over.comp_left, e, equalizer.lift_ι, ι', Over.homMk_left] using
      (inferInstance : Surjective ι)
  have : Surjective (equalizer.ι f' g').left := Surjective.of_comp e.left _
  have : IsIso (equalizer.ι f' g').left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congrArg (fun k ↦ k.left) (equalizer.condition f' g')

/-- **An unramified morphism is a monomorphism exactly when it is universally injective.**
Stacks, Tag 05VH. -/
theorem FormallyUnramified.mono_iff_universallyInjective (f : X ⟶ Y) [FormallyUnramified f]
    [LocallyOfFiniteType f] : Mono f ↔ UniversallyInjective f := by
  refine ⟨fun _ ↦ inferInstance, fun hf ↦ ?_⟩
  -- the diagonal of `f` is an open immersion, and it is surjective as `f` is universally injective
  rw [← pullback.isIso_diagonal_iff, isIso_iff_isOpenImmersion_and_surjective]
  exact ⟨inferInstance, (UniversallyInjective.iff_diagonal f).1 hf⟩

/-- **Lifts of a separably closed point along an unramified morphism do not change under
extension of the field.** Let `f : X ⟶ Y` be formally unramified and locally of finite type (for
instance étale), `s : Spec Ω ⟶ Y` with `Ω` separably closed and `φ : Spec Ω' ⟶ Spec Ω` for a field
`Ω'`. Then `u ↦ φ ≫ u` is a bijection from the lifts of `s` to `X` onto the lifts of `φ ≫ s`. -/
theorem Scheme.Hom.bijective_comp_of_formallyUnramified (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω]
    [Field Ω'] (φ : Spec (.of Ω') ⟶ Spec (.of Ω)) (s : Spec (.of Ω) ⟶ Y) :
    Function.Bijective fun u : {u : Spec (.of Ω) ⟶ X // u ≫ f = s} ↦
      (⟨φ ≫ u.val, by simp [u.property]⟩ : {v : Spec (.of Ω') ⟶ X // v ≫ f = φ ≫ s}) := by
  refine ⟨fun u v h ↦ Subtype.ext ((cancel_epi φ).mp congr(($h).val)), ?_⟩
  rintro ⟨v, hv⟩
  -- Write `s` and `v` through residue fields, and `φ` as `Spec g`.
  obtain ⟨⟨t, b⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω Y).symm.surjective s
  obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω' X).symm.surjective v
  obtain ⟨g, rfl⟩ : ∃ g, Spec.map g = φ := ⟨_, Spec.map_preimage φ⟩
  have h : (⟨f x, f.residueFieldMap x ≫ a⟩ : Σ y, Y.residueField y ⟶ .of Ω') = ⟨t, b ≫ g⟩ := by
    apply (Scheme.SpecToEquivOfField Ω' Y).symm.injective
    simpa [Scheme.SpecToEquivOfField_symm_apply] using hv
  obtain ⟨e, hab⟩ := Scheme.SpecToEquivOfField_eq_iff.mp h
  dsimp only at e hab
  subst e
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp] at hab
  -- `a` is an embedding of `κ(x)` over `κ(f x)`, which lands in `Ω` since `κ(x)` is separable.
  let := (f.residueFieldMap x).hom.toAlgebra
  let := b.hom.toAlgebra
  let := (b ≫ g).hom.toAlgebra
  let := g.hom.toAlgebra
  have : IsScalarTower (Y.residueField (f x)) Ω Ω' := .of_algebraMap_eq' rfl
  let a' : X.residueField x →ₐ[Y.residueField (f x)] Ω' :=
    { a.hom with commutes' r := congr($hab r) }
  obtain ⟨a₂, ha₂⟩ := (Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits Ω' Ω fun r ↦
    IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable _ r)).surjective a'
  -- Bundle `a₂` as a morphism out of `κ(x)` itself, so that it composes with `f.residueFieldMap x`.
  obtain ⟨c, hc⟩ : ∃ c : X.residueField x ⟶ .of Ω, ∀ r, c.hom r = a₂ r :=
    ⟨CommRingCat.ofHom (a₂ : X.residueField x →+* Ω), fun _ ↦ rfl⟩
  have hca : c ≫ g = a := by
    ext r
    rw [CommRingCat.comp_apply, hc]
    have := congr($ha₂ r)
    rw [Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply] at this
    -- `algebraMap Ω Ω'` is `g` and `a'` is `a`, by construction of the algebra structures.
    exact this
  have hcb : f.residueFieldMap x ≫ c = b := by
    ext r
    rw [CommRingCat.comp_apply, hc]
    exact a₂.commutes r
  refine ⟨⟨(Scheme.SpecToEquivOfField Ω X).symm ⟨x, c⟩, ?_⟩, ?_⟩
  · simp [Scheme.SpecToEquivOfField_symm_apply, ← hcb, Spec.map_comp]
  · ext1
    simp [Scheme.SpecToEquivOfField_symm_apply, ← hca]

/-- **Points over a separably closed point of an unramified morphism.** If `f` is formally
unramified and locally of finite type and the residue field of `f x` is separably closed, then
so is the residue field of `x`: the finite separable extension `κ(f x) → κ(x)` is an isomorphism. -/
theorem Scheme.Hom.isSepClosed_residueField_of_formallyUnramified (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] (x : X)
    [IsSepClosed (Y.residueField (f x))] : IsSepClosed (X.residueField x) := by
  let := (f.residueFieldMap x).hom.toAlgebra
  exact IsSepClosed.of_ringEquiv
    (RingEquiv.ofBijective _ (IsSepClosed.algebraMap_bijective (Y.residueField (f x))
      (X.residueField x)))

end AlgebraicGeometry
