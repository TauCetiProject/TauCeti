/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Fiber
import TauCeti.CategoryTheory.MorphismProperty.Limits
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
In particular two sections of an unramified morphism agree on an open subscheme.

## References

* The Stacks Project, Tag 02G8 (the fibre criterion for unramified morphisms).
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

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
  -- Fixing the universe also lets instance search find isomorphism invariance.
  have : MorphismProperty.RespectsIso @FormallyUnramified.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
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

end AlgebraicGeometry
