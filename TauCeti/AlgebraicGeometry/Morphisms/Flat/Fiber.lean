/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import TauCeti.CategoryTheory.MorphismProperty.Limits
import TauCeti.RingTheory.Flat.Fiber

/-!
# The fibrewise criterion for flatness of finite morphisms

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes, with `f` finite and locally of finite
presentation and `X` flat over `S`. If for every point `s` of `S` the base change of `f` to the
fibre `Y_s = g.fiber s`, that is `X ×_Y Y_s ⟶ Y_s`, is flat, then `f` is flat
(`AlgebraicGeometry.Scheme.Hom.flat_of_flat_pullback_fiberι`). No Noetherian hypothesis is
needed.

This turns flatness over fields into flatness over an arbitrary base: for a finite morphism
between two families over `S` (for instance multiplication by a nonzero integer on an elliptic
curve over `S`), flatness of `f` reduces to flatness of its restrictions to the fibres, which are
morphisms of schemes over fields.

The proof reduces to `S`, `Y` and `X` affine and then applies the algebraic criterion
`Module.Flat.of_flat_fiber` to the finitely presented `Γ(Y)`-module `Γ(X)`. Along the way the
hypothesis is used in the equivalent form that the base change of `f` along
`Y ×_S Spec K ⟶ Y` is flat for every field `K` and every morphism `Spec K ⟶ S`; every such
morphism factors through the residue field of its image point.

## Main results

* `AlgebraicGeometry.Scheme.Hom.flat_of_flat_pullback_fiberι`: the fibrewise criterion for
  flatness of a finite, locally finitely presented morphism.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, troisième partie, Théorème 11.3.10,
  the *critère de platitude par fibres*.
-/

public section

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}}

/-- Precomposition with an isomorphism keeps a morphism flat. Inside the main proof below, instance
search for this times out, so it is stated separately. -/
private lemma flat_iso_hom_comp {X' Z : Scheme.{u}} (e : X' ≅ X) (k : X ⟶ Z) (h : Flat k) :
    Flat (e.hom ≫ k) :=
  inferInstance

/-- The affine case of `flat_of_flat_baseChange_field`, for `Spec A ⟶ Spec B ⟶ Spec R`, by the
algebraic criterion `Module.Flat.of_flat_fiber`. -/
private lemma flat_SpecMap_of_flat_baseChange_field {R B A : CommRingCat.{u}} (φ : B ⟶ A)
    (ψ : R ⟶ B) [IsFinite (Spec.map φ)] [LocallyOfFinitePresentation (Spec.map φ)]
    [Flat (Spec.map φ ≫ Spec.map ψ)]
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ Spec R),
      Flat (pullback.snd (Spec.map φ) (pullback.fst (Spec.map ψ) s))) :
    Flat (Spec.map φ) := by
  have hfin : φ.hom.Finite := (IsFinite.SpecMap_iff _).mp ‹_›
  have hfp : φ.hom.FinitePresentation := HasRingHomProperty.Spec_iff.mp ‹_›
  have hflat : (φ.hom.comp ψ.hom).Flat := by
    rwa [← CommRingCat.hom_comp, ← Flat.SpecMap_iff, Spec.map_comp]
  rw [Flat.SpecMap_iff]
  algebraize [ψ.hom, φ.hom, φ.hom.comp ψ.hom]
  have : Module.FinitePresentation B A := .of_finite_of_finitePresentation _ _
  refine Module.Flat.of_flat_fiber (R := R) fun p _ ↦ ?_
  set κ := p.ResidueField
  set F := B ⊗[R] κ
  have h₁ := h κ (Spec.map (CommRingCat.ofHom (algebraMap R κ)))
  -- `algebraize` defines the algebra structures through `ψ` and `φ`.
  have e₁ : ψ = CommRingCat.ofHom (algebraMap R B) := rfl
  have e₂ : φ = CommRingCat.ofHom (algebraMap B A) := rfl
  -- The base change of `Spec A ⟶ Spec B` to the fibre `Spec F` is `Spec` of `F ⟶ A ⊗[B] F`.
  rw [e₁, e₂, ← pullbackSpecIso_hom_fst' R B κ] at h₁
  have h₂ := MorphismProperty.pullback_snd_of_comp_eq (P := @Flat) _ _ _
    (Iso.inv_hom_id_assoc (pullbackSpecIso R B κ) _) h₁
  rw [← pullbackSpecIso_hom_snd B A F] at h₂
  have h₃ := flat_iso_hom_comp (pullbackSpecIso B A F).symm _ h₂
  rw [Iso.symm_hom, Iso.inv_hom_id_assoc, Flat.SpecMap_iff] at h₃
  rw [← RingHom.flat_algebraMap_iff]
  have : algebraMap F (F ⊗[B] A) =
      (Algebra.TensorProduct.comm B A F).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := B) (A := A) (B := F)).toRingHom := by
    ext x <;> simp [F, κ]
  rw [this]
  exact .comp h₃ (.of_bijective (Algebra.TensorProduct.comm B A F).bijective)

/-- The fibrewise criterion with the fibres replaced by base changes to arbitrary fields. -/
private theorem flat_of_flat_baseChange_field (f : X ⟶ Y) (g : Y ⟶ S) [IsFinite f]
    [LocallyOfFinitePresentation f] [Flat (f ≫ g)]
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S),
      Flat (pullback.snd f (pullback.fst g s))) :
    Flat f := by
  have : IsZariskiLocalAtTarget @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget @Flat.{u} (Q := @RingHom.Flat)
  wlog hS : ∃ R, S = Spec R generalizing X Y S with H
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat.{u}) (S.affineCover.pullback₁ g)]
    intro (i : S.affineCover.I₀)
    dsimp [Scheme.Cover.pullbackHom]
    set u := S.affineCover.f i
    have : Flat (pullback.snd f (pullback.fst g u) ≫ pullback.snd g u) := by
      rw [← pullbackRightPullbackFstIso_hom_snd]
      exact flat_iso_hom_comp _ _ inferInstance
    refine H (pullback.snd f (pullback.fst g u)) (pullback.snd g u) (fun K _ s ↦ ?_) ⟨_, rfl⟩
    exact MorphismProperty.pullback_snd_pullback_snd (P := @Flat) f _ _ _
      (pullbackLeftPullbackSndIso g u s).hom (by simp) (h K (s ≫ u))
  obtain ⟨R, rfl⟩ := hS
  wlog hY : ∃ B, Y = Spec B generalizing X Y with H
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat.{u}) Y.affineCover]
    intro j
    set v := Y.affineCover.f j
    dsimp [Scheme.Cover.pullbackHom]
    have : Flat (pullback.snd f v ≫ v ≫ g) := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
      exact Flat.comp _ _
    refine H (pullback.snd f v) (v ≫ g) (fun K _ s ↦ ?_) ⟨_, rfl⟩
    refine MorphismProperty.pullback_snd_pullback_snd (P := @Flat) f _ _ _
      ((pullbackRightPullbackFstIso g s v).inv ≫ pullback.snd v (pullback.fst g s)) ?_ (h K s)
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      pullbackRightPullbackFstIso_inv_fst]
  obtain ⟨B, rfl⟩ := hY
  wlog hX : ∃ A, X = Spec A generalizing X with H
  · have : IsAffine X := isAffine_of_isAffineHom f
    have : Flat ((X.isoSpec.inv ≫ f) ≫ g) := by rw [Category.assoc]; infer_instance
    have := H (X.isoSpec.inv ≫ f)
      (fun K _ s ↦ MorphismProperty.pullback_snd_comp_left (P := @Flat) f _ _ inferInstance (h K s))
      ⟨_, rfl⟩
    rw [← X.isoSpec.hom_inv_id_assoc f]
    infer_instance
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  exact flat_SpecMap_of_flat_baseChange_field φ ψ h

/-- **The fibrewise criterion for flatness of a finite morphism.** Let `f : X ⟶ Y` be finite and
locally of finite presentation, and `g : Y ⟶ S` such that `X` is flat over `S`. If for every
point `s` of `S` the base change `X ×_Y Y_s ⟶ Y_s` of `f` to the fibre `Y_s` of `g` is flat, then
`f` is flat. -/
theorem Scheme.Hom.flat_of_flat_pullback_fiberι (f : X ⟶ Y) (g : Y ⟶ S) [IsFinite f]
    [LocallyOfFinitePresentation f] [Flat (f ≫ g)]
    (h : ∀ s : S, Flat (pullback.snd f (g.fiberι s))) : Flat f := by
  refine flat_of_flat_baseChange_field f g fun K _ s ↦ ?_
  rw [← Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S s]
  exact MorphismProperty.pullback_snd_pullback_fst_comp (P := @Flat) f g _ _ (h _)

end AlgebraicGeometry
