/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Basic
public import Mathlib.AlgebraicGeometry.Fiber
import TauCeti.RingTheory.Syntomic.Fiber

/-!
# Syntomic morphisms are detected on fibres

A morphism `f : X ⟶ Y` is syntomic of relative dimension `n` exactly when it is flat and locally
of finite presentation and each of its fibres `f.fiber y ⟶ Spec κ(y)` over a residue field is
syntomic of relative dimension `n`
(`TauCeti.AlgebraicGeometry.syntomicOfRelativeDimension_iff_flat_and_fiberToSpecResidueField`).

Both sides are local on the source and the target, so the converse direction reduces to a morphism
`Spec A ⟶ Spec R`, where it is the fibrewise criterion for standard syntomic ring maps
(`TauCeti.locally_isStandardSyntomicOfRelativeDimension_of_fiber`): the fibre of
`Spec A ⟶ Spec R` over a prime `p` is `Spec (κ(p) ⊗[R] A) ⟶ Spec κ(p)`
(`AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso`).

## Main results

* `TauCeti.AlgebraicGeometry.SyntomicOfRelativeDimension.of_fiberToSpecResidueField`: a flat
  morphism locally of finite presentation whose fibres are syntomic of relative dimension `n` is
  syntomic of relative dimension `n`.
* `TauCeti.AlgebraicGeometry.syntomicOfRelativeDimension_iff_flat_and_fiberToSpecResidueField`:
  the fibrewise characterization of syntomic morphisms of relative dimension `n`.

## References

* The Stacks Project, Morphisms of Schemes, Section *Syntomic morphisms*: a flat morphism locally of
  finite presentation is syntomic if and only if its fibres are local complete intersections.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {n : ℕ}

/-- The affine case of the fibrewise criterion: a flat finitely presented `R`-algebra `A` whose
fibres over the points of `Spec R` are syntomic of relative dimension `n` gives a syntomic morphism
`Spec A ⟶ Spec R` of relative dimension `n`. -/
private theorem syntomicOfRelativeDimension_SpecMap_of_fiberToSpecResidueField {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    [hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap R A)))]
    [hfp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R A)))]
    (h : ∀ y, SyntomicOfRelativeDimension n
      ((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiberToSpecResidueField y)) :
    SyntomicOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom,
    RingHom.flat_algebraMap_iff] at hfl
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation), CommRingCat.hom_ofHom,
    RingHom.finitePresentation_algebraMap] at hfp
  rw [syntomicOfRelativeDimension_SpecMap_iff, CommRingCat.hom_ofHom]
  refine locally_isStandardSyntomicOfRelativeDimension_of_fiber fun p _ ↦ ?_
  -- The fibre over `p` is `Spec (κ(p) ⊗[R] A) ⟶ Spec κ(p)`.
  have hp := h ⟨p, inferInstance⟩
  rw [MorphismProperty.arrow_mk_iso_iff (@SyntomicOfRelativeDimension n)
    (Spec.fiberToSpecResidueFieldIso R A ⟨p, inferInstance⟩),
    syntomicOfRelativeDimension_SpecMap_iff, CommRingCat.hom_ofHom] at hp
  exact hp

/-- **The fibrewise criterion for syntomic morphisms.** A flat morphism locally of finite
presentation, each of whose fibres `f.fiber y ⟶ Spec κ(y)` over a residue field is syntomic of
relative dimension `n`, is syntomic of relative dimension `n`. -/
theorem SyntomicOfRelativeDimension.of_fiberToSpecResidueField {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ y, SyntomicOfRelativeDimension n (f.fiberToSpecResidueField y)) :
    SyntomicOfRelativeDimension n f := by
  wlog hY : ∃ R, Y = Spec R generalizing X Y with H
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @SyntomicOfRelativeDimension n)
      Y.affineCover]
    intro i
    refine H (pullback.snd f (Y.affineCover.f i)) (fun y ↦ ?_) ⟨_, rfl⟩
    -- The fibres of a base change are base changes of the fibres.
    exact MorphismProperty.of_isPullback
      (isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback _ _) y) (h _)
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ A, X = Spec A generalizing X with H
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @SyntomicOfRelativeDimension n)
      X.affineCover]
    intro i
    refine H (X.affineCover.f i ≫ f) (fun y ↦ ?_) ⟨_, rfl⟩
    -- The fibres of the restriction of `f` to an open subscheme are open subschemes of the fibres
    -- of `f`. The fibre morphism `fiberToSpecResidueField` is by definition this `pullback.snd`.
    have : SyntomicOfRelativeDimension n
        (pullback.snd (X.affineCover.f i ≫ f) ((Spec R).fromSpecResidueField y)) := by
      refine (MorphismProperty.cancel_left_of_respectsIso (P := @SyntomicOfRelativeDimension n)
        (pullbackRightPullbackFstIso f _ (X.affineCover.f i)).hom _).mp ?_
      rw [pullbackRightPullbackFstIso_hom_snd]
      have hy : SyntomicOfRelativeDimension n (pullback.snd f ((Spec R).fromSpecResidueField y)) :=
        h y
      exact IsZariskiLocalAtSource.comp hy _
    exact this
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  algebraize [φ.hom]
  have hφ : φ = CommRingCat.ofHom (algebraMap R A) := by
    ext
    simp [RingHom.algebraMap_toAlgebra]
  rw [hφ] at h ‹Flat _› ‹LocallyOfFinitePresentation _› ⊢
  exact syntomicOfRelativeDimension_SpecMap_of_fiberToSpecResidueField h

/-- A morphism is syntomic of relative dimension `n` exactly when it is flat and locally of finite
presentation and each of its fibres `f.fiber y ⟶ Spec κ(y)` over a residue field is syntomic of
relative dimension `n`. -/
theorem syntomicOfRelativeDimension_iff_flat_and_fiberToSpecResidueField {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    SyntomicOfRelativeDimension n f ↔ Flat f ∧ LocallyOfFinitePresentation f ∧
      ∀ y, SyntomicOfRelativeDimension n (f.fiberToSpecResidueField y) := by
  refine ⟨fun hf ↦ ⟨SyntomicOfRelativeDimension.flat n f,
    SyntomicOfRelativeDimension.locallyOfFinitePresentation n f,
    fun y ↦ inferInstanceAs (SyntomicOfRelativeDimension n (pullback.snd _ _))⟩,
    fun ⟨_, _, h⟩ ↦ ?_⟩
  exact SyntomicOfRelativeDimension.of_fiberToSpecResidueField f h

end TauCeti.AlgebraicGeometry
