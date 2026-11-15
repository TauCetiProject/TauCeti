/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.PureRelativeDimension
import TauCeti.AlgebraicGeometry.Scheme.Regular.Descent

/-!
# Smoothness along flat surjections on the source

Smoothness can be checked after a flat surjective presentation of the source. This supports
smooth quotient constructions and complements descent after base change on the target.

The resulting morphism must be locally of finite presentation; over a field, local finite
type suffices. These finiteness hypotheses do not descend along arbitrary flat surjections
without additional covering hypotheses. The covering morphism itself need not be locally
finitely presented or quasi-compact.

When the covering surjection `u : X' ⟶ X` is itself smooth of relative dimension `m` and
`u ≫ f` is smooth of relative dimension `m + n`, smoothness of `f` combines with uniqueness of
pure relative dimension on nonempty pullbacks to show that `f` is smooth of relative dimension
`n`. In particular, smooth relative dimension `n` descends along étale surjections (`m = 0`).

## Main results

* `AlgebraicGeometry.Smooth.of_comp_surjective`: smoothness descends along a flat surjection
  on the source when the resulting morphism is locally of finite presentation.
* `AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_surjective_add`: if `u` is surjective
  and smooth of relative dimension `m`, `f` is locally of finite presentation, and `u ≫ f` is
  smooth of relative dimension `m + n`, then `f` is smooth of relative dimension `n`.
* `AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_surjective`: smooth relative dimension
  `n` of a locally finitely presented morphism descends along any surjection smooth of relative
  dimension `0` (in particular, any étale surjection).

## References

* The Stacks Project, Tags 05AX and 05B5.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

private theorem smooth_pullback_snd_comp {X' X S T : Scheme.{u}}
    (u : X' ⟶ X) (f : X ⟶ S) (g : T ⟶ S) [Smooth (u ≫ f)] :
    Smooth (pullback.snd u (pullback.fst f g) ≫ pullback.snd f g) := by
  rw [← pullbackRightPullbackFstIso_hom_snd]
  infer_instance

/-- Smoothness over a field descends through any flat surjection on the source, provided
that the target morphism is locally of finite type. -/
private theorem Smooth.of_comp_surjective_of_field {K : Type u} [Field K] {X' X : Scheme.{u}}
    (u : X' ⟶ X) (f : X ⟶ Spec (.of K)) [Flat u] [Surjective u]
    [LocallyOfFiniteType f] [Smooth (u ≫ f)] : Smooth f := by
  -- Keep the induction hypothesis from becoming a local Smooth instance.
  change id (Smooth f)
  wlog hK : IsAlgClosed K generalizing K X X' with H
  · let g : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
    have := smooth_pullback_snd_comp u f g
    have hsnd := H (pullback.snd u (pullback.fst f g)) (pullback.snd f g)
      (AlgebraicClosure.isAlgClosed K)
    exact MorphismProperty.of_pullback_snd_of_descendsAlong
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsnd
  -- Over an algebraically closed field, regular stalks characterize smoothness.
  have : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := fun x ↦ by
    obtain ⟨x', rfl⟩ := u.surjective x
    have : IsRegularLocalRing (X'.presheaf.stalk x') :=
      TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth (u ≫ f) x'
    exact u.isRegularLocalRing_stalk_of_flat x'
  exact f.smooth_of_isRegularLocalRing_stalk

/-- Smoothness of a locally finitely presented morphism descends through any flat surjection
on its source. The covering morphism need not be quasi-compact or locally finitely presented. -/
theorem Smooth.of_comp_surjective {X' X S : Scheme.{u}} (u : X' ⟶ X) (f : X ⟶ S)
    [Flat u] [Surjective u] [LocallyOfFinitePresentation f] [Smooth (u ≫ f)] : Smooth f := by
  have : Flat f := Flat.of_comp_surjective u f
  refine Smooth.of_smooth_fiberToSpecResidueField f fun s ↦ ?_
  -- Unfold the named fibre so pullback instances can see its projection maps.
  dsimp only [Scheme.Hom.fiber, Scheme.Hom.fiberToSpecResidueField]
  let g := S.fromSpecResidueField s
  have := smooth_pullback_snd_comp u f g
  exact Smooth.of_comp_surjective_of_field (K := S.residueField s)
    (pullback.snd u (pullback.fst f g)) (pullback.snd f g)

/-- If `u : X' ⟶ X` is surjective and smooth of relative dimension `m`, `f : X ⟶ S` is locally
of finite presentation, and `u ≫ f` is smooth of relative dimension `m + n`, then `f` is smooth
of relative dimension `n`. -/
theorem SmoothOfRelativeDimension.of_comp_surjective_add {m n : ℕ} {X' X S : Scheme.{u}}
    (u : X' ⟶ X) (f : X ⟶ S) [SmoothOfRelativeDimension m u] [Surjective u]
    [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension (m + n) (u ≫ f)] :
    SmoothOfRelativeDimension n f := by
  have : Smooth u := SmoothOfRelativeDimension.smooth m u
  have : Smooth (u ≫ f) := SmoothOfRelativeDimension.smooth (m + n) (u ≫ f)
  have : Smooth f := Smooth.of_comp_surjective u f
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth f x
  refine ⟨U, hU, V, hV, hx, e, ?_⟩
  obtain ⟨m', hm'⟩ : ∃ m', (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m' := by
    let := (f.appLE U V e).hom.toAlgebra
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h
    exact ⟨P.dimension, _, _, _, ‹_›, P, rfl⟩
  -- View the chart on `V` as a smooth morphism `Spec Γ(X, V) ⟶ S` of relative dimension `m'`.
  have : SmoothOfRelativeDimension m' (Spec.map (f.appLE U V e)) := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension m')]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hm'
  have : SmoothOfRelativeDimension (m' + 0) (Spec.map (f.appLE U V e) ≫ hU.fromSpec) :=
    inferInstance
  have : SmoothOfRelativeDimension m' (hV.fromSpec ≫ f) := by
    rwa [Nat.add_zero, IsAffineOpen.SpecMap_appLE_fromSpec f hU hV] at this
  -- On the nonempty pullback of `u` along `Spec Γ(X, V) ⟶ X`, compare the two factorizations.
  have : Nonempty ↥(pullback u hV.fromSpec) := by
    obtain ⟨x', hx'⟩ := u.surjective x
    let v : V.toScheme := ⟨x, hx⟩
    have hv : hV.fromSpec (V.toSpecΓ v) = x := by
      rw [← Scheme.Hom.comp_apply, hV.toSpecΓ_fromSpec]
      simp [v]
    obtain ⟨p, -⟩ := Scheme.Pullback.exists_preimage_pullback x' (V.toSpecΓ v) (hx'.trans hv.symm)
    exact ⟨p⟩
  have h₁ : SmoothOfRelativeDimension (0 + (m + n))
      (pullback.fst u hV.fromSpec ≫ u ≫ f) := inferInstance
  have h₂ : SmoothOfRelativeDimension (m + m')
      (pullback.fst u hV.fromSpec ≫ u ≫ f) := by
    rw [pullback.condition_assoc]
    infer_instance
  have hp₁ :=
    ((TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension
      _).mp h₁).2
  have hp₂ :=
    ((TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension
      _).mp h₂).2
  have hmn : 0 + (m + n) = m + m' :=
    TauCeti.AlgebraicGeometry.PureRelativeDimension.unique (pullback.fst u hV.fromSpec ≫ u ≫ f)
  obtain rfl : m' = n := by omega
  exact hm'

/-- Smoothness of relative dimension `n` of a locally finitely presented morphism descends
through any surjection on its source that is smooth of relative dimension `0` (in particular,
any étale surjection). -/
theorem SmoothOfRelativeDimension.of_comp_surjective {n : ℕ} {X' X S : Scheme.{u}}
    (u : X' ⟶ X) (f : X ⟶ S) [SmoothOfRelativeDimension 0 u] [Surjective u]
    [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension n (u ≫ f)] :
    SmoothOfRelativeDimension n f := by
  have : SmoothOfRelativeDimension (0 + n) (u ≫ f) := by simpa
  exact SmoothOfRelativeDimension.of_comp_surjective_add (m := 0) u f

end AlgebraicGeometry
