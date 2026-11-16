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
import TauCeti.AlgebraicGeometry.Scheme.Regular.Descent

/-!
# Smoothness along flat surjections on the source

Smoothness can be checked after a flat surjective presentation of the source. This supports
smooth quotient constructions and complements descent after base change on the target.

The resulting morphism must be locally of finite presentation; over a field, local finite
type suffices. These finiteness hypotheses do not descend along arbitrary flat surjections
without additional covering hypotheses. The covering morphism itself need not be locally
finitely presented or quasi-compact.

## Main results

* `AlgebraicGeometry.Smooth.of_comp_surjective`: smoothness descends along a flat surjection
  on the source when the resulting morphism is locally of finite presentation.

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

end AlgebraicGeometry
