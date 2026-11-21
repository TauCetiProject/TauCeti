/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.PureRelativeDimension
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Scheme.Regular.Descent

/-!
# Smoothness along flat and étale surjections on the source

Smoothness can be checked after a flat surjective presentation of the source. This supports
smooth quotient constructions and complements descent after base change on the target.

The resulting morphism must be locally of finite presentation; over a field, local finite
type suffices. These finiteness hypotheses do not descend along arbitrary flat surjections
without additional covering hypotheses. The covering morphism itself need not be locally
finitely presented or quasi-compact.

Similarly, for a smooth morphism `f : X ⟶ Y` and an étale surjective morphism `p : X' ⟶ X`
on the source, `f` is smooth of relative dimension `n` if and only if `p ≫ f` is
(`AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_comp_iff_of_etale_of_surjective`).

## Main results

* `AlgebraicGeometry.Smooth.of_comp_surjective`: smoothness descends along a flat surjection
  on the source when the resulting morphism is locally of finite presentation.
* `AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_etale_of_surjective`: if `f : X ⟶ Y` is
  smooth, `p : X' ⟶ X` is étale and surjective, and `p ≫ f` is smooth of relative dimension `n`,
  then `f` is smooth of relative dimension `n`.
* `AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_comp_iff_of_etale_of_surjective`: for
  `p : X' ⟶ X` étale and surjective and `f : X ⟶ Y` smooth, `p ≫ f` is smooth of relative
  dimension `n` if and only if `f` is.

## References

* The Stacks Project, Tags 05AX, 05B5, 04N7, and 00ON.
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

section SmoothOfRelativeDimension

open MorphismProperty TauCeti.AlgebraicGeometry

-- Over a field, if `f : X ⟶ Spec k` is smooth, `p : X' ⟶ X` is étale and surjective, and
-- `p ≫ f` is smooth of relative dimension `n`, then `f` is smooth of relative dimension `n`.
private theorem SmoothOfRelativeDimension.of_comp_of_etale_of_surjective_field {k : Type u}
    [Field k] {X X' : Scheme.{u}} {n : ℕ} (p : X' ⟶ X) (f : X ⟶ Spec (.of k))
    [Etale p] [Surjective p] [Smooth f] [SmoothOfRelativeDimension n (p ≫ f)] :
    SmoothOfRelativeDimension n f := by
  have := SmoothOfRelativeDimension.smooth n (p ≫ f)
  have : JacobsonSpace X' := LocallyOfFiniteType.jacobsonSpace (p ≫ f)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hdim' :=
    ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (p ≫ f) n).mp inferInstance).2
  refine (smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f n).mpr ⟨‹_›, fun x hx ↦ ?_⟩
  -- The closed fibre `p ⁻¹' {x}` is nonempty in the Jacobson space `X'`, so it contains a closed
  -- point `x'` of `X'`, at which `p` preserves the local Krull dimension.
  obtain ⟨z, hz⟩ := p.surjective x
  obtain ⟨x', hx', hx'c⟩ := nonempty_inter_closedPoints (⟨z, hz⟩ : (p ⁻¹' {x}).Nonempty)
    (hx.preimage p.continuous).isLocallyClosed
  have hpx' : p x' = x := hx'
  rw [← hpx', p.ringKrullDim_stalk_eq_of_etale x']
  exact hdim' x' hx'c

/-- **Smooth relative dimension descends along étale surjective morphisms on the source.** If
`f : X ⟶ Y` is smooth, `p : X' ⟶ X` is étale and surjective, and `p ≫ f` is smooth of relative
dimension `n`, then `f` is smooth of relative dimension `n`. -/
theorem SmoothOfRelativeDimension.of_comp_of_etale_of_surjective {X X' Y : Scheme.{u}} {n : ℕ}
    (p : X' ⟶ X) (f : X ⟶ Y) [Etale p] [Surjective p] [Smooth f]
    [SmoothOfRelativeDimension n (p ≫ f)] :
    SmoothOfRelativeDimension n f := by
  refine (smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension f).mpr ⟨‹_›, ?_⟩
  -- Check pure relative dimension fibrewise over `Y` by reducing to the field case.
  have hfib (y : Y) : SmoothOfRelativeDimension n (f.fiberToSpecResidueField y) := by
    let g := Y.fromSpecResidueField y
    let q : pullback p (pullback.fst f g) ⟶ pullback f g := pullback.snd p (pullback.fst f g)
    have : Etale q :=
      MorphismProperty.of_isPullback (P := @Etale) (IsPullback.of_hasPullback _ _) ‹_›
    have : Surjective q :=
      MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback _ _) ‹_›
    have : Smooth (pullback.snd f g) :=
      MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback f g) ‹_›
    have : SmoothOfRelativeDimension n (pullback.snd (p ≫ f) g) :=
      MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n)
        (IsPullback.of_hasPullback (p ≫ f) g) ‹_›
    have hcomp : q ≫ pullback.snd f g =
        (pullbackRightPullbackFstIso f g p).hom ≫ pullback.snd (p ≫ f) g :=
      (pullbackRightPullbackFstIso f g p).inv_comp_eq.mp (by simp [q])
    have : SmoothOfRelativeDimension n (q ≫ pullback.snd f g) := by
      rw [hcomp]
      exact Nat.zero_add n ▸
        (inferInstance : SmoothOfRelativeDimension (0 + n)
          ((pullbackRightPullbackFstIso f g p).hom ≫ pullback.snd (p ≫ f) g))
    exact of_comp_of_etale_of_surjective_field (k := Y.residueField y) q (pullback.snd f g)
  have hpure (y : Y) : PureRelativeDimension n (f.fiberToSpecResidueField y) :=
    let := hfib y
    inferInstance
  refine (pureRelativeDimension_iff_relativeDimensionLE_and_isPureDimensional_fiber f).mpr
    ⟨⟨fun y ↦ ?_⟩, fun y ↦ ((pureRelativeDimension_iff_of_field _).mp (hpure y)).2⟩
  exact (relativeDimensionLE_iff_of_field _).mp (hpure y).toRelativeDimensionLE

/-- For an étale surjective morphism `p : X' ⟶ X` and a smooth morphism `f : X ⟶ Y`, the
composite `p ≫ f` is smooth of relative dimension `n` if and only if `f` is. -/
theorem Scheme.Hom.smoothOfRelativeDimension_comp_iff_of_etale_of_surjective {X X' Y : Scheme.{u}}
    {n : ℕ} (p : X' ⟶ X) [Etale p] [Surjective p] (f : X ⟶ Y) [Smooth f] :
    SmoothOfRelativeDimension n (p ≫ f) ↔ SmoothOfRelativeDimension n f :=
  ⟨fun _ ↦ SmoothOfRelativeDimension.of_comp_of_etale_of_surjective p f,
    fun _ ↦ Nat.zero_add n ▸ (inferInstance : SmoothOfRelativeDimension (0 + n) (p ≫ f))⟩

end SmoothOfRelativeDimension

end AlgebraicGeometry
