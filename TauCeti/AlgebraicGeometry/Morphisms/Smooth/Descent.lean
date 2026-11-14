/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.PureRelativeDimension
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Descent

/-!
# Descent of smooth relative dimension

Being smooth of relative dimension `n` descends along fpqc morphisms on the base, and hence also
along fppf and étale covers. Indeed, a morphism is smooth of relative dimension `n` exactly when
it is smooth and has pure relative dimension `n`
(`TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension`), and
both smoothness and syntomicity of relative dimension `n` satisfy fpqc descent.

On the source, if `f : X ⟶ Y` is smooth and `p : X' ⟶ X` is étale and surjective, then `f` is
smooth of relative dimension `n` if and only if `p ≫ f` is. Over a field `Y = Spec k`, a closed
point `x` of `X` has a closed preimage `x'` in the Jacobson space `X'`, and the étale morphism `p`
preserves the Krull dimension of the Noetherian local ring at `x'`. Over a general base `Y`,
passing to the fibres over the residue fields of `Y` reduces the claim to the field case and
establishes pure relative dimension `n` of `f`.

## Main results

* `AlgebraicGeometry.SmoothOfRelativeDimension.descendsAlong_surjective_inf_flat_inf_quasicompact`:
  smoothness of relative dimension `n` satisfies fpqc descent on the target.
* `AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_etale_of_surjective`: if `f : X ⟶ Y` is
  smooth, `p : X' ⟶ X` is étale and surjective, and `p ≫ f` is smooth of relative dimension `n`,
  then `f` is smooth of relative dimension `n`.
* `AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_comp_iff_of_etale_of_surjective`: for
  `p : X' ⟶ X` étale and surjective and `f : X ⟶ Y` smooth, `p ≫ f` is smooth of relative
  dimension `n` if and only if `f` is.

## References

* [Stacks Project, Tag 02K5](https://stacks.math.columbia.edu/tag/02K5): descent of smoothness.
* [Stacks Project, Tag 04N7](https://stacks.math.columbia.edu/tag/04N7): invariance of relative
  dimension along étale morphisms.
-/

public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SmoothOfRelativeDimension

/-- Smoothness of fixed relative dimension is invariant under isomorphisms. -/
instance (n : ℕ) : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} n) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- Smoothness of fixed relative dimension is Zariski-local on the source. -/
instance (n : ℕ) : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} n) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension n)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))

/-- Smoothness of fixed relative dimension is Zariski-local on the target. -/
instance (n : ℕ) : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{u} n) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension n)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))

/-- **Smooth morphisms of relative dimension `n` satisfy fpqc descent.** If the base change of
`g` along a surjective, flat, quasi-compact morphism is smooth of relative dimension `n`, then so
is `g`. By Mathlib's general reduction from fpqc to fppf descent for target-local properties, the
same holds along surjective, flat morphisms locally of finite presentation. -/
instance descendsAlong_surjective_inf_flat_inf_quasicompact (n : ℕ) :
    MorphismProperty.DescendsAlong (@SmoothOfRelativeDimension.{u} n)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine DescendsAlong.mk' fun {X Y Z f g} _ hf h ↦ ?_
  have : SmoothOfRelativeDimension n (pullback.fst f g) := h
  have hsm : Smooth (pullback.fst f g) := SmoothOfRelativeDimension.smooth n _
  have hsyn : SyntomicOfRelativeDimension n (pullback.fst f g) := inferInstance
  have : Smooth g := of_pullback_fst_of_descendsAlong hf hsm
  have : SyntomicOfRelativeDimension n g := of_pullback_fst_of_descendsAlong hf hsyn
  exact (smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension g).mpr ⟨‹_›, inferInstance⟩

-- Over a field, if `f : X ⟶ Spec k` is smooth, `p : X' ⟶ X` is étale and surjective, and
-- `p ≫ f` is smooth of relative dimension `n`, then `f` is smooth of relative dimension `n`.
private theorem of_comp_of_etale_of_surjective_field {k : Type u} [Field k] {X X' : Scheme.{u}}
    {n : ℕ} (p : X' ⟶ X) (f : X ⟶ Spec (.of k)) [Etale p] [Surjective p] [Smooth f]
    [SmoothOfRelativeDimension n (p ≫ f)] :
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
theorem of_comp_of_etale_of_surjective {X X' Y : Scheme.{u}} {n : ℕ} (p : X' ⟶ X) (f : X ⟶ Y)
    [Etale p] [Surjective p] [Smooth f] [SmoothOfRelativeDimension n (p ≫ f)] :
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

end AlgebraicGeometry.SmoothOfRelativeDimension

namespace AlgebraicGeometry.Scheme.Hom

/-- For an étale surjective morphism `p : X' ⟶ X` and a smooth morphism `f : X ⟶ Y`, the
composite `p ≫ f` is smooth of relative dimension `n` if and only if `f` is. -/
theorem smoothOfRelativeDimension_comp_iff_of_etale_of_surjective {X X' Y : Scheme.{u}} {n : ℕ}
    (p : X' ⟶ X) [Etale p] [Surjective p] (f : X ⟶ Y) [Smooth f] :
    SmoothOfRelativeDimension n (p ≫ f) ↔ SmoothOfRelativeDimension n f :=
  ⟨fun _ ↦ SmoothOfRelativeDimension.of_comp_of_etale_of_surjective p f,
    fun _ ↦ Nat.zero_add n ▸ (inferInstance : SmoothOfRelativeDimension (0 + n) (p ≫ f))⟩

end AlgebraicGeometry.Scheme.Hom
