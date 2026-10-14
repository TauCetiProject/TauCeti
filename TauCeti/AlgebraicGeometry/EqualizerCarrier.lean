/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Underlying points of equalizers of schemes over a base

Let `a b : Y ⟶ W` be morphisms of schemes over a base `S`, and let `y : Z ⟶ Y` be another
morphism over `S`. The equalizer of `y ≫ a` and `y ≫ b` is the inverse image along `y` of the
equalizer of `a` and `b`. This file records the consequence for underlying points: a point of `Z`
lies in the image of the equalizer of `y ≫ a` and `y ≫ b` exactly when its image under `y` lies in
the image of the equalizer of `a` and `b`. It is the tool for describing the points with values
in a scheme `Z` that avoid a locus cut out by equalizers, such as the locus where a point of a
group scheme meets the identity section.

For two sections `Q` and `R` of a scheme `X` over `S`, the image of their equalizer is the set of
points of `S` at which `Q` and `R` take the same value: a section induces an isomorphism on
residue fields, so two sections that agree at a point agree on its residue field. Over a field
`K`, the base `Spec K` has a single point, so two `K`-points have empty equalizer exactly when
they differ.

## Main results

* `TauCeti.AlgebraicGeometry.range_equalizer_ι_left_comp`: the image of the equalizer of
  `y ≫ a` and `y ≫ b` is the preimage under `y` of the image of the equalizer of `a` and `b`.
* `TauCeti.AlgebraicGeometry.isEmpty_equalizer_comp_iff`: the equalizer of `y ≫ a` and `y ≫ b`
  is empty exactly when the image of `y` misses the equalizer of `a` and `b`.
* `TauCeti.AlgebraicGeometry.range_equalizer_ι_left_of_section`: the image of the equalizer of
  two sections is the set of points of the base at which they agree.
* `TauCeti.AlgebraicGeometry.isEmpty_equalizer_iff_forall_ne`: two sections have empty equalizer
  exactly when they agree at no point of the base.
* `TauCeti.AlgebraicGeometry.isEmpty_equalizer_iff_ne`: over a field, two points of a scheme
  have empty equalizer exactly when they are distinct.
-/

public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

universe u

namespace TauCeti.AlgebraicGeometry

variable {S : Scheme.{u}} {Z Y W : Over S}

/-- The equalizer of `a` and `b` is empty exactly when that of `a'` and `b'` is, for `a = a'` and
`b = b'`. The instance argument of `equalizer` depends on the two morphisms, so `rw` cannot
replace them in place inside `IsEmpty (equalizer a b).left`; this lemma does. -/
theorem isEmpty_equalizer_congr {a a' b b' : Y ⟶ W} (ha : a = a') (hb : b = b') :
    IsEmpty (equalizer a b).left ↔ IsEmpty (equalizer a' b').left := by
  subst ha hb
  rfl

/-- **Points of the equalizer of two composites.** For morphisms `a b : Y ⟶ W` and `y : Z ⟶ Y` of
schemes over `S`, a point of `Z` lies in the image of the equalizer of `y ≫ a` and `y ≫ b` exactly
when its image under `y` lies in the image of the equalizer of `a` and `b`. -/
theorem range_equalizer_ι_left_comp (y : Z ⟶ Y) (a b : Y ⟶ W) :
    Set.range (equalizer.ι (y ≫ a) (y ≫ b)).left =
      y.left ⁻¹' Set.range (equalizer.ι a b).left := by
  ext t
  constructor
  · rintro ⟨w, rfl⟩
    -- the equalizer of `y ≫ a` and `y ≫ b` maps to the equalizer of `a` and `b` over `y`
    let k := equalizer.lift (equalizer.ι (y ≫ a) (y ≫ b) ≫ y) (by
      simpa using equalizer.condition (y ≫ a) (y ≫ b))
    refine ⟨k.left w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι, Over.comp_left,
      Scheme.Hom.comp_apply]
  · rintro ⟨z, hz⟩
    -- the fibre product of `y` and the equalizer of `a` and `b` maps to the equalizer of `y ≫ a`
    -- and `y ≫ b`, and it has a point over `t`
    obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback t z hz.symm
    let V : Over S := Over.mk (pullback.fst y.left (equalizer.ι a b).left ≫ Z.hom)
    let v : V ⟶ Z := Over.homMk (pullback.fst y.left (equalizer.ι a b).left)
    have hv : v ≫ y ≫ a = v ≫ y ≫ b := by
      ext1
      have h := congrArg CommaMorphism.left (equalizer.condition a b)
      simp only [Over.comp_left] at h
      simp only [v, Over.comp_left, Over.homMk_left]
      rw [reassoc_of% pullback.condition, h, ← reassoc_of% pullback.condition]
    refine ⟨(equalizer.lift v hv).left p, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
    exact hp

/-- **Emptiness of the equalizer of two composites.** For morphisms `a b : Y ⟶ W` and
`y : Z ⟶ Y` of schemes over `S`, the equalizer of `y ≫ a` and `y ≫ b` is empty exactly when no
point of `Z` is mapped by `y` into the equalizer of `a` and `b`. -/
theorem isEmpty_equalizer_comp_iff (y : Z ⟶ Y) (a b : Y ⟶ W) :
    IsEmpty (equalizer (y ≫ a) (y ≫ b)).left ↔
      Disjoint (Set.range y.left) (Set.range (equalizer.ι a b).left) := by
  rw [← Set.range_eq_empty_iff, range_equalizer_ι_left_comp, Set.preimage_eq_empty_iff,
    disjoint_comm]

/-- **Where two sections agree.** For sections `Q` and `R` of a scheme `X` over `S`, the image of
their equalizer is the set of points of `S` at which `Q` and `R` take the same value. -/
theorem range_equalizer_ι_left_of_section {X : Over S} (Q R : 𝟙_ (Over S) ⟶ X) :
    Set.range (equalizer.ι Q R).left = {s | Q.left s = R.left s} := by
  ext s
  refine ⟨?_, fun hs ↦ ?_⟩
  · rintro ⟨w, rfl⟩
    have h := congrArg (fun k ↦ k.left w) (equalizer.condition Q R)
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    exact h
  · -- the point `t : Spec κ(s) ⟶ S` factors through the equalizer
    let t := S.fromSpecResidueField s
    obtain ⟨p⟩ : Nonempty (Spec (S.residueField s)) := inferInstance
    have hp : t p = s := Scheme.fromSpecResidueField_apply s p
    have ht : t ≫ Q.left = t ≫ R.left :=
      (comp_eq_comp_iff_of_section (f := X.hom) (by simp) (by simp) t p).mpr
        ((congrArg Q.left hp).trans (hs.trans (congrArg R.left hp).symm))
    have hy : CartesianMonoidalCategory.toUnit (Over.mk t) ≫ Q =
        CartesianMonoidalCategory.toUnit (Over.mk t) ≫ R := by
      ext1
      simpa using ht
    refine ⟨(equalizer.lift _ hy).left p, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
    exact hp

/-- Two sections `Q` and `R` of a scheme `X` over `S` have empty equalizer exactly when they agree
at no point of `S`. -/
theorem isEmpty_equalizer_iff_forall_ne {X : Over S} (Q R : 𝟙_ (Over S) ⟶ X) :
    IsEmpty (equalizer Q R).left ↔ ∀ s, Q.left s ≠ R.left s := by
  rw [← Set.range_eq_empty_iff, range_equalizer_ι_left_of_section, Set.eq_empty_iff_forall_notMem]
  rfl

/-- **Equalizers of points over a field.** Over a field `K`, two `K`-points of a scheme over
`Spec K` have empty equalizer exactly when they are distinct: `Spec K` has a single point, and
two sections agreeing there are equal. -/
theorem isEmpty_equalizer_iff_ne {K : Type u} [Field K] {X : Over (Spec (.of K))}
    (P Q : 𝟙_ (Over (Spec (.of K))) ⟶ X) :
    IsEmpty (equalizer P Q).left ↔ P ≠ Q := by
  obtain ⟨s⟩ : Nonempty (Spec (.of K)) := inferInstance
  rw [isEmpty_equalizer_iff_forall_ne]
  refine ⟨fun h hPQ ↦ h s (by rw [hPQ]), fun hPQ t ht ↦ hPQ ?_⟩
  ext1
  simpa using (comp_eq_comp_iff_of_section (f := X.hom)
    (by simp) (by simp) (𝟙 _) t).mpr ht

end TauCeti.AlgebraicGeometry
