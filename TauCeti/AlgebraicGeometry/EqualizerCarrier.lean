/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Underlying points of equalizers of schemes over a base

Let `a b : Y ⟶ W` be morphisms of schemes over a base `S`, and let `y : Z ⟶ Y` be another
morphism over `S`. The equalizer of `y ≫ a` and `y ≫ b` is the inverse image along `y` of the
equalizer of `a` and `b`. This file records the consequence for underlying points: a point of `Z`
lies in the image of the equalizer of `y ≫ a` and `y ≫ b` exactly when its image under `y` lies in
the image of the equalizer of `a` and `b`. It is the tool for describing the points with values
in a scheme `Z` that avoid a locus cut out by equalizers, such as the locus where a point of a
group scheme meets the identity section.

Over a field `K`, the equalizer of two `K`-points of a separated `K`-scheme is a closed subscheme
of the one-point reduced scheme `Spec K`, so it is empty exactly when the two points differ.

## Main results

* `AlgebraicGeometry.range_equalizer_ι_left_comp`: the image of the equalizer of `y ≫ a` and
  `y ≫ b` is the preimage under `y` of the image of the equalizer of `a` and `b`.
* `AlgebraicGeometry.isEmpty_equalizer_comp_iff`: the equalizer of `y ≫ a` and `y ≫ b` is empty
  exactly when the image of `y` misses the equalizer of `a` and `b`.
* `AlgebraicGeometry.isEmpty_equalizer_iff_ne`: over a field, two points of a separated scheme
  have empty equalizer exactly when they are distinct.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe u

namespace AlgebraicGeometry

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

/-- **Equalizers of points over a field.** Over a field `K`, two `K`-points of a separated scheme
over `Spec K` have empty equalizer exactly when they are distinct: a nonempty equalizer is a
surjective closed immersion into the reduced scheme `Spec K`, hence an isomorphism. -/
theorem isEmpty_equalizer_iff_ne {K : Type u} [Field K] {X : Over (Spec (.of K))}
    [IsSeparated X.hom] (P Q : 𝟙_ (Over (Spec (.of K))) ⟶ X) :
    IsEmpty (equalizer P Q).left ↔ P ≠ Q := by
  obtain ⟨s⟩ : Nonempty (Spec (.of K)) := inferInstance
  refine ⟨fun h hPQ ↦ ?_, fun hPQ ↦ ?_⟩
  · subst hPQ
    exact h.elim ((equalizer.lift (𝟙 (𝟙_ (Over (Spec (.of K))))) rfl : _ ⟶ equalizer P P).left s)
  · refine not_nonempty_iff.mp fun ⟨e⟩ ↦ hPQ ?_
    have : Surjective (equalizer.ι P Q).left :=
      ⟨fun t ↦ ⟨e, Subsingleton.elim (α := Spec (.of K)) _ _⟩⟩
    have : IsIso (equalizer.ι P Q).left :=
      isIso_of_isClosedImmersion_of_surjective (Y := Spec (.of K)) _
    have : IsIso ((Over.forget _).map (equalizer.ι P Q)) := this
    have : IsIso (equalizer.ι P Q) := isIso_of_reflects_iso _ (Over.forget _)
    exact (cancel_epi (equalizer.ι P Q)).mp (equalizer.condition P Q)

end AlgebraicGeometry
