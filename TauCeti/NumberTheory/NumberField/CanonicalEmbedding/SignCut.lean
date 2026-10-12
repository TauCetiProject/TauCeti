/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Cutting a reflection-invariant subset of the mixed space at a finset of real places

Let `S` be a finset of real places and `A` a subset of the mixed space preserved by the reflection
`negAt {w}` of the real coordinate at each single place `w` of `S`.  The `2 ^ S.card` sign patterns
along `S` then cut `A` into pieces of equal volume, exhausting `A` up to the null set where some
coordinate of `S` vanishes.

Cutting `A` down to the points that are positive at every place of `S` therefore divides its
volume by `2 ^ S.card`, the real coordinates outside `S` staying free.  A set whose membership
depends on the real coordinates only through their absolute values is invariant at every real
place, and for `S` all of the real places the statement is then Mathlib's
`NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_plusPart`.

## Main results

* `TauCeti.NumberField.mixedEmbedding.isOpen_setOfPred_forall_mem_pos`: the points positive at
  every place of a finset of real places form an open set.
* `TauCeti.NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_inter_pos`: for a set invariant
  under reflection at each place of `S`, the volume is `2 ^ S.card` times the volume of the part
  that is positive at every place of `S`.
-/

public section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace TauCeti.NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- A set stable under reflecting the real coordinate at the place `w` has twice the volume of its
part where that coordinate is positive. -/
private theorem volume_eq_two_mul_volume_inter_pos_at {B : Set (mixedSpace K)}
    {w : {w : InfinitePlace K // w.IsReal}}
    (hB : ∀ x : mixedSpace K, negAt ({w} : Set _) x ∈ B ↔ x ∈ B) (hm : MeasurableSet B) :
    volume B = 2 * volume (B ∩ {x | 0 < x.1 w}) := by
  have hmP : MeasurableSet (B ∩ {x : mixedSpace K | 0 < x.1 w}) :=
    hm.inter (measurableSet_lt measurable_const (by fun_prop))
  have hmN : MeasurableSet (B ∩ {x : mixedSpace K | x.1 w < 0}) :=
    hm.inter (measurableSet_lt (by fun_prop) measurable_const)
  -- reflecting at `w` carries the part of `B` negative at `w` onto the part positive at `w`
  have hNP : B ∩ {x : mixedSpace K | x.1 w < 0}
      = negAt ({w} : Set _) ⁻¹' (B ∩ {x : mixedSpace K | 0 < x.1 w}) := by
    ext x
    simp [hB]
  have hcover : (B ∩ {x : mixedSpace K | 0 < x.1 w} ∪ B ∩ {x : mixedSpace K | x.1 w < 0})
      ∪ B ∩ {x : mixedSpace K | x.1 w = 0} = B := by
    ext x
    grind
  have hdisj : Disjoint (B ∩ {x : mixedSpace K | 0 < x.1 w})
      (B ∩ {x : mixedSpace K | x.1 w < 0}) := by
    grind
  -- the slice where the coordinate vanishes is null, so it does not change the volume
  have hvolB : volume B = volume (B ∩ {x : mixedSpace K | 0 < x.1 w}
      ∪ B ∩ {x : mixedSpace K | x.1 w < 0}) := by
    nth_rewrite 1 [← hcover]
    exact measure_congr <| union_ae_eq_left_of_ae_eq_empty <| ae_eq_empty.mpr <|
      measure_mono_null Set.inter_subset_right (volume_eq_zero w)
  rw [hvolB, measure_union hdisj hmN, hNP,
    volume_preserving_negAt.measure_preimage hmP.nullMeasurableSet, two_mul]

omit [NumberField K] in
/-- The points positive at every place of `S` form an open set: it is a finite intersection of
open half spaces. -/
theorem isOpen_setOfPred_forall_mem_pos (S : Finset {w : InfinitePlace K // w.IsReal}) :
    IsOpen {x : mixedSpace K | ∀ w ∈ S, 0 < x.1 w} := by
  simp only [Set.ofPred_forall]
  exact isOpen_biInter_finset fun w _ ↦ isOpen_lt continuous_const (by fun_prop)

open scoped Classical in
/-- **The volume of a sign cut at a finset of real places.**  If reflecting the real coordinate at
any one place of `S` preserves `A`, then prescribing a positive sign at each place of `S` divides
the volume of `A` by `2 ^ S.card`. -/
theorem volume_eq_two_pow_mul_volume_inter_pos (S : Finset {w : InfinitePlace K // w.IsReal})
    {A : Set (mixedSpace K)}
    (hA : ∀ w ∈ S, ∀ x : mixedSpace K, negAt ({w} : Set _) x ∈ A ↔ x ∈ A)
    (hm : MeasurableSet A) : volume A = 2 ^ S.card * volume (A ∩ {x | ∀ w ∈ S, 0 < x.1 w}) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert w S hw ih =>
    -- reflecting at `w` fixes `A`, and it fixes the cut along `S` because `w ∉ S`
    have hstable (x : mixedSpace K) : negAt ({w} : Set _) x ∈ A ∩ {x | ∀ v ∈ S, 0 < x.1 v}
        ↔ x ∈ A ∩ {x | ∀ v ∈ S, 0 < x.1 v} := by
      grind [negAt_apply_isReal_and_notMem]
    simp only [Finset.forall_mem_insert, Set.ofPred_and]
    rw [Finset.card_insert_of_notMem hw, pow_succ,
      ih fun v hv ↦ hA v (Finset.mem_insert_of_mem hv),
      Set.inter_comm {x : mixedSpace K | 0 < x.1 w}, ← Set.inter_assoc,
      volume_eq_two_mul_volume_inter_pos_at hstable
        (hm.inter (isOpen_setOfPred_forall_mem_pos S).measurableSet), mul_assoc]

end TauCeti.NumberField.mixedEmbedding
