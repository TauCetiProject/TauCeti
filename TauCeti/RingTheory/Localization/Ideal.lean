/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Ideals that become principal in an away localization

If `r • I ≤ (t)` for an element `t` of an ideal `I`, then `I` and `(t)` agree after inverting
`r`. This is how a local equation of an ideal is read off from a relation holding up to a
multiplier, as produced by Nakayama's lemma.

## Main results

* `Ideal.map_eq_span_singleton_of_isUnit`: if `f r` is a unit for a ring homomorphism `f`,
  then `r • I ≤ (t)` and `t ∈ I` imply that `I` generates `(f t)` after applying `f`.
* `Ideal.map_algebraMap_away_eq_span_singleton`: if `r • I ≤ (t)` and `t ∈ I`, then `I`
  generates `(t)` in the localization away from `r`.
-/

public section

open scoped Pointwise

namespace Ideal

/-- If `f r` is a unit, `r • I ≤ (t)`, and `t ∈ I`, then `I` generates the principal ideal
`(f t)` after applying the ring homomorphism `f`. -/
theorem map_eq_span_singleton_of_isUnit {B B' : Type*} [CommSemiring B] [CommSemiring B']
    (f : B →+* B') {I : Ideal B} {r t : B} (ht : t ∈ I) (h : r • I ≤ Ideal.span {t})
    (hr : IsUnit (f r)) :
    I.map f = Ideal.span {f t} := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun i hi ↦ ?_) ?_
  · obtain ⟨b, hb⟩ :=
      Ideal.mem_span_singleton'.mp (h (Submodule.smul_mem_pointwise_smul i r I hi))
    rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ hr, ← map_mul, ← smul_eq_mul, ← hb,
      map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ ht

/-- If `r • I ≤ (t)` for some `t ∈ I`, then `I` generates the principal ideal `(t)` in the
localization away from `r`. -/
theorem map_algebraMap_away_eq_span_singleton {B B' : Type*} [CommSemiring B]
    [CommSemiring B'] [Algebra B B'] {I : Ideal B} {r t : B} [IsLocalization.Away r B']
    (ht : t ∈ I) (h : r • I ≤ Ideal.span {t}) :
    I.map (algebraMap B B') = Ideal.span {algebraMap B B' t} :=
  map_eq_span_singleton_of_isUnit (algebraMap B B') ht h
    (IsLocalization.Away.algebraMap_isUnit (S := B') r)

end Ideal
