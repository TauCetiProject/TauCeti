/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Basic results on roots of unity

This file records a criterion for a root of unity congruent to `1` modulo an ideal to equal `1`.

## Main results

* `TauCeti.eq_one_of_pow_eq_one_of_sub_one_mem`: in a domain, a root of unity of invertible order
  that is congruent to `1` modulo a proper ideal is `1`.
-/

public section

noncomputable section

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- In a commutative domain, a root of unity whose order is invertible and which is congruent to
`1` modulo a proper ideal is equal to `1`. -/
theorem eq_one_of_pow_eq_one_of_sub_one_mem [IsDomain R] {I : Ideal R} (hI : I ≠ ⊤) {n : ℕ}
    (hn : IsUnit (n : R)) {ζ : R} (hζ : ζ ^ n = 1) (hmem : ζ - 1 ∈ I) : ζ = 1 := by
  by_contra hne
  have hgeom : ∑ i ∈ Finset.range n, ζ ^ i = 0 := by
    have h := geom_sum_mul ζ n
    rw [hζ, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  have hres : Ideal.Quotient.mk I ζ = 1 := by
    have h : Ideal.Quotient.mk I (ζ - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rwa [map_sub, map_one, sub_eq_zero] at h
  refine hI (I.eq_top_of_isUnit_mem ?_ hn)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  have h := congrArg (Ideal.Quotient.mk I) hgeom
  rw [map_sum, map_zero] at h
  simpa [map_pow, hres] using h

end TauCeti
