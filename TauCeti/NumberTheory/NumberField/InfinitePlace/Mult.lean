/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.Ramification
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Multiplicities of infinite places in an extension

Let `L / K` be an extension of number fields and `v` an infinite place of `K`. The multiplicities
`m_w ∈ {1, 2}` of the infinite places `w ∣ v` of `L` add up to `m_v [L : K]`: above `v` the
multiplicity is `m_w = m_v [L_w : K_v]` (`NumberField.InfinitePlace.mult_mul_finrank`), and the
local degrees above `v` add up to `[L : K]` (`NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank`).

Grouping the infinite places of `L` by their restriction to `K` turns this into a product
formula: for any function `g` on the infinite places of `K`,
`∏_w g(w|_K) ^ m_w = ∏_v g(v) ^ (m_v [L : K])`. This is the archimedean half of the comparison of
heights computed over `K` and over `L`.

## Main results

* `NumberField.InfinitePlace.mem_placesOver`: `w ∈ v.placesOver L ↔ w.LiesOver v`.
* `NumberField.InfinitePlace.sum_mult_eq_mult_mul_finrank`: `∑_{w ∣ v} m_w = m_v [L : K]`.
* `NumberField.InfinitePlace.prod_comap_pow_mult`:
  `∏_w g(w|_K) ^ m_w = ∏_v g(v) ^ (m_v [L : K])`.

## References

* X. Wu, *Diophantine geometry, week 08: arithmetic heights* (2023), §2, Lemma 2.2.
-/

public section

open Module

namespace NumberField.InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- An infinite place of `L` belongs to `v.placesOver L` exactly when it lies over `v`. -/
@[simp]
theorem mem_placesOver {v : InfinitePlace K} {w : InfinitePlace L} :
    w ∈ v.placesOver L ↔ w.LiesOver v :=
  Iff.rfl

variable [NumberField K] [NumberField L]

variable (L) in
open scoped Classical in
/-- The multiplicities of the infinite places of `L` above an infinite place `v` of `K` add up to
the multiplicity of `v` times `[L : K]`. -/
theorem sum_mult_eq_mult_mul_finrank (v : InfinitePlace K) :
    ∑ w ∈ v.placesOver L, w.mult = v.mult * finrank K L := by
  rw [← sum_inertiaDeg_eq_finrank K L v, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw ↦ ?_
  have : w.LiesOver v := by simpa using hw
  rw [inertiaDeg_eq_finrank, mult_mul_finrank]

/-- Grouping the infinite places of `L` by their restriction to `K`: a product over the infinite
places `w` of `L` of `g (w|_K) ^ m_w` is the product over the infinite places `v` of `K` of
`g v ^ (m_v [L : K])`. -/
theorem prod_comap_pow_mult {M : Type*} [CommMonoid M] (g : InfinitePlace K → M) :
    ∏ w : InfinitePlace L, g (w.comap (algebraMap K L)) ^ w.mult =
      ∏ v : InfinitePlace K, g v ^ (v.mult * finrank K L) := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ fun w : InfinitePlace L ↦ w.comap (algebraMap K L)]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [← sum_mult_eq_mult_mul_finrank L v, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr ?_ fun w hw ↦ ?_
  · ext w
    simp [liesOver_iff_comap_eq]
  · have : w.LiesOver v := by simpa using hw
    rw [LiesOver.comap_eq w v]

end NumberField.InfinitePlace
