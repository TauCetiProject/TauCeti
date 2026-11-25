/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Radical

import Mathlib.RingTheory.Nakayama
import TauCeti.RingTheory.Ideal.Extended

/-!
# Nakayama's lemma for an idempotent

Let `T` be a not necessarily commutative algebra over a commutative ring `S`, `J` an ideal of `S`
in the Jacobson radical, and `e` an idempotent of `T` whose summand `e T` is a finitely generated
`S`-module. If `e T ⊆ S e + JT`, then `e T = S e`: applying left multiplication by `e` to
`e T ⊆ S e + JT` gives `e T ⊆ S e + J • e T`, and Nakayama's lemma, in the form of Mathlib's
`Submodule.le_of_le_smul_of_le_jacobson`, concludes.

The extended ideal `JT` is read as `J • T` through `Ideal.mem_map_algebraMap_iff`, which does not
need `T` to be commutative.

## Main results

* `IsIdempotentElem.exists_smul_eq_mul_of_mul_sub_smul_mem`: in a not necessarily commutative
  `S`-algebra `T`, an idempotent `e` with `e T` finitely generated over `S` and
  `e T ⊆ S e + JT`, for `J` in the Jacobson radical of `S`, has `e T = S e`.
-/

public section

/-- **Nakayama's lemma for an idempotent.** Let `T` be a not necessarily commutative `S`-algebra,
`J` an ideal of `S` in the Jacobson radical, and `e` an idempotent of `T` such that `e T` is a
finitely generated `S`-module. If `e T ⊆ S e + JT`, then `e T = S e`. -/
theorem IsIdempotentElem.exists_smul_eq_mul_of_mul_sub_smul_mem {S T : Type*} [CommRing S]
    [Ring T] [Algebra S T] {J : Ideal S} (hJ : J ≤ Ring.jacobson S) {e : T}
    (he : IsIdempotentElem e) (hfg : (LinearMap.mulLeft S e).range.FG)
    (h : ∀ x : T, ∃ s : S, e * x - s • e ∈ J.map (algebraMap S T)) (x : T) :
    ∃ s : S, s • e = e * x := by
  let f := LinearMap.mulLeft S e
  have hle : LinearMap.range f ≤ S ∙ e := by
    refine Submodule.le_of_le_smul_of_le_jacobson hfg hJ fun z hz ↦ ?_
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hz
    obtain ⟨s, hs⟩ := h y
    have hmem : f (e * y - s • e) ∈ J • LinearMap.range f := by
      rw [LinearMap.range_eq_map, ← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem ((Ideal.mem_map_algebraMap_iff J).mp hs)
    have hy : f y = s • e + f (e * y - s • e) := by
      simp only [f, LinearMap.mulLeft_apply, mul_sub, ← mul_assoc, mul_smul_comm, he.eq]
      abel
    rw [hy]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ s (Submodule.mem_span_singleton_self e)) hmem
  simpa only [f, LinearMap.mulLeft_apply] using
    Submodule.mem_span_singleton.mp (hle (LinearMap.mem_range_self f x))
