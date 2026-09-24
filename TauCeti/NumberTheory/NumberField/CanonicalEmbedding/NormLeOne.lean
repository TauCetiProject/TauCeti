/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne

/-!
# Reflecting real coordinates preserves the fundamental cone

Membership in Mathlib's `NumberField.mixedEmbedding.fundamentalCone K` depends on a point only
through its norms at the infinite places, and so does its mixed norm. Reflecting the real
coordinates at a set of real places with `negAt` changes none of these norms, so it preserves the
fundamental cone and every unit translate of the norm-≤-one region `normLeOne K`.

## Main results

* `TauCeti.NumberField.mixedEmbedding.negAt_mem_fundamentalCone_iff`: `negAt s x` lies in the
  fundamental cone exactly when `x` does.
* `TauCeti.NumberField.mixedEmbedding.negAt_mem_unit_smul_normLeOne_iff`: the same for the
  translate `u • normLeOne K` by a unit `u`.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Pointwise

namespace TauCeti.NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

/-- Reflecting real coordinates preserves Mathlib's fundamental cone. -/
@[simp]
theorem negAt_mem_fundamentalCone_iff (s : Set {w : InfinitePlace K // w.IsReal})
    (x : mixedSpace K) : negAt s x ∈ fundamentalCone K ↔ x ∈ fundamentalCone K :=
  ⟨fun h ↦ fundamentalCone.mem_of_normAtPlace_eq h fun w ↦ by simp [normAtPlace_negAt],
    fun h ↦ fundamentalCone.mem_of_normAtPlace_eq h fun w ↦ by simp [normAtPlace_negAt]⟩

/-- Reflecting real coordinates preserves each unit translate of `normLeOne K`, since it commutes
with the unit action. -/
@[simp]
theorem negAt_mem_unit_smul_normLeOne_iff (s : Set {w : InfinitePlace K // w.IsReal})
    (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    negAt s x ∈ u • fundamentalCone.normLeOne K ↔ x ∈ u • fundamentalCone.normLeOne K := by
  simp only [Set.mem_smul_set_iff_inv_smul_mem, unitSMul_smul, fundamentalCone.mem_normLeOne,
    map_mul, norm_negAt]
  refine and_congr_left fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;>
    exact fundamentalCone.mem_of_normAtPlace_eq h fun w ↦ by simp [map_mul, normAtPlace_negAt]

end TauCeti.NumberField.mixedEmbedding
