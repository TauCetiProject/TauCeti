/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
import TauCeti.Data.EReal.Operations

/-!
# Topological entropy of iterates

For `k ≥ 1`, the topological entropy of `T^[k]` is `k` times that of `T`:
`coverEntropy (T^[k]) F = k * coverEntropy T F` for a uniformly continuous `T` (in particular a
continuous map of a compact space). The inequality `≤` holds for every map.

The key identity is `dynEntourage (T^[k]) (dynEntourage T U k) n = dynEntourage T U (k * n)`: being
close for `n` steps of `T^[k]`, at the scale of `k` steps of `T`, is being close for `k * n` steps
of `T`.

## Main results

* `TauCeti.dynEntourage_iterate` — the identity above.
* `TauCeti.coverEntropyEntourage_iterate`, `TauCeti.coverEntropyInfEntourage_iterate` — the
  entourage-level identities.
* `TauCeti.coverEntropy_iterate_le`, `TauCeti.coverEntropyInf_iterate_le` — the entropy of `T^[k]`
  is at most `k` times that of `T`.
* `TauCeti.coverEntropy_iterate`, `TauCeti.coverEntropyInf_iterate` — equality for uniformly
  continuous `T`, and `TauCeti.coverEntropy_iterate_of_compactSpace`,
  `TauCeti.coverEntropyInf_iterate_of_compactSpace` for continuous `T` on a compact space.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, Problem 4.13, p. 131.
* P. Walters, *An Introduction to Ergodic Theory*, Graduate Texts in Mathematics 79, Springer,
  1982, Theorem 7.10.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth
open scoped Uniformity

variable {X : Type*} {T : X → X} {k : ℕ}

/-- Being `dynEntourage T U k`-close for `n` steps of `T^[k]` is being `U`-close for `k * n` steps
of `T`. -/
@[simp]
theorem dynEntourage_iterate (T : X → X) (U : SetRel X X) (k n : ℕ) :
    dynEntourage (T^[k]) (dynEntourage T U k) n = dynEntourage T U (k * n) := by
  ext ⟨x, y⟩
  simp only [mem_dynEntourage, ← Function.iterate_mul, ← Function.iterate_add_apply]
  refine ⟨fun h m hm ↦ ?_, fun h j hj i hi ↦ h _ ?_⟩
  · have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    have := h (m / k) (Nat.div_lt_of_lt_mul hm) (m % k) (Nat.mod_lt _ hk)
    rwa [Nat.mod_add_div] at this
  · calc i + k * j < k + k * j := by omega
      _ = k * (j + 1) := by ring
      _ ≤ k * n := Nat.mul_le_mul_left k hj

/-- The minimal cardinality of a dynamical cover of `F` for `T^[k]` at the entourage
`dynEntourage T U k` and time `n` equals that for `T` at `U` and time `k * n`. -/
@[simp]
theorem coverMincard_iterate (T : X → X) (F : Set X) (U : SetRel X X) (k n : ℕ) :
    coverMincard (T^[k]) F (dynEntourage T U k) n = coverMincard T F U (k * n) := by
  simp only [coverMincard, IsDynCoverOf, dynEntourage_iterate]

/-- The cover entropy of `T^[k]` at the entourage `dynEntourage T U k` is `k` times the cover
entropy of `T` at `U`. -/
theorem coverEntropyEntourage_iterate (hk : k ≠ 0) (T : X → X) (F : Set X) (U : SetRel X X) :
    coverEntropyEntourage (T^[k]) F (dynEntourage T U k) = k * coverEntropyEntourage T F U := by
  simp only [coverEntropyEntourage, coverMincard_iterate]
  exact Monotone.expGrowthSup_comp_mul
    (fun _ _ h ↦ ENat.toENNReal_mono (coverMincard_monotone_time T F U h)) hk

/-- The `liminf` cover entropy of `T^[k]` at the entourage `dynEntourage T U k` is `k` times the
`liminf` cover entropy of `T` at `U`. -/
theorem coverEntropyInfEntourage_iterate (hk : k ≠ 0) (T : X → X) (F : Set X)
    (U : SetRel X X) :
    coverEntropyInfEntourage (T^[k]) F (dynEntourage T U k) =
      k * coverEntropyInfEntourage T F U := by
  simp only [coverEntropyInfEntourage, coverMincard_iterate]
  exact Monotone.expGrowthInf_comp_mul
    (fun _ _ h ↦ ENat.toENNReal_mono (coverMincard_monotone_time T F U h)) hk

variable [UniformSpace X]

/-- The topological entropy of `T^[k]` is at most `k` times that of `T`. -/
theorem coverEntropy_iterate_le (hk : k ≠ 0) (T : X → X) (F : Set X) :
    coverEntropy (T^[k]) F ≤ k * coverEntropy T F := by
  refine iSup₂_le fun U hU ↦ ?_
  calc coverEntropyEntourage (T^[k]) F U
      ≤ coverEntropyEntourage (T^[k]) F (dynEntourage T U k) :=
        coverEntropyEntourage_antitone _ F
          ((dynEntourage_antitone T U (Nat.one_le_iff_ne_zero.2 hk)).trans_eq dynEntourage_one)
    _ = k * coverEntropyEntourage T F U := coverEntropyEntourage_iterate hk T F U
    _ ≤ k * coverEntropy T F :=
        mul_le_mul_of_nonneg_left (coverEntropyEntourage_le_coverEntropy T F hU)
          (Nat.cast_nonneg' k)

/-- The `liminf` topological entropy of `T^[k]` is at most `k` times that of `T`. -/
theorem coverEntropyInf_iterate_le (hk : k ≠ 0) (T : X → X) (F : Set X) :
    coverEntropyInf (T^[k]) F ≤ k * coverEntropyInf T F := by
  refine iSup₂_le fun U hU ↦ ?_
  calc coverEntropyInfEntourage (T^[k]) F U
      ≤ coverEntropyInfEntourage (T^[k]) F (dynEntourage T U k) :=
        coverEntropyInfEntourage_antitone _ F
          ((dynEntourage_antitone T U (Nat.one_le_iff_ne_zero.2 hk)).trans_eq dynEntourage_one)
    _ = k * coverEntropyInfEntourage T F U := coverEntropyInfEntourage_iterate hk T F U
    _ ≤ k * coverEntropyInf T F :=
        mul_le_mul_of_nonneg_left (coverEntropyInfEntourage_le_coverEntropyInf T F hU)
          (Nat.cast_nonneg' k)

/-- For a uniformly continuous `T` and `k ≥ 1`, the topological entropy of `T^[k]` is `k` times
that of `T`. -/
theorem coverEntropy_iterate (hT : UniformContinuous T) (hk : k ≠ 0) (F : Set X) :
    coverEntropy (T^[k]) F = k * coverEntropy T F := by
  have hk₀ : (0 : EReal) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  refine (coverEntropy_iterate_le hk T F).antisymm <|
    EReal.mul_iSup_le hk₀ (EReal.natCast_ne_top k) fun U ↦
      EReal.mul_iSup_le hk₀ (EReal.natCast_ne_top k) fun hU ↦ ?_
  rw [← coverEntropyEntourage_iterate hk T F U]
  exact coverEntropyEntourage_le_coverEntropy _ F (dynEntourage_mem_uniformity hT hU k)

/-- For a uniformly continuous `T` and `k ≥ 1`, the `liminf` topological entropy of `T^[k]` is `k`
times that of `T`. -/
theorem coverEntropyInf_iterate (hT : UniformContinuous T) (hk : k ≠ 0) (F : Set X) :
    coverEntropyInf (T^[k]) F = k * coverEntropyInf T F := by
  have hk₀ : (0 : EReal) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  refine (coverEntropyInf_iterate_le hk T F).antisymm <|
    EReal.mul_iSup_le hk₀ (EReal.natCast_ne_top k) fun U ↦
      EReal.mul_iSup_le hk₀ (EReal.natCast_ne_top k) fun hU ↦ ?_
  rw [← coverEntropyInfEntourage_iterate hk T F U]
  exact coverEntropyInfEntourage_le_coverEntropyInf _ F (dynEntourage_mem_uniformity hT hU k)

/-- For a continuous map `T` of a compact space and `k ≥ 1`, the topological entropy of `T^[k]` is
`k` times that of `T`. -/
theorem coverEntropy_iterate_of_compactSpace [CompactSpace X] (hT : Continuous T) (hk : k ≠ 0)
    (F : Set X) : coverEntropy (T^[k]) F = k * coverEntropy T F :=
  coverEntropy_iterate (CompactSpace.uniformContinuous_of_continuous hT) hk F

/-- For a continuous map `T` of a compact space and `k ≥ 1`, the `liminf` topological entropy of
`T^[k]` is `k` times that of `T`. -/
theorem coverEntropyInf_iterate_of_compactSpace [CompactSpace X] (hT : Continuous T)
    (hk : k ≠ 0) (F : Set X) : coverEntropyInf (T^[k]) F = k * coverEntropyInf T F :=
  coverEntropyInf_iterate (CompactSpace.uniformContinuous_of_continuous hT) hk F

end TauCeti
