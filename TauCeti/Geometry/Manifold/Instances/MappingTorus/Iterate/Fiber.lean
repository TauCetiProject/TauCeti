/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Iterate.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Card

/-!
# Fibers of the integer-iterate map

For a nonzero integer `k`, the natural map `Y_(φ^k) → Y_φ`, `[s, z] ↦ [k * s, z]`,
has exactly `k.natAbs` points in each fiber. Over `[t, x]` they are
`[(t + j) / k, φ^(-j) x]`, with `0 ≤ j < |k|`. Two integer indices give the same
point exactly when they are congruent modulo `k`.

This counts the sheets in the comparison between suspensions of a diffeomorphism and its
integer iterates, including negative iterates. It requires no compactness or separation
assumptions on the fiber manifold and is independent of the orbit of `x` under `φ`.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*,
  Algebraic & Geometric Topology 5 (2005), Section 2, for the mapping-torus description
  of periodic trajectories.
-/

public section

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} (φ : M ≃ₘ^n⟮I, I⟯ M) {k : ℤ}

/-- Two integer representatives of a fiber of the iterate map agree exactly when their
indices are congruent modulo the iterate. -/
theorem mk_iterateMap_fiber_eq_iff (hk : k ≠ 0) (t : ℝ) (x : M) (a b : ℤ) :
    mk (φ ^ k) ((t + a) / k) ((φ ^ (-a)) x) =
        mk (φ ^ k) ((t + b) / k) ((φ ^ (-b)) x) ↔ a ≡ b [ZMOD k] := by
  have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  rw [mk_eq_mk_iff]
  constructor
  · rintro ⟨j, hj, _⟩
    apply Int.modEq_iff_dvd.2
    refine ⟨-j, ?_⟩
    have hj' : (a : ℝ) - b = k * j := by
      field_simp at hj
      nlinarith
    exact_mod_cast (by linarith : (b : ℝ) - a = k * (-j))
  · intro hab
    obtain ⟨j, hj⟩ := hab.symm.dvd
    refine ⟨j, ?_, ?_⟩
    · have hj' : (a : ℝ) - b = k * j := by exact_mod_cast hj
      apply (div_eq_iff hk').2
      field_simp
      nlinarith
    · rw [← Diffeomorph.mul_apply, ← zpow_mul, ← zpow_add]
      congr 2
      linear_combination -hj

/-- The fiber over `[t, x]` has the representatives indexed by `Fin |k|`, with no repetitions. -/
theorem preimage_iterateMap_mk_eq_range_fin (hk : k ≠ 0) (t : ℝ) (x : M) :
    iterateMap φ k ⁻¹' {mk φ t x} =
      range (fun j : Fin k.natAbs ↦
        mk (φ ^ k) ((t + (j : ℕ)) / k) ((φ ^ (-(j : ℤ))) x)) := by
  rw [preimage_iterateMap_mk φ k hk]
  apply Subset.antisymm
  · rintro _ ⟨j, rfl⟩
    have hj0 := Int.emod_nonneg j hk
    have hjlt := Int.emod_lt j hk
    let r : Fin k.natAbs := ⟨(j % k).toNat, by omega⟩
    refine ⟨r, (mk_iterateMap_fiber_eq_iff φ hk t x _ j).2 ?_⟩
    have hr : (r : ℤ) = j % k := by
      simp only [r, Int.toNat_of_nonneg hj0]
    rw [hr]
    exact Int.mod_modEq j k
  · rintro _ ⟨j, rfl⟩
    exact ⟨(j : ℕ), by simp⟩

/-- Distinct indices below `|k|` give distinct points in a fiber of the iterate map. -/
theorem injective_mk_iterateMap_fiber (hk : k ≠ 0) (t : ℝ) (x : M) :
    Injective (fun j : Fin k.natAbs ↦
      mk (φ ^ k) ((t + (j : ℕ)) / k) ((φ ^ (-(j : ℤ))) x)) := by
  intro a b hab
  have hm := (Int.modEq_natAbs).2 ((mk_iterateMap_fiber_eq_iff φ hk t x _ _).1 hab)
  have ha : (a : ℤ) % (k.natAbs : ℤ) = a :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast a.isLt)
  have hb : (b : ℤ) % (k.natAbs : ℤ) = b :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast b.isLt)
  have heq : (a : ℤ) = b := by simpa only [Int.ModEq, ha, hb] using hm
  exact Fin.ext (by exact_mod_cast heq)

/-- Every fiber of a nonzero integer-iterate map is finite. -/
@[simp]
theorem finite_preimage_iterateMap (hk : k ≠ 0) (y : SmoothMappingTorus φ) :
    (iterateMap φ k ⁻¹' {y}).Finite := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ y
  rw [uncurry_apply_pair, preimage_iterateMap_mk_eq_range_fin φ hk]
  exact finite_range _

/-- Every fiber of the integer-iterate map has exactly the absolute value of the iterate
many points, even for a negative iterate and a noncompact fiber manifold. -/
@[simp]
theorem ncard_preimage_iterateMap (hk : k ≠ 0) (y : SmoothMappingTorus φ) :
    (iterateMap φ k ⁻¹' {y}).ncard = k.natAbs := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ y
  rw [uncurry_apply_pair, preimage_iterateMap_mk_eq_range_fin φ hk,
    ncard_range_of_injective (injective_mk_iterateMap_fiber φ hk t x)]
  simp

end TauCeti.SmoothMappingTorus
