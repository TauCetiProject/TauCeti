/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Projectivization.LineBundle
public import TauCeti.Topology.VectorBundle.Orientation.Atlas

/-!
# Orientability of the line bundles `𝒪(k)` on real projective space

The real line bundle `𝒪(k)` on `ℝℙⁿ = ℙ ℝ (Fin (n + 1) → ℝ)` (`Projectivization.twistCore k`) is
glued from the trivial lines over the standard affine opens `U_i = {[v] | v i ≠ 0}` along the
transition functions `[v] ↦ (v i / v j) ^ k`. This file shows that for `n ≥ 1` it is orientable
exactly when `k` is even (`Projectivization.nonempty_vectorBundleOrientation_twistCore_iff`).

For even `k` the transition functions are positive on the overlaps, so the standard charts form a
positive atlas, which orients the bundle (`VectorBundleCore.orientationOfPositiveAtlas`). For odd
`k` and `n ≥ 1`, consider the points `[1 : c : 0 : ⋯ : 0]` for `c = ±1`, which lie in both `U_0`
and `U_1`. The open sets `U_0` and `U_1` are copies of `ℝⁿ`, hence connected
(`Projectivization.isPreconnected_affineOpen`), so an orientation reads as a single orientation of
`ℝ` in each of the two charts. At `[1 : c : 0 : ⋯ : 0]` the two readings differ by the sign of
the transition `(1 / c) ^ k`, which is `1` for `c = 1` and `-1` for `c = -1`, a contradiction
(`TauCeti.VectorBundleOrientation.isEmpty_of_det_coordChangeL_pos_of_neg`). For `n = 0` the space
`ℝℙ⁰` is a point and every `𝒪(k)` is orientable.

For `n = 1`, `ℝℙ¹` is a circle and `𝒪(1)` and the tautological bundle `𝒪(-1)` are the Möbius line
bundle, the simplest bundle that is not orientable. This is the case in which the integral Thom
comparison for a Morse–Bott critical circle of index one with this negative normal bundle needs the
orientation local system of the bundle: the zeroth homology of the circle with coefficients in that
local system is `ℤ/2` rather than `ℤ`.

## Main results

* `Projectivization.nonempty_vectorBundleOrientation_twistCore_iff`: `𝒪(k)` on `ℝℙⁿ` is orientable
  if and only if `n = 0` or `k` is even.
* `Projectivization.isEmpty_vectorBundleOrientation_twistCore`: for `n ≠ 0` and odd `k`, in
  particular for the Möbius line bundles `𝒪(±1)` on `ℝℙ¹`, `𝒪(k)` is not orientable.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §2 (the canonical line bundle on `ℝℙⁿ`) and §9 (orientations).
-/

public section

noncomputable section

open Bundle Module Set
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- **`𝒪(k)` is not orientable for odd `k`.** For `n ≠ 0` and odd `k`, the line bundle `𝒪(k)` on
`ℝℙⁿ` has no orientation. For `n = 1` and `k = ±1` this is the Möbius line bundle on the circle
`ℝℙ¹`. -/
theorem isEmpty_vectorBundleOrientation_twistCore (hι : Fintype.card ι = 1) (hn : n ≠ 0)
    {k : ℤ} (hk : Odd k) :
    IsEmpty (TauCeti.VectorBundleOrientation ℝ (twistCore (𝕜 := ℝ) (n := n) k).Fiber ι) := by
  have hι' : Fintype.card ι = finrank ℝ ℝ := by rw [hι, finrank_self]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  -- The points `[1 : c : 0 : ⋯ : 0]`, for `c ≠ 0`, lie in the charts `0` and `1`.
  have h01 : (0 : Fin (m + 2)) ≠ 1 := Fin.zero_ne_one
  let v (c : ℝ) : Fin (m + 2) → ℝ := Pi.single 0 1 + Pi.single 1 c
  have hv0 (c : ℝ) : v c 0 = 1 := by simp [v, h01]
  have hv1 (c : ℝ) : v c 1 = c := by simp [v, h01.symm]
  have hv (c : ℝ) : v c ≠ 0 := fun h ↦ by simpa [hv0] using congrFun h 0
  let p (c : ℝ) : ℙ ℝ (Fin (m + 2) → ℝ) := mk ℝ (v c) (hv c)
  have hp0 (c : ℝ) : p c ∈ affineOpen 0 := by simp [p, hv0]
  have hp1 {c : ℝ} (hc : c ≠ 0) : p c ∈ affineOpen 1 := by simp [p, hv1, hc]
  have htr (c : ℝ) : twistTransition k 0 1 (p c) = (1 / c) ^ k := by
    simp only [p, twistTransition_mk, hv0, hv1]
  have : MemTrivializationAtlas ((twistCore (𝕜 := ℝ) (n := m + 1) k).localTriv 0) := ⟨⟨0, rfl⟩⟩
  have : MemTrivializationAtlas ((twistCore (𝕜 := ℝ) (n := m + 1) k).localTriv 1) := ⟨⟨1, rfl⟩⟩
  -- The transition from the chart `0` to the chart `1` is `1` at `[1 : 1 : 0 : ⋯ : 0]` and `-1` at
  -- `[1 : -1 : 0 : ⋯ : 0]`.
  refine TauCeti.VectorBundleOrientation.isEmpty_of_det_coordChangeL_pos_of_neg hι'
    ((twistCore k).localTriv 0) ((twistCore k).localTriv 1) (isPreconnected_affineOpen 0)
    (isPreconnected_affineOpen 1) (twistCore_localTriv_baseSet k 0).ge
    (twistCore_localTriv_baseSet k 1).ge (hp0 1) (hp1 one_ne_zero) (hp0 (-1))
    (hp1 (neg_ne_zero.2 one_ne_zero)) ?_ ?_
  · rw [det_coordChangeL_localTriv_twistCore k (hp0 1) (hp1 one_ne_zero)]
    simp [htr]
  · rw [det_coordChangeL_localTriv_twistCore k (hp0 (-1)) (hp1 (neg_ne_zero.2 one_ne_zero))]
    simp [htr, hk.neg_one_zpow]

/-- **Orientability of `𝒪(k)` on `ℝℙⁿ`.** The line bundle `𝒪(k)` on `ℝℙⁿ` is orientable if and
only if `n = 0` or `k` is even. For even `k` its transition functions are positive, and for
`n = 0` the base is a point. -/
theorem nonempty_vectorBundleOrientation_twistCore_iff (hι : Fintype.card ι = 1) (k : ℤ) :
    Nonempty (TauCeti.VectorBundleOrientation ℝ (twistCore (𝕜 := ℝ) (n := n) k).Fiber ι) ↔
      n = 0 ∨ Even k := by
  classical
  have hι' : Fintype.card ι = finrank ℝ ℝ := by rw [hι, finrank_self]
  refine ⟨fun ⟨o⟩ ↦ ?_, fun h ↦ ?_⟩
  · by_contra! h
    exact (isEmpty_vectorBundleOrientation_twistCore hι h.1 h.2).elim o
  · -- The standard charts form a positive atlas.
    let b : Basis ι ℝ ℝ :=
      (Module.finBasisOfFinrankEq ℝ ℝ hι'.symm).reindex (Fintype.equivFin ι).symm
    refine ⟨(twistCore (𝕜 := ℝ) (n := n) k).orientationOfPositiveAtlas b.orientation hι'
      (S := univ) (fun x ↦ ⟨_, mem_univ _, (twistCore k).mem_baseSet_at x⟩)
      fun i _ j _ x ⟨hi, hj⟩ ↦ ?_⟩
    rw [twistCore_baseSet] at hi hj
    rw [det_coordChange_twistCore]
    rcases h with rfl | hk
    · obtain rfl : i = j := Fin.ext (by lia)
      rw [twistTransition_self k hj]
      exact one_pos
    · rw [twistTransition_def]
      exact hk.zpow_pos
        (div_ne_zero ((mem_affineOpen_iff i x).1 hi) ((mem_affineOpen_iff j x).1 hj))

end Projectivization
