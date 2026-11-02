/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Ladder.Double
import Mathlib.Algebra.Field.ZMod

/-!
# Examples of the even Montgomery-ladder relation

The even step accepts scaled representatives and remains correct on singular models,
including in characteristic two. On `y² = x³ + x` over `𝔽₇`, three successive even steps
starting from `(3, 3)` reach infinity. The intermediate pairs represent `[2]P`, `[4]P`,
and `[8]P`; none is the zero raw pair.
-/

namespace TauCeti.Montgomery

open WeierstrassCurve

-- No normalization of the input representative is required.
example {K : Type*} [Field K] [DecidableEq K] {A B N D c : K}
    (hB : B ≠ 0) (hD : D ≠ 0) (h : 4 * N = (A + 2) * D) (hc : c ≠ 0)
    (P : (model A B).toAffine.Point) (k : ℕ) :
    double N D (c • coordinates A B (k • P)) ≠ 0 ∧
      (double N D (c • coordinates A B (k • P))).cross
        (coordinates A B ((2 * k) • P)) = 0 := by
  apply double_nsmul hB hD h P k
  · simp [hc, coordinates_ne_zero hB]
  · simp

-- The scaled relation is sufficient even in characteristic two, on the singular model A = 0.
example (P : (model (0 : ZMod 2) 1).toAffine.Point) (k : ℕ) :
    double 1 1 (coordinates 0 1 (k • P)) ≠ 0 ∧
      (double 1 1 (coordinates 0 1 (k • P))).cross
        (coordinates 0 1 ((2 * k) • P)) = 0 :=
  double_nsmul (by decide) (by decide) (by decide) P k (coordinates_ne_zero (by decide) _) (by simp)

-- Track actual raw outputs rather than assuming the group order or the intermediate multiples.
example [Fact (Nat.Prime 7)] :
    let P : (model (0 : ZMod 7) 1).toAffine.Point := .some 3 3 (by
      rw [Affine.nonsingular_iff, Affine.equation_iff]
      norm_num
      decide +revert)
    8 • P = 0 := by
  intro P
  have hd₁ : double (2 : ZMod 7) 4 ⟨3, 1⟩ = ⟨4, 4⟩ := by
    clear P
    ext <;> norm_num [double_x, double_z] <;> decide +revert
  have hd₂ : double (2 : ZMod 7) 4 ⟨4, 4⟩ = ⟨0, 2⟩ := by
    clear P hd₁
    ext <;> norm_num [double_x, double_z]
    decide +revert
  have hd₄ : double (2 : ZMod 7) 4 ⟨0, 2⟩ = ⟨1, 0⟩ := by
    clear P hd₁ hd₂
    ext <;> norm_num [double_x, double_z]
    decide +revert
  have h₁ : (Pair.mk (3 : ZMod 7) 1).cross (coordinates 0 1 (1 • P)) = 0 := by
    simp [P]
  have hD : (4 : ZMod 7) ≠ 0 := (ZMod.natCast_eq_zero_iff 4 7).not.mpr (by decide)
  have h₂ := double_nsmul (N := 2) (D := 4) (by simp) hD (by norm_num) P 1
    (S := ⟨3, 1⟩) (by simp [Pair.ne_zero_iff]) h₁
  rw [hd₁] at h₂
  have h₄ := double_nsmul (N := 2) (D := 4) (by simp) hD (by norm_num) P 2 h₂.1 h₂.2
  rw [hd₂] at h₄
  have h₈ := double_nsmul (N := 2) (D := 4) (by simp) hD (by norm_num) P 4 h₄.1 h₄.2
  rw [hd₄] at h₈
  apply (coordinates_z_eq_zero_iff (by simp)).mp
  simpa [Pair.cross_def] using h₈.2

end TauCeti.Montgomery
