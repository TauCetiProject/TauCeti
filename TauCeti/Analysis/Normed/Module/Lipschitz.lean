/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Lipschitz bounds for pointwise products

A pointwise product of two bounded Lipschitz maps is Lipschitz, with constant given by the
product rule `‖f x g x - f y g y‖ ≤ ‖f x - f y‖ ‖g x‖ + ‖f y‖ ‖g x - g y‖`. This file records two
instances of this rule.

* A field of continuous linear maps applied to a field of vectors
  (`LipschitzWith.clm_apply`). For example, a Lipschitz field of bilinear forms evaluated on the
  gradient of a smooth compactly supported function is Lipschitz.
* A scalar cutoff `χ` times a function `h` that is Lipschitz and bounded only on a set `s` off which
  `χ` vanishes (`LipschitzWith.smul_of_lipschitzOnWith`). The product is Lipschitz on the whole
  space, whatever the values of `h` off `s`. This is how a coefficient field given on a domain is
  localized to a globally Lipschitz field.
-/

public section

open scoped NNReal

variable {𝕜 X F G : Type*} [PseudoMetricSpace X]

/-- **A bounded Lipschitz field of linear maps, applied to a bounded Lipschitz field of vectors,
is Lipschitz.** If `A` is `K_A`-Lipschitz with `‖A x‖ ≤ R_A` and `y` is `K_y`-Lipschitz with
`‖y x‖ ≤ R_y`, then `x ↦ A x (y x)` is `(K_A R_y + R_A K_y)`-Lipschitz. -/
theorem LipschitzWith.clm_apply [NontriviallyNormedField 𝕜] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] {A : X → F →L[𝕜] G} {y : X → F}
    {KA Ky RA Ry : ℝ≥0} (hA : LipschitzWith KA A) (hy : LipschitzWith Ky y) (hAR : ∀ x, ‖A x‖ ≤ RA)
    (hyR : ∀ x, ‖y x‖ ≤ Ry) :
    LipschitzWith (KA * Ry + RA * Ky) fun x => A x (y x) := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  rw [dist_eq_norm]
  have hAd : ‖A x - A x'‖ ≤ KA * dist x x' := by
    simpa [dist_eq_norm] using hA.dist_le_mul x x'
  have hyd : ‖y x - y x'‖ ≤ Ky * dist x x' := by
    simpa [dist_eq_norm] using hy.dist_le_mul x x'
  calc ‖A x (y x) - A x' (y x')‖ = ‖(A x - A x') (y x) + A x' (y x - y x')‖ := by
        rw [_root_.sub_apply, map_sub]
        abel_nf
    _ ≤ ‖A x - A x'‖ * ‖y x‖ + ‖A x'‖ * ‖y x - y x'‖ :=
        (norm_add_le _ _).trans (add_le_add ((A x - A x').le_opNorm _) ((A x').le_opNorm _))
    _ ≤ (KA * dist x x') * Ry + RA * (Ky * dist x x') := by
        gcongr
        · exact hyR x
        · exact hAR x'
    _ = ↑(KA * Ry + RA * Ky) * dist x x' := by push_cast; ring

/-- **A cutoff times a function Lipschitz on its support region is Lipschitz.** Let `χ` be
`L`-Lipschitz with `‖χ x‖ ≤ C` and `χ = 0` off `s`, and let `h` be `K`-Lipschitz on `s` with
`‖h x‖ ≤ R` for `x ∈ s`. Then `x ↦ χ x • h x` is `(C K + L R)`-Lipschitz on the whole space, for
any values of `h` off `s`. -/
theorem LipschitzWith.smul_of_lipschitzOnWith [NormedField 𝕜] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 F] {s : Set X} {χ : X → 𝕜} {h : X → F} {K L C R : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχC : ∀ x, ‖χ x‖ ≤ C) (hχs : ∀ x ∉ s, χ x = 0) (hh : LipschitzOnWith K h s)
    (hR : ∀ x ∈ s, ‖h x‖ ≤ R) :
    LipschitzWith (C * K + L * R) fun x => χ x • h x := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hχd : ‖χ x - χ y‖ ≤ L * dist x y := by
    simpa [dist_eq_norm] using hχ.dist_le_mul x y
  have hd : 0 ≤ (C : ℝ) * K * dist x y := by positivity
  rw [dist_eq_norm]
  push_cast
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
  · -- Both points lie in `s`.
    have hhd : ‖h x - h y‖ ≤ K * dist x y := by
      simpa [dist_eq_norm] using hh.dist_le_mul x hx y hy
    calc ‖χ x • h x - χ y • h y‖ = ‖χ x • (h x - h y) + (χ x - χ y) • h y‖ := by
          congr 1
          simp only [smul_sub, sub_smul]
          abel
      _ ≤ ‖χ x‖ * ‖h x - h y‖ + ‖χ x - χ y‖ * ‖h y‖ :=
          (norm_add_le _ _).trans (by rw [norm_smul, norm_smul])
      _ ≤ C * (K * dist x y) + (L * dist x y) * R := by
          gcongr
          · exact hχC x
          · exact hR y hy
      _ = (C * K + L * R) * dist x y := by ring
  · -- Only `x` lies in `s`, so `χ y = 0`.
    calc ‖χ x • h x - χ y • h y‖ = ‖χ x - χ y‖ * ‖h x‖ := by
          rw [hχs y hy, zero_smul, sub_zero, sub_zero, norm_smul]
      _ ≤ (L * dist x y) * R := by gcongr; exact hR x hx
      _ ≤ (C * K + L * R) * dist x y := by nlinarith
  · -- Only `y` lies in `s`, so `χ x = 0`.
    calc ‖χ x • h x - χ y • h y‖ = ‖χ x - χ y‖ * ‖h y‖ := by
          rw [hχs x hx, zero_smul, zero_sub, zero_sub, norm_neg, norm_neg, norm_smul]
      _ ≤ (L * dist x y) * R := by gcongr; exact hR y hy
      _ ≤ (C * K + L * R) * dist x y := by nlinarith
  · rw [hχs x hx, hχs y hy, zero_smul, zero_smul, sub_zero, norm_zero]
    positivity
