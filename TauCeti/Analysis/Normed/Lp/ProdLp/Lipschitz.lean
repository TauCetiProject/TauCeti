/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
import TauCeti.Analysis.Normed.Lp.ProdLp

/-!
# Componentwise Lipschitz maps of `ℓ^p` products

For `1 ≤ p ≤ ∞`, the componentwise map `(x, y) ↦ (f x, g y)` of a `K₁`-Lipschitz map `f` and a
`K₂`-Lipschitz map `g` is `max K₁ K₂`-Lipschitz on the `ℓ^p` products `WithLp p (α × β)`
(`LipschitzWith.withLpProdMap`). This is the Lipschitz counterpart of Mathlib's
`Isometry.withLpProdMap`. A typical instance is a map of `WithLp 2 (ℝ × E)` that keeps the first
coordinate and moves the second by a Lipschitz map of `E`, with constant `max 1 K`.
-/

public section

open scoped ENNReal NNReal

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {α β α' β' : Type*} [SeminormedAddCommGroup α]
  [SeminormedAddCommGroup β] [SeminormedAddCommGroup α'] [SeminormedAddCommGroup β']

/-- The componentwise map `(x, y) ↦ (f x, g y)` of a `K₁`-Lipschitz map `f` and a `K₂`-Lipschitz
map `g` is `max K₁ K₂`-Lipschitz on the `ℓ^p` products. -/
theorem LipschitzWith.withLpProdMap {K₁ K₂ : ℝ≥0} {f : α → α'} {g : β → β'}
    (hf : LipschitzWith K₁ f) (hg : LipschitzWith K₂ g) :
    LipschitzWith (max K₁ K₂) (WithLp.map p (Prod.map f g)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, ← one_mul ‖WithLp.map p (Prod.map f g) x - _‖]
  refine WithLp.prod_mul_norm_le_mul_norm ?_ ?_
  · simpa [← dist_eq_norm] using (hf.dist_le_mul x.fst y.fst).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left K₁ K₂) dist_nonneg)
  · simpa [← dist_eq_norm] using (hg.dist_le_mul x.snd y.snd).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right K₁ K₂) dist_nonneg)
