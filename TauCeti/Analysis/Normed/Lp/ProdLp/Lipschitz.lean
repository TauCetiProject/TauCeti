/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp

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

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {α β α' β' : Type*} [PseudoEMetricSpace α]
  [PseudoEMetricSpace β] [PseudoEMetricSpace α'] [PseudoEMetricSpace β']

/-- The componentwise map `(x, y) ↦ (f x, g y)` of a `K₁`-Lipschitz map `f` and a `K₂`-Lipschitz
map `g` is `max K₁ K₂`-Lipschitz on the `ℓ^p` products. -/
theorem LipschitzWith.withLpProdMap {K₁ K₂ : ℝ≥0} {f : α → α'} {g : β → β'}
    (hf : LipschitzWith K₁ f) (hg : LipschitzWith K₂ g) :
    LipschitzWith (max K₁ K₂) (WithLp.map p (Prod.map f g)) := by
  intro x y
  have hf' := hf.weaken (le_max_left K₁ K₂) x.fst y.fst
  have hg' := hg.weaken (le_max_right K₁ K₂) x.snd y.snd
  set K : ℝ≥0∞ := ((max K₁ K₂ : ℝ≥0) : ℝ≥0∞)
  rcases p.trichotomy with rfl | rfl | hp
  · exact absurd (Fact.out : (1 : ℝ≥0∞) ≤ 0) (by simp)
  · simp only [WithLp.prod_edist_eq_sup, mul_max]
    exact sup_le_sup (by simpa using hf') (by simpa using hg')
  · calc edist (WithLp.map p (Prod.map f g) x) (WithLp.map p (Prod.map f g) y)
        _ = (edist (f x.fst) (f y.fst) ^ p.toReal + edist (g x.snd) (g y.snd) ^ p.toReal) ^
            (1 / p.toReal) := by
          simp [WithLp.prod_edist_eq_add hp]
        _ ≤ ((K * edist x.fst y.fst) ^ p.toReal + (K * edist x.snd y.snd) ^ p.toReal) ^
            (1 / p.toReal) := by gcongr
        _ = K * edist x y := by
          simp [WithLp.prod_edist_eq_add hp, ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← mul_add,
            ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hp.le), ENNReal.rpow_rpow_inv hp.ne']
