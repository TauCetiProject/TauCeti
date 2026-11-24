/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.SmoothEmbedding

import Mathlib.Tactic.Ring

/-!
# Product coordinates from a translating flow

A smooth flow translating a smooth real function identifies the ambient manifold with the
product of the real line and the actual zero level. The zero level may carry any atlas for
which its inclusion is a smooth embedding; no finite-dimensionality assumption is required.

Source references: https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public section

open Function Set
open scoped ContDiff Manifold

noncomputable section

namespace Flow

variable {E F H K M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ}
  [ChartedSpace K {x : M // f x = 0}]

/-- Flowing out the zero level gives product coordinates. The inverse flows a point for minus
its scalar value, so its first coordinate is the original function. -/
def zeroLevelProductDiffeomorph (φ : Flow ℝ M)
    (hφ : ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M ↦ φ p.1 p.2))
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hι : Manifold.IsSmoothEmbedding J I ∞ (Subtype.val : {x : M // f x = 0} → M))
    (hscalar : ∀ t x, f (φ t x) = f x + t) :
    (ℝ × {x : M // f x = 0}) ≃ₘ⟮𝓘(ℝ).prod J, I⟯ M := by
  have hback := hφ.comp (hf.neg.prodMk contMDiff_id)
  refine
    { toFun := fun z ↦ φ z.1 z.2
      invFun := fun x ↦ (f x, ⟨φ (-f x) x, by rw [hscalar]; ring⟩)
      left_inv := ?_
      right_inv := ?_
      contMDiff_toFun := hφ.comp (contMDiff_fst.prodMk (hι.contMDiff.comp contMDiff_snd))
      contMDiff_invFun := hf.prodMk
        ((ContMDiff.iff_comp_isImmersion hι.isImmersion).2
          ⟨hback.continuous.subtype_mk (fun x ↦ by
            -- Membership unfolds the zero-level subtype of the backward-flow map.
            change f (φ (-f x) x) = 0
            rw [hscalar]
            ring), hback⟩) }
  · intro z
    apply Prod.ext
    · -- The first inverse coordinate is the scalar potential.
      change f (φ z.1 z.2) = z.1
      rw [hscalar, z.2.property, zero_add]
    · apply Subtype.ext
      -- The second inverse coordinate is the backward flow on the level subtype.
      change φ (-f (φ z.1 z.2)) (φ z.1 z.2) = z.2
      rw [hscalar, z.2.property, zero_add, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  · intro x
    -- The forward and backward flow maps cancel by the additive action law.
    change φ (f x) (φ (-f x) x) = x
    rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]

variable (φ : Flow ℝ M)
  (hφ : ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M ↦ φ p.1 p.2))
  (hf : ContMDiff I 𝓘(ℝ) ∞ f)
  (hι : Manifold.IsSmoothEmbedding J I ∞ (Subtype.val : {x : M // f x = 0} → M))
  (hscalar : ∀ t x, f (φ t x) = f x + t)

/-- The product coordinates are given by the original flow. -/
@[simp]
theorem coe_zeroLevelProductDiffeomorph :
    ⇑(φ.zeroLevelProductDiffeomorph hφ hf hι hscalar) =
      fun z : ℝ × {x : M // f x = 0} ↦ φ z.1 z.2 := (rfl)

/-- The time coordinate of the inverse is the scalar function. -/
@[simp]
theorem zeroLevelProductDiffeomorph_symm_apply_fst (x : M) :
    ((φ.zeroLevelProductDiffeomorph hφ hf hι hscalar).symm x).1 = f x := (rfl)

/-- The level coordinate of the inverse is obtained by flowing backwards by the scalar value. -/
@[simp]
theorem coe_zeroLevelProductDiffeomorph_symm_apply_snd (x : M) :
    (((φ.zeroLevelProductDiffeomorph hφ hf hι hscalar).symm x).2 : M) = φ (-f x) x := (rfl)

/-- The scalar function is the time coordinate in the product chart. -/
theorem apply_zeroLevelProductDiffeomorph (z : ℝ × {x : M // f x = 0}) :
    f (φ.zeroLevelProductDiffeomorph hφ hf hι hscalar z) = z.1 := by
  rw [coe_zeroLevelProductDiffeomorph, hscalar, z.2.property, zero_add]

/-- The scalar function composed with the product coordinates is the first projection. -/
theorem comp_zeroLevelProductDiffeomorph :
    f ∘ φ.zeroLevelProductDiffeomorph hφ hf hι hscalar = Prod.fst := by
  funext z
  exact apply_zeroLevelProductDiffeomorph φ hφ hf hι hscalar z

/-- At time zero, the product coordinates restrict to the level inclusion. -/
@[simp]
theorem zeroLevelProductDiffeomorph_apply_zero (z : {x : M // f x = 0}) :
    φ.zeroLevelProductDiffeomorph hφ hf hι hscalar (0, z) = z :=
  φ.map_zero_apply z

end Flow
