/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integrability of products of smooth functions

The product of two smooth real functions on a real normed space, one of which has compact
support, is integrable with respect to every measure that is finite on compact sets. The same
holds after applying to either factor a linear operator on `C^∞(E)` that does not enlarge
supports, such as a differential operator.

## Main results

* `ContMDiffMap.integrable_mul_of_hasCompactSupport`: the product of two smooth functions, one of
  which has compact support, is integrable.
* `ContMDiffMap.integrable_apply_mul_of_tsupport_subset`,
  `ContMDiffMap.integrable_mul_apply_of_tsupport_subset`: the same after applying an operator that
  does not enlarge supports to the first or second factor.
-/

public section

open MeasureTheory
open scoped ContDiff Manifold

namespace ContMDiffMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- The product of two smooth functions, one of which has compact support, is integrable. -/
theorem integrable_mul_of_hasCompactSupport {f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (hfg : HasCompactSupport f ∨ HasCompactSupport g) : Integrable (fun x ↦ f x * g x) μ :=
  (f.contMDiff.continuous.mul g.contMDiff.continuous).integrable_of_hasCompactSupport
    (hfg.elim (·.mul_right) (·.mul_left))

variable {D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}

/-- If `D` does not enlarge supports, then `(D f) g` is integrable whenever `f` or `g` has compact
support. -/
theorem integrable_apply_mul_of_tsupport_subset (hD : ∀ f, tsupport (D f) ⊆ tsupport f)
    {f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯} (hfg : HasCompactSupport f ∨ HasCompactSupport g) :
    Integrable (fun x ↦ D f x * g x) μ :=
  integrable_mul_of_hasCompactSupport
    (hfg.imp (·.of_isClosed_subset (isClosed_tsupport _) (hD f)) _root_.id)

/-- If `D` does not enlarge supports, then `f (D g)` is integrable whenever `f` or `g` has compact
support. -/
theorem integrable_mul_apply_of_tsupport_subset (hD : ∀ f, tsupport (D f) ⊆ tsupport f)
    {f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯} (hfg : HasCompactSupport f ∨ HasCompactSupport g) :
    Integrable (fun x ↦ f x * D g x) μ :=
  integrable_mul_of_hasCompactSupport
    (hfg.imp _root_.id (·.of_isClosed_subset (isClosed_tsupport _) (hD g)))

end ContMDiffMap
