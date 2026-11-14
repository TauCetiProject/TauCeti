/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integrability of products of `C^n` functions

The product of two `C^n` functions on a manifold with values in a normed ring, one of which has
compact support, is integrable with respect to every measure that is finite on compact sets. The
same holds after applying to either factor an operator that does not enlarge supports, such as a
differential operator.

## Main results

* `ContMDiffMap.integrable_mul_of_hasCompactSupport`: the product of two `C^n` functions, one of
  which has compact support, is integrable.
* `ContMDiffMap.integrable_apply_mul_of_tsupport_subset`,
  `ContMDiffMap.integrable_mul_apply_of_tsupport_subset`: the same after applying an operator that
  does not enlarge supports to the first or second factor.
-/

public section

open MeasureTheory
open scoped ContDiff Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
  [OpensMeasurableSpace M] {μ : Measure M} [IsFiniteMeasureOnCompacts μ] {n : ℕ∞ω}
  {A : Type*} [NormedRing A] [NormedSpace 𝕜 A]

/-- The product of two `C^n` functions, one of which has compact support, is integrable. -/
theorem integrable_mul_of_hasCompactSupport {f g : C^n⟮I, M; 𝓘(𝕜, A), A⟯}
    (hfg : HasCompactSupport f ∨ HasCompactSupport g) : Integrable (fun x ↦ f x * g x) μ :=
  (f.contMDiff.continuous.mul g.contMDiff.continuous).integrable_of_hasCompactSupport
    (hfg.elim (·.mul_right) (·.mul_left))

variable {D : C^n⟮I, M; 𝓘(𝕜, A), A⟯ → C^n⟮I, M; 𝓘(𝕜, A), A⟯}

/-- If `D` does not enlarge supports, then `(D f) g` is integrable whenever `f` or `g` has compact
support. -/
theorem integrable_apply_mul_of_tsupport_subset (hD : ∀ f, tsupport (D f) ⊆ tsupport f)
    {f g : C^n⟮I, M; 𝓘(𝕜, A), A⟯} (hfg : HasCompactSupport f ∨ HasCompactSupport g) :
    Integrable (fun x ↦ D f x * g x) μ :=
  integrable_mul_of_hasCompactSupport
    (hfg.imp (·.mono' ((subset_tsupport _).trans (hD f))) _root_.id)

/-- If `D` does not enlarge supports, then `f (D g)` is integrable whenever `f` or `g` has compact
support. -/
theorem integrable_mul_apply_of_tsupport_subset (hD : ∀ f, tsupport (D f) ⊆ tsupport f)
    {f g : C^n⟮I, M; 𝓘(𝕜, A), A⟯} (hfg : HasCompactSupport f ∨ HasCompactSupport g) :
    Integrable (fun x ↦ f x * D g x) μ :=
  integrable_mul_of_hasCompactSupport
    (hfg.imp _root_.id (·.mono' ((subset_tsupport _).trans (hD g))))

end ContMDiffMap
