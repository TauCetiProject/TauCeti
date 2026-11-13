/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Geometry.Manifold.Complex
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Nowhere vanishing holomorphic differentials

Suppose a compact connected Riemann surface `X` carries a holomorphic `1`-form `ω` with `ω x ≠ 0`
at every point, as the complex torus `ℂ / L` does with the descended form `dz`. Then:

* `ω` has order zero everywhere, so its divisor is zero and the zero divisor is canonical
  (`TauCeti.RiemannSurface.OneForm.divisor_eq_zero_of_apply_ne_zero`,
  `TauCeti.RiemannSurface.OneForm.isCanonicalDivisor_zero_of_apply_ne_zero`);
* every holomorphic `1`-form is a constant multiple of `ω`: the ratio `η / ω` is a holomorphic
  function on a compact connected surface, hence constant by the maximum principle
  (`MDifferentiable.exists_eq_const_of_compactSpace`). So the holomorphic `1`-forms are the line
  `ℂ ∙ ω` and have dimension one
  (`TauCeti.RiemannSurface.OneForm.holomorphicOneForms_eq_span_singleton_of_apply_ne_zero`,
  `TauCeti.RiemannSurface.OneForm.finrank_holomorphicOneForms_eq_one_of_apply_ne_zero`).

These give `h⁰(K) = 1` and `deg K = 0` in genus one, as for complex tori.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§9 and 17 (holomorphic differentials on tori, canonical divisors).
-/

public noncomputable section

open Filter Function IsManifold Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface.OneForm

open AlgebraicGeometry

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {ω η : OneForm X} {x : X}

section Global

variable (hω : ω ∈ holomorphicOneForms X) (hω₀ : ∀ x, ω x ≠ 0)
include hω hω₀

/-- **A nowhere vanishing holomorphic `1`-form spans the holomorphic `1`-forms.** On a compact
connected Riemann surface, every holomorphic `1`-form is a constant multiple of a holomorphic
`1`-form `ω` that vanishes nowhere: the ratio is a holomorphic function, hence constant. -/
theorem holomorphicOneForms_eq_span_singleton_of_apply_ne_zero [CompactSpace X]
    [ConnectedSpace X] : holomorphicOneForms X = ℂ ∙ ω := by
  refine le_antisymm (fun η hη ↦ ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hω)
  have hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (ratio η ω) := fun x ↦
    (mem_holomorphicOneForms.1 hη x).mdifferentiableAt_ratio (mem_holomorphicOneForms.1 hω x)
      (hω₀ x)
  obtain ⟨c, hc⟩ := hf.exists_eq_const_of_compactSpace
  refine Submodule.mem_span_singleton.2 ⟨c, funext fun x ↦ ?_⟩
  exact (ratio_eq_iff (hω₀ x)).1 (congrFun hc x)

/-- **The holomorphic `1`-forms are one-dimensional** on a compact connected Riemann surface
carrying a nowhere vanishing holomorphic `1`-form. -/
theorem finrank_holomorphicOneForms_eq_one_of_apply_ne_zero [CompactSpace X]
    [ConnectedSpace X] : Module.finrank ℂ (holomorphicOneForms X) = 1 := by
  rw [holomorphicOneForms_eq_span_singleton_of_apply_ne_zero hω hω₀]
  inhabit X
  exact finrank_span_singleton fun h ↦ hω₀ default (by rw [h, Pi.zero_apply])

/-- A nowhere vanishing holomorphic `1`-form on a compact Riemann surface has divisor zero. -/
theorem divisor_eq_zero_of_apply_ne_zero [CompactSpace X] : ω.divisor = 0 := by
  ext x
  rw [coeff_divisor (meromorphicAt_of_mem_holomorphicOneForms hω),
    (mem_holomorphicOneForms.1 hω x).order_eq_zero (hω₀ x)]
  rfl

/-- **The zero divisor is canonical** on a compact Riemann surface carrying a nowhere vanishing
holomorphic `1`-form. -/
theorem isCanonicalDivisor_zero_of_apply_ne_zero [CompactSpace X] :
    IsCanonicalDivisor (0 : WeilDivisor X) := by
  rw [← divisor_eq_zero_of_apply_ne_zero hω hω₀]
  refine isCanonicalDivisor_divisor (meromorphicAt_of_mem_holomorphicOneForms hω) fun x ↦ ?_
  rw [(mem_holomorphicOneForms.1 hω x).order_eq_zero (hω₀ x)]
  exact WithTop.zero_ne_top

end Global

end TauCeti.RiemannSurface.OneForm
