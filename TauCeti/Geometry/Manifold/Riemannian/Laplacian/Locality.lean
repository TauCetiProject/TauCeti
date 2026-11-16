/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian

/-!
# Locality of the Laplace–Beltrami operator

The Laplace–Beltrami operator is a differential operator, so its value at a point depends only
on the germ of the function there. It vanishes off the topological support of a function, and two
`C²` functions which agree near a point have the same Laplacian at that point.

## Main results

* `TauCeti.Manifold.laplaceBeltrami_eq_zero_of_notMem_tsupport`: `Δ f x = 0` for `x` off the
  topological support of `f`.
* `TauCeti.Manifold.laplaceBeltrami_congr_of_eventuallyEq`: `Δ f x = Δ g x` when `f = g` near `x`.
-/

public section

open Bundle Filter
open scoped Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The Laplace–Beltrami operator vanishes off the topological support of a function. -/
theorem laplaceBeltrami_eq_zero_of_notMem_tsupport {f : M → ℝ} {x : M}
    (hx : x ∉ tsupport f) : laplaceBeltrami I f x = 0 := by
  rw [laplaceBeltrami_def]
  refine divergence_eq_zero_of_notMem_tsupport I fun hx' ↦ hx ?_
  refine closure_minimal (fun y hy ↦ by_contra fun h ↦ (Function.mem_support.1 hy) ?_)
    (isClosed_tsupport f) hx'
  exact mgradient_eq_zero_iff.2 <|
    (notMem_tsupport_iff_eventuallyEq.1 h).mvfderiv_eq.trans mvfderiv_zero

/-- Two `C²` functions which agree near a point have the same Laplace–Beltrami operator there. -/
theorem laplaceBeltrami_congr_of_eventuallyEq {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) {x : M} (h : f =ᶠ[𝓝 x] g) :
    laplaceBeltrami I f x = laplaceBeltrami I g x := by
  have h0 := laplaceBeltrami_eq_zero_of_notMem_tsupport I
    (notMem_tsupport_iff_eventuallyEq.2 h.sub_eq)
  rwa [laplaceBeltrami_sub I hf hg, sub_eq_zero] at h0

end TauCeti.Manifold
