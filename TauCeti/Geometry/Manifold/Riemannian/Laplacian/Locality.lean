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
functions which agree near a point and are `C²` there have the same Laplacian at that point.

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

/-- Two functions which agree near a point and are `C²` there have the same Laplace–Beltrami
operator at that point. -/
theorem laplaceBeltrami_congr_of_eventuallyEq {f g : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hg : ContMDiffAt I 𝓘(ℝ) 2 g x) (h : f =ᶠ[𝓝 x] g) :
    laplaceBeltrami I f x = laplaceBeltrami I g x := by
  have : IsManifold I (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
  rw [← one_add_one_eq_two] at hf hg
  have hcov : CovariantDerivative.leviCivitaConnection I M (mgradient I f) x =
      CovariantDerivative.leviCivitaConnection I M (mgradient I g) x :=
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOn.congr_of_eventuallyEq
      ((contMDiffAt_mgradient (n := 1) hf).mdifferentiableAt (by simp))
      ((contMDiffAt_mgradient (n := 1) hg).mdifferentiableAt (by simp)) Filter.univ_mem
      (h.eventuallyEq_nhds.mono fun y hy ↦ by rw [mgradient_def, hy.mvfderiv_eq, ← mgradient_def])
  rw [laplaceBeltrami_def, laplaceBeltrami_def, divergence_def, divergence_def, hcov]

end TauCeti.Manifold
