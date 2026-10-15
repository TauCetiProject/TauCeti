/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# Continuity of the functional calculus in its function at elements of finite spectrum

Mathlib's `tendsto_cfc_fun` passes uniform convergence on the spectrum, among functions continuous
on the spectrum, to the continuous functional calculus. When the spectrum of `a` is finite, every
function is continuous on it and pointwise convergence on it is uniform, so pointwise convergence
on the spectrum alone gives `cfc (F x) a → cfc f a`. This applies, for example, to every matrix.

## Main results

* `TauCeti.tendsto_cfc_fun_of_finite_spectrum` — at an element of finite spectrum, pointwise
  convergence of functions on the spectrum gives convergence of their functional calculi.
-/

public section

open Filter Topology

namespace TauCeti

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
  [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- If the spectrum of `a` is finite and `F x → f` pointwise on it along a filter `l`, then
`cfc (F x) a → cfc f a`. No continuity of `F x` or `f` is needed. -/
theorem tendsto_cfc_fun_of_finite_spectrum {l : Filter X} {F : X → R → R} {f : R → R} {a : A}
    (ha : (spectrum R a).Finite) (hFf : ∀ t ∈ spectrum R a, Tendsto (fun x ↦ F x t) l (𝓝 (f t))) :
    Tendsto (fun x ↦ cfc (F x) a) l (𝓝 (cfc f a)) := by
  refine tendsto_cfc_fun ?_ (Eventually.of_forall fun _ ↦ ha.continuousOn _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  exact ha.eventually_all.2 fun t ht ↦
    (Metric.tendsto_nhds.1 (hFf t ht) ε hε).mono fun _ h ↦ by rwa [dist_comm]

end TauCeti
