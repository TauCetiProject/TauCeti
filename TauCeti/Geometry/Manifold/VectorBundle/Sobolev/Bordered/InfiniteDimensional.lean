/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# `W^{k,p}(V)` over a surface with boundary is infinite-dimensional

Let `M` be a `Cᵏ` manifold modelled on the closed upper half-plane and `V → M` a `Cᵏ` vector bundle
with finite-dimensional fibre. The bordered Sobolev space `W^{k,p}(V)` of
`TauCeti.BorderedSobolevSection A p k` contains the `Cᵏ` sections
(`TauCeti.BorderedSobolevSection.ofContMDiffSection_injective`), so it is infinite-dimensional as
soon as the `Cᵏ` sections are (`TauCeti.BorderedSobolevSection.not_finiteDimensional`), and then
its identity is not a compact operator, by Riesz's theorem
(`TauCeti.BorderedSobolevSection.not_isCompactOperator_id`). This is in contrast with Rellich
compactness, which concerns the inclusion that forgets one derivative and is not proved here.

## Main results

* `TauCeti.BorderedSobolevSection.not_finiteDimensional`: `W^{k,p}(V)` is infinite-dimensional
  when the `Cᵏ` sections are.
* `TauCeti.BorderedSobolevSection.not_isCompactOperator_id`: its identity is then not compact.
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ENNReal ContDiff

namespace TauCeti

namespace BorderedSobolevSection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ} [IsManifold closedUpperHalfPlaneModel k M]
  [ContMDiffVectorBundle k F V closedUpperHalfPlaneModel]

/-- **`W^{k,p}(V)` is infinite-dimensional** when the `Cᵏ` sections of `V` are, since it contains
them. -/
theorem not_finiteDimensional (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V)
    (h : ¬ FiniteDimensional ℝ Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯) :
    ¬ FiniteDimensional ℝ (BorderedSobolevSection A p k) := fun _ ↦
  h (FiniteDimensional.of_injective (ofContMDiffSection A p k) (ofContMDiffSection_injective A p k))

/-- **The identity is not compact.** If the `Cᵏ` sections of `V` form an infinite-dimensional
space, the identity of `W^{k,p}(V)` is not a compact operator. -/
theorem not_isCompactOperator_id (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V)
    (h : ¬ FiniteDimensional ℝ Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯) :
    ¬ IsCompactOperator (id : BorderedSobolevSection A p k → BorderedSobolevSection A p k) :=
  fun hc ↦ not_finiteDimensional A h (FiniteDimensional.of_isCompactOperator_id hc)

end BorderedSobolevSection

end TauCeti
