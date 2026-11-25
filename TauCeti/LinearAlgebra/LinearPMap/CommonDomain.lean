/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearPMap

/-!
# The partial linear map of a linear map on a common domain

A linear map `A : D →ₗ K` on a space `D` together with an injective linear map `ι : D →ₗ H`
defines the partial linear map `LinearMap.domainOperator ι A hι` from `H` to `K` with domain
`range ι`, acting by `ι x ↦ A x`. Unbounded operators are often described this way: by a bounded
operator on a smaller space with a bounded injective inclusion (see
`TauCeti.Topology.Algebra.Module.LinearPMap.CommonDomain`), or by an operator on test functions
or compactly supported smooth forms, which carry no topology, together with their injection into
an `L²` space.

This file gives the domain, the values, the graph and the range of this partial linear map: the
graph is the range of `x ↦ (ι x, A x)` (`LinearMap.graph_domainOperator`) and the range is the
range of `A` (`LinearMap.range_domainOperator`).

## Main definitions

* `LinearMap.domainOperator`: the partial linear map `ι x ↦ A x` with domain `range ι`.
-/

public section

noncomputable section

open Function

namespace LinearMap

variable {R D H K : Type*} [Ring R] [AddCommMonoid D] [Module R D] [AddCommGroup H] [Module R H]
  [AddCommGroup K] [Module R K] (ι : D →ₗ[R] H) (A : D →ₗ[R] K) (hι : Injective ι)

/-- The partial linear map from `H` to `K` with domain the range of an injective linear map
`ι : D →ₗ H`, acting by `ι x ↦ A x`. -/
def domainOperator : H →ₗ.[R] K where
  domain := range ι
  toFun := A ∘ₗ (LinearEquiv.ofInjective ι hι).symm.toLinearMap

/-- The domain of `domainOperator ι A hι` is the range of `ι`. -/
@[simp]
theorem domain_domainOperator : (domainOperator ι A hι).domain = range ι := (rfl)

/-- A vector lies in the domain of `domainOperator ι A hι` exactly when it is in the range of
`ι`. -/
theorem mem_domain_domainOperator_iff {y : H} :
    y ∈ (domainOperator ι A hι).domain ↔ ∃ x, ι x = y :=
  mem_range

/-- Every `ι x` lies in the domain of `domainOperator ι A hι`. -/
theorem apply_mem_domain_domainOperator (x : D) : ι x ∈ (domainOperator ι A hι).domain :=
  (mem_domain_domainOperator_iff ι A hι).2 ⟨x, rfl⟩

/-- `domainOperator ι A hι` sends `ι x` to `A x`. -/
theorem domainOperator_apply {y : (domainOperator ι A hι).domain} {x : D} (hx : ι x = y) :
    domainOperator ι A hι y = A x := by
  have hy : y = LinearEquiv.ofInjective ι hι x :=
    Subtype.ext (hx.symm.trans (LinearEquiv.ofInjective_apply _ x).symm)
  -- This lemma is where the definition of `domainOperator` is deliberately unfolded: its value at
  -- `ofInjective ι hι x` is `A ((ofInjective ι hι).symm (ofInjective ι hι x))`.
  rw [hy]
  exact congrArg A ((LinearEquiv.ofInjective ι hι).symm_apply_apply x)

/-- `domainOperator ι A hι` sends `ι x` to `A x`. -/
@[simp]
theorem domainOperator_apply_mk (x : D) (hx : ι x ∈ (domainOperator ι A hι).domain) :
    domainOperator ι A hι ⟨ι x, hx⟩ = A x :=
  domainOperator_apply ι A hι rfl

/-- A pair `(y, z)` lies on the graph of `domainOperator ι A hι` exactly when `y = ι x` and
`z = A x` for some `x : D`. -/
theorem mem_graph_domainOperator_iff {p : H × K} :
    p ∈ (domainOperator ι A hι).graph ↔ ∃ x, ι x = p.1 ∧ A x = p.2 := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨⟨y, hy⟩, hy₁, hy₂⟩
    obtain ⟨x, rfl⟩ := (mem_domain_domainOperator_iff ι A hι).1 hy
    exact ⟨x, hy₁, (domainOperator_apply_mk ι A hι x hy).symm.trans hy₂⟩
  · rintro ⟨x, hx₁, hx₂⟩
    exact ⟨⟨ι x, apply_mem_domain_domainOperator ι A hι x⟩, hx₁,
      (domainOperator_apply_mk ι A hι x _).trans hx₂⟩

/-- The graph of `domainOperator ι A hι` is the range of `x ↦ (ι x, A x)`. -/
theorem graph_domainOperator : (domainOperator ι A hι).graph = range (ι.prod A) := by
  ext p
  rw [mem_graph_domainOperator_iff]
  simp [Prod.ext_iff]

/-- The range of `domainOperator ι A hι` is the range of `A`. -/
theorem range_domainOperator : range (domainOperator ι A hι).toFun = range A :=
  range_comp_of_range_eq_top A (LinearEquiv.range _)

/-- For the identity inclusion, `domainOperator` is the everywhere defined map `A`. -/
theorem domainOperator_id (A : H →ₗ[R] K) :
    domainOperator LinearMap.id A injective_id = A.toPMap ⊤ := by
  refine LinearPMap.ext ?_ fun y hy hy' ↦ ?_
  · rw [domain_domainOperator, toPMap_domain, range_id]
  · -- `rw [LinearMap.toPMap_apply]` does not find the coercion of `LinearMap.toPMap`, so the two
    -- formulas are composed as terms.
    exact (domainOperator_apply _ A _ (x := y) rfl).trans (toPMap_apply A ⊤ ⟨y, hy'⟩).symm

end LinearMap
