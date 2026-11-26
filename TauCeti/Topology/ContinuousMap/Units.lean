/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Exponentials in the units of `C(X, ℂ)`

For a locally compact space `X`, the units of the ring `C(X, ℂ)` of continuous complex functions,
with the compact-open topology, form a topological group. A unit that is pointwise the exponential
`exp ∘ g` of a continuous function `g` lies in its identity component: the path `s ↦ exp (s g)`
of units joins `1` to it (`ContinuousMap.mem_connectedComponentOfOne_of_exp`).
-/

public section

namespace ContinuousMap

/-- A unit of `C(X, ℂ)` that is the exponential of a continuous function `g` lies in the identity
component of the unit group: `s ↦ exp (s g)` joins it to `1` through units. -/
theorem mem_connectedComponentOfOne_of_exp {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] {u : C(X, ℂ)ˣ} {g : C(X, ℂ)}
    (hg : ∀ x, (u : C(X, ℂ)) x = Complex.exp (g x)) :
    u ∈ Subgroup.connectedComponentOfOne C(X, ℂ)ˣ := by
  let E : C(ℝ, C(X, ℂ)) :=
    curry ⟨fun p : ℝ × X ↦ Complex.exp (p.1 * g p.2), by fun_prop⟩
  have hE (s t : ℝ) : E s * E t = E (s + t) := by
    ext x
    simp [E, ← Complex.exp_add, add_mul]
  have hE₀ : E 0 = 1 := by
    ext x
    simp [E]
  let v : ℝ → C(X, ℂ)ˣ := fun s ↦
    ⟨E s, E (-s), by simp [hE, hE₀], by simp [hE, hE₀]⟩
  have hv : Continuous v :=
    Units.continuous_iff.2 ⟨E.continuous, E.continuous.comp continuous_neg⟩
  have hv₀ : v 0 = 1 := Units.ext (by simpa [v] using hE₀)
  have hv₁ : v 1 = u := Units.ext (by ext x; simp [v, E, hg])
  exact (isPreconnected_range hv).subset_connectedComponent ⟨0, hv₀⟩ ⟨1, hv₁⟩

end ContinuousMap
