/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.RepresentationTheory.InvariantForm.SumOfConjugates

/-!
# Invariant inner products for finite group actions

A real inner product can be summed over a finite group action by linear automorphisms.  The
resulting positive-definite symmetric bilinear form is preserved by the action, without any
faithfulness assumption.  Its positive sublevel sets are invariant neighbourhoods of the origin,
open in finite dimensions, and arbitrarily small such sublevel sets fit inside a prescribed open
neighbourhood.

These invariant ellipsoids are the linear-algebraic shrinking device in finite-action charts: an
equivariant chart about a fixed point can be restricted to an invariant ball while retaining every
group element, including elements acting trivially.

The construction specializes `Representation.sumOfConjugatesForm`, the undivided form average
already used for invariant-form theory.  Division by the positive group order would only rescale
the form and its sublevel sets.  This is the classical construction used in the proof of Bochner
linearization; see S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math.
46 (1945), 372–381.

## Main definitions and results

* `Representation.posDef_toQuadraticMap_sumOfConjugatesForm_inner`: the orbit-sum inner product is
  positive definite.
* `Representation.invariantInnerSublevel`: its invariant sublevel sets, open in finite
  dimensions.
* `Representation.exists_pos_invariantInnerSublevel_subset`: arbitrarily small invariant sublevel
  sets exist.
-/

public section

open LinearMap (BilinForm)

namespace Representation

section Monoid

variable {G V : Type*} [Monoid G] [Fintype G]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The orbit-sum inner product of `x` with itself is the sum of the squared norms of the points
`ρ g x`. -/
theorem sumOfConjugatesForm_inner_apply_self (ρ : Representation ℝ G V) (x : V) :
    sumOfConjugatesForm ρ (innerₗ V) x x = ∑ g : G, ‖ρ g x‖ ^ 2 := by
  simp [sumOfConjugatesForm_apply]

/-- The orbit-sum inner product is positive definite. -/
theorem posDef_toQuadraticMap_sumOfConjugatesForm_inner (ρ : Representation ℝ G V) :
    (sumOfConjugatesForm ρ (innerₗ V)).toQuadraticMap.PosDef := by
  intro x hx
  rw [LinearMap.BilinMap.toQuadraticMap_apply, sumOfConjugatesForm_inner_apply_self]
  refine Finset.sum_pos' (fun g _ ↦ sq_nonneg ‖ρ g x‖) ⟨1, Finset.mem_univ _, ?_⟩
  rw [map_one, Module.End.one_apply]
  exact pow_pos (norm_pos_iff.mpr hx) 2

/-- The orbit-sum quadratic value varies continuously in finite dimensions. -/
theorem continuous_sumOfConjugatesForm_inner_apply_self [FiniteDimensional ℝ V]
    (ρ : Representation ℝ G V) :
    Continuous fun x ↦ sumOfConjugatesForm ρ (innerₗ V) x x := by
  simp only [sumOfConjugatesForm_inner_apply_self]
  have hρ := fun g ↦ LinearMap.continuous_of_finiteDimensional (ρ g)
  fun_prop

/-- The orbit-sum inner product controls the original squared norm through the identity summand. -/
theorem norm_sq_le_sumOfConjugatesForm_inner_apply_self (ρ : Representation ℝ G V) (x : V) :
    ‖x‖ ^ 2 ≤ sumOfConjugatesForm ρ (innerₗ V) x x := by
  rw [sumOfConjugatesForm_inner_apply_self]
  have h := Finset.single_le_sum (fun g _ ↦ sq_nonneg ‖ρ g x‖) (Finset.mem_univ (1 : G))
  rwa [map_one, Module.End.one_apply] at h

/-- The positive sublevel set of the orbit-sum inner product.  The parameter is its squared
radius. -/
def invariantInnerSublevel (ρ : Representation ℝ G V) (c : ℝ) : Set V :=
  {x | sumOfConjugatesForm ρ (innerₗ V) x x < c}

@[simp]
theorem mem_invariantInnerSublevel (ρ : Representation ℝ G V) {c : ℝ} {x : V} :
    x ∈ ρ.invariantInnerSublevel c ↔ sumOfConjugatesForm ρ (innerₗ V) x x < c := Iff.rfl

/-- Invariant inner sublevel sets are open in finite dimensions. -/
theorem isOpen_invariantInnerSublevel [FiniteDimensional ℝ V] (ρ : Representation ℝ G V)
    (c : ℝ) : IsOpen (ρ.invariantInnerSublevel c) :=
  isOpen_lt ρ.continuous_sumOfConjugatesForm_inner_apply_self continuous_const

/-- Every open neighbourhood of the origin contains a positive invariant inner sublevel set. -/
theorem exists_pos_invariantInnerSublevel_subset (ρ : Representation ℝ G V) {U : Set V}
    (hU : IsOpen U) (h0 : 0 ∈ U) :
    ∃ c > 0, ρ.invariantInnerSublevel c ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU 0 h0
  refine ⟨r ^ 2, pow_pos hr 2, fun x hx ↦ hrU ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  have hsq := (ρ.norm_sq_le_sumOfConjugatesForm_inner_apply_self x).trans_lt
    ((ρ.mem_invariantInnerSublevel).1 hx)
  exact (pow_lt_pow_iff_left₀ (norm_nonneg x) hr.le two_ne_zero).1 hsq

end Monoid

section Group

variable {G V : Type*} [Group G] [Fintype G]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Every group element preserves every invariant inner sublevel set. -/
@[simp]
theorem preimage_invariantInnerSublevel (ρ : Representation ℝ G V) (g : G) (c : ℝ) :
    ρ g ⁻¹' ρ.invariantInnerSublevel c = ρ.invariantInnerSublevel c := by
  ext x
  simp only [Set.mem_preimage, mem_invariantInnerSublevel]
  rw [isInvariantForm_sumOfConjugatesForm ρ (innerₗ V) |>.apply]

end Group

end Representation
