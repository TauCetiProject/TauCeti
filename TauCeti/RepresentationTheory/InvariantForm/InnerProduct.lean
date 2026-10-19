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
faithfulness assumption.  Its positive sublevel sets are invariant open neighbourhoods of the
origin, and arbitrarily small such neighbourhoods fit inside a prescribed open neighbourhood.

These invariant ellipsoids are the linear-algebraic shrinking device in finite-action charts: an
equivariant chart about a fixed point can be restricted to an invariant ball while retaining every
group element, including elements acting trivially.

The construction specializes `Representation.sumOfConjugatesForm`, the undivided form average
already used for invariant-form theory.  Division by the positive group order would only rescale
the form and its balls.  This is the classical construction used in the proof of Bochner
linearization; see S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math.
46 (1945), 372–381.

## Main definitions and results

* `Representation.posDef_toQuadraticMap_sumOfConjugatesForm_inner`: the orbit-sum inner product is
  positive definite.
* `Representation.invariantInnerBall`: its open invariant sublevel sets.
* `Representation.exists_pos_invariantInnerBall_subset`: arbitrarily small invariant balls exist.
-/

public section

open LinearMap (BilinForm)

namespace Representation

section Monoid

variable {G V : Type*} [Monoid G] [Fintype G]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The orbit sum of the ambient inner product is the sum of the squared orbit lengths. -/
theorem sumOfConjugatesForm_inner_apply_self (ρ : Representation ℝ G V) (x : V) :
    sumOfConjugatesForm ρ (innerₗ V) x x = ∑ g : G, ‖ρ g x‖ ^ 2 := by
  simp [sumOfConjugatesForm_apply]

/-- The orbit-sum inner product is positive definite. -/
theorem posDef_toQuadraticMap_sumOfConjugatesForm_inner (ρ : Representation ℝ G V) :
    (sumOfConjugatesForm ρ (innerₗ V)).toQuadraticMap.PosDef := by
  intro x hx
  rw [LinearMap.BilinMap.toQuadraticMap_apply, sumOfConjugatesForm_inner_apply_self]
  refine Finset.sum_pos' (fun g _ ↦ sq_nonneg ‖ρ g x‖) ⟨1, Finset.mem_univ _, ?_⟩
  simpa using sq_pos_of_pos (norm_pos_iff.mpr hx)

/-- The orbit-sum quadratic value varies continuously in finite dimensions. -/
theorem continuous_sumOfConjugatesForm_inner_apply_self [FiniteDimensional ℝ V]
    (ρ : Representation ℝ G V) :
    Continuous fun x ↦ sumOfConjugatesForm ρ (innerₗ V) x x := by
  rw [continuous_iff_continuousAt]
  intro x
  simp only [sumOfConjugatesForm_inner_apply_self]
  fun_prop (disch := aesop)

/-- The orbit-sum inner product controls the original squared norm through the identity summand. -/
theorem norm_sq_le_sumOfConjugatesForm_inner (ρ : Representation ℝ G V) (x : V) :
    ‖x‖ ^ 2 ≤ sumOfConjugatesForm ρ (innerₗ V) x x := by
  rw [sumOfConjugatesForm_inner_apply_self]
  simpa using
    (Finset.single_le_sum (fun g _ ↦ sq_nonneg ‖ρ g x‖) (Finset.mem_univ (1 : G)))

end Monoid

section Group

variable {G V : Type*} [Group G] [Fintype G]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The positive sublevel set of the orbit-sum inner product.  The parameter is its squared
radius. -/
def invariantInnerBall (ρ : Representation ℝ G V) (c : ℝ) : Set V :=
  {x | sumOfConjugatesForm ρ (innerₗ V) x x < c}

@[simp]
theorem mem_invariantInnerBall (ρ : Representation ℝ G V) {c : ℝ} {x : V} :
    x ∈ ρ.invariantInnerBall c ↔ sumOfConjugatesForm ρ (innerₗ V) x x < c := Iff.rfl

/-- Every group element preserves every invariant inner ball. -/
@[simp]
theorem preimage_invariantInnerBall (ρ : Representation ℝ G V) (g : G) (c : ℝ) :
    ρ g ⁻¹' ρ.invariantInnerBall c = ρ.invariantInnerBall c := by
  ext x
  simp only [Set.mem_preimage, mem_invariantInnerBall]
  rw [isInvariantForm_sumOfConjugatesForm ρ (innerₗ V) |>.apply]

/-- Invariant inner balls are open in finite dimensions. -/
theorem isOpen_invariantInnerBall [FiniteDimensional ℝ V] (ρ : Representation ℝ G V)
    (c : ℝ) : IsOpen (ρ.invariantInnerBall c) := by
  exact isOpen_lt ρ.continuous_sumOfConjugatesForm_inner_apply_self continuous_const

/-- Every open neighbourhood of the origin contains a positive invariant inner ball. -/
theorem exists_pos_invariantInnerBall_subset (ρ : Representation ℝ G V) {U : Set V}
    (hU : IsOpen U) (h0 : 0 ∈ U) :
    ∃ c > 0, ρ.invariantInnerBall c ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU 0 h0
  refine ⟨r ^ 2, sq_pos_of_pos hr, ?_⟩
  intro x hx
  apply hrU
  rw [Metric.mem_ball, dist_zero_right]
  have hnorm := ρ.norm_sq_le_sumOfConjugatesForm_inner x
  have havg := hx
  rw [mem_invariantInnerBall] at havg
  have hsq : ‖x‖ ^ 2 < r ^ 2 := by nlinarith
  nlinarith [norm_nonneg x]

end Group

end Representation
