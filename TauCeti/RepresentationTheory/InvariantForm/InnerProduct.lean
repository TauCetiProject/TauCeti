/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.RepresentationTheory.InvariantForm.SumOfConjugates

import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Invariant inner products for finite actions

A real inner product can be summed over a finite monoid representation.  The resulting
positive-definite symmetric bilinear form controls the original norm, and its positive strict
sublevel sets are convex, contain the origin and, in finite dimensions, are open neighbourhoods
of it; arbitrarily small such sublevel sets fit inside a prescribed open neighbourhood.  When the
monoid is a group, so that it acts by linear automorphisms, the form is preserved by the action,
without any faithfulness assumption, and so are its sublevel sets.

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
* `Representation.sumOfConjugatesInnerSublevel`: its strict sublevel sets, open in finite
  dimensions.
* `Representation.exists_pos_sumOfConjugatesInnerSublevel_subset`: arbitrarily small such
  sublevel sets exist.
* `Representation.convex_sumOfConjugatesInnerSublevel`: these sublevel sets are convex.
* `Representation.preimage_sumOfConjugatesInnerSublevel`: for a group, every element preserves
  these sublevel sets.
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
    (sumOfConjugatesForm ρ (innerₗ V)).toQuadraticMap.PosDef :=
  posDef_toQuadraticMap_sumOfConjugatesForm fun x hx ↦ by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, innerₗ_apply_apply]
    exact real_inner_self_pos.mpr hx

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
  have h := le_sumOfConjugatesForm_apply_self (σ := ρ) (B := innerₗ V)
    (fun _ ↦ real_inner_self_nonneg) x
  rwa [innerₗ_apply_apply, real_inner_self_eq_norm_sq] at h

/-- The strict sublevel set `{x | ∑ g, ‖ρ g x‖ ^ 2 < c}` of the orbit-sum inner product; the
parameter `c` is a squared radius, and the set is nonempty exactly when `0 < c`.  When `G` is a
group the set is `ρ`-invariant (`Representation.preimage_sumOfConjugatesInnerSublevel`). -/
def sumOfConjugatesInnerSublevel (ρ : Representation ℝ G V) (c : ℝ) : Set V :=
  {x | sumOfConjugatesForm ρ (innerₗ V) x x < c}

@[simp]
theorem mem_sumOfConjugatesInnerSublevel (ρ : Representation ℝ G V) {c : ℝ} {x : V} :
    x ∈ ρ.sumOfConjugatesInnerSublevel c ↔ sumOfConjugatesForm ρ (innerₗ V) x x < c := Iff.rfl

/-- The orbit-sum inner sublevel sets are open in finite dimensions. -/
theorem isOpen_sumOfConjugatesInnerSublevel [FiniteDimensional ℝ V] (ρ : Representation ℝ G V)
    (c : ℝ) : IsOpen (ρ.sumOfConjugatesInnerSublevel c) :=
  isOpen_lt ρ.continuous_sumOfConjugatesForm_inner_apply_self continuous_const

/-- Every open neighbourhood of the origin contains a positive orbit-sum inner sublevel set. -/
theorem exists_pos_sumOfConjugatesInnerSublevel_subset (ρ : Representation ℝ G V) {U : Set V}
    (hU : IsOpen U) (h0 : 0 ∈ U) :
    ∃ c > 0, ρ.sumOfConjugatesInnerSublevel c ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU 0 h0
  refine ⟨r ^ 2, pow_pos hr 2, fun x hx ↦ hrU ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  have hsq := (ρ.norm_sq_le_sumOfConjugatesForm_inner_apply_self x).trans_lt
    ((ρ.mem_sumOfConjugatesInnerSublevel).1 hx)
  exact (pow_lt_pow_iff_left₀ (norm_nonneg x) hr.le two_ne_zero).1 hsq

/-- The orbit-sum inner sublevel sets are convex. -/
theorem convex_sumOfConjugatesInnerSublevel (ρ : Representation ℝ G V) (c : ℝ) :
    Convex ℝ (ρ.sumOfConjugatesInnerSublevel c) := by
  have hf : ConvexOn ℝ Set.univ (∑ g : G, fun x ↦ ‖ρ g x‖ ^ 2) :=
    Finset.sum_induction _ (ConvexOn ℝ Set.univ) (fun _ _ ↦ ConvexOn.add)
      (convexOn_const 0 convex_univ) fun g _ ↦
        (convexOn_univ_norm.pow (fun _ _ ↦ norm_nonneg _) 2).comp_linearMap (ρ g)
  rw [Finset.sum_fn] at hf
  simpa [sumOfConjugatesInnerSublevel, sumOfConjugatesForm_inner_apply_self] using hf.convex_lt c

end Monoid

section Group

variable {G V : Type*} [Group G] [Fintype G]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Every group element preserves every orbit-sum inner sublevel set. -/
@[simp]
theorem preimage_sumOfConjugatesInnerSublevel (ρ : Representation ℝ G V) (g : G) (c : ℝ) :
    ρ g ⁻¹' ρ.sumOfConjugatesInnerSublevel c = ρ.sumOfConjugatesInnerSublevel c := by
  ext x
  simp only [Set.mem_preimage, mem_sumOfConjugatesInnerSublevel]
  rw [isInvariantForm_sumOfConjugatesForm ρ (innerₗ V) |>.apply]

end Group

end Representation
