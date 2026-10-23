/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.ContinuousInv
public import TauCeti.Topology.Algebra.Group.UCB.Basic

/-!
# Bounded functions on a discrete group

On a discrete group every bounded continuous function is uniformly continuous for the right
uniformity. Thus `TauCeti.UCB G` is the entire algebra `G →ᵇ ℝ`. The identification preserves
the supremum norm, pointwise order, constants, and left and right translations. Since every
function on a discrete space is continuous, this is the bounded-function space used for
finitely additive probabilities and discrete invariant means.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.1.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- Every bounded continuous function on a discrete group belongs to `ucb G`. -/
@[simp]
theorem mem_ucb_of_discreteTopology (f : G →ᵇ ℝ) : f ∈ ucb G := by
  rw [mem_ucb_iff]
  simp [nhds_discrete]

/-- On a discrete group the UCB subalgebra is the entire bounded-function algebra. -/
@[simp]
theorem ucb_eq_top : ucb G = ⊤ := by
  ext f
  simp

namespace UCB

variable (G) in
/-- The canonical algebra equivalence from UCB to all bounded functions on a discrete group. -/
def discreteAlgEquiv : UCB G ≃ₐ[ℝ] (G →ᵇ ℝ) :=
  (Subalgebra.equivOfEq _ _ ucb_eq_top).trans Subalgebra.topEquiv

@[simp]
theorem discreteAlgEquiv_apply (f : UCB G) : discreteAlgEquiv G f = (f : G →ᵇ ℝ) :=
  (rfl)

@[simp]
theorem coe_discreteAlgEquiv_symm (f : G →ᵇ ℝ) :
    ((discreteAlgEquiv G).symm f : G →ᵇ ℝ) = f :=
  (discreteAlgEquiv G).apply_symm_apply f

/-- The discrete identification preserves and reflects the pointwise order. -/
@[simp]
theorem discreteAlgEquiv_le_discreteAlgEquiv_iff {f h : UCB G} :
    discreteAlgEquiv G f ≤ discreteAlgEquiv G h ↔ f ≤ h :=
  Iff.rfl

/-- The inverse discrete identification preserves and reflects the pointwise order. -/
@[simp]
theorem discreteAlgEquiv_symm_le_discreteAlgEquiv_symm_iff {f h : G →ᵇ ℝ} :
    (discreteAlgEquiv G).symm f ≤ (discreteAlgEquiv G).symm h ↔ f ≤ h := by
  rw [← discreteAlgEquiv_le_discreteAlgEquiv_iff]
  simp

variable (G) in
/-- The discrete identification as a linear isometry equivalence for the supremum norm. -/
def discreteLinearIsometryEquiv : UCB G ≃ₗᵢ[ℝ] (G →ᵇ ℝ) where
  toLinearEquiv := (discreteAlgEquiv G).toLinearEquiv
  norm_map' _ := rfl

@[simp]
theorem discreteLinearIsometryEquiv_apply (f : UCB G) :
    discreteLinearIsometryEquiv G f = (f : G →ᵇ ℝ) :=
  (rfl)

@[simp]
theorem discreteLinearIsometryEquiv_symm_apply (f : G →ᵇ ℝ) :
    (discreteLinearIsometryEquiv G).symm f = (discreteAlgEquiv G).symm f :=
  (rfl)

end UCB

end TauCeti
