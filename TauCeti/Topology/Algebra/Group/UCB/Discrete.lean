/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.ContinuousInv
public import TauCeti.Topology.Algebra.Group.UCB.Translation

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

/-- On a discrete group the UCB subalgebra is the entire bounded-function algebra. -/
@[simp]
theorem ucb_eq_top : ucb G = ⊤ := by
  ext f
  simp [mem_ucb_iff, nhds_discrete]

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

/-- The discrete identification sends left translation to precomposition by `g⁻¹ * ·`. -/
@[simp]
theorem discreteAlgEquiv_leftTranslation (g : G) (f : UCB G) :
    discreteAlgEquiv G (leftTranslation g f) =
      (discreteAlgEquiv G f).compContinuous (ContinuousMap.mulLeft g⁻¹) :=
  coe_leftTranslation g f

/-- The inverse discrete identification intertwines left translation. -/
@[simp]
theorem discreteAlgEquiv_symm_compContinuous_mulLeft (g : G) (f : G →ᵇ ℝ) :
    (discreteAlgEquiv G).symm (f.compContinuous (ContinuousMap.mulLeft g⁻¹)) =
      leftTranslation g ((discreteAlgEquiv G).symm f) := by
  apply (discreteAlgEquiv G).injective
  simp [coe_leftTranslation]

/-- The discrete identification sends right translation to precomposition by `· * g`. -/
@[simp]
theorem discreteAlgEquiv_rightTranslation (g : G) (f : UCB G) :
    discreteAlgEquiv G (rightTranslation g f) =
      (discreteAlgEquiv G f).compContinuous (ContinuousMap.mulRight g) :=
  coe_rightTranslation g f

/-- The inverse discrete identification intertwines right translation. -/
@[simp]
theorem discreteAlgEquiv_symm_compContinuous_mulRight (g : G) (f : G →ᵇ ℝ) :
    (discreteAlgEquiv G).symm (f.compContinuous (ContinuousMap.mulRight g)) =
      rightTranslation g ((discreteAlgEquiv G).symm f) := by
  apply (discreteAlgEquiv G).injective
  simp [coe_rightTranslation]

/-- The inverse discrete identification preserves and reflects the pointwise order. -/
@[simp]
theorem discreteAlgEquiv_symm_le_discreteAlgEquiv_symm_iff {f h : G →ᵇ ℝ} :
    (discreteAlgEquiv G).symm f ≤ (discreteAlgEquiv G).symm h ↔ f ≤ h :=
  Iff.rfl

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
