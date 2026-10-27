/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.ContinuousInv
public import TauCeti.Topology.Algebra.Group.UCB.CompRight

/-!
# Bounded functions on a discrete group

On a discrete group every bounded continuous function is uniformly continuous for the right
uniformity. Thus `TauCeti.UCB G` is the entire algebra `G →ᵇ ℝ`. The identification preserves
the supremum norm, pointwise order, constants, and left and right translations. Since every
function on a discrete space is continuous, this is the bounded-function space used for
finitely additive probabilities and discrete invariant means.

For the same reason, precomposition `f ↦ f ∘ r` with an arbitrary map `r : G → H` into a
topological group sends `UCB H` to `UCB G`; this is `TauCeti.UCB.compRightAlgHomOfDiscrete r`.
When `r` is equivariant along a homomorphism `φ : H →* G`, in the sense that
`r (φ h * x) = h * r x`, the pullback intertwines `L_h` with `L_(φ h)`. Such maps arise as the
retractions of a discrete group onto a subgroup along a choice of right coset representatives.

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

/-- The inverse discrete identification intertwines left translation. -/
@[simp]
theorem discreteAlgEquiv_symm_compContinuous_mulLeft (g : G) (f : G →ᵇ ℝ) :
    (discreteAlgEquiv G).symm (f.compContinuous (ContinuousMap.mulLeft g⁻¹)) =
      leftTranslation g ((discreteAlgEquiv G).symm f) := by
  apply (discreteAlgEquiv G).injective
  simp [coe_leftTranslation]

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

section CompRight

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- On a discrete group `G`, the pullback `f ↦ f ∘ r` along an arbitrary map `r : G → H`, as a
unital algebra homomorphism from `UCB H` to `UCB G`. -/
def compRightAlgHomOfDiscrete (r : G → H) : UCB H →ₐ[ℝ] UCB G where
  toFun f := (discreteAlgEquiv G).symm
    ((f : H →ᵇ ℝ).compContinuous ⟨r, continuous_of_discreteTopology⟩)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The pullback `f ∘ r` is the precomposition of `f` with `r`. -/
theorem coe_compRightAlgHomOfDiscrete (r : G → H) (f : UCB H) :
    (compRightAlgHomOfDiscrete r f : G →ᵇ ℝ) =
      (f : H →ᵇ ℝ).compContinuous ⟨r, continuous_of_discreteTopology⟩ :=
  (rfl)

@[simp]
theorem compRightAlgHomOfDiscrete_apply (r : G → H) (f : UCB H) (x : G) :
    (compRightAlgHomOfDiscrete r f : G →ᵇ ℝ) x = (f : H →ᵇ ℝ) (r x) :=
  (rfl)

/-- Along a continuous homomorphism, the pullback out of a discrete group is the pullback
`TauCeti.UCB.compRightAlgHom`. -/
theorem compRightAlgHomOfDiscrete_coe (φ : G →ₜ* H) :
    compRightAlgHomOfDiscrete (φ : G → H) = compRightAlgHom φ :=
  AlgHom.ext fun _ => ext fun _ => by simp

/-- The pullback preserves the pointwise order. -/
theorem monotone_compRightAlgHomOfDiscrete (r : G → H) :
    Monotone (compRightAlgHomOfDiscrete r) :=
  fun _ _ h => le_def.2 fun x => le_def.1 h (r x)

/-- The pullback does not increase the supremum norm. -/
theorem norm_compRightAlgHomOfDiscrete_apply_le (r : G → H) (f : UCB H) :
    ‖compRightAlgHomOfDiscrete r f‖ ≤ ‖f‖ :=
  (f : H →ᵇ ℝ).norm_compContinuous_le _

/-- If `r (φ h * x) = h * r x` for a homomorphism `φ : H →* G`, then the pullback along `r`
intertwines left translation by `h` with left translation by `φ h`. -/
theorem compRightAlgHomOfDiscrete_leftTranslation (φ : H →* G) {r : G → H}
    (hr : ∀ h x, r (φ h * x) = h * r x) (h : H) (f : UCB H) :
    compRightAlgHomOfDiscrete r (leftTranslation h f) =
      leftTranslation (φ h) (compRightAlgHomOfDiscrete r f) := by
  ext x
  simp [← map_inv, hr]

end CompRight

end UCB

end TauCeti
