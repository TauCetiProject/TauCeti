/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import TauCeti.Topology.Algebra.Group.UCB.CompRight
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Extending bounded functions from a subgroup of a discrete group

A right transversal `T` of `H ≤ G` writes each `x : G` uniquely as `h * t`, with `h ∈ H`
and `t ∈ T`. The first coordinate of Mathlib's `Subgroup.IsComplement.equiv` is an
`H`-equivariant map `G → H`. If `1 ∈ T`, it is a retraction onto `H`.

Precomposition with this map extends `UCB H` to `UCB G` when `G` is discrete. The extension
is a positive unital algebra homomorphism, preserves the supremum norm, and intertwines
translation by `H`. It allows a mean on `G` to average functions on `H`, even when `H` has
mass zero for the associated invariant probability.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 2.2 (subgroups).
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2.

The coset decomposition and its equivariance are supplied by Mathlib's
`Subgroup.IsComplement.equiv` and `Subgroup.IsComplement.equiv_mul_left`.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction

namespace TauCeti.UCB

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  {H : Subgroup G}

/-- Extend a bounded function on a subgroup by making it constant in the right-transversal
coordinate: `f (h * t) = f h`. -/
def extendSubgroup (T : H.RightTransversal) : UCB H →ₐ[ℝ] UCB G where
  toFun f :=
    ⟨(f : H →ᵇ ℝ).compContinuous ⟨fun x => (T.2.equiv x).1, continuous_of_discreteTopology⟩,
      mem_ucb_iff.2 fun ε hε => by simpa [nhds_discrete] using hε⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The extension evaluates on the subgroup coordinate of the coset decomposition.
Use this formula explicitly so simplification can retain the specialized subgroup
evaluation rules below. -/
theorem extendSubgroup_apply (T : H.RightTransversal) (f : UCB H) (x : G) :
    (extendSubgroup T f : G →ᵇ ℝ) x = (f : H →ᵇ ℝ) (T.2.equiv x).1 :=
  (rfl)

/-- On `h * t`, the extension takes the value at `h`. -/
@[simp]
theorem extendSubgroup_apply_mul (T : H.RightTransversal) (f : UCB H) (h : H) (t : T.1) :
    (extendSubgroup T f : G →ᵇ ℝ) (h * t) = (f : H →ᵇ ℝ) h := by
  rw [extendSubgroup_apply, ← T.2.equiv_symm_apply (h, t), T.2.equiv.apply_symm_apply]

/-- With the identity chosen to represent `H`, extension agrees with the original function
on `H`. -/
@[simp]
theorem extendSubgroup_apply_coe (T : H.RightTransversal) (hT : 1 ∈ T.1) (f : UCB H)
    (h : H) : (extendSubgroup T f : G →ᵇ ℝ) h = (f : H →ᵇ ℝ) h := by
  rw [extendSubgroup_apply, T.2.equiv_fst_eq_self_of_mem_of_one_mem hT h.2]
  congr 1

/-- Restriction to the subgroup is a left inverse of extension for a normalized transversal. -/
@[simp]
theorem compRightAlgHom_extendSubgroup (T : H.RightTransversal) (hT : 1 ∈ T.1) (f : UCB H) :
    compRightAlgHom (ContinuousMonoidHom.subgroupSubtype H) (extendSubgroup T f) = f := by
  ext h
  rw [compRightAlgHom_apply]
  exact extendSubgroup_apply_coe T hT f h

/-- Extension preserves the pointwise order. -/
theorem monotone_extendSubgroup (T : H.RightTransversal) : Monotone (extendSubgroup T) :=
  fun _ _ h => le_def.2 fun x => le_def.1 h (T.2.equiv x).1

/-- Extension preserves the supremum norm, for any right transversal. -/
@[simp]
theorem norm_extendSubgroup (T : H.RightTransversal) (f : UCB H) :
    ‖(extendSubgroup T f : G →ᵇ ℝ)‖ = ‖(f : H →ᵇ ℝ)‖ := by
  refine le_antisymm ((f : H →ᵇ ℝ).norm_compContinuous_le _) ?_
  let t := (T.2.equiv 1).2
  refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun h => ?_
  have hb := (extendSubgroup T f : G →ᵇ ℝ).norm_coe_le_norm ((h : G) * t)
  rwa [Real.norm_eq_abs, extendSubgroup_apply_mul] at hb

/-- Extension intertwines translation on the subgroup with translation by its image in `G`. -/
theorem extendSubgroup_leftTranslation (T : H.RightTransversal) (h : H) (f : UCB H) :
    extendSubgroup T (leftTranslation h f) = leftTranslation (h : G) (extendSubgroup T f) := by
  ext x
  simp only [leftTranslation_apply, extendSubgroup_apply]
  exact congrArg (fun y => (f : H →ᵇ ℝ) y.1) (T.2.equiv_mul_left h⁻¹ x).symm

end TauCeti.UCB
