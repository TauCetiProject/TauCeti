/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Topology.Algebra.PointTopology.Basic

/-!
# The point topology on the multiplicative group

For a commutative topological `R`-algebra `A`, the points of the multiplicative group
`𝔾ₘ = Spec R[T;T⁻¹]` with values in `A` are the units of `A`
(`TauCeti.MultiplicativeGroup.pointsMulEquiv`). A point is determined by its values on `T` and on
`T⁻¹`, so the point topology is the topology of `Aˣ` as the hyperbola `xy = 1` in `A × A`, that is,
Mathlib's topology on `Aˣ` induced by `Units.embedProduct`. This file bundles the identification as
an isomorphism of topological groups.

As an application, the points of an affine group over a totally disconnected ring are totally
disconnected (`TauCeti.PointTopology.instTotallyDisconnectedSpaceWithConv`), but the hypothesis on
the coefficient ring cannot be dropped: the real points of `𝔾ₘ` form `ℝˣ`, which contains the
connected half-line of positive reals.

## Main declarations

* `TauCeti.MultiplicativeGroup.pointsContinuousMulEquiv`: the points of `𝔾ₘ` with the point
  topology are isomorphic, as topological groups, to `Aˣ` with the units topology.
* `TauCeti.MultiplicativeGroup.not_totallyDisconnectedSpace_real`: the real points of `𝔾ₘ` are not
  totally disconnected.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  §3, pp. 3–4.
-/

public section

open WithConv TauCeti.PointTopology
open scoped LaurentPolynomial

namespace TauCeti.MultiplicativeGroup

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [TopologicalSpace A]
  [IsTopologicalSemiring A]

variable (R A) in
/-- The points of the multiplicative group with values in `A`, with the point topology, are
isomorphic as topological groups to the units of `A` with the topology induced by
`Units.embedProduct`. The underlying group isomorphism is `pointsMulEquiv`. -/
noncomputable def pointsContinuousMulEquiv : WithConv (R[T;T⁻¹] →ₐ[R] A) ≃ₜ* Aˣ where
  toMulEquiv := pointsMulEquiv
  -- The unit attached to a point and its inverse are the values on `T` and `T⁻¹`.
  continuous_toFun := Units.continuous_iff.mpr
    ⟨by simpa [Function.comp_def] using continuous_eval_ofConv (LaurentPolynomial.T (R := R) 1),
      by simpa using continuous_eval_ofConv (LaurentPolynomial.T (R := R) (-1))⟩
  continuous_invFun := by
    rw [continuous_withConv_iff]
    intro f
    simp only [MulEquiv.invFun_eq_symm, pointsMulEquiv_symm_apply, ofConv_toConv]
    induction f using LaurentPolynomial.induction_on' with
    | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
    | C_mul_T n a =>
      simp only [map_mul, laurentEval_C, laurentEval_T]
      refine continuous_const.mul ?_
      obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
      · simp only [zpow_natCast, Units.val_pow_eq_pow_val]
        exact Units.continuous_val.pow m
      · simp only [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
        exact Units.continuous_coe_inv.pow m

/-- The underlying group isomorphism of `pointsContinuousMulEquiv` is `pointsMulEquiv`. -/
@[simp]
theorem coe_pointsContinuousMulEquiv :
    (pointsContinuousMulEquiv R A : WithConv (R[T;T⁻¹] →ₐ[R] A) ≃* Aˣ) = pointsMulEquiv :=
  (rfl)

/-- The forward map of `pointsContinuousMulEquiv` is `pointsMulEquiv`. -/
@[simp]
theorem pointsContinuousMulEquiv_apply (f : WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    pointsContinuousMulEquiv R A f = pointsMulEquiv f :=
  (rfl)

/-- The inverse map of `pointsContinuousMulEquiv` is the inverse of `pointsMulEquiv`. -/
@[simp]
theorem pointsContinuousMulEquiv_symm_apply (u : Aˣ) :
    (pointsContinuousMulEquiv R A).symm u = (pointsMulEquiv (R := R)).symm u :=
  (rfl)

/-- The real points of the multiplicative group, with the point topology, are not totally
disconnected: they contain the connected image of the path `r ↦ exp r`. -/
theorem not_totallyDisconnectedSpace_real :
    ¬TotallyDisconnectedSpace (WithConv (ℝ[T;T⁻¹] →ₐ[ℝ] ℝ)) := by
  intro h
  let u : ℝ → ℝˣ := fun r ↦ Units.mk0 (Real.exp r) (Real.exp_ne_zero r)
  have hu : Continuous u := Units.continuous_iff.mpr ⟨Real.continuous_exp,
    by simpa [u, ← Real.exp_neg] using (by fun_prop : Continuous fun r : ℝ ↦ Real.exp (-r))⟩
  let g := fun r ↦ (pointsContinuousMulEquiv ℝ ℝ).symm (u r)
  have hsub := isTotallyDisconnected_of_totallyDisconnectedSpace (Set.range g) (Set.range g)
    subset_rfl (isPreconnected_range ((pointsContinuousMulEquiv ℝ ℝ).symm.continuous.comp hu))
  have h01 : u 0 = u 1 := (pointsContinuousMulEquiv ℝ ℝ).symm.injective (hsub ⟨0, rfl⟩ ⟨1, rfl⟩)
  have h1 : Real.exp 1 = 1 := by simpa [u] using (congrArg Units.val h01).symm
  exact one_ne_zero (Real.exp_eq_one_iff 1 |>.mp h1)

end TauCeti.MultiplicativeGroup
