/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.BoundaryValue.Sobolev
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Symmetry of the boundary value operator of a chord with isotropic boundary conditions

Let `X` be a real inner product space with a skew-adjoint operator `J`, `⟪J u, v⟫ = -⟪u, J v⟫`,
such as a complex structure compatible with the inner product, so that `ω(u, v) = ⟪J u, v⟫` is a
skew form. Let `F₀` and `F₁` be subspaces of `X` which are isotropic for `ω`, such as two Lagrangian
subspaces of `ℂⁿ`, and let `A` be an essentially bounded coefficient on `(0, 1]` whose values are
`J`-symmetric, `⟪A t u, J v⟫ = ⟪J u, A t v⟫`; for a complex structure `J` this says that `J A(t)`
is symmetric. This file shows that the operator

`B = J (d/dt - A) : (w, w') ↦ J (w' - A w)`

from the Sobolev space `TauCeti.PathSobolev.H1 F₀ F₁` of paths with `w 0 ∈ F₀` and `w 1 ∈ F₁` to
`L²((0, 1], X)` is symmetric through the value map `ι = TauCeti.PathSobolev.valueL`,
`(w, w') ↦ w`:

`⟪B x, ι y⟫ = ⟪ι x, B y⟫`

(`TauCeti.PathSobolev.inner_compLpL_comp_boundaryValueOperator_valueL`).

For the coefficient term this is the pointwise `J`-symmetry of `A`. For the derivative term it is
integration by parts: for classical paths `w` and `v`, `t ↦ ⟪J w t, v t⟫` has derivative
`⟪J w', v⟫ - ⟪w, J v'⟫`, so the difference of the two pairings is the boundary term
`ω(w 1, v 1) - ω(w 0, v 0)`, which vanishes since both paths start in the isotropic `F₀` and end in
the isotropic `F₁` (`TauCeti.PathSobolev.setIntegral_inner_apply_deriv_eq`). Both sides are
continuous in `(x, y)`, and the jets of classical paths are dense in `H1`, so the identity extends
(`TauCeti.PathSobolev.inner_compLpL_derivL_valueL`).

For a Hamiltonian chord between two Lagrangians, with `A` the linearized Hamiltonian vector field
along the chord and `F₀`, `F₁` the tangent spaces of the Lagrangians at its ends, `B` is the
asymptotic operator of the stationary Floer strip over the chord. The Fredholm theorem for
trajectory operators over the common domain `D = H1 F₀ F₁`
(`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`) asks for two properties of
the limits `A(±∞)` of the linearized Floer operator on a strip between two Lagrangians: symmetry
through `ι`, proved here, and invertibility. For invertible `J` the latter is that of `d/dt - A`,
which holds exactly at a nondegenerate chord
(`TauCeti.PathSobolev.isInvertible_boundaryValueOperator_iff`).

## Main results

* `TauCeti.PathSobolev.setIntegral_inner_apply_deriv_eq`: integration by parts for classical
  paths with isotropic boundary values.
* `TauCeti.PathSobolev.inner_compLpL_derivL_valueL`: the derivative term `J d/dt` is symmetric
  through `ι` on `H1 F₀ F₁`.
* `TauCeti.PathSobolev.inner_compLpL_comp_boundaryValueOperator_valueL`: the operator
  `J (d/dt - A)` is symmetric through `ι`.

## References

* A. Floer, *Morse theory for Lagrangian intersections*, J. Differential Geom. **28** (1988),
  513–547 (the linearized operator on strips with Lagrangian boundary conditions).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33 (the self-adjoint operators `J (d/dt) + S(t)` with Lagrangian boundary
  conditions).
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

namespace PathSobolev

local notation "μ₁" => (volume.restrict (Ioc (0 : ℝ) 1))

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] {F₀ F₁ : Submodule ℝ X}
  {J : X →L[ℝ] X}

/-- **Integration by parts for paths with isotropic boundary values.** Let `J` be skew-adjoint and
let `F₀` and `F₁` be isotropic for the form `⟪J ·, ·⟫`. For `C¹` paths `w` and `v` with boundary
values in `F₀` and `F₁`, `∫₀¹ ⟪J w', v⟫ = ∫₀¹ ⟪w, J v'⟫`: the difference is the boundary term
`⟪J w 1, v 1⟫ - ⟪J w 0, v 0⟫`, which vanishes. -/
theorem setIntegral_inner_apply_deriv_eq (hJ : ∀ u v : X, ⟪J u, v⟫ = -⟪u, J v⟫)
    (hF₀ : ∀ u ∈ F₀, ∀ v ∈ F₀, ⟪J u, v⟫ = 0) (hF₁ : ∀ u ∈ F₁, ∀ v ∈ F₁, ⟪J u, v⟫ = 0)
    (w v : boundaryPath F₀ F₁) :
    ∫ t in Ioc 0 1, ⟪J (deriv (w : ℝ → X) t), (v : ℝ → X) t⟫ =
      ∫ t in Ioc 0 1, ⟪(w : ℝ → X) t, J (deriv (v : ℝ → X) t)⟫ := by
  have hw := contDiff_coe w
  have hv := contDiff_coe v
  have hcw := (hw.continuous_deriv le_rfl)
  have hcv := (hv.continuous_deriv le_rfl)
  -- The pairing `t ↦ ⟪J w t, v t⟫` has derivative `⟪J w t, v' t⟫ + ⟪J w' t, v t⟫`.
  have hderiv (t : ℝ) : HasDerivAt (fun t ↦ ⟪J ((w : ℝ → X) t), (v : ℝ → X) t⟫)
      (⟪J ((w : ℝ → X) t), deriv (v : ℝ → X) t⟫ + ⟪J (deriv (w : ℝ → X) t), (v : ℝ → X) t⟫)
      t :=
    (J.hasFDerivAt.comp_hasDerivAt t (hw.differentiable one_ne_zero t).hasDerivAt).inner ℝ
      (hv.differentiable one_ne_zero t).hasDerivAt
  have hcont : Continuous fun t ↦
      ⟪J ((w : ℝ → X) t), deriv (v : ℝ → X) t⟫ + ⟪J (deriv (w : ℝ → X) t), (v : ℝ → X) t⟫ :=
    ((J.continuous.comp hw.continuous).inner hcv).add
      ((J.continuous.comp hcw).inner hv.continuous)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
    (hcont.intervalIntegrable 0 1)
  rw [hF₁ _ (coe_one_mem w) _ (coe_one_mem v), hF₀ _ (coe_zero_mem w) _ (coe_zero_mem v),
    sub_zero] at hftc
  -- By skewness the integrand is `⟪J w', v⟫ - ⟪w, J v'⟫`.
  have hfun : (fun t ↦
      ⟪J ((w : ℝ → X) t), deriv (v : ℝ → X) t⟫ + ⟪J (deriv (w : ℝ → X) t), (v : ℝ → X) t⟫) =
      fun t ↦ ⟪J (deriv (w : ℝ → X) t), (v : ℝ → X) t⟫ -
        ⟪(w : ℝ → X) t, J (deriv (v : ℝ → X) t)⟫ := by
    funext t
    rw [hJ]
    ring
  rw [hfun, intervalIntegral.integral_sub ((J.continuous.comp hcw).inner hv.continuous
      |>.intervalIntegrable 0 1) (hw.continuous.inner (J.continuous.comp hcv)
      |>.intervalIntegrable 0 1), sub_eq_zero, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one] at hftc
  exact hftc

/-- On the jets of classical paths, the pairing of `J w'` with `v` in `L²` is the pairing of `w`
with `J v'`. -/
private theorem inner_compLpL_derivL_jetH1_valueL_jetH1 (hJ : ∀ u v : X, ⟪J u, v⟫ = -⟪u, J v⟫)
    (hF₀ : ∀ u ∈ F₀, ∀ v ∈ F₀, ⟪J u, v⟫ = 0) (hF₁ : ∀ u ∈ F₁, ∀ v ∈ F₁, ⟪J u, v⟫ = 0)
    (w v : boundaryPath F₀ F₁) :
    ⟪J.compLpL 2 μ₁ (derivL F₀ F₁ (jetH1 F₀ F₁ w)), valueL F₀ F₁ (jetH1 F₀ F₁ v)⟫ =
      ⟪valueL F₀ F₁ (jetH1 F₀ F₁ w), J.compLpL 2 μ₁ (derivL F₀ F₁ (jetH1 F₀ F₁ v))⟫ := by
  rw [valueL_jetH1, valueL_jetH1, derivL_jetH1, derivL_jetH1, L2.inner_def, L2.inner_def]
  calc ∫ t, ⟪J.compLpL 2 μ₁ ((memLp_deriv w).toLp (deriv (w : ℝ → X))) t,
          (memLp_coe v).toLp (v : ℝ → X) t⟫ ∂μ₁
      = ∫ t in Ioc 0 1, ⟪J (deriv (w : ℝ → X) t), (v : ℝ → X) t⟫ := by
        refine integral_congr_ae ?_
        filter_upwards [J.coeFn_compLpL ((memLp_deriv w).toLp (deriv (w : ℝ → X))),
          MemLp.coeFn_toLp (memLp_deriv w), MemLp.coeFn_toLp (memLp_coe v)] with t h₁ h₂ h₃
        rw [h₁, h₂, h₃]
    _ = ∫ t in Ioc 0 1, ⟪(w : ℝ → X) t, J (deriv (v : ℝ → X) t)⟫ :=
        setIntegral_inner_apply_deriv_eq hJ hF₀ hF₁ w v
    _ = ∫ t, ⟪(memLp_coe w).toLp (w : ℝ → X) t,
          J.compLpL 2 μ₁ ((memLp_deriv v).toLp (deriv (v : ℝ → X))) t⟫ ∂μ₁ := by
        refine integral_congr_ae ?_
        filter_upwards [J.coeFn_compLpL ((memLp_deriv v).toLp (deriv (v : ℝ → X))),
          MemLp.coeFn_toLp (memLp_deriv v), MemLp.coeFn_toLp (memLp_coe w)] with t h₁ h₂ h₃
        rw [h₁, h₂, h₃]

/-- **The derivative term is symmetric.** Let `J` be skew-adjoint and let `F₀` and `F₁` be
isotropic for the form `⟪J ·, ·⟫`. On the Sobolev space `H1 F₀ F₁`, the operator `(w, w') ↦ J w'`
is symmetric through the value map `ι : (w, w') ↦ w`: `⟪J x', ι y⟫ = ⟪ι x, J y'⟫` in `L²`. -/
theorem inner_compLpL_derivL_valueL (hJ : ∀ u v : X, ⟪J u, v⟫ = -⟪u, J v⟫)
    (hF₀ : ∀ u ∈ F₀, ∀ v ∈ F₀, ⟪J u, v⟫ = 0) (hF₁ : ∀ u ∈ F₁, ∀ v ∈ F₁, ⟪J u, v⟫ = 0)
    (x y : H1 F₀ F₁) :
    ⟪J.compLpL 2 μ₁ (derivL F₀ F₁ x), valueL F₀ F₁ y⟫ =
      ⟪valueL F₀ F₁ x, J.compLpL 2 μ₁ (derivL F₀ F₁ y)⟫ := by
  -- Both sides are continuous in each argument, and the identity holds on the dense set of jets
  -- of classical paths.
  have hcl (x : H1 F₀ F₁) : IsClosed {y : H1 F₀ F₁ |
      ⟪J.compLpL 2 μ₁ (derivL F₀ F₁ x), valueL F₀ F₁ y⟫ =
        ⟪valueL F₀ F₁ x, J.compLpL 2 μ₁ (derivL F₀ F₁ y)⟫} :=
    isClosed_eq (continuous_const.inner (valueL F₀ F₁).continuous)
      (continuous_const.inner ((J.compLpL 2 μ₁).continuous.comp (derivL F₀ F₁).continuous))
  have hjet (w : boundaryPath F₀ F₁) (y : H1 F₀ F₁) :
      ⟪J.compLpL 2 μ₁ (derivL F₀ F₁ (jetH1 F₀ F₁ w)), valueL F₀ F₁ y⟫ =
        ⟪valueL F₀ F₁ (jetH1 F₀ F₁ w), J.compLpL 2 μ₁ (derivL F₀ F₁ y)⟫ :=
    H1_induction (hcl _) (inner_compLpL_derivL_jetH1_valueL_jetH1 hJ hF₀ hF₁ w) y
  refine H1_induction (P := fun x ↦ ⟪J.compLpL 2 μ₁ (derivL F₀ F₁ x), valueL F₀ F₁ y⟫ =
      ⟪valueL F₀ F₁ x, J.compLpL 2 μ₁ (derivL F₀ F₁ y)⟫) ?_ (fun w ↦ hjet w y) x
  exact isClosed_eq
    ((((J.compLpL 2 μ₁).continuous.comp (derivL F₀ F₁).continuous)).inner continuous_const)
    ((valueL F₀ F₁).continuous.inner continuous_const)

/-- **The boundary value operator of a chord is symmetric.** Let `J` be skew-adjoint, let `F₀`
and `F₁` be isotropic for the form `⟪J ·, ·⟫`, such as two Lagrangian subspaces, and let the
coefficient `A` be `J`-symmetric almost everywhere: `⟪A t u, J v⟫ = ⟪J u, A t v⟫`. Then the
operator `B = J (d/dt - A) : (w, w') ↦ J (w' - A w)` from `H1 F₀ F₁` to `L²` is symmetric through
the value map `ι : (w, w') ↦ w`: `⟪B x, ι y⟫ = ⟪ι x, B y⟫`. -/
theorem inner_compLpL_comp_boundaryValueOperator_valueL (hJ : ∀ u v : X, ⟪J u, v⟫ = -⟪u, J v⟫)
    (hF₀ : ∀ u ∈ F₀, ∀ v ∈ F₀, ⟪J u, v⟫ = 0) (hF₁ : ∀ u ∈ F₁, ∀ v ∈ F₁, ⟪J u, v⟫ = 0)
    {A : Lp (X →L[ℝ] X) ∞ μ₁} (hA : ∀ᵐ t ∂μ₁, ∀ u v : X, ⟪A t u, J v⟫ = ⟪J u, A t v⟫)
    (x y : H1 F₀ F₁) :
    ⟪((J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ A)) x, valueL F₀ F₁ y⟫ =
      ⟪valueL F₀ F₁ x, ((J.compLpL 2 μ₁).comp (boundaryValueOperator F₀ F₁ A)) y⟫ := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, boundaryValueOperator_apply,
    boundaryValueOperator_apply, map_sub, map_sub, inner_sub_left, inner_sub_right,
    inner_compLpL_derivL_valueL hJ hF₀ hF₁]
  -- The coefficient term: `⟪J (A x), y⟫ = -⟪A x, J y⟫ = -⟪J x, A y⟫ = ⟪x, J (A y)⟫`.
  congr 1
  rw [Lp.inner_compLpL_eq_neg_inner_compLpL hJ, Lp.inner_operatorMultiplication_compLpL hA,
    Lp.inner_compLpL_eq_neg_inner_compLpL hJ, neg_neg]

end PathSobolev

end TauCeti
