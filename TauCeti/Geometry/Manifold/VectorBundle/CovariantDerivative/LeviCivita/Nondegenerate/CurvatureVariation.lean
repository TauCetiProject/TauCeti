/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Variation
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Variation
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Regularity

/-!
# The first variation of the curvature of a family of nondegenerate metrics

Let `g` be a smooth family of nondegenerate metrics on `M`, of any signature, parametrized by a
manifold `P`, let `c` be a parameter curve which is `C²` at `t`, and let `∇ˢ` be a Levi-Civita
connection of `g_{c s}` for every `s`. Write `Γ'` for the derivative at `s = t` of the difference
tensor `∇ˢ - ∇ᵗ` (Mathlib's `CovariantDerivative.difference`), so that `Γ'(Y, v) = ∂ₛ ∇ˢ_v Y`; it is
the tensor of the first variation formula of the Levi-Civita connection
(`ContMDiffNondegenerateMetricFamily.two_mul_apply_deriv_difference_eq_derivBilinearTensor`).
This file proves that the curvature `R^s(X, Y) Z` varies by

`∂ₛ R^s(X, Y) Z = (∇ᵗ_X Γ')(Z, Y) - (∇ᵗ_Y Γ')(Z, X)` at `s = t`,

where `(∇_X Γ')(Z, Y) = ∇_X (Γ'(Z, Y)) - Γ'(∇_X Z, Y) - Γ'(Z, ∇_X Y)`.

The curvature formula is the general variation formula for torsion-free families of connections,
`TauCeti.Manifold.hasDerivAt_curvatureOperator_of_hasDerivAt_difference`. Its hypotheses hold for
Levi-Civita connections: the difference tensors are differentiable in `s` by the first variation
of the Levi-Civita connection, and `(s, y) ↦ ∇ˢ_X Z (y)` is jointly `C²` by the joint regularity
of the Levi-Civita connections of a smooth metric family
(`ContMDiffNondegenerateMetricFamily.contMDiffOn_covariantDerivative_of_isLeviCivitaConnection`),
transferred to `∇ˢ` by uniqueness of the Levi-Civita connection.

## Main results

In the namespace `TauCeti.Manifold.ContMDiffNondegenerateMetricFamily`:

* `hasDerivAt_curvatureOperator_of_isLeviCivitaConnection`: the first variation of the curvature.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.K, Theorem 1.174.
* B. Chow and D. Knopf, *The Ricci Flow: An Introduction*, AMS (2004), Chapter 3, Lemma 3.2.
* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, CUP (2006), Section 2.3.
-/

public section

noncomputable section

open Bundle FiberBundle Filter Set VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  (g : ContMDiffNondegenerateMetricFamily I M IP P) {c : ℝ → P}
  {cov : ℝ → CovariantDerivative I E (fun x : M ↦ TangentSpace I x)} {t : ℝ}

variable [IsManifold IP 1 P] {x : M}

/-- **The first variation of the curvature of a family of nondegenerate metrics.** Let `g` be a
smooth family of nondegenerate metrics parametrized by `P`, let `c` be a parameter curve which is
`C²` at `t`, and let `∇ˢ` be a Levi-Civita connection of `g_{c s}` for every `s`. Write `Γ'` for the
derivative at `t` of the difference tensors `∇ˢ - ∇ᵗ`, the variation of the Levi-Civita connection
characterized by `two_mul_apply_deriv_difference_eq_derivBilinearTensor`, so that
`Γ'(Z, Y) = ∂ₛ ∇ˢ_Y Z`. Then for vector fields `X`, `Y` which are `C²` at `x` and `Z` which is `C³`
at `x`, the curvature `R^s(X, Y) Z` at `x` has parameter derivative

`(∇ᵗ_X Γ')(Z, Y) - (∇ᵗ_Y Γ')(Z, X)`

at `t`, where `(∇_X Γ')(Z, Y) = ∇_X (Γ'(Z, Y)) - Γ'(∇_X Z, Y) - Γ'(Z, ∇_X Y)`. -/
theorem hasDerivAt_curvatureOperator_of_isLeviCivitaConnection
    (hc : ContMDiffAt 𝓘(ℝ) IP 2 c t)
    (hcov : ∀ s, (g.metric (c s)).IsLeviCivitaConnection (cov s))
    {X Y Z : Π y : M, TangentSpace I y} (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x)
    (hZ : CMDiffAt 3 (T% Z) x) :
    HasDerivAt (fun s ↦ (cov s).curvatureOperator X Y Z x)
      ((cov t (fun y ↦ deriv (fun s ↦ (cov s).difference (cov t) y) t (Z y) (Y y)) x (X x) -
          deriv (fun s ↦ (cov s).difference (cov t) x) t (cov t Z x (X x)) (Y x) -
          deriv (fun s ↦ (cov s).difference (cov t) x) t (Z x) (cov t Y x (X x))) -
        (cov t (fun y ↦ deriv (fun s ↦ (cov s).difference (cov t) y) t (Z y) (X y)) x (Y x) -
          deriv (fun s ↦ (cov s).difference (cov t) x) t (cov t Z x (Y x)) (X x) -
          deriv (fun s ↦ (cov s).difference (cov t) x) t (Z x) (cov t X x (Y x)))) t := by
  have hC (y : M) : HasDerivAt (F := E →L[ℝ] E →L[ℝ] E)
      (fun s ↦ (cov s).difference (cov t) y)
      (deriv (fun s ↦ (cov s).difference (cov t) y) t) t :=
    DifferentiableAt.hasDerivAt (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] E)
      (g.differentiableAt_difference_of_isLeviCivitaConnection hc hcov y)
  have hZ' : ∀ᶠ y in 𝓝 x, MDiffAt (T% Z) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hZ).mono fun y hy ↦
      hy.mdifferentiableAt (by simp)
  exact hasDerivAt_curvatureOperator_of_hasDerivAt_difference (Eventually.of_forall hC)
    (congrFun (hcov t).torsion x) (hX.mdifferentiableAt (by simp))
    (hY.mdifferentiableAt (by simp)) hZ'
    (g.contMDiffAt_covariantDerivative_apply_of_isLeviCivitaConnection hc hcov hX hZ)
    (g.contMDiffAt_covariantDerivative_apply_of_isLeviCivitaConnection hc hcov hY hZ)

end TauCeti.Manifold.ContMDiffNondegenerateMetricFamily
