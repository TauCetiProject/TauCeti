/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Non-divergence-form equations under a change of variables

Let `Φ` be a change of variables of order two from an open set `U` onto an open set `V`, with
inverse `Ψ`, also of order two, and let `u ∈ W^{2,p}(V)`, `1 ≤ p < ∞`, be a strong solution of the
non-divergence-form equation

`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f` almost everywhere on `V`.

This file shows that `v = u ∘ Φ ∈ W^{2,p}(U)` is a strong solution of an equation of the same form
on `U` (`TauCeti.PDE.ae_traceCLM_comp_iteratedGradient_compL_add_inner_add_mul_eq`):

`tr (A' ∘ D²v) + ⟪b', ∇v⟫ + (c ∘ Φ) v = f ∘ Φ`,

with, at `x ∈ U`, `y = Φ x` and `M = DΨ(y)`,

* `A'(x) = M ∘ A(y) ∘ M†`, where `M†` is the adjoint of `M`;
* `b'(x) = M b(y) + ∑ᵢ D²Ψ(y) eᵢ (A(y)† eᵢ)` for any orthonormal basis `(eᵢ)`.

The second-order part transforms by conjugation, as for a linear change of variables, while the
curvature of `Ψ` contributes the first-order term `∑ᵢ D²Ψ(y) eᵢ (A(y)† eᵢ)`. Flattening the
boundary of a domain of class `C²` by such a change of variables turns an equation near a curved
boundary portion into one near a flat boundary portion, where the half-space estimates apply.

## The argument

Since `Φ ∘ Ψ` is the identity on `V`, `u = v ∘ Ψ`, and the chain rule for the weak Hessian
(`TauCeti.Wkp.inner_iteratedGradient_compL_ae`) gives

`⟪D²u(y) f, g⟫ = ⟪D²v(Ψ y) (M f), M g⟫ + ⟪∇v(Ψ y), D²Ψ(y) f g⟫`,

with `∇u(y) = M† ∇v(Ψ y)` and `u(y) = v(Ψ y)`. Computing the trace in the basis `(eᵢ)`,
`tr (A ∘ D²u) = ∑ᵢ ⟪D²u(y) eᵢ, A† eᵢ⟫`, and the cyclicity of the trace,
`tr (A ∘ M† ∘ D²v ∘ M) = tr (M ∘ A ∘ M† ∘ D²v)`, rewrite the equation at `y` in terms of `v` at
`Ψ y`. Pulling it back along `Φ` gives the equation for `v` at almost every `x ∈ U`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2 and the proof of Theorem 9.13 (flattening the boundary transforms the operator into
  one of the same form).
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace

namespace TauCeti.PDE

open Wkp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The trace of `A ∘ D²u` for `D²u` given by the chain rule
`⟪D²u f, g⟫ = ⟪D (M f), M g⟫ + ⟪w, S f g⟫`: it is `tr ((M ∘ A ∘ M†) ∘ D) + ∑ᵢ ⟪S eᵢ (A† eᵢ), w⟫`
for any orthonormal basis `(eᵢ)`. -/
private theorem traceCLM_comp_eq_of_forall_inner_eq {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) {A H M D : E →L[ℝ] E} {S : E →L[ℝ] E →L[ℝ] E} {w : E}
    (hH : ∀ f g : E, ⟪H f, g⟫_ℝ = ⟪D (M f), M g⟫_ℝ + ⟪w, S f g⟫_ℝ) :
    traceCLM ℝ E (A ∘L H) =
      traceCLM ℝ E ((M ∘L A ∘L M.adjoint) ∘L D) + ∑ i, ⟪S (e i) (A.adjoint (e i)), w⟫_ℝ := by
  have hcyc : traceCLM ℝ E ((M ∘L A ∘L M.adjoint) ∘L D) =
      traceCLM ℝ E (A ∘L (M.adjoint ∘L D ∘L M)) := by
    rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.traceCLM_comp_comm]
    simp only [ContinuousLinearMap.comp_assoc]
  rw [hcyc, traceCLM_apply, traceCLM_apply, LinearMap.trace_eq_sum_inner _ e,
    LinearMap.trace_eq_sum_inner _ e, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
    ← ContinuousLinearMap.adjoint_inner_left A, ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_comm, hH, real_inner_comm (M _), real_inner_comm w]

variable [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {U V : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {Φ Ψ : E → E} {L L' c c' : ℝ}

/-- **A non-divergence-form equation under a change of variables of order two.** Let `Φ` be a
change of variables of order two from `U` into `V` with inverse `Ψ`, a change of variables of order
two from `V` into `U`, and let `1 ≤ p < ∞`. If `u ∈ W^{2,p}(V)` solves

`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c₀ u = f`

almost everywhere on `V`, then `v = u ∘ Φ ∈ W^{2,p}(U)` solves

`tr (A' ∘ D²v) + ⟪b', ∇v⟫ + (c₀ ∘ Φ) v = f ∘ Φ`

almost everywhere on `U`, where, at `x ∈ U` with `y = Φ x` and `M = DΨ(y)`, `A'(x) = M ∘ A(y) ∘ M†`
and `b'(x) = M b(y) + ∑ᵢ D²Ψ(y) eᵢ (A(y)† eᵢ)` for an orthonormal basis `(eᵢ)`. The sum does not
depend on the basis, and the coefficient fields `A`, `b`, `c₀` and the right-hand side `f` are
arbitrary functions. -/
theorem ae_traceCLM_comp_iteratedGradient_compL_add_inner_add_mul_eq {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (hΦ : IsChangeOfVariables 2 U V Φ L c)
    (hΨ : IsChangeOfVariables 2 V U Ψ L' c') (hΦΨ : RightInvOn Ψ Φ V) (hp : p ≠ ⊤)
    (u : Wkp mu V p 2) {A : E → E →L[ℝ] E} {b : E → E} {c₀ f : E → ℝ}
    (hu : ∀ᵐ y ∂mu.restrict V, traceCLM ℝ E (A y ∘L iteratedGradient 1 u y) +
      ⟪b y, iteratedGradient 0 (lowerOrder 1 u) y⟫_ℝ + c₀ y * value 2 u y = f y) :
    ∀ᵐ x ∂mu.restrict U,
      traceCLM ℝ E ((fderiv ℝ Ψ (Φ x) ∘L A (Φ x) ∘L (fderiv ℝ Ψ (Φ x)).adjoint) ∘L
          iteratedGradient 1 (compL hΦ hp u) x) +
        ⟪fderiv ℝ Ψ (Φ x) (b (Φ x)) +
            ∑ i, fderiv ℝ (fderiv ℝ Ψ) (Φ x) (e i) ((A (Φ x)).adjoint (e i)),
          iteratedGradient 0 (lowerOrder 1 (compL hΦ hp u)) x⟫_ℝ +
        c₀ (Φ x) * value 2 (compL hΦ hp u) x = f (Φ x) := by
  set v := compL hΦ hp u
  -- `u = v ∘ Ψ`, so the chain rule along `Ψ` expresses `u` and its derivatives through `v`.
  have hvu : compL hΨ hp v = u := compL_compL_of_rightInvOn hΦ hΨ hΦΨ hp u
  have hH := inner_iteratedGradient_compL_ae hΨ hp v
  have hval := value_compL_ae hΨ hp v
  have hgrad : ∀ᵐ y ∂mu.restrict V, iteratedGradient 0 (lowerOrder 1 (compL hΨ hp v)) y =
      (fderiv ℝ Ψ y).adjoint (iteratedGradient 0 (lowerOrder 1 v) (Ψ y)) := by
    filter_upwards [gradient_firstOrder_compL_ae hΨ hp v] with y hy
    rw [← gradient_firstOrder_one, hy, gradient_firstOrder_one]
  rw [hvu] at hH hval hgrad
  -- The equation for `u` at `y`, rewritten in terms of `v` at `Ψ y`.
  have hkey : ∀ᵐ y ∂mu.restrict V,
      traceCLM ℝ E ((fderiv ℝ Ψ y ∘L A y ∘L (fderiv ℝ Ψ y).adjoint) ∘L
          iteratedGradient 1 v (Ψ y)) +
        ⟪fderiv ℝ Ψ y (b y) + ∑ i, fderiv ℝ (fderiv ℝ Ψ) y (e i) ((A y).adjoint (e i)),
          iteratedGradient 0 (lowerOrder 1 v) (Ψ y)⟫_ℝ +
        c₀ y * value 2 v (Ψ y) = f y := by
    filter_upwards [hu, hH, hval, hgrad] with y hy hHy hvy hgy
    rw [traceCLM_comp_eq_of_forall_inner_eq e hHy, hgy, hvy,
      ContinuousLinearMap.adjoint_inner_right] at hy
    rw [← hy, inner_add_left, sum_inner]
    ring
  filter_upwards [hΦ.ae_comp hkey, ae_restrict_mem U.isOpen.measurableSet] with x hx hxU
  rwa [hΦ.injOn (hΨ.mapsTo (hΦ.mapsTo hxU)) hxU (hΦΨ (hΦ.mapsTo hxU))] at hx

end TauCeti.PDE
