/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import TauCeti.Analysis.InnerProductSpace.Trace.Free

/-!
# Change of variables in non-divergence-form equations

Let `Φ` be a change of variables of order two from an open set `U` into an open set `V`
(`TauCeti.Wkp.IsChangeOfVariables`), with derivative `M(x) = DΦ(x)` and second derivative
`D²Φ(x)`, and let `N(x)` be a right inverse of `M(x)`. A strong solution `u ∈ W^{2,p}(V)` of the
non-divergence-form equation

`tr (A ∘ D²u) + ⟪b, ∇u⟫ + γ u = f` almost everywhere in `V`

becomes, after the change of variables `w = u ∘ Φ`, a strong solution of an equation of the same
form in `U` (`TauCeti.PDE.ae_traceCLM_comp_iteratedGradient_compL_add_inner_add_mul_eq`),

`tr (A' ∘ D²w) + ⟪b', ∇w⟫ + γ' w = f'` almost everywhere in `U`,

with the transformed coefficients

* `A'(x) = N(x) A(Φ x) N(x)†`,
* `b'(x) = N(x) (b(Φ x) - ∑ᵢ D²Φ(x) eᵢ (A'(x)† eᵢ))` for an orthonormal basis `(eᵢ)`,
* `γ'(x) = γ(Φ x)` and `f'(x) = f(Φ x)`.

Unlike the divergence form, where the volume element and the test functions absorb the change of
variables, the second derivatives of `Φ` enter here: they produce the first-order correction in
`b'`. This is the change of variables that flattens the boundary of a domain of class `C²` in the
`W^{2,p}` theory of non-divergence-form equations: a strong solution near a curved boundary
portion becomes a strong solution of an equation of the same form near a flat one, where the
estimates up to a flat boundary apply.

## The argument

The weak Hessian of `w` is `D²w(x) = M(x)† ∘ D²u(Φ x) ∘ M(x) + H(x)` with
`H(x) f = (D²Φ(x) f)† ∇u(Φ x)` (`TauCeti.Wkp.iteratedGradient_compL_ae`), and its weak gradient
is `M(x)† ∇u(Φ x)` (`TauCeti.Wkp.iteratedGradient_lowerOrder_compL_ae`). Since `M N = 1`, the
trace is cyclic and `N† M† = 1`, the first part contributes
`tr (A' ∘ M† ∘ D²u(Φ x) ∘ M) = tr (A(Φ x) ∘ D²u(Φ x))`, while `tr (A' ∘ H)` is the first-order term
`⟪∑ᵢ D²Φ(x) eᵢ (A'† eᵢ), ∇u(Φ x)⟫`, and `⟪N z, ∇w⟫ = ⟪z, ∇u(Φ x)⟫`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §6.2 and the proof of Theorem 9.13 (straightening the boundary transforms the equation into one
  of the same form).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2 (flattening the boundary).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace

namespace TauCeti.PDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {U V : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {Φ : E → E} {L c : ℝ}

/-- **Change of variables in a non-divergence-form equation.** Let `Φ` be a change of variables
of order two from `U` into `V`, let `N(x)` be a right inverse of `DΦ(x)` for `x ∈ U`, and let
`1 ≤ p < ∞`. If `u ∈ W^{2,p}(V)` is a strong solution of
`tr (A ∘ D²u) + ⟪b, ∇u⟫ + γ u = f` almost everywhere in `V`, then `w = u ∘ Φ`
(`TauCeti.Wkp.compL`) is a strong solution of

`tr (A' ∘ D²w) + ⟪b', ∇w⟫ + γ(Φ x) w = f(Φ x)` almost everywhere in `U`,

where `A'(x) = N(x) A(Φ x) N(x)†` and, for any orthonormal basis `(eᵢ)` of `E`,
`b'(x) = N(x) (b(Φ x) - ∑ᵢ D²Φ(x) eᵢ (N(x) A(Φ x)† N(x)† eᵢ))`; note `A'(x)† = N(x) A(Φ x)† N(x)†`.
Here `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u` and `∇u` the weak gradient. -/
theorem ae_traceCLM_comp_iteratedGradient_compL_add_inner_add_mul_eq
    (h : Wkp.IsChangeOfVariables 2 U V Φ L c) (hp : p ≠ ⊤) {N : E → E →L[ℝ] E}
    (hN : ∀ x ∈ (U : Set E), fderiv ℝ Φ x ∘L N x = ContinuousLinearMap.id ℝ E)
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E)
    {A : E → E →L[ℝ] E} {b : E → E} {γ f : E → ℝ} {u : Wkp mu V p 2}
    (hu : ∀ᵐ y ∂mu.restrict V, traceCLM ℝ E (A y ∘L Wkp.iteratedGradient 1 u y) +
      ⟪b y, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) y⟫_ℝ + γ y * Wkp.value 2 u y = f y) :
    ∀ᵐ x ∂mu.restrict U,
      traceCLM ℝ E ((N x ∘L A (Φ x) ∘L (N x).adjoint) ∘L
          Wkp.iteratedGradient 1 (Wkp.compL h hp u) x) +
        ⟪N x (b (Φ x) - ∑ i, fderiv ℝ (fderiv ℝ Φ) x (e i)
            (N x ((A (Φ x)).adjoint ((N x).adjoint (e i))))),
          Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 (Wkp.compL h hp u)) x⟫_ℝ +
        γ (Φ x) * Wkp.value 2 (Wkp.compL h hp u) x = f (Φ x) := by
  filter_upwards [h.ae_comp hu, Wkp.iteratedGradient_compL_ae h hp u,
    Wkp.iteratedGradient_lowerOrder_compL_ae h hp u, Wkp.value_compL_ae h hp u,
    ae_restrict_mem U.isOpen.measurableSet] with x hux hD hg hv hx
  set M := fderiv ℝ Φ x
  set g := Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) (Φ x)
  set A' := N x ∘L A (Φ x) ∘L (N x).adjoint with hA'def
  have hMN := hN x hx
  have hA' : ∀ z, A'.adjoint z = N x ((A (Φ x)).adjoint ((N x).adjoint z)) := fun z => by
    simp [A', ContinuousLinearMap.adjoint_comp]
  -- The trace of `A' ∘ D²w`, computed on the basis `e`.
  have htr : traceCLM ℝ E (A' ∘L Wkp.iteratedGradient 1 (Wkp.compL h hp u) x) =
      traceCLM ℝ E (A (Φ x) ∘L Wkp.iteratedGradient 1 u (Φ x)) +
        ⟪∑ i, fderiv ℝ (fderiv ℝ Φ) x (e i) (A'.adjoint (e i)), g⟫_ℝ := by
    have hH (f : E) : (Wkp.iteratedGradient 1 (Wkp.compL h hp u) x -
        M.adjoint ∘L Wkp.iteratedGradient 1 u (Φ x) ∘L M) f =
          (fderiv ℝ (fderiv ℝ Φ) x f).adjoint g := by
      rw [sub_apply, hD f, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_apply, add_sub_cancel_left]
    rw [← sub_add_cancel (Wkp.iteratedGradient 1 (Wkp.compL h hp u) x)
        (M.adjoint ∘L Wkp.iteratedGradient 1 u (Φ x) ∘L M), ContinuousLinearMap.comp_add,
      map_add, hA'def, ContinuousLinearMap.traceCLM_comp_adjoint_comp_comp_of_comp_eq_id hMN,
      ContinuousLinearMap.traceCLM_comp_eq_sum_inner _ e _ g hH, add_comm]
  -- The drift: `⟪N z, M† g⟫ = ⟪z, g⟫` since `M N = 1`.
  have hdrift (z : E) : ⟪N x z, M.adjoint g⟫_ℝ = ⟪z, g⟫_ℝ := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    simpa using congrArg (fun z' => ⟪z', g⟫_ℝ) (congrArg (fun T => T z) hMN)
  rw [htr, hg, hv, hdrift, ← hux]
  simp only [hA', inner_sub_left]
  ring

end TauCeti.PDE
