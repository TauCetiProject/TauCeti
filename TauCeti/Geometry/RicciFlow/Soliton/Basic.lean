/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The gradient Ricci soliton equation

The native soliton equation is `Ric + Hess f = c g`. Potential regularity is supplied separately
when constructing its flow. Adding a constant to the potential leaves the equation unchanged;
a constant potential gives the Einstein equation.

## References

* P. Topping, *Lectures on the Ricci flow*, §1.2.
* The public formalizations https://github.com/frenzymath/lean-eval-submissions and
  https://github.com/frenzymath/PoincareConjecture.
-/

public section

noncomputable section

open Bundle CovariantDerivative
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The gradient Ricci soliton equation `Ric + Hess f = c g` for the ambient metric. -/
def SatisfiesGradientRicciSolitonEquation (f : M → ℝ) (c : ℝ) : Prop :=
  ∀ (x : M) (v w : TangentSpace I x),
    (leviCivitaConnection I M).ricciTensor x v w + hessian I f x v w = c * inner ℝ v w

/-- Characterize a gradient Ricci soliton by its bilinear metric equation. -/
theorem satisfiesGradientRicciSolitonEquation_iff {f : M → ℝ} {c : ℝ} :
    SatisfiesGradientRicciSolitonEquation (I := I) f c ↔ ∀ (x : M) (v w : TangentSpace I x),
      (leviCivitaConnection I M).ricciTensor x v w + hessian I f x v w = c * inner ℝ v w := by
  rfl

/-- Adding a constant to a potential does not change the soliton equation. -/
theorem satisfiesGradientRicciSolitonEquation_add_const_iff (f : M → ℝ) (a c : ℝ) :
    SatisfiesGradientRicciSolitonEquation (I := I) (fun x ↦ f x + a) c ↔
      SatisfiesGradientRicciSolitonEquation (I := I) f c := by
  have hgrad : mgradient I (fun x ↦ f x + a) = mgradient I f := by
    funext x
    rw [mgradient_def, mgradient_def, mvfderiv_add_const]
  simp only [satisfiesGradientRicciSolitonEquation_iff, hessian_def, hgrad]

/-- A constant potential gives exactly the Einstein equation for the ambient metric. -/
@[simp]
theorem satisfiesGradientRicciSolitonEquation_const_iff (a c : ℝ) :
    SatisfiesGradientRicciSolitonEquation (I := I) (fun _ : M ↦ a) c ↔
      ∀ (x : M) (v w : TangentSpace I x),
        (leviCivitaConnection I M).ricciTensor x v w = c * inner ℝ v w := by
  simp only [satisfiesGradientRicciSolitonEquation_iff, hessian_const, add_zero]

end TauCeti.Manifold
