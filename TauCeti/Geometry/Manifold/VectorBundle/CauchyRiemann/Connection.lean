/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
import Mathlib.Geometry.Manifold.Notation

/-!
# The real Cauchy–Riemann operator of a connection

Let `V` be a complex vector bundle over a manifold `M` with an almost complex structure `j`, and
let `∇` be a covariant derivative on `V` (Mathlib's `IsCovariantDerivativeOn`). Its
`(0,1)`-part `(∇ξ)^{0,1} v = ½ (∇_v ξ + i • ∇_{j v} ξ)` is a real Cauchy–Riemann operator, and it
is complex linear when `∇` commutes with multiplication by `i`
(McDuff–Salamon, Appendix C.1, after Definition C.1.5).

## Main results

* `IsCovariantDerivativeOn.isRealCauchyRiemannOperator_zeroOnePart`: the `(0,1)`-part of a
  covariant derivative is a real Cauchy–Riemann operator.
* `IsCovariantDerivativeOn.isComplexLinearOperator_zeroOnePart`: it is complex linear for a
  complex connection.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (j : SmoothAlmostComplexStructure I M)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]

open SmoothAlmostComplexStructure

/-- The `(0,1)`-part `(∇ξ)^{0,1}` of a covariant derivative is a real Cauchy–Riemann operator. -/
theorem _root_.IsCovariantDerivativeOn.isRealCauchyRiemannOperator_zeroOnePart
    {cov : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}
    (hcov : IsCovariantDerivativeOn F cov) :
    IsRealCauchyRiemannOperator F j fun σ x ↦ j.zeroOnePart (cov σ x) where
  isZeroOneForm σ x := isZeroOneForm_zeroOnePart (cov σ x)
  add hσ hσ' := by rw [hcov.add hσ hσ', zeroOnePart_add]
  leibniz hσ hg := by
    rw [hcov.leibniz hσ hg, zeroOnePart_add, zeroOnePart_smul, zeroOnePart_smulRight]

/-- The `(0,1)`-part of a complex covariant derivative, one which commutes with multiplication by
`i`, is a complex linear real Cauchy–Riemann operator. -/
theorem _root_.IsCovariantDerivativeOn.isComplexLinearOperator_zeroOnePart
    {cov : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}
    (hcov : IsCovariantDerivativeOn F cov)
    (hI : ∀ ⦃σ : Π x : M, V x⦄ ⦃x : M⦄, MDiffAt (T% σ) x →
      cov (Complex.I • σ) x = Complex.I • cov σ x) :
    IsComplexLinearOperator F fun σ x ↦ j.zeroOnePart (cov σ x) := by
  refine (hcov.isRealCauchyRiemannOperator_zeroOnePart j).isComplexLinearOperator ?_
  intro σ x hσ
  rw [hI hσ, zeroOnePart_complex_smul]

end TauCeti
