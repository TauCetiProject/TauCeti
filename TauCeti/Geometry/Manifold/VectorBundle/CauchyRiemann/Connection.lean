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

* `IsCovariantDerivativeOn.zeroOnePart_add` and `IsCovariantDerivativeOn.zeroOnePart_leibniz`:
  the Cauchy–Riemann axioms for the `(0,1)`-part at each point of a set over which `cov` is a
  covariant derivative.
* `IsCovariantDerivativeOn.isRealCauchyRiemannOperator_zeroOnePart`: the `(0,1)`-part of a
  covariant derivative is a real Cauchy–Riemann operator.
* `IsCovariantDerivativeOn.isComplexLinearOperator_zeroOnePart`: it is complex linear for a
  complex connection.
* `TauCeti.IsRealCauchyRiemannOperator.tensorialAt_sub_zeroOnePart`: a real Cauchy–Riemann
  operator differs from the `(0,1)`-part of a covariant derivative over a set by a tensorial term
  at each point of that set.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1.
-/

public section

open Bundle Set
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

/-- At a point of a set over which `cov` is a covariant derivative, the `(0,1)`-part of `cov` is
additive on sections differentiable at that point. -/
theorem _root_.IsCovariantDerivativeOn.zeroOnePart_add
    {cov : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x} {s : Set M}
    (hcov : IsCovariantDerivativeOn F cov s) {σ σ' : Π x : M, V x} {x : M} (hx : x ∈ s)
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) :
    j.zeroOnePart (cov (σ + σ') x) = j.zeroOnePart (cov σ x) + j.zeroOnePart (cov σ' x) := by
  rw [hcov.add hσ hσ' hx, SmoothAlmostComplexStructure.zeroOnePart_add]

/-- At a point of a set over which `cov` is a covariant derivative, the `(0,1)`-part of `cov`
satisfies the Leibniz rule `D (g • ξ) = g • D ξ + (∂bar g) ⊗ ξ`. -/
theorem _root_.IsCovariantDerivativeOn.zeroOnePart_leibniz
    {cov : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x} {s : Set M}
    (hcov : IsCovariantDerivativeOn F cov s) {σ : Π x : M, V x} {g : M → ℝ} {x : M} (hx : x ∈ s)
    (hσ : MDiffAt (T% σ) x) (hg : MDiffAt g x) :
    j.zeroOnePart (cov (g • σ) x) = g x • j.zeroOnePart (cov σ x) + j.dbarSMulRight g σ x := by
  rw [hcov.leibniz hσ hg hx, SmoothAlmostComplexStructure.zeroOnePart_add, zeroOnePart_smul,
    zeroOnePart_smulRight]

/-- The `(0,1)`-part `(∇ξ)^{0,1}` of a covariant derivative is a real Cauchy–Riemann operator. -/
theorem _root_.IsCovariantDerivativeOn.isRealCauchyRiemannOperator_zeroOnePart
    {cov : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}
    (hcov : IsCovariantDerivativeOn F cov) :
    IsRealCauchyRiemannOperator F j fun σ x ↦ j.zeroOnePart (cov σ x) where
  isZeroOneForm σ x := isZeroOneForm_zeroOnePart (cov σ x)
  add hσ hσ' := hcov.zeroOnePart_add j (mem_univ _) hσ hσ'
  leibniz hσ hg := hcov.zeroOnePart_leibniz j (mem_univ _) hσ hg

variable {j} in
/-- At a point of a set over which `cov` is a covariant derivative, a real Cauchy–Riemann operator
differs from the `(0,1)`-part of `cov` by a tensorial term. -/
theorem IsRealCauchyRiemannOperator.tensorialAt_sub_zeroOnePart
    {D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}
    (hD : IsRealCauchyRiemannOperator F j D)
    {cov : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x} {s : Set M}
    (hcov : IsCovariantDerivativeOn F cov s) {x : M} (hx : x ∈ s) :
    TensorialAt I F (fun σ ↦ D σ x - j.zeroOnePart (cov σ x)) x where
  smul hg hσ := by
    simp only [hD.leibniz hσ hg, hcov.zeroOnePart_leibniz j hx hσ hg, smul_sub]
    abel
  add hσ hσ' := by
    simp only [hD.add hσ hσ', hcov.zeroOnePart_add j hx hσ hσ']
    abel

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
