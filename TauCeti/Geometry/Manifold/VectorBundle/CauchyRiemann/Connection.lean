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

* `TauCeti.SmoothAlmostComplexStructure.zeroOnePart`: the `(0,1)`-part of a `V`-valued one-form,
  its complex antilinear part (`TauCeti.SmoothAlmostComplexStructure.toLinearMap_zeroOnePart`).
* `IsCovariantDerivativeOn.isRealCauchyRiemannOperator_zeroOnePart`: the `(0,1)`-part of a
  covariant derivative is a real Cauchy–Riemann operator.
* `IsCovariantDerivativeOn.isComplexLinearOperator_zeroOnePart`: it is complex linear for a
  complex connection.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1.
-/

@[expose] public section

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

namespace SmoothAlmostComplexStructure

/-- The `(0,1)`-part `η^{0,1} v = ½ (η v + i • η (j v))` of a `V`-valued one-form `η`. -/
def zeroOnePart {x : M} (η : TangentSpace I x →L[ℝ] V x) : TangentSpace I x →L[ℝ] V x :=
  (2⁻¹ : ℝ) • (η + Complex.I • η.comp (j.toEndomorphism x))

variable {j}

theorem zeroOnePart_apply {x : M} (η : TangentSpace I x →L[ℝ] V x) (v : TangentSpace I x) :
    j.zeroOnePart η v = (2⁻¹ : ℝ) • (η v + Complex.I • η (j x v)) :=
  rfl

/-- The `(0,1)`-part of a one-form is its complex antilinear part
`TauCeti.complexAntilinearPart` for `j` and multiplication by `i`. -/
theorem toLinearMap_zeroOnePart {x : M} (η : TangentSpace I x →L[ℝ] V x) :
    (j.zeroOnePart η).toLinearMap = complexAntilinearPart (j.toEndomorphism x).toLinearMap
      (DistribSMul.toLinearMap ℝ (V x) Complex.I) η.toLinearMap := by
  ext v
  simp [zeroOnePart_apply, complexAntilinearPart_apply]

/-- The `(0,1)`-part of a one-form is a `(0,1)`-form. -/
theorem isZeroOneForm_zeroOnePart {x : M} (η : TangentSpace I x →L[ℝ] V x) :
    j.IsZeroOneForm (j.zeroOnePart η) := by
  intro v
  simp only [zeroOnePart_apply, apply_apply, map_neg, smul_add, smul_neg,
    smul_comm Complex.I (2⁻¹ : ℝ), smul_smul Complex.I Complex.I, Complex.I_mul_I, neg_one_smul]
  abel

/-- The `(0,1)`-part of `dg ⊗ ξ` is `(∂bar g) ⊗ ξ`. -/
theorem zeroOnePart_smulRight (g : M → ℝ) (σ : Π x : M, V x) (x : M) :
    j.zeroOnePart ((d% g x).smulRight (σ x)) = j.dbarSMulRight g σ x := by
  ext v
  simp only [zeroOnePart_apply, dbarSMulRight_apply, ContinuousLinearMap.smulRight_apply,
    smul_comm Complex.I (_ : ℝ)]

end SmoothAlmostComplexStructure

open SmoothAlmostComplexStructure

/-- The `(0,1)`-part `(∇ξ)^{0,1}` of a covariant derivative is a real Cauchy–Riemann operator. -/
theorem _root_.IsCovariantDerivativeOn.isRealCauchyRiemannOperator_zeroOnePart
    {cov : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}
    (hcov : IsCovariantDerivativeOn F cov) :
    IsRealCauchyRiemannOperator F j fun σ x ↦ j.zeroOnePart (cov σ x) where
  isZeroOneForm σ x := isZeroOneForm_zeroOnePart (cov σ x)
  add hσ hσ' := by
    rw [hcov.add hσ hσ']
    ext v
    simp only [zeroOnePart_apply, add_apply, smul_add]
    abel
  leibniz {σ g x} hσ hg := by
    rw [hcov.leibniz hσ hg, ← zeroOnePart_smulRight]
    ext v
    simp only [zeroOnePart_apply, add_apply, smul_apply,
      smul_add, smul_comm Complex.I (g x), smul_comm (2⁻¹ : ℝ) (g x)]
    abel

/-- The `(0,1)`-part of a complex covariant derivative, one which commutes with multiplication by
`i`, is a complex linear real Cauchy–Riemann operator. -/
theorem _root_.IsCovariantDerivativeOn.isComplexLinearOperator_zeroOnePart
    {cov : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}
    (hI : ∀ ⦃σ : Π x : M, V x⦄ ⦃x : M⦄, MDiffAt (T% σ) x →
      cov (Complex.I • σ) x = Complex.I • cov σ x) :
    IsComplexLinearOperator F fun σ x ↦ j.zeroOnePart (cov σ x) := by
  intro σ x hσ
  dsimp only
  rw [hI hσ]
  ext v
  simp only [zeroOnePart_apply, smul_apply, smul_add,
    smul_comm Complex.I (2⁻¹ : ℝ)]

end TauCeti
