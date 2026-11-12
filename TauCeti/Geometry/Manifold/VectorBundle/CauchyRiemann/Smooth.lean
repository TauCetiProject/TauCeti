/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.Notation

/-!
# Smoothness of the zeroth-order terms of real Cauchy–Riemann operators

If two real Cauchy–Riemann operators send smooth sections to smooth `V`-valued one-forms, then
their difference, the zeroth-order term `IsRealCauchyRiemannOperator.difference`, is a smooth
section of the bundle `Hom(V, Hom(TM, V))`, and so is the antilinear part
`IsRealCauchyRiemannOperator.antilinearPart` of such an operator. This is the smoothness of the
zeroth-order term in McDuff–Salamon's statement that two smooth real Cauchy–Riemann operators differ
by a smooth section of `Λ^{0,1} ⊗ End_ℝ V`. The smoothness of an operator is phrased with Mathlib's
`ContMDiffCovariantDerivativeOn`, which only asks that the operator sends `C^(n + 1)` sections over
a set to `C^n` sections of `Hom(TM, V)` there.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.contMDiffOn_difference` and
  `TauCeti.IsRealCauchyRiemannOperator.contMDiffOn_antilinearPart`: smoothness of the zeroth-order
  terms of smooth real Cauchy–Riemann operators.
* `TauCeti.contMDiffCovariantDerivativeOn_sectionComplexLinearPart`: the complex linear part of a
  smooth operator is smooth.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, Definition C.1.5 and Exercise C.1.7.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {j : SmoothAlmostComplexStructure I M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  {D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}

open SmoothAlmostComplexStructure

variable [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]

variable [FiniteDimensional ℝ E] [T2Space M] {u : Set M} {n : ℕ∞ω}

omit [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] in
/-- If two real Cauchy–Riemann operators send `C^(n + 1)` sections over `u` to `C^n` sections of
`Hom(TM, V)` over `u`, then their difference is a `C^n` section over `u` of the bundle
`Hom(V, Hom(TM, V))`: the zeroth-order term by which two smooth real Cauchy–Riemann operators
differ is smooth. -/
theorem IsRealCauchyRiemannOperator.contMDiffOn_difference [VectorBundle ℝ F V]
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] {D' : (Π x : M, V x) → Π x : M,
      TangentSpace I x →L[ℝ] V x}
    (hD : IsRealCauchyRiemannOperator F j D) (hD' : IsRealCauchyRiemannOperator F j D')
    (hn : n + 1 ≤ ∞) (hDs : ContMDiffCovariantDerivativeOn F n D u)
    (hD's : ContMDiffCovariantDerivativeOn F n D' u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] E →L[ℝ] F)
        (E := fun x ↦ V x →L[ℝ] TangentSpace I x →L[ℝ] V x) y (hD.difference hD' y)) u := by
  have : ContMDiffVectorBundle n F V I := .of_le (le_self_add.trans hn)
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    .of_le (le_self_add.trans hn)
  refine Manifold.contMDiffOn_hom_of_forall_contMDiff (le_self_add.trans hn) fun τ hτ ↦ ?_
  have hτu : CMDiff[u] (n + 1) (T% τ) := (hτ.of_le hn).contMDiffOn
  refine ((hDs.contMDiff hτu).sub_section (hD's.contMDiff hτu)).congr fun y _ ↦ ?_
  rw [hD.difference_apply hD' ((hτ y).mdifferentiableAt (by simp)), Pi.sub_apply]

/-- The complex linear part `D^ℂ ξ = ½ (D ξ - i • D (i • ξ))` of an operator sending `C^(n + 1)`
sections over `u` to `C^n` sections of `Hom(TM, V)` over `u` does the same. -/
theorem contMDiffCovariantDerivativeOn_sectionComplexLinearPart (hn : n + 1 ≤ ∞)
    [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
    [ContMDiffVectorBundle ∞ F V I] (hDs : ContMDiffCovariantDerivativeOn F n D u) :
    ContMDiffCovariantDerivativeOn F n (sectionComplexLinearPart D) u where
  contMDiff {σ} hσ := by
    have : ContMDiffVectorBundle n F V I := .of_le (le_self_add.trans hn)
    have hIσ : CMDiff[u] (n + 1) (T% (Complex.I • σ)) :=
      ContMDiffOn.smul_totalSpace (a := fun _ ↦ Complex.I) contMDiffOn_const hσ
    have h := ((hDs.contMDiff hσ).sub_section (Manifold.contMDiffOn_hom_const_smul
      (le_self_add.trans hn) Complex.I (hDs.contMDiff hIσ))).const_smul_section (a := (2⁻¹ : ℝ))
    exact h.congr fun y _ ↦ by
      simp only [sectionComplexLinearPart_apply, Pi.smul_apply, Pi.sub_apply]

/-- The antilinear part of a real Cauchy–Riemann operator sending `C^(n + 1)` sections over `u`
to `C^n` sections of `Hom(TM, V)` over `u` is a `C^n` section over `u` of the bundle
`Hom(V, Hom(TM, V))`. -/
theorem IsRealCauchyRiemannOperator.contMDiffOn_antilinearPart [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [VectorBundle ℝ F V] [VectorBundle ℂ F V] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle ∞ F V I] (hD : IsRealCauchyRiemannOperator F j D)
    (hn : n + 1 ≤ ∞) (hDs : ContMDiffCovariantDerivativeOn F n D u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] E →L[ℝ] F)
        (E := fun x ↦ V x →L[ℝ] TangentSpace I x →L[ℝ] V x) y (hD.antilinearPart y)) u := by
  rw [antilinearPart_eq_difference]
  exact hD.contMDiffOn_difference hD.isRealCauchyRiemannOperator_sectionComplexLinearPart hn hDs
    (contMDiffCovariantDerivativeOn_sectionComplexLinearPart hn hDs)

end TauCeti
