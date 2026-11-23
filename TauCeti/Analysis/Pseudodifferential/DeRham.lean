/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.DeRhamSymbol
public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential

/-!
# The exterior derivative on `ℝⁿ` as a classical symbol

On the coordinate space `ℝⁿ`, write complex-valued `k`-forms as functions with values in the
complexified exterior power `(⋀ᵏ ℝⁿ)_ℂ`. The exterior derivative is then the first-order
differential operator `d u = ∑ⱼ eⱼ ∧ ∂ⱼ u` with constant coefficients. This file realizes it as a
classical symbol of order `1` (`TauCeti.ClassicalSymbol.extDeriv`):

* its quantization is `u ↦ ∑ⱼ eⱼ ∧ ∂ⱼ u` on Schwartz input, with no smoothing remainder
  (`TauCeti.ClassicalSymbol.quantizeSchwartzValue_extDeriv`);
* its principal symbol is the de Rham symbol `σ(d)(x, ξ) = i (ξ ∧ ·)`,
  `TauCeti.HomogeneousSymbol.extDeriv` (`TauCeti.ClassicalSymbol.principal_extDeriv`), so the
  exactness and ellipticity results of `TauCeti.Analysis.Pseudodifferential.DeRhamSymbol` are
  statements about this operator.

It is an instance of the classical symbol `TauCeti.ClassicalSymbol.ofLinear L` of a first-order
operator `u ↦ -i ∑ⱼ L(eⱼ) ∂ⱼ u` with constant coefficients, whose full and principal symbol is
`L ξ`.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §7, pp. 520–522.
-/

public section

noncomputable section

open scoped LineDeriv SchwartzMap

namespace TauCeti

namespace ClassicalSymbol

variable {n : ℕ}

/-- The symbol `ξ ↦ i (ξ ∧ ·)` of the exterior derivative, as a real-linear function of the
covector. -/
private def extDerivLinear (k : ℕ) :
    CoordinateSpace n →L[ℝ] (WithLp 2 (Complexification (⋀[ℝ]^k (CoordinateSpace n))) →L[ℂ]
      WithLp 2 (Complexification (⋀[ℝ]^(k + 1) (CoordinateSpace n)))) :=
  Complex.I • ((ContinuousLinearMap.complexifyL2ₗᵢ _ _).toContinuousLinearMap ∘L
    LinearMap.toContinuousLinearMap
      (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
        ExteriorAlgebra.wedgeLeftₗ ℝ (CoordinateSpace n) k))

private theorem extDerivLinear_apply (k : ℕ) (ξ : CoordinateSpace n) :
    extDerivLinear k ξ =
      Complex.I • (ExteriorAlgebra.wedgeLeft ξ k).toContinuousLinearMap.complexifyL2 := by
  simp [extDerivLinear]

variable (n) in
/-- **The exterior derivative** on `k`-forms on `ℝⁿ`, acting on functions with values in complex
`k`-forms: the classical symbol of order `1` of `d u = ∑ⱼ eⱼ ∧ ∂ⱼ u`
(`TauCeti.ClassicalSymbol.quantizeSchwartzValue_extDeriv`), with principal symbol
`HomogeneousSymbol.extDeriv` (`TauCeti.ClassicalSymbol.principal_extDeriv`). -/
def extDeriv (k : ℕ) :
    ClassicalSymbol n (WithLp 2 (Complexification (⋀[ℝ]^k (CoordinateSpace n))))
      (WithLp 2 (Complexification (⋀[ℝ]^(k + 1) (CoordinateSpace n)))) 1 :=
  ofLinear (extDerivLinear k)

/-- The principal symbol of the exterior derivative is the de Rham symbol `i (ξ ∧ ·)`. -/
@[simp]
theorem principal_extDeriv (k : ℕ) :
    (extDeriv n k).principal = HomogeneousSymbol.extDeriv _ _ k := by
  rw [extDeriv, principal_ofLinear]
  ext1
  funext p
  rw [HomogeneousSymbol.coefficient_ofLinear, HomogeneousSymbol.coefficient_extDeriv,
    extDerivLinear_apply]

/-- The full symbol of the exterior derivative is `i (ξ ∧ ·)` at every point. -/
@[simp]
theorem coefficient_toSymbol_extDeriv (k : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (extDeriv n k).toSymbol.coefficient p =
      Complex.I • (ExteriorAlgebra.wedgeLeft p.2 k).toContinuousLinearMap.complexifyL2 := by
  rw [extDeriv, coefficient_toSymbol_ofLinear, extDerivLinear_apply]

/-- **The exterior derivative is a pseudodifferential operator**: on Schwartz input the
quantization of `ClassicalSymbol.extDeriv n k` is `u ↦ ∑ⱼ eⱼ ∧ ∂ⱼ u`, with no smoothing
remainder. -/
theorem quantizeSchwartzValue_extDeriv (k : ℕ)
    (u : 𝓢(CoordinateSpace n, WithLp 2 (Complexification (⋀[ℝ]^k (CoordinateSpace n)))))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (extDeriv n k).toSymbol.coefficient u x =
      ∑ j, (ExteriorAlgebra.wedgeLeft (EuclideanSpace.single j 1 : CoordinateSpace n)
        k).toContinuousLinearMap.complexifyL2
          (∂_{(EuclideanSpace.single j 1 : CoordinateSpace n)} u x) := by
  rw [extDeriv, quantizeSchwartzValue_ofLinear, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [extDerivLinear_apply, smul_apply, smul_smul]
  simp

end ClassicalSymbol

end TauCeti
