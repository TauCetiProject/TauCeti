/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.CurlSymbol
public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The curl in dimension three as a classical symbol

The principal symbol of the curl `curl = ⋆ d` on `1`-forms of an oriented three-dimensional space
is `σ(curl)(x, ξ) = i ⋆ (ξ ∧ ·)`, the symbol `i ξ × ·` (`TauCeti.HomogeneousSymbol.curl`). This file
adds two facts about it.

* `TauCeti.HomogeneousSymbol.adjoint_curl_comp_curl`: `σ(curl)† σ(curl) = σ(d)† σ(d)` on
  `1`-forms, since the Hodge star `⋀² E → ⋀¹ E` is an isometry.
* On the coordinate space `ℝⁿ` with `n = 3`, the curl is the first-order differential operator
  `curl u = ∑ⱼ ⋆ (eⱼ ∧ ∂ⱼ u)` on `(⋀¹ ℝⁿ)_ℂ`-valued functions. It is a classical symbol of order `1`
  (`TauCeti.ClassicalSymbol.curl`) whose quantization is this differential operator on Schwartz
  input (`TauCeti.ClassicalSymbol.quantizeSchwartzValue_curl`), with no smoothing remainder, and
  whose principal symbol is `TauCeti.HomogeneousSymbol.curl`
  (`TauCeti.ClassicalSymbol.principal_curl`); in particular it is not elliptic
  (`TauCeti.ClassicalSymbol.not_isElliptic_curl`). It is an instance of the classical symbol
  `TauCeti.ClassicalSymbol.ofLinear L` of a first-order operator `u ↦ -i ∑ⱼ L(eⱼ) ∂ⱼ u` with
  constant coefficients, whose full and principal symbol is `L ξ`.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §7, pp. 520–522 (symbol sequences of complexes of differential operators).
* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1 (the Hodge star).
-/

public section

noncomputable section

open Module
open scoped ContDiff RealInnerProductSpace LineDeriv SchwartzMap

namespace TauCeti

namespace HomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 3)]
  (o : Orientation ℝ E (Fin 3))

/-- **`curl* curl = d* d` on `1`-forms**: since the Hodge star is an isometry, the symbol of the
curl has the same square as the symbol of the exterior derivative on `1`-forms. -/
theorem adjoint_curl_comp_curl :
    (curl X E o).adjoint.comp (curl X E o) = (extDeriv X E 1).adjoint.comp (extDeriv X E 1) := by
  have h : 1 + 1 + 1 = finrank ℝ E := (Fact.out : finrank ℝ E = 3).symm
  -- The complexified star `S` satisfies `S† S = 1`.
  have hS : ContinuousLinearMap.adjoint
      (LinearMap.toContinuousLinearMap (o.hodgeStar h).toLinearMap).complexifyL2 ∘L
        (LinearMap.toContinuousLinearMap (o.hodgeStar h).toLinearMap).complexifyL2 =
      ContinuousLinearMap.id ℂ _ := by
    rw [ContinuousLinearMap.adjoint_complexifyL2, ← ContinuousLinearMap.complexifyL2_comp,
      o.adjoint_hodgeStar_comp_hodgeStar h, ContinuousLinearMap.one_def,
      ContinuousLinearMap.complexifyL2_id]
  ext1
  funext p
  simp only [coefficient_comp, coefficient_adjoint, coefficient_curl_eq_comp_extDeriv,
    ContinuousLinearMap.adjoint_comp]
  rw [ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc _ _ ((extDeriv X E 1).coefficient p), hS,
    ContinuousLinearMap.id_comp]

end HomogeneousSymbol

namespace ClassicalSymbol

/-! ### The curl on `ℝ³` -/

variable {n : ℕ} [Fact (finrank ℝ (CoordinateSpace n) = 3)]
  (o : Orientation ℝ (CoordinateSpace n) (Fin 3))

/-- The symbol `ξ ↦ i ⋆ (ξ ∧ ·)` of the curl, as a real-linear function of the covector. -/
private def curlLinear :
    CoordinateSpace n →L[ℝ] (WithLp 2 (Complexification (⋀[ℝ]^1 (CoordinateSpace n))) →L[ℂ]
      WithLp 2 (Complexification (⋀[ℝ]^1 (CoordinateSpace n)))) :=
  Complex.I • ((ContinuousLinearMap.complexifyL2ₗᵢ _ _).toContinuousLinearMap ∘L
    LinearMap.toContinuousLinearMap
      (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
        LinearMap.llcomp ℝ _ _ _
          (o.hodgeStar (k := 1 + 1) (l := 1)
            (Fact.out : finrank ℝ (CoordinateSpace n) = 3).symm).toLinearMap ∘ₗ
          ExteriorAlgebra.wedgeLeftₗ ℝ (CoordinateSpace n) 1))

private theorem curlLinear_apply (ξ : CoordinateSpace n) :
    curlLinear o ξ = Complex.I • (LinearMap.toContinuousLinearMap
      ((o.hodgeStar (k := 1 + 1) (l := 1)
          (Fact.out : finrank ℝ (CoordinateSpace n) = 3).symm).toLinearMap ∘ₗ
        ExteriorAlgebra.wedgeLeft ξ 1)).complexifyL2 := by
  simp [curlLinear, LinearMap.llcomp_apply']

/-- **The curl** on the oriented three-dimensional coordinate space, acting on functions with values
in complex `1`-forms: the classical symbol of order `1` of `curl u = ∑ⱼ ⋆ (eⱼ ∧ ∂ⱼ u)`
(`TauCeti.ClassicalSymbol.quantizeSchwartzValue_curl`), with principal symbol
`HomogeneousSymbol.curl` (`TauCeti.ClassicalSymbol.principal_curl`). -/
def curl : ClassicalSymbol n (WithLp 2 (Complexification (⋀[ℝ]^1 (CoordinateSpace n))))
    (WithLp 2 (Complexification (⋀[ℝ]^1 (CoordinateSpace n)))) 1 :=
  ofLinear (curlLinear o)

/-- The principal symbol of the curl is `i ⋆ (ξ ∧ ·)`, the symbol `i ξ × ·`. -/
@[simp]
theorem principal_curl : (curl o).principal = HomogeneousSymbol.curl _ _ o := by
  rw [curl, principal_ofLinear]
  ext1
  funext p
  rw [HomogeneousSymbol.coefficient_ofLinear, HomogeneousSymbol.coefficient_curl,
    curlLinear_apply]

/-- The full symbol of the curl is `i ⋆ (ξ ∧ ·)`, the symbol `i ξ × ·`, at every point. -/
@[simp]
theorem coefficient_toSymbol_curl (p : CoordinateSpace n × CoordinateSpace n) :
    (curl o).toSymbol.coefficient p = Complex.I • (LinearMap.toContinuousLinearMap
      ((o.hodgeStar (k := 1 + 1) (l := 1)
          (Fact.out : finrank ℝ (CoordinateSpace n) = 3).symm).toLinearMap ∘ₗ
        ExteriorAlgebra.wedgeLeft p.2 1)).complexifyL2 := by
  rw [curl, coefficient_toSymbol_ofLinear, curlLinear_apply o]

/-- **The curl is a pseudodifferential operator**: on Schwartz input the quantization of
`ClassicalSymbol.curl` is the curl `u ↦ ∑ⱼ ⋆ (eⱼ ∧ ∂ⱼ u)`, with no smoothing remainder. -/
theorem quantizeSchwartzValue_curl
    (u : 𝓢(CoordinateSpace n, WithLp 2 (Complexification (⋀[ℝ]^1 (CoordinateSpace n)))))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (curl o).toSymbol.coefficient u x =
      ∑ j, (LinearMap.toContinuousLinearMap
        ((o.hodgeStar (k := 1 + 1) (l := 1)
            (Fact.out : finrank ℝ (CoordinateSpace n) = 3).symm).toLinearMap ∘ₗ
          ExteriorAlgebra.wedgeLeft (EuclideanSpace.single j 1 : CoordinateSpace n) 1)).complexifyL2
            (∂_{(EuclideanSpace.single j 1 : CoordinateSpace n)} u x) := by
  rw [curl, quantizeSchwartzValue_ofLinear, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [curlLinear_apply o, smul_apply, smul_smul]
  simp

/-- **The curl is not elliptic.** -/
theorem not_isElliptic_curl : ¬ (curl o).IsElliptic := by
  rw [isElliptic_def, principal_curl]
  exact HomogeneousSymbol.not_isElliptic_curl o

end ClassicalSymbol

end TauCeti
