/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.LinearChange
public import TauCeti.Analysis.Pseudodifferential.Quantization
import TauCeti.Analysis.Distribution.SchwartzSpace.Conjugation
import TauCeti.Analysis.InnerProductSpace.Adjoint.Scalar

/-!
# Complex conjugation of quantizations

Let `a` be a scalar coefficient on `ℝⁿ`, with values in `ℂ →L[ℂ] ℂ`. Conjugating the output and the
input of its left quantization `Op(a)` gives again a left quantization:

`conj (Op(a) u) = Op(ã) (conj u)`,  `ã(x, ξ) = conj a(x, -ξ)`

(`TauCeti.quantizeSchwartzValue_conjCLM`). The frequency changes sign because conjugation reverses
the phase `exp(i x·ξ)`, while the position is unchanged. In the coefficient space the conjugate of
a scalar operator is its adjoint, so `ã(x, ξ)` is written `a(x, -ξ)†`. For a classical symbol `a`,
the symbol `ã` is the pointwise adjoint of the change of frequency `ξ ↦ -ξ`, again classical of the
same order, with principal symbol `conj σ(a)(x, -ξ)`
(`TauCeti.ClassicalSymbol.quantizeSchwartzValue_conjCLM`,
`TauCeti.ClassicalSymbol.coefficient_principal_pointwiseAdjoint_compProdMap_neg`).

This is the compatibility of the Fourier convention with conjugation through which real operators
are recovered from complex ones: an operator preserving real-valued functions commutes with
conjugation, so its symbol satisfies `a(x, -ξ) = conj a(x, ξ)`.

## Main results

* `TauCeti.quantizeSchwartzValue_conjCLM`: `Op(ã) (conj u) = conj (Op(a) u)` for every coefficient
  `a`, on Schwartz functions.
* `TauCeti.ClassicalSymbol.quantizeSchwartzValue_conjCLM`: the same identity for a classical
  symbol, with `ã` the classical symbol `(a ∘ (id × -id))†`.
* `TauCeti.ClassicalSymbol.coefficient_principal_pointwiseAdjoint_compProdMap_neg`: the principal
  symbol of `ã` is `conj σ(a)(x, -ξ)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace ComplexConjugate
open MeasureTheory Real FourierTransform

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Conjugation of a quantization.** For a scalar coefficient `a`, conjugating the input and
the output of `Op(a)` gives the quantization of `ã(x, ξ) = a(x, -ξ)† = conj a(x, -ξ)`:

`Op(ã) (conj u) (x) = conj (Op(a) u (x))`. -/
theorem quantizeSchwartzValue_conjCLM (a : E × E → ℂ →L[ℂ] ℂ) (u : 𝓢(E, ℂ)) (x : E) :
    quantizeSchwartzValue (fun p ↦ ContinuousLinearMap.adjoint (a (p.1, -p.2)))
        (SchwartzMap.conjCLM u) x =
      conj (quantizeSchwartzValue a u x) := by
  rw [quantizeSchwartzValue_def, quantizeSchwartzValue_def, ← integral_conj,
    ← integral_neg_eq_self]
  congr 1 with ζ
  -- Conjugation reverses the phase.
  have hphase : ((𝐞 ⟪-ζ, x⟫ : Circle) : ℂ) = conj (𝐞 ⟪ζ, x⟫ : ℂ) := by
    simp [Real.fourierChar_apply, ← Complex.exp_conj, map_ofNat]
  -- The sign change of the frequency in `ã` undoes the substitution `ζ ↦ -ζ`.
  have hfreq : -((2 * π) • -ζ) = (2 * π) • ζ := by simp
  -- `𝓕 (conj u) (-ζ) = conj (𝓕⁻ u (-ζ)) = conj (𝓕 u ζ)`.
  have hfourier : 𝓕 (SchwartzMap.conjCLM u) (-ζ) = conj (𝓕 u ζ) := by
    rw [SchwartzMap.fourier_conjCLM_apply, SchwartzMap.fourierInv_coe,
      Real.fourierInv_eq_fourier_neg, neg_neg, SchwartzMap.fourier_coe]
  rw [Circle.smul_def, Circle.smul_def, hphase, hfreq, hfourier]
  simp [ContinuousLinearMap.adjoint_apply_eq_star_apply_star]

namespace ClassicalSymbol

variable {n : ℕ} {m : ℝ}

/-- The coefficient of `(a ∘ (id × -id))†` at `(x, ξ)` is the adjoint of `a(x, -ξ)`. -/
theorem coefficient_pointwiseAdjoint_compProdMap_neg (a : ClassicalSymbol n ℂ ℂ m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (compProdMap (.id ℝ _) (.neg ℝ) a).pointwiseAdjoint.toSymbol.coefficient p =
      ContinuousLinearMap.adjoint (a.toSymbol.coefficient (p.1, -p.2)) := by
  simp [ContinuousLinearMap.adjointRealCLM_apply, toSymbol_compProdMap,
    Symbol.coefficient_compProdMap]

/-- **Conjugation of the quantization of a classical symbol.** For a classical symbol `a` of order
`m`, `conj (Op(a) u) = Op(ã) (conj u)` for the classical symbol `ã = (a ∘ (id × -id))†` of order
`m`, whose coefficient is `ã(x, ξ) = conj a(x, -ξ)`. -/
theorem quantizeSchwartzValue_conjCLM (a : ClassicalSymbol n ℂ ℂ m)
    (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (compProdMap (.id ℝ _) (.neg ℝ) a).pointwiseAdjoint.toSymbol.coefficient
        (SchwartzMap.conjCLM u) x =
      conj (quantizeSchwartzValue a.toSymbol.coefficient u x) := by
  rw [← TauCeti.quantizeSchwartzValue_conjCLM]
  exact quantizeSchwartzValue_congr_left
    (fun ξ ↦ coefficient_pointwiseAdjoint_compProdMap_neg a (x, ξ)) _

/-- The principal symbol of `ã = (a ∘ (id × -id))†` is `conj σ(a)(x, -ξ)`. -/
theorem coefficient_principal_pointwiseAdjoint_compProdMap_neg (a : ClassicalSymbol n ℂ ℂ m)
    (x ξ : CoordinateSpace n) :
    (compProdMap (.id ℝ _) (.neg ℝ) a).pointwiseAdjoint.principal.coefficient (x, ξ) 1 =
      conj (a.principal.coefficient (x, -ξ) 1) := by
  simp [ContinuousLinearMap.adjoint_apply_eq_star_apply_star, principal_compProdMap,
    HomogeneousSymbol.coefficient_compProdMap]

end ClassicalSymbol

end TauCeti
