/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.Conjugation
public import TauCeti.Analysis.Normed.Operator.IntrinsicStar
public import TauCeti.Analysis.Pseudodifferential.Elliptic
public import TauCeti.Analysis.Pseudodifferential.LinearChange
public import TauCeti.Analysis.Pseudodifferential.Quantization
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

### Vector-valued coefficients

More generally, let `V` and `W` carry a conjugation, a continuous conjugate-linear involution
`star`, such as complex conjugation on `ℂ` or componentwise conjugation on `ℂʳ`. The conjugate of a
value `T = a(x, ξ)` is then its intrinsic star `star ∘ T ∘ star`
(`ContinuousLinearMap.intrinsicStarL`), and

`Op(a) (star u) = star (Op(b) u)`,  `b(x, ξ) = conj (a(x, -ξ))`

(`TauCeti.quantizeSchwartzValue_conjPostcompCLM_starL`, for every coefficient `a`), the
pseudodifferential form of `SchwartzMap.fourierMultiplierCLM_conjPostcompCLM`. For a classical
symbol `a` of order `m`, `b` is the classical symbol `a.intrinsicStar` of the same order
(`TauCeti.ClassicalSymbol.intrinsicStar`), whose homogeneous terms, and in particular whose
principal symbol, are those of `a` conjugated and reflected in the same way
(`TauCeti.ClassicalSymbol.principal_intrinsicStar`). It is elliptic exactly when `a` is
(`TauCeti.ClassicalSymbol.isElliptic_intrinsicStar_iff`). For scalar symbols it is the symbol
`(a ∘ (id × -id))†` above
(`TauCeti.ClassicalSymbol.pointwiseAdjoint_compProdMap_neg_eq_intrinsicStar`).

## Main results

* `TauCeti.quantizeSchwartzValue_conjCLM`: `Op(ã) (conj u) = conj (Op(a) u)` for every coefficient
  `a`, on Schwartz functions.
* `TauCeti.ClassicalSymbol.quantizeSchwartzValue_conjCLM`: the same identity for a classical
  symbol, with `ã` the classical symbol `(a ∘ (id × -id))†`.
* `TauCeti.ClassicalSymbol.coefficient_principal_pointwiseAdjoint_compProdMap_neg`: the principal
  symbol of `ã` is `conj σ(a)(x, -ξ)`.
* `TauCeti.quantizeSchwartzValue_conjPostcompCLM_starL`: `Op(a) (star u) = star (Op(b) u)` with
  `b(x, ξ) = conj (a(x, -ξ))`, for every vector-valued coefficient `a`.
* `TauCeti.ClassicalSymbol.intrinsicStar`: the conjugated and reflected classical symbol, with its
  coefficient (`TauCeti.ClassicalSymbol.coefficient_intrinsicStar`), homogeneous terms, principal
  symbol and quantization (`TauCeti.ClassicalSymbol.quantizeSchwartzValue_intrinsicStar`). It is
  a conjugate-linear involution (`TauCeti.ClassicalSymbol.intrinsicStar_intrinsicStar`,
  `TauCeti.ClassicalSymbol.intrinsicStar_smul`).
* `TauCeti.ClassicalSymbol.isElliptic_intrinsicStar_iff`: conjugation preserves ellipticity.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (1.1)–(1.4).
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace ComplexConjugate
open MeasureTheory Real FourierTransform WithConv

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

section VectorValued

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] [StarAddMonoid V]
  [StarModule ℂ V] [ContinuousStar V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [StarAddMonoid W] [StarModule ℂ W] [ContinuousStar W]

/-- **Conjugation of a quantization, vector-valued.** For every coefficient `a` with values in
`V →L[ℂ] W`, the quantization of `a` applied to the conjugate `star ∘ u` of a Schwartz function is
the conjugate of the quantization of the conjugated and reflected coefficient
`b(x, ξ) = conj (a(x, -ξ))` applied to `u`:

`Op(a) (star u) (x) = star (Op(b) u (x))`. -/
theorem quantizeSchwartzValue_conjPostcompCLM_starL (a : E × E → V →L[ℂ] W) (u : 𝓢(E, V))
    (x : E) :
    quantizeSchwartzValue a
        (SchwartzMap.conjPostcompCLM (starL ℂ : V ≃L⋆[ℂ] V).toContinuousLinearMap u) x =
      star (quantizeSchwartzValue (fun p ↦ (star (toConv (a (p.1, -p.2)))).ofConv) u x) := by
  -- The star of a Bochner integral is the integral of the star.
  have hstar (g : E → W) : star (∫ ζ, g ζ) = ∫ ζ, star (g ζ) :=
    ((starL' ℝ : W ≃L[ℝ] W).integral_comp_comm g).symm
  -- `𝓕 (star u) ζ = star (𝓕 u (-ζ))`; then substitute `ζ ↦ -ζ`.
  rw [quantizeSchwartzValue_def, quantizeSchwartzValue_def, hstar, ← integral_neg_eq_self]
  congr 1 with ζ
  rw [SchwartzMap.fourier_conjPostcompCLM_apply, SchwartzMap.fourierInv_coe,
    fourierInv_eq_fourier_neg, SchwartzMap.fourier_coe]
  simp [Circle.smul_def, smul_neg, inner_neg_left]

end VectorValued

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

/-! ### The conjugate of a vector-valued classical symbol -/

section IntrinsicStar

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [StarAddMonoid V] [StarModule ℂ V]
  [ContinuousStar V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [StarAddMonoid W] [StarModule ℂ W] [ContinuousStar W]

open ContinuousLinearMap (intrinsicStarL)

/-- The **conjugate** `(x, ξ) ↦ conj (a(x, -ξ))` of a classical symbol `a`, where the conjugate of
a value `T` is its intrinsic star `star ∘ T ∘ star`: a classical symbol of the same order, whose
homogeneous terms are those of `a` conjugated and reflected in the same way. Its quantization is
the complex conjugate `u ↦ star (Op(a) (star u))` of the quantization of `a`
(`TauCeti.ClassicalSymbol.quantizeSchwartzValue_intrinsicStar`). -/
def intrinsicStar (a : ClassicalSymbol n V W m) : ClassicalSymbol n V W m :=
  (compProdMap (.id ℝ (CoordinateSpace n)) (.neg ℝ) a).map intrinsicStarL

variable (a b : ClassicalSymbol n V W m)

@[simp]
theorem coefficient_intrinsicStar (p : CoordinateSpace n × CoordinateSpace n) :
    a.intrinsicStar.toSymbol.coefficient p =
      (star (toConv (a.toSymbol.coefficient (p.1, -p.2)))).ofConv := by
  simp [intrinsicStar]

@[simp]
theorem term_intrinsicStar (j : ℕ) :
    a.intrinsicStar.term j =
      ((a.term j).compProdMap (.id ℝ (CoordinateSpace n)) (.neg ℝ)).map intrinsicStarL := by
  simp [intrinsicStar]

/-- The principal symbol of the conjugate of `a` is the principal symbol of `a`, conjugated and
reflected. -/
@[simp]
theorem principal_intrinsicStar :
    a.intrinsicStar.principal =
      (a.principal.compProdMap (.id ℝ (CoordinateSpace n)) (.neg ℝ)).map intrinsicStarL := by
  simp [intrinsicStar]

/-- The value of the principal symbol of the conjugate of `a` at `(x, ξ)` is the conjugate of the
value of the principal symbol of `a` at `(x, -ξ)`. -/
theorem coefficient_principal_intrinsicStar (p : CoordinateSpace n × CoordinateSpace n) :
    a.intrinsicStar.principal.coefficient p =
      (star (toConv (a.principal.coefficient (p.1, -p.2)))).ofConv := by
  simp

@[simp]
theorem intrinsicStar_intrinsicStar : a.intrinsicStar.intrinsicStar = a :=
  ext <| Symbol.ext <| funext fun p ↦ by ext; simp

@[simp]
theorem intrinsicStar_zero : (0 : ClassicalSymbol n V W m).intrinsicStar = 0 :=
  ext <| Symbol.ext <| funext fun p ↦ by ext; simp

@[simp]
theorem intrinsicStar_add : (a + b).intrinsicStar = a.intrinsicStar + b.intrinsicStar :=
  ext <| Symbol.ext <| funext fun p ↦ by ext; simp

@[simp]
theorem intrinsicStar_neg : (-a).intrinsicStar = -a.intrinsicStar :=
  ext <| Symbol.ext <| funext fun p ↦ by ext; simp

@[simp]
theorem intrinsicStar_sub : (a - b).intrinsicStar = a.intrinsicStar - b.intrinsicStar :=
  ext <| Symbol.ext <| funext fun p ↦ by ext; simp

/-- Conjugation of symbols is conjugate linear. -/
@[simp]
theorem intrinsicStar_smul (c : ℂ) : (c • a).intrinsicStar = star c • a.intrinsicStar :=
  ext <| Symbol.ext <| funext fun p ↦ by ext; simp

/-- **The quantization of the conjugate symbol.** The quantization of the conjugate of `a` is the
complex conjugate of the quantization of `a`: `Op(a.intrinsicStar) u = star (Op(a) (star u))`. -/
theorem quantizeSchwartzValue_intrinsicStar (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue a.intrinsicStar.toSymbol.coefficient u x =
      star (quantizeSchwartzValue a.toSymbol.coefficient
        (SchwartzMap.conjPostcompCLM (starL ℂ : V ≃L⋆[ℂ] V).toContinuousLinearMap u) x) := by
  have := FiniteDimensional.completeSpace ℂ V
  rw [quantizeSchwartzValue_conjPostcompCLM_starL, star_star]
  exact quantizeSchwartzValue_congr_left (fun ξ ↦ by simp) u

/-- **Conjugation preserves ellipticity.** The conjugate of a classical symbol is elliptic exactly
when the symbol is. -/
@[simp]
theorem isElliptic_intrinsicStar_iff [CompleteSpace W] :
    a.intrinsicStar.IsElliptic ↔ a.IsElliptic := by
  have := FiniteDimensional.completeSpace ℂ V
  rw [isElliptic_def, isElliptic_def, HomogeneousSymbol.isElliptic_iff_bijective,
    HomogeneousSymbol.isElliptic_iff_bijective, principal_intrinsicStar]
  -- The conjugate principal symbol at `ξ` is the conjugate of the principal symbol at `-ξ`.
  refine ⟨fun h x ξ hξ ↦ ?_, fun h x ξ hξ ↦ ?_⟩ <;>
    simpa using h x (-ξ) (neg_ne_zero.2 hξ)

end IntrinsicStar

/-- For a scalar classical symbol, the pointwise adjoint `(a ∘ (id × -id))†` is its conjugate
`a.intrinsicStar`: the adjoint of a scalar operator is its intrinsic star. -/
theorem pointwiseAdjoint_compProdMap_neg_eq_intrinsicStar (a : ClassicalSymbol n ℂ ℂ m) :
    (compProdMap (.id ℝ _) (.neg ℝ) a).pointwiseAdjoint = a.intrinsicStar :=
  ext <| Symbol.ext <| funext fun p ↦ by
    ext
    simp [ContinuousLinearMap.adjoint_apply_eq_star_apply_star]

end ClassicalSymbol

end TauCeti
