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

/-!
# Complex conjugation of pseudodifferential operators

Let `V` and `W` carry a conjugation, a continuous conjugate-linear involution `star`, such as
complex conjugation on `ℂ` or componentwise conjugation on `ℂʳ`. The **complex conjugate** of an
operator `P` is `u ↦ star (P (star u))`; on linear maps this is Mathlib's intrinsic star
`LinearMap.intrinsicStar`. For a coefficient `a`, the conjugate of `T = a(x, ξ)` is the
intrinsic star `star ∘ T ∘ star` (`ContinuousLinearMap.intrinsicStarL`), which for scalar
coefficients is the complex conjugate number.

Conjugation turns the character `exp(2πi ⟪ζ, x⟫)` of the Fourier inversion formula into
`exp(-2πi ⟪ζ, x⟫)`, so it reflects the frequency. Thus the complex conjugate of a Kohn–Nirenberg
quantization is again one, with conjugated and reflected symbol:

`star (Op(a) (star u)) = Op(b) u`, `b(x, ξ) = conj (a(x, -ξ))`

(`TauCeti.quantizeSchwartzValue_conjPostcompCLM_starL`, for every coefficient `a`). This is the
pseudodifferential form of `SchwartzMap.fourierMultiplierCLM_conjPostcompCLM`, the case of
coefficients independent of `x`. For instance the conjugate of `D = -i∂`, of symbol `ξ`, is `-D`, of
symbol `conj (-ξ) = -ξ`, while the real operator `∂ = iD`, of symbol `iξ`, is its own conjugate.

For a classical symbol `a` of order `m`, `b` is the classical symbol `a.intrinsicStar` of the same
order (`TauCeti.ClassicalSymbol.intrinsicStar`), whose homogeneous terms, and in particular whose
principal symbol, are those of `a` conjugated and reflected in the same way
(`TauCeti.ClassicalSymbol.principal_intrinsicStar`). It is elliptic exactly when `a` is
(`TauCeti.ClassicalSymbol.isElliptic_intrinsicStar_iff`).

These identities are the local input for conjugation of pseudodifferential operators on manifolds
(`TauCeti.intrinsicStar_mem_classicalPseudodifferentialOperators_iff`), through which real
operators are recognized among complex ones.

## Main declarations

* `TauCeti.quantizeSchwartzValue_conjPostcompCLM_starL`: `Op(a) (star u) = star (Op(b) u)` with
  `b(x, ξ) = conj (a(x, -ξ))`, for every coefficient `a`.
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

noncomputable section

open scoped FourierTransform SchwartzMap RealInnerProductSpace
open MeasureTheory Real FourierTransform WithConv

namespace TauCeti

/-! ### Conjugation of the quantization -/

section Quantization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] [StarAddMonoid V]
  [StarModule ℂ V] [ContinuousStar V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [StarAddMonoid W] [StarModule ℂ W] [ContinuousStar W]

/-- **Conjugation of a quantization.** For every coefficient `a`, the quantization of `a` applied
to the conjugate `star ∘ u` of a Schwartz function is the conjugate of the quantization of the
conjugated and reflected coefficient `b(x, ξ) = conj (a(x, -ξ))` applied to `u`:

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

end Quantization

/-! ### The conjugate of a classical symbol -/

namespace ClassicalSymbol

variable {n : ℕ} {m : ℝ}
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [StarAddMonoid V] [StarModule ℂ V]
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

end ClassicalSymbol

end TauCeti
