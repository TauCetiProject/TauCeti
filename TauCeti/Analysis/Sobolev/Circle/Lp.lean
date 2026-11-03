/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Basic

/-!
# The circle Sobolev space `H⁰` is `L²` of the circle

The Fourier-coefficient Sobolev space `H^s` of `TauCeti/Analysis/Sobolev/Circle/Basic.lean` has
the weights `(1 + |n|) ^ s`, which are all `1` when `s = 0`. So `H⁰` is the space `ℓ²(ℤ)` of
square-summable coefficient sequences, and Mathlib's Fourier basis `fourierBasis` of
`L²(AddCircle T)` identifies it with the square-integrable functions on the circle, normalized
Haar measure, by Parseval's identity. Under this identification an element of `H⁰` is the `L²`
function whose Fourier coefficients are its coefficients, and for `s > 1/2` the `L²` function of
an element of `H^s` is its continuous representative `CircleSobolev.toContinuousMap`.

Operations on functions on the circle which are not diagonal in the Fourier basis, such as
precomposition with a diffeomorphism of the circle, are defined on `H⁰` through this
identification.

## Main definitions

* `TauCeti.CircleSobolev.toLpₗᵢ T`: the linear isometric equivalence
  `H⁰ ≃ₗᵢ[ℂ] L²(AddCircle T)`.

## Main statements

* `TauCeti.CircleSobolev.fourierCoeff_toLpₗᵢ` and
  `TauCeti.CircleSobolev.coeff_toLpₗᵢ_symm`: the Fourier coefficients of `toLpₗᵢ T a` are the
  coefficients of `a`.
* `TauCeti.CircleSobolev.toLpₗᵢ_inclusion_eq_toLp_toContinuousMap`: for `s > 1/2` and
  `a ∈ H^s`, the `L²` function of `a` is the class of its continuous representative.

## References

* Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Cambridge University Press,
  2004, Chapter I (the Fourier coefficients of `L²` functions and Parseval's identity).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace CircleSobolev

variable (T : ℝ) [hT : Fact (0 < T)]

/-- **`H⁰` is `L²` of the circle.** The linear isometric equivalence between `H⁰` and the space of
square-integrable functions on `AddCircle T`, for normalized Haar measure, sending a coefficient
sequence to the `L²` sum of its Fourier series. -/
def toLpₗᵢ : CircleSobolev 0 ℂ ≃ₗᵢ[ℂ] Lp ℂ 2 (AddCircle.haarAddCircle (T := T)) :=
  toℓ2ₗᵢ.trans fourierBasis.repr.symm

/-- The Fourier coefficients of the `L²` function of `a ∈ H⁰` are the coefficients of `a`. -/
@[simp]
theorem fourierCoeff_toLpₗᵢ (a : CircleSobolev 0 ℂ) (n : ℤ) :
    fourierCoeff (toLpₗᵢ T a) n = a.coeff n := by
  rw [← fourierBasis_repr, toLpₗᵢ, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, coe_toℓ2ₗᵢ, toℓ2_apply, weight_zero_left, one_smul]

/-- The coefficients of the element of `H⁰` attached to an `L²` function are its Fourier
coefficients. -/
@[simp]
theorem coeff_toLpₗᵢ_symm (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) (n : ℤ) :
    ((toLpₗᵢ T).symm f).coeff n = fourierCoeff f n := by
  rw [← fourierCoeff_toLpₗᵢ T, LinearIsometryEquiv.apply_symm_apply]

/-- The Fourier monomial `x e^{inθ}` of `H⁰` is the `L²` Fourier mode `x e_n`. -/
@[simp]
theorem toLpₗᵢ_single (n : ℤ) (x : ℂ) :
    toLpₗᵢ T (single n x) = x • fourierLp (T := T) 2 n := by
  refine fourierBasis.repr.injective (lp.ext (funext fun m ↦ ?_))
  rw [fourierBasis_repr, fourierCoeff_toLpₗᵢ, coeff_single, map_smul, ← coe_fourierBasis,
    HilbertBasis.repr_self]
  rcases eq_or_ne m n with rfl | hm
  · simp
  · simp [hm]

/-- **The `L²` function of a continuous element.** For `s > 1/2` and `a ∈ H^s`, the `L²` function
of `a`, regarded as an element of `H⁰`, is the class of its continuous representative. -/
theorem toLpₗᵢ_inclusion_eq_toLp_toContinuousMap {s : ℝ} (hs : 1 / 2 < s)
    (a : CircleSobolev s ℂ) :
    toLpₗᵢ T (inclusion (by linarith) a) =
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (toContinuousMap T hs a) := by
  refine fourierBasis.repr.injective (lp.ext (funext fun n ↦ ?_))
  rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_toLpₗᵢ, fourierCoeff_toLp,
    fourierCoeff_toContinuousMap, coeff_inclusion]

end CircleSobolev

end TauCeti
