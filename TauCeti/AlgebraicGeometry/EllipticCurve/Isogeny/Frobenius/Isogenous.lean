/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Zeta
-- Proof-only: powers of Frobenius commute with every morphism.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Composition
-- Proof-only: the local polynomial at good reduction, read through the Frobenius trace.
import TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
-- Proof-only: `deg (1 - π) = #E(𝔽_q)`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.OneSubFrobenius.Degree

/-!
# Isogenous elliptic curves over a finite field have the same number of points

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a finite field `F` with `q` elements, and
let `π₁`, `π₂` be their `q`-power Frobenius endomorphisms. Frobenius commutes with every isogeny
defined over `F`, so `φ ∘ π₁ ^ n = π₂ ^ n ∘ φ`, and composition is biadditive, so

`φ ∘ (1 - π₁ ^ n) = (1 - π₂ ^ n) ∘ φ`.

The degree is multiplicative and `deg φ ≠ 0`, hence `deg (1 - π₁ ^ n) = deg (1 - π₂ ^ n)` for
every `n`. For `n = 1` both sides are point counts, `deg (1 - π) = #E(𝔽_q)`, which gives the
classical statement that isogenous curves over `𝔽_q` have the same number of points. For general
`n` both sides are point counts over an extension of `F` of degree `n`, and they are the
coefficients of the logarithm of the zeta function, so isogenous curves have the same zeta
function.

Over the fraction field of a discrete valuation ring with finite residue field, the local
polynomial of a curve with good reduction (Mathlib's `WeierstrassCurve.localPolynomial`, the
local factor of the `L`-function) is `1 - a T + q T²`, with `a` the Frobenius trace of the
reduction. So two curves with good reduction whose reductions are isogenous have the same local
polynomial. The reduction of an isogeny defined over the fraction field to an isogeny of the
reduced curves is not constructed here; it is supplied as the isogeny of reductions.

## Main results

* `TauCeti.Isogeny.degree_one_sub_frobenius_pow_eq`: `deg (1 - π₁ ^ n) = deg (1 - π₂ ^ n)`.
* `TauCeti.Isogeny.pointCount_eq`: isogenous curves over a finite field have the same number of
  points, the point at infinity included.
* `TauCeti.Isogeny.frobeniusTrace_eq`: they have the same Frobenius trace `a_q`.
* `TauCeti.Isogeny.frobeniusPowTrace_eq`: they have the same traces of the powers of Frobenius.
* `TauCeti.Isogeny.pointCount_baseChange_eq`: they have the same number of points over every
  finite extension of `F`.
* `TauCeti.Isogeny.zetaFunction_eq`: they have the same zeta function.
* `TauCeti.Isogeny.localPolynomial_eq`: two curves with good reduction whose reductions are
  isogenous have the same local polynomial.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.1–2.
-/

public section

open WeierstrassCurve

namespace TauCeti.Isogeny

section FiniteField

variable {F : Type*} [Field F] [Finite F] {W₁ W₂ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Isogenous curves have the same `deg (1 - π ^ n)`**: if `φ : W₁ → W₂` is an isogeny over a
finite field, then `deg (1 - π₁ ^ n) = deg (1 - π₂ ^ n)` for the Frobenius endomorphisms `π₁` of
`W₁` and `π₂` of `W₂`. -/
theorem degree_one_sub_frobenius_pow_eq (φ : Isogeny W₁ W₂) (n : ℕ) :
    (1 - Hom.ofIsogeny (frobeniusIsogeny W₁) ^ n).degree =
      (1 - Hom.ofIsogeny (frobeniusIsogeny W₂) ^ n).degree := by
  -- `(1 - π₂ ^ n) ∘ φ = φ ∘ (1 - π₁ ^ n)`, and `deg φ` cancels from the degrees of both sides
  have h := congrArg Hom.degree <| show
      (1 - Hom.ofIsogeny (frobeniusIsogeny W₂) ^ n).comp (Hom.ofIsogeny φ) =
        (Hom.ofIsogeny φ).comp (1 - Hom.ofIsogeny (frobeniusIsogeny W₁) ^ n) by
    rw [Hom.sub_comp, Hom.comp_sub, Hom.frobenius_pow_comp, Hom.one_def, Hom.one_def,
      Hom.id_comp, Hom.comp_id]
  rw [Hom.degree_comp, Hom.degree_comp, Hom.degree_ofIsogeny, mul_comm] at h
  exact (Nat.eq_of_mul_eq_mul_left φ.degree_pos h).symm

/-- **Isogenous curves over a finite field have the same number of points**, the point at infinity
included. -/
theorem pointCount_eq (φ : Isogeny W₁ W₂) : W₁.pointCount = W₂.pointCount := by
  simpa only [pow_one, ← ofIsogeny_oneSubFrobeniusIsogeny, Hom.degree_ofIsogeny,
    degree_oneSubFrobeniusIsogeny_eq_pointCount] using φ.degree_one_sub_frobenius_pow_eq 1

/-- **Isogenous curves over a finite field have the same Frobenius trace** `a_q = q + 1 - #E(𝔽_q)`.
-/
theorem frobeniusTrace_eq (φ : Isogeny W₁ W₂) : W₁.frobeniusTrace = W₂.frobeniusTrace := by
  rw [frobeniusTrace_def, frobeniusTrace_def, φ.pointCount_eq]

/-- **Isogenous curves over a finite field have the same traces of the powers of Frobenius**
`q ^ n + 1 - deg (1 - π ^ n)`. -/
theorem frobeniusPowTrace_eq (φ : Isogeny W₁ W₂) (n : ℕ) :
    W₁.frobeniusPowTrace n = W₂.frobeniusPowTrace n := by
  rw [frobeniusPowTrace_def, frobeniusPowTrace_def, φ.degree_one_sub_frobenius_pow_eq]

/-- **Isogenous curves over a finite field have the same number of points over every finite
extension** `E` of the base, the point at infinity included. -/
theorem pointCount_baseChange_eq (φ : Isogeny W₁ W₂) (E : Type*) [Field E] [Finite E]
    [Algebra F E] : (W₁⁄E).pointCount = (W₂⁄E).pointCount := by
  -- over `E` both Frobenius traces are the trace of the `[E : F]`th power of Frobenius
  have h := (W₁.frobeniusPowTrace_finrank E).symm.trans
    ((φ.frobeniusPowTrace_eq _).trans (W₂.frobeniusPowTrace_finrank E))
  rw [frobeniusTrace_def, frobeniusTrace_def] at h
  have h' : ((W₁⁄E).pointCount : ℤ) = (W₂⁄E).pointCount := by linarith
  exact_mod_cast h'

/-- **Isogenous curves over a finite field have the same zeta function**
`Z(W/F, T) = exp (∑_{n ≥ 1} #W(𝔽_{qⁿ}) Tⁿ / n)`. -/
theorem zetaFunction_eq (φ : Isogeny W₁ W₂) : W₁.zetaFunction = W₂.zetaFunction := by
  simp only [zetaFunction_def, φ.degree_one_sub_frobenius_pow_eq]

end FiniteField

section LocalPolynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (IsLocalRing.ResidueField R)] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {W₁ W₂ : WeierstrassCurve K}

/-- **Curves with good reduction and isogenous reductions have the same local polynomial**: over
the fraction field of a discrete valuation ring with finite residue field, if `W₁` and `W₂` have
good reduction and there is an isogeny between their reductions, then their local factors
`1 - a T + q T²` (Mathlib's `WeierstrassCurve.localPolynomial`) agree. -/
theorem localPolynomial_eq
    (φ : Isogeny ((W₁.minimal R).reduction R).toAffine ((W₂.minimal R).reduction R).toAffine)
    (h₁ : (W₁.minimal R).HasGoodReduction R) (h₂ : (W₂.minimal R).HasGoodReduction R) :
    W₁.localPolynomial R = W₂.localPolynomial R := by
  have := (hasGoodReduction_iff_isElliptic_reduction R).1 h₁
  have := (hasGoodReduction_iff_isElliptic_reduction R).1 h₂
  rw [localPolynomial_eq_of_hasGoodReduction R W₁ h₁,
    localPolynomial_eq_of_hasGoodReduction R W₂ h₂, φ.frobeniusTrace_eq]

end LocalPolynomial

end TauCeti.Isogeny

end
