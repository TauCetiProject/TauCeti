/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.ParameterFamily
public import TauCeti.RingTheory.MvPolynomial.JetInterpolation
import TauCeti.LinearAlgebra.Basis.Submodule

/-!
# Rational evaluation of bounded-degree polynomials at a tuple of a number field

Let `K` be a number field and `κ : σ → K` a tuple. Evaluating at `κ` the rational polynomials of
total degree at most `d` gives a `ℚ`-subspace

  `W = (restrictTotalDegree σ ℚ d).map (aeval κ)`

of `K`. Its complex counterpart is the value map at the conjugate points of `κ`: the complex
polynomials of total degree at most `d` are evaluated at the points `(τ (κ j))_j ∈ ℂ^σ`, one for
each complex embedding `τ : K →+* ℂ`, which is `TauCeti.firstJetValueMap` at these points.

This file shows that the two have the same rank. The vectors of conjugates `(τ x)_τ` of the
elements `x` of any `ℚ`-subspace `W` of `K` span a complex subspace of dimension `dim_ℚ W`
(`TauCeti.NumberField.finrank_span_canonicalEmbedding_image`), and for the subspace of values of
bounded-degree polynomials this complex span is exactly the range of the complex value map
(`TauCeti.NumberField.range_firstJetValueMap_conjugate`), since both are spanned by the conjugate
vectors of the monomials `κ ^ α` with `|α| ≤ d`. Hence the complex value map at the conjugate
points is onto `ℂ^{K →+* ℂ}` if and only if every element of `K` is the value at `κ` of a rational
polynomial of total degree at most `d`
(`TauCeti.NumberField.firstJetValueMap_conjugate_surjective_iff`). In matrix terms, the complex
matrix of the value map is the rational matrix of bounded evaluation in a `ℚ`-basis of `K`
multiplied by the invertible embedding matrix of that basis, so both have the same rank.

In particular, if the conjugate points of `κ` are well poised in degree `d`, so that values and
first derivatives at them can be prescribed independently, then their values alone can be
prescribed, so rational bounded evaluation at `κ` is onto `K`, polynomial evaluation `ℚ[X] → K`
at `κ` is surjective, and `κ` generates `K` as a `ℚ`-algebra. This is how generators of a number
field are obtained from a nonvanishing first-jet minor in Couveignes' construction of small models
of number fields.

The surjectivity is over `ℚ` only. For `κ = √5` in `ℚ(√5)` and `d = 1`, the rational values
`a + b√5` exhaust the field, but the integral values form `ℤ[√5]`, of index `2` in the ring of
integers. Conversely, at `κ = 0` in a quadratic field every rational polynomial value is
rational, and the conjugate value map has rank `1`.

## Main results

* `TauCeti.NumberField.range_firstJetValueMap_conjugate`: the range of the complex value map at
  the conjugate points of `κ` is the complex span of the conjugate vectors of the rational values
  at `κ` of the polynomials of total degree at most `d`.
* `TauCeti.NumberField.firstJetValueMap_conjugate_surjective_iff`: the complex value map at the
  conjugate points is onto if and only if rational evaluation at `κ` of the polynomials of total
  degree at most `d` is onto `K`.
* `TauCeti.NumberField.map_aeval_restrictTotalDegree_eq_top_of_wellPoised`: if the conjugate
  points of `κ` are well poised in degree `d`, then rational bounded evaluation at `κ` is onto `K`.
* `TauCeti.NumberField.aeval_surjective_of_firstJetValueMap_surjective`: if the complex value map
  at the conjugate points of `κ` is onto, then polynomial evaluation at `κ` is surjective, so `κ`
  generates `K` as a `ℚ`-algebra (`MvPolynomial.aeval_surjective_iff_adjoin_range_eq_top`).

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), 487–497, §3, p. 492.
-/

public section

open Module MvPolynomial NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### Bounded evaluation at a tuple and at its conjugates -/

variable {σ : Type*} (κ : σ → K) (d : ℕ)

/-- The value of a monomial at the conjugate points of `κ` is the vector of conjugates of its value
at `κ`. -/
theorem firstJetValueMap_conjugate_basisRestrictTotalDegree (s : {s : σ →₀ ℕ // s.degree ≤ d}) :
    firstJetValueMap (fun (τ : K →+* ℂ) j ↦ τ (κ j)) d (basisRestrictTotalDegree σ ℂ d s) =
      canonicalEmbedding K (aeval κ (monomial (s : σ →₀ ℕ) (1 : ℚ))) := by
  funext τ
  simp [eval_monomial, aeval_monomial, map_finsuppProd]

/-- The range of the complex value map at the conjugate points `(τ (κ j))_j` of `κ` is the complex
span of the conjugate vectors of the values at `κ` of the rational polynomials of total degree at
most `d`. Both are spanned by the conjugate vectors of the monomials `κ ^ α` with `|α| ≤ d`. -/
theorem range_firstJetValueMap_conjugate :
    LinearMap.range (firstJetValueMap (fun (τ : K →+* ℂ) j ↦ τ (κ j)) d) =
      Submodule.span ℂ
        (canonicalEmbedding K '' (restrictTotalDegree σ ℚ d).map (aeval κ).toLinearMap) := by
  -- The conjugate vectors of the rational values at `κ` span the same complex subspace as the
  -- conjugate vectors of the values of the monomial basis.
  have hspan : Submodule.span ℂ
      (canonicalEmbedding K '' (restrictTotalDegree σ ℚ d).map (aeval κ).toLinearMap) =
        Submodule.span ℂ (Set.range fun s ↦ canonicalEmbedding K
          (aeval κ (basisRestrictTotalDegree σ ℚ d s : MvPolynomial σ ℚ))) := by
    rw [Submodule.map_coe, ← Set.image_comp]
    exact (basisRestrictTotalDegree σ ℚ d).span_image
      ((canonicalEmbedding K).toRatAlgHom.toLinearMap ∘ₗ (aeval κ).toLinearMap)
  rw [hspan, LinearMap.range_eq_map, ← (basisRestrictTotalDegree σ ℂ d).span_eq,
    Submodule.map_span, ← Set.range_comp]
  congr 2
  funext s
  simpa using firstJetValueMap_conjugate_basisRestrictTotalDegree κ d s

/-- The complex value map at the conjugate points `(τ (κ j))_j` of `κ` in degree `d` is onto if and
only if every element of `K` is the value at `κ` of a rational polynomial of total degree at
most `d`. -/
theorem firstJetValueMap_conjugate_surjective_iff :
    Function.Surjective (firstJetValueMap (fun (τ : K →+* ℂ) j ↦ τ (κ j)) d) ↔
      (restrictTotalDegree σ ℚ d).map (aeval κ).toLinearMap = ⊤ := by
  rw [← LinearMap.range_eq_top, range_firstJetValueMap_conjugate,
    span_canonicalEmbedding_image_eq_top_iff]

variable {κ d}

/-- If the conjugate points `(τ (κ j))_j` of `κ` are well poised in degree `d`, then every element
of `K` is the value at `κ` of a rational polynomial of total degree at most `d`. -/
theorem map_aeval_restrictTotalDegree_eq_top_of_wellPoised
    (h : WellPoised (fun (τ : K →+* ℂ) j ↦ τ (κ j)) d) :
    (restrictTotalDegree σ ℚ d).map (aeval κ).toLinearMap = ⊤ :=
  (firstJetValueMap_conjugate_surjective_iff κ d).1
    (firstJetMap_surjective_iff.1 (wellPoised_iff.1 h)).1

/-- If the complex value map at the conjugate points `(τ (κ j))_j` of `κ` is onto in some degree,
then evaluation of rational polynomials at `κ` is onto `K`. -/
theorem aeval_surjective_of_firstJetValueMap_surjective
    (h : Function.Surjective (firstJetValueMap (fun (τ : K →+* ℂ) j ↦ τ (κ j)) d)) :
    Function.Surjective (aeval κ : MvPolynomial σ ℚ →ₐ[ℚ] K) := by
  intro x
  obtain ⟨f, -, hf⟩ := (Submodule.mem_map (f := (aeval κ).toLinearMap)).1
    (((firstJetValueMap_conjugate_surjective_iff κ d).1 h).ge (Submodule.mem_top (x := x)))
  exact ⟨f, hf⟩

end TauCeti.NumberField
