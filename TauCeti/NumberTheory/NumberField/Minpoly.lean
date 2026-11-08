/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Minimal polynomials of algebraic integers

An algebraic integer `x` of a number field `K` has a minimal polynomial over `ℤ`, as an element of
`𝓞 K`, and a minimal polynomial over `ℚ`, as an element of `K`. Since `ℤ` is integrally closed,
the second is the first with its coefficients cast to `ℚ`.

## Main results

* `NumberField.RingOfIntegers.minpoly_rat_coe`:
  `minpoly ℚ (x : K) = (minpoly ℤ x).map (algebraMap ℤ ℚ)`.
* `TauCeti.NumberField.minpoly_int_eq_of_aeval_eq_zero`: a root of `minpoly ℚ x` in a nontrivial
  `ℚ`-algebra has the same minimal polynomial over `ℤ` as `x`.
* `TauCeti.NumberField.minpoly_two_mul_sub_one_of_minpoly_eq_X_sq_sub_X_add`: an algebraic
  integer `ω` with minimal polynomial `X² - X + c` has `2ω - 1` with minimal polynomial
  `X² - (1 - 4c)`.
* `TauCeti.NumberField.exists_multiset_map_algebraMap_eq_roots`: a monic integer polynomial which
  splits in a field `M` of characteristic zero factors over `𝓞 M` into linear factors whose
  roots map onto the roots in `M`.
-/

public section

open scoped NumberField

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

/-- The minimal polynomial over `ℚ` of an algebraic integer `x`, viewed in `K`, is its minimal
polynomial over `ℤ` with the coefficients cast to `ℚ`. -/
theorem minpoly_rat_coe (x : 𝓞 K) :
    minpoly ℚ (x : K) = (minpoly ℤ x).map (algebraMap ℤ ℚ) := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ x.isIntegral_coe, minpoly_coe]

end NumberField.RingOfIntegers

namespace TauCeti.NumberField

open Polynomial

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

section RingTarget

variable {M : Type*} [Ring M] [Algebra ℚ M]

/-- In any `ℚ`-algebra, `minpoly ℚ θ` and `minpoly ℤ θ` take the same value at every element. -/
theorem aeval_minpoly_rat_eq_aeval_minpoly_int (β : M) :
    aeval β (minpoly ℚ (θ : K)) = aeval β (minpoly ℤ θ) := by
  rw [_root_.NumberField.RingOfIntegers.minpoly_rat_coe, aeval_map_algebraMap]

/-- A root of `minpoly ℚ θ` in a `ℚ`-algebra is an algebraic integer. -/
theorem isIntegral_of_aeval_eq_zero {β : M}
    (hβ : aeval β (minpoly ℚ (θ : K)) = 0) : IsIntegral ℤ β :=
  ⟨minpoly ℤ θ, minpoly.monic θ.isIntegral, by
    rwa [aeval_minpoly_rat_eq_aeval_minpoly_int] at hβ⟩

/-- A root of `minpoly ℚ θ` in a nontrivial `ℚ`-algebra has the same minimal polynomial over `ℤ`
as `θ`. -/
theorem minpoly_int_eq_of_aeval_eq_zero [Nontrivial M] {β : M}
    (hβ : aeval β (minpoly ℚ (θ : K)) = 0) : minpoly ℤ β = minpoly ℤ θ := by
  have hQ := (minpoly.eq_iff_aeval_minpoly_eq_zero (IsIntegral.of_finite ℚ (θ : K))).mpr hβ
  refine (minpoly.unique' ℤ β (minpoly.monic θ.isIntegral)
    ((aeval_minpoly_rat_eq_aeval_minpoly_int β).symm.trans hβ) fun q hq => ?_).symm
  -- A nonzero integer polynomial vanishing at `β` stays nonzero over `ℚ`, so its degree is at
  -- least that of `minpoly ℚ β = minpoly ℚ θ`, which is the degree of `minpoly ℤ θ`.
  refine or_iff_not_imp_left.mpr fun hq0 hqβ => hq.not_ge ?_
  have hinj := (algebraMap ℤ ℚ).injective_int
  rw [← degree_map_eq_of_injective hinj, ← degree_map_eq_of_injective hinj,
    ← _root_.NumberField.RingOfIntegers.minpoly_rat_coe, hQ]
  exact minpoly.degree_le_of_ne_zero ℚ β ((Polynomial.map_ne_zero_iff hinj).mpr hq0)
    (by rwa [aeval_map_algebraMap])

end RingTarget

/-- For an algebraic integer `ω` with minimal polynomial `X² - X + c` over `ℤ`, the element
`2ω - 1` is a square root of `1 - 4c`: its minimal polynomial over `ℤ` is `X² - (1 - 4c)`. This
converts the half-integer presentation of a quadratic field back into the radicand
presentation. -/
theorem minpoly_two_mul_sub_one_of_minpoly_eq_X_sq_sub_X_add {ω : 𝓞 K} {c : ℤ}
    (hmin : minpoly ℤ ω = X ^ 2 - X + C c) :
    minpoly ℤ (2 * ω - 1) = X ^ 2 - C (1 - 4 * c) := by
  -- Scaling the roots of `X² - X + c` by `2` gives the minimal polynomial `X² - 2X + 4c` of `2ω`.
  have hscale : minpoly ℤ ((2 : ℤ) • ω) = X ^ 2 - C 2 * X + C (4 * c) := by
    rw [IsIntegrallyClosed.minpoly_smul two_ne_zero ω.isIntegral, hmin]
    ext i
    have hdeg : (X ^ 2 - X + C c : ℤ[X]).natDegree = 2 := by compute_degree!
    rw [coeff_scaleRoots, hdeg]
    rcases i with _ | _ | _ | i <;> simp [coeff_X, coeff_C, -eq_intCast]
    ring
  -- Over `ℚ`, subtracting `1` composes the minimal polynomial with `X + 1`; the coefficient map
  -- `ℤ → ℚ` is injective.
  have hcoe : ((2 * ω - 1 : 𝓞 K) : K) = (((2 : ℤ) • ω : 𝓞 K) : K) - algebraMap ℚ K 1 := by simp
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  rw [← _root_.NumberField.RingOfIntegers.minpoly_rat_coe, hcoe, minpoly.sub_algebraMap,
    _root_.NumberField.RingOfIntegers.minpoly_rat_coe, hscale]
  simp
  ring

section RootsOfIntegerPolynomial

variable {M : Type*} [Field M] [CharZero M] {f : ℤ[X]}

/-- The two ways of viewing an integer polynomial over a field of characteristic zero agree. -/
private theorem map_map_intCast_rat (f : ℤ[X]) :
    (f.map (Int.castRingHom ℚ)).map (algebraMap ℚ M) =
      (f.map (algebraMap ℤ (𝓞 M))).map (algebraMap (𝓞 M) M) := by
  simp only [Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

/-- The roots of a monic integer polynomial `f` which splits in `M` are algebraic integers: there is
a multiset `t` in `𝓞 M` with `f = ∏ (X - a)` over `a ∈ t` in `(𝓞 M)[X]` and whose image in `M` is
the multiset of roots of `f` in `M`. -/
theorem exists_multiset_map_algebraMap_eq_roots (hf : f.Monic)
    (hsplit : ((f.map (Int.castRingHom ℚ)).map (algebraMap ℚ M)).Splits) :
    ∃ t : Multiset (𝓞 M), t.map (algebraMap (𝓞 M) M) =
        ((f.map (Int.castRingHom ℚ)).map (algebraMap ℚ M)).roots ∧
      f.map (algebraMap ℤ (𝓞 M)) = (t.map fun a => X - C a).prod := by
  classical
  set fM := (f.map (Int.castRingHom ℚ)).map (algebraMap ℚ M) with hfM
  -- Along the tower `ℤ → ℚ → M`, being a root of `f` over `ℚ` is being a root of `f` itself.
  have hint : ∀ x ∈ fM.roots, IsIntegral ℤ x := fun x hx =>
    ⟨f, hf, by
      rw [← aeval_def, ← aeval_map_algebraMap (A := ℚ), algebraMap_int_eq, ← eval_map_algebraMap]
      exact (mem_roots'.mp hx).2⟩
  obtain ⟨t, ht⟩ : ∃ t : Multiset (𝓞 M), t.map (algebraMap (𝓞 M) M) = fM.roots :=
    ⟨fM.roots.attach.map fun x => IsIntegralClosure.mk' (𝓞 M) x.1 (hint x.1 x.2), by
      simp [Multiset.map_map, IsIntegralClosure.algebraMap_mk']⟩
  refine ⟨t, ht, ?_⟩
  refine Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective (𝓞 M) M) ?_
  rw [← map_map_intCast_rat, ← hfM, hsplit.eq_prod_roots_of_monic ((hf.map _).map _), ← ht]
  simp [Polynomial.map_multiset_prod, Multiset.map_map]

end RootsOfIntegerPolynomial

end TauCeti.NumberField
