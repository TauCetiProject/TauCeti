/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.InfinitePlace
public import TauCeti.NumberTheory.NumberField.Quadratic.Norm
import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Norm.Basic

/-!
# Units of norm `-1` and total positivity in a quadratic field

Let `K = ℚ(√d)` be a quadratic number field, presented by `θ : 𝓞 K` with `minpoly ℤ θ = X² - d`
and `Algebra.adjoin ℚ {θ} = ⊤`. This file records how a unit of norm `-1` interacts with total
positivity.

The mechanism is a sign count carried by the norm. Every real embedding of `K` is one fixed
embedding `φ`, or `φ` composed with quadratic conjugation `σ`
(`NumberField.realRingHom_eq_or_eq_comp_quadraticConj`), so the two signs an element `x` receives
are those of `φ x` and `φ (σ x)`, whose product is `N(x)`. Hence `N(x) > 0` says the two signs
agree, that is, `x` or `-x` is totally positive
(`NumberField.isTotallyPositive_or_isTotallyPositive_neg_of_norm_pos`), and a nonzero element has
negative norm exactly when neither it nor its negative is totally positive. Multiplying by a unit
of norm `-1` exchanges the two cases, so such a unit lets every nonzero `x` be scaled to a totally
positive element by a unit of `𝓞 K`. Conversely, when `0 < d` the generator has negative norm
`N(θ) = -d`, so a totally positive unit multiple `v · θ` forces `N(v) = -1`.

## Main results

* `NumberField.exists_unit_isTotallyPositive_smul_of_norm_eq_neg_one`: a unit of norm `-1` makes
  some unit multiple of every nonzero element totally positive.
* `NumberField.norm_eq_neg_one_of_isTotallyPositive_smul_gen`: conversely, for `0 < d`, a totally
  positive unit multiple of `θ` exhibits a unit of norm `-1`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §6.A.
* F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2.
-/

public section

open Polynomial NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **A unit of norm `-1` makes some unit multiple of every nonzero element totally positive.**
An element of positive norm is already totally positive up to sign; one of negative norm is
brought to positive norm by the unit of norm `-1`. This is the archimedean content of the criterion
`NumberField.NarrowClassGroup.toClassGroup_injective_of_norm_eq_neg_one`. -/
theorem exists_unit_isTotallyPositive_smul_of_norm_eq_neg_one
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {u : (𝓞 K)ˣ}
    (hu : Algebra.norm ℚ (((u : 𝓞 K) : K)) = -1) {x : K} (hx : x ≠ 0) :
    ∃ v : (𝓞 K)ˣ, IsTotallyPositive (v • x) := by
  have hnx : Algebra.norm ℚ x ≠ 0 :=
    (Algebra.norm_ne_zero_iff_of_basis (Module.finBasis ℚ K)).mpr hx
  rcases hnx.lt_or_gt with hlt | hgt
  · -- Negative norm: `u • x` has norm `-N(x) > 0`.
    have hux : 0 < Algebra.norm ℚ (u • x) := by
      have hval : u • x = ((u : 𝓞 K) : K) * x := by simp [Units.smul_def, Algebra.smul_def]
      rw [hval, map_mul, hu]
      linarith
    obtain ⟨ε, hε⟩ := exists_unit_isTotallyPositive_smul_of_norm_pos hmin hgen hux
    exact ⟨ε * u, by rwa [mul_smul]⟩
  · exact exists_unit_isTotallyPositive_smul_of_norm_pos hmin hgen hgt

/-- **A totally positive unit multiple of `θ` produces a unit of norm `-1`.** The converse of
`exists_unit_isTotallyPositive_smul_of_norm_eq_neg_one` for a real quadratic field: the scaling
unit itself is the unit of norm `-1`. -/
theorem norm_eq_neg_one_of_isTotallyPositive_smul_gen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hd : 0 < d) {v : (𝓞 K)ˣ}
    (hv : IsTotallyPositive (v • (θ : K))) :
    Algebra.norm ℚ (((v : 𝓞 K) : K)) = -1 := by
  -- `N(v • θ) = N(v) · (-d)` is positive and `0 < d`, so `N(v)` is negative; a unit has norm `±1`.
  have hvalue : (v : (𝓞 K)ˣ) • (θ : K) = ((v : 𝓞 K) : K) * (θ : K) := by
    simp [Units.smul_def, Algebra.smul_def]
  have hne : (v : (𝓞 K)ˣ) • (θ : K) ≠ 0 := by
    rw [hvalue]
    exact mul_ne_zero (RingOfIntegers.coe_ne_zero_iff.mpr v.ne_zero) (coe_gen_ne_zero hmin)
  have hpos := norm_pos_of_isTotallyPositive hne hv
  rw [hvalue, map_mul, norm_gen_eq_neg_radicand hmin hgen] at hpos
  have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  rcases mul_ringOfIntegersQuadraticConj_unit_eq_one_or_neg_one hmin hgen v with h | h
  · have hone : Algebra.norm ℚ (((v : 𝓞 K) : K)) = 1 :=
      (norm_eq_intCast_iff_mul_ringOfIntegersQuadraticConj_eq_intCast (n := 1) hmin hgen).mpr
        (by simpa using h)
    rw [hone] at hpos
    nlinarith
  · exact (norm_eq_intCast_iff_mul_ringOfIntegersQuadraticConj_eq_intCast (n := -1) hmin hgen).mpr
      (by simpa using h)

end NumberField
