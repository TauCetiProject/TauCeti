/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import TauCeti.NumberTheory.NumberField.TotallyPositive
import TauCeti.NumberTheory.ClassFieldTheory.Global.HasseNorm.Quadratic
import TauCeti.NumberTheory.ClassFieldTheory.Global.HasseNorm.SumTwoSquares
import TauCeti.NumberTheory.NumberField.CMField.Basic
import TauCeti.NumberTheory.NumberField.CMField.Unramified
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Sums of two squares in the maximal real subfield of a CM field

Let `K` be a CM field containing a primitive fourth and a primitive seventh root of unity, for
instance a primitive `5040`-th root of unity, and `K⁺` its maximal real subfield. Then `K = K⁺(i)`
with `i² = -1`, and `K / K⁺` is unramified at every finite place
(`NumberField.IsCMField.isUnramifiedAt_of_isPrimitiveRoot`). So every unit of a completion `K⁺_v`
at a finite place is a norm from `K`, that is a sum of two squares in `K⁺_v`
(`NumberField.IsCMField.exists_sq_add_sq_of_isPrimitiveRoot`).

Combined with the Hasse principle for sums of two squares, this gives the arithmetic input to
Landherr's theorem for hermitian forms over `K`
(`NumberField.IsCMField.exists_sq_add_sq_add_mul_eq_of_isPrimitiveRoot`): for `p, q, B ∈ K⁺` with
`p` totally positive and, at each finite place, `p` or `q` a unit, there are `a, b, c, d ∈ K⁺` with
`p = a² + c² + (q p - B²) (b² + d²)` and `a b + c d = 0`. So `p` is the value
`conj α * α + (q p - B²) * conj β * β` of the hermitian form `⟨1, q p - B²⟩` at `α = a + c i` and
`β = i (b + d i)`, for which `conj β * α` lies in `K⁺`.

## Main results

* `NumberField.IsCMField.exists_sq_add_sq_of_isPrimitiveRoot`: the units of the completions of
  `K⁺` are sums of two squares.
* `NumberField.IsCMField.exists_sq_add_sq_add_mul_eq_of_isPrimitiveRoot`: the input to Landherr's
  theorem.

## References

* W. Landherr, *Äquivalenz Hermitescher Formen über einem beliebigen algebraischen Zahlkörper*,
  Abh. Math. Sem. Univ. Hamburg 11 (1936), 245–248.
* J.-P. Serre, *Local Fields*, Chapter V, §2 (the norm of an unramified extension maps the units
  onto the units).

## Provenance

The second statement follows `New.exists_sq_add_sq_quadraticAlgebra` in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Adelic/Landherr.lean`, where the units are prescribed at places of `K` and the conclusion
is a norm from a quadratic algebra over `F[X] / (X² - (q p - B²))`; here the units are prescribed at
the places of `K⁺` and the conclusion is stated in coordinates over `K⁺`. Its local input
(`New.mem_closure_range_norm_of_apply_eq`, through the norms `conj y * y` of units of the integral
finite adeles of `K`) is replaced here by the unramifiedness of `K / K⁺`.
-/

public section

open IsDedekindDomain NumberField

namespace NumberField.IsCMField

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

/-- **Units of the completions of `K⁺` are sums of two squares.** Let `K` be a CM field containing
a primitive fourth and a primitive seventh root of unity. Then every unit `a` of the completion of
`K⁺` at a finite place is a sum of two squares in that completion. -/
theorem exists_sq_add_sq_of_isPrimitiveRoot {ζ₄ ζ₇ : K} (h₄ : IsPrimitiveRoot ζ₄ 4)
    (h₇ : IsPrimitiveRoot ζ₇ 7) (v : HeightOneSpectrum (𝓞 K⁺)) {a : v.adicCompletion K⁺}
    (ha : Valued.v a = 1) : ∃ x y : v.adicCompletion K⁺, a = x ^ 2 + y ^ 2 := by
  have hsq : ζ₄ ^ 2 = -1 := h₄.sq_eq_neg_one
  -- `ζ₄ * conj ζ₄ = 1` and `ζ₄² = -1`, so conjugation moves `ζ₄`, which is not in `K⁺`
  have hθ : ζ₄ ∉ Set.range (algebraMap K⁺ K) := by
    rintro ⟨r, hr⟩
    have h1 := mul_complexConj_eq_one_of_pow_eq four_ne_zero h₄.pow_eq_one (by simp)
    rw [← hr, AlgEquiv.commutes, ← sq, hr, hsq] at h1
    norm_num at h1
  -- `K / K⁺` is unramified at every place of `K` above `v`
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) v.asIdeal
  have hU : ∃ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
      Algebra.IsUnramifiedAt (𝓞 K⁺) w.val.asIdeal :=
    ⟨⟨⟨P, hP.isPrime, Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hP.isPrime, hPv⟩⟩, hPv⟩,
      isUnramifiedAt_of_isPrimitiveRoot h₄ h₇ P⟩
  obtain ⟨x, y, h⟩ := TauCeti.ClassFieldTheory.exists_sq_sub_mul_sq_of_isUnramifiedAt hθ
    (d := -1) (by rw [hsq, map_neg, map_one]) hU ha
  exact ⟨x, y, by rw [h, map_neg, map_one, neg_one_mul, sub_neg_eq_add]⟩

/-- **The arithmetic input to Landherr's theorem.** Let `K` be a CM field containing a primitive
fourth and a primitive seventh root of unity, and `p, q, B ∈ K⁺` with `p` totally positive, such
that at every finite place of `K⁺` the element `p` or the element `q` has valuation `1`. Then there
are `a, b, c, d ∈ K⁺` with `a² + c² + (q p - B²) (b² + d²) = p` and `a b + c d = 0`. -/
theorem exists_sq_add_sq_add_mul_eq_of_isPrimitiveRoot {ζ₄ ζ₇ : K} (h₄ : IsPrimitiveRoot ζ₄ 4)
    (h₇ : IsPrimitiveRoot ζ₇ 7) {p q : K⁺} (B : K⁺) (hp : IsTotallyPositive p)
    (hpq : ∀ v : HeightOneSpectrum (𝓞 K⁺), v.valuation K⁺ p = 1 ∨ v.valuation K⁺ q = 1) :
    ∃ a b c d : K⁺, a ^ 2 + c ^ 2 + (q * p - B ^ 2) * (b ^ 2 + d ^ 2) = p ∧
      a * b + c * d = 0 := by
  refine TauCeti.ClassFieldTheory.exists_sq_add_sq_add_mul_eq hp fun v ↦ ?_
  have hval (t : K⁺) (ht : v.valuation K⁺ t = 1) :
      Valued.v (algebraMap K⁺ (v.adicCompletion K⁺) t) = 1 := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ht]
  rcases hpq v with h | h
  · exact .inl (exists_sq_add_sq_of_isPrimitiveRoot h₄ h₇ v (hval p h))
  · refine .inr ⟨fun hq ↦ ?_, exists_sq_add_sq_of_isPrimitiveRoot h₄ h₇ v (hval q h)⟩
    rw [hq, map_zero] at h
    exact zero_ne_one h

end NumberField.IsCMField
