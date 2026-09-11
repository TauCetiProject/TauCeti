/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Discriminant
public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.FieldTheory.Trace
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension

/-!
# Basics for quadratic number fields

Shared facts about a quadratic number field `K` presented by an algebraic integer `θ : 𝓞 K` whose
minimal polynomial over `ℤ` is `X² - d`. These feed the prime-splitting law
(`Quadratic/Splitting.lean`), the conjugation automorphism (`Quadratic/Conjugation/Basic.lean`), the
ring-of-integers/discriminant computation (`Quadratic/RingOfIntegers.lean`), and the field-norm
computation (`Quadratic/Norm.lean`).

## Main results

* `NumberField.minpoly_rat_quadratic`: the minimal polynomial of `θ` over `ℚ` is `X² - d`.
* `NumberField.finrank_rat_eq_two`: `K` has degree `2` over `ℚ`.
* `NumberField.gen_sq`: the integral generator squares to the radicand in `𝓞 K`.
* `NumberField.coe_gen_sq`: the generator squares to the radicand, `θ² = d` in `K`.
* `NumberField.coe_gen_sq_ratCast`: the same over `ℚ`, `θ² = (d : ℚ)` in `K`.
* `NumberField.gen_notMem_range`: the generator is not rational, `θ ∉ ℚ`.
* `NumberField.coe_gen_ne_zero`: the generator is nonzero.
* `NumberField.exists_eq_add_mul_gen`: every element of `K` is `b + aθ`.
* `NumberField.not_isSquare_radicand`: the radicand is not a rational square.
* `NumberField.exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top`: every number field of degree `2`
  over `ℚ` has such a presentation, with squarefree radicand.
* `NumberField.trace_gen_eq_zero`: the trace of the generator is `0`.
* `NumberField.discr_one_gen`: the discriminant of `{1, θ}` over `ℚ` is `4d`.
* `NumberField.discr_one_halfGen`: the discriminant of `{1, (1+θ)/2}` over `ℚ` is `d`.

The trace and discriminant computations reuse the generic quadratic-extension API
`NumberField.trace_eq_zero_of_sq_ratCast` and
`TauCeti.Algebra.discr_one_elem_eq_of_sq_algebraMap` from `TauCeti.FieldTheory.Trace`.
-/

public section

open Polynomial NumberField Module
open scoped Matrix

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- The minimal polynomial of `θ` over `ℚ` is `X² - d`, obtained from its minimal polynomial over
`ℤ` by base change along `ℤ → ℚ`. -/
theorem minpoly_rat_quadratic (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    minpoly ℚ (θ : K) = X ^ 2 - C ((d : ℤ) : ℚ) := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions ℚ K (IsIntegralClosure.isIntegral ℤ K θ), hmin]
  simp [Polynomial.map_sub, Polynomial.map_pow]

/-- The quadratic field `K = ℚ(θ)` has degree `2` over `ℚ`: its power basis has dimension
`natDegree (X² - d) = 2`. -/
theorem finrank_rat_eq_two (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : finrank ℚ K = 2 := by
  have hint : IsIntegral ℚ (θ : K) := θ.isIntegral_coe.tower_top
  rw [(PowerBasis.ofAdjoinEqTop' hint hgen).finrank,
    ← (PowerBasis.ofAdjoinEqTop' hint hgen).natDegree_minpoly, PowerBasis.ofAdjoinEqTop'_gen,
    minpoly_rat_quadratic hmin, natDegree_X_pow_sub_C]

omit [NumberField K] in
/-- The integral generator squares to the radicand: `θ² = d` in `𝓞 K`. -/
@[simp] theorem gen_sq (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    θ ^ 2 = algebraMap ℤ (𝓞 K) d := by
  have hae := minpoly.aeval ℤ θ
  rw [hmin] at hae
  have h2 : θ ^ 2 - algebraMap ℤ (𝓞 K) d = 0 := by
    simpa [map_sub, map_pow, aeval_X, aeval_C] using hae
  linear_combination h2

omit [NumberField K] in
/-- The generator squares to the radicand in `K`: `θ² = d`. -/
@[simp] theorem coe_gen_sq (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    (θ : K) ^ 2 = algebraMap ℤ K d := by
  have := congrArg (algebraMap (𝓞 K) K) (gen_sq hmin)
  rwa [map_pow, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K] at this

omit [NumberField K] in
/-- The generator squares to the radicand viewed over `ℚ`: `θ² = (d : ℚ)` in `K`. This is
`coe_gen_sq` transported along `ℤ → ℚ → K`, the form fed to the generic square-root-basis API. -/
theorem coe_gen_sq_ratCast [CharZero K] (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    (θ : K) ^ 2 = algebraMap ℚ K ((d : ℤ) : ℚ) := by
  rw [coe_gen_sq hmin, IsScalarTower.algebraMap_apply ℤ ℚ K]; norm_num

/-- The generator is irrational: `θ ∉ ℚ`. -/
theorem gen_notMem_range (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    (θ : K) ∉ (algebraMap ℚ K).range := by
  -- Were `θ = q ∈ ℚ`, its `ℚ`-minimal polynomial would divide `X - q`, so have degree `≤ 1`,
  -- contradicting `minpoly ℚ θ = X² - d`.
  rintro ⟨q, hq⟩
  have hdvd : minpoly ℚ (algebraMap ℚ K q) ∣ (X - C q) := minpoly.dvd ℚ _ (by simp)
  have h1 : (minpoly ℚ (algebraMap ℚ K q)).natDegree ≤ 1 := by
    simpa [natDegree_X_sub_C] using Polynomial.natDegree_le_of_dvd hdvd (X_sub_C_ne_zero q)
  rw [hq, minpoly_rat_quadratic hmin, natDegree_X_pow_sub_C] at h1
  norm_num at h1

/-- The generator of a quadratic presentation is **nonzero**: it is irrational
(`gen_notMem_range`), whereas `0` is rational. -/
theorem coe_gen_ne_zero (hmin : minpoly ℤ θ = X ^ 2 - C d) : (θ : K) ≠ 0 := fun h0 =>
  gen_notMem_range hmin ⟨0, by rw [map_zero, h0]⟩

/-- **Every element of a quadratic field is `b + aθ`** for rationals `a, b`. -/
theorem exists_eq_add_mul_gen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (x : K) :
    ∃ a b : ℚ, x = algebraMap ℚ K b + algebraMap ℚ K a * (θ : K) := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨finrank_rat_eq_two hmin hgen⟩
  exact Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul ℚ K
    (gen_notMem_range hmin) x

/-- **The radicand of a quadratic presentation is not a rational square.** Were `d = q²`, the
factorization `(θ - q)(θ + q) = θ² - d = 0` would force `θ = ±q ∈ ℚ`. -/
theorem not_isSquare_radicand (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    ¬ IsSquare (((d : ℤ) : ℚ)) := by
  rintro ⟨q, hq⟩
  have hθ : (θ : K) ^ 2 = algebraMap ℚ K ((d : ℤ) : ℚ) := coe_gen_sq_ratCast hmin
  have hq' : algebraMap ℚ K ((d : ℤ) : ℚ) = algebraMap ℚ K q * algebraMap ℚ K q := by
    rw [← map_mul, ← hq]
  have hfac : ((θ : K) - algebraMap ℚ K q) * ((θ : K) + algebraMap ℚ K q) = 0 := by
    linear_combination hθ + hq'
  rcases mul_eq_zero.mp hfac with h | h
  · exact gen_notMem_range hmin ⟨q, by linear_combination -h⟩
  · exact gen_notMem_range hmin ⟨-q, by rw [map_neg]; linear_combination -h⟩

/-- An irrational square root of an integer presents a quadratic field: if `z : K` is irrational
and `z² = n` for an integer `n`, then `z` is an algebraic integer with minimal polynomial `X² - n`
generating `K` over `ℚ`. -/
private theorem exists_gen_of_sq_eq_intCast [Algebra.IsQuadraticExtension ℚ K] {z : K} {n : ℤ}
    (hz2 : z ^ 2 = (n : K)) (hzQ : z ∉ Set.range (algebraMap ℚ K)) :
    ∃ θ : 𝓞 K, minpoly ℤ θ = X ^ 2 - C n ∧ Algebra.adjoin ℚ {(θ : K)} = ⊤ := by
  have hpz : aeval z (X ^ 2 - C n) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hz2, algebraMap_int_eq, eq_intCast, sub_self]
  have hint : IsIntegral ℤ z := ⟨_, monic_X_pow_sub_C _ two_ne_zero, hpz⟩
  refine ⟨⟨z, hint⟩, ?_, ?_⟩
  · set θ : 𝓞 K := ⟨z, hint⟩
    have hθ : IsIntegral ℤ θ := RingOfIntegers.isIntegral θ
    have hpθ : aeval θ (X ^ 2 - C n) = 0 :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K <| by
        rw [← aeval_algebraMap_apply, map_zero]
        exact hpz
    refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hθ)
      (monic_X_pow_sub_C _ two_ne_zero) (minpoly.isIntegrallyClosed_dvd hθ hpθ) ?_).symm
    -- The minimal polynomial of the irrational `θ` has degree at least `2`.
    have hrat := minpoly.isIntegrallyClosed_eq_field_fractions ℚ K hθ
    have hpos := minpoly.natDegree_pos (hint.tower_top (A := ℚ))
    have hne : (minpoly ℚ z).natDegree ≠ 1 := fun h => hzQ (minpoly.natDegree_eq_one_iff.mp h)
    -- `θ` is the bundled `⟨z, hint⟩`, so its image in `K` is `z` by `RingOfIntegers.map_mk`.
    have hθz : algebraMap (𝓞 K) K θ = z := RingOfIntegers.map_mk z hint
    rw [natDegree_X_pow_sub_C, ← (minpoly.monic hθ).natDegree_map (algebraMap ℤ ℚ), ← hrat, hθz]
    omega
  · rw [eq_top_iff]
    intro w _
    obtain ⟨p, q, rfl⟩ :=
      Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul ℚ K hzQ w
    exact add_mem (Subalgebra.algebraMap_mem _ q)
      (mul_mem (Subalgebra.algebraMap_mem _ p) (Algebra.self_mem_adjoin_singleton ℚ z))

/-- **Every quadratic number field has a quadratic presentation with squarefree radicand.** If
`[K : ℚ] = 2` there is an algebraic integer `θ : 𝓞 K` generating `K` over `ℚ` whose minimal
polynomial over `ℤ` is `X² - d` for a squarefree integer `d`. So any statement proved under the
hypotheses `minpoly ℤ θ = X ^ 2 - C d`, `Algebra.adjoin ℚ {(θ : K)} = ⊤` and `Squarefree d` whose
conclusion does not mention `θ` or `d` holds for every quadratic field.

Take any irrational `x ∈ K` and write `x² = b + ax`; completing the square, `2x - a` squares to the
rational `e = a² + 4b`, and scaling by the denominator of `e` makes the square an integer `n`.
Writing `n = m²d` with `d` squarefree, the irrational `z / m` squares to `d`. -/
theorem exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top (hK : finrank ℚ K = 2) :
    ∃ (θ : 𝓞 K) (d : ℤ), minpoly ℤ θ = X ^ 2 - C d ∧ Algebra.adjoin ℚ {(θ : K)} = ⊤ ∧
      Squarefree d := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  obtain ⟨x, hx⟩ := Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap ℚ K
  obtain ⟨a, b, hab⟩ :=
    Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul ℚ K hx (x ^ 2)
  set e : ℚ := a ^ 2 + 4 * b with he
  have hden : (e.den : K) ≠ 0 := Nat.cast_ne_zero.mpr e.den_nz
  set z : K := (e.den : K) * (2 * x - algebraMap ℚ K a) with hz
  -- `z² = e.num * e.den`, an integer.
  have hz2 : z ^ 2 = ((e.num * e.den : ℤ) : K) := by
    have hsq : (2 * x - algebraMap ℚ K a) ^ 2 = algebraMap ℚ K e := by
      rw [he, map_add, map_pow, map_mul, map_ofNat]
      linear_combination 4 * hab
    rw [hz, mul_pow, hsq, eq_ratCast, Rat.cast_def]
    push_cast
    field_simp
  -- `z` is irrational, since `x = (z / e.den + a) / 2` is.
  have hzQ : z ∉ Set.range (algebraMap ℚ K) := by
    rintro ⟨q, hq⟩
    refine hx ⟨(q / e.den + a) / 2, ?_⟩
    rw [map_div₀, map_add, map_div₀, hq, hz, map_natCast, map_ofNat]
    field_simp
    ring
  -- The radicand is nonzero, since `z` is irrational.
  have hn0 : (e.num * e.den : ℤ) ≠ 0 := fun h0 =>
    hzQ ⟨0, by rw [map_zero]; exact ((pow_eq_zero_iff two_ne_zero).mp (by rw [hz2, h0]; simp)).symm⟩
  -- Split off the square part `m²` of the radicand; the square root shrinks by `m`.
  obtain ⟨m, n, hmn, hsf⟩ := exists_sq_mul_squarefree (e.num * e.den)
  have hm0 : (m : K) ≠ 0 := Int.cast_ne_zero.mpr fun h0 => hn0 (by simpa [h0] using hmn.symm)
  have hw2 : (z / (m : K)) ^ 2 = (n : K) := by
    have hcast : ((e.num * e.den : ℤ) : K) = (m : K) ^ 2 * (n : K) := by
      rw [← hmn]; push_cast; ring
    rw [div_pow, hz2, hcast, mul_comm, mul_div_assoc, div_self (pow_ne_zero 2 hm0), mul_one]
  have hwQ : z / (m : K) ∉ Set.range (algebraMap ℚ K) := by
    rintro ⟨q, hq⟩
    exact hzQ ⟨q * (m : ℚ), by
      rw [map_mul, hq, map_intCast, div_mul_cancel₀ _ hm0]⟩
  obtain ⟨θ, hmin, hgen⟩ := exists_gen_of_sq_eq_intCast hw2 hwQ
  exact ⟨θ, n, hmin, hgen, hsf⟩

/-- The trace of the generator vanishes: `Tr(θ) = 0`. -/
theorem trace_gen_eq_zero (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    Algebra.trace ℚ K (θ : K) = 0 := by
  -- Specialise the generic `trace_eq_zero_of_sq_ratCast` to `θ² = d` and the irrationality of `θ`.
  have hd' : (θ : K) ^ 2 = algebraMap ℚ K ((d : ℤ) : ℚ) := coe_gen_sq_ratCast hmin
  exact trace_eq_zero_of_sq_ratCast hd' (gen_notMem_range hmin)

/-- The discriminant of the `ℚ`-family `{1, θ}` is `4d`. -/
theorem discr_one_gen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.discr ℚ ![(1 : K), (θ : K)] = ((4 * d : ℤ) : ℚ) := by
  -- Specialise the generic square-root-basis discriminant `discr_one_elem_eq_of_sq_algebraMap`.
  have hd' : (θ : K) ^ 2 = algebraMap ℚ K ((d : ℤ) : ℚ) := coe_gen_sq_ratCast hmin
  rw [TauCeti.Algebra.discr_one_elem_eq_of_sq_algebraMap (finrank_rat_eq_two hmin hgen) hd'
    (gen_notMem_range hmin)]
  push_cast; ring

/-- The discriminant of the `ℚ`-family `{1, (1+θ)/2}` is `d`. -/
theorem discr_one_halfGen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.discr ℚ ![(1 : K), (1 + (θ : K)) / 2] = ((d : ℤ) : ℚ) := by
  -- Change of basis from `{1, θ}` by `!![1, 0; 1/2, 1/2]` (determinant `1/2`): `(1/2)² · 4d = d`.
  have hP : ![(1 : K), (1 + (θ : K)) / 2]
      = (!![1, 0; 1 / 2, 1 / 2] : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ K) *ᵥ
          ![(1 : K), (θ : K)] := by
    funext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [hP, Algebra.discr_of_matrix_mulVec, discr_one_gen hmin hgen, Matrix.det_fin_two_of]
  push_cast; ring

end NumberField
