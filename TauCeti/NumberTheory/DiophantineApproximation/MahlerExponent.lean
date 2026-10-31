/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Polynomial.Norm
public import TauCeti.NumberTheory.DiophantineApproximation.LinearFormExponent
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.NumberTheory.NumberField.House
import TauCeti.Analysis.Polynomial.L1Norm
import TauCeti.Analysis.Polynomial.SupNorm.Basic
import TauCeti.FieldTheory.Minpoly.Primitive
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm

/-!
# Liouville's bound for Mahler's exponent of an algebraic number

Let `ξ` be an algebraic number of degree `D` over `ℚ`. A nonzero value of an integer polynomial
`P` of degree at most `n` at `ξ` cannot be too small: there is `c > 0`, depending only on `ξ` and
`n`, with `|P(ξ)| ≥ c H(P) ^ (-(D - 1))`, where `H(P)` is the largest absolute value of a
coefficient of `P`. Consequently Mahler's exponent satisfies `wₙ(ξ) ≤ D - 1` for every `n`.

The exponent is `D - 1` and not `D`. If `a` is the leading coefficient of the primitive minimal
polynomial of `ξ`, then `γ = (P.scaleRoots a)(a ξ) = a ^ (deg P) P(ξ)` is a nonzero algebraic
integer of `ℚ(ξ)`, so the product of its `D` conjugates, its norm, is a nonzero integer. The
conjugate at `ξ` itself is `a ^ (deg P) P(ξ)`, and only the other `D - 1` conjugates are bounded
above in terms of `H(P)`.

## Main results

* `IsAlgebraic.exists_pos_le_norm_aeval_mul_supNorm_pow`: **Liouville's inequality for the value
  of an integer polynomial**, `c ≤ |P(ξ)| H(P) ^ (D - 1)` for complex algebraic `ξ` and
  `P ∈ ℤ[X]` of degree at most `n` with `P(ξ) ≠ 0`.
* `IsAlgebraic.mahlerExponent_le`: for real algebraic `ξ` of degree `D`, `wₙ(ξ) ≤ D - 1`.
* `TauCeti.mahlerExponent_eq_of_natDegree_minpoly_eq`: for real `ξ` algebraic of degree `n + 1`,
  `wₙ(ξ) = n`, so the bound is attained.
* `TauCeti.mahlerExponent_ratCast`: rational numbers have Mahler exponent `0` in every degree.

## References

* Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge Tracts in Mathematics 160, 2004,
  Chapter 3.
-/

public section

open Polynomial NumberField
open scoped ENNReal IntermediateField

namespace TauCeti

/-- If `x = s g` is an algebraic integer, then the conjugate under `σ` of the algebraic integer
`(P.scaleRoots s)(x)` is `s ^ deg P P(σ g)`. -/
private theorem map_aeval_scaleRoots {F : Type*} [Field F] [NumberField F] (P : ℤ[X]) {s : ℤ}
    {g : F} {x : 𝓞 F} (hx : (x : F) = s • g) (σ : F →+* ℂ) :
    σ (aeval x (P.scaleRoots s) : F) = (s : ℂ) ^ P.natDegree * aeval (σ g) P := by
  have hσP : σ (aeval g P) = aeval (σ g) P := (aeval_algHom_apply σ.toIntAlgHom g P).symm
  rw [RingOfIntegers.coe_eq_algebraMap, ← aeval_algebraMap_apply,
    ← RingOfIntegers.coe_eq_algebraMap, hx, scaleRoots_aeval_smul, map_zsmul, hσP, zsmul_eq_mul,
    Int.cast_pow]

/-- The absolute value form of `map_aeval_scaleRoots`, for `0 ≤ s`. -/
private theorem norm_map_aeval_scaleRoots {F : Type*} [Field F] [NumberField F] (P : ℤ[X])
    {s : ℤ} (hs : 0 ≤ s) {g : F} {x : 𝓞 F} (hx : (x : F) = s • g) (σ : F →+* ℂ) :
    ‖σ (aeval x (P.scaleRoots s) : F)‖ = (s : ℝ) ^ P.natDegree * ‖aeval (σ g) P‖ := by
  rw [map_aeval_scaleRoots P hx, norm_mul, norm_pow, Complex.norm_intCast,
    abs_of_nonneg (by exact_mod_cast hs : (0 : ℝ) ≤ s)]

end TauCeti

open TauCeti

/-- **Liouville's inequality for the value of an integer polynomial.** Let `ξ ∈ ℂ` be algebraic
of degree `D` over `ℚ` and let `n ∈ ℕ`. There is `c > 0` such that every `P ∈ ℤ[X]` of degree at
most `n` with `P(ξ) ≠ 0` satisfies `c ≤ |P(ξ)| H(P) ^ (D - 1)`, where `H(P)` is the coefficient
sup norm of `P`. -/
theorem IsAlgebraic.exists_pos_le_norm_aeval_mul_supNorm_pow {ξ : ℂ} (hξ : IsAlgebraic ℚ ξ)
    (n : ℕ) : ∃ c > 0, ∀ P : ℤ[X], P.natDegree ≤ n → aeval ξ P ≠ 0 →
      c ≤ ‖aeval ξ P‖ * P.supNorm ^ ((minpoly ℚ ξ).natDegree - 1) := by
  -- Work in the number field `F = ℚ(ξ)`, with `g ∈ F` the generator, and `s` the leading
  -- coefficient of the primitive minimal polynomial of `g`, so that `s g` is an algebraic integer.
  set F := ℚ⟮ξ⟯
  have : FiniteDimensional ℚ F := IntermediateField.adjoin.finiteDimensional hξ.isIntegral
  have : NumberField F := ⟨⟩
  set g : F := IntermediateField.AdjoinSimple.gen ℚ ξ
  set s : ℤ := (primitiveMinpoly g).leadingCoeff
  have hs : 0 < s := leadingCoeff_primitiveMinpoly_pos g
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsg : IsIntegral ℤ (s • g) :=
    isIntegral_leadingCoeff_primitiveMinpoly_smul (Algebra.IsAlgebraic.isAlgebraic g)
  set x : 𝓞 F := ⟨s • g, hsg⟩
  have hx : (x : F) = s • g := RingOfIntegers.coe_mk hsg
  set D := (minpoly ℚ ξ).natDegree
  have hD : Module.finrank ℚ F = D := IntermediateField.adjoin.finrank hξ.isIntegral
  -- `R` bounds every conjugate of `ξ`; the constant `B` is chosen so that `B H(P)` bounds every
  -- conjugate of the algebraic integer `γ` attached to `P` further down.
  set R : ℝ := max 1 (house g)
  have hR (σ : F →+* ℂ) : max 1 ‖σ g‖ ≤ R := max_le_max le_rfl (norm_embedding_le_house g σ)
  set B : ℝ := (s : ℝ) ^ n * ((n + 1) * R ^ n)
  have hB : 0 < B := by positivity
  refine ⟨((s : ℝ) ^ n * B ^ (D - 1))⁻¹, by positivity, fun P hP hPξ ↦ ?_⟩
  set d := P.natDegree
  have hH := P.supNorm_nonneg
  set σ₀ : F →+* ℂ := (IntermediateField.val F).toRingHom
  have hσ₀ : σ₀ g = ξ := IntermediateField.AdjoinSimple.coe_gen ℚ ξ
  -- The algebraic integer `γ = (P.scaleRoots s)(s g)` has conjugates `σ γ = s ^ d P(σ g)`.
  set γ : 𝓞 F := aeval x (P.scaleRoots s)
  have hγ (σ : F →+* ℂ) : ‖σ (γ : F)‖ = (s : ℝ) ^ d * ‖aeval (σ g) P‖ :=
    norm_map_aeval_scaleRoots P hs.le hx σ
  have hγ0 : γ ≠ 0 := by
    refine fun h0 ↦ (mul_pos (pow_pos (zero_lt_one.trans_le hs1) d) (norm_pos_iff.2 hPξ)).ne' ?_
    rw [← hσ₀, ← hγ σ₀, h0]
    simp
  have hsd : (s : ℝ) ^ d ≤ (s : ℝ) ^ n := pow_le_pow_right₀ hs1 hP
  -- Every conjugate of `γ`, and hence its house, is at most `B H(P)`.
  have hhouse : house (γ : F) ≤ B * P.supNorm := by
    obtain ⟨σ, -, hσ⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty fun φ : F →+* ℂ ↦ ‖φ γ‖₊
    rw [house_eq_sup', hσ, coe_nnnorm, hγ]
    calc (s : ℝ) ^ d * ‖aeval (σ g) P‖
        ≤ (s : ℝ) ^ n * ((n + 1) * P.supNorm * max 1 ‖σ g‖ ^ n) := by
          gcongr
          rw [aeval_def, algebraMap_int_eq, ← eval_map, ← P.supNorm_map (Int.castRingHom ℂ)]
          exact norm_eval_le_add_one_mul_supNorm_mul (natDegree_map_le.trans hP) _
      _ ≤ (s : ℝ) ^ n * ((n + 1) * P.supNorm * R ^ n) := by
          gcongr
          exact hR σ
      _ = B * P.supNorm := by ring
  -- Since `γ` is a nonzero algebraic integer, its conjugate `σ₀ γ = s ^ d P(ξ)` is bounded below
  -- in terms of the bound `B H(P)` on its other conjugates.
  have key : 1 ≤ ‖σ₀ γ‖ * house (γ : F) ^ (D - 1) := by
    simpa [← Rat.norm_cast_real, hD] using
      (RingOfIntegers.one_le_abs_norm hγ0).trans (norm_norm_le_norm_mul_house_pow (γ : F) σ₀)
  rw [hγ, hσ₀] at key
  have := house_nonneg (γ : F)
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  calc (1 : ℝ) ≤ (s : ℝ) ^ d * ‖aeval ξ P‖ * house (γ : F) ^ (D - 1) := key
    _ ≤ (s : ℝ) ^ n * ‖aeval ξ P‖ * (B * P.supNorm) ^ (D - 1) := by gcongr
    _ = ‖aeval ξ P‖ * P.supNorm ^ (D - 1) * ((s : ℝ) ^ n * B ^ (D - 1)) := by
          rw [mul_pow]; ring

/-- **Liouville's bound for Mahler's exponent.** If `ξ` is a real algebraic number of degree `D`
over `ℚ`, then `wₙ(ξ) ≤ D - 1` for every `n`. -/
theorem IsAlgebraic.mahlerExponent_le {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) (n : ℕ) :
    mahlerExponent n ξ ≤ ((minpoly ℚ ξ).natDegree - 1 : ℕ) := by
  have hξℂ : IsAlgebraic ℚ (ξ : ℂ) := hξ.algebraMap
  obtain ⟨c, hc, hLiou⟩ := hξℂ.exists_pos_le_norm_aeval_mul_supNorm_pow n
  rw [show minpoly ℚ (ξ : ℂ) = minpoly ℚ ξ from
    minpoly.algebraMap_eq (algebraMap ℝ ℂ).injective ξ] at hLiou
  set e := (minpoly ℚ ξ).natDegree - 1
  rw [mahlerExponent_def, linearFormExponent_le_iff]
  intro w hw
  rw [← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal (not_lt.1 fun hew ↦ hw ?_)
  -- For `w > e`, Liouville's inequality bounds the sup norm of every solution.
  refine ((isCompact_closedBall (0 : ℤ × (Fin n → ℤ)) (c ^ ((e : ℝ) - w)⁻¹)).finite_of_discrete
    ).subset fun x hx ↦ ?_
  rw [mem_linearFormApproximations] at hx
  rw [mem_closedBall_zero_iff]
  set L : ℝ := x.1 + ∑ j, x.2 j * ξ ^ (j.val + 1)
  have hL : ‖aeval (ξ : ℂ) (linearFormPoly x)‖ = |L| := by
    rw [aeval_linearFormPoly, ← Real.norm_eq_abs, ← Complex.norm_real]
    simp [L]
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 fun h ↦ by simp [L, h] at hx
  have hc' : c ≤ ‖x‖ ^ ((e : ℝ) - w) := by
    calc c ≤ |L| * (linearFormPoly x).supNorm ^ e := by
          rw [← hL]
          refine hLiou _ (natDegree_linearFormPoly_le x) fun h ↦ ?_
          rw [h, norm_zero] at hL
          exact hx.1.ne hL
      _ ≤ ‖x‖ ^ (-w) * ‖x‖ ^ e := by
          have := (linearFormPoly x).supNorm_nonneg
          gcongr
          · exact hx.2
          · exact supNorm_linearFormPoly_le x
      _ = ‖x‖ ^ ((e : ℝ) - w) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
          ring_nf
  calc ‖x‖ = (‖x‖ ^ ((e : ℝ) - w)) ^ ((e : ℝ) - w)⁻¹ :=
        (Real.rpow_rpow_inv hx0.le (by linarith)).symm
    _ ≤ c ^ ((e : ℝ) - w)⁻¹ := Real.rpow_le_rpow_of_nonpos hc hc' (inv_nonpos.2 (by linarith))

namespace TauCeti

/-- For a real algebraic number `ξ` of degree `n + 1` over `ℚ`, Mahler's exponent in degree `n` is
exactly `n`, so Liouville's bound `wₙ(ξ) ≤ D - 1` is attained for `D = n + 1`. For instance,
`w₁(ξ) = 1` for every real quadratic irrational `ξ`. -/
theorem mahlerExponent_eq_of_natDegree_minpoly_eq {ξ : ℝ} {n : ℕ}
    (hn : (minpoly ℚ ξ).natDegree = n + 1) : mahlerExponent n ξ = n := by
  have hξ : IsAlgebraic ℚ ξ :=
    (by_contra fun h ↦ by simp [minpoly.eq_zero h] at hn : IsIntegral ℚ ξ).isAlgebraic
  refine le_antisymm ?_ (natCast_le_mahlerExponent fun h ↦ by omega)
  simpa [hn] using hξ.mahlerExponent_le n

/-- Rational numbers have Mahler exponent `0` in every degree. -/
@[simp]
theorem mahlerExponent_ratCast (n : ℕ) (q : ℚ) : mahlerExponent n q = 0 := by
  have h := (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) q).mahlerExponent_le n
  rw [minpoly.eq_X_sub_C] at h
  simpa using h

end TauCeti
