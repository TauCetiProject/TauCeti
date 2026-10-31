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
import TauCeti.Analysis.Polynomial.L1Norm
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
* `IsAlgebraic.mahlerExponent_eq_of_natDegree_minpoly_eq`: for real algebraic `ξ` of degree
  `n + 1`, `wₙ(ξ) = n`, so the bound is attained.
* `TauCeti.mahlerExponent_ratCast`: rational numbers have Mahler exponent `0` in every degree.

## References

* Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge Tracts in Mathematics 160, 2004,
  Chapter 3.
-/

public section

open Polynomial NumberField
open scoped ENNReal IntermediateField

namespace TauCeti

/-- The trivial bound for the value of an integer polynomial of degree at most `n` at a complex
number: `|P(z)| ≤ (n + 1) H(P) max(1, |z|) ^ n`. -/
private theorem norm_aeval_le {n : ℕ} {P : ℤ[X]} (hP : P.natDegree ≤ n) (z : ℂ) :
    ‖aeval z P‖ ≤ (n + 1) * P.supNorm * max 1 ‖z‖ ^ n := by
  have hmap : aeval z P = (P.map (Int.castRingHom ℂ)).eval z := by
    rw [aeval_def, eval_map, algebraMap_int_eq]
  have hl1 : (P.map (Int.castRingHom ℂ)).l1Norm ≤ (n + 1) * P.supNorm := by
    rw [l1Norm_map _ _ fun x ↦ by simp [Int.norm_eq_abs]]
    refine P.l1Norm_le_natDegree_add_one_mul_supNorm.trans ?_
    have := P.supNorm_nonneg
    gcongr
  rw [hmap]
  refine (norm_eval_le_l1Norm_mul _ z).trans ?_
  have := P.supNorm_nonneg
  gcongr
  · exact le_max_left _ _
  · exact natDegree_map_le.trans hP

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
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast leadingCoeff_primitiveMinpoly_pos g
  set x : 𝓞 F := ⟨s • g, isIntegral_leadingCoeff_primitiveMinpoly_smul
    (Algebra.IsAlgebraic.isAlgebraic g)⟩
  set D := (minpoly ℚ ξ).natDegree
  have hD : Module.finrank ℚ F = D := IntermediateField.adjoin.finrank hξ.isIntegral
  -- `R` bounds every conjugate of `ξ`; the constant `B` is chosen so that `B H(P)` bounds every
  -- conjugate of the algebraic integer `γ` attached to `P` further down.
  set R : ℝ := 1 + ∑ σ : F →ₐ[ℚ] ℂ, ‖σ g‖
  have hR (σ : F →ₐ[ℚ] ℂ) : max 1 ‖σ g‖ ≤ R :=
    max_le (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
      (le_add_of_nonneg_of_le zero_le_one
        (Finset.single_le_sum (f := (‖· g‖)) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ σ)))
  set B : ℝ := (s : ℝ) ^ n * ((n + 1) * R ^ n)
  have hB : 0 < B := by positivity
  refine ⟨((s : ℝ) ^ n * B ^ (D - 1))⁻¹, by positivity, fun P hP hPξ ↦ ?_⟩
  set d := P.natDegree
  have hH := P.supNorm_nonneg
  set σ₀ : F →ₐ[ℚ] ℂ := IntermediateField.val F
  have hσ₀ : σ₀ g = ξ := IntermediateField.AdjoinSimple.coe_gen ℚ ξ
  -- The algebraic integer `γ = (P.scaleRoots s)(s g)` has conjugates `σ γ = s ^ d P(σ g)`.
  set γ : 𝓞 F := aeval x (P.scaleRoots s)
  have hγ (σ : F →ₐ[ℚ] ℂ) : σ (γ : F) = (s : ℂ) ^ d * aeval (σ g) P := by
    have h : (γ : F) = s ^ d • aeval g P := by
      rw [← scaleRoots_aeval_smul]
      exact (aeval_algebraMap_apply F x (P.scaleRoots s)).symm
    have hσP : σ (aeval g P) = aeval (σ g) P :=
      (aeval_algHom_apply (σ : F →+* ℂ).toIntAlgHom g P).symm
    rw [h, map_zsmul, hσP, zsmul_eq_mul, Int.cast_pow]
  have hγ0 : γ ≠ 0 := by
    rintro h0
    have h := hγ σ₀
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (leadingCoeff_primitiveMinpoly_pos g).ne'
    rw [h0, hσ₀] at h
    exact mul_ne_zero (pow_ne_zero _ hs0) hPξ (by simpa using h.symm)
  have hsd : (s : ℝ) ^ d ≤ (s : ℝ) ^ n := pow_le_pow_right₀ hs hP
  have hbound (σ : F →ₐ[ℚ] ℂ) : ‖σ (γ : F)‖ ≤ B * P.supNorm := by
    rw [hγ, norm_mul, norm_pow, Complex.norm_intCast, abs_of_nonneg (by linarith)]
    calc (s : ℝ) ^ d * ‖aeval (σ g) P‖
        ≤ (s : ℝ) ^ n * ((n + 1) * P.supNorm * max 1 ‖σ g‖ ^ n) := by
          gcongr
          exact norm_aeval_le hP _
      _ ≤ (s : ℝ) ^ n * ((n + 1) * P.supNorm * R ^ n) := by
          gcongr
          exact hR σ
      _ = B * P.supNorm := by ring
  -- Since `γ` is a nonzero algebraic integer, its conjugate `σ₀ γ = s ^ d P(ξ)` is bounded below
  -- in terms of the bound `B H(P)` on all its conjugates.
  have key := RingOfIntegers.one_le_norm_mul_pow_of_forall_norm_le hγ0 σ₀ hbound
  rw [hγ, hσ₀, norm_mul, norm_pow, Complex.norm_intCast, abs_of_nonneg (by linarith), hD] at key
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  calc (1 : ℝ) ≤ (s : ℝ) ^ d * ‖aeval ξ P‖ * (B * P.supNorm) ^ (D - 1) := key
    _ ≤ (s : ℝ) ^ n * ‖aeval ξ P‖ * (B * P.supNorm) ^ (D - 1) := by gcongr
    _ = ‖aeval ξ P‖ * P.supNorm ^ (D - 1) * ((s : ℝ) ^ n * B ^ (D - 1)) := by
          rw [mul_pow]; ring

namespace TauCeti

/-- The integer polynomial `x₀ + ∑ j, xⱼ X ^ (j + 1)`, whose value at `ξ` is the linear form of
`x` at the powers `ξ, ξ ^ 2, …, ξ ^ n`. -/
private noncomputable def linearFormPoly {n : ℕ} (x : ℤ × (Fin n → ℤ)) : ℤ[X] :=
  C x.1 + ∑ j, C (x.2 j) * X ^ (j.val + 1)

private theorem natDegree_linearFormPoly_le {n : ℕ} (x : ℤ × (Fin n → ℤ)) :
    (linearFormPoly x).natDegree ≤ n :=
  (natDegree_add_le _ _).trans <| max_le (by simp) <| natDegree_sum_le_of_forall_le _ _
    fun j _ ↦ (natDegree_C_mul_X_pow_le _ _).trans j.isLt

private theorem aeval_linearFormPoly {n : ℕ} (x : ℤ × (Fin n → ℤ)) (ξ : ℝ) :
    aeval (ξ : ℂ) (linearFormPoly x) = ((x.1 + ∑ j, x.2 j * ξ ^ (j.val + 1) : ℝ) : ℂ) := by
  simp [linearFormPoly]

private theorem supNorm_linearFormPoly_le {n : ℕ} (x : ℤ × (Fin n → ℤ)) :
    (linearFormPoly x).supNorm ≤ ‖x‖ := by
  rw [supNorm_eq_iSup]
  refine ciSup_le fun i ↦ ?_
  simp only [linearFormPoly, coeff_add, coeff_C, finsetSum_coeff, coeff_C_mul_X_pow]
  rcases i with _ | k
  · simpa using norm_fst_le x
  · by_cases hk : k < n
    · have h (j : Fin n) : k = j.val ↔ ⟨k, hk⟩ = j := (Fin.ext_iff (a := ⟨k, hk⟩)).symm
      simpa [h] using (norm_le_pi_norm x.2 ⟨k, hk⟩).trans (norm_snd_le x)
    · have h (j : Fin n) : k ≠ j.val := by
        have := j.isLt
        omega
      simp [h]

end TauCeti

open TauCeti

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
    rw [aeval_linearFormPoly, Complex.norm_real, Real.norm_eq_abs]
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

/-- For a real algebraic number `ξ` of degree `n + 1` over `ℚ`, Mahler's exponent in degree `n` is
exactly `n`, so Liouville's bound `wₙ(ξ) ≤ D - 1` is attained for `D = n + 1`. For instance,
`w₁(ξ) = 1` for every real quadratic irrational `ξ`. -/
theorem IsAlgebraic.mahlerExponent_eq_of_natDegree_minpoly_eq {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ)
    {n : ℕ} (hn : (minpoly ℚ ξ).natDegree = n + 1) : mahlerExponent n ξ = n := by
  refine le_antisymm ?_ (natCast_le_mahlerExponent fun h ↦ by omega)
  simpa [hn] using hξ.mahlerExponent_le n

namespace TauCeti

/-- Rational numbers have Mahler exponent `0` in every degree. -/
@[simp]
theorem mahlerExponent_ratCast (n : ℕ) (q : ℚ) : mahlerExponent n q = 0 := by
  have h := (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) q).mahlerExponent_le n
  rwa [minpoly.eq_X_sub_C, natDegree_X_sub_C, Nat.sub_self, Nat.cast_zero, nonpos_iff_eq_zero,
    eq_ratCast] at h

end TauCeti
