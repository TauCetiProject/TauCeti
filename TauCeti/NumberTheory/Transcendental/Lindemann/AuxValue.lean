/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.NumberTheory.Transcendental.Lindemann.AuxPoly
public import TauCeti.NumberTheory.Transcendental.Lindemann.ExpSum
public import TauCeti.NumberTheory.Transcendental.Lindemann.HermiteIntegral

import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Int.Basic
import Mathlib.Topology.Algebra.Order.Floor
import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# The auxiliary values of the Lindemann–Weierstrass theorem

Let `x = ∑ δ_γ' [γ']` be a formal exponential sum over a field `K`, with support `S` of
cardinality `t`, and let `f = auxPoly S l p γ` be the auxiliary polynomial of Hermite's proof of
the Lindemann–Weierstrass theorem. The auxiliary value is
`auxValue x l p γ = -∑_{γ' ∈ S} δ_γ' (sumIDeriv f)(γ')`, an element of `K`.

In Hermite's proof it is an algebraic integer, nonzero for large primes `p`, whose conjugates are
small once `∑ δ_γ' exp γ' = 0`. This file proves these four properties.

* `algebraMap_auxValue_eq_sum_hermiteIntegral`: if `∑ δ_γ' exp γ' = 0`, then the image of
  `auxValue x l p γ` in `ℂ` is `∑ δ_γ' F_f(γ')`, where `F_f` is Hermite's integral.
* `auxValue_galConj`: conjugating `x` by an automorphism `τ` conjugates its auxiliary values,
  `auxValue (galConj τ x) l p (τ γ) = τ (auxValue x l p γ)`. In particular `τ` permutes the
  auxiliary values of a Galois-invariant sum.
* `exists_auxValue_eq`, `isIntegral_auxValue`: if the coefficients `δ_γ'` and the numbers `l γ'`
  are algebraic integers and `γ ∈ S`, then `auxValue x l p γ` is `-δ_γ A ^ p` modulo `p` times the
  algebraic integers, where `A = l ^ t ∏_{γ' ∈ S, γ' ≠ γ} (γ - γ')`; in particular it is an
  algebraic integer.
* `auxValue_ne_zero`: under the same hypotheses and `l ≠ 0`, over a number field,
  `auxValue x l p γ ≠ 0` for every prime `p` with `|N(δ_γ A)| < p`.
* `norm_auxValue_le`, `eventually_norm_auxValue_lt_one`: if `∑ δ_γ' exp γ' = 0`, then the
  auxiliary values are bounded by `C c ^ p / (p - 1)!`, so that they all have absolute value less
  than `1` for large `p`.

The polynomial estimate behind the bound is `norm_eval_auxPoly_le`.

## References

* J.-H. Evertse, *Diophantine Approximation* (2019), ch. 4, §4.2, the proof of Theorem 4.11 and
  Lemmas 4.12, 4.14 and 4.15.
-/

public section

open AddMonoidAlgebra Finset Filter Polynomial Topology
open scoped Nat
open NumberField

namespace TauCeti.LindemannWeierstrass

section auxValue

variable {K : Type*} [Field K] [DecidableEq K]

/-- The auxiliary value `-∑_{γ' ∈ S} δ_γ' (sumIDeriv f)(γ')` of Hermite's proof of the
Lindemann–Weierstrass theorem, for the formal exponential sum `x = ∑ δ_γ' [γ']` with support `S`
and the auxiliary polynomial `f = auxPoly S l p γ`. -/
noncomputable def auxValue (x : K[K]) (l p : ℕ) (γ : K) : K :=
  -∑ γ' ∈ x.coeff.support, x.coeff γ' * (sumIDeriv (auxPoly x.coeff.support l p γ)).eval γ'

/-- The defining formula of `auxValue x l p γ`. -/
theorem auxValue_def (x : K[K]) (l p : ℕ) (γ : K) :
    auxValue x l p γ =
      -∑ γ' ∈ x.coeff.support, x.coeff γ' * (sumIDeriv (auxPoly x.coeff.support l p γ)).eval γ' :=
  (rfl)

/-- The auxiliary values of the zero sum vanish. -/
@[simp]
theorem auxValue_zero (l p : ℕ) (γ : K) : auxValue (0 : K[K]) l p γ = 0 := by
  simp [auxValue]

/-- Conjugating a formal exponential sum by an automorphism `τ` conjugates its auxiliary values:
`auxValue (galConj τ x) l p (τ γ) = τ (auxValue x l p γ)`. -/
theorem auxValue_galConj {F : Type*} [CommSemiring F] [Algebra F K] (τ : K ≃ₐ[F] K) (x : K[K])
    (l p : ℕ) (γ : K) : auxValue (galConj τ x) l p (τ γ) = τ (auxValue x l p γ) := by
  have hS : (galConj τ x).coeff.support = x.coeff.support.image (τ : K →+* K) := by
    simp [support_galConj, map_eq_image]
  have hf : auxPoly (x.coeff.support.image (τ : K →+* K)) l p (τ γ) =
      (auxPoly x.coeff.support l p γ).map (τ : K →+* K) := by
    rw [auxPoly_map, RingHom.coe_coe]
  rw [auxValue, auxValue, hS, hf,
    sum_image (g := (τ : K →+* K)) fun _ _ _ _ h ↦ τ.injective h, map_neg, map_sum]
  congr 1
  refine sum_congr rfl fun γ' _ ↦ ?_
  simp only [sumIDeriv_map, eval_map, eval₂_at_apply]
  simp

variable [CharZero K]

/-- If the coefficients of `x` and the numbers `l γ'` for `γ'` in the support `S` of `x` are
algebraic integers, `γ ∈ S` and `p ≠ 0`, then `auxValue x l p γ = -(δ_γ A ^ p + p w)` for an
algebraic integer `w`, where `A = l ^ t ∏_{γ' ∈ S, γ' ≠ γ} (γ - γ')`. -/
theorem exists_auxValue_eq {x : K[K]} {l p : ℕ} {γ : K} (hγ : γ ∈ x.coeff.support) (hp : p ≠ 0)
    (hx : ∀ γ', IsIntegral ℤ (x.coeff γ'))
    (hl : ∀ γ' ∈ x.coeff.support, IsIntegral ℤ ((l : K) * γ')) :
    ∃ w : K, IsIntegral ℤ w ∧ auxValue x l p γ =
      -(x.coeff γ * ((l : K) ^ #x.coeff.support * ∏ γ' ∈ x.coeff.support.erase γ, (γ - γ')) ^ p +
        p * w) := by
  have h (γ' : K) (hγ' : γ' ∈ x.coeff.support) := exists_eval_sumIDeriv_auxPoly_eq hγ hp hl hγ'
  choose! y hy hfy using h
  refine ⟨∑ γ' ∈ x.coeff.support, x.coeff γ' * y γ',
    IsIntegral.sum _ fun γ' hγ' ↦ (hx γ').mul (hy γ' hγ'), ?_⟩
  rw [auxValue, sum_congr rfl fun γ' hγ' ↦ by rw [hfy γ' hγ'], mul_sum]
  simp only [mul_add, mul_ite, mul_zero, sum_add_distrib, sum_ite_eq', hγ, ite_true]
  congr 2
  exact sum_congr rfl fun _ _ ↦ by ring

/-- If the coefficients of `x` and the numbers `l γ'` for `γ'` in the support of `x` are algebraic
integers, then the auxiliary value `auxValue x l p γ` at a point `γ` of the support is an algebraic
integer. -/
theorem isIntegral_auxValue {x : K[K]} {l p : ℕ} {γ : K} (hγ : γ ∈ x.coeff.support)
    (hx : ∀ γ', IsIntegral ℤ (x.coeff γ'))
    (hl : ∀ γ' ∈ x.coeff.support, IsIntegral ℤ ((l : K) * γ')) :
    IsIntegral ℤ (auxValue x l p γ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · have h1 : sumIDeriv (1 : K[X]) = 1 := by simpa using sumIDeriv_C (1 : K)
    simpa [auxValue, auxPoly_def, h1] using (IsIntegral.sum _ fun γ' _ ↦ hx γ').neg
  obtain ⟨w, hw, h⟩ := exists_auxValue_eq hγ hp hx hl
  rw [h]
  exact ((hx γ).mul ((isIntegral_pow_card_mul_prod_sub hγ (isIntegral_natCast l) hl).pow p)).add
    ((isIntegral_natCast p).mul hw) |>.neg

/-- **Nonvanishing of the auxiliary values**. Let `K` be a number field, let the coefficients of
`x` and the numbers `l γ'` for `γ'` in the support `S` of `x` be algebraic integers, `l ≠ 0` and
`γ ∈ S`. Then `auxValue x l p γ ≠ 0` for every prime `p` exceeding `|N(δ_γ A)|`, where
`A = l ^ t ∏_{γ' ∈ S, γ' ≠ γ} (γ - γ')` and `N` is the norm from `K` to `ℚ`. -/
theorem auxValue_ne_zero [NumberField K] {x : K[K]} {l p : ℕ} {γ : K}
    (hγ : γ ∈ x.coeff.support) (hx : ∀ γ', IsIntegral ℤ (x.coeff γ')) (hl₀ : l ≠ 0)
    (hl : ∀ γ' ∈ x.coeff.support, IsIntegral ℤ ((l : K) * γ')) (hp : p.Prime)
    (hpN : |Algebra.norm ℚ (x.coeff γ *
      ((l : K) ^ #x.coeff.support * ∏ γ' ∈ x.coeff.support.erase γ, (γ - γ')))| < p) :
    auxValue x l p γ ≠ 0 := by
  obtain ⟨w, hw, h⟩ := exists_auxValue_eq hγ hp.ne_zero hx hl
  set A := (l : K) ^ #x.coeff.support * ∏ γ' ∈ x.coeff.support.erase γ, (γ - γ')
  intro h0
  -- In the ring of integers, `δ_γ A ^ p = -p w`; taking norms, `p` divides `N(δ_γ) N(A) ^ p`.
  let δ' : 𝓞 K := ⟨x.coeff γ, hx γ⟩
  let A' : 𝓞 K := ⟨A, isIntegral_pow_card_mul_prod_sub hγ (isIntegral_natCast l) hl⟩
  let w' : 𝓞 K := ⟨w, hw⟩
  have heq : δ' * A' ^ p = algebraMap ℤ (𝓞 K) (-p) * w' := by
    apply RingOfIntegers.coe_injective
    simp only [map_mul, map_pow, map_neg, map_natCast]
    -- The coercions `↑δ'`, `↑A'`, `↑w'` are `x.coeff γ`, `A`, `w` by `RingOfIntegers.coe_mk`.
    exact (by linear_combination h - h0 : x.coeff γ * A ^ p = -(p : K) * w)
  have hA : A ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hl₀))
      (prod_ne_zero_iff.2 fun γ' hγ' ↦ sub_ne_zero.2 (ne_of_mem_erase hγ').symm)
  have hδA : δ' * A' ≠ 0 := by
    rw [← RingOfIntegers.coe_ne_zero_iff, map_mul]
    exact mul_ne_zero (Finsupp.mem_support_iff.1 hγ) hA
  have hdvd : (p : ℤ) ∣ Algebra.norm ℤ (δ' * A') := by
    have hn := congrArg (Algebra.norm ℤ) heq
    rw [map_mul, map_pow, map_mul, Algebra.norm_algebraMap] at hn
    have hpos : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
    have : (p : ℤ) ∣ Algebra.norm ℤ δ' * Algebra.norm ℤ A' ^ p := by
      rw [hn]
      exact dvd_mul_of_dvd_left (dvd_pow (dvd_neg.2 dvd_rfl) hpos.ne') _
    rw [map_mul]
    rcases Int.Prime.dvd_mul' hp this with hd | hd
    · exact dvd_mul_of_dvd_left hd _
    · exact dvd_mul_of_dvd_right (Int.Prime.dvd_pow' hp hd) _
  -- Since `N(δ_γ A)` is a nonzero integer, `p ≤ |N(δ_γ A)|`, contradicting the choice of `p`.
  have hle := Int.natAbs_le_of_dvd_ne_zero hdvd ((Algebra.norm_ne_zero_iff).2 hδA)
  rw [Int.natAbs_natCast] at hle
  have hlt : ((Algebra.norm ℤ (δ' * A')).natAbs : ℚ) < p := by
    rwa [Nat.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int]
  exact hlt.not_ge (by exact_mod_cast hle)

end auxValue

section norm

/-- **The size of the auxiliary polynomial**. If `γ ∈ S` and all the points of `S` have absolute
value at most `R`, then `|auxPoly S l p γ (u)| ≤ (l (2 R + 1)) ^ (t p) / (p - 1)!` for every `u`
with `|u| ≤ R`, where `t` is the cardinality of `S`. -/
theorem norm_eval_auxPoly_le {𝕜 : Type*} [RCLike 𝕜] [DecidableEq 𝕜] {S : Finset 𝕜} (l p : ℕ)
    {γ : 𝕜} (hγ : γ ∈ S) {R : ℝ} (hS : ∀ γ' ∈ S, ‖γ'‖ ≤ R) {u : 𝕜} (hu : ‖u‖ ≤ R) :
    ‖(auxPoly S l p γ).eval u‖ ≤ (l * (2 * R + 1)) ^ (#S * p) / (p - 1)! := by
  have hR : 0 ≤ R := (norm_nonneg u).trans hu
  have hB : 1 ≤ 2 * R + 1 := by linarith
  have hsub (γ' : 𝕜) (hγ' : γ' ∈ S) : ‖u - γ'‖ ≤ 2 * R + 1 := by
    linarith [norm_sub_le u γ', hS γ' hγ']
  have hprod : ‖∏ γ' ∈ S.erase γ, (u - γ') ^ p‖ ≤ (2 * R + 1) ^ ((#S - 1) * p) := by
    rw [norm_prod, pow_mul', ← card_erase_of_mem hγ, ← prod_const]
    refine prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun γ' hγ' ↦ ?_
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hsub γ' (mem_of_mem_erase hγ')) p
  have hexp : p - 1 + (#S - 1) * p ≤ #S * p := by
    have : 1 ≤ #S := card_pos.2 ⟨γ, hγ⟩
    rcases Nat.exists_eq_add_of_le this with ⟨t, ht⟩
    rw [ht, add_tsub_cancel_left]
    ring_nf
    omega
  have key : ‖u - γ‖ ^ (p - 1) * ‖∏ γ' ∈ S.erase γ, (u - γ') ^ p‖ ≤ (2 * R + 1) ^ (#S * p) :=
    calc ‖u - γ‖ ^ (p - 1) * ‖∏ γ' ∈ S.erase γ, (u - γ') ^ p‖
        ≤ (2 * R + 1) ^ (p - 1) * (2 * R + 1) ^ ((#S - 1) * p) := by
          gcongr
          exact hsub γ hγ
      _ ≤ (2 * R + 1) ^ (#S * p) := by
          rw [← pow_add]
          exact pow_le_pow_right₀ hB hexp
  simp only [auxPoly_def, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_prod, norm_mul,
    norm_div, norm_pow, RCLike.norm_natCast, mul_pow]
  calc _ = (l : ℝ) ^ (#S * p) / (p - 1)! *
        (‖u - γ‖ ^ (p - 1) * ‖∏ γ' ∈ S.erase γ, (u - γ') ^ p‖) := by ring
    _ ≤ (l : ℝ) ^ (#S * p) / (p - 1)! * (2 * R + 1) ^ (#S * p) := by gcongr
    _ = _ := by ring

variable {K : Type*} [Field K] [DecidableEq K] [Algebra K ℂ]

/-- **Hermite's analytic expression for the auxiliary values**. If the formal exponential sum
`x = ∑ δ_γ' [γ']` with support `S` satisfies `∑ δ_γ' exp γ' = 0`, then the image of
`auxValue x l p γ` in `ℂ` is `∑_{γ' ∈ S} δ_γ' F_f(γ')`, where `F_f` is Hermite's integral of
`f = auxPoly S l p γ`. -/
theorem algebraMap_auxValue_eq_sum_hermiteIntegral {x : K[K]} (hx : expEval K x = 0)
    (l p : ℕ) (γ : K) :
    algebraMap K ℂ (auxValue x l p γ) = ∑ γ' ∈ x.coeff.support, algebraMap K ℂ (x.coeff γ') *
      hermiteIntegral ((auxPoly x.coeff.support l p γ).map (algebraMap K ℂ))
        (algebraMap K ℂ γ') := by
  rw [sum_mul_hermiteIntegral_of_sum_mul_exp_eq_zero _ _ _ (by rwa [← expEval_apply]),
    auxValue, map_neg, map_sum]
  simp only [map_mul, sumIDeriv_map, eval_map, eval₂_at_apply]

/-- **The size of the auxiliary values**. If the formal exponential sum `x = ∑ δ_γ' [γ']` with
support `S` satisfies `∑ δ_γ' exp γ' = 0`, `γ ∈ S` and all the points of `S` have absolute value
at most `R`, then `|auxValue x l p γ| ≤ (∑ |δ_γ'|) R exp(R) (l (2 R + 1)) ^ (t p) / (p - 1)!`,
where `t` is the cardinality of `S`. -/
theorem norm_auxValue_le {x : K[K]} (hx : expEval K x = 0) (l p : ℕ) {γ : K}
    (hγ : γ ∈ x.coeff.support) {R : ℝ}
    (hR : ∀ γ' ∈ x.coeff.support, ‖algebraMap K ℂ γ'‖ ≤ R) :
    ‖algebraMap K ℂ (auxValue x l p γ)‖ ≤
      (∑ γ' ∈ x.coeff.support, ‖algebraMap K ℂ (x.coeff γ')‖) * R * Real.exp R *
        ((l * (2 * R + 1)) ^ (#x.coeff.support * p) / (p - 1)!) := by
  classical
  set S := x.coeff.support
  have hinj := (algebraMap K ℂ).injective
  have hR' : ∀ z ∈ S.image (algebraMap K ℂ), ‖z‖ ≤ R := by
    simpa using hR
  rw [algebraMap_auxValue_eq_sum_hermiteIntegral hx, auxPoly_map, sum_mul, sum_mul, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun γ' hγ' ↦ ?_)
  rw [norm_mul, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [← mul_assoc, ← card_image_of_injective S hinj]
  refine (norm_hermiteIntegral_le fun u hu ↦
    norm_eval_auxPoly_le l p (mem_image_of_mem _ hγ) hR' (hu.trans (hR γ' hγ'))).trans ?_
  have hR₀ : 0 ≤ R := (norm_nonneg _).trans (hR γ' hγ')
  gcongr
  · exact hR γ' hγ'
  · exact hR γ' hγ'

/-- If the formal exponential sum `x` satisfies `∑ δ_γ' exp γ' = 0`, then for all large `p` the
auxiliary values `auxValue x l p γ` at the points `γ` of the support of `x` have absolute value
less than `1`. -/
theorem eventually_norm_auxValue_lt_one {x : K[K]} (hx : expEval K x = 0) (l : ℕ) :
    ∀ᶠ p in atTop, ∀ γ ∈ x.coeff.support, ‖algebraMap K ℂ (auxValue x l p γ)‖ < 1 := by
  set S := x.coeff.support
  set R := ∑ γ' ∈ S, ‖algebraMap K ℂ γ'‖
  have hR (γ' : K) (hγ' : γ' ∈ S) : ‖algebraMap K ℂ γ'‖ ≤ R :=
    single_le_sum (f := fun γ' ↦ ‖algebraMap K ℂ γ'‖) (fun _ _ ↦ norm_nonneg _) hγ'
  set C := (∑ γ' ∈ S, ‖algebraMap K ℂ (x.coeff γ')‖) * R * Real.exp R
  set c := (l * (2 * R + 1)) ^ #S
  -- The bound `C c ^ p / (p - 1)! = C c * c ^ (p - 1) / (p - 1)!` tends to `0`.
  have hlim : Tendsto (fun p : ℕ ↦ C * ((l * (2 * R + 1)) ^ (#S * p) / (p - 1)!)) atTop (𝓝 0) := by
    have h := ((FloorSemiring.tendsto_pow_div_factorial_atTop c).comp
      (tendsto_sub_atTop_nat 1)).const_mul (C * c)
    rw [mul_zero] at h
    refine h.congr' ((eventually_ge_atTop 1).mono fun p hp ↦ ?_)
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
    simp only [Function.comp_apply, add_tsub_cancel_left, pow_mul, c]
    ring
  filter_upwards [hlim.eventually (gt_mem_nhds zero_lt_one)] with p hp γ hγ
  exact (norm_auxValue_le hx l p hγ hR).trans_lt hp

end norm

end TauCeti.LindemannWeierstrass

end

/-! ### Examples -/

open AddMonoidAlgebra Polynomial
open scoped Nat

namespace TauCeti.LindemannWeierstrass

/- The auxiliary values of the zero sum vanish. -/
example (l p : ℕ) (γ : ℚ) : auxValue (0 : ℚ[ℚ]) l p γ = 0 := by
  simp

/- For the single term `[0]` the auxiliary value is `-l ^ p`. It depends on `l`, so it is not an
invariant of the formal sum. -/
example (l q : ℕ) : auxValue (single (0 : ℚ) (1 : ℚ)) l (q + 1) 0 = -(l : ℚ) ^ (q + 1) := by
  have hS : (single (0 : ℚ) (1 : ℚ)).coeff.support = {0} := by simp
  have hdeg : (auxPoly {(0 : ℚ)} l (q + 1) 0).natDegree ≤ q := by
    simpa [auxPoly_def] using natDegree_C_mul_X_pow_le ((l : ℚ) ^ (q + 1) / q !) q
  rw [auxValue, hS, Finset.sum_singleton, sumIDeriv_apply_of_le hdeg, eval_finsetSum,
    Finset.sum_range_succ, Finset.sum_eq_zero fun j hj ↦
      eval_iterate_derivative_auxPoly_self_of_lt _ _ _ (by simpa using hj)]
  simpa using eval_iterate_derivative_auxPoly_self {(0 : ℚ)} l (q + 1) 0

end TauCeti.LindemannWeierstrass
