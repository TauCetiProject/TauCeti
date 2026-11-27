/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.GaussianTheta
public import Mathlib.Data.Nat.Factorization.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.DiscreteMoments
import TauCeti.Data.Nat.Factorization.Basic
import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds
import TauCeti.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Gaussian pair sums for quadratic-twist second moments

The second moment of a Jacobi-twisted theta series splits according to whether the odd part of
`a * b` is square. For positive integers `a, b`, write `W` for the product of the norms of the
Gaussian monomials at `a * u` and `b * u`. For every `δ > 0` and `u > 0`, both of the following
pair weights are summable, with constants uniform in the parity and scale:

* `W` restricted to products with square odd part: its sum multiplied by `u` is at most
  `C * u ^ (-2 * δ)`.
* `W * √(a * b) * (1 + log (a * b))` over all pairs: its sum multiplied by `u` is at most
  `C * u ^ (-(2 + 2 * δ))`. This bounds the nonsquare contribution, where the character sum
  has a square-root and logarithm bound. At `u ≥ 1 / T` with `T > 0`, the extra `u ^ (-2)` is
  at most `T ^ 2`.

The two weights are those of `New.sum_sq_thetaSeries_jacobiSym_le` in
`grh/src/Lib/Analytic/QuadraticTwist.lean` of [grh-lean](https://github.com/lsernau/grh-lean),
commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

noncomputable section

open Real Nat Finset

namespace TauCeti

private theorem norm_gaussianMonomial_pnat_le (j : Fin 2) (n : ℕ+) {u : ℝ} (hu : 0 < u) :
    ‖gaussianMonomial j (n * u)‖ ≤ 3 * exp (-(n * u)) := by
  have hnu : 0 ≤ (n : ℝ) * u := by positivity
  refine (norm_gaussianMonomial_le j _).trans ?_
  rw [abs_of_nonneg hnu]
  gcongr
  rw [pow_two]
  exact mul_le_of_le_one_right (exp_nonneg _) (exp_le_one_iff.mpr (neg_nonpos.mpr hnu))

private theorem summable_norm_gaussianMonomial_pnat (j : Fin 2) {u : ℝ} (hu : 0 < u) :
    Summable fun n : ℕ+ ↦ ‖gaussianMonomial j (n * u)‖ := by
  obtain ⟨_, _, h⟩ := exists_summable_and_tsum_rpow_mul_exp_neg_le (a := 0) le_rfl
  have hs : Summable (fun n : ℕ+ ↦ exp (-(n * u))) := by simpa using (h u hu).1
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦
    norm_gaussianMonomial_pnat_le j n hu) (hs.mul_left 3)

private theorem sum_gaussianMonomial_divisorsAntidiagonal_le (j : Fin 2) {u : ℝ}
    (hu : 0 < u) (m : ℕ+) :
    ∑ p ∈ (m : ℕ).divisorsAntidiagonal,
      ‖gaussianMonomial j (p.1 * u)‖ * ‖gaussianMonomial j (p.2 * u)‖ ≤
      9 * (#(m : ℕ).divisors : ℝ) * exp (-(√(m : ℝ) * u)) := by
  let B : ℝ := 9 * exp (-(√(m : ℝ) * u))
  calc
    _ ≤ ∑ _ ∈ (m : ℕ).divisorsAntidiagonal, B := by
      apply sum_le_sum
      intro p hp
      have hm := (mem_divisorsAntidiagonal.mp hp).1
      have hm' : (p.1 : ℝ) * p.2 = m := by exact_mod_cast hm
      have hroot : √(m : ℝ) ≤ (p.1 : ℝ) + p.2 := by
        rw [← hm']
        exact (Real.sqrt_le_iff).2 ⟨by positivity, by
          nlinarith [sq_nonneg (p.1 : ℝ), sq_nonneg (p.2 : ℝ)]⟩
      let n₁ : ℕ+ := ⟨p.1, Nat.pos_of_ne_zero (left_ne_zero_of_mem_divisorsAntidiagonal hp)⟩
      let n₂ : ℕ+ := ⟨p.2, Nat.pos_of_ne_zero (right_ne_zero_of_mem_divisorsAntidiagonal hp)⟩
      calc
        _ ≤ (3 * exp (-(p.1 * u))) * (3 * exp (-(p.2 * u))) :=
          mul_le_mul (norm_gaussianMonomial_pnat_le j n₁ hu)
            (norm_gaussianMonomial_pnat_le j n₂ hu) (norm_nonneg _) (by positivity)
        _ = 9 * exp (-(((p.1 : ℝ) + p.2) * u)) := by
          rw [mul_mul_mul_comm, ← exp_add]
          ring_nf
        _ ≤ B := by
          unfold B
          gcongr
    _ = _ := by
      rw [Nat.sum_divisorsAntidiagonal (fun _ _ ↦ B), sum_const, nsmul_eq_mul]
      unfold B
      ring

private def gaussianPairFiber (j : Fin 2) (u : ℝ) (m : ℕ+) : ℝ :=
  ∑ p ∈ (m : ℕ).divisorsAntidiagonal,
    ‖gaussianMonomial j (p.1 * u)‖ * ‖gaussianMonomial j (p.2 * u)‖

private def gaussianPairWeight (j : Fin 2) (u : ℝ) (S : Set ℕ) (a b : ℕ) : ℝ :=
  S.indicator (fun _ ↦ ‖gaussianMonomial j (a * u)‖ * ‖gaussianMonomial j (b * u)‖) (a * b)

private theorem summable_gaussianPairWeight (j : Fin 2) {u : ℝ} (hu : 0 < u) (S : Set ℕ) :
    Summable (fun p : ℕ+ × ℕ+ ↦ gaussianPairWeight j u S p.1 p.2) := by
  classical
  have hs := summable_norm_gaussianMonomial_pnat j hu
  have hs₂ := hs.mul_of_nonneg hs (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  apply Summable.of_nonneg_of_le _ _ hs₂
  · intro p
    simp only [gaussianPairWeight, Set.indicator_apply]
    split_ifs <;> positivity
  · intro p
    simp only [gaussianPairWeight, Set.indicator_apply]
    split_ifs
    · exact le_rfl
    · positivity

private theorem sum_gaussianPairWeight (j : Fin 2) (u : ℝ) (S : Set ℕ) (m : ℕ+) :
    (∑ p ∈ (m : ℕ).divisorsAntidiagonal, gaussianPairWeight j u S p.1 p.2) =
      ((PNat.val ⁻¹' S).indicator (gaussianPairFiber j u)) m := by
  classical
  simp only [Set.indicator_apply, Set.mem_preimage, gaussianPairFiber]
  split_ifs with hm
  · refine sum_congr rfl fun p hp ↦ ?_
    simp only [gaussianPairWeight, (mem_divisorsAntidiagonal.mp hp).1, Set.indicator_of_mem hm]
  · refine sum_eq_zero fun p hp ↦ ?_
    simp only [gaussianPairWeight, (mem_divisorsAntidiagonal.mp hp).1, Set.indicator_of_notMem hm]

private theorem hasSum_gaussianPairFiber (j : Fin 2) {u : ℝ} (hu : 0 < u) (S : Set ℕ) :
    HasSum ((PNat.val ⁻¹' S).indicator (gaussianPairFiber j u))
      (∑' p : ℕ+ × ℕ+, gaussianPairWeight j u S p.1 p.2) := by
  exact (summable_gaussianPairWeight j hu S).hasSum.sum_divisorsAntidiagonal.congr_fun
    (fun m ↦ (sum_gaussianPairWeight j u S m).symm)

private theorem gaussianPairFiber_le_of_eq_pow_mul_sq {δ D : ℝ} (hδ : 0 ≤ δ)
    (hdiv : ∀ n : ℕ, (#n.divisors : ℝ) ≤ D * (n : ℝ) ^ δ)
    (j : Fin 2) {u : ℝ} (hu : 0 < u) {m k : ℕ+} {d : Fin 2}
    (h : (m : ℕ) = (2 : ℕ) ^ d.val * (k : ℕ) ^ 2) :
    gaussianPairFiber j u m ≤ (9 * D * 2 ^ δ) * ((k : ℝ) ^ (2 * δ) * exp (-(k * u))) := by
  have hD : 0 ≤ D := zero_le_one.trans (by simpa using hdiv 1)
  have hm : (m : ℝ) = (2 : ℝ) ^ d.val * (k : ℝ) ^ 2 := by exact_mod_cast h
  have hd : d.val ≤ 1 := by omega
  have htwo : 1 ≤ (2 : ℝ) ^ d.val := one_le_pow₀ (by norm_num)
  have htwo' : (2 : ℝ) ^ d.val ≤ 2 := by simpa using pow_le_pow_right₀ (by norm_num) hd
  have hroot : (k : ℝ) ≤ √(m : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity), hm]
    exact le_mul_of_one_le_left (by positivity) htwo
  have hpow : (m : ℝ) ^ δ ≤ (2 : ℝ) ^ δ * (k : ℝ) ^ (2 * δ) := by
    rw [hm, mul_rpow (by positivity) (by positivity), rpow_mul (by positivity), rpow_two]
    gcongr
  calc
    gaussianPairFiber j u m ≤ 9 * (#(m : ℕ).divisors : ℝ) * exp (-(√(m : ℝ) * u)) :=
      sum_gaussianMonomial_divisorsAntidiagonal_le j hu m
    _ ≤ 9 * (D * (2 ^ δ * (k : ℝ) ^ (2 * δ))) * exp (-(k * u)) := by
      gcongr
      exact (hdiv _).trans (by gcongr)
    _ = _ := by ring

/-- The Gaussian pair sum over products with square odd part, multiplied by the square
of the theta normalization, converges with bound `C u⁻²ᵟ` for every positive scale. -/
theorem exists_mul_tsum_gaussianMonomial_sq_ordCompl_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (j : Fin 2) (u : ℝ), 0 < u →
      let g : ℕ+ × ℕ+ → ℝ := fun p ↦ if IsSquare (ordCompl[2] ((p.1 : ℕ) * p.2)) then
        ‖gaussianMonomial j (p.1 * u)‖ * ‖gaussianMonomial j (p.2 * u)‖ else 0
      Summable g ∧ u * (∑' p, g p) ≤ C * u ^ (-(2 * δ)) := by
  classical
  obtain ⟨D, hD, hdiv⟩ := exists_pos_card_divisors_le_rpow hδ
  obtain ⟨E, hE, hmoment⟩ := exists_summable_and_tsum_rpow_mul_exp_neg_le
    (a := 2 * δ) (by positivity)
  refine ⟨2 * (9 * D * 2 ^ δ) * E, by positivity, fun j u hu ↦ ?_⟩
  let S₀ : Set ℕ := {m | IsSquare (ordCompl[2] m)}
  let S : Set ℕ+ := PNat.val ⁻¹' S₀
  refine ⟨?_, ?_⟩
  · refine (summable_gaussianPairWeight j hu S₀).congr fun p ↦ ?_
    simp only [gaussianPairWeight, S₀, Set.indicator_apply, Set.mem_ofPred_eq]
  have hsum := hasSum_gaussianPairFiber j hu S₀
  have hFs := summable_subtype_iff_indicator.mpr hsum.summable
  have hrepr (m : S) : ∃ d : Fin 2, ∃ k : ℕ+, (m.val : ℕ) = (2 : ℕ) ^ d.val * (k : ℕ) ^ 2 := by
    obtain ⟨d, k, hk⟩ := Nat.exists_eq_pow_mul_sq_of_isSquare_ordCompl m.property
    have hk₀ : 0 < k := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hk
    exact ⟨d, ⟨k, hk₀⟩, hk⟩
  choose d k hdk using hrepr
  let b : ℕ+ → ℝ := fun n ↦ (9 * D * 2 ^ δ) * ((n : ℝ) ^ (2 * δ) * exp (-(n * u)))
  have hb := (hmoment u hu).1.mul_left (9 * D * 2 ^ δ)
  have hb₂ : Summable (fun p : Fin 2 × ℕ+ ↦ b p.2) := by
    simpa only [one_mul] using (hasSum_fintype (fun _ : Fin 2 ↦ (1 : ℝ))).summable.mul_of_nonneg hb
      (fun _ ↦ zero_le_one) (fun _ ↦ by positivity)
  have hinj : Function.Injective (fun m : S ↦ (d m, k m)) := by
    intro x y h
    exact Subtype.ext (PNat.coe_injective ((hdk x).trans <|
      (congrArg (fun p : Fin 2 × ℕ+ ↦ (2 : ℕ) ^ p.1.val * (p.2 : ℕ) ^ 2) h).trans (hdk y).symm))
  have hbound := Summable.tsum_le_tsum_of_inj (fun m : S ↦ (d m, k m)) hinj
    (fun p _ ↦ by dsimp [b]; positivity)
    (fun m ↦ gaussianPairFiber_le_of_eq_pow_mul_sq hδ.le hdiv j hu (hdk m)) hFs hb₂
  calc
    _ = u * ∑' m : S, gaussianPairFiber j u m := by
      rw [tsum_subtype S, hsum.tsum_eq]
      congr 1
      apply tsum_congr
      intro p
      simp only [gaussianPairWeight, S₀, Set.indicator_apply, Set.mem_ofPred_eq]
    _ ≤ u * ∑' p : Fin 2 × ℕ+, b p.2 := mul_le_mul_of_nonneg_left hbound hu.le
    _ = u * (2 * ((9 * D * 2 ^ δ) * ∑' n : ℕ+, (n : ℝ) ^ (2 * δ) * exp (-(n * u)))) := by
      rw [hb₂.tsum_prod, tsum_fintype, Fin.sum_univ_two]
      simp only [b, tsum_mul_left]
      ring
    _ ≤ u * (2 * ((9 * D * 2 ^ δ) * (E * u ^ (-(2 * δ + 1))))) := by
      gcongr
      exact (hmoment u hu).2
    _ = _ := by
      rw [neg_add, rpow_add hu, rpow_neg_one]; field_simp

private theorem gaussianPair_sqrt_mul_log_le {δ : ℝ} (hδ : 0 < δ) (j : Fin 2)
    {u : ℝ} (hu : 0 < u) (p : ℕ+ × ℕ+) :
    ‖gaussianMonomial j (p.1 * u)‖ * ‖gaussianMonomial j (p.2 * u)‖ *
      (√((p.1 : ℝ) * p.2) * (1 + log ((p.1 : ℝ) * p.2))) ≤
      (1 + δ⁻¹) * ((3 * ((p.1 : ℝ) ^ (1 / 2 + δ) * exp (-(p.1 * u)))) *
        (3 * ((p.2 : ℝ) ^ (1 / 2 + δ) * exp (-(p.2 * u))))) := by
  let a := 1 / 2 + δ
  have hm : 1 ≤ (p.1 : ℝ) * p.2 := by
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast p.1.property)
      (by exact_mod_cast p.2.property)
  let m : ℝ := (p.1 : ℝ) * p.2
  have hlog : 1 + log m ≤ (1 + δ⁻¹) * m ^ δ := by
    have hpow := Real.one_le_rpow hm hδ.le
    have hm₀ : 0 ≤ m := zero_le_one.trans hm
    linarith [log_le_rpow_div hm₀ hδ, div_eq_mul_inv (m ^ δ) δ]
  calc
    _ ≤ (3 * exp (-(p.1 * u))) * (3 * exp (-(p.2 * u))) *
        (√m * ((1 + δ⁻¹) * m ^ δ)) := by
      exact mul_le_mul (mul_le_mul (norm_gaussianMonomial_pnat_le j p.1 hu)
        (norm_gaussianMonomial_pnat_le j p.2 hu) (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left hlog (sqrt_nonneg _)) (by positivity [log_nonneg hm])
        (by positivity)
    _ = (3 * exp (-(p.1 * u))) * (3 * exp (-(p.2 * u))) * ((1 + δ⁻¹) * m ^ a) := by
      dsimp only [a]
      rw [sqrt_eq_rpow, rpow_add (by positivity : 0 < m)]
      ring
    _ = _ := by
      have he : m ^ a = (p.1 : ℝ) ^ a * (p.2 : ℝ) ^ a := mul_rpow (by positivity) (by positivity)
      rw [he]
      ring

/-- The square-root and logarithm weight from the nonsquare character sums can be
summed even without restricting to the nonsquare products. The bound includes the square
of the theta normalization. -/
theorem exists_mul_tsum_gaussianMonomial_sqrt_mul_log_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (j : Fin 2) (u : ℝ), 0 < u →
      let g : ℕ+ × ℕ+ → ℝ := fun p ↦ ‖gaussianMonomial j (p.1 * u)‖ *
        ‖gaussianMonomial j (p.2 * u)‖ * (√((p.1 : ℝ) * p.2) * (1 + log ((p.1 : ℝ) * p.2)))
      Summable g ∧ u * (∑' p, g p) ≤ C * u ^ (-(2 + 2 * δ)) := by
  let a := 1 / 2 + δ
  have ha : 0 ≤ a := by dsimp [a]; positivity
  obtain ⟨E, hE, hmoment⟩ := exists_summable_and_tsum_rpow_mul_exp_neg_le ha
  refine ⟨(1 + δ⁻¹) * (3 * E) ^ 2, by positivity, fun j u hu ↦ ?_⟩
  let f : ℕ+ → ℝ := fun n ↦ 3 * ((n : ℝ) ^ a * exp (-(n * u)))
  have hf : Summable f := (hmoment u hu).1.mul_left 3
  have h₂ := (hf.mul_of_nonneg hf (fun _ ↦ by dsimp [f]; positivity)
    (fun _ ↦ by dsimp [f]; positivity)).mul_left (1 + δ⁻¹)
  let g : ℕ+ × ℕ+ → ℝ := fun p ↦ ‖gaussianMonomial j (p.1 * u)‖ *
    ‖gaussianMonomial j (p.2 * u)‖ * (√((p.1 : ℝ) * p.2) * (1 + log ((p.1 : ℝ) * p.2)))
  have hg₀ (p : ℕ+ × ℕ+) : 0 ≤ g p := by
    have hm : 1 ≤ (p.1 : ℝ) * p.2 := by
      exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast p.1.property)
        (by exact_mod_cast p.2.property)
    dsimp only [g]
    positivity [log_nonneg hm]
  have hg (p : ℕ+ × ℕ+) : g p ≤ (1 + δ⁻¹) * (f p.1 * f p.2) :=
    gaussianPair_sqrt_mul_log_le hδ j hu p
  have hgs := Summable.of_nonneg_of_le hg₀ hg h₂
  refine ⟨hgs, ?_⟩
  have hsum := hgs.tsum_le_tsum hg h₂
  have hprod := hf.tsum_mul_tsum hf (hf.mul_of_nonneg hf (fun _ ↦ by dsimp [f]; positivity)
    (fun _ ↦ by dsimp [f]; positivity))
  rw [tsum_mul_left, ← hprod] at hsum
  have hf_le : (∑' n, f n) ≤ 3 * (E * u ^ (-(a + 1))) := by
    simp only [f, tsum_mul_left]
    gcongr
    exact (hmoment u hu).2
  calc
    u * ∑' p, g p ≤ u * ((1 + δ⁻¹) * (3 * (E * u ^ (-(a + 1)))) ^ 2) := by
      refine (mul_le_mul_of_nonneg_left hsum hu.le).trans ?_
      rw [← sq]
      gcongr
    _ = _ := by
      have he : u * (u ^ (-(a + 1))) ^ 2 = u ^ (-(2 + 2 * δ)) := by
        rw [← rpow_two, ← rpow_mul hu.le]
        nth_rw 1 [← rpow_one u]
        rw [← rpow_add hu]
        congr 1
        dsimp [a]
        ring
      rw [← he, mul_pow, mul_pow]
      ring

end TauCeti
