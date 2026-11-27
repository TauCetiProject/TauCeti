/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.Analytic.IsolatedZeros
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Local

/-!
# Changing the zero cutoff in the subtracted Perron formula

A contour can be shifted at a height in `(T, T + 1]` that avoids zero ordinates, but the
explicit formula uses the inclusive cutoff `|Im ρ| ≤ T`. We bound the change of the
multiplicity-weighted zero sum between these heights. The positive and negative ordinate
bands are counted separately, so no conjugation symmetry of an individual character is needed.

The local counting input is `TauCeti.exists_finsum_analyticOrderAt_LFunction_le`. See
Koukoulopoulos, *The Distribution of Prime Numbers*, Lemma 11.4 and the proof of Theorem 5.1
for the local expansion and the use of nearby heights in Perron inversion.
-/

public section

open Complex Metric Set
open Finset hiding Ioo Ioc

namespace DirichletCharacter

private theorem sum_orders_le_of_mem_disc {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hne : χ ≠ 1) {s₀ : ℂ} {Z : Finset ℂ}
    (hZ : ∀ z ∈ Z, ‖z - s₀‖ ≤ 3 ∧ χ.LFunction z = 0) :
    ∑ z ∈ Z, ((analyticOrderAt χ.LFunction z).toNat : ℝ) ≤
      ∑ᶠ z : {z : ℂ // ‖z - s₀‖ ≤ 3 ∧ χ.LFunction z = 0},
        ((analyticOrderAt χ.LFunction z.val).toNat : ℝ) := by
  classical
  have ha : AnalyticOnNhd ℂ χ.LFunction univ := fun _ _ ↦ analyticAt_LFunction χ (.inr hne)
  have hfin := ha.finite_setOf_mem_and_eq_zero_of_isCompact isPreconnected_univ
    (mem_univ (2 : ℂ)) (LFunction_ne_zero_of_one_le_re χ (.inl hne) (by norm_num))
    (isCompact_closedBall s₀ 3) (subset_univ _)
  have hfin' : {z : ℂ | ‖z - s₀‖ ≤ 3 ∧ χ.LFunction z = 0}.Finite := by
    simpa only [mem_closedBall, dist_eq_norm] using hfin
  let m (z : ℂ) : ℝ := (analyticOrderAt χ.LFunction z).toNat
  calc
    _ ≤ ∑ z ∈ hfin'.toFinset, m z :=
      sum_le_sum_of_subset_of_nonneg (fun z hz ↦ (Set.Finite.mem_toFinset hfin').mpr (hZ z hz))
        (fun _ _ _ ↦ Nat.cast_nonneg _)
    _ = ∑ᶠ z, ∑ᶠ (_ : z ∈ {z : ℂ | ‖z - s₀‖ ≤ 3 ∧ χ.LFunction z = 0}), m z :=
      (finsum_mem_eq_finite_toFinset_sum m hfin').symm
    _ = _ := (finsum_set_coe_eq_finsum_mem (f := m) _).symm

/-- The nontrivial zeros of a primitive nonprincipal Dirichlet character with absolute
ordinates in `(T, T + 1]`, counted with multiplicity, number at most `C log(N(T+2))` for
one absolute `C`. The estimate also holds for any finite subset of this shell. -/
theorem exists_sum_orders_le_of_mem_ordinate_shell :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → ∀ {T : ℝ}, 0 ≤ T → ∀ Z : Finset ℂ,
        (∀ z ∈ Z, z.re ∈ Ioo 0 1 ∧ |z.im| ∈ Ioc T (T + 1) ∧ χ.LFunction z = 0) →
        ∑ z ∈ Z, ((analyticOrderAt χ.LFunction z).toNat : ℝ) ≤ C * Real.log (N * (T + 2)) := by
  classical
  obtain ⟨B, hB⟩ := TauCeti.exists_finsum_analyticOrderAt_LFunction_le 2 3
  refine ⟨2 * max 1 B, by positivity, fun N _ χ hprim hne T hT Z hZ ↦ ?_⟩
  have hlog : 0 ≤ Real.log (N * (T + 2)) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le (n := N)
    nlinarith)
  have bound (t : ℝ) (ht : |t| = T) (S : Finset ℂ)
      (hS : ∀ z ∈ S, z.re ∈ Ioo 0 1 ∧ |z.im - t| ≤ 1 ∧ χ.LFunction z = 0) :
      ∑ z ∈ S, ((analyticOrderAt χ.LFunction z).toNat : ℝ) ≤
        max 1 B * Real.log (N * (T + 2)) := by
    let s₀ : ℂ := 2 + t * I
    have hgeom (z) (hz : z ∈ S) : ‖z - s₀‖ ≤ 3 ∧ χ.LFunction z = 0 := by
      obtain ⟨hre, him, hz₀⟩ := hS z hz
      have hparts : |z.re - 2| + |z.im - t| ≤ 3 := by
        rw [abs_of_nonpos (by linarith [hre.2] : z.re - 2 ≤ 0)]
        linarith [hre.1]
      exact ⟨(norm_le_abs_re_add_abs_im _).trans (by simpa [s₀] using hparts), hz₀⟩
    refine (sum_orders_le_of_mem_disc χ hne hgeom).trans ?_
    have hcount := hB N χ hprim hne s₀ (by simp [s₀])
    exact (by simpa [s₀, ht] using hcount : _ ≤ B * Real.log (N * (T + 2))).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 B) hlog)
  rw [← sum_filter_add_sum_filter_not Z (fun z : ℂ ↦ 0 ≤ z.im), two_mul, add_mul]
  apply add_le_add
  · apply bound T (abs_of_nonneg hT)
    intro z hz
    obtain ⟨hz, him⟩ := mem_filter.mp hz
    obtain ⟨hre, ht, hzero⟩ := hZ z hz
    rw [abs_of_nonneg him] at ht
    exact ⟨hre, abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩, hzero⟩
  · apply bound (-T) (by simp [abs_of_nonneg hT])
    intro z hz
    obtain ⟨hz, him⟩ := mem_filter.mp hz
    obtain ⟨hre, ht, hzero⟩ := hZ z hz
    rw [abs_of_neg (lt_of_not_ge him)] at ht
    exact ⟨hre, abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩, hzero⟩

/-- For endpoints `0 ≤ a ≤ b` with `1 ≤ b`, replacing the inclusive height `T > 0` in the
subtracted Perron zero sum by any height `T' ≤ T + 1` at or above `T` changes the
sum by at most `C * b/T * log(N(T+2))`, with `C` absolute. In the dyadic formula `a = b/2`.
Only the zeros with `T < |Im ρ| ≤ T'` need to lie in the strip. In particular, any
real-axis terms cancel, independently of the value assigned to the kernel at zero. -/
theorem exists_norm_subtracted_perron_zero_sum_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → ∀ {a b T T' : ℝ}, 0 ≤ a → a ≤ b → 1 ≤ b → 0 < T → T ≤ T' →
        T' ≤ T + 1 → ∀ Z : Finset ℂ,
        (∀ z ∈ Z, |z.im| ∈ Ioc T T' → z.re ∈ Ioo 0 1 ∧ χ.LFunction z = 0) →
        ‖(∑ z ∈ Z with |z.im| ≤ T', (analyticOrderAt χ.LFunction z).toNat •
            (((b : ℂ) ^ z - (a : ℂ) ^ z) / z)) -
          (∑ z ∈ Z with |z.im| ≤ T, (analyticOrderAt χ.LFunction z).toNat •
            (((b : ℂ) ^ z - (a : ℂ) ^ z) / z))‖ ≤ C * (b / T) * Real.log (N * (T + 2)) := by
  classical
  obtain ⟨B, hB₀, hB⟩ := exists_sum_orders_le_of_mem_ordinate_shell
  refine ⟨2 * B, by positivity, fun N _ χ hp hne a b T T' ha hab hb₁ hT hle hT' Z hZ ↦ ?_⟩
  have hb : 0 < b := by linarith
  let f (z : ℂ) := (analyticOrderAt χ.LFunction z).toNat • (((b : ℂ) ^ z - (a : ℂ) ^ z) / z)
  let S := (Z.filter fun z ↦ |z.im| ≤ T').filter fun z ↦ ¬ |z.im| ≤ T
  have hsub : (Z.filter fun z ↦ |z.im| ≤ T').filter (fun z ↦ |z.im| ≤ T) =
      Z.filter (fun z ↦ |z.im| ≤ T) := by
    ext z
    simp only [mem_filter]
    constructor
    · exact fun h ↦ ⟨h.1.1, h.2⟩
    · exact fun h ↦ ⟨⟨h.1, h.2.trans hle⟩, h.2⟩
  have hsplit := sum_filter_add_sum_filter_not (Z.filter fun z ↦ |z.im| ≤ T')
    (fun z ↦ |z.im| ≤ T) f
  rw [hsub] at hsplit
  have hS (z) (hz : z ∈ S) : z.re ∈ Ioo 0 1 ∧ |z.im| ∈ Ioc T (T + 1) ∧
      χ.LFunction z = 0 := by
    obtain ⟨hz', h⟩ := mem_filter.mp hz
    obtain ⟨hz, hz'⟩ := mem_filter.mp hz'
    obtain ⟨hre, hzero⟩ := hZ z hz ⟨lt_of_not_ge h, hz'⟩
    exact ⟨hre, ⟨lt_of_not_ge h, hz'.trans hT'⟩, hzero⟩
  rw [← hsplit, add_sub_cancel_left]
  calc
    ‖∑ z ∈ S, f z‖ ≤ ∑ z ∈ S, ‖f z‖ := norm_sum_le _ _
    _ ≤ ∑ z ∈ S, ((analyticOrderAt χ.LFunction z).toNat : ℝ) * (2 * b / T) := by
      apply sum_le_sum
      intro z hz
      obtain ⟨hr, ht, _⟩ := hS z hz
      have hn : T ≤ ‖z‖ := ht.1.le.trans (abs_im_le_norm _)
      simp only [f, nsmul_eq_mul, norm_mul, Complex.norm_natCast, norm_div]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc
        ‖(b : ℂ) ^ z - (a : ℂ) ^ z‖ / ‖z‖ ≤ (b + b) / ‖z‖ := by
          gcongr
          refine (norm_sub_le _ _).trans ?_
          rw [norm_cpow_eq_rpow_re_of_pos hb, norm_cpow_eq_rpow_re_of_nonneg ha hr.1.ne']
          have hpow : b ^ z.re ≤ b := Real.rpow_le_self_of_one_le hb₁ hr.2.le
          exact add_le_add hpow ((Real.rpow_le_rpow ha hab hr.1.le).trans hpow)
        _ ≤ 2 * b / T := by
          simpa only [two_mul] using div_le_div_of_nonneg_left (by linarith : 0 ≤ b + b) hT hn
    _ ≤ (B * Real.log (N * (T + 2))) * (2 * b / T) := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (hB N χ hp hne hT.le S hS) (by positivity)
    _ = _ := by ring

end DirichletCharacter
