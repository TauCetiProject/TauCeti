/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.SpecialFunctions.Log.MulLog

/-!
# Vandermonde ratios of theta-chain words

The internal Harish-Chandra entries of a word lie on a four-spaced grid, with a unit
perturbation at each entry. Two words share their exterior entries. The logarithm of the
ratio of their Vandermonde products is bounded linearly in the number of entries. This
controls variation of the Weyl dimensions used in choosing the level prime.

The rank comparison comes from Levent Alpöge's [formalization of the Riemann hypothesis][alpoge],
notably `Formalism.MainNotions.Sizes3b` and `Formalism.L2.SG.Pf.SzHypFam.aSz`.

[alpoge]: https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005
-/

public section

open Finset Real

namespace TauCeti.ThetaLift

/-- The linear terms from the gaps of length `4(d+1)` telescope to two boundary sums. -/
private theorem abs_sum_linear_gap_le {a : ℕ → ℝ} (ha : ∀ i, a i ∈ Set.Icc 0 1) (n d : ℕ) :
    |∑ i ∈ range (n - (d + 1)), (a (i + (d + 1)) - a i) / (4 * (d + 1))| ≤ 1 / 4 := by
  let e := d + 1
  by_cases he : n < e
  · rw [Nat.sub_eq_zero_of_le he.le, sum_range_zero, abs_zero]
    norm_num
  have he : e ≤ n := le_of_not_gt he
  have hsplit := sum_range_add a e (n - e)
  rw [Nat.add_sub_of_le he] at hsplit
  have hsplit' := sum_range_add a (n - e) e
  rw [Nat.sub_add_cancel he] at hsplit'
  have hb (s : ℕ) : 0 ≤ ∑ i ∈ range e, a (s + i) ∧ ∑ i ∈ range e, a (s + i) ≤ (e : ℝ) :=
    ⟨sum_nonneg fun i _ ↦ (ha (s + i)).1, by
      calc _ ≤ ∑ _i ∈ range e, (1 : ℝ) := sum_le_sum fun i _ ↦ (ha (s + i)).2
           _ = _ := by simp⟩
  have heq : (∑ i ∈ range (n - e), (a (i + e) - a i)) =
      (∑ i ∈ range e, a (n - e + i)) - ∑ i ∈ range e, a i := by
    rw [sum_sub_distrib]
    simp only [add_comm _ e]
    linarith only [hsplit, hsplit']
  have hfirst := hb 0
  simp only [zero_add] at hfirst
  have h : |∑ i ∈ range (n - e), (a (i + e) - a i)| ≤ (e : ℝ) := by
    rw [heq, abs_le]
    constructor <;> linarith only [(hb (n - e)).1, (hb (n - e)).2, hfirst.1, hfirst.2]
  have hden : 0 < 4 * ((d : ℝ) + 1) := by positivity
  simp only [div_eq_mul_inv, ← sum_mul, abs_mul, abs_of_pos (inv_pos.mpr hden)]
  rw [← div_eq_mul_inv, div_le_iff₀ hden]
  exact h.trans_eq (by dsimp only [e]; push_cast; ring)

/-- The log correction to a gap of length `4(d+1)` has total size at most a boundary term
plus a summable quadratic error. -/
private theorem abs_sum_log_gap_le {a : ℕ → ℝ} (ha : ∀ i, a i ∈ Set.Icc 0 1)
    (n d : ℕ) :
    |∑ i ∈ range (n - (d + 1)), log (1 + (a (i + (d + 1)) - a i) / (4 * (d + 1)))| ≤
      1 / 4 + n / (4 * ((d : ℝ) + 1) * (d + 2)) := by
  let D : ℝ := (d : ℝ) + 1
  let t : ℕ → ℝ := fun i ↦ (a (i + (d + 1)) - a i) / (4 * D)
  have hD : 1 ≤ D := le_add_of_nonneg_left (Nat.cast_nonneg d)
  have ht (i : ℕ) : |t i| ≤ 1 / (4 * D) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 4 * D)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact abs_le.2 ⟨by linarith [(ha (i + (d + 1))).1, (ha i).2],
      by linarith [(ha (i + (d + 1))).2, (ha i).1]⟩
  have hlin : |∑ i ∈ range (n - (d + 1)), t i| ≤ 1 / 4 := abs_sum_linear_gap_le ha n d
  have herr (i : ℕ) : |log (1 + t i) - t i| ≤ 1 / (4 * D * (D + 1)) := by
    have hquarter : |t i| ≤ 1 / 4 := (ht i).trans
      (one_div_le_one_div_of_le (by norm_num) (by linarith only [hD]))
    have h := abs_log_sub_add_sum_range_le (x := -t i)
      (by rw [abs_neg]; linarith only [hquarter]) 1
    have htaylor : |log (1 + t i) - t i| ≤ |t i| ^ 2 / (1 - |t i|) := by
      simpa [sub_eq_add_neg, add_comm] using h
    calc
      _ ≤ |t i| ^ 2 / (1 - |t i|) := htaylor
      _ ≤ (1 / (4 * D)) ^ 2 / (1 / 2) := by
        gcongr
        · exact ht i
        · linarith only [hquarter]
      _ ≤ 1 / (4 * D * (D + 1)) := by
        have hD₀ : 0 < D := by positivity
        field_simp
        nlinarith only [hD, sq_nonneg (D - 1)]
  have hsum := (abs_sum_le_sum_abs (fun i ↦ log (1 + t i) - t i) (range (n - (d + 1)))).trans
    (sum_le_sum fun i _ ↦ herr i)
  rw [sum_sub_distrib] at hsum
  simp only [sum_const, card_range, nsmul_eq_mul] at hsum
  have hc : ((n - (d + 1) : ℕ) : ℝ) ≤ n := Nat.cast_le.mpr (Nat.sub_le ..)
  obtain ⟨hge, hle⟩ := abs_le.mp hsum
  have hbound := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 1 / (4 * D * (D + 1)))
  have hfin : |∑ i ∈ range (n - (d + 1)), log (1 + t i)| ≤ 1 / 4 + n / (4 * D * (D + 1)) := by
    rw [div_eq_mul_inv (n : ℝ), abs_le] at ⊢
    rw [abs_le] at hlin
    simp only [one_div] at hle hge hbound
    constructor <;> linarith only [hlin.1, hlin.2, hle, hge, hbound]
  simpa only [t, D, show ∀ x : ℝ, x + 1 + 1 = x + 2 from fun x ↦ by ring] using hfin

/-- Bound the total log correction of the internal gaps relative to the unperturbed grid. -/
private theorem abs_sum_log_gaps_le {a : ℕ → ℝ} (ha : ∀ i, a i ∈ Set.Icc 0 1) (n : ℕ) :
    |∑ d ∈ range n, ∑ i ∈ range (n - (d + 1)),
      log (1 + (a (i + (d + 1)) - a i) / (4 * (d + 1)))| ≤ (n : ℝ) / 2 := by
  -- The quadratic gap weights telescope, so their sum costs at most one.
  have hw : (∑ d ∈ range n, 1 / (((d : ℝ) + 1) * (d + 2))) ≤ 1 := calc
    _ = ∑ d ∈ range n, (((d : ℝ) + 1)⁻¹ - ((d : ℝ) + 2)⁻¹) := by
      refine sum_congr rfl fun d _ ↦ ?_
      field_simp
      ring
    _ = 1 - ((n : ℝ) + 1)⁻¹ := by
      simpa only [Nat.cast_succ, Nat.cast_zero, zero_add, inv_one, add_assoc, one_add_one_eq_two]
        using sum_range_sub' (fun d ↦ ((d : ℝ) + 1)⁻¹) n
    _ ≤ _ := sub_le_self _ (by positivity)
  calc
    _ ≤ ∑ d ∈ range n, (1 / 4 + n / (4 * ((d : ℝ) + 1) * (d + 2))) :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ ↦ abs_sum_log_gap_le ha n d)
    _ = (n : ℝ) / 4 + (n / 4) * ∑ d ∈ range n, 1 / (((d : ℝ) + 1) * (d + 2)) := by
      rw [sum_add_distrib, mul_sum]
      simp only [sum_const, card_range, nsmul_eq_mul]
      congr 1
      · ring
      · exact sum_congr rfl fun d _ ↦ by field_simp
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ (n : ℝ) / 4)
      linarith only [h]

/-- The correction to the logarithm of the internal Vandermonde product, measured from
its unperturbed grid, is bounded by half the number of internal entries. -/
private theorem abs_log_vandermonde_grid_le {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, a i ∈ Set.Icc 0 1) (c Δ : ℝ) :
    |(∑ i : Fin n, ∑ j > i, log ((c + Δ * (4 * (j : ℝ) + a j)) -
      (c + Δ * (4 * (i : ℝ) + a i)))) -
      ∑ i : Fin n, ∑ j > i, log (Δ * (4 * ((j : ℝ) - (i : ℝ))))| ≤ (n : ℝ) / 2 := by
  rcases eq_or_ne Δ 0 with rfl | hΔ
  · simp only [zero_mul, add_zero, sub_self, log_zero, sum_const_zero, abs_zero]
    positivity
  let A (i : ℕ) : ℝ := if hi : i < n then a ⟨i, hi⟩ else 0
  have hA (i : ℕ) : A i ∈ Set.Icc 0 1 := by
    unfold A
    split
    · exact ha _
    · exact ⟨le_rfl, zero_le_one⟩
  rw [← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  -- Reindex a pair `(i,j)` by its positive distance `d+1` and its starting index `i`.
  have h := abs_sum_log_gaps_le hA n
  simp only [sum_sigma'] at h ⊢
  convert h using 2
  refine sum_bij' (fun p _ ↦ ⟨p.2.val - p.1.val - 1, p.1.val⟩)
    (fun p hp ↦ ⟨⟨p.2, by simp only [mem_sigma, mem_range] at hp; omega⟩,
      ⟨p.2 + (p.1 + 1), by simp only [mem_sigma, mem_range] at hp; omega⟩⟩) ?_ ?_ ?_ ?_ ?_
  · intro ⟨i, j⟩ hp
    simp only [mem_sigma, mem_univ, mem_Ioi, true_and, Fin.lt_def] at hp
    simp only [mem_sigma, mem_range]
    have := j.isLt
    omega
  · intro p hp
    simp only [mem_sigma, mem_univ, mem_Ioi, true_and, Fin.lt_def]
    omega
  · intro ⟨i, j⟩ hp
    simp only [mem_sigma, mem_univ, mem_Ioi, true_and, Fin.lt_def] at hp
    congr 1
    exact Fin.ext (by dsimp; omega)
  · intro p hp
    rcases p with ⟨d, i⟩
    simp
  · intro ⟨i, j⟩ hp
    simp only [mem_sigma, mem_univ, mem_Ioi, true_and, Fin.lt_def] at hp
    have hi : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hp
    have hij : (i : ℕ) + ((j : ℕ) - i - 1 + 1) = j := by omega
    have hd : ((j : ℕ) - i - 1 : ℕ) + 1 = (j : ℕ) - i := by omega
    have hdR : (((j : ℕ) - i - 1 : ℕ) : ℝ) + 1 = (j : ℝ) - (i : ℝ) := by
      rw [← Nat.cast_one (R := ℝ), ← Nat.cast_add, hd, Nat.cast_sub (le_of_lt hp)]
    simp only [hij, A, dite_eq_left i.isLt, dite_eq_left j.isLt, hdR]
    have hbase : (j : ℝ) - (i : ℝ) ≠ 0 := by linarith only [hi]
    have hgap : (c + Δ * (4 * (j : ℝ) + a j)) - (c + Δ * (4 * (i : ℝ) + a i)) ≠ 0 := by
      rw [add_sub_add_left_eq_sub, ← mul_sub]
      exact mul_ne_zero hΔ (by linarith only [hi, (ha j).1, (ha i).2])
    rw [← log_div hgap (mul_ne_zero hΔ (mul_ne_zero (by norm_num) hbase))]
    congr 1
    field_simp [hΔ, hbase]
    ring

/-- Expand the logarithm of a word's Vandermonde into its exterior and interior
contributions, and record nonvanishing for taking ratios. -/
private theorem log_det_vandermonde_word {n : ℕ} {v : Fin n → ℝ} {l u : ℝ}
    (hl : l ∉ Set.range v) (hu : u ∉ Set.range v) (hv : Function.Injective v) (hlu : l ≠ u) :
    let x : Fin (n + 2) → ℝ := Fin.cons l (Fin.cons u v)
    (Matrix.vandermonde x).det ≠ 0 ∧ log (Matrix.vandermonde x).det =
      log (u - l) + (∑ i, log (v i - l)) + (∑ i, log (u - v i)) +
        ∑ i : Fin n, ∑ j > i, log (v j - v i) := by
  intro x
  have hinj : Function.Injective x := Fin.cons_injective_of_injective
    (by simp [Fin.range_cons, hlu, hl]) (Fin.cons_injective_of_injective hu hv)
  refine ⟨Matrix.det_vandermonde_ne_zero_iff.mpr hinj, ?_⟩
  have hlog : log (Matrix.vandermonde x).det = ∑ i, ∑ j > i, log (x j - x i) := by
    rw [Matrix.det_vandermonde, log_prod (fun i _ ↦ prod_ne_zero_iff.2 fun j hj ↦
      sub_ne_zero.mpr (hinj.ne (mem_Ioi.mp hj).ne'))]
    exact sum_congr rfl fun i _ ↦ log_prod fun j hj ↦ sub_ne_zero.mpr (hinj.ne (mem_Ioi.mp hj).ne')
  rw [hlog, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.Ioi_zero_eq_map, sum_map, Fin.coe_succEmb, Fin.sum_Ioi_succ, x,
    Fin.cons_zero, Fin.cons_succ]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, ← log_neg_eq_log (u - v _), neg_sub]
  ring

/-- **Vandermonde comparison for two theta-chain words.** The internal entries of each word
are perturbations by at most one grid unit of the same four-spaced grid. The two common
exterior entries lie at least one grid unit away from the allowed internal entries. Then
the absolute Vandermonde ratio lies between `exp (-3 * n)` and `exp (3 * n)`, where `n` is the
number of internal entries. The two exterior entries are put first in the matrix rows. -/
theorem abs_det_vandermonde_div_mem_Icc_of_words {n : ℕ} {a b : Fin n → ℝ} {c Δ l u : ℝ}
    (hΔ : 0 < Δ) (hlu : l ≠ u) (ha : ∀ i, a i ∈ Set.Icc 0 1) (hb : ∀ i, b i ∈ Set.Icc 0 1)
    (hl : ∀ i : Fin n, Δ ≤ c + Δ * (4 * (i : ℝ)) - l)
    (hu : ∀ i : Fin n, Δ ≤ u - (c + Δ * (4 * (i : ℝ) + 1))) :
    let x := Fin.cons l (Fin.cons u (fun i : Fin n ↦ c + Δ * (4 * (i : ℝ) + a i)))
    let y := Fin.cons l (Fin.cons u (fun i : Fin n ↦ c + Δ * (4 * (i : ℝ) + b i)))
    |(Matrix.vandermonde x).det / (Matrix.vandermonde y).det| ∈
      Set.Icc (exp (-3 * n)) (exp (3 * n)) := by
  let v (f : Fin n → ℝ) (i : Fin n) := c + Δ * (4 * (i : ℝ) + f i)
  intro xa xb
  have hleft {f : Fin n → ℝ} (hf : ∀ i, f i ∈ Set.Icc 0 1) (i : Fin n) : Δ ≤ v f i - l :=
    (hl i).trans (by dsimp only [v]; gcongr; linarith only [(hf i).1])
  have hright {f : Fin n → ℝ} (hf : ∀ i, f i ∈ Set.Icc 0 1) (i : Fin n) : Δ ≤ u - v f i :=
    (hu i).trans (by dsimp only [v]; gcongr; exact (hf i).2)
  have hmono {f : Fin n → ℝ} (hf : ∀ i, f i ∈ Set.Icc 0 1) : StrictMono (v f) := by
    intro i j hij
    have h : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
    have hinner : 4 * (i : ℝ) + f i < 4 * (j : ℝ) + f j := by
      linarith only [h, (hf i).2, (hf j).1]
    dsimp only [v]
    exact add_lt_add_right (mul_lt_mul_of_pos_left hinner hΔ) c
  have hclose (i : Fin n) : |v a i - v b i| ≤ Δ := by
    have heq : v a i - v b i = Δ * (a i - b i) := by dsimp only [v]; ring
    rw [heq, abs_mul, abs_of_pos hΔ]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (abs_le.2 ⟨by linarith [(ha i).1, (hb i).2], by linarith [(ha i).2, (hb i).1]⟩ :
        |a i - b i| ≤ 1) hΔ.le
  have hword {f : Fin n → ℝ} (hf : ∀ i, f i ∈ Set.Icc 0 1) :=
    log_det_vandermonde_word (by rintro ⟨i, rfl⟩; linarith only [hΔ, hleft hf i])
      (by rintro ⟨i, rfl⟩; linarith only [hΔ, hright hf i]) (hmono hf).injective hlu
  -- Each exterior sum costs at most `n`; the common exterior gap cancels.
  have hends {p q : Fin n → ℝ} (hp : ∀ i, Δ ≤ p i) (hq : ∀ i, Δ ≤ q i)
      (hdiff : ∀ i, |p i - q i| ≤ Δ) : |∑ i, (log (p i) - log (q i))| ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ i, |log (p i) - log (q i)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := sum_le_sum fun i _ ↦ by
        apply le_of_mul_le_mul_left _ hΔ
        simpa only [mul_one] using (mul_abs_log_sub_log_le (hp i) (hq i)).trans (hdiff i)
      _ = _ := by simp
  have hl' := hends (hleft ha) (hleft hb) (fun i ↦ by
    simpa only [sub_sub_sub_cancel_right] using hclose i)
  have hu' := hends (hright ha) (hright hb) (fun i ↦ by
    simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hclose i)
  obtain ⟨hla, hua⟩ := abs_le.mp (abs_log_vandermonde_grid_le ha c Δ)
  obtain ⟨hlb, hub⟩ := abs_le.mp (abs_log_vandermonde_grid_le hb c Δ)
  rw [sum_sub_distrib, abs_le] at hl' hu'
  have hlogs : |log (Matrix.vandermonde xa).det - log (Matrix.vandermonde xb).det| ≤ 3 * n := by
    rw [(hword ha).2, (hword hb).2, abs_le]
    constructor <;> linarith only [hla, hua, hlb, hub, hl'.1, hl'.2, hu'.1, hu'.2]
  have hratio := div_ne_zero (hword ha).1 (hword hb).1
  rw [← log_div (hword ha).1 (hword hb).1, ← log_abs] at hlogs
  obtain ⟨hlo, hhi⟩ := abs_le.mp hlogs
  exact ⟨(le_log_iff_exp_le (abs_pos.mpr hratio)).mp (by linarith only [hlo]),
    (log_le_iff_le_exp (abs_pos.mpr hratio)).mp hhi⟩

end TauCeti.ThetaLift
