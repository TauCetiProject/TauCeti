/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.InformationTheory.Hamming
public import TauCeti.InformationTheory.Hamming
public import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Hamming balls in the binary cube and the Varshamov–Gilbert bound

For a binary word `c : ι → Bool` and any `x` in a commutative semiring,
`∑ y, x ^ hammingDist y c = (1 + x) ^ n`, where `n` is the number of coordinates
(`TauCeti.sum_pow_hammingDist_eq`, in `TauCeti.InformationTheory.Hamming`). Taking
`x = exp (-2 t)` with `t ≥ 0` and bounding `cosh t ≤ exp (t² / 2)` gives the Chernoff bound for the
Hamming ball of radius `r ≤ m / 2` in `Fin m → Bool`,

```text
#{ω | hammingDist ω c ≤ r} ≤ 2^m exp (-2 (m / 2 - r)² / m),
```

which is Hoeffding's bound for a sum of `m` independent fair Bernoulli variables.

The Varshamov–Gilbert bound (A. B. Tsybakov, *Introduction to Nonparametric Estimation*,
Springer, 2009, Lemma 2.9, p. 104) follows by the greedy argument
(`TauCeti.exists_finset_pairwise_lt_hammingDist_forall_exists`, in
`TauCeti.InformationTheory.Hamming`): a largest code containing the constant word `false` whose
distinct words are at distance more than `⌊m / 8⌋` covers the cube by balls of radius `⌊m / 8⌋`,
so for `m ≥ 8` it has more than `2^{m/8}` words. It is stated as a family
`ω : Fin (M + 1) → Fin m → Bool` with `ω 0` the constant word `false`, and as a lower bound for the
packing number `Metric.packingNumber (m / 8)` of the cube `Hamming fun _ : Fin m ↦ Bool`.

## Main results

* `TauCeti.card_hammingDist_le_two_pow_mul_exp`: the Chernoff bound for a Hamming ball with a free
  parameter `t ≥ 0`; `TauCeti.card_hammingDist_le`: the optimized form.
* `TauCeti.exists_finset_varshamovGilbert`: a code containing `false` with more than `2^{m/8}`
  words at pairwise distance more than `⌊m / 8⌋`.
* `TauCeti.exists_varshamovGilbert`, `TauCeti.le_packingNumber_hamming`: the indexed and the
  packing-number forms.

The two lemmas used from `TauCeti.InformationTheory.Hamming` and the greedy-code argument of
`exists_finset_varshamovGilbert` are adapted from the lean-CKSD project
(<https://github.com/bjbraams/lean-CKSD>), file `CKSD/Nonparametric/LowerBounds/Testing.lean`
(`CKSD.sum_pow_hammingDist_eq`, `CKSD.exists_hamming_packing`); the ball bounds and the indexed and
packing-number forms are new proofs.
-/

public section

open Finset Real
open scoped NNReal

namespace TauCeti

/-- The Chernoff bound for a Hamming ball in `Fin m → Bool`: for every `t ≥ 0`, the number of
words within distance `r` of `c` is at most `2^m exp (m t² / 2 - t (m - 2 r))`. -/
theorem card_hammingDist_le_two_pow_mul_exp {m : ℕ} (c : Fin m → Bool) (r : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    ((univ.filter fun ω : Fin m → Bool ↦ (hammingDist ω c : ℝ) ≤ r).card : ℝ) ≤
      2 ^ m * exp (m * t ^ 2 / 2 - t * (m - 2 * r)) := by
  have hpt (ω : Fin m → Bool) : (if (hammingDist ω c : ℝ) ≤ r then (1 : ℝ) else 0) ≤
      exp (2 * t * r) * exp (-2 * t) ^ hammingDist ω c := by
    rw [← exp_natCast_mul, ← exp_add]
    split_ifs with h
    · exact one_le_exp (by nlinarith)
    · exact (exp_pos _).le
  have hcosh : 1 + exp (-2 * t) ≤ 2 * exp (t ^ 2 / 2 - t) := by
    have h := cosh_le_exp_half_sq t
    rw [cosh_eq] at h
    have hneg : -t + -t = -2 * t := by ring
    have h1 : 1 + exp (-2 * t) = exp (-t) * (exp t + exp (-t)) := by
      simp [mul_add, ← exp_add, hneg]
    have h2 : exp (t ^ 2 / 2 - t) = exp (-t) * exp (t ^ 2 / 2) := by
      rw [← exp_add]
      congr 1
      ring
    rw [h1, h2]
    nlinarith [exp_pos (-t)]
  calc ((univ.filter fun ω : Fin m → Bool ↦ (hammingDist ω c : ℝ) ≤ r).card : ℝ)
      = ∑ ω : Fin m → Bool, if (hammingDist ω c : ℝ) ≤ r then (1 : ℝ) else 0 := by
        rw [sum_boole]
    _ ≤ ∑ ω : Fin m → Bool, exp (2 * t * r) * exp (-2 * t) ^ hammingDist ω c :=
        sum_le_sum fun ω _ ↦ hpt ω
    _ = exp (2 * t * r) * (1 + exp (-2 * t)) ^ m := by
        rw [← mul_sum, sum_pow_hammingDist_eq, Fintype.card_fin]
    _ ≤ exp (2 * t * r) * (2 * exp (t ^ 2 / 2 - t)) ^ m := by gcongr
    _ = 2 ^ m * exp (m * t ^ 2 / 2 - t * (m - 2 * r)) := by
        rw [mul_pow, ← exp_natCast_mul, mul_left_comm, ← exp_add]
        congr 2
        ring

/-- The Hoeffding bound for a Hamming ball in `Fin m → Bool`: for `r ≤ m / 2`, at most
`2^m exp (-2 (m / 2 - r)² / m)` words lie within distance `r` of `c`. -/
theorem card_hammingDist_le {m : ℕ} (c : Fin m → Bool) {r : ℝ} (hr : r ≤ m / 2) :
    ((univ.filter fun ω : Fin m → Bool ↦ (hammingDist ω c : ℝ) ≤ r).card : ℝ) ≤
      2 ^ m * exp (-2 * (m / 2 - r) ^ 2 / m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using card_hammingDist_le_two_pow_mul_exp c r le_rfl
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  refine (card_hammingDist_le_two_pow_mul_exp c r
    (t := (m - 2 * r) / m) (div_nonneg (by linarith) hm'.le)).trans_eq ?_
  congr 2
  field_simp
  ring

/-- For `m ≥ 8`, `2^{m/8} + 1 ≤ exp (9 m / 32)`: with `s = m / 8 ≥ 1` and `u = 2^s ≥ 2`,
`exp (9 s / 4) ≥ 8^s = u³ ≥ u + 1`, since `log 2 < 3 / 4`. -/
private lemma two_rpow_div_eight_add_one_le_exp {m : ℕ} (hm : 8 ≤ m) :
    (2 : ℝ) ^ ((m : ℝ) / 8) + 1 ≤ exp (9 * m / 32) := by
  have hs : (1 : ℝ) ≤ m / 8 := by
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast (by omega : 1 * 8 ≤ m)
  set u : ℝ := (2 : ℝ) ^ ((m : ℝ) / 8) with hu
  have hu2 : 2 ≤ u := by
    simpa using rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) hs
  have hu3 : u ^ 3 ≤ exp (9 * m / 32) := by
    rw [hu, ← rpow_natCast, ← rpow_mul (by norm_num), rpow_def_of_pos (by norm_num)]
    gcongr
    have := log_two_lt_d9
    have : (0 : ℝ) ≤ m := by positivity
    norm_num at *
    nlinarith
  nlinarith [mul_nonneg (mul_nonneg (by linarith : 0 ≤ u) (sub_nonneg.2 hu2))
    (by linarith : 0 ≤ u + 2)]

/-- **Varshamov–Gilbert bound**, as a code: for `m ≥ 8` there is a code in `Fin m → Bool`
containing the constant word `false`, with at least `2^{m/8} + 1` words, whose distinct words are
at Hamming distance more than `⌊m / 8⌋`. -/
theorem exists_finset_varshamovGilbert {m : ℕ} (hm : 8 ≤ m) :
    ∃ C : Finset (Fin m → Bool), (fun _ ↦ false) ∈ C ∧
      (2 : ℝ) ^ ((m : ℝ) / 8) + 1 ≤ C.card ∧
      (C : Set (Fin m → Bool)).Pairwise fun x y ↦ m / 8 < hammingDist x y := by
  obtain ⟨C, h0, hsep, hcover⟩ :=
    exists_finset_pairwise_lt_hammingDist_forall_exists (m / 8) (fun _ : Fin m ↦ false)
  refine ⟨C, h0, ?_, hsep⟩
  let ball : (Fin m → Bool) → Finset (Fin m → Bool) := fun x ↦
    univ.filter fun ω ↦ (hammingDist ω x : ℝ) ≤ (m / 8 : ℕ)
  have hD : ((m / 8 : ℕ) : ℝ) ≤ m / 8 := Nat.cast_div_le
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hcount : (2 : ℝ) ^ m ≤ C.card * (2 ^ m * exp (-2 * (m / 2 - (m / 8 : ℕ)) ^ 2 / m)) := by
    have hsub : (univ : Finset (Fin m → Bool)) ⊆ C.biUnion ball := fun y _ ↦ by
      obtain ⟨x, hx, hyx⟩ := hcover y
      exact mem_biUnion.mpr ⟨x, hx, mem_filter.mpr ⟨mem_univ _, by exact_mod_cast hyx⟩⟩
    calc (2 : ℝ) ^ m = ((univ : Finset (Fin m → Bool)).card : ℝ) := by simp
      _ ≤ ∑ x ∈ C, ((ball x).card : ℝ) := by
        exact_mod_cast (card_le_card hsub).trans card_biUnion_le
      _ ≤ ∑ _x ∈ C, 2 ^ m * exp (-2 * (m / 2 - (m / 8 : ℕ)) ^ 2 / m) :=
        sum_le_sum fun x _ ↦ card_hammingDist_le x (by linarith)
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hexp : exp (9 * m / 32) ≤ exp (2 * (m / 2 - (m / 8 : ℕ)) ^ 2 / m) := by
    refine exp_le_exp.mpr ?_
    rw [le_div_iff₀ hm0]
    have h38 : 3 * m / 8 ≤ m / 2 - ((m / 8 : ℕ) : ℝ) := by linarith
    nlinarith [mul_self_le_mul_self (by positivity) h38]
  have hC : exp (2 * (m / 2 - (m / 8 : ℕ)) ^ 2 / m) ≤ C.card := by
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    have h3 := exp_pos (2 * (m / 2 - (m / 8 : ℕ)) ^ 2 / m)
    rw [neg_mul, neg_div, exp_neg] at hcount
    rw [← mul_le_mul_iff_left₀ (inv_pos.mpr h3), ← mul_le_mul_iff_left₀ h2]
    field_simp at hcount ⊢
    linarith
  linarith [two_rpow_div_eight_add_one_le_exp hm]

/-- **Varshamov–Gilbert bound** (Tsybakov, Lemma 2.9): for `m ≥ 8` there are `M ≥ 2^{m/8}` and
words `ω : Fin (M + 1) → Fin m → Bool` with `ω 0` the constant word `false` and
`m / 8 ≤ hammingDist (ω j) (ω k)` for `j ≠ k`. -/
theorem exists_varshamovGilbert {m : ℕ} (hm : 8 ≤ m) :
    ∃ (M : ℕ) (ω : Fin (M + 1) → Fin m → Bool), (2 : ℝ) ^ ((m : ℝ) / 8) ≤ M ∧
      ω 0 = (fun _ ↦ false) ∧ ∀ j k, j ≠ k → (m : ℝ) / 8 ≤ hammingDist (ω j) (ω k) := by
  obtain ⟨C, h0, hcard, hsep⟩ := exists_finset_varshamovGilbert hm
  let C' := C.erase fun _ ↦ false
  have hC' : (C'.card : ℝ) + 1 = C.card := by
    rw [card_erase_of_mem h0, Nat.cast_sub (card_pos.mpr ⟨_, h0⟩)]
    ring
  let e := C'.equivFin.symm
  let ω : Fin (C'.card + 1) → Fin m → Bool := Fin.cons (fun _ ↦ false) fun i ↦ (e i : _)
  have hω : Function.Injective ω := Fin.cons_injective_iff.mpr
    ⟨fun ⟨i, hi⟩ ↦ (mem_erase.mp (e i).property).1 hi, Subtype.val_injective.comp e.injective⟩
  have hmem (j : Fin (C'.card + 1)) : ω j ∈ C := by
    induction j using Fin.cases with
    | zero => exact h0
    | succ i => exact (mem_erase.mp (e i).property).2
  refine ⟨C'.card, ω, by linarith, rfl, fun j k hjk ↦ ?_⟩
  have h := hsep (hmem j) (hmem k) (hω.ne hjk)
  have h8 : (m : ℝ) < 8 * ((m / 8 : ℕ) + 1) := by
    exact_mod_cast (by omega : m < 8 * (m / 8 + 1))
  have h1 : ((m / 8 : ℕ) : ℝ) + 1 ≤ hammingDist (ω j) (ω k) := by exact_mod_cast h
  linarith

/-- **Varshamov–Gilbert bound**, packing form: for `m ≥ 8` the cube `Hamming fun _ : Fin m ↦ Bool`
contains `M + 1` points, with `M ≥ 2^{m/8}`, at pairwise distance more than `m / 8`. -/
theorem le_packingNumber_hamming {m : ℕ} (hm : 8 ≤ m) :
    ∃ M : ℕ, (2 : ℝ) ^ ((m : ℝ) / 8) ≤ M ∧
      ((M + 1 : ℕ) : ℕ∞) ≤
        Metric.packingNumber ((m : ℝ≥0) / 8)
          (Set.univ : Set (Hamming fun _ : Fin m ↦ Bool)) := by
  obtain ⟨C, h0, hcard, hsep⟩ := exists_finset_varshamovGilbert hm
  have hpos : 1 ≤ C.card := card_pos.mpr ⟨_, h0⟩
  refine ⟨C.card - 1, ?_, ?_⟩
  · rw [Nat.cast_sub hpos]
    push_cast
    linarith
  · let S : Set (Hamming fun _ : Fin m ↦ Bool) := Hamming.toHamming '' (C : Set (Fin m → Bool))
    have hS : S.encard = C.card := by
      rw [Hamming.toHamming.injective.encard_image, Set.encard_coe_eq_coe_finsetCard]
    have hsepS : Metric.IsSeparated ((m : ℝ≥0) / 8 : ℝ≥0) S := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      have h := hsep hx hy fun h ↦ hxy (congrArg _ h)
      rw [edist_nndist, Hamming.nndist_eq_hammingDist, ENNReal.coe_lt_coe,
        div_lt_iff₀ (by norm_num)]
      exact_mod_cast (by omega : m < hammingDist x y * 8)
    rw [Nat.sub_add_cancel hpos, ← hS]
    exact hsepS.encard_le_packingNumber (Set.subset_univ _)

end TauCeti
