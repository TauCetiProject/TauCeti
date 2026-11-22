/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Positivity

/-!
# Monic integer polynomials in a weighted coefficient box

For a degree `n` and a real cutoff `X`, `TauCeti.monicWeightedBox n X` is the set of monic
integer polynomials `x^n + a₁ x^(n-1) + ⋯ + aₙ` of degree `n` with `|aᵢ| < X^i` for every `i`.
Giving the coefficient `aᵢ` weight `i` makes the discriminant of a monic polynomial weighted
homogeneous of weight `n(n-1)`, so this box is the natural height ball over which monic
polynomials with local or Galois conditions are counted. Indexed by the power of `x`, the
coefficient of `x^i` is bounded by `X^(n-i)`.

Removing the constant term, `Polynomial.divX` maps the degree `n + 1` box into the degree `n`
box. Induction along this map shows that the box is finite, with at most
`3^n X^(n(n+1)/2)` elements once `X ≥ 1`.
-/

public section

open Polynomial

namespace TauCeti

/-- The monic integer polynomials of degree `n` whose coefficient of `x^i` has absolute value
less than `X^(n-i)`, for every `i < n`. -/
def monicWeightedBox (n : ℕ) (X : ℝ) : Set ℤ[X] :=
  {f | f.Monic ∧ f.natDegree = n ∧ ∀ i < n, |(f.coeff i : ℝ)| < X ^ (n - i)}

@[simp]
theorem mem_monicWeightedBox {n : ℕ} {X : ℝ} {f : ℤ[X]} :
    f ∈ monicWeightedBox n X ↔
      f.Monic ∧ f.natDegree = n ∧ ∀ i < n, |(f.coeff i : ℝ)| < X ^ (n - i) :=
  Iff.rfl

/-- The only monic polynomial of degree zero is `1`. -/
@[simp]
theorem monicWeightedBox_zero (X : ℝ) : monicWeightedBox 0 X = {1} := by
  ext f
  simp only [mem_monicWeightedBox, Nat.not_lt_zero, false_imp_iff, imp_true_iff, and_true,
    Set.mem_singleton_iff]
  exact ⟨fun ⟨hf, hd⟩ ↦ hf.natDegree_eq_zero.mp hd,
    fun h ↦ h ▸ ⟨monic_one, natDegree_one⟩⟩

/-- Dropping the constant term maps the degree `n + 1` box into the degree `n` box. -/
theorem divX_mem_monicWeightedBox {n : ℕ} {X : ℝ} {f : ℤ[X]}
    (hf : f ∈ monicWeightedBox (n + 1) X) : f.divX ∈ monicWeightedBox n X := by
  obtain ⟨hm, hd, hc⟩ := mem_monicWeightedBox.mp hf
  have hdeg : f.divX.natDegree = n := by
    rw [natDegree_divX_eq_natDegree_tsub_one, hd, Nat.add_sub_cancel]
  refine ⟨?_, hdeg, fun i hi ↦ ?_⟩
  · rw [Monic, leadingCoeff, hdeg, coeff_divX, ← hd]
    exact hm
  · rw [coeff_divX]
    simpa using hc (i + 1) (by omega)

/-- A polynomial in the degree `n + 1` box is `X * g + C c` for some `g` in the degree `n` box
and some constant `c` with `|c| < X^(n+1)`. -/
private theorem monicWeightedBox_succ_subset (n : ℕ) (X : ℝ) :
    monicWeightedBox (n + 1) X ⊆ (fun p : ℤ[X] × ℤ ↦ p.1 * Polynomial.X + C p.2) ''
      (monicWeightedBox n X ×ˢ {c : ℤ | |(c : ℝ)| < X ^ (n + 1)}) := by
  intro f hf
  refine ⟨(f.divX, f.coeff 0), ⟨divX_mem_monicWeightedBox hf, ?_⟩, divX_mul_X_add f⟩
  simpa using (mem_monicWeightedBox.mp hf).2.2 0 (Nat.succ_pos n)

/-- The integers of absolute value less than `Y` lie in a finite interval. -/
private theorem setOf_abs_lt_subset (Y : ℝ) :
    {c : ℤ | |(c : ℝ)| < Y} ⊆ ↑(Finset.Ioo (-⌈Y⌉) ⌈Y⌉) := by
  intro c hc
  rw [Set.mem_ofPred_eq, abs_lt] at hc
  simp only [Finset.coe_Ioo, Set.mem_Ioo]
  constructor
  · have : (-⌈Y⌉ : ℝ) < c := by linarith [Int.le_ceil Y]
    exact_mod_cast this
  · exact Int.cast_lt.mp (hc.2.trans_le (Int.le_ceil Y))

/-- There are at most `3 Y` integers of absolute value less than `Y ≥ 1`. -/
private theorem ncard_setOf_abs_lt_le {Y : ℝ} (hY : 1 ≤ Y) :
    ({c : ℤ | |(c : ℝ)| < Y}.ncard : ℝ) ≤ 3 * Y := by
  have h := Set.ncard_le_ncard (setOf_abs_lt_subset Y) (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Int.card_Ioo] at h
  have hcast : ((⌈Y⌉ - -⌈Y⌉ - 1).toNat : ℝ) = 2 * ⌈Y⌉ - 1 := by
    have hpos : 0 ≤ ⌈Y⌉ - -⌈Y⌉ - 1 := by
      have : (1 : ℤ) ≤ ⌈Y⌉ := Int.one_le_ceil_iff.mpr (by linarith)
      omega
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hpos]
    push_cast
    ring
  have hceil : (⌈Y⌉ : ℝ) < Y + 1 := Int.ceil_lt_add_one Y
  calc ({c : ℤ | |(c : ℝ)| < Y}.ncard : ℝ) ≤ ((⌈Y⌉ - -⌈Y⌉ - 1).toNat : ℝ) := by
        exact_mod_cast h
    _ ≤ 3 * Y := by rw [hcast]; linarith

/-- The weighted box is finite. -/
theorem finite_monicWeightedBox (n : ℕ) (X : ℝ) : (monicWeightedBox n X).Finite := by
  induction n with
  | zero => simp
  | succ n ih =>
    exact (((ih.prod ((Finset.finite_toSet _).subset (setOf_abs_lt_subset _))).image
      _).subset (monicWeightedBox_succ_subset n X))

/-- For `X ≥ 1`, the degree `n` weighted box has at most `3^n X^(n(n+1)/2)` elements. -/
theorem ncard_monicWeightedBox_le (n : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    ((monicWeightedBox n X).ncard : ℝ) ≤ 3 ^ n * X ^ (n * (n + 1) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hfin : {c : ℤ | |(c : ℝ)| < X ^ (n + 1)}.Finite :=
      (Finset.finite_toSet _).subset (setOf_abs_lt_subset _)
    have hle := Set.ncard_le_ncard (monicWeightedBox_succ_subset n X)
      (((finite_monicWeightedBox n X).prod hfin).image _)
    have himage := Set.ncard_image_le (f := fun p : ℤ[X] × ℤ ↦ p.1 * Polynomial.X + C p.2)
      ((finite_monicWeightedBox n X).prod hfin)
    rw [Set.ncard_prod] at himage
    have hexp : (n + 1) * (n + 1 + 1) / 2 = n * (n + 1) / 2 + (n + 1) := by
      rw [show (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) by ring,
        Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    calc ((monicWeightedBox (n + 1) X).ncard : ℝ)
        ≤ ((monicWeightedBox n X).ncard : ℝ) * {c : ℤ | |(c : ℝ)| < X ^ (n + 1)}.ncard := by
          exact_mod_cast hle.trans himage
      _ ≤ (3 ^ n * X ^ (n * (n + 1) / 2)) * (3 * X ^ (n + 1)) :=
          mul_le_mul ih (ncard_setOf_abs_lt_le (one_le_pow₀ hX)) (by positivity)
            (by positivity)
      _ = 3 ^ (n + 1) * X ^ ((n + 1) * (n + 1 + 1) / 2) := by
          rw [hexp, pow_add, pow_succ]
          ring

end TauCeti
