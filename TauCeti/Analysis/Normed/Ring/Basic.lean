/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.Ring.Idempotent

/-!
# Elementary inequalities in seminormed rings

This file records elementary consequences of the submultiplicativity of the norm (for instance, a
nonzero idempotent has norm at least `1`: `IsIdempotentElem.one_le_norm`, forcing an idempotent
of norm `< 1` to be `0` and one within `< 1` of `1` to be `1`), exact positive-power norms without
`NormOneClass`, an estimate for `‖w - 1‖` with `‖w‖ = 1` when the norm is multiplicative,
convergence to `0` of finite partial products when factors tend to `0` cofinitely
(`TauCeti.tendsto_finsetProd_cofinite_zero`), and norm bounds for powers of units — including the
shell lemma `Units.exists_lt_norm_zpow_lt` showing that the norms of integer powers of a unit `u`
with `‖u‖ < 1` in a nontrivial normed ring visit every open interval `(a, b)` with `0 ≤ a` and
`a * ‖u⁻¹‖ < b`.

The affine estimate `TauCeti.sub_mul_mem_closedBall_of_norm_le` bounds the distance of
`w₀ - w₁ * u` from `w₀` using a bound on the norm of `u`.

Among the former are the estimates `‖e * a - c‖ ≤ ‖e‖ ‖a - b‖ + ‖e * b - c‖`
(`TauCeti.norm_mul_sub_le_left`) and `‖a * e - c‖ ≤ ‖a - b‖ ‖e‖ + ‖b * e - c‖`
(`TauCeti.norm_mul_sub_le_right`), which compare a product with `c` through the product with `b`,
the nonvanishing `1 - x ≠ 0` for `‖x‖ < 1` (`TauCeti.one_sub_ne_zero_of_norm_lt_one`),
the lower bound `1 - ‖q‖ ≤ ‖1 - qⁿ‖` for `‖q‖ ≤ 1` and `n ≠ 0`
(`TauCeti.one_sub_norm_le_norm_one_sub_pow`),
and `‖a * c - b * d‖ₑ ≤ ‖a - b‖ₑ + ‖c - d‖ₑ` for `‖b‖ ≤ 1` and `‖c‖ ≤ 1`
(`TauCeti.enorm_mul_sub_mul_le`), which bounds the change of a product of two factors.
-/

public section

namespace TauCeti

/-- If `‖u‖ ≤ ρ`, then `w₀ - w₁ * u` lies in the closed ball of radius `‖w₁‖ * ρ` about `w₀`. -/
theorem sub_mul_mem_closedBall_of_norm_le {R : Type*} [NonUnitalSeminormedRing R]
    (w₀ w₁ : R) {u : R} {ρ : ℝ} (hu : ‖u‖ ≤ ρ) :
    w₀ - w₁ * u ∈ Metric.closedBall w₀ (‖w₁‖ * ρ) := by
  rw [mem_closedBall_iff_norm, sub_sub_cancel_left, norm_neg]
  exact norm_mul_le_of_le le_rfl hu

/-- A product of two elements in the open unit ball again belongs to the open unit ball. -/
theorem norm_mul_lt_one {K : Type*} [NonUnitalSeminormedRing K] (u v : K) (hu : ‖u‖ < 1)
    (hv : ‖v‖ < 1) : ‖u * v‖ < 1 := by
  calc
    ‖u * v‖ ≤ ‖u‖ * ‖v‖ := norm_mul_le _ _
    _ ≤ ‖u‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hv.le (norm_nonneg u)
    _ < 1 := hu

/-- The distance from `e * a` to `c` exceeds the distance from `e * b` to `c` by at most
`‖e‖ ‖a - b‖`: `‖e * a - c‖ ≤ ‖e‖ ‖a - b‖ + ‖e * b - c‖`. -/
theorem norm_mul_sub_le_left {R : Type*} [NonUnitalSeminormedRing R] (e a b c : R) :
    ‖e * a - c‖ ≤ ‖e‖ * ‖a - b‖ + ‖e * b - c‖ := by
  rw [← sub_add_sub_cancel (e * a) (e * b) c, ← mul_sub]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)

/-- The distance from `a * e` to `c` exceeds the distance from `b * e` to `c` by at most
`‖a - b‖ ‖e‖`: `‖a * e - c‖ ≤ ‖a - b‖ ‖e‖ + ‖b * e - c‖`. This is the right-multiplication
version of `TauCeti.norm_mul_sub_le_left`. -/
theorem norm_mul_sub_le_right {R : Type*} [NonUnitalSeminormedRing R] (e a b c : R) :
    ‖a * e - c‖ ≤ ‖a - b‖ * ‖e‖ + ‖b * e - c‖ := by
  rw [← sub_add_sub_cancel (a * e) (b * e) c, ← sub_mul]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)

/-- Replacing the factors `b` and `d` of `b * d` by `a` and `c` changes the product by at most the
sum of the two changes, `‖a * c - b * d‖ₑ ≤ ‖a - b‖ₑ + ‖c - d‖ₑ`, when `‖b‖ ≤ 1` and `‖c‖ ≤ 1`.
This is the normed counterpart of `TauCeti.abs_mul_sub_mul_le`. -/
theorem enorm_mul_sub_mul_le {R : Type*} [NonUnitalSeminormedRing R] {a b c d : R}
    (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) : ‖a * c - b * d‖ₑ ≤ ‖a - b‖ₑ + ‖c - d‖ₑ := by
  have h : ‖a * c - b * d‖ ≤ ‖a - b‖ + ‖c - d‖ := by
    rw [← sub_add_sub_cancel (a * c) (b * c) (b * d), ← sub_mul, ← mul_sub]
    exact norm_add_le_of_le ((norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hc))
      ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hb))
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _)
    (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h

/-- Consecutive powers stay in the open unit ball when the first factor is strictly inside
and the second factor is in the closed unit ball. -/
theorem norm_pow_succ_mul_pow_lt_one {K : Type*} [SeminormedRing K]
    (u v : K) (hu : ‖u‖ < 1) (hv : ‖v‖ ≤ 1) (n : ℕ) :
    ‖u ^ (n + 1) * v ^ n‖ < 1 := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simpa using hu
  calc
    ‖u ^ (n + 1) * v ^ n‖ ≤ ‖u ^ (n + 1)‖ * ‖v ^ n‖ := norm_mul_le _ _
    _ ≤ ‖u‖ ^ (n + 1) * ‖v‖ ^ n :=
      mul_le_mul (norm_pow_le' _ (Nat.succ_pos n)) (norm_pow_le' _ hn) (norm_nonneg _)
        (pow_nonneg (norm_nonneg _) _)
    _ ≤ ‖u‖ ^ (n + 1) * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hv)
        (pow_nonneg (norm_nonneg _) _)
    _ < 1 := by simpa using pow_lt_one₀ (norm_nonneg _) hu (Nat.succ_ne_zero n)

/-- For `‖q‖ < 1` also `‖qⁿ‖ < 1` for every `n ≠ 0`. -/
theorem norm_pow_lt_one {R : Type*} [SeminormedRing R] {q : R} (hq : ‖q‖ < 1) {n : ℕ}
    (hn : n ≠ 0) : ‖q ^ n‖ < 1 :=
  (norm_pow_le' q (Nat.pos_of_ne_zero hn)).trans_lt (pow_lt_one₀ (norm_nonneg q) hq hn)

/-- Multiplying by further powers of an element of norm at most one does not increase the norm:
`‖qⁿ⁺¹ w‖ ≤ ‖q w‖` when `‖q‖ ≤ 1`. -/
theorem norm_pow_succ_mul_le {R : Type*} [SeminormedRing R] {q : R} (hq : ‖q‖ ≤ 1) (w : R)
    (n : ℕ) : ‖q ^ (n + 1) * w‖ ≤ ‖q * w‖ := by
  induction n with
  | zero => rw [zero_add, pow_one]
  | succ n ih =>
    calc ‖q ^ (n + 1 + 1) * w‖ = ‖q * (q ^ (n + 1) * w)‖ := by rw [pow_succ', mul_assoc]
      _ ≤ ‖q‖ * ‖q ^ (n + 1) * w‖ := norm_mul_le _ _
      _ ≤ ‖q * w‖ := mul_le_of_le_one_left (norm_nonneg _) hq |>.trans ih

/-- Without the normalisation `‖1‖ = 1`, powers are still bounded by `‖xⁿ‖ ≤ max ‖1‖ 1 * ‖x‖ⁿ`,
including the power `x⁰ = 1`. -/
theorem norm_pow_le_max_mul {R : Type*} [SeminormedRing R] (x : R) (n : ℕ) :
    ‖x ^ n‖ ≤ max ‖(1 : R)‖ 1 * ‖x‖ ^ n := by
  rcases n with _ | n
  · simp
  · exact (norm_pow_le' x n.succ_pos).trans
      (le_mul_of_one_le_left (by positivity) (le_max_right _ _))

/-- Without the normalisation `‖1‖ = 1`, a product with a power still satisfies
`‖x * yⁿ‖ ≤ ‖x‖ * ‖y‖ⁿ`, including the case `n = 0`, where `x * y⁰ = x`. -/
theorem norm_mul_pow_le {R : Type*} [SeminormedRing R] (x y : R) (n : ℕ) :
    ‖x * y ^ n‖ ≤ ‖x‖ * ‖y‖ ^ n := by
  rcases n with _ | n
  · simp
  · exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_pow_le' y n.succ_pos) (norm_nonneg x))

/-- Left-multiplying by `uⁿ` decreases the norm by at most `‖u⁻¹‖ⁿ`, including the case `n = 0`. -/
theorem _root_.Units.norm_le_norm_inv_pow_mul_norm_pow_mul {R : Type*} [SeminormedRing R] (u : Rˣ)
    (n : ℕ) (x : R) :
    ‖x‖ ≤ ‖((u⁻¹ : Rˣ) : R)‖ ^ n * ‖(u : R) ^ n * x‖ := by
  rcases n with _ | n
  · simp
  · calc ‖x‖ = ‖(↑((u ^ (n + 1))⁻¹) : R) * (↑(u ^ (n + 1)) * x)‖ := by
          rw [Units.inv_mul_cancel_left]
      _ ≤ ‖(↑((u ^ (n + 1))⁻¹) : R)‖ * ‖↑(u ^ (n + 1)) * x‖ := norm_mul_le _ _
      _ = ‖((u⁻¹ : Rˣ) : R) ^ (n + 1)‖ * ‖(u : R) ^ (n + 1) * x‖ := by simp
      _ ≤ ‖((u⁻¹ : Rˣ) : R)‖ ^ (n + 1) * ‖(u : R) ^ (n + 1) * x‖ :=
          mul_le_mul_of_nonneg_right (norm_pow_le' _ n.succ_pos) (norm_nonneg _)

/-- In a nontrivial normed ring, `1 ≤ ‖u‖ⁿ * ‖u⁻ⁿ‖` for every unit `u` and every `n : ℕ`. -/
theorem _root_.Units.one_le_norm_pow_mul_norm_zpow_neg {R : Type*} [NormedRing R] [Nontrivial R]
    (u : Rˣ) (n : ℕ) :
    1 ≤ ‖(u : R)‖ ^ n * ‖((u ^ (-(n : ℤ)) : Rˣ) : R)‖ :=
  (one_le_norm_one R).trans <| by
    simpa [zpow_neg, ← inv_pow] using (u⁻¹).norm_le_norm_inv_pow_mul_norm_pow_mul n 1

/-- **Shells for submultiplicative unit powers.** In a nontrivial normed ring, the norms of integer
powers of a unit `u` with `‖u‖ < 1` visit every open interval `(a, b)` with `0 ≤ a` and
`a * ‖u⁻¹‖ < b`. Unlike `rescale_to_shell_zpow` (which applies `exists_mem_Ico_zpow` using
multiplicativity `‖u ^ z‖ = ‖u‖ ^ z`) or `TauCeti.NormedRing.PseudoUniformizer`, the norm need
not be multiplicative on `u`. -/
theorem _root_.Units.exists_lt_norm_zpow_lt {R : Type*} [NormedRing R] [Nontrivial R]
    (u : Rˣ) (hu : ‖(u : R)‖ < 1) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a * ‖((u⁻¹ : Rˣ) : R)‖ < b) :
    ∃ z : ℤ, a < ‖((u ^ z : Rˣ) : R)‖ ∧ ‖((u ^ z : Rˣ) : R)‖ < b := by
  let M : ℝ := ‖((u⁻¹ : Rˣ) : R)‖
  have hM : 0 < M := Units.norm_pos u⁻¹
  have hb : 0 < b := (mul_nonneg ha hM.le).trans_lt hab
  let φ (z : ℤ) : ℝ := ‖((u ^ z : Rˣ) : R)‖
  obtain ⟨m₁, hm₁⟩ := exists_pow_lt_of_lt_one hb hu
  have hφ₁ : φ (m₁ + 1 : ℕ) < b := by
    have hpow : ‖(u : R)‖ ^ (m₁ + 1) < b :=
      (pow_le_pow_of_le_one (norm_nonneg _) hu.le (Nat.le_succ m₁)).trans_lt hm₁
    simpa only [φ, zpow_natCast, Units.val_pow_eq_pow_val] using
      (norm_pow_le' (u : R) m₁.succ_pos).trans_lt hpow
  rcases ha.eq_or_lt with rfl | ha_pos
  · exact ⟨(m₁ + 1 : ℕ), Units.norm_pos _, hφ₁⟩
  obtain ⟨m₂, hm₂⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr ha_pos) hu
  have hpow₂ : ‖(u : R)‖ ^ (m₂ + 1) < a⁻¹ :=
    (pow_le_pow_of_le_one (norm_nonneg _) hu.le (Nat.le_succ m₂)).trans_lt hm₂
  let z₀ : ℤ := -((m₂ + 1 : ℕ) : ℤ)
  have hφ₀ : a < φ z₀ := by
    have h1 := u.one_le_norm_pow_mul_norm_zpow_neg (m₂ + 1)
    calc a = a * 1 := (mul_one a).symm
      _ ≤ a * (‖(u : R)‖ ^ (m₂ + 1) * φ z₀) := mul_le_mul_of_nonneg_left h1 ha
      _ < a * (a⁻¹ * φ z₀) :=
          mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hpow₂ (Units.norm_pos _)) ha_pos
      _ = φ z₀ := mul_inv_cancel_left₀ ha_pos.ne' _
  have hstep (z : ℤ) : φ z ≤ φ (z + 1) * M := by
    have hz : u ^ z = u ^ (z + 1) * u⁻¹ := by rw [zpow_add_one, mul_inv_cancel_right]
    have hval : ((u ^ z : Rˣ) : R) = ((u ^ (z + 1) : Rˣ) : R) * ((u⁻¹ : Rˣ) : R) :=
      congrArg Units.val hz
    exact (congrArg norm hval).le.trans (norm_mul_le _ _)
  suffices ∀ (k : ℕ) (w : ℤ), a < φ w → φ (w + k) < b → ∃ z, a < φ z ∧ φ z < b by
    obtain ⟨k, hk⟩ := Int.le.dest (by omega : z₀ ≤ ((m₁ + 1 : ℕ) : ℤ))
    exact this k z₀ hφ₀ (hk.symm ▸ hφ₁)
  intro k
  induction k with
  | zero => exact fun w haw hbw ↦ ⟨w, haw, by simpa using hbw⟩
  | succ k ih =>
    intro w haw hb₁
    rcases lt_or_ge a (φ (w + 1)) with hgt | hle
    · refine ih (w + 1) hgt ?_
      have heq : w + 1 + (k : ℤ) = w + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rwa [heq]
    · exact ⟨w, haw, ((hstep w).trans (mul_le_mul_of_nonneg_right hle hM.le)).trans_lt hab⟩

/-- Without the normalisation `‖1‖ = 1`, a product with a finite product of powers still
satisfies `‖b * ∏_{s ∈ S} (a s) ^ (e s)‖ ≤ ‖b‖ * ∏_{s ∈ S} ‖a s‖ ^ (e s)`, including empty `S`
and zero exponents. The product bounds `Finset.norm_prod_le`, `TauCeti.norm_prod_le_prod_norm`
and `Finsupp.norm_prod_pow_le` assume `NormOneClass`. -/
theorem _root_.Finset.norm_mul_prod_pow_le {ι R : Type*} [SeminormedCommRing R] (S : Finset ι)
    (a : ι → R) (e : ι → ℕ) (b : R) : ‖b * ∏ s ∈ S, a s ^ e s‖ ≤ ‖b‖ * ∏ s ∈ S, ‖a s‖ ^ e s := by
  classical
  induction S using Finset.induction_on generalizing b with
  | empty => simp
  | insert t S ht ih =>
    rw [Finset.prod_insert ht, Finset.prod_insert ht, ← mul_assoc, ← mul_assoc]
    exact (ih _).trans (by gcongr; exact norm_mul_pow_le _ _ _)

/-- Without the normalisation `‖1‖ = 1`, positive powers under a multiplicative norm satisfy
`‖x ^ (n + 1)‖ = ‖x‖ ^ (n + 1)`. -/
theorem norm_pow_succ {M : Type*} [Norm M] [Monoid M] [NormMulClass M] (x : M) (n : ℕ) :
    ‖x ^ (n + 1)‖ = ‖x‖ ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ x (n + 1), norm_mul, ih, pow_succ ‖x‖ (n + 1)]

/-- For a multiplicative norm with `‖1‖ = 1`, an element `w` of norm one and `r` of norm at most
one, `‖w - 1‖ ≤ ‖(w - 1) a‖ + 2 ‖a - r‖ + 2 (1 - ‖r‖)` for every `a`. So `w - 1` is controlled by
`(w - 1) a` wherever `a` is close to some `r` of norm close to one. -/
theorem norm_sub_one_le_norm_sub_one_mul_add {R : Type*} [SeminormedRing R] [NormMulClass R]
    [NormOneClass R] {w a r : R} (hw : ‖w‖ = 1) (hr : ‖r‖ ≤ 1) :
    ‖w - 1‖ ≤ ‖(w - 1) * a‖ + 2 * ‖a - r‖ + 2 * (1 - ‖r‖) := by
  have hw₂ : ‖w - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by norm_num [hw])
  have h₁ : ‖w - 1‖ * ‖r‖ ≤ ‖(w - 1) * a‖ + 2 * ‖a - r‖ := by
    calc ‖w - 1‖ * ‖r‖ = ‖(w - 1) * a - (w - 1) * (a - r)‖ := by
          rw [← norm_mul, ← mul_sub, sub_sub_cancel]
      _ ≤ ‖(w - 1) * a‖ + ‖w - 1‖ * ‖a - r‖ := by
          rw [← norm_mul]
          exact norm_sub_le _ _
      _ ≤ _ := by gcongr
  nlinarith [mul_nonneg (sub_nonneg.2 hw₂) (sub_nonneg.2 hr), norm_nonneg (w - 1)]

/-- A nonempty finite product is bounded by the product of the norms, in any seminormed
commutative ring. This is Mathlib's `Finset.norm_prod_le'`, which assumes `NormedCommRing`,
proved by induction on the finite set; it is the nonempty counterpart of
`TauCeti.norm_prod_le_prod_norm`. -/
theorem norm_prod_le_prod_norm_of_nonempty {ι R : Type*} [SeminormedCommRing R]
    {s : Finset ι} (hs : s.Nonempty) (f : ι → R) : ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha _ ih =>
    rw [Finset.prod_cons, Finset.prod_cons]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

/-- The norm of a finite product is bounded by the product of the norms, over a seminormed
commutative ring with `‖1‖ = 1`; that normalisation is used only for the empty product. Mathlib's
`Finset.norm_prod_le` states this only for a `NormedCommRing`. -/
theorem norm_prod_le_prod_norm {ι R : Type*} [SeminormedCommRing R] [NormOneClass R]
    (s : Finset ι) (f : ι → R) : ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · exact norm_prod_le_prod_norm_of_nonempty hs f

/-- **A finite product of unit-ball elements lies in the unit ball**, over a seminormed
commutative ring with `‖1‖ = 1`. -/
theorem norm_prod_le_one {ι R : Type*} [SeminormedCommRing R] [NormOneClass R] {s : Finset ι}
    {b : ι → R} (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) : ‖∏ i ∈ s, b i‖ ≤ 1 :=
  (norm_prod_le_prod_norm s b).trans (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) hb)

/-- **A finite product over a nonempty set of unit-ball elements lies in the unit ball**, over a
seminormed commutative ring, without assuming `‖1‖ = 1`. For the empty product, which is `1`, see
`TauCeti.norm_prod_le_one`. -/
theorem norm_prod_le_one_of_nonempty {ι R : Type*} [SeminormedCommRing R] {s : Finset ι}
    (hs : s.Nonempty) {b : ι → R} (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) : ‖∏ i ∈ s, b i‖ ≤ 1 :=
  (norm_prod_le_prod_norm_of_nonempty hs b).trans
    (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) hb)

/-- A point within distance `1` of `1` is not `0`. -/
theorem ne_zero_of_norm_sub_one_lt {R : Type*} [SeminormedRing R] [NormOneClass R] {z : R}
    (hz : ‖z - 1‖ < 1) : z ≠ 0 := by
  rintro rfl
  simp at hz

/-- An element of norm less than `1` is not `1`, that is, `1 - x ≠ 0`. -/
theorem one_sub_ne_zero_of_norm_lt_one {R : Type*} [SeminormedRing R] [NormOneClass R] {x : R}
    (hx : ‖x‖ < 1) : 1 - x ≠ 0 :=
  sub_ne_zero.2 fun h ↦ by simp [← h] at hx

/-- For `‖q‖ ≤ 1` and `n ≠ 0`, `1 - qⁿ` has norm at least `1 - ‖q‖`. -/
theorem one_sub_norm_le_norm_one_sub_pow {R : Type*} [SeminormedRing R] [NormOneClass R] {q : R}
    (hq : ‖q‖ ≤ 1) {n : ℕ} (hn : n ≠ 0) : 1 - ‖q‖ ≤ ‖1 - q ^ n‖ := by
  have h := norm_sub_norm_le (1 : R) (q ^ n)
  have h' : ‖q ^ n‖ ≤ ‖q‖ :=
    (norm_pow_le' q (Nat.pos_of_ne_zero hn)).trans (pow_le_of_le_one (norm_nonneg q) hq hn)
  rw [norm_one] at h
  linarith

/-- For `‖q‖ < 1` and `n ≠ 0`, `qⁿ ≠ 1`, that is, `1 - qⁿ ≠ 0`. For integer powers in a normed
division ring with `‖q‖ ≠ 1`, see `TauCeti.one_sub_zpow_ne_zero`. -/
theorem one_sub_pow_ne_zero {R : Type*} [SeminormedRing R] [NormOneClass R] {q : R}
    (hq : ‖q‖ < 1) {n : ℕ} (hn : n ≠ 0) : 1 - q ^ n ≠ 0 :=
  one_sub_ne_zero_of_norm_lt_one (norm_pow_lt_one hq hn)

/-- If `f` tends to `0` along the cofinite filter in a seminormed commutative ring, then so do its
finite partial products `s ↦ ∏ i ∈ s, f i`. -/
theorem tendsto_finsetProd_cofinite_zero {ι R : Type*} [SeminormedCommRing R] {f : ι → R}
    (hf : Filter.Tendsto f Filter.cofinite (nhds 0)) :
    Filter.Tendsto (fun s : Finset ι ↦ ∏ i ∈ s, f i) Filter.cofinite (nhds 0) := by
  classical
  have hfin (δ : ℝ) (hδ : 0 < δ) : {i : ι | δ ≤ ‖f i‖}.Finite :=
    (Filter.eventually_cofinite.mp (Metric.tendsto_nhds.mp hf δ hδ)).subset fun i hi ↦ by
      simpa [dist_zero_right] using hi
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hB := hfin 1 zero_lt_one
  set M := ∏ i ∈ hB.toFinset, max 1 ‖f i‖
  have hM1 : 1 ≤ M := Finset.one_le_prod₀ fun _ _ ↦ le_max_left 1 _
  have hC := hfin (min 1 (ε / M)) (lt_min zero_lt_one (div_pos hε (zero_lt_one.trans_le hM1)))
  refine (Finset.finite_toSet (insert ∅ hC.toFinset.powerset)).subset fun s hs ↦ ?_
  rw [Set.mem_compl_iff, Set.mem_ofPred_eq, dist_zero_right, not_lt] at hs
  rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_powerset]
  by_contra! h
  obtain ⟨j, hj, hjC⟩ := Finset.not_subset.mp h.2
  have hjlt : ‖f j‖ < ε / M :=
    (not_le.mp (hC.mem_toFinset.not.mp hjC)).trans_le (min_le_right _ _)
  have herase : ∏ i ∈ s.erase j, ‖f i‖ ≤ M := by
    rw [← Finset.prod_inter_mul_prod_sdiff (s.erase j) hB.toFinset]
    refine (mul_le_of_le_one_right (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
      (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun i hi ↦
        le_of_not_ge (hB.mem_toFinset.not.mp (Finset.mem_sdiff.mp hi).2))).trans ?_
    exact (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ le_max_right 1 ‖f i‖).trans
      (Finset.prod_le_prod_of_subset_of_one_le₀ Finset.inter_subset_right
        (fun _ _ ↦ by positivity) fun _ _ _ ↦ le_max_left 1 _)
  have hprod : ‖∏ i ∈ s, f i‖ < ε := by
    calc ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := norm_prod_le_prod_norm_of_nonempty ⟨j, hj⟩ f
      _ = ‖f j‖ * ∏ i ∈ s.erase j, ‖f i‖ := (Finset.mul_prod_erase s _ hj).symm
      _ ≤ ‖f j‖ * M := mul_le_mul_of_nonneg_left herase (norm_nonneg _)
      _ < ε / M * M := mul_lt_mul_of_pos_right hjlt (zero_lt_one.trans_le hM1)
      _ = ε := div_mul_cancel₀ ε (zero_lt_one.trans_le hM1).ne'
  exact hs.not_gt hprod

end TauCeti

namespace IsIdempotentElem

/-- A nonzero idempotent in a normed ring has norm at least `1`. -/
theorem one_le_norm {R : Type*} [NonUnitalNormedRing R] {p : R} (hp : IsIdempotentElem p)
    (hp0 : p ≠ 0) : 1 ≤ ‖p‖ :=
  (le_mul_iff_one_le_right (norm_pos_iff.mpr hp0)).mp <| by
    simpa only [hp.eq] using norm_mul_le p p

/-- An idempotent of norm strictly less than one in a nonunital normed ring is zero. -/
theorem eq_zero_of_norm_lt_one {R : Type*} [NonUnitalNormedRing R] {e : R}
    (he : IsIdempotentElem e) (h : ‖e‖ < 1) : e = 0 := by
  by_contra he₀
  exact (he.one_le_norm he₀).not_gt h

/-- An idempotent within norm distance `1` of `1` in a normed ring is `1`, since `1 - e` is an
idempotent of norm strictly less than `1`. -/
theorem eq_one_of_norm_sub_one_lt_one {R : Type*} [NormedRing R] {e : R}
    (he : IsIdempotentElem e) (h : ‖e - 1‖ < 1) : e = 1 :=
  sub_eq_zero.mp <| neg_eq_zero.mp <| by
    simpa only [neg_sub] using he.one_sub.eq_zero_of_norm_lt_one (by rwa [norm_sub_rev])

end IsIdempotentElem

end
