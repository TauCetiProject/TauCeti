/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Elementary inequalities in seminormed rings

This file records elementary consequences of the submultiplicativity of the norm, an estimate for
`‖w - 1‖` with `‖w‖ = 1` when the norm is multiplicative, and norm bounds for powers of units —
including the shell lemma `Units.exists_lt_norm_zpow_lt` showing that integer powers of a unit `u`
with `‖u‖ < 1` in a nontrivial normed ring visit every interval `(a, b)` with `0 ≤ a` and
`a * ‖u⁻¹‖ < b`.
-/

public section

namespace TauCeti

/-- A product of two elements in the open unit ball again belongs to the open unit ball. -/
theorem norm_mul_lt_one {K : Type*} [NonUnitalSeminormedRing K] (u v : K) (hu : ‖u‖ < 1)
    (hv : ‖v‖ < 1) : ‖u * v‖ < 1 := by
  calc
    ‖u * v‖ ≤ ‖u‖ * ‖v‖ := norm_mul_le _ _
    _ ≤ ‖u‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hv.le (norm_nonneg u)
    _ < 1 := hu

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
theorem _root_.Units.norm_le_pow_inv_mul_norm_pow_mul {R : Type*} [SeminormedRing R] (u : Rˣ)
    (n : ℕ) (x : R) :
    ‖x‖ ≤ ‖((u⁻¹ : Rˣ) : R)‖ ^ n * ‖(u : R) ^ n * x‖ := by
  rcases n with _ | n
  · simp
  · have hx : x = ((u⁻¹ : Rˣ) : R) ^ (n + 1) * ((u : R) ^ (n + 1) * x) := by
      rw [← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
        inv_pow, inv_mul_cancel, Units.val_one, one_mul]
    calc ‖x‖ = ‖((u⁻¹ : Rˣ) : R) ^ (n + 1) * ((u : R) ^ (n + 1) * x)‖ := congrArg norm hx
      _ ≤ ‖((u⁻¹ : Rˣ) : R) ^ (n + 1)‖ * ‖(u : R) ^ (n + 1) * x‖ := norm_mul_le _ _
      _ ≤ ‖((u⁻¹ : Rˣ) : R)‖ ^ (n + 1) * ‖(u : R) ^ (n + 1) * x‖ :=
          mul_le_mul_of_nonneg_right (norm_pow_le' _ n.succ_pos) (norm_nonneg _)

/-- In a nontrivial normed ring, `1 ≤ ‖u‖ⁿ * ‖u⁻ⁿ‖` for every unit `u` and every `n : ℕ`. -/
theorem _root_.Units.one_le_pow_norm_mul_norm_zpow_neg {R : Type*} [NormedRing R] [Nontrivial R]
    (u : Rˣ) (n : ℕ) :
    1 ≤ ‖(u : R)‖ ^ n * ‖((u ^ (-(n : ℤ)) : Rˣ) : R)‖ := by
  rcases n with _ | n
  · simpa using one_le_norm_one R
  · have hmul : (u : R) ^ (n + 1) * ((u ^ (-((n + 1 : ℕ) : ℤ)) : Rˣ) : R) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← Units.val_mul, ← zpow_add,
        add_neg_cancel, zpow_zero, Units.val_one]
    calc (1 : ℝ) ≤ ‖(1 : R)‖ := one_le_norm_one R
      _ = ‖(u : R) ^ (n + 1) * ((u ^ (-((n + 1 : ℕ) : ℤ)) : Rˣ) : R)‖ := congrArg norm hmul.symm
      _ ≤ ‖(u : R) ^ (n + 1)‖ * ‖((u ^ (-((n + 1 : ℕ) : ℤ)) : Rˣ) : R)‖ := norm_mul_le _ _
      _ ≤ ‖(u : R)‖ ^ (n + 1) * ‖((u ^ (-((n + 1 : ℕ) : ℤ)) : Rˣ) : R)‖ :=
          mul_le_mul_of_nonneg_right (norm_pow_le' (u : R) n.succ_pos) (norm_nonneg _)

/-- **Shells for submultiplicative unit powers.** In a nontrivial normed ring, the norms of integer
powers of a unit `u` with `‖u‖ < 1` visit every open interval `(a, b)` with `0 ≤ a` and
`a * ‖u⁻¹‖ < b`. Unlike `exists_mem_Ico_zpow` or `TauCeti.NormedRing.PseudoUniformizer`, the norm
need not be multiplicative on `u`. -/
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
    have h1 := u.one_le_pow_norm_mul_norm_zpow_neg (m₂ + 1)
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

/-- A point within distance `1` of `1` is not `0`. -/
theorem ne_zero_of_norm_sub_one_lt {R : Type*} [SeminormedRing R] [NormOneClass R] {z : R}
    (hz : ‖z - 1‖ < 1) : z ≠ 0 := by
  rintro rfl
  simp at hz

end TauCeti

end
