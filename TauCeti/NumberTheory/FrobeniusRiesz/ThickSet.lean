/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.Combinatorics.Additive.NoRelation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-!
# Dense thick sets in cyclic subgroups

Exponent sets without short relations give thick sets by taking powers of a generator of a
cyclic subgroup. The short interval of exponents preserves the cardinality under this map.
If the ambient group size lies between fixed powers of a scale `x`, the subgroup index is
bounded, and the forbidden relation length is at most `(log x)²`, the thick set can be chosen
with relative density at least `x⁻ᵋ` for any fixed positive `ε`. The same threshold works for
all such groups. This is the density needed when averaging Frobenius-restricted prime sums;
the short interval and relation exclusion also control intersections with Frobenius orbits.

The construction uses the Behrend–Ruzsa bound `TauCeti.exists_noRelation`. The application to
thick sets is from Levent Alpöge's formalization (`Formalism.FrobeniusOrbits.HostThickExists`).
-/

public section

open Filter Real

namespace TauCeti

/-- The loss in the relation-free set bound is subpolynomial, uniformly for moduli bounded by
a power of `x` and lengths bounded by `(log x)²`. Include a fixed extra factor `o` so the same
estimate controls density in an ambient group of index at most `o` over the modulus group. -/
private theorem eventually_behrend_loss_le (C b : ℝ) (o : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ M L : ℕ, 0 < L → (M : ℝ) ≤ x ^ b →
      (L : ℝ) ≤ log x ^ 2 →
      (o : ℝ) * L * exp (C * sqrt (log M * log L)) ≤ x ^ ε := by
  let r := ε / (3 * (|C| + 1))
  let δ := min (ε / 3) (r ^ 2 / max b 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hb : 0 < max b 1 := zero_lt_one.trans_le (le_max_right ..)
  have hδ : 0 < δ := lt_min (by positivity) (div_pos (sq_pos_of_pos hr) hb)
  have hd : ∀ᶠ x : ℝ in atTop, log x ^ 2 ≤ x ^ δ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ),
      (isLittleO_log_rpow_rpow_atTop 2 hδ).bound zero_lt_one] with x hx₀ hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx₀, rpow_two, rpow_nonneg hx₀,
      abs_of_nonneg (sq_nonneg (log x)), abs_of_nonneg (rpow_nonneg hx₀ δ), one_mul] using hx
  have ho := (tendsto_rpow_atTop (show 0 < ε / 3 by positivity)).eventually_ge_atTop (o : ℝ)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hd, ho] with x hx hlog ho
  intro M L hL hMb hLb
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hLδ := hLb.trans hlog
  have hxlog := log_nonneg hx
  have hlogM : log (M : ℝ) ≤ max b 1 * log x := by
    rcases M.eq_zero_or_pos with rfl | hM
    · simpa using mul_nonneg hb.le hxlog
    rw [← log_rpow hx₀]
    exact log_le_log (by positivity) (hMb.trans (rpow_le_rpow_of_exponent_le hx (le_max_left ..)))
  have hlogL : log (L : ℝ) ≤ δ * log x := by
    rw [← log_rpow hx₀]
    exact log_le_log (by positivity) hLδ
  have hδb : max b 1 * δ ≤ r ^ 2 := by
    rw [mul_comm]
    exact (le_div_iff₀ hb).mp (min_le_right ..)
  have hs : sqrt (log M * log L) ≤ r * log x := by
    refine (sqrt_le_sqrt ?_).trans_eq (sqrt_sq (mul_nonneg hr.le hxlog))
    calc
      _ ≤ (max b 1 * log x) * (δ * log x) :=
        mul_le_mul hlogM hlogL (log_natCast_nonneg L) (mul_nonneg hb.le hxlog)
      _ = (max b 1 * δ) * log x ^ 2 := by ring
      _ ≤ r ^ 2 * log x ^ 2 := mul_le_mul_of_nonneg_right hδb (sq_nonneg _)
      _ = (r * log x) ^ 2 := by ring
  have hexp : exp (C * sqrt (log M * log L)) ≤ x ^ (ε / 3) := by
    rw [rpow_def_of_pos hx₀, exp_le_exp, mul_comm (log x)]
    calc
      _ ≤ |C| * sqrt (log M * log L) := mul_le_mul_of_nonneg_right (le_abs_self _) (sqrt_nonneg _)
      _ ≤ (|C| + 1) * (r * log x) := by gcongr; linarith
      _ = ε / 3 * log x := by dsimp [r]; field_simp
  calc
    _ ≤ x ^ (ε / 3) * x ^ (ε / 3) * x ^ (ε / 3) := by
      gcongr
      exact hLδ.trans (rpow_le_rpow_of_exponent_le hx (min_le_left ..))
    _ = _ := by rw [← rpow_add hx₀, ← rpow_add hx₀]; ring_nf

open Classical in
/-- In a cyclic subgroup of bounded index in a finite group of polynomial size, one can choose
a thick set of density at least `x ^ (-ε)`, for any relation length `2 ≤ L ≤ (log x)²`.
The threshold depends only on the size exponents, index bound, and `ε`, not on the group.
The integer exponents are nonnegative and less than `|H| / (4L)`, and the power image has at
most `|H| / (4L)` points. -/
theorem eventually_exists_thickSet_density {a b ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (o : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ {G : Type*} [Group G] (H : Subgroup G) [IsCyclic H],
      H.index ≤ o → x ^ a ≤ (Nat.card G : ℝ) → (Nat.card G : ℝ) ≤ x ^ b →
      ∀ L : ℕ, 2 ≤ L → (L : ℝ) ≤ log x ^ 2 →
      ∃ (g : H) (T : Finset ℤ), orderOf g = Nat.card H ∧ T.Nonempty ∧
        (∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < Nat.card H / (4 * L)) ∧ NoRelation L T ∧
        (Nat.card G : ℝ) * x ^ (-ε) ≤ (T.image (g ^ ·)).card ∧
        ((T.image (g ^ ·)).card : ℝ) ≤ Nat.card H / (4 * L) := by
  obtain ⟨C, hC⟩ := exists_noRelation
  have hsmall : ∀ᶠ x : ℝ in atTop, (4 * (o : ℝ)) * log x ^ 2 ≤ x ^ a := by
    have h := (isLittleO_log_rpow_rpow_atTop 2 ha).const_mul_left (4 * (o : ℝ))
    filter_upwards [eventually_ge_atTop (0 : ℝ), h.bound zero_lt_one] with x hx₀ hx
    simpa only [Real.norm_eq_abs, one_mul, rpow_two, abs_of_nonneg hx₀,
      abs_of_nonneg (show 0 ≤ 4 * (o : ℝ) * log x ^ 2 by positivity),
      abs_of_nonneg (rpow_nonneg hx₀ a)] using hx
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall, eventually_behrend_loss_le C b o hε]
    with x hx hxsmall hloss
  intro G _ H _ hindex hlo hhi L hL hLx
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hGpos := (rpow_pos_of_pos hx₀ a).trans_le hlo
  have : Finite G := Nat.finite_of_card_ne_zero (by exact_mod_cast hGpos.ne')
  have hN : (Nat.card G : ℝ) = (Nat.card H : ℝ) * H.index := by exact_mod_cast H.card_mul_index.symm
  have h4L : 4 * L ≤ Nat.card H := by
    have hprod : (4 * (L : ℝ)) * o ≤ (Nat.card H : ℝ) * o := calc
      _ = 4 * (o : ℝ) * L := by ring
      _ ≤ 4 * (o : ℝ) * log x ^ 2 := by gcongr
      _ ≤ x ^ a := hxsmall
      _ ≤ Nat.card G := hlo
      _ ≤ (Nat.card H : ℝ) * o := by rw [hN]; gcongr
    exact_mod_cast le_of_mul_le_mul_right hprod (Nat.cast_pos.mpr (H.index_pos.trans_le hindex))
  obtain ⟨T, hT, hinterval, hrel, hcard, hupper⟩ := hC (Nat.card H) L Nat.card_pos hL
  obtain ⟨g, hg⟩ := exists_zpow_surjective H
  have hord : orderOf g = Nat.card H := orderOf_eq_card_of_forall_mem_zpowers
    fun y ↦ Subgroup.mem_zpowers_iff.mpr (hg y)
  have himage : (T.image (g ^ ·)).card = T.card := by
    refine Finset.card_image_iff.mpr fun s hs t ht heq ↦ ?_
    obtain ⟨hs₀, hs₁⟩ := hinterval s hs
    obtain ⟨ht₀, ht₁⟩ := hinterval t ht
    have hb := div_le_self (Nat.cast_nonneg (α := ℝ) (Nat.card H))
      (by exact_mod_cast (show 1 ≤ 4 * L by omega) : (1 : ℝ) ≤ 4 * L)
    have hst : |(t : ℝ) - s| < (orderOf g : ℝ) := by
      rw [hord, abs_lt]
      have hs' : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs₀
      have ht' : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht₀
      constructor <;> linarith
    exact (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd (zpow_eq_zpow_iff_modEq.mp heq).dvd
      (by exact_mod_cast hst))).symm
  refine ⟨g, T, hord, hT, hinterval, hrel, ?_, by rw [himage]; exact hupper h4L⟩
  rw [himage]
  refine le_trans ?_ hcard
  have hMhi := (Nat.cast_le.mpr (Nat.card_le_card_of_injective ((↑) : H → G)
    Subtype.val_injective) : (Nat.card H : ℝ) ≤ Nat.card G).trans hhi
  rw [neg_mul, exp_neg, rpow_neg hx₀.le, ← div_eq_mul_inv, hN, ← div_eq_mul_inv, div_div,
    div_le_div_iff₀ (rpow_pos_of_pos hx₀ _) (by positivity)]
  calc
    _ = (Nat.card H : ℝ) * (H.index * L * exp (C * sqrt (log (Nat.card H) * log L))) := by ring
    _ ≤ (Nat.card H : ℝ) * ((o : ℝ) * L * exp (C * sqrt (log (Nat.card H) * log L))) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left (hloss _ _ (by omega) hMhi hLx) (Nat.cast_nonneg _)

end TauCeti
