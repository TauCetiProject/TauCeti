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

/-- A fixed multiple of `(log x)²` is eventually at most any positive power of `x`. -/
private theorem eventually_mul_log_sq_le_rpow (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, c * log x ^ 2 ≤ x ^ δ := by
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    ((isLittleO_log_rpow_rpow_atTop 2 hδ).const_mul_left c).bound zero_lt_one] with x hx₀ hx
  rw [one_mul, norm_of_nonneg (rpow_nonneg hx₀ δ), rpow_two] at hx
  exact (le_norm_self _).trans hx

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
    simpa only [one_mul] using eventually_mul_log_sq_le_rpow 1 hδ
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

/-- Integer exponents in `[0, orderOf g)` give distinct powers of `g`. -/
private theorem injOn_zpow_of_lt_orderOf {G : Type*} [Group G] {g : G} {T : Set ℤ}
    (hT : ∀ s ∈ T, 0 ≤ s ∧ s < orderOf g) : Set.InjOn (g ^ ·) T := by
  intro s hs t ht heq
  have := hT s hs
  have := hT t ht
  exact (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd (zpow_eq_zpow_iff_modEq.mp heq).dvd
    (by rw [abs_lt]; omega))).symm

/-- In a cyclic subgroup `H` of bounded index in a finite group `G` of polynomial size, one can
choose a thick set `(g ^ ·) '' T ⊆ G` of density at least `x ^ (-ε)`, for any relation length
`2 ≤ L ≤ (log x)²`. Here `g ∈ G` generates `H`, so `orderOf g = |H|`. The threshold depends only
on the size exponents, index bound, and `ε`, not on the group. The integer exponents are
nonnegative and less than `orderOf g / (4L)`, so `s ↦ g ^ s` is injective on `T` and the thick
set has `|T| ≤ orderOf g / (4L)` points. -/
theorem eventually_exists_thickSet_density {a b ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (o : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ {G : Type*} [Group G] (H : Subgroup G) [IsCyclic H],
      H.index ≤ o → x ^ a ≤ (Nat.card G : ℝ) → (Nat.card G : ℝ) ≤ x ^ b →
      ∀ L : ℕ, 2 ≤ L → (L : ℝ) ≤ log x ^ 2 →
      ∃ (g : G) (T : Finset ℤ), Subgroup.zpowers g = H ∧ orderOf g = Nat.card H ∧
        T.Nonempty ∧ (∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf g / (4 * L)) ∧ NoRelation L T ∧
        (Nat.card G : ℝ) * x ^ (-ε) ≤ ((g ^ ·) '' (T : Set ℤ)).ncard ∧
        (((g ^ ·) '' (T : Set ℤ)).ncard : ℝ) ≤ orderOf g / (4 * L) := by
  obtain ⟨C, hC⟩ := exists_noRelation
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_mul_log_sq_le_rpow (4 * o) ha,
    eventually_behrend_loss_le C b o hε]
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
  obtain ⟨g, hzp⟩ := H.isCyclic_iff_exists_zpowers_eq.mp ‹_›
  have hord : orderOf g = Nat.card H := by rw [← hzp, Nat.card_zpowers]
  have hinterval' : ∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf g / (4 * L) := hord ▸ hinterval
  have hb := div_le_self (Nat.cast_nonneg (α := ℝ) (orderOf g))
    (by exact_mod_cast (show 1 ≤ 4 * L by omega) : (1 : ℝ) ≤ 4 * L)
  have himage : ((g ^ ·) '' (T : Set ℤ)).ncard = T.card := by
    refine (Set.InjOn.ncard_image (injOn_zpow_of_lt_orderOf fun s hs ↦ ?_)).trans
      (Set.ncard_coe_finset T)
    exact ⟨(hinterval' s hs).1, by exact_mod_cast (hinterval' s hs).2.trans_le hb⟩
  refine ⟨g, T, hzp, hord, hT, hinterval', hrel, ?_, by rw [himage, hord]; exact hupper h4L⟩
  rw [himage]
  refine le_trans ?_ hcard
  have hMhi := (Nat.cast_le.mpr (Nat.card_le_card_of_injective ((↑) : H → G)
    Subtype.val_injective) : (Nat.card H : ℝ) ≤ Nat.card G).trans hhi
  set E := exp (C * sqrt (log (Nat.card H) * log L))
  have hEE : exp (-C * sqrt (log (Nat.card H) * log L)) * E = 1 := by
    rw [← exp_add]; simp
  have hxx : x ^ ε * x ^ (-ε) = 1 := by rw [← rpow_add hx₀, add_neg_cancel, rpow_zero]
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  calc
    (Nat.card G : ℝ) * x ^ (-ε)
      = (Nat.card H : ℝ) * exp (-C * sqrt (log (Nat.card H) * log L)) / L *
          ((H.index * L * E) * x ^ (-ε)) := by
      rw [hN, div_mul_eq_mul_div, eq_div_iff hL0]
      linear_combination (-(Nat.card H * H.index * x ^ (-ε) * L) : ℝ) * hEE
    _ ≤ (Nat.card H : ℝ) * exp (-C * sqrt (log (Nat.card H) * log L)) / L *
          (x ^ ε * x ^ (-ε)) := by
      gcongr
      exact le_trans (by gcongr) (hloss _ _ (by omega) hMhi hLx)
    _ = _ := by rw [hxx, mul_one]

end TauCeti
