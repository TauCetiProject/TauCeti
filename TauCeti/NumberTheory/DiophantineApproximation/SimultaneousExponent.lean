/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Exponent
import TauCeti.NumberTheory.DiophantineApproximation.Dirichlet

/-!
# The simultaneous Diophantine approximation exponent

For a finite family `θ : ι → ℝ`, this file defines its simultaneous approximation
exponent as the supremum of the real numbers `w` for which infinitely many positive integers `q`
admit integers `pᵢ` satisfying

`|q θᵢ - pᵢ| ≤ q⁻ʷ`

for every `i`. Using positive denominators instead of arbitrary nonzero integer first coordinates
does not change the exponent: negating every coordinate makes the two formulations equivalent.
Recording only denominators also does not change infinitude, since for fixed `q` the displayed
bounds leave only finitely many choices for the integer vector.

The main results identify the one-dimensional exponent of an irrational real number with its
irrationality exponent, up to the expected shift by one, show that a rational family and an empty
family have infinite exponent, and show that forgetting coordinates can only increase the
exponent. Dirichlet's theorem gives the lower bound `1 / n` for a family of `n` real numbers
(`inv_card_le_simultaneousExponent`).

## References

* Y. Bugeaud, *Exponents of Diophantine approximation*, in *Dynamics and Analytic Number Theory*,
  London Math. Soc. Lecture Note Ser. 437, Cambridge Univ. Press (2016), §2, Definition 2.2.
  The exponent defined here is that simultaneous exponent, restated with positive denominators as
  explained above. The lower bound `1 / n` is the simultaneous half of Theorem 2.5.
-/

public section

open Filter
open scoped ENNReal Matrix

namespace TauCeti

variable {ι κ : Type*}

/-- The positive denominators giving simultaneous approximations to `θ` with exponent `w`. -/
def simultaneousApproximationDenominators (θ : ι → ℝ) (w : ℝ) : Set ℕ :=
  {q | 0 < q ∧ ∃ p : ι → ℤ, ∀ i, |(q : ℝ) * θ i - p i| ≤ (q : ℝ) ^ (-w)}

/-- A natural number is an admissible denominator exactly when it is positive and has integer
numerators approximating every coordinate to within the exponent bound. -/
@[simp]
theorem mem_simultaneousApproximationDenominators {θ : ι → ℝ} {w : ℝ} {q : ℕ} :
    q ∈ simultaneousApproximationDenominators θ w ↔
      0 < q ∧ ∃ p : ι → ℤ, ∀ i, |(q : ℝ) * θ i - p i| ≤ (q : ℝ) ^ (-w) :=
  Iff.rfl

/-- The simultaneous approximation exponent of a finite family `θ`. -/
noncomputable def simultaneousExponent (θ : ι → ℝ) : ℝ≥0∞ :=
  ⨆ (w : ℝ) (_ : (simultaneousApproximationDenominators θ w).Infinite), ENNReal.ofReal w

/-- The simultaneous exponent is the supremum of the exponents admitting infinitely many
simultaneous approximations. -/
theorem simultaneousExponent_def (θ : ι → ℝ) :
    simultaneousExponent θ =
      ⨆ (w : ℝ) (_ : (simultaneousApproximationDenominators θ w).Infinite),
        ENNReal.ofReal w := by
  rw [simultaneousExponent]

/-- Every exponent admitting infinitely many simultaneous approximations is bounded by the
simultaneous exponent. -/
theorem le_simultaneousExponent_of_infinite {θ : ι → ℝ} {w : ℝ}
    (h : (simultaneousApproximationDenominators θ w).Infinite) :
    ENNReal.ofReal w ≤ simultaneousExponent θ :=
  le_iSup_of_le w <| le_iSup_of_le h le_rfl

/-- The simultaneous exponent is at most `a` exactly when every exponent admitting infinitely
many simultaneous approximations is. -/
theorem simultaneousExponent_le_iff {θ : ι → ℝ} {a : ℝ≥0∞} :
    simultaneousExponent θ ≤ a ↔
      ∀ w : ℝ, (simultaneousApproximationDenominators θ w).Infinite → ENNReal.ofReal w ≤ a :=
  iSup₂_le_iff

/-- Increasing the exponent can only shrink the set of admissible denominators. -/
theorem simultaneousApproximationDenominators_antitone (θ : ι → ℝ) :
    Antitone (simultaneousApproximationDenominators θ) := by
  rintro w w' hw q ⟨hq, p, hp⟩
  refine ⟨hq, p, fun i ↦ (hp i).trans ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq) (neg_le_neg hw)

/-- Every real exponent strictly below the simultaneous exponent admits infinitely many
simultaneous approximations. -/
theorem infinite_simultaneousApproximationDenominators_of_lt_simultaneousExponent
    {θ : ι → ℝ} {w : ℝ} (h : ENNReal.ofReal w < simultaneousExponent θ) :
    (simultaneousApproximationDenominators θ w).Infinite := by
  simp only [simultaneousExponent, lt_iSup_iff] at h
  obtain ⟨w', hw', hww'⟩ := h
  exact hw'.mono <|
    simultaneousApproximationDenominators_antitone θ (ENNReal.ofReal_lt_ofReal_iff'.mp hww').1.le

/-- Restricting a family of simultaneous approximations along any map preserves every
admissible denominator. -/
theorem simultaneousApproximationDenominators_mono_comp
    (θ : ι → ℝ) (f : κ → ι) (w : ℝ) :
    simultaneousApproximationDenominators θ w ⊆
      simultaneousApproximationDenominators (θ ∘ f) w := by
  rintro q ⟨hq, p, hp⟩
  exact ⟨hq, p ∘ f, fun i ↦ hp (f i)⟩

/-- Forgetting coordinates cannot decrease the simultaneous approximation exponent. The result
does not require the reindexing map to be injective. -/
theorem simultaneousExponent_le_comp (θ : ι → ℝ) (f : κ → ι) :
    simultaneousExponent θ ≤ simultaneousExponent (θ ∘ f) := by
  refine simultaneousExponent_le_iff.2 fun w h ↦ le_simultaneousExponent_of_infinite ?_
  exact h.mono (simultaneousApproximationDenominators_mono_comp θ f w)

/-! ### Rational families -/

/-- A finite family of rational real numbers has infinite simultaneous exponent. -/
theorem simultaneousExponent_eq_top_of_forall_rat [Finite ι] {θ : ι → ℝ}
    (hθ : ∀ i, ∃ r : ℚ, (r : ℝ) = θ i) : simultaneousExponent θ = ⊤ := by
  let _ := Fintype.ofFinite ι
  choose r hr using hθ
  let d := ∏ i, (r i).den
  have hd : 0 < d := Finset.prod_pos fun i _ ↦ (r i).den_pos
  have hden (i : ι) : (r i).den ∣ d :=
    Finset.dvd_prod_of_mem (fun j ↦ (r j).den) (Finset.mem_univ i)
  have hinfinite (w : ℝ) : (simultaneousApproximationDenominators θ w).Infinite := by
    refine Set.infinite_of_forall_exists_gt fun N ↦ ?_
    refine ⟨(N + 1) * d, ?_, ?_⟩
    · refine ⟨Nat.mul_pos N.succ_pos hd,
        fun i ↦ round ((((N + 1) * d : ℕ) : ℝ) * θ i), fun i ↦ ?_⟩
      obtain ⟨k, hk⟩ := hden i
      have hzero := (r i).abs_den_mul_sub_round_eq_zero ((N + 1) * k)
      have hz : abs (((((N + 1) * d : ℕ) : ℝ) * θ i) -
          (round ((((N + 1) * d : ℕ) : ℝ) * θ i) : ℝ)) = 0 := by
        rw [← hr i]
        simpa only [hk, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm] using hzero
      rw [hz]
      positivity
    · calc
        N < N + 1 := Nat.lt_succ_self N
        _ = (N + 1) * 1 := by omega
        _ ≤ (N + 1) * d := Nat.mul_le_mul_left (N + 1) hd
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  refine iSup_le fun n ↦ ?_
  simpa using le_simultaneousExponent_of_infinite (hinfinite n)

/-- A family indexed by an empty type has infinite simultaneous exponent. -/
@[simp]
theorem simultaneousExponent_of_isEmpty [IsEmpty ι] (θ : ι → ℝ) : simultaneousExponent θ = ⊤ :=
  simultaneousExponent_eq_top_of_forall_rat isEmptyElim

/-! ### Dirichlet's lower bound -/

/-- **Dirichlet's theorem, infinitely many denominators.** For every finite family `θ`,
infinitely many positive integers `q` admit integers `pᵢ` with `|q θᵢ - pᵢ| ≤ q ^ (-1 / n)` for
every `i`, where `n` is the number of coordinates. -/
theorem infinite_simultaneousApproximationDenominators_inv_card [Fintype ι] (θ : ι → ℝ) :
    (simultaneousApproximationDenominators θ (Fintype.card ι : ℝ)⁻¹).Infinite := by
  by_cases h : ∃ i, Irrational (θ i)
  swap
  · -- A rational family has infinite exponent, so every exponent has infinitely many solutions.
    refine infinite_simultaneousApproximationDenominators_of_lt_simultaneousExponent ?_
    rw [simultaneousExponent_eq_top_of_forall_rat fun i ↦ by
      simpa [Irrational] using not_exists.mp h i]
    exact ENNReal.ofReal_lt_top
  obtain ⟨i₀, hi₀⟩ := h
  have : Nonempty ι := ⟨i₀⟩
  have hn : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  refine Set.infinite_of_forall_exists_gt fun N ↦ ?_
  -- The distances from `k θ i₀` to the nearest integer, `1 ≤ k ≤ N`, are positive, so Dirichlet's
  -- theorem with a large parameter `Q` produces a denominator `q > N`.
  have hpos (k : ℕ) (hk : k ∈ Finset.Icc 1 N) : 0 < |k * θ i₀ - round (k * θ i₀)| :=
    abs_pos.mpr <| sub_ne_zero.mpr <|
      (hi₀.natCast_mul (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hk).1)).ne_int _
  obtain ⟨Q, hQ, hQN⟩ := ((eventually_gt_atTop 1).and <| (eventually_all_finset _).mpr
    fun k hk ↦ tendsto_inv_atTop_zero.eventually (gt_mem_nhds (hpos k hk))).exists
  have hQ₀ : 0 < Q := zero_lt_one.trans hQ
  obtain ⟨p, q, hq, hqQ, hp⟩ := simultaneous_dirichlet θ hQ
  lift q to ℕ using hq.le
  simp only [Int.cast_natCast] at hqQ hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hpq (i : ι) : |(q : ℝ) * θ i - p i| ≤ Q⁻¹ := by
    rw [abs_sub_comm, mul_comm]
    exact hp i
  refine ⟨q, ⟨by exact_mod_cast hq, p, fun i ↦ (hpq i).trans ?_⟩, ?_⟩
  · -- `q ≤ Q ^ n` gives `Q⁻¹ ≤ q ^ (-1 / n)`.
    rw [Real.rpow_neg hq'.le]
    refine inv_anti₀ (by positivity) ?_
    calc (q : ℝ) ^ (Fintype.card ι : ℝ)⁻¹ ≤ (Q ^ Fintype.card ι) ^ (Fintype.card ι : ℝ)⁻¹ := by
          gcongr
      _ = Q := Real.pow_rpow_inv_natCast hQ₀.le hn
  · by_contra! hqN
    exact (hQN q (Finset.mem_Icc.mpr ⟨by exact_mod_cast hq, hqN⟩)).not_ge
      ((round_le _ (p i₀)).trans (hpq i₀))

/-- **Dirichlet's lower bound for the simultaneous exponent.** Every family of `n` real numbers
has simultaneous exponent at least `1 / n`. For the empty family both sides are `⊤`. -/
theorem inv_card_le_simultaneousExponent [Fintype ι] (θ : ι → ℝ) :
    (Fintype.card ι : ℝ≥0∞)⁻¹ ≤ simultaneousExponent θ := by
  cases isEmpty_or_nonempty ι
  · simp
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  simpa [ENNReal.ofReal_inv_of_pos hn] using le_simultaneousExponent_of_infinite
    (infinite_simultaneousApproximationDenominators_inv_card θ)

/-! ### One dimension -/

/-- For an irrational real number `ξ`, infinitely many one-dimensional simultaneous
approximations of exponent `w` give the `LiouvilleWith` condition of exponent `w + 1`. -/
theorem _root_.Irrational.liouvilleWith_add_one_of_simultaneous_infinite {w ξ : ℝ}
    (hξ : Irrational ξ)
    (h : (simultaneousApproximationDenominators ![ξ] w).Infinite) :
    LiouvilleWith (w + 1) ξ := by
  refine ⟨2, Nat.frequently_atTop_iff_infinite.2 <| h.mono ?_⟩
  rintro q ⟨hq, p, hp⟩
  refine ⟨p 0, hξ.ne_rational (p 0) q, ?_⟩
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have heq : |ξ - (p 0 : ℝ) / q| = |(q : ℝ) * ξ - p 0| / q := by
    have halg : ξ - (p 0 : ℝ) / q = ((q : ℝ) * ξ - p 0) / q := by
      field_simp
    rw [halg, abs_div, abs_of_pos hq']
  rw [heq]
  calc
    |(q : ℝ) * ξ - p 0| / q ≤ (q : ℝ) ^ (-w) / q := by gcongr; exact hp 0
    _ = (q : ℝ) ^ (-(w + 1)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hq']
      ring_nf
    _ < 2 / (q : ℝ) ^ (w + 1) := by
      rw [Real.rpow_neg hq'.le, div_eq_mul_inv]
      have hpos := inv_pos.mpr (Real.rpow_pos_of_pos hq' (w + 1))
      nlinarith

/-- A `LiouvilleWith` exponent strictly larger than `w + 1` supplies infinitely many
one-dimensional simultaneous approximations of exponent `w`. -/
theorem _root_.LiouvilleWith.simultaneous_infinite {p w ξ : ℝ} (h : LiouvilleWith p ξ)
    (hpw : w + 1 < p) : (simultaneousApproximationDenominators ![ξ] w).Infinite := by
  rw [← Nat.frequently_atTop_iff_infinite]
  refine ((eventually_gt_atTop 0).and_frequently
    (h.frequently_lt_rpow_neg hpw)).mono fun q hq ↦ ?_
  obtain ⟨hq0, m, hne, hm⟩ := hq
  have hq' : (0 : ℝ) < q := Nat.cast_pos.2 hq0
  refine ⟨hq0, ![m], fun i ↦ ?_⟩
  have heq : |(q : ℝ) * ξ - m| = q * |ξ - (m : ℝ) / q| := by
    have halg : (q : ℝ) * ξ - m = q * (ξ - (m : ℝ) / q) := by
      field_simp
    rw [halg, abs_mul, abs_of_pos hq']
  have hbound : |(q : ℝ) * ξ - m| ≤ (q : ℝ) ^ (-w) := calc
    |(q : ℝ) * ξ - m| = q * |ξ - (m : ℝ) / q| := heq
    _ ≤ q * (q : ℝ) ^ (-(w + 1)) := (mul_lt_mul_of_pos_left hm hq').le
    _ = (q : ℝ) ^ (-w) := by
      conv_lhs => lhs; rw [← Real.rpow_one (q : ℝ)]
      rw [← Real.rpow_add hq']
      ring_nf
  fin_cases i
  simpa using hbound

/-- For an irrational real number `ξ`, the one-dimensional simultaneous exponent, shifted by
one, is the irrationality exponent of `ξ`. -/
theorem _root_.Irrational.simultaneousExponent_add_one {ξ : ℝ} (hξ : Irrational ξ) :
    simultaneousExponent ![ξ] + 1 = irrationalityExponent ξ := by
  apply le_antisymm
  · have hex : ∃ w, (simultaneousApproximationDenominators ![ξ] w).Infinite :=
      ⟨0, hξ.liouvilleWith_two.simultaneous_infinite (by norm_num)⟩
    rw [simultaneousExponent, ENNReal.biSup_add' hex]
    refine iSup₂_le fun w hw ↦ ?_
    by_cases hw0 : 0 ≤ w
    · rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add hw0 zero_le_one]
      exact le_irrationalityExponent_of_liouvilleWith
        (hξ.liouvilleWith_add_one_of_simultaneous_infinite hw)
    · simp only [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hw0), zero_add]
      exact one_le_irrationalityExponent ξ
  · rw [irrationalityExponent_le_iff]
    intro p hp
    by_cases hp1 : p ≤ 1
    · exact (ENNReal.ofReal_le_ofReal hp1).trans (by simp)
    · have hp1' : 1 < p := lt_of_not_ge hp1
      rw [← sub_add_cancel p 1, ENNReal.ofReal_add (sub_nonneg.mpr hp1'.le) zero_le_one]
      refine add_le_add ?_ (by simp)
      refine le_of_forall_lt fun c hc ↦ ?_
      have hc_top : c ≠ ⊤ := ne_top_of_lt (hc.trans ENNReal.ofReal_lt_top)
      have hcw : c.toReal < p - 1 :=
        (ENNReal.lt_ofReal_iff_toReal_lt hc_top).mp hc
      obtain ⟨w, hcw', hwp⟩ := exists_between hcw
      rw [← ENNReal.ofReal_toReal hc_top]
      exact
        (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_nonneg.trans_lt hcw')).mpr hcw' |>.trans_le <|
        le_simultaneousExponent_of_infinite
          (hp.simultaneous_infinite (by linarith))

/-! ### Examples -/

example : simultaneousExponent ![(1 / 2 : ℝ), (1 / 3 : ℝ)] = ⊤ := by
  apply simultaneousExponent_eq_top_of_forall_rat
  intro i
  fin_cases i
  · exact ⟨1 / 2, by norm_num⟩
  · exact ⟨1 / 3, by norm_num⟩

end TauCeti
