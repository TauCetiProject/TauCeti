/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Basic
public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Crosscut.Chord
import TauCeti.Analysis.Complex.Inner
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Prime ends of the unit disc at points of the circle

Every point `ζ` of the unit circle determines a prime end of the unit disc. Cut the disc by the
chords perpendicular to `ζ` at the levels `t = 1 - 1 / (n + 2)`: the chord at level `t` is the
segment between the two points of the circle whose real inner product with `ζ` is `t`. These
chords form a null chain of the disc, whose domains are the caps `{z | t < ⟪ζ, z⟫_ℝ}` of the
disc beyond them. Caps at distinct points of the circle are eventually disjoint, so distinct
points give distinct prime ends: the circle embeds into the prime ends of the disc.

That every prime end of the disc arises in this way is the disc case of Carathéodory's prime-end
theorem, and is not proved here.

## Main declarations

* `TauCeti.isNullChain_unitDiscRadialChain` -- the chords at levels `1 - 1 / (n + 2)` form a
  null chain.
* `TauCeti.nullChainDomain_unitDiscRadialChain` -- its domains are the caps beyond its chords.
* `TauCeti.unitDiscPrimeEnd_injective` -- distinct points of the circle give distinct prime ends.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Section 2.4.
-/

public section

noncomputable section

open Complex Filter Metric Set Topology

namespace TauCeti

variable {ζ : ℂ} {t : ℝ}

/-- A point of the closed unit disc at level at least `t` is within `√(2 (1 - t))` of `ζ`. -/
private lemma norm_sub_sq_le (hζ : ‖ζ‖ = 1) {z : ℂ} (hz : ‖z‖ ≤ 1) (hzt : t ≤ inner ℝ ζ z) :
    ‖z - ζ‖ ^ 2 ≤ 2 * (1 - t) := by
  rw [norm_sub_sq_real, hζ, real_inner_comm]
  nlinarith [norm_nonneg z]

/-- The chords of the unit disc perpendicular to `ζ` at the levels `1 - 1 / (n + 2)`. -/
def unitDiscRadialChain (ζ : ℂ) (n : ℕ) : Set ℂ :=
  unitDiscChord ζ (1 - 1 / ((n : ℝ) + 2))

theorem unitDiscRadialChain_apply (ζ : ℂ) (n : ℕ) :
    unitDiscRadialChain ζ n = unitDiscChord ζ (1 - 1 / ((n : ℝ) + 2)) :=
  (rfl)

private lemma level_pos (n : ℕ) : 0 < 1 - 1 / ((n : ℝ) + 2) := by
  have : 1 / ((n : ℝ) + 2) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith [n.cast_nonneg (α := ℝ)]
  linarith

private lemma level_lt_one (n : ℕ) : 1 - 1 / ((n : ℝ) + 2) < 1 := by
  have : 0 < 1 / ((n : ℝ) + 2) := by positivity
  linarith

private lemma abs_level_lt_one (n : ℕ) : |1 - 1 / ((n : ℝ) + 2)| < 1 := by
  rw [abs_of_pos (level_pos n)]
  exact level_lt_one n

/-- Eventually the level `1 - 1 / (n + 2)` is close enough to `1` that `8 (1 - t) < ε ^ 2`. -/
private lemma eventually_eight_mul_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 8 * (1 / ((n : ℝ) + 2)) < ε ^ 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (8 / ε ^ 2)
  refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h8 : 8 / ε ^ 2 < (n : ℝ) + 2 := by linarith
  rw [div_lt_iff₀ (by positivity)] at h8
  rw [mul_one_div, div_lt_iff₀ (by positivity)]
  linarith

private lemma level_strictMono : StrictMono fun n : ℕ => 1 - 1 / ((n : ℝ) + 2) := by
  intro m n hmn
  have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
  have : 1 / ((n : ℝ) + 2) < 1 / ((m : ℝ) + 2) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  simp only
  linarith

/-- The domains cut off by the radial chain at `ζ` are the caps beyond its chords. -/
theorem nullChainDomain_unitDiscRadialChain (hζ : ‖ζ‖ = 1) (n : ℕ) :
    nullChainDomain (ball 0 1) (unitDiscRadialChain ζ) n =
      ball (0 : ℂ) 1 ∩ {z | 1 - 1 / ((n : ℝ) + 2) < inner ℝ ζ z} := by
  set t := 1 - 1 / ((n : ℝ) + 2)
  set t' := 1 - 1 / (((n + 1 : ℕ) : ℝ) + 2)
  have htt' : t < t' := level_strictMono n.lt_succ_self
  ext q
  rw [mem_nullChainDomain_iff, unitDiscRadialChain_apply, unitDiscRadialChain_apply]
  constructor
  · rintro ⟨w, hw, hqw⟩
    have hwD : w ∈ ball 0 1 \ unitDiscChord ζ t := connectedComponentIn_nonempty_iff.mp ⟨q, hqw⟩
    have hwt' : inner ℝ ζ w = t' := inner_eq_of_mem_unitDiscChord hζ hw
    rwa [connectedComponentIn_ball_sdiff_unitDiscChord hζ
      ⟨hwD.1, lt_of_lt_of_eq htt' hwt'.symm⟩] at hqw
  · intro hq
    have hmid : ζ * t' ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_mul, hζ, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact abs_level_lt_one (n + 1)
    have hmidt : inner ℝ ζ (ζ * t') = t' := by simp [inner_mul_left_of_norm_eq_one hζ]
    refine ⟨ζ * t', mem_unitDiscChord_of_mem_ball hζ hmid hmidt, ?_⟩
    rwa [connectedComponentIn_ball_sdiff_unitDiscChord hζ ⟨hmid, lt_of_lt_of_eq htt' hmidt.symm⟩]

/-- **The radial chain is a null chain.** For a point `ζ` of the unit circle, the chords of the
unit disc perpendicular to `ζ` at the levels `1 - 1 / (n + 2)` form a null chain of the disc. -/
theorem isNullChain_unitDiscRadialChain (hζ : ‖ζ‖ = 1) :
    IsNullChain (ball 0 1) (unitDiscRadialChain ζ) where
  exists_isCrosscut n := exists_isCrosscut_unitDiscChord hζ (abs_level_lt_one n)
  disjoint_succ n := by
    refine disjoint_left.mpr fun z hz hz' => ?_
    have h := (inner_eq_of_mem_unitDiscChord hζ hz).symm.trans
      (inner_eq_of_mem_unitDiscChord hζ hz')
    exact (level_strictMono n.lt_succ_self).ne h
  nullChainDomain_succ_subset n := by
    rw [nullChainDomain_unitDiscRadialChain hζ, nullChainDomain_unitDiscRadialChain hζ]
    exact inter_subset_inter_right _ fun z hz => (level_strictMono n.lt_succ_self).trans hz
  eventually_chordal_lt ε hε := by
    refine (eventually_eight_mul_lt hε).mono fun n hsmall z hz w hw => ?_
    have ht := abs_level_lt_one n
    have hzb : ‖z‖ ≤ 1 := by
      simpa using unitDiscChord_subset_closedBall hζ ht.le hz
    have hwb : ‖w‖ ≤ 1 := by
      simpa using unitDiscChord_subset_closedBall hζ ht.le hw
    have hz' := norm_sub_sq_le hζ hzb (inner_eq_of_mem_unitDiscChord hζ hz).ge
    have hw' := norm_sub_sq_le hζ hwb (inner_eq_of_mem_unitDiscChord hζ hw).ge
    have hzw : ‖z - w‖ < ε :=
      lt_of_pow_lt_pow_left₀ 2 hε.le (by linarith [norm_sub_sq_le_two_mul z w ζ])
    refine lt_of_le_of_lt (div_le_self (norm_nonneg _) ?_) hzw
    rw [Real.one_le_sqrt]
    nlinarith [sq_nonneg ‖z‖, sq_nonneg ‖w‖]

/-- The prime end of the unit disc at a point `ζ` of the unit circle, represented by the radial
chain of chords perpendicular to `ζ`. -/
def unitDiscPrimeEnd (ζ : sphere (0 : ℂ) 1) : PrimeEnd (ball 0 1) :=
  PrimeEnd.mk (unitDiscRadialChain ζ)
    (isNullChain_unitDiscRadialChain (mem_sphere_zero_iff_norm.mp ζ.2))

/-- The prime end of the unit disc at `ζ` is the class of the radial chain at `ζ`. -/
theorem unitDiscPrimeEnd_def (ζ : sphere (0 : ℂ) 1) :
    unitDiscPrimeEnd ζ = PrimeEnd.mk (unitDiscRadialChain ζ)
      (isNullChain_unitDiscRadialChain (mem_sphere_zero_iff_norm.mp ζ.2)) :=
  (rfl)

/-- **Distinct points of the circle give distinct prime ends of the disc.** -/
theorem unitDiscPrimeEnd_injective : Function.Injective unitDiscPrimeEnd := by
  rintro ⟨ζ, hζ⟩ ⟨ζ', hζ'⟩ h
  rw [unitDiscPrimeEnd_def, unitDiscPrimeEnd_def] at h
  rw [mem_sphere_zero_iff_norm] at hζ hζ'
  by_contra hne
  have hd : 0 < ‖ζ - ζ'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h' => hne (by simp [h']))
  obtain ⟨m, hm⟩ := (eventually_eight_mul_lt hd).exists
  have hequiv : NullChainEquivalent (ball 0 1) (unitDiscRadialChain ζ) (unitDiscRadialChain ζ') :=
    PrimeEnd.mk_eq_mk_iff.mp h
  obtain ⟨hequiv, -⟩ := nullChainEquivalent_def.mp hequiv
  obtain ⟨n, hn⟩ := hequiv m
  rw [nullChainDomain_unitDiscRadialChain hζ', nullChainDomain_unitDiscRadialChain hζ] at hn
  set k := max n m
  set t := 1 - 1 / ((k : ℝ) + 2)
  set u := 1 - 1 / ((m : ℝ) + 2)
  have hut : u ≤ t := level_strictMono.monotone (le_max_right n m)
  have hnt : 1 - 1 / ((n : ℝ) + 2) ≤ t := level_strictMono.monotone (le_max_left n m)
  -- a point of the cap of `ζ'` at level `t`, which then lies in the cap of `ζ` at level `u`
  set q := ζ' * (((1 + t) / 2 : ℝ) : ℂ)
  have ht1 : t < 1 := level_lt_one k
  have ht0 : 0 < t := level_pos k
  have hqn : ‖q‖ < 1 := by
    rw [norm_mul, hζ', one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hqt : t < inner ℝ ζ' q := by
    rw [inner_mul_left_of_norm_eq_one hζ', Complex.ofReal_re]
    linarith
  have hqζ : q ∈ ball (0 : ℂ) 1 ∩ {z | u < inner ℝ ζ z} :=
    hn ⟨mem_ball_zero_iff.mpr hqn, lt_of_le_of_lt hnt hqt⟩
  have h₁ := norm_sub_sq_le hζ hqn.le hqζ.2.le
  have h₂ := norm_sub_sq_le hζ' hqn.le (hut.trans hqt.le)
  have h₃ := norm_sub_sq_le_two_mul ζ ζ' q
  rw [norm_sub_rev ζ q, norm_sub_rev ζ' q] at h₃
  have hu : 1 - u = 1 / ((m : ℝ) + 2) := by ring
  linarith

end TauCeti

end
