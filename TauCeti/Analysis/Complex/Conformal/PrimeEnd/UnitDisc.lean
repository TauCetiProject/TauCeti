/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Basic
public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Crosscut.Chord
import Mathlib.Analysis.InnerProductSpace.Continuous
import TauCeti.Analysis.Complex.Inner
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.Normed.Group.Basic

/-!
# The prime ends of the unit disc are the points of the circle

Every point `ζ` of the unit circle determines a prime end of the unit disc. Cut the disc by the
chords perpendicular to `ζ` at the levels `t = 1 - 1 / (n + 2)`: the chord at level `t` is the
segment between the two points of the circle whose real inner product with `ζ` is `t`. These
chords form a null chain of the disc, whose domains are the caps `{z | t < ⟪ζ, z⟫_ℝ}` of the
disc beyond them. Caps at distinct points of the circle are eventually disjoint, so distinct
points give distinct prime ends: the circle embeds into the prime ends of the disc.

Conversely every null chain of the disc is equivalent to a radial chain, so every prime end of
the disc arises in this way: the prime ends of the disc are exactly the points of the circle.
This is the disc case of Carathéodory's prime-end theorem. The crosscuts of a null chain shrink
to points of the circle, and so do the domains they cut off: the part of the disc away from a
short crosscut is convex, misses it, and contains points of the first crosscut, so it does not
lie in the domain. The closures of the domains then have a common point `ζ` on the circle, and
the chain is equivalent to the radial chain at `ζ`. The argument needs neither the Jordan curve
theorem nor the fact that a crosscut cuts the disc into exactly two pieces.

## Main declarations

* `TauCeti.isNullChain_unitDiscRadialChain` -- the chords at levels `1 - 1 / (n + 2)` form a
  null chain.
* `TauCeti.nullChainDomain_unitDiscRadialChain` -- its domains are the caps beyond its chords.
* `TauCeti.unitDiscPrimeEnd_injective` -- distinct points of the circle give distinct prime ends.
* `TauCeti.IsNullChain.exists_nullChainEquivalent_unitDiscRadialChain` -- every null chain of the
  disc is equivalent to a radial chain.
* `TauCeti.unitDiscPrimeEnd_surjective`, `TauCeti.unitDiscPrimeEnd_bijective` -- every prime end
  of the disc is the prime end at a point of the circle.

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

/-! ### Every prime end of the disc is radial -/

section Surjective

variable {C : ℕ → Set ℂ} {k : ℕ}

/-- The crosscuts of a null chain of the disc eventually have small Euclidean diameter: on the
closed disc the chordal distance is at least half the Euclidean one. -/
private lemma IsNullChain.eventually_norm_sub_lt (hC : IsNullChain (ball 0 1) C) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ n in atTop, ∀ z ∈ C n, ∀ w ∈ C n, ‖z - w‖ < ε := by
  filter_upwards [hC.eventually_chordal_lt (ε / 2) (by positivity)] with n hn z hz w hw
  have hsub : C n ⊆ closedBall 0 1 := by
    obtain ⟨x, y, γ, hγ, hrange⟩ := hC.exists_isCrosscut n
    rw [← hrange, ← closure_ball (0 : ℂ) one_ne_zero]
    exact hγ.range_subset_closure
  have hz1 : ‖z‖ ≤ 1 := by simpa using hsub hz
  have hw1 : ‖w‖ ≤ 1 := by simpa using hsub hw
  have hpos : 0 < √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) := Real.sqrt_pos.mpr (by positivity)
  have hle : √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) ≤ 2 := by
    rw [Real.sqrt_le_left zero_le_two]
    have hz2 : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg z) hz1
    have hw2 : ‖w‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg w) hw1
    nlinarith [sq_nonneg ‖z‖, sq_nonneg ‖w‖]
  have h := (div_lt_iff₀ hpos).mp (hn z hz w hw)
  nlinarith

/-- **The domains of a null chain of the disc shrink to the circle.** Eventually the domain cut
off by the `n`-th crosscut lies within `√(2δ)` of an endpoint `x` of that crosscut. -/
private lemma IsNullChain.eventually_exists_norm_sub_sq_le (hC : IsNullChain (ball 0 1) C)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∃ x ∈ C n, ‖x‖ = 1 ∧
      ∀ z ∈ nullChainDomain (ball 0 1) C n, ‖z - x‖ ^ 2 ≤ 2 * δ := by
  obtain ⟨p, hpC, hpU⟩ := (hC.isConnected_inter 0).nonempty
  have hp : ‖p‖ < 1 := mem_ball_zero_iff.mp hpU
  set δ' := min δ ((1 - ‖p‖) / 2)
  have hδ' : 0 < δ' := lt_min hδ (by linarith)
  have hδ'p : ‖p‖ < 1 - δ' := by linarith [min_le_right δ ((1 - ‖p‖) / 2)]
  filter_upwards [hC.eventually_norm_sub_lt hδ'] with n hn
  obtain ⟨x, y, γ, hγ, hrange⟩ := hC.exists_isCrosscut n
  have hxC : x ∈ C n := hrange ▸ ⟨0, γ.source⟩
  have hx : ‖x‖ = 1 := by
    simpa [frontier_ball (0 : ℂ) one_ne_zero] using hγ.source_mem_frontier
  refine ⟨x, hxC, hx, fun z hz => ?_⟩
  have hzU : z ∈ ball (0 : ℂ) 1 := (nullChainDomain_subset hz).1
  -- the crosscut stays within `δ'` of `x`, and the domain lies at level at least `1 - δ'`
  have hlevel : 1 - δ' ≤ inner ℝ x z := by
    by_contra! hlt
    -- the part of the disc below level `1 - δ'` misses the crosscut, so it lies in the domain
    have hA : ball 0 1 ∩ {w | inner ℝ x w < 1 - δ'} ⊆ nullChainDomain (ball 0 1) C n :=
      ((convex_ball 0 1).inter
          (convex_halfSpace_lt (innerₗ ℂ x).isLinear _)).isPreconnected.subset_nullChainDomain
        (fun w hw => ⟨hw.1, fun hwC => by
          have hw2 : inner ℝ x w < 1 - δ' := hw.2
          linarith [one_sub_norm_sub_le_inner hx w, hn w hwC x hxC]⟩)
        ⟨z, ⟨hzU, hlt⟩, hz⟩
    -- but it contains the point `p` of the first crosscut, which no domain contains
    have hpA : p ∈ ball 0 1 ∩ {w | inner ℝ x w < 1 - δ'} := by
      refine ⟨hpU, lt_of_le_of_lt ?_ hδ'p⟩
      simpa [hx] using real_inner_le_norm x p
    exact (nullChainDomain_subset
      (hC.antitone_nullChainDomain (Nat.zero_le n) (hA hpA))).2 hpC
  calc ‖z - x‖ ^ 2 ≤ 2 * (1 - (1 - δ')) :=
        norm_sub_sq_le hx (mem_ball_zero_iff.mp hzU).le hlevel
    _ ≤ 2 * δ := by linarith [min_le_left δ ((1 - ‖p‖) / 2)]

/-- If a point `ζ` of the circle adheres to the domain cut off by a crosscut of a null chain of
the disc but does not lie on the crosscut, that domain contains a cap of the radial chain at
`ζ`. -/
private lemma IsNullChain.exists_cap_subset_nullChainDomain (hC : IsNullChain (ball 0 1) C)
    (hζ : ‖ζ‖ = 1) (hζD : ζ ∈ closure (nullChainDomain (ball 0 1) C k)) (hζC : ζ ∉ C k) :
    ∃ n, nullChainDomain (ball 0 1) (unitDiscRadialChain ζ) n ⊆
      nullChainDomain (ball 0 1) C k := by
  obtain ⟨x, y, γ, -, hrange⟩ := hC.exists_isCrosscut k
  have hCk : IsClosed (C k) := hrange ▸ (isCompact_range γ.continuous).isClosed
  obtain ⟨r, hr, hrC⟩ := Metric.isOpen_iff.mp hCk.isOpen_compl ζ hζC
  obtain ⟨n, hn⟩ := (eventually_eight_mul_lt hr).exists
  refine ⟨n, ?_⟩
  rw [nullChainDomain_unitDiscRadialChain hζ]
  set t := 1 - 1 / ((n : ℝ) + 2)
  -- the cap is a convex set off the crosscut
  refine ((convex_ball 0 1).inter
      (convex_halfSpace_gt (innerₗ ℂ ζ).isLinear t)).isPreconnected.subset_nullChainDomain
    (fun z hz => ⟨hz.1, hrC ?_⟩) ?_
  · have h := norm_sub_sq_le hζ (mem_ball_zero_iff.mp hz.1).le hz.2.le
    have h' : 1 - t = 1 / ((n : ℝ) + 2) := by ring
    have hpos : 0 < 1 / ((n : ℝ) + 2) := by positivity
    rw [mem_ball, dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hr.le (by rw [h'] at h; linarith)
  -- and it meets the domain, since `ζ` adheres to the domain
  · have hopen : IsOpen {z : ℂ | t < inner ℝ ζ z} :=
      isOpen_lt continuous_const (continuous_const.inner continuous_id)
    have hζt : ζ ∈ {z : ℂ | t < inner ℝ ζ z} := by
      rw [mem_ofPred_eq, real_inner_self_eq_norm_sq, hζ, one_pow]
      exact level_lt_one n
    obtain ⟨q, hqt, hqD⟩ := _root_.mem_closure_iff.mp hζD _ hopen hζt
    exact ⟨q, ⟨(nullChainDomain_subset hqD).1, hqt⟩, hqD⟩

/-- **Every null chain of the disc is equivalent to a radial chain.** For a null chain `C` of the
unit disc there is a point `ζ` of the unit circle such that `C` is equivalent to the chain of
chords perpendicular to `ζ`. -/
theorem IsNullChain.exists_nullChainEquivalent_unitDiscRadialChain
    (hC : IsNullChain (ball 0 1) C) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ NullChainEquivalent (ball 0 1) C (unitDiscRadialChain ζ) := by
  set D := nullChainDomain (ball (0 : ℂ) 1) C
  have hDb : ∀ n, closure (D n) ⊆ closedBall 0 1 := fun n =>
    closure_minimal (nullChainDomain_subset.trans (sdiff_subset.trans ball_subset_closedBall))
      isClosed_closedBall
  -- the closures of the domains have a common point `ζ`
  obtain ⟨ζ, hζD⟩ : (⋂ n, closure (D n)).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
      (fun n => closure_mono (hC.nullChainDomain_succ_subset n))
      (fun n => (hC.nonempty_nullChainDomain n).closure)
      ((isCompact_closedBall 0 1).of_isClosed_subset isClosed_closure (hDb 0))
      fun _ => isClosed_closure
  rw [mem_iInter] at hζD
  -- eventually `ζ` and the whole domain lie close to an endpoint of the crosscut
  have hnear : ∀ δ > 0, ∀ᶠ n in atTop, ∃ x : ℂ, ‖x‖ = 1 ∧ ‖ζ - x‖ ^ 2 ≤ 2 * δ ∧
      ∀ z ∈ D n, ‖z - x‖ ^ 2 ≤ 2 * δ := fun δ hδ =>
    (hC.eventually_exists_norm_sub_sq_le hδ).mono fun n ⟨x, _, hx, hD⟩ =>
      ⟨x, hx, closure_minimal (t := {z | ‖z - x‖ ^ 2 ≤ 2 * δ}) hD
        (isClosed_le (by fun_prop) continuous_const) (hζD n), hD⟩
  -- so `ζ` lies on the circle
  have hζ : ‖ζ‖ = 1 := by
    refine le_antisymm (by simpa using hDb 0 (hζD 0)) (not_lt.mp fun hlt => ?_)
    have hpos : 0 < (1 - ‖ζ‖) ^ 2 / 4 := by nlinarith
    obtain ⟨n, x, hx, hζx, -⟩ := (hnear _ hpos).exists
    have hlt' : ‖ζ - x‖ < 1 - ‖ζ‖ := lt_of_pow_lt_pow_left₀ 2 (by linarith) (by nlinarith)
    have := norm_sub_norm_le x ζ
    rw [norm_sub_rev] at this
    linarith
  refine ⟨ζ, hζ, nullChainEquivalent_def.mpr ⟨fun m => ?_, fun m => ?_⟩⟩
  -- a cap of the radial chain lies in each domain, avoiding whichever of two consecutive
  -- crosscuts misses `ζ`
  · by_cases hζC : ζ ∈ C m
    · have hζC' : ζ ∉ C (m + 1) := disjoint_left.mp (hC.disjoint_succ m) hζC
      obtain ⟨n, hn⟩ := hC.exists_cap_subset_nullChainDomain hζ (hζD (m + 1)) hζC'
      exact ⟨n, hn.trans (hC.nullChainDomain_succ_subset m)⟩
    · exact hC.exists_cap_subset_nullChainDomain hζ (hζD m) hζC
  -- each cap of the radial chain contains a domain, which lies close to `ζ`
  · set ε := 1 / ((m : ℝ) + 2)
    have hε : 0 < ε := by positivity
    obtain ⟨n, x, -, hζx, hD⟩ := (hnear (ε ^ 2 / 16) (by positivity)).exists
    refine ⟨n, fun z hz => ?_⟩
    rw [nullChainDomain_unitDiscRadialChain hζ]
    refine ⟨(nullChainDomain_subset hz).1, ?_⟩
    have h := norm_sub_sq_le_two_mul z ζ x
    have hzζ : ‖z - ζ‖ < ε :=
      lt_of_pow_lt_pow_left₀ 2 hε.le (by nlinarith [hD z hz])
    have := one_sub_norm_sub_le_inner hζ z
    simp only [mem_ofPred_eq]
    linarith

/-- **Every prime end of the disc is radial.** Every prime end of the unit disc is the prime end
at some point of the unit circle. -/
theorem unitDiscPrimeEnd_surjective : Function.Surjective unitDiscPrimeEnd := by
  intro p
  induction p using PrimeEnd.ind with
  | h C hC =>
    obtain ⟨ζ, hζ, hequiv⟩ := hC.exists_nullChainEquivalent_unitDiscRadialChain
    exact ⟨⟨ζ, mem_sphere_zero_iff_norm.mpr hζ⟩, PrimeEnd.mk_eq_mk_iff.mpr hequiv.symm⟩

/-- **The prime ends of the disc are the points of the circle.** The map sending a point of the
unit circle to its radial prime end is a bijection onto the prime ends of the unit disc. -/
theorem unitDiscPrimeEnd_bijective : Function.Bijective unitDiscPrimeEnd :=
  ⟨unitDiscPrimeEnd_injective, unitDiscPrimeEnd_surjective⟩

end Surjective

end TauCeti

end
