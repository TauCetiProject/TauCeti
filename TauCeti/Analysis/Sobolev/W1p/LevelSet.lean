/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.ChainRule

import Mathlib.Algebra.Order.Group.PosPart

/-!
# Weak gradients on level sets

For `1 ≤ p < ∞`, the weak gradient of a Sobolev function vanishes almost everywhere on
each of its level sets. Consequently, the weak gradients of two Sobolev functions agree
almost everywhere on the set where their values agree.

The level may be any real number, including on domains of infinite measure. These locality
statements apply to measurable level sets, which need not contain any open set. They remove
the ambiguity of truncation gradients at a threshold and support continuity of positive
truncation in the Sobolev norm.

If the superlevel sets `{u > l}`, `l > k`, have finite measure and `u > k` on a set of positive
measure, then there are levels
`lⱼ ≥ k`, each exceeded by `u` on a set of positive measure, along which the measure of
`{u > lⱼ, ∇u ≠ 0}` tends to zero. This is the measure-theoretic input of the weak maximum
principle with bounded drift.

The same holds for the classical gradient of a `C¹` function, which is read off from the weak
statement on small balls.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Gradient Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- The weak gradient vanishes almost everywhere on every level set, for `1 ≤ p < ∞`.
The level may be any real number, even when `Ω` has infinite measure. -/
theorem W1p.gradient_ae_eq_zero_on_level_set (hp : p ≠ ∞) (u : W1p mu Omega p) (k : ℝ) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = k → W1p.gradient u x = 0 := by
  classical
  have hneg := W1p.value_neg_ae u
  have hconst : HasWeakFDerivOn mu Omega (fun _ : E => k) 0 :=
    hasWeakFDerivOn_iff.2 fun _ => hasWeakLineDerivOn_const k
  have hsplit := (W1p.hasWeakFDerivOn_posPartAbove hp k u).sub
    (W1p.hasWeakFDerivOn_posPartAbove hp (-k) (-u))
  have hvalue :
      (fun x => max (W1p.value u x - k) 0) -
          (fun x => max (W1p.value (-u) x - -k) 0) =ᵐ[mu.restrict Omega]
        (fun x => W1p.value u x - k) := by
    filter_upwards [hneg] with x hx
    simpa only [Pi.sub_apply, hx, Pi.neg_apply, neg_sub_neg, posPart_def, negPart_def,
      neg_sub] using posPart_sub_negPart (W1p.value u x - k)
  have hderiv := ((W1p.hasWeakFDerivOn u).sub hconst).ae_eq (hsplit.congr_ae hvalue)
  filter_upwards [hneg, hderiv] with x hnegx hx
  intro hlevel
  have hpos : {y | k < W1p.value u y}.indicator (⇑(W1p.gradient u)) x = 0 :=
    indicator_of_notMem (by simpa only [mem_ofPred_eq, hlevel] using lt_irrefl k) _
  have hneg : {y | -k < W1p.value (-u) y}.indicator (⇑(W1p.gradient (-u))) x = 0 :=
    indicator_of_notMem
      (by simpa only [mem_ofPred_eq, hnegx, Pi.neg_apply, hlevel] using lt_irrefl (-k)) _
  have hz : innerSL ℝ (W1p.gradient u x) = 0 := by
    simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero, hpos, hneg, map_zero] using hx
  exact innerSL_inj.mp (hz.trans (map_zero _).symm)

/-- Weak gradients agree almost everywhere wherever the values agree, even if their
coincidence set has empty interior. -/
theorem W1p.gradient_ae_eq_on_eq (hp : p ≠ ∞) (u v : W1p mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      W1p.value u x = W1p.value v x → W1p.gradient u x = W1p.gradient v x := by
  have hvalue : ⇑(W1p.value (u - v)) =ᵐ[mu.restrict Omega]
      W1p.value u - W1p.value v := by
    simpa only [← W1p.valueL_apply, map_sub] using Lp.coeFn_sub (W1p.value u) (W1p.value v)
  have hgradient : ⇑(W1p.gradient (u - v)) =ᵐ[mu.restrict Omega]
      W1p.gradient u - W1p.gradient v := by
    simpa only [← W1p.gradientL_apply, map_sub] using Lp.coeFn_sub (W1p.gradient u) (W1p.gradient v)
  filter_upwards [W1p.gradient_ae_eq_zero_on_level_set hp (u - v) 0, hvalue, hgradient]
    with x hx hux hgx
  intro h
  apply sub_eq_zero.mp
  simpa only [hgx, Pi.sub_apply] using hx (by simp [hux, h])

/-- Let `u ∈ W^{1,p}(Ω)`, `1 ≤ p < ∞`, have superlevel sets `{u > l}` of finite measure for every
`l > k` (for instance because `Ω` has finite measure, or because `k ≥ 0`), and suppose `u > k` on
a set of positive measure. Then there are levels `lⱼ ≥ k`, each exceeded by `u` on a set of positive
measure, along which the measure of `{u > lⱼ, ∇u ≠ 0}` tends to zero. The proof compares the
levels with an increasing sequence approaching the essential supremum `M` of `u`; along it the
sets shrink to `{u = M, ∇u ≠ 0}`, which is null because the weak gradient vanishes almost
everywhere on level sets, or to the empty set if `u` is essentially unbounded above. The
statement asserts neither monotonicity nor convergence of the levels. -/
theorem W1p.exists_tendsto_measure_lt_value_and_gradient_ne_zero (hp : p ≠ ∞)
    (u : W1p mu Omega p) {k : ℝ}
    (hfin : ∀ l, k < l → mu.restrict Omega {x | l < W1p.value u x} ≠ ∞)
    (hk : ¬ ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ k) :
    ∃ l : ℕ → ℝ, (∀ j, k ≤ l j ∧ ¬ ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ l j) ∧
      Tendsto (fun j ↦ mu.restrict Omega {x | l j < W1p.value u x ∧ W1p.gradient u x ≠ 0})
        atTop (𝓝 0) := by
  set μ := mu.restrict Omega
  set T : ℝ → Set E :=
    fun l ↦ {x | l < W1p.value u x ∧ W1p.gradient u x ≠ 0}
  have hT : ∀ l, MeasurableSet (T l) := fun l ↦
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable (W1p.value u)).measurable).inter
      ((Lp.stronglyMeasurable (W1p.gradient u)).measurable (measurableSet_singleton 0).compl)
  have hTanti : Antitone T := fun l l' hll' x hx ↦ ⟨hll'.trans_lt hx.1, hx.2⟩
  -- It suffices to find increasing levels `mⱼ`, eventually above `k`, with `⋂ⱼ T mⱼ` null, each
  -- below an admissible level.
  have key : ∀ m : ℕ → ℝ, Monotone m → (∃ i, k < m i) → μ (⋂ j, T (m j)) = 0 →
      (∀ j, ∃ l, k ≤ l ∧ m j ≤ l ∧ ¬ ∀ᵐ x ∂μ, W1p.value u x ≤ l) →
      ∃ l : ℕ → ℝ, (∀ j, k ≤ l j ∧ ¬ ∀ᵐ x ∂μ, W1p.value u x ≤ l j) ∧
        Tendsto (fun j ↦ μ (T (l j))) atTop (𝓝 0) := by
    intro m hm ⟨i, hi⟩ hnull hL
    choose l hkl hml hnot using hL
    refine ⟨l, fun j ↦ ⟨hkl j, hnot j⟩, tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ?_ (fun _ ↦ zero_le) fun j ↦ measure_mono (hTanti (hml j))⟩
    have := tendsto_measure_iInter_atTop (μ := μ) (s := fun j ↦ T (m j))
      (fun j ↦ (hT _).nullMeasurableSet) (fun i j hij ↦ hTanti (hm hij))
      ⟨i, ne_top_of_le_ne_top (hfin _ hi) (measure_mono fun _ hx ↦ hx.1)⟩
    rwa [hnull] at this
  set L : Set ℝ := {l | k ≤ l ∧ ¬ ∀ᵐ x ∂μ, W1p.value u x ≤ l}
  have hkL : k ∈ L := ⟨le_rfl, hk⟩
  by_cases hbdd : BddAbove L
  · -- `u` is essentially bounded above by `M = sup L > k`; approach `M` from below.
    set M := sSup L
    have hle : ∀ᵐ x ∂μ, W1p.value u x ≤ M := by
      have hj : ∀ j : ℕ, ∀ᵐ x ∂μ, W1p.value u x ≤ M + 1 / ((j : ℝ) + 1) := by
        intro j
        by_contra hj
        have hmemL : M + 1 / ((j : ℝ) + 1) ∈ L :=
          ⟨(le_csSup hbdd hkL).trans (le_add_of_nonneg_right (by positivity)), hj⟩
        linarith [le_csSup hbdd hmemL, (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1))]
      filter_upwards [ae_all_iff.2 hj] with x hx
      refine le_of_forall_pos_le_add fun ε hε ↦ ?_
      obtain ⟨j, hjε⟩ := exists_nat_one_div_lt hε
      linarith [hx j]
    have hkM : k < M := lt_of_not_ge fun hMk ↦ hk (hle.mono fun x hx ↦ hx.trans hMk)
    refine key (fun j ↦ M - 1 / ((j : ℝ) + 1)) (fun i j hij ↦ ?_) ?_ ?_ fun j ↦ ?_
    · dsimp only
      gcongr
    · obtain ⟨i, hi⟩ := exists_nat_one_div_lt (sub_pos.2 hkM)
      exact ⟨i, by linarith⟩
    · rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hle, W1p.gradient_ae_eq_zero_on_level_set hp u M] with x hxM hlev hx
      rw [mem_iInter] at hx
      have hMx : M ≤ W1p.value u x := le_of_forall_pos_le_add fun ε hε ↦ by
        obtain ⟨j, hjε⟩ := exists_nat_one_div_lt hε
        linarith [(hx j).1]
      exact (hx 0).2 (hlev (le_antisymm hxM hMx))
    · have hlt : max k (M - 1 / ((j : ℝ) + 1)) < M :=
        max_lt hkM (sub_lt_self _ (by positivity))
      obtain ⟨l', hl'L, hl'⟩ := exists_lt_of_lt_csSup ⟨k, hkL⟩ hlt
      exact ⟨max k (M - 1 / ((j : ℝ) + 1)), le_max_left _ _, le_max_right _ _,
        fun hae ↦ hl'L.2 (hae.mono fun x hx ↦ hx.trans hl'.le)⟩
  · -- `u` is essentially unbounded above; take the levels `j`.
    refine key (fun j ↦ (j : ℝ)) Nat.mono_cast (exists_nat_gt k) ?_ fun j ↦ ?_
    · rw [measure_eq_zero_iff_ae_notMem]
      refine Eventually.of_forall fun x hx ↦ ?_
      obtain ⟨j, hj⟩ := exists_nat_gt (W1p.value u x)
      exact lt_asymm hj (mem_iInter.1 hx j).1
    · obtain ⟨l, hlL, hjl⟩ := not_bddAbove_iff.1 hbdd j
      exact ⟨l, hlL.1, hjl.le, hlL.2⟩

/-- The classical gradient of a function of class `C¹` on `Ω` vanishes almost everywhere on each
of its level sets in `Ω`. This is read off from
`TauCeti.W1p.gradient_ae_eq_zero_on_level_set` on small balls. -/
theorem gradient_ae_eq_zero_on_level_set_of_contDiffOn {w : E → ℝ}
    (hw : ContDiffOn ℝ 1 w Omega) (k : ℝ) :
    ∀ᵐ x ∂mu.restrict Omega, w x = k → ∇ w x = 0 := by
  have hO := Omega.isOpen
  set N := {x | x ∈ (Omega : Set E) ∧ w x = k ∧ ∇ w x ≠ 0}
  have hN : mu N = 0 := by
    refine measure_null_of_locally_null N fun x hx => ?_
    obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hO x hx.1
    set V : Opens E := ⟨Metric.ball x (r / 2), Metric.isOpen_ball⟩
    obtain ⟨U, hUv, hUg⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact
      (mu := mu) (Omega := V) (p := 2) hO hw (isCompact_closedBall x (r / 2))
      Metric.ball_subset_closedBall ((Metric.closedBall_subset_ball (by linarith)).trans hrO)
    refine ⟨N ∩ V, inter_mem_nhdsWithin N
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith))), ?_⟩
    have hae : ∀ᵐ y ∂mu.restrict V, w y = k → ∇ w y = 0 := by
      filter_upwards [W1p.gradient_ae_eq_zero_on_level_set ENNReal.ofNat_ne_top U k, hUv, hUg]
        with y hy hv hg hyk
      rw [← hg]
      exact hy (hv.trans hyk)
    rw [ae_restrict_iff' V.isOpen.measurableSet, ae_iff] at hae
    refine measure_mono_null (fun y hy => ?_) hae
    obtain ⟨⟨-, hyk, hyg⟩, hyV⟩ := hy
    exact fun h => hyg (h hyV hyk)
  filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN),
    ae_restrict_mem hO.measurableSet] with x hx hxO hxk
  by_contra h
  exact hx ⟨hxO, hxk, h⟩

end TauCeti
