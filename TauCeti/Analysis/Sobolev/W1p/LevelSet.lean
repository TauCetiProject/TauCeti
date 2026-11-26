/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.ChainRule

import Mathlib.Algebra.Order.Group.PosPart
import TauCeti.MeasureTheory.Function.EssSup
import TauCeti.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

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
principle. Its level-set argument is
`TauCeti.W1p.ae_value_le_of_forall_le_of_tendsto`: for `k ≥ 0`, if at every level `l ≥ k` exceeded
on a set of positive measure a fixed positive constant is bounded by a quantity `F(Γₗ)` attached
to `Γₗ = {u > l, ∇u ≠ 0}`, and `F(Γ)` tends to zero with `|Γ|`, then `u ≤ k` almost everywhere.
The gradient of `(u - l)⁺` vanishes almost everywhere outside `Γₗ`, and it is not zero if `u > l`
on a set of positive measure and a Sobolev inequality holds for `(u - l)⁺`.

Above a level `l ≥ 0`, `u = (u - l)⁺ + l` and `∇(u - l)⁺ = ∇u`, while below it `(u - l)⁺` and its
gradient vanish (`TauCeti.W1p.ae_posPartAbove_cases`). So a first-order term tested against
`(u - l)⁺` only sees the truncation:
`∫ ⟪b, ∇u⟫ (u - l)⁺ = ∫ ⟪b, ∇(u - l)⁺⟫ (u - l)⁺`
(`TauCeti.W1p.integral_inner_gradient_mul_value_posPartAbove`).

The same holds for the classical gradient of a `C¹` function, which is read off from the weak
statement on small balls. In particular a level set of a `C¹` function on which its derivative
does not vanish is null.
-/

public section

namespace TauCeti

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Gradient Topology

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

/-- At a level `k`, the jet of a Sobolev function has zero gradient almost everywhere on the
level set of its value. -/
theorem W1p.snd_ae_eq_zero_of_fst_eq (hp : p ≠ ∞) (u : W1p mu Omega p) (k : ℝ) :
    ∀ᵐ x ∂mu.restrict Omega, ((u : Sobolev1JetLp mu Omega p) x).fst = k →
      ((u : Sobolev1JetLp mu Omega p) x).snd = 0 := by
  filter_upwards [W1p.value_apply_ae u, W1p.gradient_apply_ae u,
    W1p.gradient_ae_eq_zero_on_level_set hp u k] with x hv hg hz
  intro hx
  rw [← hg]
  exact hz (hv.trans hx)

/-- Weak gradients agree almost everywhere wherever the values agree, even if their
coincidence set has empty interior. -/
theorem W1p.gradient_ae_eq_on_eq (hp : p ≠ ∞) (u v : W1p mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      W1p.value u x = W1p.value v x → W1p.gradient u x = W1p.gradient v x := by
  filter_upwards [W1p.gradient_ae_eq_zero_on_level_set hp (u - v) 0, W1p.value_sub_ae u v,
    W1p.gradient_sub_ae u v] with x hx hux hgx
  intro h
  apply sub_eq_zero.mp
  simpa only [hgx, Pi.sub_apply] using hx (by rw [hux, Pi.sub_apply, h, sub_self])

/-- The set `{u > l, ∇u ≠ 0}` of a Sobolev function is measurable. -/
theorem W1p.measurableSet_lt_value_and_gradient_ne_zero (u : W1p mu Omega p) (l : ℝ) :
    MeasurableSet {x | l < W1p.value u x ∧ W1p.gradient u x ≠ 0} :=
  (measurableSet_lt measurable_const (Lp.stronglyMeasurable (W1p.value u)).measurable).inter
    ((Lp.stronglyMeasurable (W1p.gradient u)).measurable (measurableSet_singleton 0).compl)

/-- If increasing levels `mⱼ`, eventually above `k`, have a null intersection of the sets
`{u > mⱼ, ∇u ≠ 0}`, and each lies below an admissible level `l ≥ k` (one exceeded by `u` on a set
of positive measure), then admissible levels along which the measure of `{u > l, ∇u ≠ 0}` tends to
zero exist. -/
private theorem W1p.exists_tendsto_measure_of_monotone_levels (u : W1p mu Omega p) {k : ℝ}
    (hfin : ∀ l, k < l → mu.restrict Omega {x | l < W1p.value u x} ≠ ∞)
    (m : ℕ → ℝ) (hm : Monotone m) (hmk : ∃ i, k < m i)
    (hnull : mu.restrict Omega (⋂ j, {x | m j < W1p.value u x ∧ W1p.gradient u x ≠ 0}) = 0)
    (hL : ∀ j, ∃ l, k ≤ l ∧ m j ≤ l ∧ ¬ ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ l) :
    ∃ l : ℕ → ℝ, (∀ j, k ≤ l j ∧ ¬ ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ l j) ∧
      Tendsto (fun j ↦ mu.restrict Omega {x | l j < W1p.value u x ∧ W1p.gradient u x ≠ 0})
        atTop (𝓝 0) := by
  set μ := mu.restrict Omega
  set T : ℝ → Set E :=
    fun l ↦ {x | l < W1p.value u x ∧ W1p.gradient u x ≠ 0}
  have hT : ∀ l, MeasurableSet (T l) := W1p.measurableSet_lt_value_and_gradient_ne_zero u
  have hTanti : Antitone T := fun l l' hll' x hx ↦ ⟨hll'.trans_lt hx.1, hx.2⟩
  obtain ⟨i, hi⟩ := hmk
  choose l hkl hml hnot using hL
  refine ⟨l, fun j ↦ ⟨hkl j, hnot j⟩, tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds ?_ (fun _ ↦ zero_le) fun j ↦ measure_mono (hTanti (hml j))⟩
  have := tendsto_measure_iInter_atTop (μ := μ) (s := fun j ↦ T (m j))
    (fun j ↦ (hT _).nullMeasurableSet) (fun i j hij ↦ hTanti (hm hij))
    ⟨i, ne_top_of_le_ne_top (hfin _ hi) (measure_mono fun _ hx ↦ hx.1)⟩
  rwa [hnull] at this

/-- The bounded case of `W1p.exists_tendsto_measure_lt_value_and_gradient_ne_zero`: `u` is
essentially bounded above, so there are admissible levels `lⱼ ≥ k` along which the measure of
`{u > lⱼ, ∇u ≠ 0}` tends to zero. -/
private theorem W1p.exists_tendsto_measure_of_bddAbove (hp : p ≠ ∞) (u : W1p mu Omega p) {k : ℝ}
    (hfin : ∀ l, k < l → mu.restrict Omega {x | l < W1p.value u x} ≠ ∞)
    (hk : ¬ ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ k)
    (hbdd : BddAbove {l : ℝ | k ≤ l ∧ ¬ ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ l}) :
    ∃ l : ℕ → ℝ, (∀ j, k ≤ l j ∧ ¬ ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ l j) ∧
      Tendsto (fun j ↦ mu.restrict Omega {x | l j < W1p.value u x ∧ W1p.gradient u x ≠ 0})
        atTop (𝓝 0) := by
  set μ := mu.restrict Omega
  set L : Set ℝ := {l | k ≤ l ∧ ¬ ∀ᵐ x ∂μ, W1p.value u x ≤ l}
  have hkL : k ∈ L := ⟨le_rfl, hk⟩
  obtain ⟨hle, hkM⟩ := ae_le_csSup_of_bddAbove (W1p.value u) hk hbdd
  set M := sSup L
  refine W1p.exists_tendsto_measure_of_monotone_levels u hfin (fun j ↦ M - 1 / ((j : ℝ) + 1))
    (fun i j hij ↦ ?_) ?_ ?_ fun j ↦ ?_
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
  by_cases hbdd : BddAbove {l : ℝ | k ≤ l ∧ ¬ ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ l}
  · exact W1p.exists_tendsto_measure_of_bddAbove hp u hfin hk hbdd
  · -- `u` is essentially unbounded above; take the levels `j`.
    refine W1p.exists_tendsto_measure_of_monotone_levels u hfin (fun j ↦ (j : ℝ)) Nat.mono_cast
      (exists_nat_gt k) ?_ fun j ↦ ?_
    · rw [measure_eq_zero_iff_ae_notMem]
      refine Eventually.of_forall fun x hx ↦ ?_
      obtain ⟨j, hj⟩ := exists_nat_gt (W1p.value u x)
      exact lt_asymm hj (mem_iInter.1 hx j).1
    · obtain ⟨l, hlL, hjl⟩ := not_bddAbove_iff.1 hbdd j
      exact ⟨l, hlL.1, hjl.le, hlL.2⟩

/-- **The level-set argument of the weak maximum principle.** Let `u ∈ W^{1,p}(Ω)`,
`1 ≤ p < ∞`, and `k ≥ 0`, and let `F` assign to every set a quantity in `[0, ∞]` which tends to
zero along every sequence of measurable sets whose measures tend to zero. If a constant `c ≠ 0`
satisfies `c ≤ F {u > l, ∇u ≠ 0}` at every level `l ≥ k` which `u` exceeds on a set of positive
measure, then `u ≤ k` almost everywhere: otherwise there are such levels along which
`|{u > l, ∇u ≠ 0}| → 0` (`TauCeti.W1p.exists_tendsto_measure_lt_value_and_gradient_ne_zero`). -/
theorem W1p.ae_value_le_of_forall_le_of_tendsto (hp : p ≠ ∞) (u : W1p mu Omega p) {k : ℝ}
    (hk : 0 ≤ k) {F : Set E → ℝ≥0∞}
    (hF : ∀ Γ : ℕ → Set E, (∀ j, MeasurableSet (Γ j)) →
      Tendsto (fun j ↦ mu.restrict Omega (Γ j)) atTop (𝓝 0) →
        Tendsto (fun j ↦ F (Γ j)) atTop (𝓝 0))
    {c : ℝ≥0∞} (hc : c ≠ 0)
    (hlevel : ∀ l, k ≤ l → (¬ ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ l) →
      c ≤ F {x | l < W1p.value u x ∧ W1p.gradient u x ≠ 0}) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ k := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  -- Since `u ∈ Lᵖ` and `k ≥ 0`, the superlevel sets `{u > l}`, `l > k`, have finite measure.
  have hfin : ∀ l, k < l → mu.restrict Omega {x | l < W1p.value u x} ≠ ∞ := fun l hkl ↦
    ((Lp.memLp (W1p.value u)).measure_gt_lt_top hp0 hp (hk.trans_lt hkl)).ne
  by_contra hcon
  obtain ⟨l, hl, htend⟩ := W1p.exists_tendsto_measure_lt_value_and_gradient_ne_zero hp u hfin hcon
  exact hc (le_antisymm (ge_of_tendsto' (hF _
    (fun j ↦ W1p.measurableSet_lt_value_and_gradient_ne_zero u (l j)) htend)
    fun j ↦ hlevel (l j) (hl j).1 (hl j).2) zero_le)

/-- Above a level `l ≥ 0`, the gradient of `(u - l)⁺` vanishes almost everywhere outside the set
`{u > l, ∇u ≠ 0}`. -/
theorem W1p.ae_mem_of_gradient_posPartAbove_ne_zero (hp : p ≠ ∞) {l : ℝ} (hl : 0 ≤ l)
    (u : W1p mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.gradient (W1p.posPartAbove hp hl u) x ≠ 0 →
      x ∈ {x | l < W1p.value u x ∧ W1p.gradient u x ≠ 0} := by
  filter_upwards [W1p.gradient_posPartAbove_ae hp hl u] with x hx hne
  rw [hx] at hne
  by_cases hlt : l < W1p.value u x
  · rw [indicator_of_mem (s := {y | l < W1p.value u y}) hlt] at hne
    exact ⟨hlt, hne⟩
  · exact absurd (indicator_of_notMem (s := {y | l < W1p.value u y}) hlt _) hne

/-- Above a level `l ≥ 0`, `u = (u - l)⁺ + l` and `∇(u - l)⁺ = ∇u`; below it `(u - l)⁺` and its
gradient vanish. -/
theorem W1p.ae_posPartAbove_cases (hp : p ≠ ∞) {l : ℝ} (hl : 0 ≤ l) (u : W1p mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      (W1p.value u x = W1p.value (W1p.posPartAbove hp hl u) x + l ∧
        W1p.gradient (W1p.posPartAbove hp hl u) x = W1p.gradient u x) ∨
      (W1p.value (W1p.posPartAbove hp hl u) x = 0 ∧
        W1p.gradient (W1p.posPartAbove hp hl u) x = 0) := by
  filter_upwards [W1p.value_posPartAbove_ae hp hl u, W1p.gradient_posPartAbove_ae hp hl u]
    with x hv hg
  by_cases hx : l < W1p.value u x
  · left
    rw [hv, hg, indicator_of_mem (s := {y | l < W1p.value u y}) hx, max_eq_left (by linarith)]
    exact ⟨by ring, rfl⟩
  · right
    rw [hv, hg, indicator_of_notMem (s := {y | l < W1p.value u y}) hx,
      max_eq_right (sub_nonpos.2 (not_lt.1 hx))]
    exact ⟨rfl, rfl⟩

/-- Above a level `l ≥ 0`, a first-order term tested against `v = (u - l)⁺` only sees `v`:
`∫ ⟪b, ∇u⟫ v = ∫ ⟪b, ∇v⟫ v`, since `∇u = ∇v` where `v ≠ 0`. -/
theorem W1p.integral_inner_gradient_mul_value_posPartAbove (hp : p ≠ ∞) {l : ℝ} (hl : 0 ≤ l)
    (u : W1p mu Omega p) (b : E → E) :
    ∫ x in Omega, ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (W1p.posPartAbove hp hl u) x ∂mu =
      ∫ x in Omega, ⟪b x, W1p.gradient (W1p.posPartAbove hp hl u) x⟫_ℝ *
        W1p.value (W1p.posPartAbove hp hl u) x ∂mu := by
  refine integral_congr_ae ((W1p.ae_posPartAbove_cases hp hl u).mono fun x hx ↦ ?_)
  rcases hx with ⟨-, hg⟩ | ⟨hv, -⟩
  · simp only [hg]
  · simp [hv]

omit [FiniteDimensional ℝ E] in
/-- If `∇v = 0` almost everywhere outside a measurable set `Γ`, then in `ℝ≥0∞` the weighted
integral `∫_Ω w |∇v| |v|` of a nonnegative weight `w` is a lower integral that only sees `Γ`. -/
theorem W1p.ofReal_integral_mul_norm_gradient_mul_norm_value_eq {v : W1p mu Omega p}
    {w : E → ℝ} (hw : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ w x)
    (hint : Integrable (fun x ↦ w x * (‖W1p.gradient v x‖ * ‖W1p.value v x‖)) (mu.restrict Omega))
    {Γ : Set E} (hΓ : MeasurableSet Γ)
    (hgrad : ∀ᵐ x ∂mu.restrict Omega, W1p.gradient v x ≠ 0 → x ∈ Γ) :
    ENNReal.ofReal (∫ x in Omega, w x * (‖W1p.gradient v x‖ * ‖W1p.value v x‖) ∂mu) =
      ∫⁻ x in Γ, ‖w x‖ₑ * (‖W1p.gradient v x‖ₑ * ‖W1p.value v x‖ₑ) ∂mu.restrict Omega := by
  rw [ofReal_integral_eq_lintegral_ofReal hint
      (hw.mono fun x hx ↦ mul_nonneg hx (by positivity)), ← lintegral_indicator hΓ]
  refine lintegral_congr_ae ?_
  filter_upwards [hgrad, hw] with x hx hwx
  by_cases hxΓ : x ∈ Γ
  · rw [indicator_of_mem hxΓ, ENNReal.ofReal_mul hwx, ENNReal.ofReal_mul (norm_nonneg _),
      ofReal_norm, ofReal_norm, Real.eNorm_of_nonneg hwx]
  · have hg0 : W1p.gradient v x = 0 := by_contra fun hne ↦ hxΓ (hx hne)
    rw [indicator_of_notMem hxΓ, hg0, norm_zero, zero_mul, mul_zero, ENNReal.ofReal_zero]

/-- If `u > l ≥ 0` on a set of positive measure and `(u - l)⁺` satisfies a Sobolev inequality
`‖(u - l)⁺‖_q ≤ S ‖∇(u - l)⁺‖_p` with `q ≠ 0`, then the gradient of `(u - l)⁺` is not zero:
otherwise `(u - l)⁺ = 0`, that is `u ≤ l`, almost everywhere. -/
theorem W1p.enorm_gradient_posPartAbove_ne_zero (hp : p ≠ ∞) {l : ℝ} (hl : 0 ≤ l)
    {u : W1p mu Omega p} {q : ℝ≥0∞} (hq : q ≠ 0) {S : ℝ≥0}
    (hsob : eLpNorm (W1p.value (W1p.posPartAbove hp hl u)) q (mu.restrict Omega) ≤
      S * ‖W1p.gradient (W1p.posPartAbove hp hl u)‖ₑ)
    (hnot : ¬ ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ l) :
    ‖W1p.gradient (W1p.posPartAbove hp hl u)‖ₑ ≠ 0 := by
  intro hzero
  refine hnot ?_
  have hv0 : eLpNorm (W1p.value (W1p.posPartAbove hp hl u)) q (mu.restrict Omega) = 0 :=
    le_antisymm (hsob.trans_eq (by rw [hzero, mul_zero])) zero_le
  rw [eLpNorm_eq_zero_iff hq] at hv0
  filter_upwards [hv0, W1p.value_posPartAbove_ae hp hl u] with x h₁ h₂
  rw [h₂, Pi.zero_apply] at h₁
  linarith [le_max_left (W1p.value u x - l) 0]

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

namespace ContDiff

open MeasureTheory TauCeti TopologicalSpace
open scoped Gradient

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]

/-- A level set of a `C¹` function is null if the derivative does not vanish on it. -/
theorem measure_setOf_eq_eq_zero_of_fderiv_ne_zero {w : E → ℝ} (hw : ContDiff ℝ 1 w) {k : ℝ}
    (hreg : ∀ x, w x = k → fderiv ℝ w x ≠ 0) : mu {x | w x = k} = 0 := by
  have h := gradient_ae_eq_zero_on_level_set_of_contDiffOn (mu := mu) (Omega := ⊤)
    hw.contDiffOn k
  rw [Opens.coe_top, Measure.restrict_univ] at h
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [h] with x hx hxk
  exact hreg x hxk (by simpa [gradient] using hx hxk)

end ContDiff
