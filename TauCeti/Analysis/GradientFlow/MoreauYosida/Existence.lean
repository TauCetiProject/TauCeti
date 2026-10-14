/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Sequences
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Data.EReal.Operations

/-!
# Existence of resolvent steps and of minimizing movement sequences

For an energy `φ : X → EReal` on an extended metric space and a time step `τ > 0`, a point of the
resolvent `J_τ x` minimizes `y ↦ φ y + d(x, y)² / (2τ)`. This file proves, by the direct method of
the calculus of variations, that such a minimizer exists under the hypotheses of
Ambrosio–Gigli–Savaré, and hence that the minimizing movement scheme can be run from every point
of the relevant finite-distance component.

The hypotheses use an auxiliary notion of convergence on `X`, which need not be that of the
metric. In applications it is weaker: the weak topology of a Hilbert space, or the narrow topology
on the Wasserstein space `P₂(X)`, whose bounded sets are not relatively compact for the metric.
Following Ambrosio–Gigli–Savaré, Assumption 2.1, with `y_n ⇀ y` denoting this convergence, the
hypotheses are:

* the distance is sequentially lower semicontinuous: if `y_n ⇀ y`, then
  `d(x, y) ≤ liminf d(x, y_n)` (only the point `x` of the resolvent step is needed);
* the energy is sequentially lower semicontinuous on bounded sets: if `y_n ⇀ y` and `(y_n)` has
  finite diameter, then `φ y ≤ liminf φ (y_n)`;
* bounded sublevels are relatively sequentially compact: a sequence of finite diameter along
  which `φ` is bounded above by a real number has a subsequence with `y_{n_k} ⇀ y` for some `y`;
* coercivity: `φ_{τ₀}(x₀) > -∞` for some time step `τ₀` and point `x₀`, where `φ_τ` is the
  Moreau–Yosida approximation.

Coercivity at `(τ₀, x₀)` propagates to every smaller time step and every point at finite distance
from `x₀` (`TauCeti.moreauYosida_ne_bot_of_lt`), through the quantitative bound
`φ_{τ₀}(x₀) ≤ φ_τ(x) + d(x, x₀)² / (2 (τ₀ - τ))` for `τ < τ₀`. Together with the other hypotheses
it makes a minimizing sequence for `φ_τ(x)` bounded and contained in a sublevel of `φ`, so that a
limit of a subsequence is a resolvent step.

## Main results

* `TauCeti.moreauYosida_le_moreauYosida_add`: the bound
  `φ_{τ₀}(x₀) ≤ φ_τ(x) + d(x, x₀)² / (2 (τ₀ - τ))` for `τ < τ₀` and `d(x, x₀) < ∞`, and
  `TauCeti.moreauYosida_ne_bot_of_lt`: coercivity propagates.
* `TauCeti.le_liminf_apply_add_edist_sq_div`: the penalized energy `φ + d(x, ·)² / (2τ)` is
  lower semicontinuous along any convergence for which `φ` and `d(x, ·)` are.
* `TauCeti.moreauYosidaResolvent_nonempty`: under the hypotheses above, the resolvent `J_τ x` is
  nonempty for every `0 < τ < τ₀` and every `x` at finite distance from `x₀`.
* `TauCeti.moreauYosidaResolvent_nonempty_of_lowerSemicontinuous`: in a proper metric space, the
  resolvent of a lower semicontinuous coercive energy is nonempty, the auxiliary convergence being
  that of the metric.
* `TauCeti.exists_forall_mem_moreauYosidaResolvent`: under the same hypotheses, every point at
  finite distance from `x₀` starts a minimizing movement sequence, in which each term is a
  resolvent step from the previous one.

## Implementation notes

The auxiliary convergence is a map `l : X → Filter X`, with `y_n ⇀ y` meaning
`Tendsto (fun n ↦ y_n) atTop (l y)`. For a topology `σ` on `X` one takes `l = @nhds X σ`, and
for a topology induced by a map `f : X → Y`, such as the narrow topology on `P₂(X)` pulled back
from probability measures, `l y = comap f (𝓝 (f y))`. No property of `l` is used. Taking a map
rather than a second `TopologicalSpace X` instance keeps it from competing with the topology of
the metric.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 2, Section 2.1 (Assumption 2.1) and
  Section 2.2 (Lemma 2.2.1 and Corollary 2.2.2).
-/

public section

noncomputable section

open Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti

section PseudoEMetricSpace

variable {X : Type*} [PseudoEMetricSpace X] {φ : X → EReal} {τ τ' τ₀ : ℝ≥0} {x x₀ : X}

/-- For time steps `τ < τ₀`, the penalty `d(x₀, z)² / (2τ₀)` is at most
`d(x, z)² / (2τ) + d(x, x₀)² / (2 (τ₀ - τ))`. With `a = d(x, z)`, `b = d(x, x₀)` and `s = τ₀ - τ`,
this is the triangle inequality followed by `(a + b)² / (τ + s) ≤ a² / τ + b² / s`. -/
theorem edist_sq_div_le_add (hττ₀ : τ < τ₀) (x x₀ z : X) :
    edist x₀ z ^ 2 / (2 * τ₀) ≤ edist x z ^ 2 / (2 * τ) + edist x x₀ ^ 2 / (2 * (τ₀ - τ)) := by
  have hs : (τ₀ : ℝ≥0∞) - τ ≠ 0 := (tsub_pos_of_lt (ENNReal.coe_lt_coe.2 hττ₀)).ne'
  have hτ₀ : (τ₀ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 (pos_of_gt hττ₀).ne'
  have hxzx₀ : edist x₀ z ≤ edist x x₀ + edist x z := edist_triangle_left x₀ z x
  -- Infinite distances make the right-hand side infinite.
  rcases eq_or_ne (edist x x₀) ⊤ with hb | hb
  · rw [hb, ENNReal.top_pow two_ne_zero, ENNReal.top_div_of_ne_top (by finiteness), add_top]
    exact le_top
  rcases eq_or_ne (edist x z) ⊤ with ha | ha
  · rw [ha, ENNReal.top_pow two_ne_zero, ENNReal.top_div_of_ne_top (by finiteness), top_add]
    exact le_top
  -- With `τ = 0`, the right-hand side is infinite unless `d(x, z) = 0`, and then `z` is as far
  -- from `x₀` as `x` is.
  rcases eq_or_ne τ 0 with rfl | hτ
  · rcases eq_or_ne (edist x z) 0 with ha₀ | ha₀
    · rw [ha₀, add_zero] at hxzx₀
      rw [ha₀, ENNReal.coe_zero, tsub_zero, zero_pow two_ne_zero, ENNReal.zero_div, zero_add]
      gcongr
    · rw [ENNReal.coe_zero, mul_zero, ENNReal.div_zero (pow_ne_zero 2 ha₀), top_add]
      exact le_top
  have hτ' : (τ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hτ
  have hxz : edist x₀ z ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hb, ha⟩) hxzx₀
  have h₁ : edist x z ^ 2 / (2 * τ) ≠ ⊤ := ENNReal.div_ne_top (by finiteness) (by simp [hτ'])
  have h₂ : edist x x₀ ^ 2 / (2 * (τ₀ - τ)) ≠ ⊤ :=
    ENNReal.div_ne_top (by finiteness) (by simp [hs])
  rw [← ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by finiteness) (by simp [hτ₀]))
    (ENNReal.add_ne_top.2 ⟨h₁, h₂⟩), ENNReal.toReal_add h₁ h₂]
  have hc := ENNReal.toReal_le_add hxzx₀ hb ha
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal, ENNReal.toReal_sub_of_le (ENNReal.coe_le_coe.2 hττ₀.le)
      ENNReal.coe_ne_top]
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hτ)
  have hsr : (0 : ℝ) < τ₀ - τ := sub_pos.2 (NNReal.coe_lt_coe.2 hττ₀)
  calc (edist x₀ z).toReal ^ 2 / (2 * τ₀)
      ≤ ((edist x x₀).toReal + (edist x z).toReal) ^ 2 / (2 * τ₀) := by gcongr
    _ ≤ (edist x z).toReal ^ 2 / (2 * τ) + (edist x x₀).toReal ^ 2 / (2 * (τ₀ - τ)) := by
      have := Finset.sq_sum_div_le_sum_sq_div Finset.univ
        ![(edist x x₀).toReal, (edist x z).toReal] (g := ![2 * ((τ₀ : ℝ) - τ), 2 * τ])
        (by simp only [Finset.mem_univ, Fin.forall_fin_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, forall_const]; constructor <;> positivity)
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
      rwa [show (2 : ℝ) * τ₀ = 2 * (τ₀ - τ) + 2 * τ by ring, add_comm (_ ^ 2 / (2 * (τ : ℝ)))]

/-- **Propagation of coercivity**, quantitatively (Ambrosio–Gigli–Savaré, Lemma 2.2.1). For time
steps `τ < τ₀` and a point `x` at finite distance from `x₀`,
`φ_{τ₀}(x₀) ≤ φ_τ(x) + d(x, x₀)² / (2 (τ₀ - τ))`. -/
theorem moreauYosida_le_moreauYosida_add (hττ₀ : τ < τ₀) (hx : edist x x₀ ≠ ⊤) :
    moreauYosida φ τ₀ x₀ ≤
      moreauYosida φ τ x + (edist x x₀ ^ 2 / (2 * (τ₀ - τ)) : ℝ≥0∞) := by
  have hQ : edist x x₀ ^ 2 / (2 * (τ₀ - τ)) ≠ ⊤ :=
    ENNReal.div_ne_top (by finiteness)
      (by simp [(tsub_pos_of_lt (ENNReal.coe_lt_coe.2 hττ₀)).ne'])
  rw [← EReal.coe_ennreal_toReal hQ, ← EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
    (.inl (EReal.coe_ne_top _)), le_moreauYosida_iff]
  intro z hz
  rw [EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _)),
    EReal.coe_ennreal_toReal hQ, add_assoc, ← EReal.coe_ennreal_add]
  have hx₀z : edist x₀ z ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hx, hz⟩)
    (edist_triangle_left x₀ z x)
  exact (moreauYosida_le φ τ₀ hx₀z).trans (add_le_add le_rfl
    (EReal.coe_ennreal_le_coe_ennreal_iff.2 (edist_sq_div_le_add hττ₀ x x₀ z)))

/-- **Propagation of coercivity.** If `φ_{τ₀}(x₀) > -∞`, then `φ_τ(x) > -∞` for every time step
`τ < τ₀` and every point `x` at finite distance from `x₀`. -/
theorem moreauYosida_ne_bot_of_lt (hττ₀ : τ < τ₀) (hx : edist x x₀ ≠ ⊤)
    (h₀ : moreauYosida φ τ₀ x₀ ≠ ⊥) : moreauYosida φ τ x ≠ ⊥ := by
  intro h
  have := moreauYosida_le_moreauYosida_add (φ := φ) hττ₀ hx
  rw [h, EReal.bot_add, le_bot_iff] at this
  exact h₀ this

/-- A point `v` at finite distance from `x` whose penalized energy with time step `τ` is at most
`B` lies at distance `d` from `x` with `d² (τ' - τ) ≤ (B - A) 2ττ'`, where `A = φ_{τ'}(x)` for a
larger time step `τ'`: subtract `A ≤ φ v + d² / (2τ')` from `φ v + d² / (2τ) ≤ B`. -/
private theorem toReal_edist_sq_mul_le (hτ : 0 < τ) (hττ' : τ < τ') {A B : ℝ}
    (hA : moreauYosida φ τ' x = A) {v : X} (hv : edist x v ≠ ⊤)
    (hB : φ v + (edist x v ^ 2 / (2 * τ) : ℝ≥0∞) ≤ B) :
    (edist x v).toReal ^ 2 * (τ' - τ) ≤ (B - A) * (2 * τ * τ') := by
  have hτ' : 0 < τ' := hτ.trans hττ'
  have hP : edist x v ^ 2 / (2 * τ) ≠ ⊤ := ENNReal.div_ne_top (by finiteness) (by simp [hτ.ne'])
  have hP' : edist x v ^ 2 / (2 * τ') ≠ ⊤ :=
    ENNReal.div_ne_top (by finiteness) (by simp [hτ'.ne'])
  have hA' := hA ▸ moreauYosida_le φ τ' hv
  have htop : φ v ≠ ⊤ := by
    rintro h
    rw [h, EReal.top_add_of_ne_bot (EReal.coe_ennreal_ne_bot _), top_le_iff] at hB
    exact EReal.coe_ne_top _ hB
  have hbot : φ v ≠ ⊥ := by
    rintro h
    rw [h, EReal.bot_add, le_bot_iff] at hA'
    exact EReal.coe_ne_bot _ hA'
  obtain ⟨a, ha⟩ : ∃ a : ℝ, φ v = a := ⟨_, (EReal.coe_toReal htop hbot).symm⟩
  rw [ha, ← EReal.coe_ennreal_toReal hP, ← EReal.coe_add, EReal.coe_le_coe_iff] at hB
  rw [ha, EReal.coe_le_coe_add_coe_ennreal_iff hP'] at hA'
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal] at hB hA'
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have hττ'r : (τ : ℝ) < τ' := NNReal.coe_lt_coe.2 hττ'
  have key : (edist x v).toReal ^ 2 * (τ' - τ) / (2 * τ * τ') ≤ B - A := by
    have : (edist x v).toReal ^ 2 * (τ' - τ) / (2 * τ * τ') =
        (edist x v).toReal ^ 2 / (2 * τ) - (edist x v).toReal ^ 2 / (2 * τ') := by
      field_simp
    linarith
  rwa [div_le_iff₀ (by positivity)] at key

/-- **Lower semicontinuity of the penalized energy.** If `φ y ≤ liminf φ (w n)` and
`d(x, y) ≤ liminf d(x, w n)`, then the penalized energy `φ + d(x, ·)² / (2τ)` satisfies the same
inequality: the penalty is a monotone continuous function of `d(x, ·)`, and the `liminf` of a sum
dominates the sum of the `liminf`s. -/
theorem le_liminf_apply_add_edist_sq_div {ι : Type*} {f : Filter ι} (hτ : 0 < τ) {w : ι → X}
    {y : X} (hd : edist x y ≤ liminf (fun n ↦ edist x (w n)) f)
    (hφ : φ y ≤ liminf (fun n ↦ φ (w n)) f) :
    φ y + (edist x y ^ 2 / (2 * τ) : ℝ≥0∞) ≤
      liminf (fun n ↦ φ (w n) + (edist x (w n) ^ 2 / (2 * τ) : ℝ≥0∞)) f := by
  rcases f.eq_or_neBot with rfl | _
  · simp
  set g : ℝ≥0∞ → EReal := fun t ↦ ((t ^ 2 / (2 * τ) : ℝ≥0∞) : EReal)
  have hg : Monotone g := fun a b hab ↦ EReal.coe_ennreal_le_coe_ennreal_iff.2 (by gcongr)
  have hgc : Continuous g := continuous_coe_ennreal_ereal.comp
    ((ENNReal.continuous_div_const _ (by simp [hτ.ne'])).comp (ENNReal.continuous_pow 2))
  calc φ y + g (edist x y)
      ≤ liminf (fun n ↦ φ (w n)) f + liminf (fun n ↦ g (edist x (w n))) f :=
        add_le_add hφ ((hg hd).trans_eq (hg.map_liminf_of_continuousAt _ hgc.continuousAt))
    _ ≤ liminf (fun n ↦ φ (w n) + g (edist x (w n))) f := EReal.le_liminf_add

/-- **Existence of resolvent steps** (Ambrosio–Gigli–Savaré, Corollary 2.2.2). Let `l y` be the
filter of an auxiliary convergence `y_n ⇀ y` on `X`, possibly weaker than that of the metric (for
instance `l = @nhds X σ` for a topology `σ`), such that

* `y ↦ d(x, y)` is sequentially lower semicontinuous for `⇀`;
* `φ` is sequentially lower semicontinuous for `⇀` along sequences of finite diameter;
* every sequence of finite diameter along which `φ` is bounded above by a real number has a
  `⇀`-convergent subsequence;

and let `φ` be coercive: `φ_{τ₀}(x₀) > -∞`. Then for every time step `0 < τ < τ₀` and every
point `x` at finite distance from `x₀`, the resolvent `J_τ x` is nonempty. -/
theorem moreauYosidaResolvent_nonempty {l : X → Filter X}
    (hd : ∀ ⦃v : ℕ → X⦄ ⦃y : X⦄, Tendsto v atTop (l y) →
      edist x y ≤ liminf (fun n ↦ edist x (v n)) atTop)
    (hφ : ∀ ⦃v : ℕ → X⦄ ⦃y : X⦄, Metric.ediam (range v) ≠ ⊤ → Tendsto v atTop (l y) →
      φ y ≤ liminf (fun n ↦ φ (v n)) atTop)
    (hcpt : ∀ (c : ℝ) ⦃v : ℕ → X⦄, Metric.ediam (range v) ≠ ⊤ → (∀ n, φ (v n) ≤ c) →
      ∃ y, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (v ∘ ψ) atTop (l y))
    (hτ : 0 < τ) (hττ₀ : τ < τ₀) (hx : edist x x₀ ≠ ⊤) (h₀ : moreauYosida φ τ₀ x₀ ≠ ⊥) :
    (moreauYosidaResolvent φ τ x).Nonempty := by
  -- If `φ_τ(x) = ⊤`, every point at finite distance from `x` is a minimizer, `x` itself included.
  rcases eq_or_ne (moreauYosida φ τ x) ⊤ with htop | htop
  · refine ⟨x, mem_moreauYosidaResolvent_iff.2 ⟨by simp, fun z hz ↦ ?_⟩⟩
    have := moreauYosida_le φ τ hz
    rw [htop, top_le_iff] at this
    exact this ▸ le_top
  -- Coercivity at an intermediate time step `τ < τ' < τ₀` makes `φ_{τ'}(x)` and `φ_τ(x)` real.
  obtain ⟨τ', hττ', hτ'τ₀⟩ := exists_between hττ₀
  have hmono := antitone_moreauYosida φ x hττ'.le
  have hbot' := moreauYosida_ne_bot_of_lt hτ'τ₀ hx h₀
  obtain ⟨M, hM⟩ : ∃ M : ℝ, moreauYosida φ τ x = M :=
    ⟨_, (EReal.coe_toReal htop fun h ↦ hbot' (le_bot_iff.1 (h ▸ hmono))).symm⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, moreauYosida φ τ' x = A :=
    ⟨_, (EReal.coe_toReal (ne_top_of_le_ne_top htop hmono) hbot').symm⟩
  -- A minimizing sequence `v`, with penalized energies below `M + 1 / (n + 1)`.
  have hseq : ∀ n : ℕ, ∃ v, edist x v ≠ ⊤ ∧
      φ v + (edist x v ^ 2 / (2 * τ) : ℝ≥0∞) < ((M + 1 / (n + 1) : ℝ) : EReal) := by
    intro n
    have hlt : moreauYosida φ τ x < ((M + 1 / (n + 1) : ℝ) : EReal) := by
      rw [hM, EReal.coe_lt_coe_iff]
      linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := n)]
    rw [moreauYosida_def] at hlt
    obtain ⟨v, hv⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hvx, hv⟩ := iInf_lt_iff.1 hv
    exact ⟨v, hvx, hv⟩
  choose v hvx hv using hseq
  have hle : ∀ n, φ (v n) + (edist x (v n) ^ 2 / (2 * τ) : ℝ≥0∞) ≤ ((M + 1 : ℝ) : EReal) :=
    fun n ↦ (hv n).le.trans <| EReal.coe_le_coe_iff.2 <| add_le_add le_rfl <|
      (div_le_one n.cast_add_one_pos).2 (by linarith [n.cast_nonneg (α := ℝ)])
  -- The minimizing sequence is bounded and lies in a sublevel of `φ`.
  set C : ℝ := (M + 1 - A) * (2 * τ * τ') / (τ' - τ)
  have hR : ∀ n, edist x (v n) ≤ ENNReal.ofReal √C := fun n ↦ by
    rw [ENNReal.le_ofReal_iff_toReal_le (hvx n) (Real.sqrt_nonneg _)]
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    rw [le_div_iff₀ (sub_pos.2 (NNReal.coe_lt_coe.2 hττ'))]
    exact toReal_edist_sq_mul_le hτ hττ' hA (hvx n) (hle n)
  have hdiam : Metric.ediam (range v) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal √C + ENNReal.ofReal √C) (by finiteness)
      (Metric.ediam_le ?_)
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (edist_triangle_left _ _ x).trans (add_le_add (hR i) (hR j))
  obtain ⟨y, ψ, hψ, hy⟩ := hcpt (M + 1) hdiam fun n ↦
    (le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _)).trans (hle n)
  have hdiam' : Metric.ediam (range (v ∘ ψ)) ≠ ⊤ :=
    ne_top_of_le_ne_top hdiam (Metric.ediam_mono (range_comp_subset_range ψ v))
  -- The limit `y` is at finite distance from `x`.
  have hyx : edist x y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top <|
    (hd hy).trans (liminf_le_of_frequently_le' (Frequently.of_forall fun k ↦ hR (ψ k)))
  -- The penalized energies along the subsequence tend to `M`, so the limit `y` attains `M`.
  have hlim : Tendsto (fun k ↦ ((M + 1 / ((ψ k : ℕ) + 1) : ℝ) : EReal)) atTop (𝓝 (M : EReal)) :=
    EReal.tendsto_coe.2 (by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop).const_add M)
  refine ⟨y, mem_moreauYosidaResolvent_iff_eq_moreauYosida.2
    ⟨hyx, le_antisymm ?_ (moreauYosida_le φ τ hyx)⟩⟩
  rw [hM, ← hlim.liminf_eq]
  exact (le_liminf_apply_add_edist_sq_div hτ (hd hy) (hφ hdiam' hy)).trans
    (liminf_le_liminf (Eventually.of_forall fun k ↦ (hv (ψ k)).le))

/-- **Existence of minimizing movement sequences** (Ambrosio–Gigli–Savaré, Corollary 2.2.2).
Under the hypotheses of `TauCeti.moreauYosidaResolvent_nonempty`, with the lower semicontinuity
of the distance now required from every base point, every point `x` at finite distance from `x₀`
starts a sequence `u` with `u 0 = x` in which each `u (n + 1)` is a resolvent step from `u n`. -/
theorem exists_forall_mem_moreauYosidaResolvent {l : X → Filter X}
    (hd : ∀ (z : X) ⦃v : ℕ → X⦄ ⦃y : X⦄, Tendsto v atTop (l y) →
      edist z y ≤ liminf (fun n ↦ edist z (v n)) atTop)
    (hφ : ∀ ⦃v : ℕ → X⦄ ⦃y : X⦄, Metric.ediam (range v) ≠ ⊤ → Tendsto v atTop (l y) →
      φ y ≤ liminf (fun n ↦ φ (v n)) atTop)
    (hcpt : ∀ (c : ℝ) ⦃v : ℕ → X⦄, Metric.ediam (range v) ≠ ⊤ → (∀ n, φ (v n) ≤ c) →
      ∃ y, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (v ∘ ψ) atTop (l y))
    (hτ : 0 < τ) (hττ₀ : τ < τ₀) (hx : edist x x₀ ≠ ⊤) (h₀ : moreauYosida φ τ₀ x₀ ≠ ⊥) :
    ∃ u : ℕ → X, u 0 = x ∧ ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n) := by
  -- A resolvent step from every point of the finite-distance component of `x₀`.
  have step : ∀ z, ∃ y, edist z x₀ ≠ ⊤ → y ∈ moreauYosidaResolvent φ τ z := fun z ↦ by
    by_cases hz : edist z x₀ = ⊤
    · exact ⟨z, fun h ↦ (h hz).elim⟩
    · obtain ⟨y, hy⟩ := moreauYosidaResolvent_nonempty (hd z) hφ hcpt hτ hττ₀ hz h₀
      exact ⟨y, fun _ ↦ hy⟩
  choose f hf using step
  have hu : ∀ n, edist (f^[n] x) x₀ ≠ ⊤ := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ne_top_of_le_ne_top
        (ENNReal.add_ne_top.2 ⟨edist_ne_top_of_mem_moreauYosidaResolvent (hf _ ih), ih⟩)
        (edist_triangle_left _ _ _)
  exact ⟨fun n ↦ f^[n] x, rfl, fun n ↦ by
    simpa only [Function.iterate_succ_apply'] using hf _ (hu n)⟩

end PseudoEMetricSpace

/-- **Existence of resolvent steps in a proper space.** In a proper metric space, the resolvent
`J_τ x` of a lower semicontinuous energy `φ` with `φ_{τ₀}(x₀) > -∞` is nonempty for every time
step `0 < τ < τ₀`. This is `TauCeti.moreauYosidaResolvent_nonempty` with `l = 𝓝`, the
convergence of the metric, for which bounded sequences have convergent subsequences. -/
theorem moreauYosidaResolvent_nonempty_of_lowerSemicontinuous {X : Type*} [PseudoMetricSpace X]
    [ProperSpace X] {φ : X → EReal} {τ τ₀ : ℝ≥0} {x x₀ : X} (hφ : LowerSemicontinuous φ)
    (hτ : 0 < τ) (hττ₀ : τ < τ₀) (h₀ : moreauYosida φ τ₀ x₀ ≠ ⊥) :
    (moreauYosidaResolvent φ τ x).Nonempty :=
  moreauYosidaResolvent_nonempty (l := 𝓝)
    (fun _ y hv ↦ (((continuous_const.edist continuous_id).tendsto y).comp hv).liminf_eq.ge)
    (fun _ y _ hv ↦ (hφ.le_liminf y).trans hv.liminf_le_liminf_comp)
    (fun _ _ hv _ ↦
      let ⟨a, _, ψ, hψ, h⟩ := tendsto_subseq_of_bounded (Metric.isBounded_iff_ediam_ne_top.2 hv)
        fun n ↦ mem_range_self n
      ⟨a, ψ, hψ, h⟩)
    hτ hττ₀ (edist_ne_top x x₀) h₀

end TauCeti
