/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Taylor.Parameter
public import TauCeti.Analysis.Calculus.TimeIncrements

/-!
# Time-dependent Brownian Taylor partition formula

For a function with two continuous spatial derivatives and one continuous time
derivative, the endpoint increment minus its left-point spatial Taylor sums converges
in probability to the ordinary integral of its time derivative along Brownian motion.
The spatial second derivative is jointly continuous; no mixed or second time derivative
is required. Time derivatives are taken within the closed horizon, so one-sided
endpoint derivatives suffice.

This identifies the finite-variation time term in the partition proof of the
time-dependent Itô formula. It does not yet identify the spatial linear sum with a
stochastic integral or the spatial quadratic sum with its time-integral limit.
There are no growth or moment assumptions on the function, no filtration hypothesis,
and no nestedness requirement on the partitions. Repeated dates and a zero-length
horizon are allowed.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second
  edition, Springer, 1991, §3.3.
-/

public section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory.IsBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℝ≥0}

private theorem aestronglyMeasurable_timeSpaceRemainder (hB : IsBrownianReal B P)
    (hf : ∀ t ∈ Icc (a : ℝ) b, ContDiff ℝ 2 (f t))
    {n : ℕ} {τ : ℕ → ℝ≥0} (hτ : MonotoneOn τ (Iic n))
    (ha : τ 0 = a) (hb : τ n = b) :
    AEStronglyMeasurable (fun ω ↦ f b (B b ω) - f a (B a ω) -
      (∑ i ∈ Finset.range n, deriv (f (τ i)) (B (τ i) ω) *
        (B (τ (i + 1)) ω - B (τ i) ω)) -
      1 / 2 * ∑ i ∈ Finset.range n, deriv (deriv (f (τ i))) (B (τ i) ω) *
        (B (τ (i + 1)) ω - B (τ i) ω) ^ 2) P := by
  have hab : a ≤ b := ha ▸ hb ▸ hτ (by simp) (by simp) (Nat.zero_le n)
  have hm (t : ℝ≥0) := (hB.aemeasurable t).aestronglyMeasurable
  have hs (i : ℕ) (hi : i ∈ Finset.range n) : (τ i : ℝ) ∈ Icc (a : ℝ) b := by
    have hi' := (Finset.mem_range.mp hi).le
    constructor
    · exact_mod_cast (ha ▸ hτ (by simp) hi' (Nat.zero_le i))
    · exact_mod_cast (hb ▸ hτ hi' (by simp) hi')
  exact (((hf b ⟨by exact_mod_cast hab, le_rfl⟩).continuous.comp_aestronglyMeasurable (hm b)).sub
    ((hf a ⟨le_rfl, by exact_mod_cast hab⟩).continuous.comp_aestronglyMeasurable (hm a))).sub
      (Finset.aestronglyMeasurable_fun_sum _ fun i hi ↦
        ((hf _ (hs i hi)).continuous_deriv (by norm_num)).comp_aestronglyMeasurable (hm _)
          |>.mul ((hm _).sub (hm _))) |>.sub
    (aestronglyMeasurable_const.mul (Finset.aestronglyMeasurable_fun_sum _ fun i hi ↦
      ((hf _ (hs i hi)).deriv'.continuous_deriv_one).comp_aestronglyMeasurable (hm _)
        |>.mul (((hm _).sub (hm _)).pow 2)))

/-- **Time-dependent Brownian Taylor partition formula.** Subtracting the first two
spatial Taylor sums from the endpoint increment leaves the integral of the time derivative,
in probability along every deterministic vanishing-mesh sequence.

Only the spatial slices must be `C²`; the time derivative and spatial second derivative
are jointly continuous on the closed time horizon. No mixed derivatives, growth bounds,
filtration, or moments of the transformed process are assumed. -/
theorem tendstoInMeasure_sub_sum_taylor_two_timeSpace (hB : IsBrownianReal B P)
    (hf : ∀ t ∈ Icc (a : ℝ) b, ContDiff ℝ 2 (f t))
    (h₂ : ContinuousOn (fun p : ℝ × ℝ ↦ iteratedDeriv 2 (f p.1) p.2)
      (Icc (a : ℝ) b ×ˢ univ))
    (hg : ContinuousOn (Function.uncurry g) (Icc (a : ℝ) b ×ˢ univ))
    (htime : ∀ x t, t ∈ Icc (a : ℝ) b →
      HasDerivWithinAt (fun u ↦ f u x) (g t x) (Icc (a : ℝ) b) t)
    {N : ℕ → ℕ} {τ : ℕ → ℕ → ℝ≥0} {δ : ℕ → ℝ}
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (N k))) (ha : ∀ k, τ k 0 = a)
    (hb : ∀ k, τ k (N k) = b)
    (hmesh : ∀ k i, i < N k → (τ k (i + 1) : ℝ) - τ k i ≤ δ k)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P (fun k ω ↦ f b (B b ω) - f a (B a ω) -
      (∑ i ∈ Finset.range (N k), deriv (f (τ k i)) (B (τ k i) ω) *
        (B (τ k (i + 1)) ω - B (τ k i) ω)) -
      1 / 2 * ∑ i ∈ Finset.range (N k), deriv (deriv (f (τ k i))) (B (τ k i) ω) *
        (B (τ k (i + 1)) ω - B (τ k i) ω) ^ 2) atTop
      (fun ω ↦ ∫ t in (a : ℝ)..b, g t (B t.toNNReal ω)) := by
  let := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hcell (k i : ℕ) (hi : i ≤ N k) : (τ k i : ℝ) ∈ Icc (a : ℝ) b := by
    exact ⟨by exact_mod_cast ha k ▸ hτ k (by simp) hi (Nat.zero_le i),
      by exact_mod_cast hb k ▸ hτ k hi (by simp) hi⟩
  have hspatial := hB.tendstoInMeasure_sum_sub_taylorWithinEval_two_param isCompact_Icc hf h₂
    (grid := fun k (i : Fin (N k + 1)) ↦ τ k i)
    (fun k i j hij ↦ hτ k (by simpa using i.isLt) (by simpa using j.isLt) hij)
    ha hb (fun k i ↦ hmesh k i i.isLt) hδ
    (fun k i ↦ (τ k i : ℝ)) (fun k i ↦ hcell k i i.isLt.le)
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun k ↦
    aestronglyMeasurable_timeSpaceRemainder hB hf (hτ k) (ha k) (hb k))).2
  intro φ hφ
  obtain ⟨ψ, hψ, hlim⟩ := (hspatial.comp hφ.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hB.cont, hlim] with ω hcont hlimω
  have hX : ContinuousOn (fun t : ℝ ↦ B t.toNNReal ω) (Icc (a : ℝ) b) :=
    (hcont.comp continuous_real_toNNReal).continuousOn
  have ht := TauCeti.tendsto_sum_time_increment hX
    (hg.mono (prod_mono_right (subset_univ _))) (fun x _ t ht ↦ htime x t ht)
    (τ := fun k i ↦ (τ k i : ℝ)) (θ := fun k i ↦ (τ k (i + 1) : ℝ))
    (Eventually.of_forall fun k i hi j hj hij ↦ by exact_mod_cast hτ k hi hj hij)
    (Eventually.of_forall fun k ↦ by exact_mod_cast ha k)
    (Eventually.of_forall fun k ↦ by exact_mod_cast hb k)
    (Eventually.of_forall fun k i hi ↦ ⟨by exact_mod_cast hτ k hi.le hi (by omega), le_rfl⟩)
    (Eventually.of_forall hmesh) hδ
  have hsum := hlimω.add (ht.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
  simp only [Pi.zero_apply, zero_add] at hsum
  convert hsum using 1
  funext k
  simp only [Function.comp_apply, TauCeti.taylorWithinEval_univ_two,
    Fin.val_succ, Fin.val_castSucc, Real.toNNReal_coe]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦
    f (τ (φ (ψ k)) i) (B (τ (φ (ψ k)) (i + 1)) ω) -
      (f (τ (φ (ψ k)) i) (B (τ (φ (ψ k)) i) ω) +
        deriv (f (τ (φ (ψ k)) i)) (B (τ (φ (ψ k)) i) ω) *
          (B (τ (φ (ψ k)) (i + 1)) ω - B (τ (φ (ψ k)) i) ω) +
        1 / 2 * deriv (deriv (f (τ (φ (ψ k)) i))) (B (τ (φ (ψ k)) i) ω) *
          (B (τ (φ (ψ k)) (i + 1)) ω - B (τ (φ (ψ k)) i) ω) ^ 2))]
  have htel := Finset.sum_range_sub
    (fun i ↦ f (τ (φ (ψ k)) i) (B (τ (φ (ψ k)) i) ω)) (N (φ (ψ k)))
  rw [ha, hb] at htel
  rw [← htel, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end ProbabilityTheory.IsBrownianReal
