/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Sequences
import TauCeti.Analysis.Convex.Simons
import TauCeti.Analysis.Normed.Module.Dual.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Norm-attaining functionals and reflexivity

A continuous linear functional `f` on a normed space *attains its norm* if `‖f x‖ = ‖f‖` for
some `x` in the closed unit ball. Every functional on a reflexive space attains its norm, since
the closed unit ball is weakly compact. James's theorem is the converse for Banach spaces. This
file proves it for separable Banach spaces.

The engine is Simons' inequality (`TauCeti.exists_frequently_sub_lt_of_isMaxOn_tsum`), applied
to the real parts of a bounded sequence of functionals on the closed unit ball. If every
functional attains its norm, every σ-convex combination of such a sequence does too, and Simons'
inequality yields the *Rainwater–Simons theorem*: a bounded sequence of functionals which
converges weak-star also converges weakly, that is, against every element of the bidual
(`TauCeti.tendsto_toWeakSpace_of_forall_exists_norm_apply_eq_norm`).

For a separable space the dual closed unit ball is weak-star sequentially compact, so it is then
weakly sequentially compact, and by Eberlein–Šmulian weakly compact. The dual is therefore
reflexive, and so is the space when it is complete
(`TauCeti.surjective_inclusionInDoubleDual_iff_forall_exists_norm_apply_eq_norm`).

## Main statements

* `TauCeti.exists_norm_apply_eq_norm_of_surjective_inclusionInDoubleDual`: on a reflexive space
  every functional attains its norm.
* `TauCeti.tendsto_toWeakSpace_of_forall_exists_norm_apply_eq_norm`: the Rainwater–Simons
  theorem.
* `TauCeti.surjective_inclusionInDoubleDual_iff_forall_exists_norm_apply_eq_norm`: James's
  theorem for separable Banach spaces.

## References

* R. C. James, *Reflexivity and the supremum of linear functionals*, Ann. of Math. **66**
  (1957), 159–169.
* J. Rainwater, *Weak convergence of bounded sequences*, Proc. Amer. Math. Soc. **14** (1963),
  999.
* S. Simons, *A convergence theorem with boundary*, Pacific J. Math. **40** (1972), 703–708.
-/

public section

open Bornology Filter Function Metric NormedSpace RCLike Set Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜]

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Every continuous linear functional on a reflexive space attains its norm on the closed unit
ball. -/
theorem exists_norm_apply_eq_norm_of_surjective_inclusionInDoubleDual
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) (f : StrongDual 𝕜 E) :
    ∃ x, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖ := by
  -- `f` is weakly continuous, so `‖f‖` has a maximum on the weakly compact closed unit ball.
  have hcont : Continuous fun z : WeakSpace 𝕜 E ↦ ‖f ((toWeakSpace 𝕜 E).symm z)‖ :=
    (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip f).norm
  obtain ⟨_, ⟨x, hx, rfl⟩, hmax⟩ := (isCompact_toWeakSpace_closedBall hE 0 1).exists_isMaxOn
    ⟨_, 0, mem_closedBall_self zero_le_one, rfl⟩ hcont.continuousOn
  rw [mem_closedBall_zero_iff] at hx
  refine ⟨x, hx, le_antisymm (f.unit_le_opNorm x hx)
    (f.opNorm_le_of_unit_norm (norm_nonneg _) fun y hy ↦ ?_)⟩
  have := hmax ⟨y, mem_closedBall_zero_iff.2 hy.le, rfl⟩
  simpa using this

/-- Simons' inequality on the closed unit ball. If every functional on `E` attains its norm, and
the real part of a bidual element `Ψ` is bounded below by `θ > 0` on a bounded sequence `h k` of
functionals, then some vector `x` keeps `re (h k x)` above a positive constant for infinitely
many `k`. -/
private lemma exists_frequently_lt_re_apply
    (hE : ∀ f : StrongDual 𝕜 E, ∃ x, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖) {h : ℕ → StrongDual 𝕜 E} {C : ℝ}
    (hC : ∀ k, ‖h k‖ ≤ C) (Ψ : StrongDual 𝕜 (StrongDual 𝕜 E)) {θ : ℝ} (hθ : 0 < θ)
    (hΨ : ∀ k, θ < re (Ψ (h k))) : ∃ c > 0, ∃ x : E, ∃ᶠ k in atTop, c < re (h k x) := by
  have hΨ0 : 0 < ‖Ψ‖ := by
    refine (norm_nonneg Ψ).lt_of_ne fun h0 ↦ ?_
    have := ((hΨ 0).trans_le (re_le_norm _)).trans_le (Ψ.le_opNorm (h 0))
    rw [← h0, zero_mul] at this
    linarith
  -- The real parts of the `h k` commute with σ-convex combinations of them.
  have happly : ∀ w : ℕ → ℝ, HasSum w 1 → ∀ b : E,
      ∑' k, w k * re (h k b) = re ((∑' k, (w k : 𝕜) • h k) b) := fun w hw b ↦ by
    simpa only [ContinuousLinearMap.apply_apply] using
      (StrongDual.hasSum_mul_re_apply (ContinuousLinearMap.apply 𝕜 𝕜 b) hw.summable hC).tsum_eq
  -- Every σ-convex combination `H` of the `h k` has `θ ≤ re (Ψ H) ≤ ‖Ψ‖ ‖H‖`.
  have hHnorm : ∀ w : ℕ → ℝ, (∀ k, 0 ≤ w k) → HasSum w 1 →
      θ / ‖Ψ‖ ≤ ‖∑' k, (w k : 𝕜) • h k‖ := fun w hw0 hw ↦ by
    have hθle : θ ≤ re (Ψ (∑' k, (w k : 𝕜) • h k)) := by
      simpa only [one_mul] using hasSum_le (fun k ↦ mul_le_mul_of_nonneg_left (hΨ k).le (hw0 k))
        (hw.mul_right θ) (Ψ.hasSum_mul_re_apply hw.summable hC)
    rw [div_le_iff₀ hΨ0, mul_comm]
    exact hθle.trans ((re_le_norm _).trans (Ψ.le_opNorm _))
  -- Simons' inequality for the real parts of the `h k` on the closed unit ball, where every
  -- σ-convex combination attains its norm in real part.
  have hM : ∀ k, ∀ b ∈ closedBall (0 : E) 1, |re (h k b)| ≤ C := fun k b hb ↦
    (abs_re_le_norm _).trans (((h k).le_opNorm b).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (mem_closedBall_zero_iff.1 hb)).trans (hC k)))
  have hmax : ∀ w : ℕ → ℝ, (∀ k, 0 ≤ w k) → HasSum w 1 → ∃ b ∈ closedBall (0 : E) 1,
      IsMaxOn (fun b ↦ ∑' k, w k * re (h k b)) (closedBall 0 1) b := fun w _ hw ↦ by
    simpa only [happly w hw] using
      StrongDual.exists_isMaxOn_re_apply_closedBall_iff.2 (hE (∑' k, (w k : 𝕜) • h k))
  have hcle : ∀ w : ℕ → ℝ, (∀ k, 0 ≤ w k) → HasSum w 1 → ∃ b ∈ closedBall (0 : E) 1,
      θ / ‖Ψ‖ ≤ ∑' k, w k * re (h k b) := fun w hw0 hw ↦ by
    obtain ⟨y, hy, hyre⟩ :=
      StrongDual.exists_norm_le_one_re_apply_eq_norm_iff.2 (hE (∑' k, (w k : 𝕜) • h k))
    exact ⟨y, mem_closedBall_zero_iff.2 hy, by rw [happly w hw, hyre]; exact hHnorm w hw0 hw⟩
  have hc : 0 < θ / ‖Ψ‖ := by positivity
  obtain ⟨b, -, hfreq⟩ := exists_frequently_sub_lt_of_isMaxOn_tsum hM hmax hcle (half_pos hc)
  exact ⟨θ / ‖Ψ‖ - θ / ‖Ψ‖ / 2, by linarith, b, hfreq⟩

/-- **The Rainwater–Simons theorem.** If every continuous linear functional on `E` attains its
norm on the closed unit ball, then every bounded sequence in the dual which converges weak-star
converges weakly, that is, against every element of the bidual. -/
theorem tendsto_toWeakSpace_of_forall_exists_norm_apply_eq_norm
    (hE : ∀ f : StrongDual 𝕜 E, ∃ x, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖) {f : ℕ → StrongDual 𝕜 E}
    {g : StrongDual 𝕜 E} (hbdd : IsBounded (range f))
    (hlim : ∀ x, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ toWeakSpace 𝕜 (StrongDual 𝕜 E) (f n)) atTop
      (𝓝 (toWeakSpace 𝕜 (StrongDual 𝕜 E) g)) := by
  rw [tendsto_toWeakSpace_iff_forall_eval_tendsto]
  intro Φ
  by_contra hΦ
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hbdd
  have hfC : ∀ n, ‖f n‖ ≤ C := fun n ↦ hC _ (mem_range_self n)
  set u : ℕ → 𝕜 := fun n ↦ Φ (f n - g) with hu
  -- Along a subsequence, `Φ (f n - g)` stays away from zero and converges to some `L ≠ 0`.
  obtain ⟨ε, hε, hεu⟩ : ∃ ε > 0, ∃ᶠ n in atTop, ε ≤ ‖u n‖ := by
    have hu0 : ¬ Tendsto u atTop (𝓝 0) := fun h ↦ hΦ (by
      simpa [hu, sub_eq_add_neg] using (h.add_const (Φ g)))
    rw [Metric.tendsto_atTop] at hu0
    push Not at hu0
    obtain ⟨ε, hε, hN⟩ := hu0
    exact ⟨ε, hε, frequently_atTop.2 fun N ↦ by simpa using hN N⟩
  obtain ⟨φ₁, hφ₁, hφ₁ε⟩ := extraction_of_frequently_atTop hεu
  have huR : ∀ n, u n ∈ closedBall (0 : 𝕜) (‖Φ‖ * (C + ‖g‖)) := fun n ↦ by
    rw [mem_closedBall_zero_iff]
    exact (Φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((norm_sub_le _ _).trans (by linarith [hfC n])) (norm_nonneg Φ))
  obtain ⟨L, -, φ₂, hφ₂, hL⟩ := tendsto_subseq_of_bounded isBounded_closedBall
    fun k ↦ huR (φ₁ k)
  have hLε : ε ≤ ‖L‖ := ge_of_tendsto (hL.norm) (Eventually.of_forall fun k ↦ hφ₁ε (φ₂ k))
  have hL0 : L ≠ 0 := norm_pos_iff.1 (hε.trans_le hLε)
  -- Rotate `Φ` so that its real part is eventually above `‖L‖ / 2` on `f n - g`.
  obtain ⟨a, -, haL⟩ := exists_norm_eq_mul_self L
  set Ψ : StrongDual 𝕜 (StrongDual 𝕜 E) := a • Φ with hΨ
  have hΨlim : Tendsto (fun k ↦ re (Ψ (f (φ₁ (φ₂ k)) - g))) atTop (𝓝 ‖L‖) := by
    have := (RCLike.continuous_re.tendsto _).comp (hL.const_mul a)
    simpa only [← haL, RCLike.ofReal_re, hΨ, smul_apply, smul_eq_mul, hu, comp_def] using this
  obtain ⟨K, hK⟩ := eventually_atTop.1
    (hΨlim.eventually_const_lt (half_lt_self (norm_pos_iff.2 hL0)))
  -- Simons' inequality gives `x` with `re ((f n - g) x)` frequently large along the
  -- subsequence, against weak-star convergence.
  obtain ⟨c, hc, x, hfreq⟩ := exists_frequently_lt_re_apply hE
    (h := fun k ↦ f (φ₁ (φ₂ (k + K))) - g) (C := C + ‖g‖)
    (fun k ↦ (norm_sub_le _ _).trans (by linarith [hfC (φ₁ (φ₂ (k + K)))])) Ψ
    (half_pos (norm_pos_iff.2 hL0)) fun k ↦ hK (k + K) (by omega)
  have hz : Tendsto (fun k ↦ re ((f (φ₁ (φ₂ (k + K))) - g) x)) atTop (𝓝 0) := by
    have hsub : Tendsto (fun k ↦ φ₁ (φ₂ (k + K))) atTop atTop :=
      (hφ₁.comp hφ₂).tendsto_atTop.comp (tendsto_add_atTop_nat K)
    have := (RCLike.continuous_re.tendsto _).comp (((hlim x).comp hsub).sub_const (g x))
    simpa only [sub_self, map_zero, sub_apply, comp_def] using this
  obtain ⟨k, hk₁, hk₂⟩ := (hfreq.and_eventually (hz.eventually (gt_mem_nhds hc))).exists
  linarith

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **James's theorem for separable spaces.** A separable Banach space on which every continuous
linear functional attains its norm on the closed unit ball is reflexive. -/
theorem surjective_inclusionInDoubleDual_of_forall_exists_norm_apply_eq_norm [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (hE : ∀ f : StrongDual 𝕜 E, ∃ x, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖) :
    Surjective (inclusionInDoubleDual 𝕜 E) := by
  -- The dual closed unit ball is weakly sequentially compact: extract a weak-star convergent
  -- subsequence by separability, which converges weakly by the Rainwater–Simons theorem.
  refine surjective_inclusionInDoubleDual_of_strongDual
    (surjective_inclusionInDoubleDual_of_isCompact_toWeakSpace_closedBall
      (isCompact_toWeakSpace_iff_isSeqCompact.2 ?_))
  rintro u hu
  choose v hv hvu using hu
  obtain ⟨φ, hφ, ψ, hψ, hlim⟩ := WeakDual.isSeqCompact_closedBall (𝕜 := 𝕜) (E := E) 0 1
    (x := fun n ↦ StrongDual.toWeakDual (v n)) fun n ↦ by simpa using hv n
  refine ⟨toWeakSpace 𝕜 _ (WeakDual.toStrongDual φ), ⟨_, hφ, rfl⟩, ψ, hψ, ?_⟩
  have := tendsto_toWeakSpace_of_forall_exists_norm_apply_eq_norm hE (f := fun n ↦ v (ψ n))
    (g := WeakDual.toStrongDual φ)
    (isBounded_closedBall.subset (range_subset_iff.2 fun n ↦ hv (ψ n))) fun x ↦ by
      simpa [comp_def] using ((WeakDual.eval_continuous x).tendsto φ).comp hlim
  simpa [comp_def, ← hvu] using this

/-- **James's theorem for separable spaces.** A separable Banach space is reflexive exactly when
every continuous linear functional attains its norm on the closed unit ball. -/
theorem surjective_inclusionInDoubleDual_iff_forall_exists_norm_apply_eq_norm [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] :
    Surjective (inclusionInDoubleDual 𝕜 E) ↔
      ∀ f : StrongDual 𝕜 E, ∃ x, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖ :=
  ⟨exists_norm_apply_eq_norm_of_surjective_inclusionInDoubleDual,
    surjective_inclusionInDoubleDual_of_forall_exists_norm_apply_eq_norm⟩

end Normed

end TauCeti
