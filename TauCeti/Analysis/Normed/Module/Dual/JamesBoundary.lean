/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import TauCeti.Analysis.Convex.Simons
import TauCeti.Analysis.Normed.Module.Dual.Basic
import TauCeti.Topology.Algebra.Module.WeakSpace.Basic

/-!
# James boundaries: Simons's inequality and the Rainwater–Simons theorem

Let `Y` be a real or complex Banach space. A set `B` of functionals in the closed unit ball of
the dual is a *James boundary* when every `y : Y` has some `b ∈ B` with `re (b y) = ‖y‖`.
By Hahn–Banach the whole dual unit ball is a James boundary; when every functional on a normed
space `E` attains its norm, the canonical image of the unit ball of `E` is a James boundary of
`StrongDual 𝕜 E`. We state the boundary property as two hypotheses,
`hB₁ : ∀ b ∈ B, ‖b‖ ≤ 1` and `hB : ∀ y, ∃ b ∈ B, re (b y) = ‖y‖`.

For a bounded sequence `u` in `Y` and a James boundary `B`, we prove:

* **Simons's inequality** (`TauCeti.exists_mem_frequently_lt_re_apply_of_forall_le_norm`): if every
  finite convex combination of the `u n` has norm at least `r`, then for every `r' < r` some
  `b ∈ B` has `r' < re (b (u n))` for infinitely many `n`. That is,
  `sup_{b ∈ B} limsup_n re (b (u n)) ≥ inf {‖y‖ : y ∈ conv {u n}}`.
* **The sup-limsup theorem**
  (`TauCeti.exists_mem_frequently_lt_re_apply_of_frequently_lt_re_apply`):
  `sup_{b ∈ B} limsup_n re (b (u n)) = sup_{‖φ‖ ≤ 1} limsup_n re (φ (u n))`.
* **The Rainwater–Simons theorem** (`TauCeti.tendsto_toWeakSpace_of_forall_mem_tendsto`): if
  `b (u n) → b y` for every `b ∈ B`, then `u n → y` weakly.

Completeness of `Y` makes countable convex combinations of the bounded sequence converge, so that
Simons's inequality `TauCeti.exists_frequently_sub_lt_of_isMaxOn_tsum` applies to the
functions `b ↦ re (b (u n))` on `B`.

## References

* J. Rainwater, *Weak convergence of bounded sequences*, Proc. Amer. Math. Soc. **14** (1963),
  999.
* S. Simons, *A convergence theorem with boundary*, Pacific J. Math. **40** (1972), 703–708.
* M. Fabian, P. Habala, P. Hájek, V. Montesinos and V. Zizler, *Banach Space Theory*,
  CMS Books in Mathematics, Springer (2011), Chapter 3.
-/

public section

open Bornology Filter Finset RCLike Set Topology

namespace TauCeti

variable {𝕜 Y : Type*} [RCLike 𝕜] [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A lower bound on the norms of finite convex combinations of a bounded sequence passes to its
countable convex combinations. -/
theorem le_norm_tsum_ofReal_smul [CompleteSpace Y] {u : ℕ → Y} {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C)
    {r : ℝ}
    (hr : ∀ (s : Finset ℕ) (w : ℕ → ℝ), (∀ n, 0 ≤ w n) → ∑ n ∈ s, w n = 1 →
      r ≤ ‖∑ n ∈ s, (w n : 𝕜) • u n‖)
    {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n) (hw : HasSum w 1) :
    r ≤ ‖∑' n, (w n : 𝕜) • u n‖ := by
  set m : ℕ → ℝ := fun N ↦ ∑ n ∈ range N, w n
  have hm : Tendsto m atTop (𝓝 1) := hw.tendsto_sum_nat
  have hsum : Summable fun n ↦ (w n : 𝕜) • u n :=
    Summable.of_norm_bounded (hw.summable.mul_right C) fun n ↦ by
      rw [norm_smul, norm_ofReal, abs_of_nonneg (hw0 n)]
      exact mul_le_mul_of_nonneg_left (hu n) (hw0 n)
  have hs : Tendsto (fun N ↦ ‖∑ n ∈ range N, (w n : 𝕜) • u n‖) atTop
      (𝓝 ‖∑' n, (w n : 𝕜) • u n‖) :=
    hsum.hasSum.tendsto_sum_nat.norm
  have hle : ∀ᶠ N in atTop, r * m N ≤ ‖∑ n ∈ range N, (w n : 𝕜) • u n‖ := by
    filter_upwards [hm.eventually (lt_mem_nhds one_pos)] with N hN
    have h := hr (range N) (fun n ↦ w n / m N) (fun n ↦ div_nonneg (hw0 n) hN.le)
      (by simp_rw [div_eq_mul_inv]; rw [← sum_mul, mul_inv_cancel₀ hN.ne'])
    have heq : ∑ n ∈ range N, ((w n / m N : ℝ) : 𝕜) • u n =
        ((m N)⁻¹ : 𝕜) • ∑ n ∈ range N, (w n : 𝕜) • u n := by
      simp [smul_sum, smul_smul, div_eq_mul_inv, mul_comm]
    rw [heq, norm_smul] at h
    simpa [abs_of_pos hN, le_inv_mul_iff₀' hN] using h
  simpa using le_of_tendsto_of_tendsto (hm.const_mul r) hs hle

/-- **Simons's inequality** for a James boundary. Let `B` be a set of functionals of norm at most
`1` on a Banach space `Y` such that every `y` has some `b ∈ B` with `re (b y) = ‖y‖`. If every
finite convex combination of a bounded sequence `u` has norm at least `r`, then for every
`r' < r` some `b ∈ B` has `r' < re (b (u n))` for infinitely many `n`. -/
theorem exists_mem_frequently_lt_re_apply_of_forall_le_norm [CompleteSpace Y]
    {B : Set (StrongDual 𝕜 Y)} (hB₁ : ∀ b ∈ B, ‖b‖ ≤ 1) (hB : ∀ y, ∃ b ∈ B, re (b y) = ‖y‖)
    {u : ℕ → Y} (hu : IsBounded (range u)) {r r' : ℝ}
    (hr : ∀ (s : Finset ℕ) (w : ℕ → ℝ), (∀ n, 0 ≤ w n) → ∑ n ∈ s, w n = 1 →
      r ≤ ‖∑ n ∈ s, (w n : 𝕜) • u n‖)
    (hr' : r' < r) :
    ∃ b ∈ B, ∃ᶠ n in atTop, r' < re (b (u n)) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hu
  have hu' (n : ℕ) : ‖u n‖ ≤ C := hC _ (mem_range_self n)
  -- The values of a countable convex combination under a functional.
  have hval (w : ℕ → ℝ) (hw : HasSum w 1) (b : StrongDual 𝕜 Y) :
      ∑' n, w n * re (b (u n)) = re (b (∑' n, (w n : 𝕜) • u n)) :=
    (b.hasSum_mul_re_apply hw.summable hu').tsum_eq
  have hM (n : ℕ) (b : StrongDual 𝕜 Y) (hb : b ∈ B) : |re (b (u n))| ≤ C :=
    (abs_re_le_norm _).trans ((b.norm_apply_le_of_norm_le_one (hB₁ b hb) _).trans (hu' n))
  -- Every countable convex combination `y` attains its maximum on `B` where `re (b y) = ‖y‖`.
  obtain ⟨b, hbB, hb⟩ := exists_frequently_sub_lt_of_isMaxOn_tsum (s := B)
    (x := fun n b ↦ re (b (u n))) (c := r) hM
    (fun w _ hw ↦ by
      obtain ⟨b, hbB, hb⟩ := hB (∑' n, (w n : 𝕜) • u n)
      refine ⟨b, hbB, fun b' hb' ↦ ?_⟩
      simp only [hval w hw, hb]
      exact b'.re_apply_le_norm_of_norm_le_one (hB₁ b' hb') _)
    (fun w hw0 hw ↦ by
      obtain ⟨b, hbB, hb⟩ := hB (∑' n, (w n : 𝕜) • u n)
      refine ⟨b, hbB, ?_⟩
      simp only [hval w hw, hb]
      exact le_norm_tsum_ofReal_smul hu' hr hw0 hw)
    (sub_pos.2 hr')
  exact ⟨b, hbB, by simpa using hb⟩

/-- **The sup-limsup theorem.** For a James boundary `B` of a Banach space `Y` and a bounded
sequence `u`, if some functional `φ` of norm at most `1` has `c < re (φ (u n))` for infinitely
many `n`, then for every `c' < c` some `b ∈ B` has `c' < re (b (u n))` for infinitely many `n`.
That is, `sup_{b ∈ B} limsup_n re (b (u n)) = sup_{‖φ‖ ≤ 1} limsup_n re (φ (u n))`. -/
theorem exists_mem_frequently_lt_re_apply_of_frequently_lt_re_apply [CompleteSpace Y]
    {B : Set (StrongDual 𝕜 Y)} (hB₁ : ∀ b ∈ B, ‖b‖ ≤ 1) (hB : ∀ y, ∃ b ∈ B, re (b y) = ‖y‖)
    {u : ℕ → Y} (hu : IsBounded (range u)) {φ : StrongDual 𝕜 Y} (hφ : ‖φ‖ ≤ 1) {c c' : ℝ}
    (hc : ∃ᶠ n in atTop, c < re (φ (u n))) (hc' : c' < c) :
    ∃ b ∈ B, ∃ᶠ n in atTop, c' < re (b (u n)) := by
  obtain ⟨σ, hσ, hσc⟩ := extraction_of_frequently_atTop hc
  have hr (s : Finset ℕ) (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (hw : ∑ n ∈ s, w n = 1) :
      c ≤ ‖∑ n ∈ s, (w n : 𝕜) • u (σ n)‖ := by
    have hre : re (φ (∑ n ∈ s, (w n : 𝕜) • u (σ n))) = ∑ n ∈ s, w n * re (φ (u (σ n))) := by
      simp [map_sum]
    calc c = ∑ n ∈ s, w n * c := by rw [← sum_mul, hw, one_mul]
      _ ≤ ∑ n ∈ s, w n * re (φ (u (σ n))) :=
          sum_le_sum fun n _ ↦ mul_le_mul_of_nonneg_left (hσc n).le (hw0 n)
      _ = re (φ (∑ n ∈ s, (w n : 𝕜) • u (σ n))) := hre.symm
      _ ≤ ‖∑ n ∈ s, (w n : 𝕜) • u (σ n)‖ := φ.re_apply_le_norm_of_norm_le_one hφ _
  obtain ⟨b, hbB, hb⟩ := exists_mem_frequently_lt_re_apply_of_forall_le_norm hB₁ hB
    (hu.subset (range_comp_subset_range σ u)) hr hc'
  exact ⟨b, hbB, hσ.tendsto_atTop.frequently hb⟩

/-- **The Rainwater–Simons theorem.** Let `B` be a James boundary of a Banach space `Y`. A
bounded sequence `u` with `b (u n) → b y` for every `b ∈ B` converges weakly to `y`. -/
theorem tendsto_toWeakSpace_of_forall_mem_tendsto [CompleteSpace Y]
    {B : Set (StrongDual 𝕜 Y)} (hB₁ : ∀ b ∈ B, ‖b‖ ≤ 1) (hB : ∀ y, ∃ b ∈ B, re (b y) = ‖y‖)
    {u : ℕ → Y} (hu : IsBounded (range u)) {y : Y}
    (h : ∀ b ∈ B, Tendsto (fun n ↦ b (u n)) atTop (𝓝 (b y))) :
    Tendsto (fun n ↦ toWeakSpace 𝕜 Y (u n)) atTop (𝓝 (toWeakSpace 𝕜 Y y)) := by
  set v : ℕ → Y := fun n ↦ u n - y
  have hv : IsBounded (range v) := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hu
    refine isBounded_iff_forall_norm_le.2 ⟨C + ‖y‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (norm_sub_le _ _).trans (by gcongr; exact hC _ (mem_range_self n))
  have hBv (b : StrongDual 𝕜 Y) (hb : b ∈ B) : Tendsto (fun n ↦ re (b (v n))) atTop (𝓝 0) := by
    have := ((continuous_re.tendsto _).comp (tendsto_sub_nhds_zero_iff.2 (h b hb)))
    simpa [v, Function.comp_def] using this
  -- Upper bounds of the real parts, first for functionals of norm at most one.
  have hupper₁ (ψ : StrongDual 𝕜 Y) (hψ : ‖ψ‖ ≤ 1) (c : ℝ) (hc : 0 < c) :
      ∀ᶠ n in atTop, re (ψ (v n)) ≤ c := by
    by_contra hnot
    rw [not_eventually] at hnot
    obtain ⟨b, hbB, hb⟩ := exists_mem_frequently_lt_re_apply_of_frequently_lt_re_apply hB₁ hB hv
      hψ (hnot.mono fun n hn ↦ not_le.1 hn) (half_lt_self hc)
    obtain ⟨n, hn, hn'⟩ := (hb.and_eventually ((hBv b hbB).eventually (gt_mem_nhds
      (half_pos hc)))).exists
    exact (hn.trans hn').false
  have hupper (ψ : StrongDual 𝕜 Y) (c : ℝ) (hc : 0 < c) : ∀ᶠ n in atTop, re (ψ (v n)) ≤ c := by
    have hpos : 0 < ‖ψ‖ + 1 := by positivity
    have hψ : ‖(((‖ψ‖ + 1)⁻¹ : ℝ) : 𝕜) • ψ‖ ≤ 1 := by
      rw [norm_smul, norm_ofReal, abs_of_pos (inv_pos.2 hpos), inv_mul_le_iff₀ hpos]
      linarith
    filter_upwards [hupper₁ _ hψ (c / (‖ψ‖ + 1)) (div_pos hc hpos)] with n hn
    simp only [smul_apply, smul_eq_mul, re_ofReal_mul] at hn
    field_simp at hn
    exact hn
  have hre (ψ : StrongDual 𝕜 Y) : Tendsto (fun n ↦ re (ψ (v n))) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
    · filter_upwards [hupper (-ψ) (-a / 2) (by linarith)] with n hn
      simp only [neg_apply, map_neg] at hn
      linarith
    · filter_upwards [hupper ψ (a / 2) (by linarith)] with n hn
      linarith
  refine tendsto_toWeakSpace_iff_forall_re_eval_tendsto.2 fun φ ↦ ?_
  simpa [v, map_sub, tendsto_sub_nhds_zero_iff] using hre φ

end TauCeti
