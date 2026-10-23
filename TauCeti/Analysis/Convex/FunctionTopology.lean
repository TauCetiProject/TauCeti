/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.FunctionTopology
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Order.Field

/-!
# Limits of convex functions

A pointwise limit, on a set `s`, of functions that are eventually convex on `s` is convex on `s`.
This is the closedness of the set of convex functions (`isClosed_setOfPred_convexOn`) applied to
functions that are only known to converge on `s`.

A convex function on `(0, ∞)` bounded above by `L` stays convex when extended by the value `L` at
`0` (`ConvexOn.apply_mul_le_of_forall_le`), as the limit of convex combinations approaching `0`.
-/

public section

open Set Filter

open scoped Topology

namespace TauCeti

variable {𝕜 α β ι : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [PartialOrder β]
  [TopologicalSpace β] [OrderClosedTopology β] [AddCommMonoid α] [AddCommMonoid β]
  [SMul 𝕜 α] [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] [ContinuousAdd β]

/-- **A pointwise limit of convex functions is convex.** If the functions `F i` are eventually
convex on `s` and converge to `f` at every point of `s`, then `f` is convex on `s`. -/
theorem convexOn_of_tendsto {l : Filter ι} [l.NeBot] {F : ι → α → β} {f : α → β} {s : Set α}
    (hF : ∀ᶠ i in l, ConvexOn 𝕜 s (F i))
    (hf : ∀ x ∈ s, Tendsto (fun i => F i x) l (𝓝 (f x))) : ConvexOn 𝕜 s f := by
  classical
  -- Replace `F i` by `f` off `s`; the modified functions converge to `f` everywhere.
  have hlim : Tendsto (fun i => s.piecewise (F i) f) l (𝓝 f) := tendsto_pi_nhds.2 fun x => by
    by_cases hx : x ∈ s
    · simpa only [s.piecewise_eq_of_mem _ _ hx] using hf x hx
    · simpa only [s.piecewise_eq_of_notMem _ _ hx] using tendsto_const_nhds
  exact isClosed_setOfPred_convexOn.mem_of_tendsto hlim
    (hF.mono fun i hi => hi.congr fun x hx => (s.piecewise_eq_of_mem _ _ hx).symm)

end TauCeti

/-- A convex function `φ` on `(0, ∞)` bounded above by `L` satisfies `φ (b x) ≤ b φ x + (1 - b) L`
for `x > 0` and `0 < b ≤ 1`: extending `φ` by the value `L` at `0` keeps it convex on `[0, ∞)`.
For `φ(s) = sⁿ U(s⁻ⁿ)` nonincreasing, the best such bound is the recession constant of `U`, since
`U(r) / r = φ(r^{-1/n})`. -/
theorem ConvexOn.apply_mul_le_of_forall_le {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Ioi 0) φ)
    {L : ℝ} (hL : ∀ s ∈ Ioi (0 : ℝ), φ s ≤ L) {x b : ℝ} (hx : 0 < x) (hb₀ : 0 < b)
    (hb₁ : b ≤ 1) : φ (b * x) ≤ b * φ x + (1 - b) * L := by
  -- Write `b x` as a convex combination of `x` and `ε x` and let `ε → 0⁺`.
  set F : ℝ → ℝ := fun ε => (b - ε) / (1 - ε) * φ x + (1 - (b - ε) / (1 - ε)) * L
  have hF : Tendsto F (𝓝[>] 0) (𝓝 (b * φ x + (1 - b) * L)) := by
    have : ContinuousAt F 0 := by fun_prop (disch := norm_num)
    simpa [F] using this.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hF ?_
  filter_upwards [Ioo_mem_nhdsGT hb₀] with ε hε
  have hε1 : ε < 1 := hε.2.trans_le hb₁
  have hl₀ : 0 ≤ (b - ε) / (1 - ε) := div_nonneg (by linarith [hε.2]) (by linarith)
  have hl₁ : 0 ≤ 1 - (b - ε) / (1 - ε) := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have hne : 1 - ε ≠ 0 := by linarith
  have := hφ.2 (mem_Ioi.2 hx) (mem_Ioi.2 (mul_pos hε.1 hx)) hl₀ hl₁ (by ring)
  simp only [smul_eq_mul] at this
  rw [show (b - ε) / (1 - ε) * x + (1 - (b - ε) / (1 - ε)) * (ε * x) = b * x by
    field_simp; ring] at this
  have hεL := mul_le_mul_of_nonneg_left (hL _ (mul_pos hε.1 hx)) hl₁
  simp only [F]
  linarith
