/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.HittingTime
public import TauCeti.Topology.Order.Cadlag
import TauCeti.Topology.Order.Monotone

/-!
# Deterministic simple counting paths

`TauCeti.Probability.IsSimpleCountingPath` packages the pathwise regularity of a standard counting
trajectory `f : ℝ≥0 → ℕ`: it starts at `0`, is monotone and right-continuous, and has jumps from the
left of size at most `1` at every positive time. From these four properties it follows that `f` is
càdlàg, continuous at `0`, has only finitely many discontinuities on each bounded interval `[0, T]`,
satisfies `leftLim f t + 1 = f t` at every discontinuity, and attains each level `c` at any finite
first hitting time of `Set.Ici c`, which then strictly precedes the hit of `c + 1` (and of any
higher level `c₂ > c`).

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter I, §3.
* O. Kallenberg, *Foundations of Modern Probability*, third edition, Springer, 2021, Theorem 15.2.
-/

public section

open Filter Function MeasureTheory Set
open scoped NNReal Topology

namespace TauCeti.Probability

/-- A trajectory `f : ℝ≥0 → ℕ` is a **simple counting path** if it starts at `0`, is monotone and
right-continuous, and jumps from the left by at most `1` at every positive time. -/
structure IsSimpleCountingPath (f : ℝ≥0 → ℕ) : Prop where
  /-- The count at time `0` is `0`. -/
  apply_zero : f 0 = 0
  /-- The count is nondecreasing in time. -/
  monotone : Monotone f
  /-- The count is right-continuous at every time. -/
  isRightContinuous : IsRightContinuous f
  /-- At every positive time `t`, some strictly earlier time `s < t` satisfies `f t ≤ f s + 1`. -/
  le_add_one ⦃t : ℝ≥0⦄ : 0 < t → ∃ s < t, f t ≤ f s + 1

namespace IsSimpleCountingPath

/-- The identically zero path is a simple counting path. -/
@[simp]
theorem zero : IsSimpleCountingPath 0 where
  apply_zero := rfl
  monotone := monotone_const
  isRightContinuous _ := tendsto_const_nhds
  le_add_one _ ht := ⟨0, ht, by simp⟩

/-- A constant zero lambda path is a simple counting path. -/
@[simp]
theorem fun_zero : IsSimpleCountingPath fun _ ↦ 0 :=
  zero

/-- Every simple counting path is càdlàg. -/
theorem isCadlag {f : ℝ≥0 → ℕ} (hf : IsSimpleCountingPath f) : IsCadlag f :=
  hf.monotone.isCadlag hf.isRightContinuous

/-- Coercing a simple counting path to `ℝ` preserves the càdlàg property. -/
theorem isCadlag_real {f : ℝ≥0 → ℕ} (hf : IsSimpleCountingPath f) :
    IsCadlag fun t ↦ (f t : ℝ) := by
  have hc : Continuous (Nat.cast : ℕ → ℝ) := continuous_of_discreteTopology
  have hmono : Monotone fun t ↦ (f t : ℝ) := fun _ _ h ↦ Nat.cast_le.mpr (hf.monotone h)
  exact hmono.isCadlag fun t ↦ hc.continuousAt.tendsto.comp (hf.isRightContinuous t)

/-- A simple counting path is continuous at `0`. -/
theorem continuousAt_zero {f : ℝ≥0 → ℕ} (hf : IsSimpleCountingPath f) : ContinuousAt f 0 :=
  (hf.isRightContinuous 0).continuousAt_of_isBot fun _ ↦ zero_le

/-- A simple counting path has only finitely many discontinuities on each interval `[0, T]`. -/
theorem finite_Iic_not_continuousAt {f : ℝ≥0 → ℕ} (hf : IsSimpleCountingPath f) (T : ℝ≥0) :
    {t ∈ Iic T | ¬ ContinuousAt f t}.Finite := by
  have hIic : (Iic T : Set ℝ≥0) = Icc 0 T := by
    ext t
    simp
  rw [hIic]
  exact hf.monotone.finite_Icc_not_continuousAt 0 T

/-- At every discontinuity of a simple counting path, its left limit is one below its current
value. Positivity of `t` is automatic because a simple counting path is continuous at `0`. -/
theorem leftLim_add_one_eq_of_not_continuousAt {f : ℝ≥0 → ℕ} (hf : IsSimpleCountingPath f)
    {t : ℝ≥0} (ht : ¬ ContinuousAt f t) :
    leftLim f t + 1 = f t := by
  have ht0 : 0 < t := pos_iff_ne_zero.mpr fun h ↦ ht (h ▸ hf.continuousAt_zero)
  exact hf.monotone.leftLim_add_one_eq_of_not_continuousAt (hf.isRightContinuous t) ht
    (hf.le_add_one ht0)

/-- Along a simple counting path, the first hitting time of `Set.Ici c` is at most `t` if and only
if `c ≤ M t ω`. -/
theorem hittingAfter_Ici_le_iff {Ω : Type*} {M : ℝ≥0 → Ω → ℕ} {ω : Ω}
    (hf : IsSimpleCountingPath (M · ω)) (c : ℕ) (t : ℝ≥0) :
    hittingAfter M (Ici c) 0 ω ≤ t ↔ c ≤ M t ω := by
  simpa using hf.isRightContinuous.hittingAfter_Ici_le_iff_of_monotone hf.monotone
    (a := 0) (t := t) (c := c)

/-- Along a simple counting path, `(t : WithTop ℝ≥0)` is strictly before the first hitting time of
`Set.Ici c` if and only if `M t ω < c`. -/
theorem lt_hittingAfter_Ici_iff {Ω : Type*} {M : ℝ≥0 → Ω → ℕ} {ω : Ω}
    (hf : IsSimpleCountingPath (M · ω)) (c : ℕ) (t : ℝ≥0) :
    (t : WithTop ℝ≥0) < hittingAfter M (Ici c) 0 ω ↔ M t ω < c := by
  rw [← not_le, hf.hittingAfter_Ici_le_iff, not_le]

/-- A simple counting path hits a positive level `c` only at a strictly positive time. -/
theorem hittingAfter_Ici_pos {Ω : Type*} {M : ℝ≥0 → Ω → ℕ} {ω : Ω}
    (hf : IsSimpleCountingPath (M · ω)) {c : ℕ} (hc : 0 < c) :
    0 < hittingAfter M (Ici c) 0 ω :=
  isClosed_Ici.lt_hittingAfter_of_isRightContinuous hf.isRightContinuous
    (by simp [hf.apply_zero, hc.ne'])

/-- At a finite hitting time of `Set.Ici c`, a simple counting path takes the exact value `c`. -/
theorem apply_untopA_hittingAfter_Ici {Ω : Type*} {M : ℝ≥0 → Ω → ℕ} {ω : Ω}
    (hf : IsSimpleCountingPath (M · ω)) {c : ℕ}
    (hfin : hittingAfter M (Ici c) 0 ω ≠ ⊤) :
    M (hittingAfter M (Ici c) 0 ω).untopA ω = c := by
  refine hf.isRightContinuous.apply_untopA_hittingAfter_Ici_of_le_add_one
    (by simp [hf.apply_zero]) (fun t ht ↦ ?_) hfin
  obtain ⟨s, hst, hfs⟩ := hf.le_add_one ht
  exact ⟨s, ⟨zero_le, hst⟩, hfs⟩

/-- Along a simple counting path, any finite hitting time of `Set.Ici c` strictly precedes the
hitting time of `Set.Ici (c + 1)`. -/
theorem hittingAfter_Ici_lt_succ {Ω : Type*} {M : ℝ≥0 → Ω → ℕ} {ω : Ω}
    (hf : IsSimpleCountingPath (M · ω)) {c : ℕ}
    (hfin : hittingAfter M (Ici c) 0 ω ≠ ⊤) :
    hittingAfter M (Ici c) 0 ω < hittingAfter M (Ici (c + 1)) 0 ω := by
  refine hf.isRightContinuous.hittingAfter_Ici_lt_succ_of_le_add_one
    (by simp [hf.apply_zero]) (fun t ht ↦ ?_) hfin
  obtain ⟨s, hst, hfs⟩ := hf.le_add_one ht
  exact ⟨s, ⟨zero_le, hst⟩, hfs⟩

/-- Along a simple counting path, any finite hitting time of `Set.Ici c₁` strictly precedes the
hitting time of `Set.Ici c₂` whenever `c₁ < c₂`. -/
theorem hittingAfter_Ici_lt_of_lt {Ω : Type*} {M : ℝ≥0 → Ω → ℕ} {ω : Ω}
    (hf : IsSimpleCountingPath (M · ω)) {c₁ c₂ : ℕ} (hc : c₁ < c₂)
    (hfin : hittingAfter M (Ici c₁) 0 ω ≠ ⊤) :
    hittingAfter M (Ici c₁) 0 ω < hittingAfter M (Ici c₂) 0 ω :=
  (hf.hittingAfter_Ici_lt_succ hfin).trans_le
    (hittingAfter_apply_anti M 0 ω (Ici_subset_Ici.mpr hc))

end IsSimpleCountingPath

end TauCeti.Probability
