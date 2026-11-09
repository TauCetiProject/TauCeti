/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Group.ContinuousDiv

/-!
# Twisted extension of a function from one period

For `d > 0` and `c ≠ 0`, a function continuous on `[0, d]` with `f d = c • f 0` extends to a
continuous function `g` on `ℝ` twisted by `c` along `d`, that is, with `g (t + d) = c • g t`:
on `[k d, k d + d]` the extension is `t ↦ c ^ k • f (t - k d)`. For `c = 1` this is the periodic
extension, for `c = -1` the antiperiodic one.

## Main results

* `TauCeti.exists_continuous_add_eq_smul_eqOn`: the twisted extension.
-/

public section

open Set

namespace TauCeti

variable {V : Type*} [TopologicalSpace V] [MulAction ℝ V] [ContinuousConstSMul ℝ V]

/-- A function continuous on `[0, d]` with `f d = c • f 0`, where `d > 0` and `c ≠ 0`, agrees on
`[0, d]` with a continuous function `g` on `ℝ` satisfying `g (t + d) = c • g t`. -/
theorem exists_continuous_add_eq_smul_eqOn {d c : ℝ} (hd : 0 < d) (hc : c ≠ 0) {f : ℝ → V}
    (hf : ContinuousOn f (Icc 0 d)) (hfd : f d = c • f 0) :
    ∃ g : ℝ → V, Continuous g ∧ (∀ t, g (t + d) = c • g t) ∧ EqOn g f (Icc 0 d) := by
  set g : ℝ → V := fun t => c ^ ⌊t / d⌋ • f (t - ⌊t / d⌋ * d) with hg
  -- On `[k d, k d + d]` the extension is `c ^ k • f (t - k d)`.
  have hpiece (k : ℤ) : EqOn g (fun t => c ^ k • f (t - k * d)) (Icc (k * d) (k * d + d)) := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · subst h
      have hk : ⌊(k * d + d) / d⌋ = k + 1 := by
        rw [show (k * d + d) / d = ((k + 1 : ℤ) : ℝ) by push_cast; field_simp]
        exact Int.floor_intCast _
      have e₁ : k * d + d - ((k + 1 : ℤ) : ℝ) * d = 0 := by push_cast; ring
      have e₂ : k * d + d - k * d = d := by ring
      simp only [hg, hk, zpow_add_one₀ hc, e₁, e₂, hfd, mul_smul]
    · have hk : ⌊t / d⌋ = k :=
        Int.floor_eq_iff.2 ⟨(le_div_iff₀ hd).2 ht.1, (div_lt_iff₀ hd).2 (by linarith)⟩
      simp [hg, hk]
  have hcont (k : ℤ) : ContinuousOn g (Icc (k * d) (k * d + d)) :=
    have hmaps : MapsTo (fun t => t - k * d) (Icc (k * d) (k * d + d)) (Icc 0 d) := fun t ht =>
      ⟨sub_nonneg.2 ht.1, sub_le_iff_le_add'.2 ht.2⟩
    ((hf.comp (continuous_sub_right _).continuousOn hmaps).const_smul _).congr (hpiece k)
  refine ⟨g, continuous_iff_continuousAt.2 fun t => ?_, fun t => ?_, fun t ht => ?_⟩
  · set k := ⌊t / d⌋
    have h₁ : k * d ≤ t := (le_div_iff₀ hd).1 (Int.floor_le _)
    have h₂ : t < k * d + d := by
      have := (div_lt_iff₀ hd).1 (Int.lt_floor_add_one (t / d)); linarith
    have hlow := hcont (k - 1)
    push_cast at hlow
    have hU : ContinuousOn g (Icc (k * d - d) (k * d + d)) := by
      rw [← Icc_union_Icc_eq_Icc (b := k * d) (by linarith) (by linarith)]
      refine ContinuousOn.union_of_isClosed ?_ (hcont k) isClosed_Icc isClosed_Icc
      convert hlow using 2 <;> ring
    exact hU.continuousAt (Icc_mem_nhds (by linarith) h₂)
  · have hk : ⌊(t + d) / d⌋ = ⌊t / d⌋ + 1 := by
      rw [add_div, div_self hd.ne', Int.floor_add_one]
    simp only [hg, hk, zpow_add_one₀ hc]
    push_cast
    rw [mul_comm, mul_smul]
    congr 3
    ring
  · simpa using hpiece 0 (by simpa using ht)

end TauCeti
