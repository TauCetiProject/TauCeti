/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.WeakSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A diagonal net from a weakly null sequence

If `u m ⇀ 0`, then for each fixed `m` the vectors `u m + c m • u n` converge weakly to
`u m` as `n` tends to infinity. Selecting two indices for each finite family of tests and
each required accuracy gives a single weakly null net of these vectors. The coefficients
`c m` can grow arbitrarily fast.
-/

public section

open Filter Topology

/-- Given a weakly null sequence `u` and any coefficients `c`, there is a weakly null net
of vectors `u m + c m • u n`. At index `(F, k)` the chosen indices satisfy `k < m < n`,
and every functional in `F` takes a value of norm less than `1 / (k + 1)`. -/
theorem Filter.Tendsto.exists_tendsto_toWeakSpace_add_smul
    {𝕜 E : Type*} [SeminormedCommRing 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]
    {u : ℕ → E} (hu : Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E 0)))
    (c : ℕ → 𝕜) :
    ∃ m n : Finset (StrongDual 𝕜 E) × ℕ → ℕ,
      (∀ i, i.2 < m i ∧ m i < n i ∧
        ∀ f ∈ i.1, ‖f (u (m i) + c (m i) • u (n i))‖ < 1 / ((i.2 : ℝ) + 1)) ∧
      Tendsto (fun i ↦ toWeakSpace 𝕜 E (u (m i) + c (m i) • u (n i))) atTop
        (𝓝 (toWeakSpace 𝕜 E 0)) := by
  classical
  have hlim (f : StrongDual 𝕜 E) : Tendsto (fun n ↦ f (u n)) atTop (𝓝 0) := by
    simpa only [map_zero] using TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto.mp hu f
  have select (i : Finset (StrongDual 𝕜 E) × ℕ) :
      ∃ m n : ℕ, i.2 < m ∧ m < n ∧
        ∀ f ∈ i.1, ‖f (u m + c m • u n)‖ < 1 / ((i.2 : ℝ) + 1) := by
    let ε := 1 / ((i.2 : ℝ) + 1)
    have hε : 0 < ε := by positivity [ε]
    have hsmall : ∀ᶠ m in atTop, ∀ f ∈ i.1, ‖f (u m)‖ < ε :=
      i.1.eventually_all.mpr fun f _ ↦
        (tendsto_zero_iff_norm_tendsto_zero.mp (hlim f)).eventually_lt_const hε
    obtain ⟨m, hm, hmε⟩ := ((eventually_gt_atTop i.2).and hsmall).exists
    have hrow : ∀ᶠ n in atTop, ∀ f ∈ i.1, ‖f (u m + c m • u n)‖ < ε := by
      refine i.1.eventually_all.mpr fun f hf ↦ ?_
      have ht : Tendsto (fun n ↦ f (u m + c m • u n)) atTop (𝓝 (f (u m))) := by
        simpa only [map_add, map_smul, smul_eq_mul, mul_zero, add_zero] using
          tendsto_const_nhds.add ((hlim f).const_mul (c m))
      exact ht.norm.eventually_lt_const (hmε f hf)
    obtain ⟨n, hn, hnε⟩ := ((eventually_gt_atTop m).and hrow).exists
    exact ⟨m, n, hm, hn, hnε⟩
  choose m n h using select
  refine ⟨m, n, h, TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto.mpr fun f ↦ ?_⟩
  rw [map_zero]
  apply squeeze_zero_norm'
  · filter_upwards [eventually_ge_atTop ({f}, 0)] with i hi
    exact ((h i).2.2 f (hi.1 (Finset.mem_singleton_self f))).le
  · rw [← prod_atTop_atTop_eq]
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp tendsto_snd
