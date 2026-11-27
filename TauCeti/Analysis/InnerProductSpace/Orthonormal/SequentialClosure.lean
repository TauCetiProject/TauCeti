/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import TauCeti.Topology.Algebra.Module.WeakSpace.DiagonalNet
import TauCeti.Analysis.InnerProductSpace.Parseval
import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded

/-!
# Weak closure and sequential closure along an orthonormal sequence

For an orthonormal sequence `e`, the set of vectors `e m + m • e n` with `1 ≤ m < n`
has zero in its weak closure. Bessel's inequality for functionals
(`Orthonormal.summable_norm_apply_sq`) supplies the weakly null input to the diagonal net.
Every weakly convergent sequence of the displayed vectors is norm bounded
(`Filter.Tendsto.isBounded_range_of_toWeakSpace`). Only finitely many first indices can then
occur, so one coordinate equals one infinitely often.

Taking `e n = lp.single 2 n 1` gives the example in real or complex `ℓ²(ℕ)`. The
general statement applies to orthonormal sequences in seminormed inner product spaces.
-/

public section

open Bornology Filter Set Topology
open scoped InnerProductSpace

/-- Zero belongs to the weak closure of the vectors `e m + m • e n` with `0 < m < n`
in an orthonormal sequence, and lies outside their weak sequential closure. -/
theorem Orthonormal.zero_mem_closure_diff_seqClosure_add_natCast_smul
    {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {e : ℕ → E} (he : Orthonormal 𝕜 e) :
    let A := {x : WeakSpace 𝕜 E | ∃ m n : ℕ, 0 < m ∧ m < n ∧
      toWeakSpace 𝕜 E (e m + (m : 𝕜) • e n) = x}
    0 ∈ closure A \ seqClosure A := by
  classical
  constructor
  · have hweak : Tendsto (fun j ↦ toWeakSpace 𝕜 E (e j)) atTop (𝓝 (toWeakSpace 𝕜 E 0)) := by
      refine TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto.mpr fun f ↦ ?_
      rw [map_zero, tendsto_zero_iff_norm_tendsto_zero]
      simpa using (he.summable_norm_apply_sq f).tendsto_atTop_zero.sqrt
    obtain ⟨m, n, hmn, hlim⟩ := hweak.exists_tendsto_toWeakSpace_add_smul (fun j ↦ (j : 𝕜))
    apply mem_closure_of_tendsto (by simpa only [map_zero] using hlim)
    exact Eventually.of_forall fun i ↦
      ⟨m i, n i, (Nat.zero_le _).trans_lt (hmn i).1, (hmn i).2.1, rfl⟩
  · rintro ⟨v, hv, hvlim⟩
    choose m n _ hmn heq using hv
    let u (j : ℕ) := e (m j) + (m j : 𝕜) • e (n j)
    have hlim : Tendsto (fun j ↦ toWeakSpace 𝕜 E (u j)) atTop (𝓝 (toWeakSpace 𝕜 E 0)) := by
      simpa only [map_zero] using hvlim.congr fun j ↦ (heq j).symm
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hlim.isBounded_range_of_toWeakSpace
    obtain ⟨K, hK⟩ := exists_nat_gt C
    have hm (j : ℕ) : m j < K := by
      have horth : ⟪e (m j), (m j : 𝕜) • e (n j)⟫_𝕜 = 0 := by
        simp [inner_smul_right, he.inner_eq_zero (hmn j).ne]
      have hsq : ‖u j‖ ^ 2 = 1 + (m j : ℝ) ^ 2 := by
        simpa [u, sq, norm_smul, he.norm_eq_one] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
      have hle : (m j : ℝ) ≤ ‖u j‖ := by nlinarith [norm_nonneg (u j)]
      exact_mod_cast hle.trans_lt ((hC _ (mem_range_self j)).trans_lt hK)
    -- A first coordinate that recurs infinitely often prevents convergence to zero.
    have hfinite : ∃ᶠ j in atTop, ∃ p ∈ Finset.range K, m j = p :=
      Frequently.of_forall fun j ↦ ⟨m j, Finset.mem_range.mpr (hm j), rfl⟩
    obtain ⟨p, -, hp⟩ := (frequently_exists_finset _).mp hfinite
    have hcoord := TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto.mp hlim (innerSL 𝕜 (e p))
    rw [map_zero] at hcoord
    obtain ⟨j, hj, hne⟩ := (hp.and_eventually (hcoord.eventually_ne zero_ne_one)).exists
    apply hne
    simp [u, ← hj, innerSL_apply_apply, inner_add_right, inner_smul_right,
      he.inner_eq_zero (hmn j).ne, inner_self_eq_norm_sq_to_K, he.norm_eq_one]
