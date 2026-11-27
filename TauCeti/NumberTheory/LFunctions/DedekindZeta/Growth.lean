/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
public import TauCeti.Analysis.Complex.GrowthOrder.Logarithmic

import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Growth

/-!
# Order of the completed Dedekind zeta function

By `toMeromorphicNFOn_mul_completedDedekindZeta_eq_sum`, the entire extension of
`s(s - 1) Λ_K(s)` is a finite sum of the pole-cleared Mellin completions of ideal lattices.
The split Mellin estimates for these lattices bound the entire extension by
`exp (C (1 + ‖s‖) log (2 + ‖s‖))`, the order-one estimate used for Hadamard factorization.
-/

public section

open NumberField NumberField.mixedEmbedding Set

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- The pole-cleared completed Dedekind zeta function satisfies a global
`exp (C (1 + ‖s‖) log (2 + ‖s‖))` bound. -/
theorem exists_norm_toMeromorphicNFOn_mul_completedDedekindZeta_le_exp_mul_log :
    ∃ C > 0, ∀ s : ℂ, ‖toMeromorphicNFOn
      (fun z : ℂ ↦ z * (z - 1) * completedDedekindZeta K z) univ s‖ ≤
        Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  classical
  obtain ⟨rep, hrep, -⟩ := exists_completedDedekindZeta_eq_sum K
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  choose C hC hb using fun c ↦
    exists_norm_mellinKernelEntireCompletion_le_exp_mul_log hD (idealLattice K (rep c))
  let B : ℝ := ∑ c, C c
  have hB : 0 ≤ B := Finset.sum_nonneg fun c _ ↦ (hC c).le
  have hcard : 0 < (Fintype.card (ClassGroup (𝓞 K)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  refine ⟨B + 2 * Fintype.card (ClassGroup (𝓞 K)),
    add_pos_of_nonneg_of_pos hB (mul_pos two_pos hcard), fun s ↦ ?_⟩
  have hCB (c : ClassGroup (𝓞 K)) : C c ≤ B :=
    Finset.single_le_sum (f := C) (fun i _ ↦ (hC i).le) (Finset.mem_univ c)
  have hsum := norm_sum_mul_le_mul_exp_mul_log (t := Finset.univ) (a := fun _ ↦ (1 : ℂ))
    (fun c _ ↦ hCB c) (fun c _ ↦ hb c s)
  rw [toMeromorphicNFOn_mul_completedDedekindZeta_eq_sum K hD rep hrep, Finset.sum_apply]
  exact (by simpa using hsum : _ ≤ _).trans
    (Real.mul_exp_mul_one_add_mul_log_two_add_le (by positivity) (norm_nonneg s))

/-- The entire extension of `s(s - 1) Λ_K(s)` has growth order at most one. -/
theorem orderLE_toMeromorphicNFOn_mul_completedDedekindZeta :
    OrderLE (toMeromorphicNFOn
      (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) univ) 1 := by
  obtain ⟨C, -, hC⟩ := exists_norm_toMeromorphicNFOn_mul_completedDedekindZeta_le_exp_mul_log K
  exact orderLE_one_of_norm_le_exp_mul_log hC

end TauCeti.LFunctions
