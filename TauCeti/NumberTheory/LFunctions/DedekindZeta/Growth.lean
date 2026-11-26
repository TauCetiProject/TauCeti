/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
public import TauCeti.Analysis.Complex.GrowthOrder.Logarithmic

import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Growth
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IdealLattice

/-!
# Order of the completed Dedekind zeta function

The entire extension of `s(s - 1) Λ_K(s)` is a finite sum of the pole-cleared
Mellin completions of ideal lattices. The split Mellin estimates for these lattices
bound the entire extension by `exp (C (1 + ‖s‖) log (2 + ‖s‖))`, the order-one
estimate used for Hadamard factorization. The sum formula also retains the nonzero
values at the former poles, where the unextended product vanishes.

The partial zeta normalization is that of J. Neukirch, *Algebraic Number Theory*,
Chapter VII, §5, as formalized by `completedPartialZeta_eq_mellinKernelFEPair_Λ`.
-/

public section

open Filter NumberField NumberField.mixedEmbedding Set
open scoped nonZeroDivisors Topology

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- The pole-cleared Dedekind completion is the sum of the pole-cleared Mellin completions
of the lattices of any system of ideal class representatives, including at `0` and `1`. -/
theorem toMeromorphicNFOn_mul_completedDedekindZeta_eq_sum
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) :
    toMeromorphicNFOn (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) univ =
      ∑ c, mellinKernelEntireCompletion hD (idealLattice K (rep c)) := by
  classical
  have hm : Meromorphic (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) := by fun_prop
  have hd : Differentiable ℂ (∑ c, mellinKernelEntireCompletion hD (idealLattice K (rep c))) :=
    Differentiable.sum fun c _ ↦ differentiable_mellinKernelEntireCompletion hD _
  ext z
  have hne (w : ℂ) : ∀ᶠ s in 𝓝[≠] z, s ≠ w := by
    by_cases h : z = w
    · subst w
      exact self_mem_nhdsWithin
    · exact (eventually_ne_nhds h).filter_mono nhdsWithin_le_nhds
  -- Compare the punctured germs: the finite sum gives the analytic value even at a pole.
  have hgerm : (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) =ᶠ[𝓝[≠] z]
      ∑ c, mellinKernelEntireCompletion hD (idealLattice K (rep c)) := by
    filter_upwards [hne 0, hne 1] with s hs₀ hs₁
    rw [completedDedekindZeta_eq_sum_completedPartialZeta rep hrep, Finset.sum_apply,
      Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [mellinKernelEntireCompletion_eq_mul_Λ hD _ hs₀ hs₁,
      completedPartialZeta_eq_mellinKernelFEPair_Λ hD (rep c) hs₀ hs₁]
  have hnf := meromorphicNFOn_toMeromorphicNFOn
    (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) univ (mem_univ z)
  exact ((hnf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hd.analyticAt z).meromorphicNFAt).mp
    ((hm.meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)).trans hgerm)).eq_of_nhds

/-- The repaired product `s(s - 1) Λ_K(s)` is entire. -/
@[fun_prop]
theorem differentiable_toMeromorphicNFOn_mul_completedDedekindZeta :
    Differentiable ℂ (toMeromorphicNFOn
      (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) univ) := by
  obtain ⟨rep, hrep, -⟩ := exists_completedDedekindZeta_eq_sum K
  rw [toMeromorphicNFOn_mul_completedDedekindZeta_eq_sum K
    isUnitFundamentalDomain_unitFundamentalDomain rep hrep]
  exact Differentiable.sum fun c _ ↦ differentiable_mellinKernelEntireCompletion _ _

/-- The repaired product `s(s - 1) Λ_K(s)` at `0` equals the residue of `Λ_K` at `1`. -/
@[simp]
theorem toMeromorphicNFOn_mul_completedDedekindZeta_zero :
    toMeromorphicNFOn (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) univ 0 =
      classNumber K * (2 * mellinConstant K) := by
  obtain ⟨rep, hrep, -⟩ := exists_completedDedekindZeta_eq_sum K
  rw [toMeromorphicNFOn_mul_completedDedekindZeta_eq_sum K
    isUnitFundamentalDomain_unitFundamentalDomain rep hrep, Finset.sum_apply]
  simp [classNumber]

/-- The repaired product `s(s - 1) Λ_K(s)` at `1` equals the residue of `Λ_K` at `1`. -/
@[simp]
theorem toMeromorphicNFOn_mul_completedDedekindZeta_one :
    toMeromorphicNFOn (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) univ 1 =
      classNumber K * (2 * mellinConstant K) := by
  obtain ⟨rep, hrep, -⟩ := exists_completedDedekindZeta_eq_sum K
  rw [toMeromorphicNFOn_mul_completedDedekindZeta_eq_sum K
    isUnitFundamentalDomain_unitFundamentalDomain rep hrep, Finset.sum_apply]
  simp [classNumber]

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
