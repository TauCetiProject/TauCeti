/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.CompletedPartialZeta
import TauCeti.Analysis.Contour.Residue.Germ

/-!
# Pole cancellation in weighted sums of completed partial zeta functions

The Laurent principal parts at `0` and `1` of a completed partial zeta function do not depend
on the ideal class (Neukirch, *Algebraic Number Theory*, VII §5). Thus a linear combination
with weights of sum zero has only removable singularities. Normalizing the sum, rather than
normalizing only its summands, supplies the analytic values at the two endpoints.
-/

public section

open Filter NumberField Set
open scoped nonZeroDivisors Topology

namespace TauCeti.LFunctions

/-- The normal form of a balanced linear combination of completed partial zeta functions
is entire: their common residues at both `0` and `1` cancel. -/
theorem analyticAt_toMeromorphicNFOn_sum_mul_completedPartialZeta {K ι : Type*}
    [Field K] [NumberField K] (t : Finset ι) (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (w : ι → ℂ) (hw : ∑ i ∈ t, w i = 0) (s : ℂ) :
    AnalyticAt ℂ (toMeromorphicNFOn (fun z ↦ ∑ i ∈ t, w i * completedPartialZeta (I i) z)
      univ) s := by
  let f (i : ι) (z : ℂ) := w i * completedPartialZeta (I i) z
  have hm (i : ι) : Meromorphic (f i) := by
    dsimp only [f]
    fun_prop
  have hsum : Meromorphic (fun z ↦ ∑ i ∈ t, f i z) := by fun_prop
  have hnf := meromorphicNFOn_toMeromorphicNFOn (fun z ↦ ∑ i ∈ t, f i z) univ (mem_univ s)
  rw [← hnf.meromorphicOrderAt_nonneg_iff_analyticAt,
    meromorphicOrderAt_toMeromorphicNFOn hsum.meromorphicOn (mem_univ s)]
  have hfs : (fun z ↦ ∑ i ∈ t, f i z) = ∑ i ∈ t, f i :=
    funext fun z ↦ (Finset.sum_apply z t f).symm
  have cancel {a r : ℂ}
      (ho : ∀ i, meromorphicOrderAt (completedPartialZeta (I i)) a = (-1 : ℤ))
      (hr : ∀ i, Tendsto (fun z ↦ (z - a) * completedPartialZeta (I i) z) (𝓝[≠] a) (𝓝 r)) :
      0 ≤ meromorphicOrderAt (fun z ↦ ∑ i ∈ t, f i z) a := by
    have hb : (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun z ↦ ∑ i ∈ t, f i z) a := by
      rw [hfs]
      refine le_meromorphicOrderAt_sum (fun i _ ↦ hm i a) fun i _ ↦ ?_
      dsimp only [f]
      rw [fun_meromorphicOrderAt_mul analyticAt_const.meromorphicAt
        (meromorphic_completedPartialZeta _ _), ho]
      exact le_add_of_nonneg_left analyticAt_const.meromorphicOrderAt_nonneg
    apply (Contour.residue_eq_zero_iff_of_neg_one_le (hsum a) hb).mp
    have hres (i : ι) : Contour.residue (f i) a = w i * r := by
      dsimp only [f]
      rw [Contour.residue_const_mul,
        Contour.residue_eq_of_tendsto_sub_mul (meromorphic_completedPartialZeta (I i) a) (hr i)]
    simp_rw [hfs, Contour.residue_sum t (fun i _ ↦ hm i a), hres, ← Finset.sum_mul, hw, zero_mul]
  by_cases h₀ : s = 0
  · subst s
    exact cancel (fun i ↦ meromorphicOrderAt_completedPartialZeta_zero (I i))
      (fun i ↦ by simpa only [sub_zero] using tendsto_mul_completedPartialZeta_zero (I i))
  by_cases h₁ : s = 1
  · subst s
    exact cancel (fun i ↦ meromorphicOrderAt_completedPartialZeta_one (I i))
      (fun i ↦ tendsto_sub_one_mul_completedPartialZeta (I i))
  exact (Finset.analyticAt_fun_sum t fun i _ ↦
    analyticAt_const.mul (analyticAt_completedPartialZeta (I i) h₀ h₁)).meromorphicOrderAt_nonneg

end TauCeti.LFunctions
