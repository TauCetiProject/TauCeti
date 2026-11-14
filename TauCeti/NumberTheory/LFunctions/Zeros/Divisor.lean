/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic
import TauCeti.Analysis.Meromorphic.Conj

/-!
# The zero divisor of a meromorphically continued L-function record

For a record `d` satisfying `HasMeromorphicContinuation`, the divisor of the completed function
`Λ = d.completed` on any domain `U` is `-d.polarOrder` at the recorded poles in `U` and is
nonnegative everywhere else. Its negative part is therefore exactly the polar divisor.

The entire completion `d.entireCompletion` clears these poles without creating zeros, so it has
the same zero count as `Λ` on every region. Its signed count equals its zero count, and on a
bounded region it exceeds the signed count of `Λ` by the number of poles in the region. In
particular the two signed counts agree on regions avoiding the poles. These adapters let
counting arguments run on whichever of `Λ` and its entire completion is more convenient.

For any function whose punctured germs obey a critical-line functional-conjugation symmetry
`(fun w ↦ f (1 - w)) =ᶠ[𝓝[≠] z] fun w ↦ c * conj (f (conj w))`, the reflection `z ↦ 1 - conj z`
preserves `meromorphicOrderAt f` and `MeromorphicOn.divisor f Set.univ`; whenever a whole-plane
divisor is invariant under `z ↦ 1 - conj z`, `TauCeti.divisorSupportOneSubConj` packages that
reflection as an involutive permutation of `(MeromorphicOn.divisor f Set.univ).support` for
reindexing sums and products over the zeros.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §12 and §15.
-/

public section

open ComplexConjugate Set Topology

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable {d : AnalyticLFunctionData} (h : d.HasMeromorphicContinuation) {U R : Set ℂ} {s : ℂ}

include h

/-- At a recorded pole in the domain, the divisor of the completed function is minus the
recorded pole order. -/
theorem HasMeromorphicContinuation.divisor_completed_of_polarOrder_ne_zero (hs : s ∈ U)
    (hp : d.polarOrder s ≠ 0) :
    MeromorphicOn.divisor d.completed U s = -(d.polarOrder s : ℤ) := by
  rw [h.meromorphic.meromorphicOn.divisor_apply hs, h.meromorphicOrderAt_eq s hp,
    ← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.untop₀_coe]

/-- Away from the recorded poles, the divisor of the completed function is nonnegative. -/
theorem HasMeromorphicContinuation.divisor_completed_nonneg (hp : d.polarOrder s = 0) :
    0 ≤ MeromorphicOn.divisor d.completed U s := by
  by_cases hs : s ∈ U
  · rw [h.meromorphic.meromorphicOn.divisor_apply hs]
    exact WithTop.untop₀_nonneg.mpr (h.analyticAt s hp).meromorphicOrderAt_nonneg
  · simp [hs]

/-- The divisor of the completed function is negative exactly at the recorded poles in the
domain. -/
theorem HasMeromorphicContinuation.divisor_completed_neg_iff :
    MeromorphicOn.divisor d.completed U s < 0 ↔ s ∈ U ∧ d.polarOrder s ≠ 0 := by
  constructor
  · intro hneg
    refine ⟨by_contra fun hs ↦ by simp [hs] at hneg, fun hp ↦ ?_⟩
    exact (h.divisor_completed_nonneg hp).not_gt hneg
  · rintro ⟨hs, hp⟩
    rw [h.divisor_completed_of_polarOrder_ne_zero hs hp]
    exact neg_neg_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hp)

/-- The negative part of the divisor of the completed function on `U` is the polar divisor on
`U`. -/
theorem HasMeromorphicContinuation.min_divisor_completed_zero (hs : s ∈ U) :
    min (MeromorphicOn.divisor d.completed U s) 0 = -(d.polarOrder s : ℤ) := by
  by_cases hp : d.polarOrder s = 0
  · simpa [hp] using h.divisor_completed_nonneg (U := U) hp
  · rw [h.divisor_completed_of_polarOrder_ne_zero hs hp]
    simp

/-- The divisor of the entire completion is nonnegative on every domain. -/
theorem HasMeromorphicContinuation.divisor_entireCompletion_nonneg (U : Set ℂ) (s : ℂ) :
    0 ≤ MeromorphicOn.divisor d.entireCompletion U s :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun z _ ↦ h.analyticAt_entireCompletion z) s

/-- Clearing the poles does not change any zero multiplicity. -/
@[simp]
theorem HasMeromorphicContinuation.toNat_divisor_entireCompletion (s : ℂ) :
    (MeromorphicOn.divisor d.entireCompletion univ s).toNat =
      (MeromorphicOn.divisor d.completed univ s).toNat := by
  rw [h.divisor_entireCompletion]
  by_cases hp : d.polarOrder s = 0
  · simp [hp]
  · rw [h.divisor_completed_of_polarOrder_ne_zero (mem_univ s) hp]
    simp

/-- The entire completion has the same zero count as the completed function on every region. -/
@[simp]
theorem HasMeromorphicContinuation.zeroCount_entireCompletion (R : Set ℂ) :
    zeroCount d.entireCompletion univ R = zeroCount d.completed univ R := by
  simp_rw [zeroCount_def, h.toNat_divisor_entireCompletion]

/-- The signed count of the entire completion is its zero count. -/
theorem HasMeromorphicContinuation.divisorCount_entireCompletion_eq_zeroCount (R : Set ℂ) :
    divisorCount d.entireCompletion univ R = (zeroCount d.entireCompletion univ R : ℤ) :=
  divisorCount_eq_zeroCount fun z _ ↦ h.divisor_entireCompletion_nonneg univ z

/-- On a bounded region, the signed count of the entire completion is the signed count of the
completed function plus the number of recorded poles in the region. -/
theorem HasMeromorphicContinuation.divisorCount_entireCompletion
    (hR : Bornology.IsBounded R) :
    divisorCount d.entireCompletion univ R =
      divisorCount d.completed univ R + ∑ᶠ s ∈ R, (d.polarOrder s : ℤ) := by
  have hpoles : (R ∩ Function.support fun s ↦ (d.polarOrder s : ℤ)).Finite :=
    d.polarOrder.support.finite_toSet.subset fun s hs ↦ by simpa using hs.2
  simp_rw [divisorCount_def, h.divisor_entireCompletion]
  exact finsum_mem_add_distrib'
    (MeromorphicOn.divisor_finite_inter_support hR (subset_univ _)) hpoles

/-- On a region avoiding the recorded poles, the entire completion and the completed function
have the same signed count. No boundedness is needed. -/
theorem HasMeromorphicContinuation.divisorCount_entireCompletion_of_polarOrder_eq_zero
    (hR : ∀ s ∈ R, d.polarOrder s = 0) :
    divisorCount d.entireCompletion univ R = divisorCount d.completed univ R := by
  simp_rw [divisorCount_def]
  exact finsum_mem_congr rfl fun s hs ↦ by simp [h.divisor_entireCompletion, hR s hs]

/-- On a bounded region, the zero count of the completed function is its signed count plus the
number of recorded poles in the region. -/
theorem HasMeromorphicContinuation.zeroCount_completed_eq_divisorCount_add
    (hR : Bornology.IsBounded R) :
    (zeroCount d.completed univ R : ℤ) =
      divisorCount d.completed univ R + ∑ᶠ s ∈ R, (d.polarOrder s : ℤ) := by
  rw [← h.zeroCount_entireCompletion, ← h.divisorCount_entireCompletion_eq_zeroCount,
    h.divisorCount_entireCompletion hR]

end TauCeti.LFunctions.AnalyticLFunctionData

namespace TauCeti

/-- Under a punctured-neighbourhood functional-conjugation identity
`(fun w ↦ f (1 - w)) =ᶠ[𝓝[≠] z] fun w ↦ c * conj (f (conj w))`, the reflection `z ↦ 1 - conj z`
preserves `meromorphicOrderAt f`. -/
theorem meromorphicOrderAt_one_sub_conj {f : ℂ → ℂ} {c : ℂ}
    (hfe : ∀ z : ℂ, (fun w ↦ f (1 - w)) =ᶠ[𝓝[≠] z] fun w ↦ c * conj (f (conj w))) (z : ℂ) :
    meromorphicOrderAt f (1 - conj z) = meromorphicOrderAt f z := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hzero (u : ℂ) : f =ᶠ[𝓝[≠] u] (0 : ℂ → ℂ) := by
      have hsub : Filter.Tendsto (fun v : ℂ ↦ 1 - v) (𝓝[≠] u) (𝓝[≠] (1 - u)) :=
        (continuous_const.sub continuous_id).continuousWithinAt.tendsto_nhdsWithin fun v hv ↦
          sub_right_injective.ne hv
      filter_upwards [hsub.eventually (hfe (1 - u))] with v hv
      simpa using hv
    rw [meromorphicOrderAt_congr (hzero (1 - conj z)), meromorphicOrderAt_congr (hzero z)]
    simp
  · have hlhs : meromorphicOrderAt (fun w : ℂ ↦ f (1 - w)) (conj z) =
        meromorphicOrderAt f (1 - conj z) :=
      meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) (g := fun w : ℂ ↦ 1 - w)
        (by fun_prop) (by simp)
    have hrhs : meromorphicOrderAt (fun w : ℂ ↦ c * conj (f (conj w))) (conj z) =
        meromorphicOrderAt f z := by
      have hsmul : (fun w : ℂ ↦ c * conj (f (conj w))) = c • (conj ∘ f ∘ conj) := by
        funext w
        simp [Function.comp_def, smul_eq_mul]
      rw [hsmul, meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hc,
        meromorphicOrderAt_conj_conj, Complex.conj_conj]
    rw [← hlhs, meromorphicOrderAt_congr (hfe (conj z)), hrhs]

/-- Under a punctured-neighbourhood functional-conjugation identity
`(fun w ↦ f (1 - w)) =ᶠ[𝓝[≠] z] fun w ↦ c * conj (f (conj w))`, the reflection `z ↦ 1 - conj z`
preserves the whole-plane divisor of `f`. -/
theorem divisor_one_sub_conj {f : ℂ → ℂ} {c : ℂ}
    (hfe : ∀ z : ℂ, (fun w ↦ f (1 - w)) =ᶠ[𝓝[≠] z] fun w ↦ c * conj (f (conj w))) (z : ℂ) :
    MeromorphicOn.divisor f Set.univ (1 - conj z) = MeromorphicOn.divisor f Set.univ z := by
  by_cases hm : MeromorphicOn f univ
  · rw [hm.divisor_apply (mem_univ _), hm.divisor_apply (mem_univ _),
      meromorphicOrderAt_one_sub_conj hfe z]
  · simp [MeromorphicOn.divisor_eq_zero_of_not_meromorphicOn hm]

/-- When the whole-plane divisor of `f` is invariant under `z ↦ 1 - conj z`, that reflection
restricts to an involutive permutation of `(MeromorphicOn.divisor f Set.univ).support`. -/
noncomputable def divisorSupportOneSubConj {f : ℂ → ℂ}
    (hd : ∀ z : ℂ, MeromorphicOn.divisor f Set.univ (1 - conj z) =
      MeromorphicOn.divisor f Set.univ z) :
    Equiv.Perm (MeromorphicOn.divisor f Set.univ).support :=
  Function.Involutive.toPerm
    (fun ρ ↦ ⟨1 - conj (ρ : ℂ), Function.mem_support.mpr <| by
      rw [hd]
      exact Function.mem_support.mp ρ.property⟩)
    fun ρ ↦ by ext; simp

/-- The support permutation `divisorSupportOneSubConj` acts on the underlying point by
`ρ ↦ 1 - conj ρ`. -/
@[simp]
theorem coe_divisorSupportOneSubConj_apply {f : ℂ → ℂ}
    (hd : ∀ z : ℂ, MeromorphicOn.divisor f Set.univ (1 - conj z) =
      MeromorphicOn.divisor f Set.univ z)
    (ρ : (MeromorphicOn.divisor f Set.univ).support) :
    (divisorSupportOneSubConj hd ρ : ℂ) = 1 - conj (ρ : ℂ) :=
  (rfl)

/-- `divisorSupportOneSubConj` is its own inverse. -/
@[simp]
theorem divisorSupportOneSubConj_symm {f : ℂ → ℂ}
    (hd : ∀ z : ℂ, MeromorphicOn.divisor f Set.univ (1 - conj z) =
      MeromorphicOn.divisor f Set.univ z) :
    (divisorSupportOneSubConj hd).symm = divisorSupportOneSubConj hd :=
  (rfl)

/-- `divisorSupportOneSubConj` is an involution on the divisor support. -/
@[simp]
theorem divisorSupportOneSubConj_apply_apply {f : ℂ → ℂ}
    (hd : ∀ z : ℂ, MeromorphicOn.divisor f Set.univ (1 - conj z) =
      MeromorphicOn.divisor f Set.univ z)
    (ρ : (MeromorphicOn.divisor f Set.univ).support) :
    divisorSupportOneSubConj hd (divisorSupportOneSubConj hd ρ) = ρ := by
  ext
  simp

end TauCeti
