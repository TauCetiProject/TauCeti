/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Translation and punctured-limit evaluation of local meromorphic normal forms

Mathlib's `toMeromorphicNFAt f x` modifies `f` only at `x` when `f` is meromorphic at `x` (and
returns `0` otherwise) so that the resulting function lies in `MeromorphicNFAt · x`. This file
supplies two basic properties of `toMeromorphicNFAt`:

* `TauCeti.toMeromorphicNFAt_comp_add_const`, `TauCeti.toMeromorphicNFAt_comp_sub_const`:
  conversion to normal form commutes with translation in the argument, whether or not `f` is
  meromorphic at the shifted centre.
* `MeromorphicAt.toMeromorphicNFAt_apply_eq_of_tendsto`: if `f` is meromorphic at `x` and
  converges to `a` on `𝓝[≠] x`, then its normal-form representative at `x` evaluates to `a` at `x`.
-/

public section

open Filter Topology

section Limits

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- If `f` is meromorphic at `x` and tends to `a` on the punctured neighbourhood `𝓝[≠] x`, then
its local meromorphic normal form at `x` evaluates to `a` at `x`. Meromorphicity cannot be
dropped: for instance `f = conj` on `ℂ` tends to `1` on `𝓝[≠] 1` without being meromorphic at `1`,
so `toMeromorphicNFAt conj 1 1 = 0 ≠ 1`. -/
theorem MeromorphicAt.toMeromorphicNFAt_apply_eq_of_tendsto {f : 𝕜 → E} {x : 𝕜} {a : E}
    (hf : MeromorphicAt f x) (hlim : Tendsto f (𝓝[≠] x) (𝓝 a)) :
    toMeromorphicNFAt f x x = a := by
  have hord : 0 ≤ meromorphicOrderAt f x :=
    (tendsto_nhds_iff_meromorphicOrderAt_nonneg hf).1 ⟨a, hlim⟩
  have han : AnalyticAt 𝕜 (toMeromorphicNFAt f x) x :=
    hf.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.1 hord
  have hlim' : Tendsto f (𝓝[≠] x) (𝓝 (toMeromorphicNFAt f x x)) :=
    han.continuousAt.continuousWithinAt.tendsto.congr' hf.eq_nhdsNE_toMeromorphicNFAt.symm
  exact tendsto_nhds_unique hlim' hlim

end Limits

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- Local conversion to meromorphic normal form commutes with adding a constant to the argument. -/
theorem toMeromorphicNFAt_comp_add_const (f : 𝕜 → E) (x c : 𝕜) :
    toMeromorphicNFAt (f ∘ (· + c)) x = toMeromorphicNFAt f (x + c) ∘ (· + c) := by
  by_cases hf : MeromorphicAt f (x + c)
  swap
  · rw [toMeromorphicNFAt_of_not_meromorphicAt hf,
      toMeromorphicNFAt_of_not_meromorphicAt
        (meromorphicAt_comp_add_const_iff_meromorphicAt.not.2 hf)]
    rfl
  have hf' : MeromorphicAt (f ∘ (· + c)) x := meromorphicAt_comp_add_const_iff_meromorphicAt.2 hf
  have hne : ∀ z ≠ x, toMeromorphicNFAt (f ∘ (· + c)) x z =
      (toMeromorphicNFAt f (x + c) ∘ (· + c)) z := by
    intro z hz
    have hzc : z + c ≠ x + c := add_left_injective c |>.ne hz
    simp only [Function.comp_apply, ← hf'.eqOn_compl_singleton_toMeromorphicNFAt hz,
      ← hf.eqOn_compl_singleton_toMeromorphicNFAt hzc]
  have hnhds : toMeromorphicNFAt (f ∘ (· + c)) x =ᶠ[𝓝 x]
      toMeromorphicNFAt f (x + c) ∘ (· + c) :=
    (meromorphicNFAt_toMeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      (meromorphicNFAt_comp_add_const_iff_meromorphicNFAt.2 meromorphicNFAt_toMeromorphicNFAt)).1
      (eventually_nhdsWithin_of_forall hne)
  ext z
  by_cases hz : z = x
  · subst z
    exact hnhds.eq_of_nhds
  · exact hne z hz

/-- Pointwise form of `TauCeti.toMeromorphicNFAt_comp_add_const`. -/
@[simp]
theorem toMeromorphicNFAt_comp_add_const_apply (f : 𝕜 → E) (x c z : 𝕜) :
    toMeromorphicNFAt (f ∘ (· + c)) x z = toMeromorphicNFAt f (x + c) (z + c) :=
  congrFun (toMeromorphicNFAt_comp_add_const f x c) z

/-- Local conversion to meromorphic normal form commutes with subtracting a constant from the
argument. -/
theorem toMeromorphicNFAt_comp_sub_const (f : 𝕜 → E) (x c : 𝕜) :
    toMeromorphicNFAt (f ∘ (· - c)) x = toMeromorphicNFAt f (x - c) ∘ (· - c) := by
  simpa only [sub_eq_add_neg] using toMeromorphicNFAt_comp_add_const f x (-c)

/-- Pointwise form of `TauCeti.toMeromorphicNFAt_comp_sub_const`. -/
@[simp]
theorem toMeromorphicNFAt_comp_sub_const_apply (f : 𝕜 → E) (x c z : 𝕜) :
    toMeromorphicNFAt (f ∘ (· - c)) x z = toMeromorphicNFAt f (x - c) (z - c) :=
  congrFun (toMeromorphicNFAt_comp_sub_const f x c) z

end TauCeti
