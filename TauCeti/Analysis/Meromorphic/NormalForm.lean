/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Pointwise evaluation and translation of local meromorphic normal forms

Mathlib's `toMeromorphicNFAt f x` modifies `f` only at `x` so that it lies in local meromorphic
normal form there (`MeromorphicNFAt`), taking its limiting value at a removable singularity and `0`
at a pole or non-meromorphic point.

This file provides two complements to `Mathlib.Analysis.Meromorphic.NormalForm`:
* `MeromorphicNFAt.toMeromorphicNFAt_apply_of_eventuallyEq` and
  `AnalyticAt.toMeromorphicNFAt_apply_of_eventuallyEq`: if `f` agrees on a punctured neighbourhood
  of `x` with a normal-form (in particular analytic) function `g`, then `toMeromorphicNFAt f x x`
  evaluates to `g x`.
* `TauCeti.toMeromorphicNFAt_comp_add_const` and `TauCeti.toMeromorphicNFAt_comp_sub_const`:
  conversion to local normal form commutes with translation of the domain, matching Mathlib's
  `meromorphicNFAt_comp_add_const_iff_meromorphicNFAt`.
-/

public section

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → E} {x c : 𝕜}

/-- If `f` agrees on a punctured neighbourhood of `x` with a function `g` in local meromorphic
normal form at `x`, then the normal form of `f` at `x` takes the value `g x` at `x`. -/
theorem MeromorphicNFAt.toMeromorphicNFAt_apply_of_eventuallyEq
    (hg : MeromorphicNFAt g x) (hfg : f =ᶠ[𝓝[≠] x] g) :
    toMeromorphicNFAt f x x = g x := by
  have h := toMeromorphicNFAt_eventuallyEq_nhds_congr hfg
  rw [toMeromorphicNFAt_eq_self.mpr hg] at h
  exact h.eq_of_nhds

/-- If `f` agrees on a punctured neighbourhood of `x` with a function `g` analytic at `x`, then
`toMeromorphicNFAt f x x` recovers the removable limit `g x`. -/
theorem AnalyticAt.toMeromorphicNFAt_apply_of_eventuallyEq
    (hg : AnalyticAt 𝕜 g x) (hfg : f =ᶠ[𝓝[≠] x] g) :
    toMeromorphicNFAt f x x = g x :=
  hg.meromorphicNFAt.toMeromorphicNFAt_apply_of_eventuallyEq hfg

/-- Conversion to local meromorphic normal form commutes with translation by `+ c`, including when
`f` is not meromorphic at `x + c`. -/
@[to_fun toMeromorphicNFAt_fun_comp_add_const]
theorem TauCeti.toMeromorphicNFAt_comp_add_const (f : 𝕜 → E) (x c : 𝕜) :
    toMeromorphicNFAt (f ∘ (· + c)) x = toMeromorphicNFAt f (x + c) ∘ (· + c) := by
  by_cases hf : MeromorphicAt f (x + c)
  swap
  · have hf' : ¬MeromorphicAt (f ∘ (· + c)) x :=
      meromorphicAt_comp_add_const_iff_meromorphicAt.not.2 hf
    ext z
    simp [hf, hf']
  have hf' : MeromorphicAt (f ∘ (· + c)) x := meromorphicAt_comp_add_const_iff_meromorphicAt.2 hf
  have hadd : Tendsto (· + c) (𝓝[≠] x) (𝓝[≠] (x + c)) :=
    (continuous_id.add continuous_const).continuousWithinAt.tendsto_nhdsWithin fun z hz ↦
      (add_left_injective c).ne hz
  ext z
  by_cases hz : z = x
  · subst hz
    have hnf : MeromorphicNFAt (toMeromorphicNFAt f (z + c) ∘ (· + c)) z :=
      meromorphicNFAt_comp_add_const_iff_meromorphicNFAt.2 meromorphicNFAt_toMeromorphicNFAt
    exact hnf.toMeromorphicNFAt_apply_of_eventuallyEq
      (hadd.eventually hf.eq_nhdsNE_toMeromorphicNFAt)
  · rw [← hf'.eqOn_compl_singleton_toMeromorphicNFAt hz, Function.comp_apply, Function.comp_apply,
      ← hf.eqOn_compl_singleton_toMeromorphicNFAt ((add_left_injective c).ne hz)]

/-- Conversion to local meromorphic normal form commutes with translation by `- c`. -/
@[to_fun toMeromorphicNFAt_fun_comp_sub_const]
theorem TauCeti.toMeromorphicNFAt_comp_sub_const (f : 𝕜 → E) (x c : 𝕜) :
    toMeromorphicNFAt (f ∘ (· - c)) x = toMeromorphicNFAt f (x - c) ∘ (· - c) := by
  simp_rw [sub_eq_add_neg, TauCeti.toMeromorphicNFAt_comp_add_const]
