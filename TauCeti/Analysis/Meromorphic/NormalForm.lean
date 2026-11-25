/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Translation, uniqueness, and punctured-limit evaluation of local meromorphic normal forms

Mathlib's `toMeromorphicNFAt f x` modifies `f` only at `x` when `f` is meromorphic at `x` (and
returns `0` otherwise) so that the resulting function lies in `MeromorphicNFAt · x`. This file
supplies basic properties of `toMeromorphicNFAt` and `toMeromorphicNFOn`:

* `MeromorphicNFAt.toMeromorphicNFAt_eq_of_eqOn_compl_singleton`: if `g` is already in normal form
  at `x` and `f` agrees with `g` off `x`, then `toMeromorphicNFAt f x = g`.
* `MeromorphicAt.toMeromorphicNFAt_apply_eq_of_tendsto`: if `f` is meromorphic at `x` and
  converges to `a` on `𝓝[≠] x`, then its normal-form representative at `x` evaluates to `a` at `x`.
* `TauCeti.toMeromorphicNFAt_comp_add_const`, `TauCeti.toMeromorphicNFAt_comp_sub_const`:
  conversion to normal form commutes with translation in the argument, whether or not `f` is
  meromorphic at the shifted centre.
* `TauCeti.toMeromorphicNFOn_comp_add_const`, `TauCeti.toMeromorphicNFOn_comp_sub_const`: the same
  for conversion to normal form on a set, the set being pulled back along the translation.
-/

public section

open Filter Topology

section Pointwise

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- If `g` is in meromorphic normal form at `x` and `f` agrees with `g` off `x`, then converting
`f` to local meromorphic normal form at `x` yields `g`. -/
theorem MeromorphicNFAt.toMeromorphicNFAt_eq_of_eqOn_compl_singleton {f g : 𝕜 → E} {x : 𝕜}
    (hg : MeromorphicNFAt g x) (hfg : Set.EqOn f g {x}ᶜ) :
    toMeromorphicNFAt f x = g := by
  have hfg' : f =ᶠ[𝓝[≠] x] g := eventually_nhdsWithin_of_forall hfg
  have hf : MeromorphicAt f x := (MeromorphicAt.meromorphicAt_congr hfg').2 hg.meromorphicAt
  ext z
  by_cases hz : z = x
  · subst hz
    simpa [toMeromorphicNFAt_eq_self.mpr hg] using
      (toMeromorphicNFAt_eventuallyEq_nhds_congr hfg').eq_of_nhds
  · rw [← hf.eqOn_compl_singleton_toMeromorphicNFAt hz, hfg hz]

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

/-- A function in meromorphic normal form at `x` with nonzero meromorphic order at `x` vanishes
at `x`. -/
theorem MeromorphicNFAt.apply_eq_zero_of_meromorphicOrderAt_ne_zero {f : 𝕜 → E} {x : 𝕜}
    (hf : MeromorphicNFAt f x) (h : meromorphicOrderAt f x ≠ 0) : f x = 0 :=
  not_not.mp (hf.meromorphicOrderAt_eq_zero_iff.not.mp h)

end Pointwise

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- Local conversion to meromorphic normal form commutes with adding a constant to the argument. -/
theorem toMeromorphicNFAt_comp_add_const (f : 𝕜 → E) (x c : 𝕜) :
    toMeromorphicNFAt (f ∘ (· + c)) x = toMeromorphicNFAt f (x + c) ∘ (· + c) := by
  by_cases hf : MeromorphicAt f (x + c)
  · refine (meromorphicNFAt_comp_add_const_iff_meromorphicNFAt.2
      meromorphicNFAt_toMeromorphicNFAt).toMeromorphicNFAt_eq_of_eqOn_compl_singleton
      fun z hz ↦ ?_
    exact hf.eqOn_compl_singleton_toMeromorphicNFAt ((add_left_injective c).ne hz)
  · simp [hf, meromorphicAt_comp_add_const_iff_meromorphicAt]

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

/-- Conversion to meromorphic normal form on a set commutes with adding a constant to the
argument, the set being pulled back along the translation. -/
theorem toMeromorphicNFOn_comp_add_const (f : 𝕜 → E) (U : Set 𝕜) (c : 𝕜) :
    toMeromorphicNFOn (f ∘ (· + c)) ((· + c) ⁻¹' U) = toMeromorphicNFOn f U ∘ (· + c) := by
  have hm : MeromorphicOn (f ∘ (· + c)) ((· + c) ⁻¹' U) ↔ MeromorphicOn f U := by
    rw [MeromorphicOn.meromorphicOn_comp_add_const_iff_meromorphicOn, Set.add_singleton,
      Set.image_preimage_eq _ (add_right_surjective c)]
  by_cases hf : MeromorphicOn f U
  · funext z
    by_cases hz : z + c ∈ U
    · rw [Function.comp_apply, toMeromorphicNFOn_eq_toMeromorphicNFAt (hm.2 hf) hz,
        toMeromorphicNFOn_eq_toMeromorphicNFAt hf hz, toMeromorphicNFAt_comp_add_const_apply]
    · rw [Function.comp_apply, toMeromorphicNFOn_eq_self_on_compl (hm.2 hf) hz,
        toMeromorphicNFOn_eq_self_on_compl hf hz, Function.comp_apply]
  · rw [toMeromorphicNFOn_of_not_meromorphicOn hf,
      toMeromorphicNFOn_of_not_meromorphicOn (mt hm.1 hf), Pi.zero_comp]

/-- Pointwise form of `TauCeti.toMeromorphicNFOn_comp_add_const`. -/
@[simp]
theorem toMeromorphicNFOn_comp_add_const_apply (f : 𝕜 → E) (U : Set 𝕜) (c z : 𝕜) :
    toMeromorphicNFOn (f ∘ (· + c)) ((· + c) ⁻¹' U) z = toMeromorphicNFOn f U (z + c) :=
  congrFun (toMeromorphicNFOn_comp_add_const f U c) z

/-- Conversion to meromorphic normal form on a set commutes with subtracting a constant from the
argument, the set being pulled back along the translation. -/
theorem toMeromorphicNFOn_comp_sub_const (f : 𝕜 → E) (U : Set 𝕜) (c : 𝕜) :
    toMeromorphicNFOn (f ∘ (· - c)) ((· - c) ⁻¹' U) = toMeromorphicNFOn f U ∘ (· - c) := by
  simpa only [sub_eq_add_neg] using toMeromorphicNFOn_comp_add_const f U (-c)

/-- Pointwise form of `TauCeti.toMeromorphicNFOn_comp_sub_const`. -/
@[simp]
theorem toMeromorphicNFOn_comp_sub_const_apply (f : 𝕜 → E) (U : Set 𝕜) (c z : 𝕜) :
    toMeromorphicNFOn (f ∘ (· - c)) ((· - c) ⁻¹' U) z = toMeromorphicNFOn f U (z - c) :=
  congrFun (toMeromorphicNFOn_comp_sub_const f U c) z

end TauCeti
