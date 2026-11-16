/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Divisor

import TauCeti.Analysis.Meromorphic.Conj

/-!
# Critical-line reflection of whole-plane meromorphic divisors

For a complex function `f : ℂ → ℂ` satisfying punctured-neighbourhood functional-conjugation
identities `(fun w ↦ f (1 - w)) =ᶠ[𝓝[≠] ·] fun w ↦ c * conj (f (conj w))` at `conj z` and
`1 - z`, the reflection `z ↦ 1 - conj z` preserves `MeromorphicOn.divisor f Set.univ`
(`TauCeti.divisor_one_sub_conj`). Over any nontrivially normed star field `𝕜`, whenever the
whole-space divisor of `f : 𝕜 → E` is globally invariant under `z ↦ 1 - conj z`,
`TauCeti.divisorSupportOneSubConj` packages this reflection as an involutive permutation of
`(MeromorphicOn.divisor f Set.univ).support` for reindexing sums and products over the divisor
support.

## Main definitions

* `TauCeti.divisorSupportOneSubConj`: the involutive permutation `ρ ↦ 1 - conj ρ` on the support
  of a `1 - conj`-invariant whole-space divisor.

## Main results

* `TauCeti.divisor_one_sub_conj`: pointwise invariance of `MeromorphicOn.divisor f Set.univ` under
  `z ↦ 1 - conj z` from local punctured-neighbourhood functional-conjugation germs.
* `TauCeti.coe_divisorSupportOneSubConj_apply`, `TauCeti.divisorSupportOneSubConj_symm`,
  `TauCeti.divisorSupportOneSubConj_apply_apply`: characteristic `@[simp]` lemmas for
  `divisorSupportOneSubConj`.
-/

public section

open ComplexConjugate Set Topology

namespace TauCeti

/-- Under punctured-neighbourhood functional-conjugation identities at `conj z` and `1 - z`
(including the degenerate case `c = 0`), the reflection `z ↦ 1 - conj z` preserves the whole-plane
divisor of `f`. -/
theorem divisor_one_sub_conj {f : ℂ → ℂ} {c z : ℂ}
    (hfe : (fun w ↦ f (1 - w)) =ᶠ[𝓝[≠] (conj z)] fun w ↦ c * conj (f (conj w)))
    (hfe' : (fun w ↦ f (1 - w)) =ᶠ[𝓝[≠] (1 - z)] fun w ↦ c * conj (f (conj w))) :
    MeromorphicOn.divisor f Set.univ (1 - conj z) = MeromorphicOn.divisor f Set.univ z := by
  by_cases hm : MeromorphicOn f univ
  · rw [hm.divisor_apply (mem_univ _), hm.divisor_apply (mem_univ _),
      meromorphicOrderAt_one_sub_conj hfe hfe']
  · simp [MeromorphicOn.divisor_eq_zero_of_not_meromorphicOn hm]

section Support

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- When the whole-space divisor of `f` is invariant under `z ↦ 1 - conj z`, that reflection
restricts to an involutive permutation of `(MeromorphicOn.divisor f Set.univ).support`. -/
noncomputable def divisorSupportOneSubConj {f : 𝕜 → E}
    (hd : ∀ z : 𝕜, MeromorphicOn.divisor f Set.univ (1 - conj z) =
      MeromorphicOn.divisor f Set.univ z) :
    Equiv.Perm (MeromorphicOn.divisor f Set.univ).support :=
  Function.Involutive.toPerm
    (fun ρ ↦ ⟨1 - conj (ρ : 𝕜), Function.mem_support.mpr <| by
      rw [hd]
      exact Function.mem_support.mp ρ.property⟩)
    fun ρ ↦ by ext; simp

/-- The support permutation `divisorSupportOneSubConj` acts on the underlying point by
`ρ ↦ 1 - conj ρ`. -/
@[simp]
theorem coe_divisorSupportOneSubConj_apply {f : 𝕜 → E}
    (hd : ∀ z : 𝕜, MeromorphicOn.divisor f Set.univ (1 - conj z) =
      MeromorphicOn.divisor f Set.univ z)
    (ρ : (MeromorphicOn.divisor f Set.univ).support) :
    (divisorSupportOneSubConj hd ρ : 𝕜) = 1 - conj (ρ : 𝕜) :=
  (rfl)

/-- `divisorSupportOneSubConj` is its own inverse. -/
@[simp]
theorem divisorSupportOneSubConj_symm {f : 𝕜 → E}
    (hd : ∀ z : 𝕜, MeromorphicOn.divisor f Set.univ (1 - conj z) =
      MeromorphicOn.divisor f Set.univ z) :
    (divisorSupportOneSubConj hd).symm = divisorSupportOneSubConj hd :=
  (rfl)

/-- `divisorSupportOneSubConj` is an involution on the divisor support. -/
@[simp]
theorem divisorSupportOneSubConj_apply_apply {f : 𝕜 → E}
    (hd : ∀ z : 𝕜, MeromorphicOn.divisor f Set.univ (1 - conj z) =
      MeromorphicOn.divisor f Set.univ z)
    (ρ : (MeromorphicOn.divisor f Set.univ).support) :
    divisorSupportOneSubConj hd (divisorSupportOneSubConj hd ρ) = ρ := by
  ext
  simp

end Support

end TauCeti
