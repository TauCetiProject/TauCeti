/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Continuation
import TauCeti.Analysis.Meromorphic.Conj

/-!
# Reflection of meromorphic continuation

Reflection across the real axis preserves a right half-plane. Hence it commutes with canonical
meromorphic continuation from that half-plane, including the zero fallback when no continuation
exists.
-/

public section

open scoped ComplexConjugate

namespace TauCeti

/-- Canonical continuation from a right half-plane commutes with complex conjugation in both
argument and value. -/
@[simp]
theorem meromorphicContinuation_conj_conj (σ : ℝ) (f : ℂ → ℂ) :
    meromorphicContinuation σ (conj ∘ f ∘ conj) =
      conj ∘ meromorphicContinuation σ f ∘ conj := by
  have reflect {g h : ℂ → ℂ} (hh : MeromorphicNFOn h Set.univ)
      (heq : Set.EqOn h g {z | σ < z.re}) :
      MeromorphicNFOn (conj ∘ h ∘ conj) Set.univ ∧
        Set.EqOn (conj ∘ h ∘ conj) (conj ∘ g ∘ conj) {z | σ < z.re} := by
    refine ⟨meromorphicNFOn_conj_conj_iff.mpr (by simpa using hh), ?_⟩
    intro z hz
    exact congrArg conj (heq (by simpa using hz))
  by_cases hex : ∃ g : ℂ → ℂ, MeromorphicNFOn g Set.univ ∧ Set.EqOn g f {z | σ < z.re}
  · obtain ⟨hn, heq⟩ := reflect (meromorphicNFOn_meromorphicContinuation σ f)
      (meromorphicContinuation_eqOn hex)
    exact meromorphicContinuation_eq hn heq
  · have hn : ¬ ∃ g : ℂ → ℂ, MeromorphicNFOn g Set.univ ∧
        Set.EqOn g (conj ∘ f ∘ conj) {z | σ < z.re} := by
      rintro ⟨g, hg, heq⟩
      obtain ⟨hgn, hgf⟩ := reflect hg heq
      exact hex ⟨conj ∘ g ∘ conj, hgn, by simpa [Function.comp_def] using hgf⟩
    rw [meromorphicContinuation_of_not_exists hn, meromorphicContinuation_of_not_exists hex]
    ext z
    simp

end TauCeti
