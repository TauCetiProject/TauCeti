/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.Basic

/-!
# Conjugation and open holomorphic domains

This file records the elementary conjugation API used by the conformal-mapping roadmap's
Schwarz-reflection layer.  Mathlib already proves the pointwise fact
`DifferentiableAt.conj_conj`: if `f` is complex differentiable at `conj z`, then
`z ↦ conj (f (conj z))` is complex differentiable at `z`.  The lemmas here package that
pointwise result for open domains and reflected images, which is the form needed before the
real-axis Schwarz reflection principle.
-/

public section

namespace TauCeti

open Complex Set
open scoped ComplexConjugate

variable {f : ℂ → ℂ} {S : Set ℂ} {z : ℂ}

/-!
Mathlib's conjugation lemmas are stated using both `conj` and `starRingEnd ℂ`; the
conformal roadmap fixes `starRingEnd ℂ` as the reflection map.  The next two lemmas make the
reflected set usable without unfolding the image witness.
-/

/-- Membership in the conjugate image of a set, written with `starRingEnd ℂ`. -/
lemma mem_starRingEnd_image_iff :
    z ∈ (starRingEnd ℂ) '' S ↔ (starRingEnd ℂ) z ∈ S := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hz
    refine ⟨(starRingEnd ℂ) z, hz, ?_⟩
    simp

/-- Since complex conjugation is an involution, its image of a set is its preimage. -/
lemma starRingEnd_image_eq_preimage : (starRingEnd ℂ) '' S = (starRingEnd ℂ) ⁻¹' S := by
  ext z
  exact mem_starRingEnd_image_iff

/-- Complex conjugation sends open subsets of `ℂ` to open subsets of `ℂ`. -/
lemma isOpen_starRingEnd_image (hS : IsOpen S) : IsOpen ((starRingEnd ℂ) '' S) := by
  rw [starRingEnd_image_eq_preimage]
  exact hS.preimage continuous_star

/--
Open-domain form of the antiholomorphic-composition prerequisite for Schwarz reflection.

If `f` is holomorphic on an open set `S`, then `z ↦ conj (f (conj z))` is holomorphic on the
reflected open set `conj '' S`.  This is the `DifferentiableOn` wrapper around Mathlib's
pointwise `DifferentiableAt.conj_conj`.
-/
lemma differentiableOn_starRingEnd_comp_starRingEnd_of_isOpen (hS : IsOpen S)
    (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
      ((starRingEnd ℂ) '' S) := by
  intro z hz
  have hzS : (starRingEnd ℂ) z ∈ S := mem_starRingEnd_image_iff.mp hz
  have hfz : DifferentiableAt ℂ f ((starRingEnd ℂ) z) :=
    (hf ((starRingEnd ℂ) z) hzS).differentiableAt (hS.mem_nhds hzS)
  simpa [Function.comp_def] using (hfz.conj_conj).differentiableWithinAt

/--
Conjugating both source and target preserves holomorphicity on open domains, in both
directions.
-/
lemma differentiableOn_starRingEnd_comp_starRingEnd_iff_of_isOpen (hS : IsOpen S) :
    DifferentiableOn ℂ (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
        ((starRingEnd ℂ) '' S) ↔
      DifferentiableOn ℂ f S := by
  constructor
  · intro h
    have hopen : IsOpen ((starRingEnd ℂ) '' S) := isOpen_starRingEnd_image hS
    have htwice :=
      differentiableOn_starRingEnd_comp_starRingEnd_of_isOpen
        (S := (starRingEnd ℂ) '' S)
        (f := fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) hopen h
    simpa [starRingEnd_image_eq_preimage, Set.preimage_preimage, Function.comp_def] using htwice
  · exact differentiableOn_starRingEnd_comp_starRingEnd_of_isOpen hS

end TauCeti
