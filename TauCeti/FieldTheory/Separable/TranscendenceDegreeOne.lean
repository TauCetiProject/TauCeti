/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.SeparablyGenerated

/-!
# Separating elements in transcendence degree one

A finitely generated extension of a perfect field admits a finite separating transcendence
basis.  When the extension has transcendence degree one, that basis consists of one element.
Thus there is a transcendental `x` such that the extension is separable algebraic over the
simple field `k(x)`.

This is the one-variable form of Mathlib's
`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`.  It is useful for passing from
abstract separable generation to constructions that require a single separating parameter.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.10.2.
-/

public section

noncomputable section

open IntermediateField
open scoped IntermediateField

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- A finitely generated extension of transcendence degree one over a perfect field has a
**separating element**: an element `x` transcendental over the base such that the extension is
separable algebraic over `k(x)`.

This is the singleton form of
`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`. -/
theorem exists_transcendental_and_isSeparable_adjoin_of_perfectField
    [PerfectField k] [Algebra.EssFiniteType k F] (htr : Algebra.trdeg k F = 1) :
    ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
  have hcard : s.card = 1 := by
    have h := hs.cardinalMk_eq_trdeg.trans htr
    have h' : (s.card : Cardinal.{v}) = (1 : Cardinal.{v}) := by
      simpa only [Cardinal.mk_fintype, Fintype.card_coe] using h
    exact Nat.cast_injective h'
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
  refine ⟨x, hs.1.transcendental ⟨x, by simp⟩, ?_⟩
  rw [Finset.coe_singleton] at hsep
  exact hsep

end TauCeti
