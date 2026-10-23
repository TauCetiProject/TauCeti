/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Separating elements in transcendence degree one

A finitely generated extension of a perfect field admits a finite separating transcendence
basis.  When the extension has transcendence degree one, that basis consists of one element.
Thus there is a transcendental `x` such that the extension is separable algebraic over the
simple field `k(x)`.

This is the one-variable form of Mathlib's
`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`.  It is useful for passing from
abstract separable generation to constructions that require a single separating parameter.

An element outside the image of the base field with an exponential-characteristic power in
that image rules out every separating element, even over an imperfect base field.

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

/-- **A purely inseparable element outside `k` rules out separating elements**: if `α ∈ F` is not
in `k` but some power `α ^ q ^ n`, `q` the exponential characteristic of `k`, is, then `F` is
separable over `k(x)` for no `x` transcendental over `k`. -/
theorem not_isSeparable_adjoin_of_pow_mem (q : ℕ) [ExpChar k q] {α : F}
    (hα : α ∉ (algebraMap k F).range) {n : ℕ} (hn : α ^ q ^ n ∈ (algebraMap k F).range)
    {x : F} (hx : Transcendental k x) : ¬ Algebra.IsSeparable k⟮x⟯ F := by
  -- `α` would be separable and purely inseparable over `k(x)`, hence in `k(x)`; being algebraic
  -- over `k`, it would then be in `k`.
  intro hsep
  have := expChar_of_injective_algebraMap (algebraMap k k⟮x⟯).injective q
  obtain ⟨c, hc⟩ := hn
  have hmem : α ∈ perfectClosure k⟮x⟯ F := by
    rw [mem_perfectClosure_iff_pow_mem q]
    exact ⟨n, algebraMap k k⟮x⟯ c, by rw [← IsScalarTower.algebraMap_apply, hc]⟩
  rw [perfectClosure.eq_bot_of_isSeparable, IntermediateField.mem_bot] at hmem
  obtain ⟨β, rfl⟩ := hmem
  have hβ : IsAlgebraic k β := by
    refine (isAlgebraic_algebraMap_iff (algebraMap k⟮x⟯ F).injective).mp
      (IsAlgebraic.of_pow (n := q ^ n) (pow_pos (expChar_pos k q) n) ?_)
    rw [← hc]
    exact isAlgebraic_algebraMap c
  have := hx.isIntegrallyClosedIn_adjoin
  obtain ⟨d, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hβ.isIntegral
  exact hα ⟨d, (IsScalarTower.algebraMap_apply k k⟮x⟯ F d).symm⟩


end TauCeti
