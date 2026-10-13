/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Basic
public import TauCeti.FieldTheory.Separable.TranscendenceDegreeOne
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Separably generated algebraic function fields

An algebraic function field over a perfect field admits a separating element: a transcendental
element `x` over which the function field is finite and separable.  This supplies the parameter
needed for the differential calculus of an algebraic function field in arbitrary characteristic,
while keeping the more general results over imperfect fields stated with an explicit separating
element.

Over an imperfect field a separating element need not exist. An element of `F` outside `k` with a
`p`-power in `k`, such as `t^{1/p}` in `𝔽_p(t^{1/p})(X)` over `𝔽_p(t)`, would be both separable
and purely inseparable over `k(x)` for a separating `x`, hence a constant of `k(x)`, which it is
not.

## Main results

* `TauCeti.IsFunctionField.exists_transcendental_and_isSeparable_adjoin_of_perfectField`: a
  function field over a perfect field has a separating element.
* `TauCeti.not_isSeparable_adjoin_of_pow_mem`: an element outside `k` with a power
  `α ^ q ^ n` in `k` rules out every separating element.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.10.2 and
Section IV.1.
-/

public section

noncomputable section

open scoped IntermediateField

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

namespace IsFunctionField

/-- **A function field over a perfect field is separably generated** (Stichtenoth,
Proposition 3.10.2): it has a transcendental element `x` such that `F / k(x)` is separable.
Finiteness over `k(x)` follows separately from
`TauCeti.IsFunctionField.finiteDimensional_adjoin`. -/
theorem exists_transcendental_and_isSeparable_adjoin_of_perfectField [PerfectField k]
    (hF : IsFunctionField k F) :
    ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  let : Algebra.EssFiniteType k F := hF.essFiniteType
  exact TauCeti.exists_transcendental_and_isSeparable_adjoin_of_perfectField hF.trdeg_eq_one

end IsFunctionField

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
