/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Rank-one quotients by Hopf ideals

A closed subgroup of an affine group scheme over a field has coordinate algebra of dimension
one exactly when it is the identity subgroup. This criterion uses the coordinate algebra,
so it distinguishes an infinitesimal subgroup from a trivial subgroup even when both have
only one geometric point.
-/

public section

namespace TauCeti.HopfIdeal

universe u v

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k}

/-- A quotient by a Hopf ideal has dimension one over the base field exactly when the ideal
is the augmentation ideal, which defines the identity subgroup. -/
theorem finrank_quotient_eq_one_iff (I : HopfIdeal k H) :
    Module.finrank k (CommHopfAlgCat.quotient H I) = 1 ↔ I = augmentation k H := by
  constructor
  · intro h
    have hsurj := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h).2
    apply le_antisymm (I.le_augmentation k H)
    intro x hx
    obtain ⟨a, ha⟩ := hsurj ((CommHopfAlgCat.mkQuotient H I).hom x)
    have ha0 : a = 0 := by
      have hc := congrArg (Coalgebra.counit (R := k)) ha
      simpa only [Bialgebra.counit_algebraMap, CoalgHomClass.counit_comp_apply,
        (mem_augmentation k H).mp hx] using hc
    apply mem_toIdeal.mp
    apply (CommHopfAlgCat.mkQuotient_eq_zero_iff H I x).mp
    rw [← ha, ha0, map_zero]
  · rintro rfl
    let e := kerLiftBialgEquiv (Bialgebra.counitBialgHom k H)
      Bialgebra.counit_surjective
    rw [augmentation_def]
    exact e.toAlgEquiv.toLinearEquiv.finrank_eq.trans (Module.finrank_self k)

end TauCeti.HopfIdeal
