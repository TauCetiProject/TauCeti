/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Finiteness of integral scalar quotients

The quotient of a finitely generated abelian group by a nonzero integer multiple is finite.
This supplies finiteness for reductions of integral representations without choosing a basis.
-/

public section

namespace TauCeti

/-- A finitely generated abelian group modulo a nonzero integer multiple is finite. -/
instance instFiniteQuotSMulTopInt (M : Type*) [AddCommGroup M] [Module.Finite ℤ M]
    (r : ℤ) [NeZero r] : Finite (QuotSMulTop r M) :=
  Module.finite_of_fg_torsion _ fun x =>
    ⟨⟨r, mem_nonZeroDivisors_of_ne_zero (NeZero.ne r)⟩,
      Module.mem_annihilator.mp (QuotSMulTop.mem_annihilator M r) x⟩

end TauCeti
