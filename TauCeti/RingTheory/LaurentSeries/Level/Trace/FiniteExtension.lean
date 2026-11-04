/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Level.Residue

/-!
# Residues and traces in finite extensions of Laurent fields

Let `K` be algebraically closed of characteristic zero and `F = K⸨t⸩`. For a finite
extension `L/F`, the residue of `x dt`, computed through any ramified-level presentation,
is the coefficient of `t⁻¹` in `Tr_{L/F}(x)`. Thus the existing choice-independent residue
can be computed without choosing a parameter or an isomorphism with a ramified level.

For a tower `L/M/F`, this description and transitivity of trace give
`Res_M(Tr_{L/M}(x) dt) = Res_L(x dt)`. Here all residues use the same base differential
`dt`; the ramification factors are already included in `Level.residueOfFinrankEq`.

The level calculation is `Level.coeff_neg_one_trace`, and transport uses Mathlib's
`Algebra.trace_eq_of_algEquiv` and `Algebra.trace_trace`.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968).
-/

public section

open Module
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Level

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  {L : Type*} [Field L] [Algebra K⸨X⸩ L] {e : ℕ+}

/-- The residue of `x dt` in a finite extension is the residue of its trace down to the
base Laurent field. This computes the residue without a choice of level presentation. -/
theorem residueOfFinrankEq_eq_coeff_neg_one_trace (h : finrank K⸨X⸩ L = e) (x : L) :
    residueOfFinrankEq h x = (Algebra.trace K⸨X⸩ L x).coeff (-1) := by
  rw [residueOfFinrankEq_apply h (algEquivOfFinrankEq h), residue_apply,
    ← coeff_neg_one_trace, Algebra.trace_eq_of_algEquiv]

/-- Trace preserves residues in any tower of finite extensions of `K⸨t⸩`, with every
form expressed as a multiple of the same base differential `dt`. -/
theorem residueOfFinrankEq_trace {M : Type*} [Field M] [Algebra K⸨X⸩ M]
    [Algebra M L] [IsScalarTower K⸨X⸩ M L] {d : ℕ+}
    (hM : finrank K⸨X⸩ M = d) (hL : finrank K⸨X⸩ L = e) (x : L) :
    residueOfFinrankEq hM (Algebra.trace M L x) = residueOfFinrankEq hL x := by
  have : FiniteDimensional K⸨X⸩ M := .of_finrank_pos (hM ▸ d.pos)
  have : FiniteDimensional K⸨X⸩ L := .of_finrank_pos (hL ▸ e.pos)
  have : FiniteDimensional M L := .right K⸨X⸩ M L
  rw [residueOfFinrankEq_eq_coeff_neg_one_trace,
    residueOfFinrankEq_eq_coeff_neg_one_trace, Algebra.trace_trace]

end TauCeti.LaurentSeries.Level
