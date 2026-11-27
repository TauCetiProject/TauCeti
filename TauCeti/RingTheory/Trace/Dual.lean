/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.LinearAlgebra.Dual.Transfer

/-!
# Linear forms over a separable extension, through the trace

Let `L / K` be a finite separable field extension and `V` a vector space over `L`.  Composing an
`L`-linear form on `V` with the trace `Tr_{L/K} : L → K` gives a `K`-linear form on `V`, and every
`K`-linear form on `V` arises this way from exactly one `L`-linear form. The trace form is
perfect by `traceForm_nondegenerate`, so `LinearMap.dualTransferEquiv` applies. The `L`-linear
form attached to `μ` sends `v` to the element of `L` which the trace form pairs with
`b ↦ μ (b • v)`.

This is how Weil differentials of a function field are transported along an extension of the
constant field: they are linear forms over the constant field, and the trace form of the
constant-field extension converts linear forms over the larger constant field to linear forms over
the smaller one.

## Main results

* `Algebra.isPerfPair_mul_compr₂_trace`: the trace multiplication pairing is perfect, so
  `(Algebra.trace K L).dualTransferEquiv` identifies the two module duals.
* `Module.Dual.apply_eq_zero_iff_forall_trace_eq_zero`: an `L`-linear form vanishes at `v`
  exactly when the traces of its values on the `L`-line through `v` all vanish.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  proof of Theorem 3.4.6, where this identification converts the trace of a Weil differential
  into a Weil differential over the larger constant field.
-/

public section

namespace Algebra

/-- The multiplication pairing of the trace of a finite separable field extension is perfect. -/
instance isPerfPair_mul_compr₂_trace {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ((LinearMap.mul K L).compr₂ (trace K L)).IsPerfPair := by
  have hpair : traceForm K L = (LinearMap.mul K L).compr₂ (trace K L) := by
    ext x y
    simp
  have h := traceForm_nondegenerate K L
  rw [hpair] at h
  exact .of_injective (LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp h.1))
    (LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp h.2))

end Algebra

namespace Module.Dual

variable {K L V : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] [AddCommMonoid V] [Module L V] [Module K V] [IsScalarTower K L V]

omit [Module K V] [IsScalarTower K L V] in
/-- An `L`-linear form vanishes at `v` exactly when the traces of its values at the multiples
`b • v` all vanish. -/
theorem apply_eq_zero_iff_forall_trace_eq_zero (φ : Module.Dual L V) (v : V) :
    φ v = 0 ↔ ∀ b : L, Algebra.trace K L (φ (b • v)) = 0 :=
  ⟨fun h b ↦ by simp [h], fun h ↦ (traceForm_nondegenerate K L).1 (φ v) fun b ↦ by
    simpa [mul_comm] using h b⟩

end Module.Dual
