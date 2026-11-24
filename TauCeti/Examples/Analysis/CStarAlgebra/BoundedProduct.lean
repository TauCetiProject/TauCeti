/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.Normed.Lp.C0Ideal

/-!
# Norms in the quotient of a bounded product of C⋆-algebras by its `c₀` ideal

For a sequence `(A n)` of nonzero unital C⋆-algebras, the bounded product `lp A ∞` modulo its
`c₀` ideal is a unital C⋆-algebra (`lp.inftyCStarAlgebra`, `TwoSidedIdeal.Quotient.cstarAlgebra`)
whose norm is the limit superior of the coordinate norms (`lp.norm_mk_c0Ideal`). These examples
evaluate that norm:

* the unit `(1ₙ)` has quotient norm `1` (`lp.normOneClass_quotient_c0Ideal`), so the quotient is
  nonzero;
* for any bounded family `(aₙ)`, the family `(aₙ / (n + 1))` has quotient norm `0`.

In particular, for the matrix algebras `M_{n+1}`, the quotient `∏ₙ M_{n+1} / ⊕ₙ M_{n+1}` is
nonzero.
-/

public section

open Filter Topology
open scoped ENNReal ComplexOrder

namespace TauCeti.BoundedProductExamples

/-- The unit of a bounded product of nonzero unital C⋆-algebras has quotient norm one modulo the
`c₀` ideal. -/
example {A : ℕ → Type*} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)] :
    ‖(1 : lp A ∞ ⧸ lp.c0Ideal A)‖ = 1 :=
  norm_one

/-- For a bounded family `(aₙ)`, the family `(aₙ / (n + 1))` has quotient norm zero modulo the
`c₀` ideal. -/
example {A : ℕ → Type*} [∀ n, NonUnitalNormedRing (A n)] [∀ n, NormedSpace ℂ (A n)]
    (a b : lp A ∞) (hb : ∀ n, b n = ((n : ℂ) + 1)⁻¹ • a n) :
    ‖TwoSidedIdeal.Quotient.mk (lp.c0Ideal A) b‖ = 0 := by
  rw [lp.norm_mk_c0Ideal, Nat.cofinite_eq_atTop]
  refine Tendsto.limsup_eq (squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    (by simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ‖a‖))
  rw [hb, norm_smul, mul_comm, norm_inv]
  gcongr
  · exact lp.norm_apply_le_norm ENNReal.top_ne_zero a n
  · exact_mod_cast (Complex.norm_natCast (n + 1)).ge

/-- **`∏ₙ M_{n+1} / ⊕ₙ M_{n+1}` is nonzero.** -/
example : Nontrivial
    (lp (fun n : ℕ ↦ CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ∞ ⧸
      lp.c0Ideal fun n : ℕ ↦ CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :=
  inferInstance

end TauCeti.BoundedProductExamples
