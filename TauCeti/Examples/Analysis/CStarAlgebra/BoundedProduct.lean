/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.BoundedProduct
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Analysis.Normed.Lp.C0Ideal

/-!
# The quotient of the bounded product of matrix algebras by the `c₀` sum

For a sequence `(A n)` of nonzero unital C⋆-algebras, the bounded product `lp A ∞` modulo its
`c₀` ideal is a unital C⋆-algebra (`lp.inftyCStarAlgebra`, `TwoSidedIdeal.Quotient.cstarAlgebra`)
whose norm is the limit superior of the coordinate norms (`lp.norm_mk_c0Ideal`). These examples
evaluate that norm:

* a family `(aₙ)` with `‖aₙ‖ = 1` for every `n` has quotient norm `1`; in particular so does the
  unit `(1ₙ)`, and the quotient is nonzero;
* the family `(aₙ / (n + 1))` has quotient norm `0`.

For `A n = M_{n+1}` this is the Check `∏ₙ M_{n+1} / ⊕ₙ M_{n+1}` of the CStarAlgebras roadmap, C5.4.
-/

public section

open Filter Topology
open scoped ENNReal ComplexOrder

namespace TauCeti.BoundedProductExamples

variable {A : ℕ → Type*} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]

/-- A bounded family of norm-one elements has quotient norm one modulo the `c₀` ideal. -/
theorem norm_mk_c0Ideal_of_forall_norm_eq_one (a : lp A ∞) (ha : ∀ n, ‖a n‖ = 1) :
    ‖TwoSidedIdeal.Quotient.mk (lp.c0Ideal A) a‖ = 1 := by
  rw [lp.norm_mk_c0Ideal]
  simp [ha]

/-- The unit of the bounded product has quotient norm one modulo the `c₀` ideal. -/
theorem norm_mk_c0Ideal_one : ‖TwoSidedIdeal.Quotient.mk (lp.c0Ideal A) 1‖ = 1 :=
  norm_mk_c0Ideal_of_forall_norm_eq_one 1 fun _ ↦ by simp

/-- The quotient of the bounded product of nonzero unital C⋆-algebras by the `c₀` ideal is
nonzero. -/
instance nontrivial_quotient_c0Ideal : Nontrivial (lp A ∞ ⧸ lp.c0Ideal A) :=
  nontrivial_of_ne (TwoSidedIdeal.Quotient.mk (lp.c0Ideal A) 1) 0 fun h ↦ by
    simpa [h] using (norm_mk_c0Ideal_one (A := A)).symm

/-- If `‖aₙ‖ = 1` for every `n`, the family `(aₙ / (n + 1))` has quotient norm zero modulo the
`c₀` ideal. -/
theorem norm_mk_c0Ideal_of_apply_eq_inv_smul (a b : lp A ∞) (ha : ∀ n, ‖a n‖ = 1)
    (hb : ∀ n, b n = ((n : ℂ) + 1)⁻¹ • a n) :
    ‖TwoSidedIdeal.Quotient.mk (lp.c0Ideal A) b‖ = 0 := by
  rw [lp.norm_mk_c0Ideal, Nat.cofinite_eq_atTop]
  refine Tendsto.limsup_eq ?_
  have h (n : ℕ) : ‖b n‖ = 1 / ((n : ℝ) + 1) := by
    rw [hb, norm_smul, ha, mul_one, norm_inv, ← Nat.cast_succ, Complex.norm_natCast,
      Nat.cast_succ, one_div]
  simpa only [h] using (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto
    (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0))

/-- **`∏ₙ M_{n+1} / ⊕ₙ M_{n+1}` is nonzero.** -/
example : Nontrivial
    (lp (fun n : ℕ ↦ CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ∞ ⧸
      lp.c0Ideal fun n : ℕ ↦ CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :=
  inferInstance

end TauCeti.BoundedProductExamples
