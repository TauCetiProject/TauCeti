/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Discriminant.Regular
public import TauCeti.RingTheory.IntegralOrder.Basic
public import TauCeti.RingTheory.Trace.Regular.Opposite

/-!
# The regular discriminant of an opposite order

Passing to an opposite algebra preserves regular-trace discriminants when the ambient regular
trace form is nondegenerate. For orders this compares the actual integral discriminants, by
injecting into the fraction field. In particular an order in a finite-dimensional division
`ℚ`-algebra and its opposite have the same discriminant, as used for the right class-index bound
in Masser and Wüstholz, *Factorization estimates for abelian varieties*, §3, last paragraph.
-/

public section

open Module Submodule MulOpposite

namespace Algebra

variable {K A ι : Type*} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
  [Fintype ι] [DecidableEq ι]

/-- Passing to the opposite algebra preserves the regular discriminant of every finite family. -/
theorem regularDiscr_op (hB : (regularTraceForm K A).Nondegenerate) (b : ι → A) :
    regularDiscr K (op ∘ b) = regularDiscr K b := by
  simp only [regularDiscr_def, Function.comp_apply, regularTraceForm_op hB]

end Algebra

namespace TauCeti.IntegralOrder.IsOrder

variable {R K E ι : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Ring E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
  {Λ : Subalgebra R E} [Fintype ι] [DecidableEq ι]

/-- **An order and its opposite have the same regular discriminant.** The bases are transported
through the canonical linear equivalence with the opposite order. The nondegeneracy hypothesis
holds for semisimple algebras in characteristic zero, in particular for division algebras over
`ℚ`. -/
theorem regularDiscr_op (hΛ : IsOrder K Λ)
    (hB : (Algebra.regularTraceForm K E).Nondegenerate) (b : Basis ι R Λ) :
    Algebra.regularDiscr R (b.map Λ.linearEquivOp) = Algebra.regularDiscr R b := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  have hspan : span K (Set.range Λ.val) = ⊤ := by simpa using hΛ.span_eq_top
  let bK := b.ofFractionRingOfSpan Λ.val.toLinearMap Subtype.val_injective hspan
  have := Module.Finite.of_basis bK
  let bop := b.map Λ.linearEquivOp
  have := Module.Free.of_basis bop
  have := Module.Finite.of_basis bop
  have hΛop := isOrder_op_iff.mpr hΛ
  have hspanop : span K (Set.range Λ.op.val) = ⊤ := by
    rw [Subalgebra.coe_val, Subtype.range_val]
    exact hΛop.span_eq_top
  apply IsFractionRing.injective R K
  rw [Algebra.algebraMap_regularDiscr Λ.op.val Subtype.val_injective hspanop,
    Algebra.algebraMap_regularDiscr Λ.val Subtype.val_injective hspan]
  have heq : Λ.op.val ∘ (b.map Λ.linearEquivOp) = op ∘ (Λ.val ∘ b) := by
    ext i
    rfl
  rw [heq, Algebra.regularDiscr_op hB]

end TauCeti.IntegralOrder.IsOrder
