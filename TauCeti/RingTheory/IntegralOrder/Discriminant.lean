/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Discriminant.Opposite
public import TauCeti.RingTheory.IntegralOrder.Basic

/-!
# The regular discriminant of an opposite order

An order over a fraction ring and its opposite have the same regular discriminant when the
ambient regular trace form is nondegenerate. This applies to orders in finite-dimensional
division `ℚ`-algebras, as used for the right class-index bound in Masser and Wüstholz,
*Factorization estimates for abelian varieties*, §3, last paragraph.
-/

public section

open Module Submodule MulOpposite

namespace TauCeti.IntegralOrder.IsOrder

variable {R K E ι : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Ring E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
  {Λ : Subalgebra R E} [Fintype ι] [DecidableEq ι]

/-- When the ambient regular trace form is nondegenerate, an order and its opposite have the
same regular discriminant for corresponding bases. -/
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
    funext i
    simp only [Function.comp_apply, Basis.map_apply, Subalgebra.val_apply,
      Subalgebra.linearEquivOp_apply_coe]
  rw [heq, Algebra.regularDiscr_op hB]

end TauCeti.IntegralOrder.IsOrder
