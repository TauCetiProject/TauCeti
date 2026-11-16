/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions

/-!
# A C⋆-algebra as a right Hilbert module over itself

Right Hilbert `A`-modules are represented with Mathlib's class as `CStarModule Aᵐᵒᵖ E`: the right
action is `x a = MulOpposite.op a • x` and the usual `A`-valued inner product is
`MulOpposite.unop (inner Aᵐᵒᵖ x y)`. This file equips the C⋆-algebra `A` itself with this
structure, with right action given by multiplication on the right
(`MulOpposite.smul_eq_mul_unop`) and inner product `⟨a, b⟩_A = star a * b`. The module norm is
the C⋆-norm of `A`, by the C⋆-identity. It is the basic example of a full right Hilbert
module.

This is not Mathlib's self-module `CStarModule A A`, whose inner product `⟪a, b⟫_A = b * star a`
is adapted to the left action of `A` by multiplication on the left. The right self-module is the
left self-module of `Aᵐᵒᵖ` transported along `MulOpposite.op : A → Aᵐᵒᵖ`;
`CStarModule.inner_op_op` records this compatibility.

## Main declarations

* `CStarModule.instMulOpposite`: the instance `CStarModule Aᵐᵒᵖ A`.
* `CStarModule.unop_inner_mulOpposite`: the inner product formula `⟨a, b⟩_A = star a * b`.
* `CStarModule.dense_range_unop_inner_mulOpposite`: the inner products `⟨a, b⟩_A` are dense
  in `A`. Consequently their closed linear span is all of `A`
  (`CStarModule.topologicalClosure_span_range_unop_inner_mulOpposite`): `A` is full as a right
  Hilbert module over itself.

## References

* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
-/

public section

open MulOpposite Filter Topology

namespace CStarModule

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A C⋆-algebra `A` is a right Hilbert `A`-module over itself, with right action
`MulOpposite.op b • a = a * b` and `A`-valued inner product `⟨a, b⟩_A = star a * b`. Its module
norm is the C⋆-norm of `A`. -/
instance instMulOpposite : CStarModule Aᵐᵒᵖ A where
  inner x y := op (star x * y)
  inner_add_right := by simp [mul_add]
  inner_self_nonneg := op_nonneg.mpr (star_mul_self_nonneg _)
  inner_self := by simp
  inner_op_smul_right := by simp [smul_eq_mul_unop, mul_assoc]
  inner_smul_right_complex := by simp [mul_smul_comm]
  star_inner _ _ := by simp
  norm_eq_sqrt_norm_inner_self x := by
    simp only [MulOpposite.norm_op, CStarRing.norm_star_mul_self,
      Real.sqrt_mul_self (norm_nonneg x)]

/-- The `Aᵐᵒᵖ`-valued inner product of the right self-module. -/
lemma inner_mulOpposite (x y : A) : inner Aᵐᵒᵖ x y = op (star x * y) := (rfl)

/-- The `A`-valued inner product of the right self-module is `⟨x, y⟩_A = star x * y`. -/
@[simp]
lemma unop_inner_mulOpposite (x y : A) : unop (inner Aᵐᵒᵖ x y) = star x * y := (rfl)

/-- The right self-module of `A` is the left self-module of `Aᵐᵒᵖ` (Mathlib's
`CStarModule Aᵐᵒᵖ Aᵐᵒᵖ`, with inner product `⟪u, v⟫ = v * star u`) transported along
`MulOpposite.op`. -/
lemma inner_op_op (x y : A) : inner Aᵐᵒᵖ (op x) (op y) = inner Aᵐᵒᵖ x y := by
  simp [inner_mulOpposite, WithCStarModule.inner_def]

/-- The inner products `⟨x, y⟩_A = star x * y` of the right self-module form a dense subset of
`A`. -/
theorem dense_range_unop_inner_mulOpposite :
    Dense (Set.range fun p : A × A ↦ unop (inner Aᵐᵒᵖ p.1 p.2)) := by
  -- Along an increasing approximate unit `e`, `⟨e, y⟩_A = e * y` tends to `y`.
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  refine fun y ↦ mem_closure_of_tendsto (hl.tendsto_mul_right y) ?_
  filter_upwards [hl.eventually_star_eq] with e he
  exact ⟨(e, y), by simp [he]⟩

/-- The right self-module of `A` is full: the closed complex linear span of its inner products
`⟨x, y⟩_A` is all of `A`. -/
theorem topologicalClosure_span_range_unop_inner_mulOpposite :
    (Submodule.span ℂ (Set.range fun p : A × A ↦ unop (inner Aᵐᵒᵖ p.1 p.2))).topologicalClosure
      = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp <|
    dense_range_unop_inner_mulOpposite.mono Submodule.subset_span

end CStarModule
