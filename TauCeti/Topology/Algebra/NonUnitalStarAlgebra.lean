/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import TauCeti.Algebra.Star.Opposite

/-!
# Topological closure and dense inclusions of nonunital `⋆`-subalgebras

This file provides `@[simp]` and density lemmas for nonunital `⋆`-subalgebras and opposite
`⋆`-algebra homomorphisms:

* `NonUnitalStarSubalgebra.topologicalClosure_coe`: the underlying set of `s.topologicalClosure`
  is `closure (s : Set A)`, matching `StarSubalgebra.topologicalClosure_coe`.
* `NonUnitalStarAlgHom.denseRange_op`: `f.op` has dense range if and only if `f` does.
* `NonUnitalStarSubalgebra.denseRange_subtype` and `NonUnitalStarSubalgebra.denseRange_subtype_op`:
  the subtype inclusion of `s` (and its multiplicative opposite) has dense range if and only if
  `(s : Set A)` is dense.
-/

public section

/-- `f.op : Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ` has dense range if and only if `f : A →⋆ₙₐ[R] B` does. -/
@[simp]
theorem NonUnitalStarAlgHom.denseRange_op {R A B : Type*} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B] [TopologicalSpace B]
    (f : A →⋆ₙₐ[R] B) : DenseRange f.op ↔ DenseRange f := by
  have h : Set.range (f.op : Aᵐᵒᵖ → Bᵐᵒᵖ) =
      (MulOpposite.opHomeomorph : B → Bᵐᵒᵖ) '' Set.range f := by
    ext b; constructor
    · rintro ⟨a, rfl⟩; exact ⟨f a.unop, ⟨a.unop, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩; exact ⟨MulOpposite.op a, by simp⟩
  rw [DenseRange, DenseRange, h, MulOpposite.opHomeomorph.isDenseEmbedding.dense_image]

namespace NonUnitalStarSubalgebra

section TopologicalClosure

variable {R A : Type*} [CommSemiring R] [TopologicalSpace A] [Star A]
  [NonUnitalSemiring A] [Module R A] [ContinuousStar A]
  [ContinuousConstSMul R A] [IsSemitopologicalSemiring A]

/-- Coercing `s.topologicalClosure` to `Set A` gives the topological closure
`closure (s : Set A)`. -/
@[simp]
theorem topologicalClosure_coe (s : NonUnitalStarSubalgebra R A) :
    (s.topologicalClosure : Set A) = _root_.closure (s : Set A) :=
  (rfl)

end TopologicalClosure

section DenseRange

variable {R A : Type*} [CommSemiring R] [TopologicalSpace A]
  [NonUnitalNonAssocSemiring A] [Module R A] [Star A]

/-- The subtype inclusion `NonUnitalStarSubalgebraClass.subtype s` has dense range if and only if
`(s : Set A)` is dense in `A`. -/
theorem denseRange_subtype (s : NonUnitalStarSubalgebra R A) :
    DenseRange (NonUnitalStarSubalgebraClass.subtype s) ↔ Dense (s : Set A) := by
  rw [NonUnitalStarSubalgebraClass.coe_subtype, denseRange_subtype_val, SetLike.setOfPred_mem_eq]

/-- The opposite subtype inclusion `(NonUnitalStarSubalgebraClass.subtype s).op` has dense range if
and only if `(s : Set A)` is dense in `A`. -/
theorem denseRange_subtype_op (s : NonUnitalStarSubalgebra R A) :
    DenseRange (NonUnitalStarSubalgebraClass.subtype s).op ↔ Dense (s : Set A) :=
  (NonUnitalStarAlgHom.denseRange_op _).trans s.denseRange_subtype

end DenseRange

end NonUnitalStarSubalgebra
