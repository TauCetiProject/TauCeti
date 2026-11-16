/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import TauCeti.Algebra.Star.Opposite

/-!
# Topological lemmas for nonunital star subalgebras and homomorphisms

This file provides:

* `NonUnitalStarSubalgebra.topologicalClosure_coe`: `@[simp]` lemma identifying the underlying set
  of `s.topologicalClosure` with `closure (s : Set A)`, matching
  `StarSubalgebra.topologicalClosure_coe`.
* `NonUnitalStarAlgHom.denseRange_op_iff`: passing to `MulOpposite` via `NonUnitalStarAlgHom.op`
  preserves `DenseRange`, without requiring any topology on the domain.
* `NonUnitalStarSubalgebraClass.denseRange_subtype_op_iff`: the opposite subtype inclusion of a
  nonunital `⋆`-subalgebra has dense range if and only if the subalgebra is dense.
-/

public section

namespace NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [TopologicalSpace A] [Star A]
  [NonUnitalSemiring A] [Module R A] [ContinuousStar A]
  [ContinuousConstSMul R A] [IsSemitopologicalSemiring A]

/-- Coercing `s.topologicalClosure` to `Set A` gives the topological closure
`closure (s : Set A)`. -/
@[simp]
theorem topologicalClosure_coe (s : NonUnitalStarSubalgebra R A) :
    (s.topologicalClosure : Set A) = _root_.closure (s : Set A) :=
  (rfl)

end NonUnitalStarSubalgebra

namespace NonUnitalStarAlgHom

/-- Taking `MulOpposite` preserves dense range of a nonunital `⋆`-algebra homomorphism, without
requiring any topology on the domain. -/
@[simp]
theorem denseRange_op_iff {R A₀ A : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A₀] [DistribMulAction R A₀] [Star A₀]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A] [TopologicalSpace A]
    (φ : A₀ →⋆ₙₐ[R] A) :
    DenseRange φ.op ↔ DenseRange φ := by
  unfold DenseRange
  have hfun : (⇑φ.op : A₀ᵐᵒᵖ → Aᵐᵒᵖ) = (MulOpposite.opHomeomorph ∘ φ) ∘ MulOpposite.unop := by
    ext x; simp
  rw [hfun, MulOpposite.unop_surjective.range_comp, Set.range_comp,
    MulOpposite.opHomeomorph.isDenseEmbedding.dense_image]

end NonUnitalStarAlgHom

namespace NonUnitalStarSubalgebraClass

/-- Taking `MulOpposite` on the subtype inclusion of a nonunital `⋆`-subalgebra has dense range
if and only if the subalgebra is dense. -/
theorem denseRange_subtype_op_iff {R A S : Type*} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Star A] [Module R A] [TopologicalSpace A]
    [SetLike S A] [NonUnitalSubsemiringClass S A] [SMulMemClass S R A] [StarMemClass S A]
    (s : S) :
    DenseRange (subtype (R := R) s).op ↔ Dense (s : Set A) := by
  simp

end NonUnitalStarSubalgebraClass
