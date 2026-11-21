/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import TauCeti.Algebra.Star.Subalgebra
public import TauCeti.Algebra.Star.Opposite

/-!
# Topological closure, corners, dense inclusions, and cores of nonunital `⋆`-subalgebras

This file provides `@[simp]`, closedness, and density lemmas for nonunital `⋆`-subalgebras and
opposite `⋆`-algebra homomorphisms, and the self-adjoint core of a closed left ideal:

* `NonUnitalStarSubalgebra.topologicalClosure_coe`: the underlying set of `s.topologicalClosure`
  is `closure (s : Set A)`, matching `StarSubalgebra.topologicalClosure_coe`.
* `NonUnitalStarSubalgebra.isClosed_corner`, `NonUnitalStarSubalgebra.isClosed_orthoCorner`:
  `IsClosed` instances for the fixed corner `s.corner hp` and orthogonal corner `s.orthoCorner hp`
  of a closed nonunital `⋆`-subalgebra.
* `NonUnitalStarAlgHom.denseRange_op`, `NonUnitalStarAlgHom.denseRange_unop`,
  `StarAlgHom.denseRange_op`, `StarAlgHom.denseRange_unop`: `@[simp]` density lemmas for opposite
  `⋆`-algebra homomorphisms.
* `NonUnitalStarSubalgebraClass.denseRange_subtype` and `denseRange_subtype_op`: the subtype
  inclusion of `s` (and its multiplicative opposite) has dense range iff `(s : Set A)` is dense.
* `ClosedSubmodule.starSubalgebra`, bundling the self-adjoint core `L ∩ star ⁻¹' L` of a closed
  submodule `L` absorbing left multiplication in `A` as a closed `NonUnitalStarSubalgebra R A`.
-/

public section

/-- `f.op : Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ` has dense range if and only if `f : A →⋆ₙₐ[R] B` does. -/
@[simp]
theorem NonUnitalStarAlgHom.denseRange_op {R A B : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B] [TopologicalSpace B]
    (f : A →⋆ₙₐ[R] B) : DenseRange f.op ↔ DenseRange f := by
  have h : ⇑f.op = MulOpposite.opHomeomorph ∘ (f ∘ MulOpposite.unop) := funext f.op_apply_apply
  rw [DenseRange, h, Set.range_comp, MulOpposite.unop_surjective.range_comp,
    MulOpposite.opHomeomorph.isDenseEmbedding.dense_image]
  rfl

/-- `NonUnitalStarAlgHom.unop f` has dense range if and only if `f` does. -/
@[simp]
theorem NonUnitalStarAlgHom.denseRange_unop {R A B : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B] [TopologicalSpace B]
    (f : Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ) : DenseRange (NonUnitalStarAlgHom.unop f) ↔ DenseRange f := by
  rw [← NonUnitalStarAlgHom.denseRange_op, Equiv.apply_symm_apply]

/-- `f.op : Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ` has dense range if and only if `f : A →⋆ₐ[R] B` does. -/
@[simp]
theorem StarAlgHom.denseRange_op {R A B : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B] [TopologicalSpace B]
    (f : A →⋆ₐ[R] B) : DenseRange f.op ↔ DenseRange f := by
  rw [← f.op.coe_toNonUnitalStarAlgHom, f.toNonUnitalStarAlgHom_op,
    NonUnitalStarAlgHom.denseRange_op, f.coe_toNonUnitalStarAlgHom]

/-- `StarAlgHom.unop f` has dense range if and only if `f` does. -/
@[simp]
theorem StarAlgHom.denseRange_unop {R A B : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B] [TopologicalSpace B]
    (f : Aᵐᵒᵖ →⋆ₐ[R] Bᵐᵒᵖ) : DenseRange (StarAlgHom.unop f) ↔ DenseRange f := by
  rw [← StarAlgHom.denseRange_op, Equiv.apply_symm_apply]

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

section Corner
variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [StarRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [TopologicalSpace A] [T2Space A] [ContinuousMul A]
/-- The fixed corner `s.corner hp` of a closed nonunital `⋆`-subalgebra is closed. -/
instance isClosed_corner (s : NonUnitalStarSubalgebra R A) [hs : IsClosed (s : Set A)]
    {p : A} (hp : IsSelfAdjoint p) : IsClosed (s.corner hp : Set A) :=
  coe_corner s hp ▸ hs.and ((isClosed_eq (continuous_const.mul continuous_id) continuous_id).and
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id))
/-- The orthogonal corner `s.orthoCorner hp` of a closed nonunital `⋆`-subalgebra is closed. -/
instance isClosed_orthoCorner (s : NonUnitalStarSubalgebra R A) [hs : IsClosed (s : Set A)]
    {p : A} (hp : IsSelfAdjoint p) : IsClosed (s.orthoCorner hp : Set A) :=
  coe_orthoCorner s hp ▸ hs.and ((isClosed_eq (continuous_const.mul continuous_id)
    continuous_const).and (isClosed_eq (continuous_id.mul continuous_const) continuous_const))
end Corner
end NonUnitalStarSubalgebra

namespace NonUnitalStarSubalgebraClass

variable {R A S : Type*} [CommSemiring R] [TopologicalSpace A]
  [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
  [SetLike S A] [NonUnitalSubsemiringClass S A] [SMulMemClass S R A] [StarMemClass S A]

/-- The subtype inclusion `NonUnitalStarSubalgebraClass.subtype s` has dense range if and only if
`(s : Set A)` is dense in `A`. -/
theorem denseRange_subtype (s : S) :
    DenseRange (NonUnitalStarSubalgebraClass.subtype s) ↔ Dense (s : Set A) := by
  rw [NonUnitalStarSubalgebraClass.coe_subtype, denseRange_subtypeVal, SetLike.setOfPred_mem_eq]

/-- The opposite subtype inclusion `(NonUnitalStarSubalgebraClass.subtype s).op` has dense range if
and only if `(s : Set A)` is dense in `A`. -/
theorem denseRange_subtype_op (s : S) :
    DenseRange (NonUnitalStarSubalgebraClass.subtype s).op ↔ Dense (s : Set A) :=
  (NonUnitalStarAlgHom.denseRange_op _).trans (denseRange_subtype s)

end NonUnitalStarSubalgebraClass

namespace ClosedSubmodule

variable {R A : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
  [Module R A] [StarModule R A] [TopologicalSpace A]

/-- The self-adjoint core `L ∩ star ⁻¹' L` of a closed left ideal `L` of `A`, bundled as a
`NonUnitalStarSubalgebra R A`. -/
def starSubalgebra (L : ClosedSubmodule R A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    NonUnitalStarSubalgebra R A where
  carrier := {x : A | x ∈ L ∧ star x ∈ L}
  mul_mem' {x y} hx hy :=
    ⟨hL x y hy.1, by rw [star_mul]; exact hL (star y) (star x) hx.2⟩
  add_mem' {x y} hx hy :=
    ⟨add_mem hx.1 hy.1, by rw [star_add]; exact add_mem hx.2 hy.2⟩
  zero_mem' := ⟨zero_mem L, by rw [star_zero]; exact zero_mem L⟩
  smul_mem' c {x} hx :=
    ⟨L.smul_mem c hx.1, by rw [star_smul]; exact L.smul_mem (star c) hx.2⟩
  star_mem' {x} hx := ⟨hx.2, by rw [star_star]; exact hx.1⟩

@[simp, grind =]
theorem mem_starSubalgebra {L : ClosedSubmodule R A} {hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L} {x : A} :
    x ∈ L.starSubalgebra hL ↔ x ∈ L ∧ star x ∈ L :=
  Iff.rfl

@[simp]
theorem coe_starSubalgebra (L : ClosedSubmodule R A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    (L.starSubalgebra hL : Set A) = (L : Set A) ∩ star ⁻¹' (L : Set A) :=
  (rfl)

instance isClosed_starSubalgebra [ContinuousStar A] (L : ClosedSubmodule R A)
    (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    IsClosed (L.starSubalgebra hL : Set A) := by
  rw [coe_starSubalgebra]
  exact L.isClosed.inter (L.isClosed.preimage continuous_star)

end ClosedSubmodule
