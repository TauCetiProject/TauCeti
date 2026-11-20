/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra

/-!
# Topological closures and self-adjoint cores for nonunital star subalgebras

This file provides:
* `NonUnitalStarSubalgebra.topologicalClosure_coe`, the `@[simp]` lemma identifying the underlying
  set of `s.topologicalClosure` with `closure (s : Set A)`, matching
  `StarSubalgebra.topologicalClosure_coe`;
* `ClosedSubmodule.starSubalgebra`, bundling the self-adjoint core `L ∩ star ⁻¹' L` of a closed
  submodule `L` absorbing left multiplication in `A` as a closed `NonUnitalStarSubalgebra R A`.
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
