/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Quotient coordinates from a complementary parametrization

If `A.coprod B` is invertible, every ambient vector has a unique decomposition
`A u + B w`. The second coordinate identifies the quotient by `range A` with the
fixed parameter space of `B`. In particular, when `A` varies and `B` stays fixed,
the quotient coordinates are read off from the inverse of a family of operators
between fixed spaces. This is useful for local coordinates on normal bundles.

The construction uses Mathlib's total continuous-linear inverse and continuous
quotient lift. No norm, completeness, or choice of an inner product is required.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition,
the normal-bundle construction preceding Theorem 6.24.
-/

public section

namespace ContinuousLinearMap

variable {R E F G : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F] [ContinuousAdd F]
  [TopologicalSpace G] [AddCommGroup G] [Module R G]
  {A : E →L[R] F} {B : G →L[R] F}

/-- The complementary coordinate of an ambient vector in the decomposition `A u + B w`.
It is zero when the coproduct is not invertible. -/
noncomputable def quotientRangeCoordinate (A : E →L[R] F) (B : G →L[R] F) : F →L[R] G :=
  snd R E G ∘L (A.coprod B).inverse

/-- The coordinate operator is the second component of the inverse coproduct. -/
theorem quotientRangeCoordinate_def (A : E →L[R] F) (B : G →L[R] F) :
    A.quotientRangeCoordinate B = snd R E G ∘L (A.coprod B).inverse :=
  (rfl)

/-- Tangent representatives have zero complementary coordinate. -/
@[simp] theorem quotientRangeCoordinate_apply_left (h : (A.coprod B).IsInvertible) (u : E) :
    A.quotientRangeCoordinate B (A u) = 0 := by
  have hi := h.inverse_apply_self (u, (0 : G))
  simpa [quotientRangeCoordinate] using congrArg Prod.snd hi

/-- A vector parametrized by the complement has its original complementary coordinate. -/
@[simp] theorem quotientRangeCoordinate_apply_right (h : (A.coprod B).IsInvertible) (w : G) :
    A.quotientRangeCoordinate B (B w) = w := by
  have hi := h.inverse_apply_self ((0 : E), w)
  simpa [quotientRangeCoordinate] using congrArg Prod.snd hi

/-- The complementary representative differs from the original vector by an element of
the range being quotiented out. -/
theorem sub_apply_quotientRangeCoordinate_mem_range (h : (A.coprod B).IsInvertible) (y : F) :
    y - B (A.quotientRangeCoordinate B y) ∈ A.range := by
  refine ⟨((A.coprod B).inverse y).1, ?_⟩
  have hi := h.self_apply_inverse y
  simpa [quotientRangeCoordinate, eq_sub_iff_add_eq] using hi

/-- The kernel of the complementary coordinate is exactly the range being quotiented out. -/
@[simp] theorem ker_quotientRangeCoordinate (h : (A.coprod B).IsInvertible) :
    (A.quotientRangeCoordinate B).ker = A.range := by
  apply le_antisymm
  · intro y hy
    have hm := sub_apply_quotientRangeCoordinate_mem_range h y
    have hy' : A.quotientRangeCoordinate B y = 0 := hy
    simpa only [hy', map_zero, sub_zero] using hm
  · rintro y ⟨u, rfl⟩
    exact quotientRangeCoordinate_apply_left h u

/-- The quotient of the ambient space by `range A`, parametrized by a fixed complementary
map `B`. The forward map takes complementary coordinates and the inverse takes the class
of `B w`. -/
noncomputable def quotientRangeEquiv (A : E →L[R] F) (B : G →L[R] F)
    (h : (A.coprod B).IsInvertible) : (F ⧸ A.range) ≃L[R] G :=
  ContinuousLinearEquiv.equivOfInverse
    (A.range.liftQL (A.quotientRangeCoordinate B)
      (by rw [ker_quotientRangeCoordinate h]))
    (A.range.mkQL ∘L B)
    (fun z => by
      obtain ⟨y, rfl⟩ := A.range.mkQ_surjective z
      simp only [comp_apply, Submodule.liftQL_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]
      apply (Submodule.Quotient.eq A.range).mpr
      simpa only [neg_sub, ContinuousLinearMap.coe_coe] using
        A.range.neg_mem (sub_apply_quotientRangeCoordinate_mem_range h y))
    (fun w => by simp [quotientRangeCoordinate_apply_right h])

/-- On an ambient representative, the quotient equivalence reads the second inverse
coordinate. -/
@[simp] theorem quotientRangeEquiv_apply_mk (h : (A.coprod B).IsInvertible) (y : F) :
    A.quotientRangeEquiv B h (Submodule.Quotient.mk y) = A.quotientRangeCoordinate B y :=
  (rfl)

/-- The inverse quotient equivalence takes the class of the fixed complementary map. -/
@[simp] theorem quotientRangeEquiv_symm_apply (h : (A.coprod B).IsInvertible) (w : G) :
    (A.quotientRangeEquiv B h).symm w = Submodule.Quotient.mk (B w) :=
  (rfl)

variable {G' : Type*} [TopologicalSpace G'] [AddCommGroup G'] [Module R G']
  {C : G' →L[R] F}

/-- Changing complementary representatives preserves all quotient coordinates.
This identifies the transition from the `B` coordinates to the `C` coordinates. -/
@[simp] theorem quotientRangeCoordinate_comp_quotientRangeCoordinate
    (hB : (A.coprod B).IsInvertible) (hC : (A.coprod C).IsInvertible) :
    (A.quotientRangeCoordinate C ∘L B) ∘L A.quotientRangeCoordinate B =
      A.quotientRangeCoordinate C := by
  ext y
  have he := congrArg (A.quotientRangeEquiv C hC)
    ((A.quotientRangeEquiv B hB).symm_apply_apply (Submodule.Quotient.mk y))
  simpa using he

/-- Transitions between two valid complementary parametrizations are invertible. -/
theorem isInvertible_quotientRangeCoordinate_comp
    (hB : (A.coprod B).IsInvertible) (hC : (A.coprod C).IsInvertible) :
    (A.quotientRangeCoordinate C ∘L B).IsInvertible := by
  refine .of_inverse (g := A.quotientRangeCoordinate B ∘L C) ?_ ?_
  · rw [← ContinuousLinearMap.comp_assoc,
      quotientRangeCoordinate_comp_quotientRangeCoordinate hB hC]
    ext w
    exact quotientRangeCoordinate_apply_right hC w
  · rw [← ContinuousLinearMap.comp_assoc,
      quotientRangeCoordinate_comp_quotientRangeCoordinate hC hB]
    ext w
    exact quotientRangeCoordinate_apply_right hB w

end ContinuousLinearMap
