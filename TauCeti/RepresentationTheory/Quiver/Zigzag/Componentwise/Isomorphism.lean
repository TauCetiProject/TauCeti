/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Grading
import all TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Basic

/-!
# Graded graph invariance of the public zigzag algebra

The canonical graph-isomorphism comparison of componentwise zigzag algebras preserves
their grading. On components with an edge it transports path length through the relation
quotient; on singleton components it fixes the dual-number generator, whose degree is two.
Thus the comparison applies to disconnected graphs and isolated vertices as well.

The membership formulas below cover both the nonnegative and integer-indexed gradings.
The image formula identifies the entire homogeneous submodules, so the comparison can
be used to transport graded modules and their internal shifts without choosing incident edges.

See Huerfano–Khovanov, *A category for the adjoint representation*, Section 3, for the
path grading and the exceptional singleton convention.
-/

public section

namespace TauCeti

universe u v w

variable (k : Type w) [CommRing k] {V : Type u} {W : Type v}
  [Finite V] [Finite W] (G : SimpleGraph V) {H : SimpleGraph W}

/-- Graph relabelling preserves and reflects each graded piece of a component algebra,
including the degree-two generator on a singleton component. -/
@[simp]
theorem zigzagComponentAlgebraEquiv_mem_zigzagComponentGrade_iff
    (e : G ≃g H) (C : G.ConnectedComponent) {n : ℕ}
    {x : zigzagComponentAlgebra k G C} :
    zigzagComponentAlgebraEquiv k G e C x ∈
        zigzagComponentGrade k H (e.connectedComponentEquiv C) n ↔
      x ∈ zigzagComponentGrade k G C n := by
  classical
  rcases subsingleton_or_nontrivial C with hC | hC
  · let : Subsingleton (e.connectedComponentEquiv C) :=
      (Equiv.subsingleton_congr (C.isoEquivSupp e)).mp hC
    rw [zigzagComponentAlgebraEquiv_of_subsingleton]
    simp only [mem_zigzagComponentGrade_of_subsingleton, AlgEquiv.trans_apply,
      AlgEquiv.apply_symm_apply, ULift.algEquiv_apply, ULift.algEquiv_symm_apply,
      ULift.down_up]
  · let : Nontrivial (e.connectedComponentEquiv C) :=
      (Equiv.nontrivial_congr (C.isoEquivSupp e)).mp hC
    rw [zigzagComponentAlgebraEquiv_of_nontrivial]
    simp only [mem_zigzagComponentGrade_of_nontrivial, AlgEquiv.trans_apply,
      AlgEquiv.apply_symm_apply, nonisolatedZigzagQuotientEquiv_mem_zigzagGrade_iff]

/-- The canonical graph-isomorphism comparison of public zigzag algebras is graded.
No connectedness or absence of isolated vertices is required. -/
@[simp]
theorem zigzagAlgebraEquiv_mem_zigzagAlgebraGrade_iff (e : G ≃g H) {n : ℕ}
    {x : zigzagAlgebra k G} :
    zigzagAlgebraEquiv k G e x ∈ zigzagAlgebraGrade k H n ↔
      x ∈ zigzagAlgebraGrade k G n := by
  simp only [mem_zigzagAlgebraGrade]
  constructor
  · intro hx C
    have h := hx (e.connectedComponentEquiv C)
    rwa [zigzagAlgebraEquiv_apply_component,
      zigzagComponentAlgebraEquiv_mem_zigzagComponentGrade_iff] at h
  · intro hx D
    obtain ⟨C, rfl⟩ := e.connectedComponentEquiv.surjective D
    rw [zigzagAlgebraEquiv_apply_component,
      zigzagComponentAlgebraEquiv_mem_zigzagComponentGrade_iff]
    exact hx C

/-- The image of a homogeneous submodule under graph relabelling is precisely the
homogeneous submodule of the same degree. -/
theorem map_zigzagAlgebraGrade_zigzagAlgebraEquiv (e : G ≃g H) (n : ℕ) :
    (zigzagAlgebraGrade k G n).map (zigzagAlgebraEquiv k G e).toLinearMap =
      zigzagAlgebraGrade k H n := by
  ext x
  obtain ⟨y, rfl⟩ := (zigzagAlgebraEquiv k G e).surjective x
  rw [Submodule.mem_map_equiv, zigzagAlgebraEquiv_mem_zigzagAlgebraGrade_iff]
  simp only [AlgEquiv.coe_symm_toLinearEquiv, AlgEquiv.symm_apply_apply]

/-- The graph-isomorphism comparison preserves the signed grading used for internal shifts. -/
@[simp]
theorem zigzagAlgebraEquiv_mem_zigzagAlgebraIntegerGrade_iff (e : G ≃g H) {d : ℤ}
    {x : zigzagAlgebra k G} :
    zigzagAlgebraEquiv k G e x ∈ zigzagAlgebraIntegerGrade k H d ↔
      x ∈ zigzagAlgebraIntegerGrade k G d := by
  by_cases hd : 0 ≤ d
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    simp only [zigzagAlgebraIntegerGrade_ofNat, zigzagAlgebraEquiv_mem_zigzagAlgebraGrade_iff]
  · simp only [zigzagAlgebraIntegerGrade_eq_bot_of_neg _ _ (lt_of_not_ge hd),
      Submodule.mem_bot, EmbeddingLike.map_eq_zero_iff]

end TauCeti
