/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic
public import Mathlib.Algebra.Group.Graph

/-!
# Graphs of opposite-form isometries

An isometry from a finite quadratic module `A` to the negative of `B` has a
quadratic-isotropic graph in `A ⊥ B`. When `A` is nondegenerate, this graph equals its
orthogonal complement and is therefore Lagrangian. These graphs are the glue subgroups
used to place two even lattices with opposite discriminant forms in a unimodular overlattice.

The subgroup is Mathlib's `AddMonoidHom.graph`; no separate graph carrier is introduced.
Quadratic isotropy is characterized for arbitrary additive homomorphisms, including
degenerate modules, before the nondegenerate Lagrangian theorem.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.6.
-/

public section

namespace TauCeti.FiniteQuadraticModule

variable (A B : FiniteQuadraticModule)

/-- A homomorphism's graph is quadratic-isotropic exactly when it reverses quadratic values. -/
@[simp]
theorem isIsotropic_graph_iff (f : A →+ B) :
    (A.prod B).IsIsotropic f.graph ↔ ∀ x, B.quadratic (f x) = -A.quadratic x := by
  rw [isIsotropic_def]
  constructor
  · intro h x
    have hx := h (x, f x) (AddMonoidHom.mem_graph.mpr rfl)
    rw [prod_quadratic] at hx
    exact eq_neg_of_add_eq_zero_right hx
  · intro h ⟨x, y⟩ hx
    simp only [AddMonoidHom.mem_graph] at hx
    rw [prod_quadratic, ← hx, h, add_neg_cancel]

/-- An opposite-form equivalence's graph equals its orthogonal complement when the source
is nondegenerate. -/
@[simp]
theorem orthogonalComplement_graph (e : A ≃+ B)
    (he : ∀ x, B.quadratic (e x) = -A.quadratic x) (hA : A.IsNondegenerate) :
    (A.toFiniteBilinearModule.prod B.toFiniteBilinearModule).orthogonalComplement
        (e : A →+ B).graph =
      (e : A →+ B).graph := by
  apply le_antisymm
  · intro x hx
    apply AddMonoidHom.mem_graph.mpr
    have heq : x.1 = e.symm x.2 := by
      apply hA.injective
      ext y
      have h : A.toFiniteBilinearModule.pairing x.1 y +
          B.toFiniteBilinearModule.pairing x.2 (e y) = 0 :=
        ((A.prod B).toFiniteBilinearModule.mem_orthogonalComplement_iff _ x).mp hx
          (y, e y) (AddMonoidHom.mem_graph.mpr rfl)
      have hi := ((A.prod B).toFiniteBilinearModule.isIsotropic_def).mp
        (((A.isIsotropic_graph_iff B e.toAddMonoidHom).mpr he).toFiniteBilinearModule)
      have hp : A.toFiniteBilinearModule.pairing (e.symm x.2) y +
          B.toFiniteBilinearModule.pairing x.2 (e y) = 0 :=
        hi (e.symm x.2, x.2) (AddMonoidHom.mem_graph.mpr (e.apply_symm_apply x.2))
          (y, e y) (AddMonoidHom.mem_graph.mpr rfl)
      exact add_right_cancel (h.trans hp.symm)
    rw [heq]
    exact e.apply_symm_apply _
  · exact ((A.isIsotropic_graph_iff B e.toAddMonoidHom).mpr he).le_orthogonalComplement

/-- An additive equivalence's graph is Lagrangian exactly when it reverses quadratic values.
Nondegeneracy is required only of the source. -/
@[simp]
theorem isLagrangian_graph_iff (e : A ≃+ B) (hA : A.IsNondegenerate) :
    (A.prod B).IsLagrangian (e : A →+ B).graph ↔
      ∀ x, B.quadratic (e x) = -A.quadratic x := by
  constructor
  · intro h
    exact (A.isIsotropic_graph_iff B e.toAddMonoidHom).mp h.isIsotropic
  · intro he
    apply ((A.prod B).isLagrangian_def _).mpr
    exact ⟨(A.isIsotropic_graph_iff B e.toAddMonoidHom).mpr he,
      ((A.prod B).toFiniteBilinearModule.isLagrangian_def _).mpr
        (A.orthogonalComplement_graph B e he hA).symm⟩

end TauCeti.FiniteQuadraticModule
