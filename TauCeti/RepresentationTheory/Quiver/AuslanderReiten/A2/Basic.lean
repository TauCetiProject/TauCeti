/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AuslanderReiten.Quiver
public import TauCeti.RepresentationTheory.Quiver.Kronecker.ArrowSpace

/-!
# The underlying Auslander–Reiten quiver of `A₂`

For the one-arrow quiver, the quiver of irreducible morphisms is the three-vertex mesh
`S₂ → P₁ → S₁`. The equivalence `a2VertexEquiv` lists its actual vertices, which are isomorphism
classes of finite-dimensional indecomposable representations, in the order `S₁`, `S₂`, `P₁`.
The arrow-count formula identifies both displayed arrows with multiplicity one and excludes every
other arrow,
including loops. It holds over every field.

This assembles the classification in `Kronecker.Indecomposable` and the irreducible-space
calculation in `Kronecker.ArrowSpace` with the basis-indexed quiver in `AuslanderReiten.Quiver`.
It describes the underlying quiver; it does not define the partial Auslander–Reiten translation.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. I (2006), IV.1.
-/

public section

namespace TauCeti.irreducibleMorphismQuiver

open CategoryTheory Quiver.Kronecker

universe u

variable (k : Type u) [Field k] (A : Type) [Unique A]

/-- The vertices of the one-arrow irreducible-morphism quiver, listed as `S₁`, `S₂`, `P₁`. -/
noncomputable def a2VertexEquiv :
    Fin 3 ≃ irreducibleMorphismQuiver.{u, 0, 0, u} k (Quiver.Kronecker A) :=
  (indecomposableKroneckerEquiv k A).trans equivSkeleton.symm

/-- Vertex zero is the class of the source simple `S₁`. -/
@[simp]
theorem a2VertexEquiv_zero :
    a2VertexEquiv k A 0 = of
      (isFinDim_iff.mpr fun v ↦
        finiteDimensional_simpleRep_obj (k := k) (src : Quiver.Kronecker A) v)
      (indecomposable_of_simple (simpleRep k (Quiver.Kronecker A) src)) := by
  simp only [a2VertexEquiv, Equiv.trans_apply, indecomposableKroneckerEquiv_zero]
  exact equivSkeleton_symm_toSkeleton _

/-- Vertex one is the class of the target simple `S₂`. -/
@[simp]
theorem a2VertexEquiv_one :
    a2VertexEquiv k A 1 = of
      (isFinDim_iff.mpr fun v ↦
        finiteDimensional_simpleRep_obj (k := k) (tgt : Quiver.Kronecker A) v)
      (indecomposable_of_simple (simpleRep k (Quiver.Kronecker A) tgt)) := by
  simp only [a2VertexEquiv, Equiv.trans_apply, indecomposableKroneckerEquiv_one]
  exact equivSkeleton_symm_toSkeleton _

/-- Vertex two is the class of the source projective `P₁`. -/
@[simp]
theorem a2VertexEquiv_two :
    a2VertexEquiv k A 2 = of
      (isFinDim_iff.mpr fun v ↦ by
        cases v <;> exact finiteDimensional_indecProjRep_obj (k := k) (src : Quiver.Kronecker A) _)
      (indecomposable_indecProjRep_of_isAcyclic (k := k) Quiver.Kronecker.isAcyclic src) := by
  simp only [a2VertexEquiv, Equiv.trans_apply, indecomposableKroneckerEquiv_two]
  exact equivSkeleton_symm_toSkeleton _

/-- With vertices listed as `S₁`, `S₂`, `P₁`, the only arrows are `1 → 2` and `2 → 0`,
each with multiplicity one. -/
@[simp↓]
theorem card_arrows_a2VertexEquiv (i j : Fin 3) :
    Nat.card (a2VertexEquiv k A i ⟶ a2VertexEquiv k A j) =
      if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 1 else 0 := by
  classical
  have hSS := not_nonempty_simpleRep_iso (k := k) (Q := Quiver.Kronecker A) src_ne_tgt
  have hSP := not_nonempty_simpleRep_indecProjRep_iso (k := k) (A := A)
  have hPS : ∀ v : Quiver.Kronecker A,
      ¬ Nonempty (indecProjRep k (Quiver.Kronecker A) src ≅
        simpleRep k (Quiver.Kronecker A) v) :=
    fun v h ↦ hSP v (h.map Iso.symm)
  have hTS : ¬ Nonempty (simpleRep k (Quiver.Kronecker A) tgt ≅
      simpleRep k (Quiver.Kronecker A) src) := fun h ↦ hSS (h.map Iso.symm)
  have cases : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases cases i with rfl | rfl | rfl <;> rcases cases j with rfl | rfl | rfl
  all_goals
    simp only [a2VertexEquiv_zero, a2VertexEquiv_one, a2VertexEquiv_two]
    rw [card_arrows_of]
    rw [finrank_irreducibleMorphismSpace_kronecker _ _
      (by first | exact indecomposable_of_simple _ |
        exact indecomposable_indecProjRep_of_isAcyclic Quiver.Kronecker.isAcyclic src)
      (by first | exact indecomposable_of_simple _ |
        exact indecomposable_indecProjRep_of_isAcyclic Quiver.Kronecker.isAcyclic src)]
    simp [hSS, hSP, hPS, hTS]

end TauCeti.irreducibleMorphismQuiver
