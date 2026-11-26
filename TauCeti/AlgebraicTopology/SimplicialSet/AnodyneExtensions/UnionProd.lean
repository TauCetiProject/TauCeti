/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd

/-!
# The pairing for the prism on a horn

Mathlib's `SSet.prodStdSimplex.pairingCore` is Moss's regular pairing for the inclusion
`(Λ[m + 1, k.castSucc] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n]) ⟶ Δ[m + 1] ⊗ Δ[n]`. Its type (I) simplices
contain a vertical edge `(k.castSucc, t) ⟶ (k.succ, t)` of the prism, and the paired type (II)
simplex is the face omitting the vertex `(k.castSucc, t)`. This file records where this vertical
edge sits in a type (I) simplex.

## Main results

* `SSet.prodStdSimplex.pairingCore.Type₁.map_edge_of_index_eq_zero`: for the pairing of
  `(Λ[m + 1, 0] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n])`, a type (I) simplex whose type (II) face is its first
  face starts with a vertical edge `(0, t) ⟶ (1, t)`.

## References

* S. Moss, *Another approach to the Kan-Quillen model structure*, J. Homotopy Relat. Struct. 15
  (2020).
-/

public section

universe u

open CategoryTheory Simplicial

namespace SSet.prodStdSimplex.pairingCore.Type₁

/-- A type (I) simplex of Moss's pairing for `(Λ[m + 1, 0] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n])` whose
type (II) face is its first face starts with a vertical edge `(0, t) ⟶ (1, t)`. -/
lemma map_edge_of_index_eq_zero {m n : ℕ} (s : Type₁.{u} (0 : Fin (m + 1)) n)
    (hs : s.index = 0) :
    (yonedaEquiv.symm (s.x.cast s.hd).simplex).app _
        (stdSimplex.edge (s.d + 1) 0 1 (Fin.zero_le _)) =
      (stdSimplex.edge (m + 1) 0 1 (Fin.zero_le _),
        stdSimplex.const n ((s.x.cast s.hd).simplex.2 0) _) := by
  have h := s.isIndex
  rw [hs, pairingCore.isIndex_succ] at h
  obtain ⟨h₀, h₁, h₂⟩ := h
  -- Both sides are compared on their vertex functions: the vertex `i` of the left-hand side is
  -- by definition the vertex `i` of the simplex, and `Fin.castSucc 0`, `Fin.succ 0` are `0`, `1`.
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i
  · exact congrArg Fin.val h₀
  · exact congrArg Fin.val h₁
  · rfl
  · exact congrArg Fin.val h₂

end SSet.prodStdSimplex.pairingCore.Type₁
