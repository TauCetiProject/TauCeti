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
edge sits in a type (I) simplex, and bounds the dimension of the type (I)
simplices from below.

## Main results

* `SSet.prodStdSimplex.pairingCore.Type₁.map_edge_of_index_eq_zero`: for the pairing of
  `(Λ[m + 2, 0] ⊗ Δ[n]) ∪ (Δ[m + 2] ⊗ ∂Δ[n])`, a type (I) simplex whose type (II) face is its first
  face starts with a vertical edge `(0, t) ⟶ (1, t)`.
* `SSet.prodStdSimplex.pairingCore.Type₁.exists_dim_eq_add_one`: for the same pairing, every
  type (I) simplex has dimension at least `2`.

## References

* S. Moss, *Another approach to the Kan-Quillen model structure*, J. Homotopy Relat. Struct. 15
  (2020).
-/

public section

universe u

open CategoryTheory Simplicial

namespace SSet.prodStdSimplex.pairingCore.Type₁

/-- A type (I) simplex of Moss's pairing for `(Λ[m + 2, 0] ⊗ Δ[n]) ∪ (Δ[m + 2] ⊗ ∂Δ[n])` whose
type (II) face is its first face starts with a vertical edge `(0, t) ⟶ (1, t)`. -/
lemma map_edge_of_index_eq_zero {m n : ℕ} (s : Type₁.{u} (0 : Fin (m + 2)) n)
    (hs : s.index = 0) :
    (yonedaEquiv.symm (s.x.cast s.hd).simplex).app _
        (stdSimplex.edge (s.d + 1) 0 1 (Fin.zero_le _)) =
      (stdSimplex.edge (m + 2) 0 1 (Fin.zero_le _),
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

/-- Every type (I) simplex of Moss's pairing for `(Λ[m + 2, 0] ⊗ Δ[n]) ∪ (Δ[m + 2] ⊗ ∂Δ[n])` has
dimension at least `2`. A `1`-simplex would have its first face as type (II) face, so its first
coordinate would start with the vertices `0` and `1` and also take the value `2`. -/
lemma exists_dim_eq_add_one {m n : ℕ} (s : Type₁.{u} (0 : Fin (m + 2)) n) :
    ∃ d, s.d = d + 1 := by
  refine Nat.exists_eq_add_one.2 (Nat.pos_of_ne_zero fun h0 ↦ ?_)
  have hs : s.index = 0 := Fin.ext (by have := s.index.isLt; omega)
  have h := s.isIndex
  rw [hs, pairingCore.isIndex_succ] at h
  obtain ⟨h₀, h₁, -⟩ := h
  have h₂ : 2 % (m + 1 + 2) = 2 := Nat.mod_eq_of_lt (by omega)
  have h₂' : 2 % (m + 1 + 1 + 1) = 2 := Nat.mod_eq_of_lt (by omega)
  obtain ⟨l, hl⟩ := pairingCore.mem_range_left s.x s.hd 2 (by simp [Fin.ext_iff, h₂])
  have hlt : l.val < s.d + 2 := l.isLt
  obtain h | h : l.val = 0 ∨ l.val = 1 := by omega
  · rw [show l = (0 : Fin (s.d + 1)).castSucc from Fin.ext h, h₀] at hl
    simp [Fin.ext_iff, h₂'] at hl
  · rw [show l = (0 : Fin (s.d + 1)).succ from Fin.ext h, h₁] at hl
    simp [Fin.ext_iff, h₂'] at hl

end SSet.prodStdSimplex.pairingCore.Type₁
