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
edge sits in a type (I) simplex, and bounds the dimension of the type (I) simplices from below.

## Main results

* `SSet.prodStdSimplex.pairingCore.Type₁.map_edge_of_index_eq_zero`: for the pairing of
  `(Λ[m + 1, 0] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n])`, a type (I) simplex whose type (II) face is its first
  face starts with the vertical edge `(0, 0) ⟶ (1, 0)`.
* `SSet.prodStdSimplex.pairingCore.Type₁.exists_dim_eq_add_one`: for the same pairing, when this
  vertical edge lies in `(Λ[m + 1, 0] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n])`, every type (I) simplex has
  dimension at least `2`.

## References

* S. Moss, *Another approach to the Kan-Quillen model structure*, J. Homotopy Relat. Struct. 15
  (2020).
-/

public section

universe u

open CategoryTheory Simplicial

namespace SSet.prodStdSimplex.pairingCore.Type₁

/-- A type (I) simplex of Moss's pairing for `(Λ[m + 1, 0] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n])` whose
type (II) face is its first face starts with the vertical edge `(0, 0) ⟶ (1, 0)`: its first two
vertices are `(0, t)` and `(1, t)`, and `t = 0` because the simplex, which does not lie in
`Δ[m + 1] ⊗ ∂Δ[n]`, lies over every vertex of `Δ[n]`. -/
lemma map_edge_of_index_eq_zero {m n : ℕ} (s : Type₁.{u} (0 : Fin (m + 1)) n)
    (hs : s.index = 0) :
    (yonedaEquiv.symm (s.x.cast s.hd).simplex).app _
        (stdSimplex.edge (s.d + 1) 0 1 (Fin.zero_le _)) =
      (stdSimplex.edge (m + 1) 0 1 (Fin.zero_le _), stdSimplex.const n 0 _) := by
  have h := s.isIndex
  rw [hs, pairingCore.isIndex_succ] at h
  obtain ⟨h₀, h₁, h₂⟩ := h
  have h0 : (s.x.cast s.hd).simplex.2 0 = 0 := by
    obtain ⟨i, hi⟩ := pairingCore.mem_range_right s.x s.hd 0
    exact le_antisymm ((stdSimplex.monotone_apply _ (Fin.zero_le i)).trans_eq hi) (Fin.zero_le _)
  -- Both sides are compared on their vertex functions: the vertex `i` of the left-hand side is
  -- by definition the vertex `i` of the simplex, and `Fin.castSucc 0`, `Fin.succ 0` are `0`, `1`.
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i
  · exact congrArg Fin.val h₀
  · exact congrArg Fin.val h₁
  · exact congrArg Fin.val h0
  · exact congrArg Fin.val (h₂.trans h0)

/-- When the vertical edge `(0, 0) ⟶ (1, 0)` lies in `(Λ[m + 1, 0] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n])`,
every type (I) simplex of Moss's pairing has dimension at least `2`. The type (II) face of a
`1`-simplex is its first face, so a type (I) `1`-simplex would be this edge
(`map_edge_of_index_eq_zero`), whereas type (I) simplices do not lie in the subcomplex. -/
lemma exists_dim_eq_add_one {m n : ℕ} (s : Type₁.{u} (0 : Fin (m + 1)) n)
    (hmem : (stdSimplex.edge (m + 1) 0 1 (Fin.zero_le _), stdSimplex.const n 0 _) ∈
      (Subcomplex.unionProd Λ[m + 1, 0] ∂Δ[n]).obj (Opposite.op ⦋1⦌)) :
    ∃ d, s.d = d + 1 := by
  obtain ⟨x, _ | d, hd, index, isIndex⟩ := s
  · refine absurd ?_ (x.cast hd).notMem
    have h := map_edge_of_index_eq_zero ⟨x, 0, hd, index, isIndex⟩
      (Subsingleton.elim (α := Fin 1) _ _)
    -- The edge `0 ⟶ 1` of `Δ[1]` is its identity simplex.
    rw [show stdSimplex.edge (0 + 1) 0 1 (Fin.zero_le _) = yonedaEquiv (𝟙 _) from
      (stdSimplex.objEquiv.symm_apply_eq.2 (by ext i; fin_cases i <;> rfl)),
      yonedaEquiv_symm_app_id] at h
    exact h ▸ hmem
  · exact ⟨d, rfl⟩

end SSet.prodStdSimplex.pairingCore.Type₁
