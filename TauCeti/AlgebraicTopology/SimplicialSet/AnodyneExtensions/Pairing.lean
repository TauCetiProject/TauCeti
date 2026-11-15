/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PairingCore

/-!
# Face indices of pairings

If a simplex `x` of a simplicial set is uniquely a codimension one face of a simplex `y`, the
index `hxy.index hd` is the unique `i` with `δ i y = x`. Which horns a pairing of a subcomplex
(in the sense of Moss) attaches is read off from these indices: a regular pairing only involving
horns `Λ[n, i]` with `i ≠ n` (resp. `i ≠ 0`) exhibits a left (resp. right) anodyne extension.
This file computes the indices of the pairings built from `PairingCore` and of opposite pairings,
where passing to the opposite simplicial set reverses the order of the vertices and hence the
index.

## Main results

* `SSet.S.IsUniquelyCodimOneFace.index_op`: the index of the opposite face is reversed.
* `SSet.Subcomplex.Pairing.index_op`: the same for the opposite of a pairing.
* `SSet.Subcomplex.PairingCore.index_pairing_equivII`: the indices of the pairing attached to
  `h : A.PairingCore` are the indices `h.index`.

## References

* S. Moss, *Another approach to the Kan-Quillen model structure*, J. Homotopy Relat. Struct. 15
  (2020).
-/

public section

universe u

open CategoryTheory

open scoped Simplicial

namespace SSet

namespace S.IsUniquelyCodimOneFace

variable {X : SSet.{u}} {x y : X.S} (hxy : IsUniquelyCodimOneFace x y)

/-- The index of a codimension one face depends only on the two simplices. -/
lemma index_congr {x' y' : X.S} (hxy' : IsUniquelyCodimOneFace x' y') (hx : x = x')
    (hy : y = y') {d : ℕ} (hd : x.dim = d) (hd' : x'.dim = d) :
    hxy.index hd = hxy'.index hd' := by
  subst hx hy
  rfl

/-- In the opposite simplicial set, the index of a codimension one face is reversed. -/
lemma index_op {d : ℕ} (hd : x.dim = d) (hd' : (S.opEquiv.symm x).dim = d) :
    hxy.op.index hd' = (hxy.index hd).rev := by
  obtain ⟨d', x, rfl⟩ := x.mk_surjective
  obtain ⟨d'', y, rfl⟩ := y.mk_surjective
  obtain rfl : d'' = d' + 1 := hxy.dim_eq
  obtain rfl : d' = d := hd
  have h : IsUniquelyCodimOneFace (S.mk (opObjEquiv.symm x)) (S.mk (opObjEquiv.symm y)) :=
    hxy.op
  rw [index_congr hxy.op h rfl rfl hd' rfl, eq_comm, ← h.δ_eq_iff rfl, cast_simplex_rfl,
    cast_simplex_rfl, op_δ, Fin.rev_rev, Equiv.apply_symm_apply, dsimp% hxy.δ_index rfl]

end S.IsUniquelyCodimOneFace

namespace Subcomplex

variable {X : SSet.{u}} {A : X.Subcomplex}

/-- The indices of the opposite of a pairing are reversed. -/
lemma Pairing.index_op (P : A.Pairing) [P.IsProper] (x : P.II) {d : ℕ} (hd : x.1.dim = d)
    (hd' : (N.opEquiv.symm x.1).dim = d) :
    (P.op.isUniquelyCodimOneFace ⟨N.opEquiv.symm x.1, x.2⟩).index hd' =
      ((P.isUniquelyCodimOneFace x).index hd).rev := by
  rw [← (P.isUniquelyCodimOneFace x).index_op hd hd']
  exact S.IsUniquelyCodimOneFace.index_congr _ _ rfl (by rw [op_p]; rfl) _ _

/-- The indices of the pairing attached to `h : A.PairingCore` are given by `h.index`. -/
lemma PairingCore.index_pairing_equivII (h : A.PairingCore) [h.IsProper] (s : h.ι) :
    (h.pairing.isUniquelyCodimOneFace (h.equivII s)).index rfl = h.index s := by
  rw [← h.isUniquelyCodimOneFace_index s]
  exact S.IsUniquelyCodimOneFace.index_congr _ _ (by simp) (by simp) _ _

end Subcomplex

end SSet
