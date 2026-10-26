/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Basic

import Mathlib.LinearAlgebra.Dimension.Finite
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# The dimension of the special linear Lie algebra

The trace-zero matrices `sl n R` form a finite free module over any commutative ring. For a
nonempty finite index type, the entries away from one diagonal place are free coordinates: the
trace-zero condition determines the remaining entry as minus the sum of the other diagonal entries.
For an empty index type, `sl n R` is the zero module.

Over a nontrivial commutative ring, the strong rank condition gives
`finrank R (sl n R) = (Fintype.card n) ^ 2 - 1`. Truncated subtraction includes the empty case;
`TauCeti.finrank_sl_add_one` gives the untruncated formula when the index type is nonempty.

## Main results

* `TauCeti.finrank_sl`: `sl n R` has rank `(card n) ^ 2 - 1`.
* `TauCeti.finrank_sl_add_one`: the untruncated form, for a nonempty index type.
* `TauCeti.finrank_inf_sl_add_one`: over a field in which the size of the matrices is nonzero, a
  subspace of matrices containing the identity meets `sl n K` in codimension one.
* `TauCeti.finrank_ker_ad_sl_add_one`: applied to a centralizer, the centralizer of `x` in
  `sl n K` has codimension one in its centralizer in `gl n K`.

The same coordinate system also gives the `Module.Free` and `Module.Finite` instances for `sl n R`
that any rank computation involving it needs; over a commutative ring these do not come for free
from finiteness of the matrices.

## Implementation notes

A private linear equivalence identifies `sl n R` with the entries away from one diagonal place.
Freeness, finiteness and dimension follow by transporting the corresponding facts about this
function space. Membership is read through `LieAlgebra.SpecialLinear.mem_sl_iff`.
-/

public section

namespace TauCeti

open Matrix Module LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} {n : Type*} [Fintype n] [DecidableEq n]

section Coordinates

variable [CommRing R] (i₀ : n)

/-- The diagonal place `(k, k)`, for `k ≠ i₀`, as one of the free coordinates of a trace-zero
matrix. -/
private def diagIdx (k : {k : n // k ≠ i₀}) : {p : n × n // p ≠ (i₀, i₀)} :=
  ⟨(k.1, k.1), fun hk => k.2 (congrArg Prod.fst hk)⟩

/-- A trace-zero matrix is determined by its entries away from `(i₀, i₀)`. -/
private def slEquivFun : SpecialLinear.sl n R ≃ₗ[R] ({p : n × n // p ≠ (i₀, i₀)} → R) where
  toFun A p := A.val p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g := ⟨Matrix.of fun i j =>
    if h : (i, j) = (i₀, i₀) then -∑ k : {k : n // k ≠ i₀}, g (diagIdx i₀ k)
    else g ⟨(i, j), h⟩, by
      rw [SpecialLinear.mem_sl_iff]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply]
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
      simp only [Prod.mk.injEq, and_self, dite_true]
      apply neg_add_eq_zero.mpr
      apply Finset.sum_congr rfl
      intro k _
      rw [dite_eq_right k.property]
      rfl⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    simp only [Matrix.of_apply]
    split
    · rename_i h
      obtain ⟨hi, hj⟩ := Prod.mk.inj h
      subst i j
      have hA := SpecialLinear.mem_sl_iff.mp A.property
      simp only [Matrix.trace, Matrix.diag_apply] at hA
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀] at hA
      exact neg_eq_of_add_eq_zero_left hA
    · rfl
  right_inv g := by
    funext p
    exact dite_eq_right p.property

end Coordinates

section FreeFinite

variable [CommRing R]

/-- **`sl n R` is a free module.** For a nonempty index type the coordinates above are a basis of
it; for an empty one it is the zero module. -/
instance : Module.Free R (SpecialLinear.sl n R) := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · infer_instance
  · exact Module.Free.of_equiv (slEquivFun (R := R) i₀).symm

/-- **`sl n R` is a finite module**, the coordinates above being finite in number. -/
instance : Module.Finite R (SpecialLinear.sl n R) := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · infer_instance
  · exact Module.Finite.equiv (slEquivFun (R := R) i₀).symm

end FreeFinite

section Finrank

variable (R n) [CommRing R] [StrongRankCondition R]

/-- **The rank of `sl n R`**: `finrank R (sl n R) = (card n) ^ 2 - 1`.

For an empty index type the matrix algebra is trivial and both sides are `0`, the truncated
subtraction `0 - 1` doing the work. -/
@[simp]
theorem finrank_sl :
    finrank R (SpecialLinear.sl n R) = Fintype.card n ^ 2 - 1 := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · simp [Module.finrank_zero_of_subsingleton]
  · rw [(slEquivFun (R := R) i₀).finrank_eq]
    simp [Fintype.card_subtype_compl, sq]

variable [Nonempty n]

/-- The untruncated codimension-one statement: `sl n R` is a hyperplane in the matrices. -/
theorem finrank_sl_add_one :
    finrank R (SpecialLinear.sl n R) + 1 = Fintype.card n ^ 2 := by
  have hpos : 1 ≤ Fintype.card n ^ 2 := Nat.one_le_pow _ _ Fintype.card_pos
  rw [finrank_sl]
  omega

end Finrank

section Field

variable {K : Type*} [Field K]

/-- A subspace of square matrices containing the identity meets `sl n K` in codimension one, when
the size of the matrices is nonzero in `K`: the trace does not vanish on it, since the identity
has trace `Fintype.card n`. -/
theorem finrank_inf_sl_add_one (hn : (Fintype.card n : K) ≠ 0) {A : Submodule K (Matrix n n K)}
    (hA : (1 : Matrix n n K) ∈ A) :
    finrank K ↥(A ⊓ (SpecialLinear.sl n K).toSubmodule) + 1 = finrank K A := by
  have hsl : (SpecialLinear.sl n K).toSubmodule = LinearMap.ker (Matrix.traceLinearMap n K K) := by
    ext Y
    simp [SpecialLinear.mem_sl_iff]
  rw [inf_comm, hsl]
  exact Module.Dual.finrank_ker_inf_add_one fun h ↦ hn (by simpa using h hA)

/-- **Centralizers in `sl n` and `gl n`.** When the size of the matrices is nonzero in `K`, the
centralizer of `x ∈ sl n K` in `sl n K` has codimension one in its centralizer in `gl n K`. -/
theorem finrank_ker_ad_sl_add_one (hn : (Fintype.card n : K) ≠ 0) (x : SpecialLinear.sl n K) :
    finrank K (LinearMap.ker (ad K (SpecialLinear.sl n K) x)) + 1 =
      finrank K (LinearMap.ker (ad K (Matrix n n K) (x : Matrix n n K))) := by
  have hmap : (LinearMap.ker (ad K (SpecialLinear.sl n K) x)).map
      ((SpecialLinear.sl n K).incl : SpecialLinear.sl n K →ₗ[K] Matrix n n K) =
        LinearMap.ker (ad K (Matrix n n K) (x : Matrix n n K)) ⊓
          (SpecialLinear.sl n K).toSubmodule := by
    ext Y
    simp only [Submodule.mem_map, LinearMap.mem_ker, ad_apply, LieHom.coe_toLinearMap,
      LieSubalgebra.coe_incl, Submodule.mem_inf, LieSubalgebra.mem_toSubmodule]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by simpa using congrArg Subtype.val hy, y.2⟩
    · rintro ⟨hY, hYsl⟩
      exact ⟨⟨Y, hYsl⟩, Subtype.ext (by simpa using hY), rfl⟩
  have h1 : (1 : Matrix n n K) ∈ LinearMap.ker (ad K (Matrix n n K) (x : Matrix n n K)) := by
    simp [LieRing.of_associative_ring_bracket]
  rw [← finrank_inf_sl_add_one hn h1, ← hmap,
    (Submodule.equivMapOfInjective
      ((SpecialLinear.sl n K).incl : SpecialLinear.sl n K →ₗ[K] Matrix n n K)
      (fun _ _ h ↦ Subtype.ext h) _).finrank_eq]

end Field

end TauCeti
