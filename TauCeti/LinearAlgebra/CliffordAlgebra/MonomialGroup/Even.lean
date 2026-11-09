/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import TauCeti.LinearAlgebra.CliffordAlgebra.MonomialGroup.Basic
-- Non-public: `CliffordAlgebra.neZeroTwo` gives `2 ≠ 0`, which shows an even signed monomial is
-- not also odd.
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic
-- Non-public: `CliffordAlgebra.involute_eq_self_iff` identifies the even signed monomials with
-- those in the even subalgebra.
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.Tactic.LinearCombination

/-!
# The even signed monomials of a Clifford algebra

The grade involution of a Clifford algebra restricts to an automorphism
`CliffordAlgebra.monomialGroupInvolute` of the group of signed monomials
`CliffordAlgebra.monomialGroup Q v`. Every signed monomial is homogeneous
(`CliffordAlgebra.involute_eq_or_eq_neg_of_mem_monomialGroup`), so the involution fixes or negates
it; the fixed ones form the subgroup `CliffordAlgebra.monomialGroupEven Q v` of even signed
monomials. Let `b` be an orthogonal basis whose generators square to `±1`, over a nontrivial ring
in which `2` is invertible. Then these are the `±e_s` with `#s` even, and they span the even
Clifford subalgebra. When `b` is moreover finite and nonempty, with `n` elements, they form a
subgroup of index two and of order `2 ^ n`; for the empty basis every signed monomial is even.

## Main definitions

* `CliffordAlgebra.monomialGroupEven`: the even signed monomials, the subgroup fixed by the grade
  involution.

## Main results

* `CliffordAlgebra.mem_monomialGroupEven_iff_mem_even` and
  `CliffordAlgebra.monomialGroupEquiv_mem_monomialGroupEven_iff`: the even signed monomials are
  those in the even Clifford subalgebra, the `±e_s` with `#s` even.
* `CliffordAlgebra.index_monomialGroupEven` and `CliffordAlgebra.natCard_monomialGroupEven`: over
  a nontrivial ring in which `2` is invertible, they form a subgroup of index two as soon as one
  generator squares to a unit, and of order `2 ^ n` for a nonempty finite orthogonal basis of `n`
  generators squaring to `±1`.
* `CliffordAlgebra.span_monomialGroupEven_eq_even`: they span the even Clifford subalgebra.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1.
-/

public section

namespace CliffordAlgebra

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}

variable {v : I → M}

variable (Q) in
/-- **The even signed monomials**: the subgroup of the group of signed monomials fixed by the grade
involution `CliffordAlgebra.monomialGroupInvolute`. Once `2` is invertible these are the signed
monomials lying in the even Clifford subalgebra
(`CliffordAlgebra.mem_monomialGroupEven_iff_mem_even`), and for an orthogonal basis they are the
`±e_s` with `#s` even (`CliffordAlgebra.monomialGroupEquiv_mem_monomialGroupEven_iff`). -/
noncomputable def monomialGroupEven (v : I → M) : Subgroup (monomialGroup Q v) :=
  (monomialGroupInvolute v).toMonoidHom.eqLocus (MonoidHom.id _)

/-- A signed monomial is even exactly when the grade involution fixes its value. -/
theorem mem_monomialGroupEven_iff {g : monomialGroup Q v} :
    g ∈ monomialGroupEven Q v ↔
      involute ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  rw [← coe_monomialGroupInvolute_apply, ← Units.ext_iff, ← Subtype.ext_iff]
  -- Membership in `MonoidHom.eqLocus f g` is the equation `f x = g x` by definition.
  exact Iff.rfl

/-- The central element `ε = -1` is even. -/
@[simp]
theorem monomialGroupEpsilon_mem_monomialGroupEven :
    monomialGroupEpsilon Q v ∈ monomialGroupEven Q v := by
  simp [mem_monomialGroupEven_iff]

variable [Invertible (2 : R)]

/-- **The even signed monomials are those in the even Clifford subalgebra**, once `2` is
invertible. -/
theorem mem_monomialGroupEven_iff_mem_even {g : monomialGroup Q v} :
    g ∈ monomialGroupEven Q v ↔ ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ even Q := by
  rw [mem_monomialGroupEven_iff, involute_eq_self_iff, ← even_toSubmodule,
    Subalgebra.mem_toSubmodule]

/-- A signed monomial is not even exactly when the grade involution negates its value, over a
nontrivial ring in which `2` is invertible. -/
theorem notMem_monomialGroupEven_iff [Nontrivial R] {g : monomialGroup Q v} :
    g ∉ monomialGroupEven Q v ↔
      involute ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        -((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  rw [mem_monomialGroupEven_iff]
  refine ⟨(involute_eq_or_eq_neg_of_mem_monomialGroup g.2).resolve_left, fun h h' ↦ ?_⟩
  -- A unit equal to its negative would make `2` vanish in the Clifford algebra.
  have h2 : (2 : CliffordAlgebra Q) * ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = 0 := by
    rw [two_mul]
    nth_rewrite 1 [← h.symm.trans h']
    exact neg_add_cancel _
  exact two_ne_zero ((Units.mul_left_eq_zero _).mp h2)

/-- **The even signed monomials have index two** as soon as one generator squares to a unit, over a
nontrivial ring in which `2` is invertible: multiplying by that odd generator exchanges the even
and the odd signed monomials. -/
theorem index_monomialGroupEven [Nontrivial R] {i : I} (hi : IsUnit (Q (v i))) :
    (monomialGroupEven Q v).index = 2 := by
  obtain ⟨a, ha⟩ := exists_monomialGroup_val_eq_ι v hi
  have hodd : involute ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      -((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
    rw [ha, involute_ι]
  refine Subgroup.index_eq_two_iff.mpr ⟨a, fun g ↦ ?_⟩
  have hmul : involute (((g * a : monomialGroup Q v) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      -(involute ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) := by
    simp only [Subgroup.coe_mul, Units.val_mul, map_mul, hodd, mul_neg]
  by_cases hg : g ∈ monomialGroupEven Q v
  · refine Or.inr ⟨hg, ?_⟩
    rw [notMem_monomialGroupEven_iff, hmul, mem_monomialGroupEven_iff.mp hg]
    simp
  · refine Or.inl ⟨?_, hg⟩
    rw [mem_monomialGroupEven_iff, hmul, notMem_monomialGroupEven_iff.mp hg]
    simp

/-! ### The even signed monomials of an orthogonal basis -/

variable [LinearOrder I] {b : Module.Basis I R M}

/-- **The even signed monomials are the `±e_s` with `#s` even**, for an orthogonal basis whose
generators square to `±1` over a nontrivial ring in which `2` is invertible. -/
@[simp]
theorem monomialGroupEquiv_mem_monomialGroupEven_iff [Nontrivial R]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (p : Finset I × ℤˣ) :
    monomialGroupEquiv hb hQ p ∈ monomialGroupEven Q b ↔ Even p.1.card := by
  have hinv : involute (((monomialGroupEquiv hb hQ p : monomialGroup Q b) :
      (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      (-1 : R) ^ p.1.card • ((monomialGroupEquiv hb hQ p : monomialGroup Q b) :
        (CliffordAlgebra Q)ˣ) := by
    rw [coe_monomialGroupEquiv_apply, map_zsmul, involute_basis hb, smul_comm]
  rcases Nat.even_or_odd p.1.card with h | h
  · rw [mem_monomialGroupEven_iff, hinv, h.neg_one_pow, one_smul]
    exact iff_of_true rfl h
  · refine iff_of_false (notMem_monomialGroupEven_iff.mpr ?_) (Nat.not_even_iff_odd.mpr h)
    rw [hinv, h.neg_one_pow, neg_one_smul]

/-- **The even signed monomials span the even Clifford subalgebra**, for an orthogonal basis whose
generators square to `±1`, once `2` is invertible: the even subalgebra has the `e_s` with `#s` even
as a basis, and each of them is an even signed monomial. -/
theorem span_monomialGroupEven_eq_even (hb : (QuadraticMap.associated Q).IsOrthoᵢ b)
    (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1) :
    Submodule.span R (Set.range fun g : monomialGroupEven Q b ↦
      (((g : monomialGroup Q b) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
      (even Q).toSubmodule := by
  refine le_antisymm (Submodule.span_le.mpr ?_) fun x hx ↦ ?_
  · rintro _ ⟨g, rfl⟩
    exact mem_monomialGroupEven_iff_mem_even.mp g.2
  -- Expand `x` in the basis `e_s`; only the terms with `#s` even survive.
  have hx' : involute x = x := involute_eq_of_mem_even (by rwa [← even_toSubmodule])
  rw [← (basis Q b).linearCombination_repr x, Finsupp.linearCombination_apply]
  refine Submodule.finsuppSum_mem _ _ _ _ fun s _ ↦ ?_
  rcases Nat.even_or_odd s.card with h | h
  · obtain ⟨u, hu⟩ := exists_monomialGroup_val_eq_basis hb hQ s
    have hu' : u ∈ monomialGroupEven Q b := by
      rw [mem_monomialGroupEven_iff, hu, involute_basis hb, h.neg_one_pow, one_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨u, hu'⟩, hu⟩)
  · -- The coordinate of `x` at an odd `s` is its own negative, hence zero.
    have h2 : (2 : R) * (basis Q b).repr x s = 0 := by
      have := basis_repr_involute hb x s
      rw [hx', h.neg_one_pow] at this
      linear_combination this
    rw [(isUnit_of_invertible (2 : R)).mul_right_eq_zero.mp h2, zero_smul]
    exact zero_mem _

/-- **The order of the even signed monomials**: for a nonempty finite orthogonal basis of `n`
generators squaring to `±1`, over a nontrivial ring in which `2` is invertible, there are
`2 ^ n` of them, half of the group of signed monomials. -/
theorem natCard_monomialGroupEven [Fintype I] [Nonempty I] [Nontrivial R]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1) :
    Nat.card (monomialGroupEven Q b) = 2 ^ Fintype.card I := by
  have h := (monomialGroupEven Q b).card_mul_index
  rw [index_monomialGroupEven (i := Classical.arbitrary I)
    (by rcases hQ (Classical.arbitrary I) with h | h <;> simp [h]),
    natCard_monomialGroup hb hQ, pow_succ] at h
  exact Nat.eq_of_mul_eq_mul_right two_pos h

end CliffordAlgebra
