/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Lattice
public import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Rank

import TauCeti.LinearAlgebra.Matrix.Rank
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Deciding a neighbor edge from a change of basis

Let `L` be an integral lattice spanned by a rational basis `b`, and `M` an integral lattice with
the same form spanned by a rational basis `c`. Write `A = b.toMatrix c` for the change-of-basis
matrix, whose columns are the vectors of `c` in the coordinates of `b`. Then `L` and `M` are
`p`-neighbors exactly when

* `p • A` has integer entries, that is `p M ⊆ L`;
* `|det A| = 1`, that is `[L : L ∩ M] = [M : L ∩ M]`;
* the column space of `p • A` reduced modulo `p` has exactly `p` elements.

The third condition computes `[M : L ∩ M]`. The vectors of `M` are `c`-integral combinations, and
such a vector lies in `L` exactly when its `b`-coordinates, which are `A` times its
`c`-coordinates, are integers. When `p • A` is integral this happens exactly when `p • A` times
the `c`-coordinates vanishes modulo `p`, so `M / (L ∩ M)` is the column space of `p • A` modulo
`p`. The second condition compares the two indices: both are absolute determinants against a
basis of `L ∩ M`, and these determinants differ by `det A`.

Each condition is a finite computation on the rational matrix `A`, so the predicate
`Matrix.IsNeighborBasisChange` is decidable, and one neighbor edge can be checked by kernel
evaluation with `decide +kernel`.
For a prime `p`, the third condition says that the reduction of `p • A` modulo `p` has rank one.

## Main definitions

* `Matrix.neighborReduction`: the reduction modulo `p` of the numerators of `p • A`.
* `Matrix.IsNeighborBasisChange`: the decidable edge test on a rational change-of-basis matrix.

## Main results

* `Module.Basis.relIndex_inf_span_eq_natCard_range`: if `p • b.toMatrix c` is integral, then the
  index of `span b ∩ span c` in `span c` is the size of the column space of
  `p • b.toMatrix c` modulo `p`.
* `TauCeti.IntegralLattice.isNeighbor_iff_isNeighborBasisChange`: `L` and `M` are `p`-neighbors
  exactly when their change-of-basis matrix passes the edge test.
* `Matrix.isNeighborBasisChange_iff_rank_eq_one`: for a prime `p`, the edge test asks for a
  reduction of rank one.

## References

* M. Kneser, *Klassenzahlen definiter quadratischer Formen*, Arch. Math. 8 (1957), 241--250.
* J. Voight, *Kneser's method of neighbors*, arXiv:2308.11566, §3.
-/

public section

open Module Submodule

namespace Matrix

variable {m n ι : Type*}

/-- The reduction modulo `p` of `p • A`, for a rational matrix `A`: its entries are the numerators
of the entries of `(p : ℚ) • A`, read in `ZMod p`. When `p • A` has integer entries, this is the
reduction of the integer matrix `p • A` modulo `p`. -/
@[expose]
def neighborReduction (A : Matrix m n ℚ) (p : ℕ) : Matrix m n (ZMod p) :=
  fun i j ↦ (((p : ℚ) * A i j).num : ZMod p)

/-- The entries of `A.neighborReduction p` are the numerators of the entries of `(p : ℚ) • A`,
read modulo `p`. -/
@[simp]
theorem neighborReduction_apply (A : Matrix m n ℚ) (p : ℕ) (i : m) (j : n) :
    A.neighborReduction p i j = (((p : ℚ) * A i j).num : ZMod p) :=
  rfl

variable [Fintype ι] [DecidableEq ι]

/-- **The edge test for Kneser neighbors.** A rational square matrix `A` passes the `p`-neighbor
test when `p • A` has integer entries, `A` has determinant `±1`, and the column space of `p • A`
modulo `p` has exactly `p` elements. By
`TauCeti.IntegralLattice.isNeighbor_iff_isNeighborBasisChange`, this says exactly that the
lattices spanned by two bases with change-of-basis matrix `A` are `p`-neighbors. -/
structure IsNeighborBasisChange (A : Matrix ι ι ℚ) (p : ℕ) : Prop where
  /-- The matrix `p • A` has integer entries. -/
  den_eq_one : ∀ i j, ((p : ℚ) * A i j).den = 1
  /-- The determinant of `A` is `±1`. -/
  abs_det_eq_one : |A.det| = 1
  /-- The column space of `p • A` modulo `p` has exactly `p` elements. -/
  natCard_range : Nat.card (Set.range (A.neighborReduction p).mulVec) = p

/-- The edge test is the conjunction of its three conditions. -/
theorem isNeighborBasisChange_iff {A : Matrix ι ι ℚ} {p : ℕ} :
    A.IsNeighborBasisChange p ↔ (∀ i j, ((p : ℚ) * A i j).den = 1) ∧ |A.det| = 1 ∧
      Nat.card (Set.range (A.neighborReduction p).mulVec) = p :=
  ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

/-- The edge test is decidable: each of its three conditions is a finite computation on `A`. -/
instance (A : Matrix ι ι ℚ) (p : ℕ) [NeZero p] : Decidable (A.IsNeighborBasisChange p) :=
  decidable_of_iff ((∀ i j, ((p : ℚ) * A i j).den = 1) ∧ |A.det| = 1 ∧
      Fintype.card (Set.range (A.neighborReduction p).mulVec) = p) <| by
    rw [← Nat.card_eq_fintype_card, isNeighborBasisChange_iff]

/-- For a prime `p`, the edge test asks that the reduction of `p • A` modulo `p` have rank one. -/
theorem isNeighborBasisChange_iff_rank_eq_one {A : Matrix ι ι ℚ} {p : ℕ} [hp : Fact p.Prime] :
    A.IsNeighborBasisChange p ↔
      (∀ i j, ((p : ℚ) * A i j).den = 1) ∧ |A.det| = 1 ∧ (A.neighborReduction p).rank = 1 := by
  rw [isNeighborBasisChange_iff, natCard_range_mulVec_eq_pow_rank, Nat.card_zmod,
    (Nat.pow_right_injective hp.out.two_le).eq_iff' (pow_one p)]

end Matrix

namespace Module.Basis

open Matrix

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]

/-- **The index of `span b ∩ span c` in `span c`, in coordinates.** If `p • b.toMatrix c` has
integer entries, then `span c / (span b ∩ span c)` is the column space of `p • b.toMatrix c`
modulo `p`. -/
theorem relIndex_inf_span_eq_natCard_range (b c : Basis ι ℚ V) {p : ℕ} [NeZero p]
    (hp : ∀ i j, ((p : ℚ) * b.toMatrix c i j).den = 1) :
    (span ℤ (Set.range b) ⊓ span ℤ (Set.range c)).toAddSubgroup.relIndex
        (span ℤ (Set.range c)).toAddSubgroup =
      Nat.card (Set.range ((b.toMatrix c).neighborReduction p).mulVec) := by
  set A := b.toMatrix c
  set R := A.neighborReduction p
  let cZ := c.restrictScalars ℤ
  -- The integer matrix `p • A`.
  let N : Matrix ι ι ℤ := fun i j ↦ ((p : ℚ) * A i j).num
  -- In `b`-coordinates, `p` times a vector of `span c` is `N` times its `c`-coordinates.
  have hrepr (x : span ℤ (Set.range c)) (i : ι) :
      (p : ℚ) * b.repr x i = ((N *ᵥ cZ.equivFun x) i : ℤ) := by
    rw [← Basis.toMatrix_mulVec_repr (b' := b) (b := c)]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Rat.coe_int_num_of_den_eq_one (hp i j), Basis.equivFun_apply,
      ← c.restrictScalars_repr_apply ℤ x j, algebraMap_int_eq, eq_intCast]
    ring
  -- The reduction map `span c → (ι → ZMod p)`, `x ↦ R (c-coordinates of x mod p)`.
  let ψ : span ℤ (Set.range c) →+ (ι → ZMod p) :=
    AddMonoidHom.mk' (fun x ↦ R *ᵥ (Int.castRingHom (ZMod p) ∘ cZ.equivFun x)) fun x y ↦ by
      rw [← Matrix.mulVec_add, map_add]
      congr 1
      ext j
      simp
  -- By definition of `neighborReduction`, `R` is the reduction of `N` modulo `p`.
  have hR : R = N.map (Int.castRingHom (ZMod p)) := rfl
  have hψ (x : span ℤ (Set.range c)) (i : ι) : ψ x i = ((N *ᵥ cZ.equivFun x) i : ℤ) := by
    rw [AddMonoidHom.mk'_apply, hR]
    exact (RingHom.map_mulVec (Int.castRingHom (ZMod p)) N _ i).symm
  -- Its kernel is the intersection with `span b`.
  have hker : (span ℤ (Set.range b) ⊓ span ℤ (Set.range c)).toAddSubgroup.addSubgroupOf
      (span ℤ (Set.range c)).toAddSubgroup = ψ.ker := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, Submodule.mem_inf,
      AddMonoidHom.mem_ker, b.mem_span_iff_repr_mem (R := ℤ), funext_iff]
    refine (and_iff_left x.2).trans <| forall_congr' fun i ↦ ?_
    rw [Pi.zero_apply, hψ, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hp₀ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have := hrepr x i
      rw [← hz, algebraMap_int_eq, eq_intCast] at this
      exact_mod_cast this.symm
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      rw [algebraMap_int_eq, eq_intCast]
      have := hrepr x i
      rw [hz, Int.cast_mul, Int.cast_natCast] at this
      exact mul_left_cancel₀ hp₀ this.symm
  -- Its range is the column space of `R`, since reduction of coordinates is surjective.
  have hrange : (ψ.range : Set (ι → ZMod p)) = Set.range R.mulVec := by
    rw [AddMonoidHom.coe_range]
    refine Function.Surjective.range_comp
      (f := fun x ↦ Int.castRingHom (ZMod p) ∘ cZ.equivFun x) (fun v ↦ ?_) R.mulVec
    refine ⟨cZ.equivFun.symm fun j ↦ ((v j).cast : ℤ), funext fun j ↦ ?_⟩
    simp only [Function.comp_apply, LinearEquiv.apply_symm_apply, eq_intCast,
      ZMod.intCast_zmod_cast]
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_ker, ← hrange, SetLike.coe_sort_coe]

end Module.Basis

namespace TauCeti.IntegralLattice

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℚ V]
  {L M : IntegralLattice V} {p : ℕ}

/-- **A decidable check for one neighbor edge.** Let `L` and `M` be integral lattices with the
same form, spanned by rational bases `b` and `c`. Then `L` and `M` are `p`-neighbors exactly when
the change-of-basis matrix `b.toMatrix c` passes the edge test `Matrix.IsNeighborBasisChange`:
`p • b.toMatrix c` is integral, `b.toMatrix c` has determinant `±1`, and the column space of
`p • b.toMatrix c` modulo `p` has `p` elements. -/
theorem isNeighbor_iff_isNeighborBasisChange [NeZero p] (b c : Basis ι ℚ V)
    (hL : L.carrier = span ℤ (Set.range b)) (hM : M.carrier = span ℤ (Set.range c))
    (hform : L.form = M.form) :
    L.IsNeighbor M p ↔ (b.toMatrix c).IsNeighborBasisChange p := by
  have hp₀ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  -- `[L : L ∩ M] = |det (b.toMatrix c)| · [M : L ∩ M]`.
  have hdet := Submodule.IsLattice.relIndex_span_eq_abs_det_mul (N := L.carrier ⊓ M.carrier) b c
    (hL ▸ inf_le_left) (hM ▸ inf_le_right)
  rw [← hL, ← hM, Basis.det_apply] at hdet
  have hcard (hp : ∀ i j, ((p : ℚ) * b.toMatrix c i j).den = 1) :
      (L.carrier ⊓ M.carrier).toAddSubgroup.relIndex M.carrier.toAddSubgroup =
        Nat.card (Set.range ((b.toMatrix c).neighborReduction p).mulVec) := by
    rw [hL, hM]
    exact b.relIndex_inf_span_eq_natCard_range c hp
  constructor
  · intro h
    have hden (i j : ι) : ((p : ℚ) * b.toMatrix c i j).den = 1 := by
      -- `M / (L ∩ M)` has order `p`, so `p • c j ∈ L`.
      have hcj : c j ∈ M.carrier := hM ▸ subset_span (Set.mem_range_self j)
      have hmem := AddSubgroup.nsmul_relIndex_mem (L.carrier ⊓ M.carrier).toAddSubgroup
        ((Submodule.mem_toAddSubgroup _).mpr hcj)
      rw [h.relIndex_inf_right, Submodule.mem_toAddSubgroup, Submodule.mem_inf, hL,
        b.mem_span_iff_repr_mem (R := ℤ)] at hmem
      obtain ⟨z, hz⟩ := hmem.1 i
      rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, ← Basis.toMatrix_apply,
        algebraMap_int_eq, eq_intCast] at hz
      rw [← hz, Rat.den_intCast]
    refine ⟨hden, ?_, (hcard hden).symm.trans h.relIndex_inf_right⟩
    rw [h.relIndex_inf_left, h.relIndex_inf_right] at hdet
    exact (mul_eq_right₀ hp₀).mp hdet.symm
  · rintro ⟨hden, habs, hrange⟩
    have hright := (hcard hden).trans hrange
    refine ⟨hform, ?_, hright⟩
    rw [hright, habs, one_mul] at hdet
    exact_mod_cast hdet

end TauCeti.IntegralLattice

/-- The change of basis from the standard basis of `ℚ²` to `(1/2, 0), (0, 2)` passes the
`2`-neighbor test: the intersection `ℤ (1, 0) + ℤ (0, 2)` of the two spans has index `2` in each.
So these spans are `2`-neighbors under any form making both of them integral lattices. -/
example : (!![1 / 2, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℚ).IsNeighborBasisChange 2 := by
  decide +kernel

/-- The same change of basis fails the `3`-neighbor test. -/
example : ¬ (!![1 / 2, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℚ).IsNeighborBasisChange 3 := by
  decide +kernel
