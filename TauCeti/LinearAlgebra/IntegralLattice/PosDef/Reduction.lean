/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.SuccessiveMinima
import Mathlib.LinearAlgebra.Transvection.Basic
import TauCeti.Algebra.Module.Primitive

/-!
# Minkowski-reduced bases of integral lattices

An ordered basis `b 0, …, b (n - 1)` of an integral lattice `L` is **Minkowski reduced** if, for
every index `i`, the vector `b i` has least norm among all vectors `x` such that
`b 0, …, b (i - 1), x` extends to a basis of `L`. We phrase this as a comparison with every basis
that agrees with `b` before `i` (`TauCeti.IntegralLattice.IsMinkowskiReduced`).

Every positive semidefinite lattice has a Minkowski-reduced basis: norms of lattice vectors are
then natural numbers, so the vectors can be chosen greedily, one index at a time. Comparing a
reduced basis with the bases obtained by exchanging two of its vectors, or by adding to `b j` a
vector in the span of the others, gives the elementary reduction inequalities: the norms
`β(b i, b i)` are nondecreasing, and `2 |β(b i, b j)| ≤ β(b i, b i)` for `i ≠ j`. The first
vector of a reduced basis is a minimal vector, and the `i`-th vector has norm at least the
`i`-th successive minimum.

In terms of the Gram matrix `L.gramMatrix b` of a reduced basis, the diagonal is nondecreasing
and each off-diagonal entry is at most half of the smaller of the two corresponding diagonal
entries in absolute value. These are the inequalities from which, together with a bound on the
product of the diagonal entries by the determinant, reduction theory bounds every entry of a
reduced Gram matrix of a positive definite lattice in terms of its rank and determinant.

## Main declarations

* `TauCeti.IntegralLattice.IsMinkowskiReduced`: Minkowski-reduced bases, unfolded by
  `TauCeti.IntegralLattice.isMinkowskiReduced_def`.
* `TauCeti.IntegralLattice.IsPosSemidef.exists_isMinkowskiReduced`: existence.
* `TauCeti.IntegralLattice.IsMinkowskiReduced.integralNorm_le_integralNorm_add`: the norm of `b j`
  does not decrease when a vector in the span of the other basis vectors is added to it.
* `TauCeti.IntegralLattice.IsMinkowskiReduced.monotone_integralNorm` and
  `TauCeti.IntegralLattice.IsMinkowskiReduced.two_mul_abs_integralForm_le`: the elementary
  reduction inequalities.
* `TauCeti.IntegralLattice.IsMinkowskiReduced.integralNorm_zero_eq_minimum` and
  `TauCeti.IntegralLattice.IsMinkowskiReduced.successiveMinimum_le_integralNorm`: comparison
  with the minimum and the successive minima.

## References

* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 12, §1.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §10.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u
variable {V : Type u} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

/-- A basis `b` of an integral lattice is **Minkowski reduced** if for every index `i`, the norm
of `b i` is at most the norm of the `i`-th vector of every basis that agrees with `b` before `i`.
Equivalently, `b i` has least norm among the vectors `x` such that `b 0, …, b (i - 1), x` extends
to a basis. -/
def IsMinkowskiReduced (L : IntegralLattice V) {n : ℕ} (b : Basis (Fin n) ℤ L) : Prop :=
  ∀ (i : Fin n) (e : Basis (Fin n) ℤ L), (∀ j < i, e j = b j) →
    L.integralNorm (b i) ≤ L.integralNorm (e i)

/-- Unfolding `IsMinkowskiReduced` into its defining condition. -/
theorem isMinkowskiReduced_def {n : ℕ} {b : Basis (Fin n) ℤ L} :
    L.IsMinkowskiReduced b ↔ ∀ (i : Fin n) (e : Basis (Fin n) ℤ L), (∀ j < i, e j = b j) →
      L.integralNorm (b i) ≤ L.integralNorm (e i) :=
  Iff.rfl

namespace IsMinkowskiReduced

variable {n : ℕ} {b : Basis (Fin n) ℤ L}

/-- The defining inequality of a Minkowski-reduced basis. -/
theorem integralNorm_le (hb : L.IsMinkowskiReduced b) {i : Fin n} (e : Basis (Fin n) ℤ L)
    (he : ∀ j < i, e j = b j) : L.integralNorm (b i) ≤ L.integralNorm (e i) :=
  hb i e he

/-- Adding to `b j` a vector in the span of the other vectors of a Minkowski-reduced basis does
not decrease its norm. -/
theorem integralNorm_le_integralNorm_add (hb : L.IsMinkowskiReduced b) (j : Fin n) {v : L}
    (hv : b.coord j v = 0) : L.integralNorm (b j) ≤ L.integralNorm (b j + v) := by
  have happly (k : Fin n) :
      (b.map (LinearEquiv.transvection hv)) k = b k + (if k = j then v else 0) := by
    rw [Basis.map_apply, LinearEquiv.transvection.apply, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_apply]
    split_ifs <;> simp
  simpa [happly] using hb.integralNorm_le (i := j) (b.map (LinearEquiv.transvection hv))
    (fun k hk ↦ by simp [happly, hk.ne])

/-- The norms of the vectors of a Minkowski-reduced basis are nondecreasing. -/
theorem monotone_integralNorm (hb : L.IsMinkowskiReduced b) :
    Monotone fun i ↦ L.integralNorm (b i) := by
  intro i j hij
  obtain rfl | hij := hij.eq_or_lt
  · exact le_rfl
  simpa using hb.integralNorm_le (i := i) (b.reindex (Equiv.swap i j)) fun k hk ↦ by
    rw [Basis.reindex_apply, Equiv.symm_swap,
      Equiv.swap_apply_of_ne_of_ne hk.ne (hk.trans hij).ne]

/-- The reduction inequality `2 |β(b i, b j)| ≤ β(b i, b i)` for distinct vectors of a
Minkowski-reduced basis. -/
theorem two_mul_abs_integralForm_le (hb : L.IsMinkowskiReduced b) {i j : Fin n} (hij : i ≠ j) :
    2 * |L.integralForm (b i) (b j)| ≤ L.integralNorm (b i) := by
  have hcoord : b.coord j (b i) = 0 := by simp [Basis.coord_apply, Basis.repr_self, hij]
  have hplus := hb.integralNorm_le_integralNorm_add j hcoord
  have hminus := hb.integralNorm_le_integralNorm_add j (v := -b i)
    (by rw [map_neg, hcoord, neg_zero])
  rw [integralNorm_add] at hplus hminus
  rw [integralNorm_neg, map_neg, L.isSymm_integralForm.eq (b j)] at hminus
  rw [L.isSymm_integralForm.eq (b j)] at hplus
  rw [← abs_two, ← abs_mul, abs_le]
  constructor <;> linarith

end IsMinkowskiReduced

/-- Every positive semidefinite integral lattice has a Minkowski-reduced basis. -/
theorem IsPosSemidef.exists_isMinkowskiReduced (hL : L.IsPosSemidef) :
    ∃ b : Basis (Fin (finrank ℤ L)) ℤ L, L.IsMinkowskiReduced b := by
  -- Choose the basis vectors greedily: `P k e` says that `e` is reduced at every index below `k`.
  let P (k : ℕ) (e : Basis (Fin (finrank ℤ L)) ℤ L) : Prop :=
    ∀ i : Fin (finrank ℤ L), i.val < k → ∀ e' : Basis (Fin (finrank ℤ L)) ℤ L,
      (∀ j < i, e' j = e j) → L.integralNorm (e i) ≤ L.integralNorm (e' i)
  have hstep (k : ℕ) (hk : k ≤ finrank ℤ L) : ∃ e, P k e := by
    induction k with
    | zero => exact ⟨finBasis ℤ L, fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨e, he⟩ := ih (by omega)
      let i₀ : Fin (finrank ℤ L) := ⟨k, by omega⟩
      -- Among the bases agreeing with `e` before `i₀`, take one minimizing the norm at `i₀`.
      obtain ⟨w, hwmin⟩ := exists_minimalFor_of_wellFoundedLT
        (fun e' : Basis (Fin (finrank ℤ L)) ℤ L ↦ ∀ j < i₀, e' j = e j)
        (fun e' ↦ (L.integralNorm (e' i₀)).toNat) ⟨e, fun _ _ ↦ rfl⟩
      refine ⟨w, fun i hi e' he' ↦ ?_⟩
      obtain hik | hik := (Nat.lt_succ_iff.mp hi).lt_or_eq
      · have hi₀ : i < i₀ := hik
        rw [hwmin.1 i hi₀]
        exact he i hik e' fun j hj ↦ (he' j hj).trans (hwmin.1 j (hj.trans hi₀))
      · obtain rfl : i = i₀ := Fin.ext hik
        have hle := hwmin.le (j := e') fun j hj ↦ (he' j hj).trans (hwmin.1 j hj)
        rw [← Int.toNat_of_nonneg (hL.integralNorm_nonneg (w i₀)),
          ← Int.toNat_of_nonneg (hL.integralNorm_nonneg (e' i₀))]
        exact_mod_cast hle
  obtain ⟨b, hb⟩ := hstep _ le_rfl
  exact ⟨b, fun i ↦ hb i i.isLt⟩

namespace IsMinkowskiReduced

/-- The first vector of a Minkowski-reduced basis of a positive semidefinite lattice is a minimal
vector. -/
@[simp] theorem integralNorm_zero_eq_minimum (hL : L.IsPosSemidef) {n : ℕ} [NeZero n]
    {b : Basis (Fin n) ℤ L} (hb : L.IsMinkowskiReduced b) :
    L.integralNorm (b 0) = L.minimum := by
  have : Nontrivial L := ⟨⟨b 0, 0, b.ne_zero 0⟩⟩
  refine le_antisymm ?_ (hL.minimum_le_integralNorm (b.ne_zero 0))
  -- A minimal vector is a positive multiple `c • w` of a primitive vector `w`, and `w` is the
  -- first vector of some basis.
  obtain ⟨x, hx, hxmin⟩ := hL.exists_ne_zero_integralNorm_eq_minimum
  obtain ⟨c, w, hc, hw, rfl⟩ := exists_eq_zsmul_isPrimitive hx
  obtain ⟨m, e, k, rfl⟩ := hw.exists_basis
  obtain rfl : m = n := by
    simpa using (finrank_eq_card_basis e).symm.trans (finrank_eq_card_basis b)
  have hc2 : 1 ≤ c ^ 2 := one_le_pow₀ (by omega)
  rw [← hxmin, integralNorm_zsmul]
  calc L.integralNorm (b 0) ≤ L.integralNorm (e.reindex (Equiv.swap k 0) 0) :=
        hb.integralNorm_le _ fun j hj ↦ absurd hj (Fin.not_lt_zero j)
    _ = L.integralNorm (e k) := by
        rw [Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_right]
    _ ≤ c ^ 2 * L.integralNorm (e k) :=
        le_mul_of_one_le_left (hL.integralNorm_nonneg (e k)) hc2

/-- The `i`-th vector of a Minkowski-reduced basis has norm at least the `i`-th successive minimum,
provided this norm is nonnegative (as it is when the lattice is positive semidefinite). -/
theorem successiveMinimum_le_integralNorm {b : Basis (Fin (finrank ℤ L)) ℤ L}
    (hb : L.IsMinkowskiReduced b) {i : Fin (finrank ℤ L)} (hi : 0 ≤ L.integralNorm (b i)) :
    (L.successiveMinimum i : ℤ) ≤ L.integralNorm (b i) := by
  let f : Fin (i.val + 1) → Fin (finrank ℤ L) := Fin.castLE (Nat.succ_le_of_lt i.isLt)
  have hle := L.successiveMinimum_le_of_linearIndependent i (c := (L.integralNorm (b i)).toNat)
    (b.linearIndependent.comp f (Fin.castLE_injective _)) fun j ↦
      (hb.monotone_integralNorm (Fin.le_iff_val_le_val.mpr (Nat.lt_succ_iff.mp j.isLt))).trans
        (Int.self_le_toNat _)
  rw [← Int.toNat_of_nonneg hi]
  exact_mod_cast hle

end IsMinkowskiReduced

end TauCeti.IntegralLattice
