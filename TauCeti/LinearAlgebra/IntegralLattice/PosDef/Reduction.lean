/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.SuccessiveMinima
import Mathlib.LinearAlgebra.Transvection.Basic
import TauCeti.Algebra.Module.Primitive
import TauCeti.LinearAlgebra.BilinearForm.PosSemidef

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

The norms of a reduced basis are comparable to the successive minima `λᵢ` of a positive
semidefinite lattice: `λᵢ ≤ β(b i, b i) ≤ (i!)² λᵢ`. For the upper bound, take a vector `y` of norm
at most `λᵢ` outside the span of `b 0, …, b (i - 1)`. Its component along the remaining basis
vectors is `d • z` with `z` primitive; rounding the other coordinates of `y / d` gives a vector
`v` such that `b 0, …, b (i - 1), v` extends to a basis, so `β(b i, b i) ≤ β(v, v)`. If `d = 1`
then `v = y`, and otherwise `d ≥ 2` and `β(v, v)` is bounded by `λᵢ` and the norms of the earlier
basis vectors.

## Main declarations

* `TauCeti.IntegralLattice.IsMinkowskiReduced`: Minkowski-reduced bases, unfolded by
  `TauCeti.IntegralLattice.isMinkowskiReduced_def`.
* `TauCeti.IntegralLattice.IsPosSemidef.exists_isMinkowskiReduced`: existence.
* `TauCeti.IntegralLattice.IsMinkowskiReduced.integralNorm_le_integralNorm_add`: the norm of `b j`
  does not decrease when a vector in the span of the other basis vectors is added to it.
* `TauCeti.IntegralLattice.IsMinkowskiReduced.monotone_integralNorm` and
  `TauCeti.IntegralLattice.IsMinkowskiReduced.two_mul_abs_integralForm_le`: the elementary
  reduction inequalities.
* `TauCeti.IntegralLattice.IsMinkowskiReduced.integralNorm_le_of_apply_eq_one`: `b i` has norm at
  most that of every `v` such that `b 0, …, b (i - 1), v` extends to a basis.
* `TauCeti.IntegralLattice.IsMinkowskiReduced.integralNorm_zero_eq_minimum`,
  `TauCeti.IntegralLattice.IsMinkowskiReduced.successiveMinimum_le_integralNorm` and
  `TauCeti.IntegralLattice.IsMinkowskiReduced.integralNorm_le_factorial_sq_mul_successiveMinimum`:
  comparison with the minimum and the successive minima.

## References

* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 12, §1.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §10.
-/

public section

open Module
open scoped Nat

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

/-- In a Minkowski-reduced basis, `b i` has norm at most that of every vector `v` such that
`b 0, …, b (i - 1), v` extends to a basis, which is the case when some integer-valued linear
functional vanishes on `b 0, …, b (i - 1)` and takes the value one on `v`. -/
theorem integralNorm_le_of_apply_eq_one (hb : L.IsMinkowskiReduced b) {i : Fin n}
    {f : L →ₗ[ℤ] ℤ} (hf : ∀ j < i, f (b j) = 0) {v : L} (hv : f v = 1) :
    L.integralNorm (b i) ≤ L.integralNorm v := by
  obtain ⟨e, he, rfl⟩ := (b.exists_basis_eq_iff i v).2 ⟨f, hf, hv⟩
  exact hb.integralNorm_le e he

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

/-- The rounding step of reduction theory. Let `y` have a nonzero coordinate in the basis `b` at
some index `j ≥ i`. Then some `v` such that `b 0, …, b (i - 1), v` extends to a basis (as witnessed
by a functional) satisfies `d • v = y - ∑_{j < i} σⱼ • b j` for some `d > 0` and coefficients with
`|2 σⱼ| ≤ d`. -/
private theorem exists_zsmul_eq_sub_sum {n : ℕ} (b : Basis (Fin n) ℤ L) (i : Fin n) {y : L}
    (hy : y - ∑ j ∈ Finset.Iio i, b.coord j y • b j ≠ 0) :
    ∃ (d : ℤ) (v : L) (σ : Fin n → ℤ), 0 < d ∧
      (∃ f : L →ₗ[ℤ] ℤ, (∀ j < i, f (b j) = 0) ∧ f v = 1) ∧
      d • v = y - ∑ j ∈ Finset.Iio i, σ j • b j ∧ ∀ j, -d ≤ 2 * σ j ∧ 2 * σ j ≤ d := by
  classical
  set s := Finset.Iio i
  -- The component of `y` along `b i, b (i + 1), …` is a positive multiple `d • z` of a primitive
  -- vector `z`, whose coordinates before `i` vanish.
  set yh := y - ∑ j ∈ s, b.coord j y • b j
  obtain ⟨d, z, hd, hzp, hdz⟩ := exists_eq_zsmul_isPrimitive hy
  obtain ⟨g, hg⟩ := isPrimitive_def.1 hzp
  have hz (k : Fin n) (hk : k < i) : b.coord k z = 0 := by
    have h : b.coord k yh = 0 := by simp [yh, s, hk, Finsupp.single_apply]
    rw [hdz, map_zsmul, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hd.ne'
  -- Round the coefficients of `y` before `i` to nearby multiples `d * rⱼ`.
  set r : Fin n → ℤ := fun j ↦ (2 * b.coord j y + d) / (2 * d)
  -- A functional vanishing on `b 0, …, b (i - 1)` and taking the value one on `z`.
  set f : L →ₗ[ℤ] ℤ := g - ∑ j ∈ s, g (b j) • b.coord j
  have hf (k : Fin n) (hk : k < i) : f (b k) = 0 := by simp [f, s, hk, Finsupp.single_apply]
  have hfz : f z = 1 := by
    simp only [f, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, hg, smul_eq_mul]
    rw [Finset.sum_eq_zero fun j hj ↦ by rw [hz j (Finset.mem_Iio.mp hj), mul_zero], sub_zero]
  refine ⟨d, z + ∑ j ∈ s, r j • b j, fun j ↦ b.coord j y - d * r j, hd, ⟨f, hf, ?_⟩, ?_,
    fun j ↦ ?_⟩
  · simp only [map_add, map_sum, map_zsmul, hfz, smul_eq_mul]
    rw [Finset.sum_eq_zero fun j hj ↦ by rw [hf j (Finset.mem_Iio.mp hj), mul_zero], add_zero]
  · rw [smul_add, ← hdz]
    simp only [yh, Finset.smul_sum, smul_smul, sub_smul, Finset.sum_sub_distrib]
    abel
  · have h₁ := Int.mul_ediv_add_emod (2 * b.coord j y + d) (2 * d)
    have h₂ := Int.emod_nonneg (2 * b.coord j y + d) (by positivity : 2 * d ≠ 0)
    have h₃ := Int.emod_lt_of_pos (2 * b.coord j y + d) (by positivity : 0 < 2 * d)
    constructor <;> linarith

namespace IsMinkowskiReduced

/-- One step of the comparison with the successive minima: if `K` bounds the norms of the
vectors of a reduced basis before `i`, then `2 β(b i, b i) ≤ λᵢ + max λᵢ (i² K)`. -/
private theorem two_mul_integralNorm_le (hL : L.IsPosSemidef)
    {b : Basis (Fin (finrank ℤ L)) ℤ L} (hb : L.IsMinkowskiReduced b) (i : Fin (finrank ℤ L))
    {K : ℤ} (hK : ∀ j < i, L.integralNorm (b j) ≤ K) :
    2 * L.integralNorm (b i) ≤
      L.successiveMinimum i + max (L.successiveMinimum i : ℤ) (i ^ 2 * K) := by
  set s := Finset.Iio i
  have hμ : (0 : ℤ) ≤ L.successiveMinimum i := Int.natCast_nonneg _
  -- A vector `y` of norm at most `λᵢ` outside the span of `b 0, …, b (i - 1)`, and the rounding
  -- `d • v = y - S` of `y`, where `b 0, …, b (i - 1), v` extends to a basis.
  obtain ⟨y, hy, hyspan⟩ := L.exists_integralNorm_le_successiveMinimum_not_mem_span i
    fun j ↦ b (Fin.castLE i.isLt.le j)
  have hyh : y - ∑ j ∈ s, b.coord j y • b j ≠ 0 := by
    intro h
    refine hyspan ?_
    rw [sub_eq_zero.mp h, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun j hj ↦ ?_
    rw [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℚ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨⟨j.val, Fin.lt_def.mp (Finset.mem_Iio.mp hj)⟩, by simp [Fin.castLE]⟩)
  obtain ⟨d, v, σ, hd, ⟨f, hf, hfv⟩, hdv, hσ⟩ := exists_zsmul_eq_sub_sum b i hyh
  set S := ∑ j ∈ s, σ j • b j
  have hNv := hb.integralNorm_le_of_apply_eq_one hf hfv
  obtain rfl | hd2 : d = 1 ∨ 2 ≤ d := by omega
  · -- If `d = 1` then every `σⱼ` vanishes and `v = y`.
    have hS : S = 0 := Finset.sum_eq_zero fun j _ ↦ by
      rw [show σ j = 0 by have := hσ j; omega, zero_smul]
    rw [hS, sub_zero, one_smul] at hdv
    rw [hdv] at hNv
    linarith [le_max_left (L.successiveMinimum i : ℤ) (i ^ 2 * K)]
  -- Otherwise `d² β(v, v) = β(y - S, y - S) ≤ 2 β(y, y) + 2 β(S, S)`, and
  -- `β(S, S) ≤ i ∑ σⱼ² β(b j, b j) ≤ i² d² K / 4`.
  have hyS : L.integralNorm (y - S) ≤ 2 * L.integralNorm y + 2 * L.integralNorm S := by
    have h₁ := L.integralNorm_add y S
    have h₂ := L.integralNorm_add y (-S)
    rw [integralNorm_neg, map_neg, ← sub_eq_add_neg] at h₂
    linarith [hL.integralNorm_nonneg (y + S)]
  have hpsd : L.integralForm.IsPosSemidef :=
    (LinearMap.BilinForm.isPosSemidef_iff_forall_nonneg _ L.isSymm_integralForm).2 fun x ↦ by
      simpa only [integralNorm_apply] using hL.integralNorm_nonneg x
  have hS : L.integralNorm S ≤ i * ∑ j ∈ s, σ j ^ 2 * L.integralNorm (b j) := by
    have h := hpsd.apply_sum_sum_le_card_mul_sum s fun j ↦ σ j • b j
    simp only [← integralNorm_apply, integralNorm_zsmul, s, Fin.card_Iio] at h
    exact h
  have hσK : 4 * ∑ j ∈ s, σ j ^ 2 * L.integralNorm (b j) ≤ i * (d ^ 2 * K) := by
    rw [Finset.mul_sum, ← Fin.card_Iio i, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun j hj ↦ ?_
    have h₁ := hσ j
    have h₂ := hL.integralNorm_nonneg (b j)
    have h₃ := hK j (Finset.mem_Iio.mp hj)
    have h₄ : 4 * σ j ^ 2 ≤ d ^ 2 := by nlinarith
    nlinarith
  have hdN : d ^ 2 * L.integralNorm v = L.integralNorm (y - S) := by
    rw [← integralNorm_zsmul, hdv]
  -- Altogether `4 d² β(v, v) ≤ 8 λᵢ + 2 i² d² K ≤ d² (2 λᵢ + 2 i² K)`, since `d² ≥ 4`.
  have hd4 : 4 ≤ d ^ 2 := by nlinarith
  have hkey : d ^ 2 * (4 * L.integralNorm v) ≤
      d ^ 2 * (2 * L.successiveMinimum i + 2 * i ^ 2 * K) := by
    nlinarith [mul_le_mul_of_nonneg_left hσK (Int.natCast_nonneg i)]
  have := le_of_mul_le_mul_left hkey (by positivity)
  linarith [le_max_right (L.successiveMinimum i : ℤ) (i ^ 2 * K)]

/-- **Reduced bases and successive minima.** The `i`-th vector of a Minkowski-reduced basis of a
positive semidefinite lattice has norm at most `(i!)²` times the `i`-th successive minimum `λᵢ`.
Since it also has norm at least `λᵢ` (`IsMinkowskiReduced.successiveMinimum_le_integralNorm`), the
norms of a reduced basis agree with the successive minima up to factors depending only on the
rank. -/
theorem integralNorm_le_factorial_sq_mul_successiveMinimum (hL : L.IsPosSemidef)
    {b : Basis (Fin (finrank ℤ L)) ℤ L} (hb : L.IsMinkowskiReduced b) (i : Fin (finrank ℤ L)) :
    L.integralNorm (b i) ≤ (i : ℕ)! ^ 2 * L.successiveMinimum i := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero =>
    have h := two_mul_integralNorm_le hL hb ⟨0, hk⟩ (K := 0) fun j hj ↦
      absurd (Fin.lt_def.mp hj) (Nat.not_lt_zero _)
    rw [mul_zero, max_eq_left (Int.natCast_nonneg _)] at h
    simp only [Nat.factorial_zero, Nat.cast_one, one_pow, one_mul]
    linarith
  | succ k ih =>
    -- The vectors before `k + 1` have norm at most `β(b k, b k) ≤ (k!)² λₖ ≤ (k!)² λₖ₊₁`.
    have hk' : k < finrank ℤ L := by omega
    have hK (j : Fin (finrank ℤ L)) (hj : j < ⟨k + 1, hk⟩) :
        L.integralNorm (b j) ≤ (k ! : ℤ) ^ 2 * L.successiveMinimum ⟨k, hk'⟩ :=
      (hb.monotone_integralNorm (Fin.le_def.mpr (Nat.lt_succ_iff.mp (Fin.lt_def.mp hj)))).trans
        (ih hk')
    have h := two_mul_integralNorm_le hL hb ⟨k + 1, hk⟩ hK
    have hμ : (L.successiveMinimum ⟨k, hk'⟩ : ℤ) ≤ L.successiveMinimum ⟨k + 1, hk⟩ :=
      Int.ofNat_le.mpr (L.monotone_successiveMinimum (Fin.le_def.mpr (Nat.le_succ k)))
    have hf : (1 : ℤ) ≤ ((k + 1)! : ℤ) ^ 2 := one_le_pow₀ (by exact_mod_cast Nat.factorial_pos _)
    have hμ' : (0 : ℤ) ≤ L.successiveMinimum ⟨k + 1, hk⟩ := Int.natCast_nonneg _
    rw [Nat.factorial_succ, Nat.cast_mul] at hf ⊢
    push_cast at h hf ⊢
    -- `2 β(b (k + 1), b (k + 1)) ≤ λₖ₊₁ + max λₖ₊₁ ((k + 1)² (k!)² λₖ) ≤ 2 ((k + 1)!)² λₖ₊₁`.
    have h₁ : max (L.successiveMinimum ⟨k + 1, hk⟩ : ℤ)
        ((k + 1) ^ 2 * (k ! ^ 2 * L.successiveMinimum ⟨k, hk'⟩)) ≤
          ((k + 1) * k !) ^ 2 * L.successiveMinimum ⟨k + 1, hk⟩ := by
      refine max_le (by nlinarith) ?_
      rw [← mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_left hμ (sq_nonneg _)
    linarith [mul_le_mul_of_nonneg_right hf hμ']

end IsMinkowskiReduced

end TauCeti.IntegralLattice
