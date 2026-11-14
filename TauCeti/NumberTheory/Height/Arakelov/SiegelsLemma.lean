/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.BombieriVaaler
public import TauCeti.NumberTheory.Height.Arakelov.KernelBasis

import TauCeti.NumberTheory.Height.Arakelov.Subspace.Bounds

/-!
# Siegel's lemma for subspaces and linear systems, after Bombieri–Vaaler and Evertse–Ferretti

Taking the vector of smallest norm or height from the basis-level product bounds of
`TauCeti.NumberTheory.Height.Arakelov.BombieriVaaler` (over `ℚ`) and
`TauCeti.NumberTheory.Height.Arakelov.KernelBasis` (over a number field `K` of degree `D = [K : ℚ]`)
yields one-vector forms of Siegel's lemma whose bounds depend on a linear system only through the
Arakelov height of its solution space (equivalently, of its row space).

Over `ℚ`, a nonzero `k`-dimensional subspace `V` of `ℚ^ι` contains a nonzero integral vector `z`
with `‖z‖ ≤ H(V) ^ (1 / k)`, where `‖z‖ = max_i |z i|` is the sup norm and `H(V)` is the absolute
Euclidean height `Submodule.subspaceHeight V`. For a system `A x = 0` of `p` independent integer
linear equations in `n > p` unknowns, this is Bombieri and Vaaler's Theorem 1:
`‖x‖ ≤ (√det (A Aᵀ) / g) ^ (1 / (n - p))`, where `g` is the greatest common divisor of the maximal
minors of `A`, improving on Mathlib's classical `Int.Matrix.exists_ne_zero_int_vec_norm_le`.

Over a general number field `K` with `r₁` real places, `r₂` complex places, and discriminant
`discr K`, a nonzero `k`-dimensional `K`-subspace `W` of `ι → K` contains a nonzero integral point
`z ∈ W ∩ 𝓞_K^ι` bounded in absolute sup height by
`(2 / π) ^ (r₂ / D) * |discr K| ^ (1 / (2 * D)) * W.subspaceHeight ^ (1 / k)`, and in absolute
Euclidean height `height2` via the unit-ball slice constants `ω_k` and `ω_{2k}`. Specializing to
`W = LinearMap.ker A.mulVecLin` for any `m × ι` matrix `A` over `K` of rank `< #ι` (with no
row-independence assumption) bounds a nonzero integral solution in terms of
`(span K (range A.row)).subspaceHeight`. Combining the sup-height bound with `(2 / π) ≤ 1`,
`height2 ≤ √#ι · absoluteProjectiveTupleHeight`, and Hadamard's bound
`Submodule.subspaceHeight_span_range_le_prod_of_ne_zero` yields Evertse and Ferretti's fixed-field
Siegel lemma (`TauCeti.exists_ne_zero_height2_le`): for `#m < #ι` nonzero linear forms `L i` in
`#ι` variables over `K`, there is a nonzero `x : ι → 𝓞 K` in their common kernel with
`height2 x ≤ √#ι * |discr K| ^ (1 / (2 * D)) * (∏ i, height2 (L i)) ^ (1 / (#ι - #m))`.

## Main results

* `Submodule.exists_ne_zero_mem_intPoints_norm_le` and
  `Matrix.exists_ne_zero_mulVec_eq_zero_norm_le`: Bombieri and Vaaler's sup-norm Siegel lemma over
  `ℚ` and `ℤ`.
* `Submodule.exists_ne_zero_mem_integerPoints_absoluteProjectiveTupleHeight_le` and
  `Submodule.exists_ne_zero_mem_integerPoints_height2_le`: one-vector Siegel bounds for a nonzero
  subspace `W` of `ι → K` in sup height and Euclidean height.
* `Matrix.exists_ne_zero_mulVec_eq_zero_absoluteProjectiveTupleHeight_le` and
  `Matrix.exists_ne_zero_mulVec_eq_zero_height2_le`: one-vector Siegel bounds for `A x = 0` over `K`
  when `A.rank < #ι`, without assuming row independence.
* `Matrix.exists_ne_zero_mulVec_eq_zero_height2_le_of_row_ne_zero` and
  `TauCeti.exists_ne_zero_height2_le`: Evertse and Ferretti's fixed-field Siegel lemma in terms of
  the Euclidean heights of the defining linear forms.

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32,
  Theorems 1 and 9.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  §2.9 (Theorem 2.9.19).
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §13, Lemma 13.1.
-/

public section

noncomputable section

open MeasureTheory Metric Module NumberField NumberField.InfinitePlace Set TauCeti

private theorem exists_le_rpow_inv_of_prod_le {k : ℕ} (hk : 0 < k) {f : Fin k → ℝ}
    {B : ℝ} (hB : 0 < B) (hle : ∏ i, f i ≤ B) : ∃ i, f i ≤ B ^ (k : ℝ)⁻¹ := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  by_contra! h
  have hprod := Finset.prod_lt_prod_of_nonempty₀
    (fun _ _ => Real.rpow_pos_of_pos hB _) (fun i _ => h i) Finset.univ_nonempty
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Real.rpow_inv_natCast_pow hB.le hk.ne'] at hprod
  exact hprod.not_ge hle

namespace Submodule

section Rat

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **Siegel's lemma for a rational subspace, in the sup norm.** A nonzero subspace `V` of `ℚ^ι`
contains a nonzero integral point `z` whose sup norm is at most `H(V) ^ (1 / k)`, where `H(V)` is
the absolute Euclidean height of `V` and `k` its dimension. -/
theorem exists_ne_zero_mem_intPoints_norm_le {V : Submodule ℚ (ι → ℚ)} (hV : V ≠ ⊥) :
    ∃ z ∈ V.intPoints, z ≠ 0 ∧ ‖z‖ ≤ V.subspaceHeight ^ (finrank ℚ V : ℝ)⁻¹ := by
  have : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV
  obtain ⟨z, hz, hzV, _, hle⟩ := V.exists_linearIndependent_intPoints_prod_norm_le
  obtain ⟨i, hi⟩ := exists_le_rpow_inv_of_prod_le finrank_pos (Submodule.subspaceHeight_pos V) hle
  exact ⟨z i, hzV i, hz.ne_zero i, hi⟩

end Rat

section NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι] [LinearOrder ι]

/-- **Siegel's lemma for a number-field subspace, sup height** (Bombieri–Vaaler, Bombieri–Gubler).
A nonzero `K`-subspace `W` of `ι → K` of dimension `k` contains a nonzero integral point
`z ∈ W ∩ 𝓞_K^ι` with
`H(z) ≤ (2 / π) ^ (r₂ / [K : ℚ]) * |discr K| ^ (1 / (2 * [K : ℚ])) * W.subspaceHeight ^ (1 / k)`. -/
theorem exists_ne_zero_mem_integerPoints_absoluteProjectiveTupleHeight_le
    {W : Submodule K (ι → K)} (hW : W ≠ ⊥) :
    ∃ z ∈ W.integerPoints, z ≠ 0 ∧
      absoluteProjectiveTupleHeight (fun i ↦ (z i : K)) ≤
        (2 / Real.pi) ^ ((nrComplexPlaces K : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * finrank ℚ K)) *
          W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hk : 0 < finrank K W := finrank_pos
  have hk0 : (finrank K W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  obtain ⟨x, hx_li, hx_mem, hle⟩ :=
    W.exists_linearIndependent_integerPoints_prod_absoluteProjectiveTupleHeight_le
  have hB :
      0 < (2 / Real.pi) ^ ((finrank K W * nrComplexPlaces K : ℝ) / finrank ℚ K) *
        |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) * W.subspaceHeight :=
    lt_of_lt_of_le (Finset.prod_pos fun j _ ↦ absoluteProjectiveTupleHeight_pos _) hle
  obtain ⟨j, hj⟩ := exists_le_rpow_inv_of_prod_le hk hB hle
  have hj0 : x j ≠ 0 := fun h0 ↦
    hx_li.ne_zero j (RingOfIntegers.coe_tuple_eq_zero_iff.mpr h0)
  refine ⟨x j, hx_mem j, hj0, hj.trans_eq ?_⟩
  rw [Real.mul_rpow (by positivity) (Submodule.subspaceHeight_pos W).le,
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (abs_nonneg _)]
  congr 2
  · congr 1
    field_simp
  · congr 1
    field_simp

/-- **Siegel's lemma for a number-field subspace, Euclidean height.** A nonzero `K`-subspace `W` of
`ι → K` of dimension `k` contains a nonzero integral point `z ∈ W ∩ 𝓞_K^ι` whose Euclidean height
`height2` is bounded by the `k`-th root of the ball-slice basis bound. -/
theorem exists_ne_zero_mem_integerPoints_height2_le {W : Submodule K (ι → K)} (hW : W ≠ ⊥) :
    ∃ z ∈ W.integerPoints, z ≠ 0 ∧
      height2 (fun i ↦ (z i : K)) ≤
        (2 ^ finrank K W /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1)) ^
          ((nrRealPlaces K : ℝ) / (finrank ℚ K * finrank K W)) *
        (2 ^ finrank K W /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1)) ^
          ((nrComplexPlaces K : ℝ) / (finrank ℚ K * finrank K W)) *
        |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * finrank ℚ K)) *
        W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hk : 0 < finrank K W := finrank_pos
  have hk0 : (finrank K W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  set ω₁ := volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1)
  set ω₂ := volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1)
  obtain ⟨x, hx_li, hx_mem, hle⟩ := W.exists_linearIndependent_integerPoints_prod_height2_le
  have hB :
      0 < (2 ^ finrank K W / ω₁) ^ ((nrRealPlaces K : ℝ) / finrank ℚ K) *
        (2 ^ finrank K W / ω₂) ^ ((nrComplexPlaces K : ℝ) / finrank ℚ K) *
        |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) * W.subspaceHeight :=
    lt_of_lt_of_le
      (Finset.prod_pos fun j _ ↦
        lt_of_lt_of_le zero_lt_one (one_le_height2_of_ne_zero (hx_li.ne_zero j)))
      hle
  obtain ⟨j, hj⟩ := exists_le_rpow_inv_of_prod_le hk hB hle
  have hj0 : x j ≠ 0 := fun h0 ↦
    hx_li.ne_zero j (RingOfIntegers.coe_tuple_eq_zero_iff.mpr h0)
  refine ⟨x j, hx_mem j, hj0, hj.trans_eq ?_⟩
  rw [Real.mul_rpow (by positivity) (Submodule.subspaceHeight_pos W).le,
    Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (abs_nonneg _)]
  congr 2
  · congr 1
    · congr 1
      rw [div_eq_mul_inv, mul_assoc, ← mul_inv]
      rfl
    · congr 1
      rw [div_eq_mul_inv, mul_assoc, ← mul_inv]
      rfl
  · congr 1
    field_simp

end NumberField

end Submodule

namespace Matrix

open Submodule

section Int

variable {ι : Type*} [Fintype ι] {p : ℕ}

/-- **Bombieri and Vaaler's Siegel lemma over `ℤ`, in the sup norm.** Let `A` be a `p × n` integer
matrix with linearly independent rows and `p < n`, and let `g` be the greatest common divisor of
its maximal minors. Then `A x = 0` has a nonzero integral solution `x` with
`‖x‖ ≤ (√det (A Aᵀ) / g) ^ (1 / (n - p))`, where `‖x‖ = max_i |x i|`. -/
theorem exists_ne_zero_mulVec_eq_zero_norm_le {A : Matrix (Fin p) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) (hp : p < Fintype.card ι) :
    ∃ x : ι → ℤ, x ≠ 0 ∧ A *ᵥ x = 0 ∧
      ‖x‖ ≤ (√((A * Aᵀ).det : ℝ) / (A.minorGcd : ℝ)) ^
        ((Fintype.card ι : ℝ) - p)⁻¹ := by
  obtain ⟨x, hx, hxker, _, hle⟩ := exists_linearIndependent_mulVec_eq_zero_prod_norm_le hA
  have hB : 0 < √((A * Aᵀ).det : ℝ) / (A.minorGcd : ℝ) :=
    lt_of_lt_of_le (Finset.prod_pos fun i _ => norm_pos_iff.mpr (hx.ne_zero i)) hle
  obtain ⟨i, hi⟩ := exists_le_rpow_inv_of_prod_le (Nat.sub_pos_of_lt hp) hB hle
  refine ⟨x i, hx.ne_zero i, hxker i, ?_⟩
  simpa only [Nat.cast_sub hp.le] using hi

end Int

section NumberField

variable {K : Type*} [Field K] [NumberField K] {m ι : Type*} [Fintype ι]

/-- **Siegel's lemma for a linear system over a number field, sup height.** For any `m × ι` matrix
`A` over `K` with `A.rank < #ι` (without assuming row independence or finiteness of `m`), `A x = 0`
has a nonzero solution `x : ι → 𝓞 K` with
`H(x) ≤ (2 / π) ^ (r₂ / [K : ℚ]) * |discr K| ^ (1 / (2 * [K : ℚ])) *
  (span K (range A.row)).subspaceHeight ^ (1 / (#ι - A.rank))`. -/
theorem exists_ne_zero_mulVec_eq_zero_absoluteProjectiveTupleHeight_le [LinearOrder ι]
    {A : Matrix m ι K} (hA : A.rank < Fintype.card ι) :
    ∃ x : ι → 𝓞 K, x ≠ 0 ∧ A *ᵥ (fun j ↦ (x j : K)) = 0 ∧
      absoluteProjectiveTupleHeight (fun j ↦ (x j : K)) ≤
        (2 / Real.pi) ^ ((nrComplexPlaces K : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * finrank ℚ K)) *
          (span K (range A.row)).subspaceHeight ^ ((Fintype.card ι : ℝ) - A.rank)⁻¹ := by
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ := fun h0 ↦ by
    have hdim := A.finrank_ker_mulVecLin
    rw [h0, finrank_bot] at hdim
    omega
  obtain ⟨x, hx_mem, hx0, hx_le⟩ :=
    exists_ne_zero_mem_integerPoints_absoluteProjectiveTupleHeight_le hker
  refine ⟨x, hx0, LinearMap.mem_ker.mp (mem_integerPoints.mp hx_mem), ?_⟩
  simpa only [A.finrank_ker_mulVecLin, A.subspaceHeight_ker_mulVecLin, Nat.cast_sub hA.le] using
    hx_le

/-- **Siegel's lemma for a linear system over a number field, Euclidean height.** For any `m × ι`
matrix `A` over `K` with `A.rank < #ι` (without assuming row independence or finiteness of `m`),
`A x = 0` has a nonzero solution `x : ι → 𝓞 K` bounded in `height2` by the `(#ι - A.rank)`-th root
of the ball-slice kernel-basis bound. -/
theorem exists_ne_zero_mulVec_eq_zero_height2_le [LinearOrder ι] {A : Matrix m ι K}
    (hA : A.rank < Fintype.card ι) :
    ∃ x : ι → 𝓞 K, x ≠ 0 ∧ A *ᵥ (fun j ↦ (x j : K)) = 0 ∧
      height2 (fun j ↦ (x j : K)) ≤
        (2 ^ (Fintype.card ι - A.rank) /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (Fintype.card ι - A.rank))) 1)) ^
          ((nrRealPlaces K : ℝ) / (finrank ℚ K * ((Fintype.card ι : ℝ) - A.rank))) *
        (2 ^ (Fintype.card ι - A.rank) /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * (Fintype.card ι - A.rank)))) 1)) ^
          ((nrComplexPlaces K : ℝ) / (finrank ℚ K * ((Fintype.card ι : ℝ) - A.rank))) *
        |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * finrank ℚ K)) *
        (span K (range A.row)).subspaceHeight ^ ((Fintype.card ι : ℝ) - A.rank)⁻¹ := by
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ := fun h0 ↦ by
    have hdim := A.finrank_ker_mulVecLin
    rw [h0, finrank_bot] at hdim
    omega
  obtain ⟨x, hx_mem, hx0, hx_le⟩ := exists_ne_zero_mem_integerPoints_height2_le hker
  refine ⟨x, hx0, LinearMap.mem_ker.mp (mem_integerPoints.mp hx_mem), hx_le.trans_eq ?_⟩
  rw [A.finrank_ker_mulVecLin, A.subspaceHeight_ker_mulVecLin, Nat.cast_sub hA.le]

/-- **Fixed-field Siegel's lemma for a matrix with nonzero rows** (Evertse–Ferretti, Lemma 13.1).
For any `m × ι` matrix `A` over `K` with `#m < #ι` and all rows nonzero (without assuming linear
independence of the rows), `A x = 0` has a nonzero solution `x : ι → 𝓞 K` with
`height2 x ≤ √#ι * |discr K| ^ (1 / (2 * [K : ℚ])) * (∏ i, height2 (A.row i)) ^ (1 / (#ι - #m))`. -/
theorem exists_ne_zero_mulVec_eq_zero_height2_le_of_row_ne_zero [Fintype m] {A : Matrix m ι K}
    (hcard : Fintype.card m < Fintype.card ι) (hrow : ∀ i, A.row i ≠ 0) :
    ∃ x : ι → 𝓞 K, x ≠ 0 ∧ A *ᵥ (fun j ↦ (x j : K)) = 0 ∧
      height2 (fun j ↦ (x j : K)) ≤
        √(Fintype.card ι) * |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * finrank ℚ K)) *
          (∏ i, height2 (A.row i)) ^ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹ := by
  classical
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hrank_le : A.rank ≤ Fintype.card m := A.rank_le_card_height
  have hA : A.rank < Fintype.card ι := hrank_le.trans_lt hcard
  obtain ⟨x, hx0, hxker, hxle⟩ := exists_ne_zero_mulVec_eq_zero_absoluteProjectiveTupleHeight_le hA
  have hpi_le : (2 / Real.pi) ^ ((nrComplexPlaces K : ℝ) / finrank ℚ K) ≤ 1 :=
    Real.rpow_le_one (by positivity) (div_le_one_of_le₀ Real.two_le_pi Real.pi_pos.le)
      (by positivity)
  have hprod_ge : 1 ≤ ∏ i, height2 (A.row i) :=
    Finset.one_le_prod₀ fun i _ ↦ one_le_height2_of_ne_zero (hrow i)
  have hsub_le : (span K (range A.row)).subspaceHeight ≤ ∏ i, height2 (A.row i) :=
    Submodule.subspaceHeight_span_range_le_prod_of_ne_zero hrow
  have hexp_le :
      ((Fintype.card ι : ℝ) - A.rank)⁻¹ ≤ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹ :=
    inv_anti₀ (sub_pos.mpr (Nat.cast_lt.mpr hcard))
      (sub_le_sub_left (Nat.cast_le.mpr hrank_le) _)
  have hH_pow :
      (span K (range A.row)).subspaceHeight ^ ((Fintype.card ι : ℝ) - A.rank)⁻¹ ≤
        (∏ i, height2 (A.row i)) ^ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹ :=
    (Real.rpow_le_rpow (Submodule.subspaceHeight_pos _).le hsub_le
      (inv_nonneg.mpr (sub_pos.mpr (Nat.cast_lt.mpr hA)).le)).trans
      (Real.rpow_le_rpow_of_exponent_le hprod_ge hexp_le)
  have hH_nn : 0 ≤ (span K (range A.row)).subspaceHeight ^ ((Fintype.card ι : ℝ) - A.rank)⁻¹ :=
    Real.rpow_nonneg (Submodule.subspaceHeight_pos _).le _
  have hsup :
      absoluteProjectiveTupleHeight (fun j ↦ (x j : K)) ≤
        |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * finrank ℚ K)) *
          (∏ i, height2 (A.row i)) ^ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹ := by
    refine hxle.trans ?_
    calc (2 / Real.pi) ^ ((nrComplexPlaces K : ℝ) / finrank ℚ K) *
            |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * finrank ℚ K)) *
            (span K (range A.row)).subspaceHeight ^ ((Fintype.card ι : ℝ) - A.rank)⁻¹
        ≤ 1 * |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * finrank ℚ K)) *
            (∏ i, height2 (A.row i)) ^ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹ := by
          gcongr
      _ = _ := by rw [one_mul]
  refine ⟨x, hx0, hxker, ?_⟩
  calc height2 (fun j ↦ (x j : K))
      ≤ √(Nat.card ι) * absoluteProjectiveTupleHeight (fun j ↦ (x j : K)) :=
        height2_le_sqrt_natCard_mul_absoluteProjectiveTupleHeight _
    _ ≤ √(Fintype.card ι) *
          (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * finrank ℚ K)) *
            (∏ i, height2 (A.row i)) ^ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹) := by
        rw [Nat.card_eq_fintype_card]
        exact mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)
    _ = _ := by ring

end NumberField

end Matrix

namespace TauCeti

/-- **Evertse and Ferretti's fixed-field Siegel lemma** (EF13, §13, Lemma 13.1). Let `K` be a
number field of degree `D = [K : ℚ]` and discriminant `discr K`, and let `L : m → ι → K` be a
family of nonzero linear forms in `#ι` variables with `#m < #ι` (without assuming linear
independence of the forms). Then there is a nonzero tuple of algebraic integers `x : ι → 𝓞 K`
annihilated by every `L i` whose absolute Euclidean height satisfies
`height2 x ≤ √#ι * |discr K| ^ (1 / (2 * D)) * (∏ i, height2 (L i)) ^ (1 / (#ι - #m))`. -/
theorem exists_ne_zero_height2_le {K : Type*} [Field K] [NumberField K] {m ι : Type*}
    [Fintype m] [Fintype ι] (hcard : Fintype.card m < Fintype.card ι) {L : m → ι → K}
    (hL : ∀ i, L i ≠ 0) :
    ∃ x : ι → 𝓞 K, x ≠ 0 ∧ (∀ i, ∑ j, L i j * (x j : K) = 0) ∧
      height2 (fun j ↦ (x j : K)) ≤
        √(Fintype.card ι) * |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * finrank ℚ K)) *
          (∏ i, height2 (L i)) ^ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹ := by
  have hrow : (Matrix.of L).row = L := funext fun i ↦ funext fun j ↦ rfl
  obtain ⟨x, hx0, hxker, hxle⟩ :=
    Matrix.exists_ne_zero_mulVec_eq_zero_height2_le_of_row_ne_zero (A := Matrix.of L) hcard
      (hrow.symm ▸ hL)
  refine ⟨x, hx0, fun i ↦ ?_, hrow ▸ hxle⟩
  simpa [Matrix.mulVec, dotProduct] using congrFun hxker i

end TauCeti

end
