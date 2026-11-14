/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.KernelBasis
import TauCeti.NumberTheory.Height.Arakelov.Subspace.Bounds

/-!
# Siegel's lemma via Arakelov subspace heights

Taking the smallest-height vector in the basis theorems of `BombieriVaaler` and `KernelBasis` yields
Bombieri–Vaaler and Evertse–Ferretti forms of Siegel's lemma over `ℚ` and over arbitrary number
fields:

* **Over `ℚ` in the sup norm** (`Submodule.exists_ne_zero_mem_intPoints_norm_le`,
  `Matrix.exists_ne_zero_mulVec_eq_zero_norm_le`): a nonzero `k`-dimensional subspace `V` of `ℚ^ι`
  contains a nonzero integer vector `z` with `‖z‖ ≤ H(V) ^ (1 / k)`, and an integer system `A x = 0`
  of `p` independent equations in `n > p` unknowns has a nonzero integer solution with
  `‖x‖ ≤ (√det(A Aᵀ) / minorGcd A) ^ (1 / (n - p))` (Bombieri–Vaaler, Theorem 1).
* **Over a number field `K` of degree `D = [K : ℚ]` with `r₁` real and `r₂` complex places**:
  for a nonzero `k`-dimensional `K`-subspace `W` of `ι → K`, `W ∩ 𝓞_K^ι` contains nonzero integral
  vectors satisfying the sup-height bound
  `H_abs(z) ≤ (2 / π) ^ (r₂ / D) * |discr K| ^ (1 / (2 * D)) * H₂(W) ^ (1 / k)`
  (`Submodule.exists_ne_zero_mem_integerPoints_absHeight_le`), the exact unit-ball Euclidean-height
  bound (`Submodule.exists_ne_zero_mem_integerPoints_height2_le`), and the Gamma-free Euclidean
  bound `H₂(z) ≤ √k * |discr K| ^ (1 / (2 * D)) * H₂(W) ^ (1 / k)`
  (`Submodule.exists_ne_zero_mem_integerPoints_height2_le_sqrt`), together with the corresponding
  kernel theorems for any `m × ι` matrix `A` of rank `R < #ι`.
* **Without row independence or coordinate ordering** (Evertse–Ferretti, Lemma 13.1): for any
  `#m < #ι` nonzero linear forms `L : m → ι → K`, passing to a maximal linearly independent
  subfamily bounds the row-space height by `∏ i, H₂(L i)` since `1 ≤ H₂(L i)` for nonzero forms,
  while `#ι - #m ≤ #ι - R` and `1 ≤ H₂(rowSpace L)` only weaken the exponent. This yields
  `Matrix.exists_ne_zero_mulVec_eq_zero_height2_le_of_card_lt` over `𝓞 K` and
  `TauCeti.exists_ne_zero_height2_le` over `K`:
  `H₂(x) ≤ √(#ι) * |discr K| ^ (1 / (2 * D)) * (∏ i, H₂(L i)) ^ (1 / (#ι - #m))`.

## Main results

* `Submodule.exists_ne_zero_mem_intPoints_norm_le`,
  `Matrix.exists_ne_zero_mulVec_eq_zero_norm_le`: Bombieri and Vaaler's Theorem 1 over `ℚ` / `ℤ`.
* `Submodule.exists_ne_zero_mem_integerPoints_absHeight_le`,
  `Submodule.exists_ne_zero_mem_integerPoints_height2_le`,
  `Submodule.exists_ne_zero_mem_integerPoints_height2_le_sqrt`: number-field subspace Siegel lemmas
  in sup height and Euclidean height.
* `Matrix.exists_ne_zero_mulVec_eq_zero_absHeight_le`,
  `Matrix.exists_ne_zero_mulVec_eq_zero_height2_le`,
  `Matrix.exists_ne_zero_mulVec_eq_zero_height2_le_sqrt`: number-field matrix Siegel lemmas in terms
  of `A.rank` and the row-space height.
* `Matrix.exists_ne_zero_mulVec_eq_zero_height2_le_of_card_lt`,
  `TauCeti.exists_ne_zero_height2_le`: Evertse and Ferretti's fixed-field Siegel lemma (Lemma 13.1)
  without row-independence or coordinate-order hypotheses.

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32,
  Theorems 1, 2, and 8.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  §2.9, Corollary 2.9.7.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §13, Lemma 13.1.
-/

public section

noncomputable section

open MeasureTheory Metric Module NumberField NumberField.InfinitePlace TauCeti
open scoped BigOperators Matrix

private theorem exists_le_rpow_inv_of_prod_le {k : ℕ} (hk : 0 < k) {f : Fin k → ℝ}
    {B : ℝ} (hB : 0 < B) (hle : ∏ i, f i ≤ B) : ∃ i, f i ≤ B ^ (k : ℝ)⁻¹ := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  by_contra! h
  have hprod := Finset.prod_lt_prod_of_nonempty₀
    (fun _ _ => Real.rpow_pos_of_pos hB _) (fun i _ => h i) Finset.univ_nonempty
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Real.rpow_inv_natCast_pow hB.le hk.ne'] at hprod
  exact hprod.not_ge hle

/-- Extracting a maximal linearly independent subfamily bounds the subspace height of the span of
any finite family of nonzero vectors by the product of their Euclidean heights. -/
private theorem subspaceHeight_span_range_le_prod {K m ι : Type*} [Field K] [NumberField K]
    [Fintype m] [Finite ι] [LinearOrder ι] {v : m → ι → K} (hv : ∀ i, v i ≠ 0) :
    Submodule.subspaceHeight (Submodule.span K (Set.range v)) ≤ ∏ i, height2 (v i) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K v
  have : Finite κ := Finite.of_injective a ha
  let _ := Fintype.ofFinite κ
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have hli' : LinearIndependent K (v ∘ a ∘ e) := hli.comp e e.injective
  have hrange : Set.range (v ∘ a ∘ e) = Set.range (v ∘ a) := by
    ext x
    simp [e.surjective.exists]
  rw [← hspan, ← hrange]
  refine (Submodule.subspaceHeight_le_prod hli').trans ?_
  let emb : Fin (Fintype.card κ) ↪ m := e.toEmbedding.trans ⟨a, ha⟩
  calc ∏ j, height2 ((v ∘ a ∘ e) j)
      = ∏ i ∈ Finset.univ.map emb, height2 (v i) :=
        (Finset.prod_map Finset.univ emb fun i ↦ height2 (v i)).symm
    _ ≤ ∏ i, height2 (v i) :=
      Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
        (fun i _ ↦ height2_nonneg (v i)) fun i _ _ ↦ one_le_height2_of_ne_zero (hv i)

namespace Submodule

section Rational

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

end Rational

section NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι] [LinearOrder ι]

open scoped Classical in
/-- **Siegel's lemma for a subspace over a number field, sup height** (Bombieri–Vaaler). A nonzero
`K`-subspace `W` of `ι → K` of dimension `k` contains a nonzero integral point `z ∈ W ∩ 𝓞_K^ι`
whose absolute projective sup height satisfies
`H_abs(z) ≤ (2 / π) ^ (r₂ / D) * |discr K| ^ (1 / (2 * D)) * H₂(W) ^ (1 / k)`,
where `D = [K : ℚ]` and `r₂ = nrComplexPlaces K`. -/
theorem exists_ne_zero_mem_integerPoints_absHeight_le {W : Submodule K (ι → K)} (hW : W ≠ ⊥) :
    ∃ z ∈ W.integerPoints, z ≠ 0 ∧
      absoluteProjectiveTupleHeight (fun i ↦ (z i : K)) ≤
        (2 / Real.pi) ^ ((nrComplexPlaces K : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
            W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  obtain ⟨z, hz, _, hzW, hle⟩ := W.exists_linearIndependent_integerPoints_prod_absHeight_le
  have hk : 0 < finrank K W := finrank_pos
  have hk_ne : (finrank K W : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hB := lt_of_lt_of_le (Finset.prod_pos fun _ _ ↦ absoluteProjectiveTupleHeight_pos _) hle
  obtain ⟨j, hj⟩ := exists_le_rpow_inv_of_prod_le hk hB hle
  refine ⟨z j, hzW j, mt RingOfIntegers.coe_tuple_eq_zero_iff.2 (hz.ne_zero j), hj.trans_eq ?_⟩
  have hexp₁ :
      (finrank K W * nrComplexPlaces K : ℝ) / finrank ℚ K * (finrank K W : ℝ)⁻¹ =
        (nrComplexPlaces K : ℝ) / finrank ℚ K := by
    field_simp [hk_ne]
  have hexp₂ :
      (finrank K W : ℝ) / (2 * finrank ℚ K) * (finrank K W : ℝ)⁻¹ =
        (2 * finrank ℚ K : ℝ)⁻¹ := by
    field_simp [hk_ne]
  rw [Real.mul_rpow (by positivity) (Submodule.subspaceHeight_pos W).le,
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (abs_nonneg _), hexp₁, hexp₂]

open scoped Classical in
/-- **Siegel's lemma for a subspace over a number field, Euclidean height.** A nonzero `K`-subspace
`W` of `ι → K` of dimension `k` contains a nonzero integral point `z ∈ W ∩ 𝓞_K^ι` satisfying
`H₂(z) ≤ ((2 ^ k / ω_k) ^ r₁ * (2 ^ k / ω_{2k}) ^ r₂) ^ (1 / (D * k)) *`
`|discr K| ^ (1 / (2 * D)) * H₂(W) ^ (1 / k)`. -/
theorem exists_ne_zero_mem_integerPoints_height2_le {W : Submodule K (ι → K)} (hW : W ≠ ⊥) :
    ∃ z ∈ W.integerPoints, z ≠ 0 ∧
      height2 (fun i ↦ (z i : K)) ≤
        (((2 : ℝ) ^ finrank K W /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1)) ^ nrRealPlaces K *
          ((2 : ℝ) ^ finrank K W /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1)) ^
              nrComplexPlaces K) ^ (finrank ℚ K * finrank K W : ℝ)⁻¹ *
          |(discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
            W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  obtain ⟨z, hz, _, hzW, hle⟩ := W.exists_linearIndependent_integerPoints_prod_height2_le
  have hk : 0 < finrank K W := finrank_pos
  have hk_ne : (finrank K W : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hB := lt_of_lt_of_le (Finset.prod_pos fun j _ ↦ height2_pos (hz.ne_zero j)) hle
  obtain ⟨j, hj⟩ := exists_le_rpow_inv_of_prod_le hk hB hle
  refine ⟨z j, hzW j, mt RingOfIntegers.coe_tuple_eq_zero_iff.2 (hz.ne_zero j), hj.trans_eq ?_⟩
  have hexp₁ : (finrank ℚ K : ℝ)⁻¹ * (finrank K W : ℝ)⁻¹ =
      (finrank ℚ K * finrank K W : ℝ)⁻¹ := (mul_inv _ _).symm
  have hexp₂ :
      (finrank K W : ℝ) / (2 * finrank ℚ K) * (finrank K W : ℝ)⁻¹ =
        (2 * finrank ℚ K : ℝ)⁻¹ := by
    field_simp [hk_ne]
  rw [Real.mul_rpow (by positivity) (Submodule.subspaceHeight_pos W).le,
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (abs_nonneg _), hexp₁, hexp₂]

/-- **Gamma-free Euclidean Siegel lemma for a subspace over a number field.** A nonzero `K`-subspace
`W` of `ι → K` of dimension `k` contains a nonzero integral point `z ∈ W ∩ 𝓞_K^ι` satisfying
`H₂(z) ≤ √k * |discr K| ^ (1 / (2 * D)) * H₂(W) ^ (1 / k)`. -/
theorem exists_ne_zero_mem_integerPoints_height2_le_sqrt {W : Submodule K (ι → K)} (hW : W ≠ ⊥) :
    ∃ z ∈ W.integerPoints, z ≠ 0 ∧
      height2 (fun i ↦ (z i : K)) ≤
        √(finrank K W : ℝ) * |(discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  obtain ⟨z, hz, _, hzW, hle⟩ := W.exists_linearIndependent_integerPoints_prod_height2_le_sqrt_pow
  have hk : 0 < finrank K W := finrank_pos
  have hB := lt_of_lt_of_le (Finset.prod_pos fun j _ ↦ height2_pos (hz.ne_zero j)) hle
  obtain ⟨j, hj⟩ := exists_le_rpow_inv_of_prod_le hk hB hle
  refine ⟨z j, hzW j, mt RingOfIntegers.coe_tuple_eq_zero_iff.2 (hz.ne_zero j), hj.trans_eq ?_⟩
  rw [Real.mul_rpow (by positivity) (Submodule.subspaceHeight_pos W).le,
    Real.pow_rpow_inv_natCast (by positivity) hk.ne']

end NumberField

end Submodule

namespace Matrix

section Rational

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

end Rational

section NumberField

variable {K m ι : Type*} [Field K] [NumberField K]

section Ordered

variable [Finite m] [Fintype ι] [LinearOrder ι]

omit [Finite m] [LinearOrder ι] in
private theorem finrank_ker_mulVecLin_eq (A : Matrix m ι K) :
    finrank K (LinearMap.ker A.mulVecLin) = Fintype.card ι - A.rank := by
  have h := A.mulVecLin.finrank_range_add_finrank_ker
  rw [← Matrix.rank, Module.finrank_fintype_fun_eq_card] at h
  omega

open scoped Classical in
/-- **Siegel's lemma for a matrix over a number field, sup height** (Bombieri–Vaaler). If
`A : Matrix m ι K` has rank `R < #ι`, then `A x = 0` has a nonzero integral solution `x : ι → 𝓞 K`
satisfying
`H_abs(x) ≤ (2 / π) ^ (r₂ / D) * |discr K| ^ (1 / (2 * D)) * H₂(rowSpace A) ^ (1 / (#ι - R))`. -/
theorem exists_ne_zero_mulVec_eq_zero_absHeight_le {A : Matrix m ι K}
    (hA : A.rank < Fintype.card ι) :
    ∃ x : ι → 𝓞 K, x ≠ 0 ∧ A *ᵥ (fun j ↦ (x j : K)) = 0 ∧
      absoluteProjectiveTupleHeight (fun j ↦ (x j : K)) ≤
        (2 / Real.pi) ^ ((nrComplexPlaces K : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
            (Submodule.span K (Set.range A.row)).subspaceHeight ^
              ((Fintype.card ι : ℝ) - A.rank)⁻¹ := by
  set W := LinearMap.ker A.mulVecLin
  have hfin : finrank K W = Fintype.card ι - A.rank := finrank_ker_mulVecLin_eq A
  have hW : W ≠ ⊥ := fun hbot ↦ by
    have h0 : finrank K W = 0 := by simp [hbot]
    omega
  obtain ⟨x, hxW, hx0, hle⟩ := W.exists_ne_zero_mem_integerPoints_absHeight_le hW
  rw [Submodule.mem_integerPoints, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hxW
  rw [hfin, A.subspaceHeight_ker_mulVecLin, Nat.cast_sub hA.le] at hle
  exact ⟨x, hx0, hxW, hle⟩

open scoped Classical in
/-- **Siegel's lemma for a matrix over a number field, Euclidean height.** If `A : Matrix m ι K` has
rank `R < #ι` and `k = #ι - R`, then `A x = 0` has a nonzero integral solution `x : ι → 𝓞 K`
satisfying
`H₂(x) ≤ ((2 ^ k / ω_k) ^ r₁ * (2 ^ k / ω_{2k}) ^ r₂) ^ (1 / (D * k)) *`
`|discr K| ^ (1 / (2 * D)) * H₂(rowSpace A) ^ (1 / k)`. -/
theorem exists_ne_zero_mulVec_eq_zero_height2_le {A : Matrix m ι K}
    (hA : A.rank < Fintype.card ι) :
    ∃ x : ι → 𝓞 K, x ≠ 0 ∧ A *ᵥ (fun j ↦ (x j : K)) = 0 ∧
      height2 (fun j ↦ (x j : K)) ≤
        (((2 : ℝ) ^ (Fintype.card ι - A.rank) /
            volume.real
              (ball (0 : EuclideanSpace ℝ (Fin (Fintype.card ι - A.rank))) 1)) ^ nrRealPlaces K *
          ((2 : ℝ) ^ (Fintype.card ι - A.rank) /
            volume.real
              (ball (0 : EuclideanSpace ℝ (Fin (2 * (Fintype.card ι - A.rank)))) 1)) ^
              nrComplexPlaces K) ^
            (finrank ℚ K * (Fintype.card ι - A.rank : ℕ) : ℝ)⁻¹ *
          |(discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
            (Submodule.span K (Set.range A.row)).subspaceHeight ^
              ((Fintype.card ι : ℝ) - A.rank)⁻¹ := by
  set W := LinearMap.ker A.mulVecLin
  have hfin : finrank K W = Fintype.card ι - A.rank := finrank_ker_mulVecLin_eq A
  have hW : W ≠ ⊥ := fun hbot ↦ by
    have h0 : finrank K W = 0 := by simp [hbot]
    omega
  obtain ⟨x, hxW, hx0, hle⟩ := W.exists_ne_zero_mem_integerPoints_height2_le hW
  rw [Submodule.mem_integerPoints, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hxW
  rw [hfin, A.subspaceHeight_ker_mulVecLin] at hle
  refine ⟨x, hx0, hxW, hle.trans_eq ?_⟩
  rw [Nat.cast_sub hA.le]

/-- **Gamma-free Euclidean Siegel lemma for a matrix over a number field.** If `A : Matrix m ι K`
has rank `R < #ι`, then `A x = 0` has a nonzero integral solution `x : ι → 𝓞 K` satisfying
`H₂(x) ≤ √(#ι - R) * |discr K| ^ (1 / (2 * D)) * H₂(rowSpace A) ^ (1 / (#ι - R))`. -/
theorem exists_ne_zero_mulVec_eq_zero_height2_le_sqrt {A : Matrix m ι K}
    (hA : A.rank < Fintype.card ι) :
    ∃ x : ι → 𝓞 K, x ≠ 0 ∧ A *ᵥ (fun j ↦ (x j : K)) = 0 ∧
      height2 (fun j ↦ (x j : K)) ≤
        √((Fintype.card ι - A.rank : ℕ) : ℝ) * |(discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          (Submodule.span K (Set.range A.row)).subspaceHeight ^
            ((Fintype.card ι : ℝ) - A.rank)⁻¹ := by
  set W := LinearMap.ker A.mulVecLin
  have hfin : finrank K W = Fintype.card ι - A.rank := finrank_ker_mulVecLin_eq A
  have hW : W ≠ ⊥ := fun hbot ↦ by
    have h0 : finrank K W = 0 := by simp [hbot]
    omega
  obtain ⟨x, hxW, hx0, hle⟩ := W.exists_ne_zero_mem_integerPoints_height2_le_sqrt hW
  rw [Submodule.mem_integerPoints, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hxW
  rw [hfin, A.subspaceHeight_ker_mulVecLin] at hle
  refine ⟨x, hx0, hxW, hle.trans_eq ?_⟩
  congr 2
  rw [Nat.cast_sub hA.le]

end Ordered

/-- **Fixed-field Siegel's lemma over `𝓞 K`, in Euclidean height** (Evertse–Ferretti, Lemma 13.1).
For an `m × ι` matrix `A` over a number field `K` with `#m < #ι` and nonzero rows, without assuming
that the rows are linearly independent, `A x = 0` has a nonzero integral solution `x : ι → 𝓞 K`
satisfying
`H₂(x) ≤ √(#ι) * |discr K| ^ (1 / (2 * [K : ℚ])) * (∏ i, H₂(A.row i)) ^ (1 / (#ι - #m))`. -/
theorem exists_ne_zero_mulVec_eq_zero_height2_le_of_card_lt [Fintype m] [Fintype ι]
    {A : Matrix m ι K} (hA : ∀ i, A.row i ≠ 0) (hm : Fintype.card m < Fintype.card ι) :
    ∃ x : ι → 𝓞 K, x ≠ 0 ∧ A *ᵥ (fun j ↦ (x j : K)) = 0 ∧
      height2 (fun j ↦ (x j : K)) ≤
        √(Fintype.card ι : ℝ) * |(discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          (∏ i, height2 (A.row i)) ^ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹ := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hrank_le : A.rank ≤ Fintype.card m := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
      Submodule.finrank_le (LinearMap.range A.mulVecLin)
  have hrank_lt : A.rank < Fintype.card ι := hrank_le.trans_lt hm
  obtain ⟨x, hx0, hAx, hxle⟩ := exists_ne_zero_mulVec_eq_zero_height2_le_sqrt hrank_lt
  refine ⟨x, hx0, hAx, hxle.trans ?_⟩
  set U := Submodule.span K (Set.range A.row)
  have hsqrt : √((Fintype.card ι - A.rank : ℕ) : ℝ) ≤ √(Fintype.card ι : ℝ) :=
    Real.sqrt_le_sqrt (Nat.cast_le.2 (Nat.sub_le _ _))
  have hsub_pos : 0 < ((Fintype.card ι - Fintype.card m : ℕ) : ℝ) :=
    Nat.cast_pos.2 (Nat.sub_pos_of_lt hm)
  have hexp :
      ((Fintype.card ι : ℝ) - A.rank)⁻¹ ≤ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹ := by
    rw [← Nat.cast_sub hrank_lt.le, ← Nat.cast_sub hm.le]
    exact inv_anti₀ hsub_pos (Nat.cast_le.2 (Nat.sub_le_sub_left hrank_le _))
  have hH_le : U.subspaceHeight ≤ ∏ i, height2 (A.row i) :=
    subspaceHeight_span_range_le_prod hA
  have hrpow :
      U.subspaceHeight ^ ((Fintype.card ι : ℝ) - A.rank)⁻¹ ≤
        (∏ i, height2 (A.row i)) ^ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹ := by
    have hpos_exp : 0 ≤ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹ := by
      rw [← Nat.cast_sub hm.le]
      positivity
    exact (Real.rpow_le_rpow_of_exponent_le (Submodule.one_le_subspaceHeight U) hexp).trans
      (Real.rpow_le_rpow (Submodule.subspaceHeight_pos U).le hH_le hpos_exp)
  exact mul_le_mul (mul_le_mul_of_nonneg_right hsqrt (by positivity)) hrpow
    (Real.rpow_nonneg (Submodule.subspaceHeight_pos U).le _) (by positivity)

end NumberField

end Matrix

namespace TauCeti

/-- **Fixed-field Siegel's lemma for linear forms, in Euclidean height** (Evertse–Ferretti,
Lemma 13.1). Let `K` be a number field of degree `D = [K : ℚ]` and discriminant `discr K`. For any
family `L : m → ι → K` of `#m < #ι` nonzero linear forms in `#ι` variables, without assuming linear
independence, there exists a nonzero vector `x : ι → K` in their common kernel satisfying
`H₂(x) ≤ √(#ι) * |discr K| ^ (1 / (2 * D)) * (∏ i, H₂(L i)) ^ (1 / (#ι - #m))`. -/
theorem exists_ne_zero_height2_le {K m ι : Type*} [Field K] [NumberField K] [Fintype m] [Fintype ι]
    {L : m → ι → K} (hL : ∀ i, L i ≠ 0) (hm : Fintype.card m < Fintype.card ι) :
    ∃ x : ι → K, x ≠ 0 ∧ (∀ i, ∑ j, L i j * x j = 0) ∧
      height2 x ≤
        √(Fintype.card ι : ℝ) * |(discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          (∏ i, height2 (L i)) ^ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹ := by
  obtain ⟨z, hz0, hLz, hle⟩ :=
    Matrix.exists_ne_zero_mulVec_eq_zero_height2_le_of_card_lt (A := Matrix.of L) hL hm
  refine ⟨fun j ↦ (z j : K), mt RingOfIntegers.coe_tuple_eq_zero_iff.1 hz0, fun i ↦ ?_, hle⟩
  simpa [Matrix.mulVec, dotProduct] using congrFun hLz i

end TauCeti

end
