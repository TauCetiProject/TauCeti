/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.NumberTheory.Height.Arakelov.KernelBasis
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.MeasureTheory.Group.GeometryOfNumbers
import TauCeti.NumberTheory.Height.Arakelov.Subspace.Bounds
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.MulVolume

/-!
# Siegel's lemma via Arakelov subspace heights

Taking the smallest-height vector in the basis theorems of `BombieriVaaler` and `KernelBasis` yields
Bombieri–Vaaler and Evertse–Ferretti forms of Siegel's lemma over `ℚ` and over arbitrary number
fields:

* **Over `ℚ` in the sup norm and Euclidean height**
  (`Submodule.exists_ne_zero_mem_intPoints_norm_le`,
  `Submodule.exists_ne_zero_mem_intPoints_height2_le`,
  `Matrix.exists_ne_zero_mulVec_eq_zero_norm_le`,
  `Matrix.exists_ne_zero_int_mulVec_eq_zero_height2_le`): a nonzero `k`-dimensional subspace `V` of
  `ℚ^ι` contains a nonzero integer vector `z` with `‖z‖ ≤ H(V) ^ (1 / k)` and
  `H₂(z) ≤ √k * H(V) ^ (1 / k)`, an integer system `A x = 0` of `p` independent equations in
  `n > p` unknowns has a nonzero integer solution with
  `‖x‖ ≤ (√det(A Aᵀ) / minorGcd A) ^ (1 / (n - p))` (Bombieri–Vaaler, Theorem 1), and any
  rational system `A x = 0` of `#m < #ι` nonzero rows has a nonzero integer solution with
  `H₂(x) ≤ √(#ι) * (∏ i, H₂(A.row i)) ^ (1 / (#ι - #m))`.
* **Over a number field `K` of degree `D = [K : ℚ]` with `r₁` real and `r₂` complex places**:
  for a nonzero `k`-dimensional `K`-subspace `W` of `ι → K`, `W ∩ 𝓞_K^ι` contains nonzero integral
  vectors satisfying `H_abs(z) ≤ (2 / π) ^ (r₂ / D) * |discr K| ^ (1 / (2 * D)) * H₂(W) ^ (1 / k)`
  (`Submodule.exists_ne_zero_mem_integerPoints_absHeight_le`), the exact unit-ball Euclidean-height
  bound (`Submodule.exists_ne_zero_mem_integerPoints_height2_le`), the sharp `(D * k)`-dimensional
  Minkowski-ball bound `H₂(z) ≤ 2 / √(D * π) * Γ(D * k / 2 + 1) ^ (1 / (D * k)) *
  |discr K| ^ (1 / (2 * D)) * H₂(W) ^ (1 / k)`
  (`Submodule.exists_ne_zero_mem_integerPoints_height2_le_mul_Gamma_rpow`, obtained by scaling
  `W.integerLattice` by `W.mulMixedSubmodule (multSqrt K)`), and the Gamma-free bound
  `H₂(z) ≤ √k * |discr K| ^ (1 / (2 * D)) * H₂(W) ^ (1 / k)`
  (`Submodule.exists_ne_zero_mem_integerPoints_height2_le_sqrt`), together with the corresponding
  kernel theorems for any `m × ι` matrix `A` of rank `R < #ι`.
* **Without row independence or coordinate ordering** (Evertse–Ferretti, Lemma 13.1): for any
  `#m < #ι` nonzero linear forms `L : m → ι → K`, passing to a maximal linearly independent
  subfamily bounds the row-space height by `∏ i, H₂(L i)`, yielding
  `Matrix.exists_ne_zero_mulVec_eq_zero_height2_le_of_card_lt` over `𝓞 K` and
  `TauCeti.exists_ne_zero_height2_le` over `K`:
  `H₂(x) ≤ √(#ι) * |discr K| ^ (1 / (2 * D)) * (∏ i, H₂(L i)) ^ (1 / (#ι - #m))`.

## Main results

* `Submodule.exists_ne_zero_mem_intPoints_norm_le`,
  `Submodule.exists_ne_zero_mem_intPoints_height2_le`,
  `Matrix.exists_ne_zero_mulVec_eq_zero_norm_le`,
  `Matrix.exists_ne_zero_int_mulVec_eq_zero_height2_le`: Bombieri–Vaaler and Euclidean Siegel lemmas
  over `ℚ` / `ℤ`.
* `Submodule.exists_ne_zero_mem_integerPoints_absHeight_le`,
  `Submodule.exists_ne_zero_mem_integerPoints_height2_le`,
  `Submodule.exists_ne_zero_mem_integerPoints_height2_le_mul_Gamma_rpow`,
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

omit [NumberField K] [LinearOrder ι] in
private theorem exists_ne_zero_mem_integerPoints_of_prod_le {W : Submodule K (ι → K)} (hW : W ≠ ⊥)
    {f : (ι → K) → ℝ} (hf : ∀ v : ι → K, v ≠ 0 → 0 < f v) {B C : ℝ}
    (h : ∃ z : Fin (finrank K W) → ι → 𝓞 K, LinearIndependent K (fun j i ↦ (z j i : K)) ∧
      span K (Set.range fun j i ↦ (z j i : K)) = W ∧ (∀ j, z j ∈ W.integerPoints) ∧
      ∏ j, f (fun i ↦ (z j i : K)) ≤ B)
    (hBC : 0 < finrank K W → B ^ (finrank K W : ℝ)⁻¹ = C) :
    ∃ z ∈ W.integerPoints, z ≠ 0 ∧ f (fun i ↦ (z i : K)) ≤ C := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hk : 0 < finrank K W := finrank_pos
  obtain ⟨z, hz, _, hzW, hle⟩ := h
  have hB := lt_of_lt_of_le (Finset.prod_pos fun j _ ↦ hf _ (hz.ne_zero j)) hle
  obtain ⟨j, hj⟩ := exists_le_rpow_inv_of_prod_le hk hB hle
  exact ⟨z j, hzW j, mt RingOfIntegers.coe_tuple_eq_zero_iff.2 (hz.ne_zero j),
    hj.trans_eq (hBC hk)⟩

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
  refine exists_ne_zero_mem_integerPoints_of_prod_le hW
    (fun v _ ↦ absoluteProjectiveTupleHeight_pos v)
    W.exists_linearIndependent_integerPoints_prod_absHeight_le fun hk ↦ ?_
  have hk_ne : (finrank K W : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  rw [Real.mul_rpow (by positivity) (Submodule.subspaceHeight_pos W).le,
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (abs_nonneg _)]
  congr 2
  · congr 1; field_simp [hk_ne]
  · congr 1; field_simp [hk_ne]

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
  refine exists_ne_zero_mem_integerPoints_of_prod_le hW (fun _ ↦ height2_pos)
    W.exists_linearIndependent_integerPoints_prod_height2_le fun hk ↦ ?_
  have hk_ne : (finrank K W : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  rw [Real.mul_rpow (by positivity) (Submodule.subspaceHeight_pos W).le,
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (abs_nonneg _), ← mul_inv]
  congr 2; congr 1; field_simp [hk_ne]

/-- **Gamma-free Euclidean Siegel lemma for a subspace over a number field.** A nonzero `K`-subspace
`W` of `ι → K` of dimension `k` contains a nonzero integral point `z ∈ W ∩ 𝓞_K^ι` satisfying
`H₂(z) ≤ √k * |discr K| ^ (1 / (2 * D)) * H₂(W) ^ (1 / k)`. -/
theorem exists_ne_zero_mem_integerPoints_height2_le_sqrt {W : Submodule K (ι → K)} (hW : W ≠ ⊥) :
    ∃ z ∈ W.integerPoints, z ≠ 0 ∧
      height2 (fun i ↦ (z i : K)) ≤
        √(finrank K W : ℝ) * |(discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ :=
  exists_ne_zero_mem_integerPoints_of_prod_le hW (fun _ ↦ height2_pos)
    W.exists_linearIndependent_integerPoints_prod_height2_le_sqrt_pow fun hk ↦ by
      rw [Real.mul_rpow (by positivity) (Submodule.subspaceHeight_pos W).le,
        Real.pow_rpow_inv_natCast (by positivity) hk.ne']

section MinkowskiBall

open NumberField.mixedEmbedding TauCeti.NumberField.mixedEmbedding

open Classical in
/-- The `(D * m)`-th root of the covolume of `W.integerLattice` scaled by
`W.mulMixedSubmodule (multSqrt K)` is `|discr K| ^ (1 / (2 * D)) * W.subspaceHeight ^ (1 / m)`. -/
private theorem covolume_comap_mulMixedSubmodule_multSqrt_rpow [Fintype ι]
    {W : Submodule K (ι → K)} (hW : W ≠ ⊥)
    (eT : W.euclideanSpan ≃L[ℝ] W.euclideanSpan)
    (heT : (eT.toLinearEquiv : W.euclideanSpan →ₗ[ℝ] W.euclideanSpan) =
      W.mulMixedSubmodule (multSqrt K)) :
    ZLattice.covolume (ZLattice.comap ℝ W.integerLattice eT.symm.toLinearMap) ^
        (((finrank ℚ K * finrank K W : ℕ) : ℝ)⁻¹) =
      |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
        W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hD : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.mpr finrank_pos
  have hm : (0 : ℝ) < finrank K W := Nat.cast_pos.mpr finrank_pos
  rw [W.covolume_comap_mulMixedSubmodule_multSqrt eT heT,
    Real.mul_rpow (by positivity) (pow_nonneg (Submodule.subspaceHeight_pos W).le _),
    Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _),
    ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_natCast,
    ← Real.rpow_mul (Submodule.subspaceHeight_pos W).le, Nat.cast_mul]
  congr 1 <;> congr 1 <;> field_simp [hD.ne', hm.ne']

omit [LinearOrder ι] in
open Classical in
/-- For any integral point `z ∈ W.integerPoints`, `height2 z` is bounded by the Euclidean norm of
`W.mulMixedSubmodule (multSqrt K) (W.integerPointsEquivIntegerLattice z)` divided by
`√[K : ℚ]`. -/
private theorem height2_le_norm_mulMixedSubmodule_multSqrt_div [Fintype ι]
    (W : Submodule K (ι → K)) (z : W.integerPoints) :
    height2 (fun i ↦ ((z : ι → 𝓞 K) i : K)) ≤
      ‖W.mulMixedSubmodule (multSqrt K)
          (W.integerPointsEquivIntegerLattice z : W.euclideanSpan)‖ /
        √(finrank ℚ K : ℝ) := by
  refine (height2_le_sqrt_sum_mult_mul_sum_norm_sq_div (z : ι → 𝓞 K)).trans_eq ?_
  rw [← W.norm_sq_mulMixedSubmodule_multSqrt z, Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

open Classical in
/-- **Fixed-field Siegel's lemma for a subspace (sharp Minkowski-ball constant).**
Every nonzero `K`-subspace `W` of `ι → K` of dimension `m` contains a nonzero integral point
`z ∈ W.integerPoints` (`W ∩ 𝓞_K^ι`) with
`height2 z ≤ 2 / √(D * π) * Γ(D * m / 2 + 1) ^ (1 / (D * m)) * |discr K| ^ (1 / (2 * D)) *
  W.subspaceHeight ^ (1 / m)`, where `D = [K : ℚ]`. -/
theorem exists_ne_zero_mem_integerPoints_height2_le_mul_Gamma_rpow {W : Submodule K (ι → K)}
    (hW : W ≠ ⊥) :
    ∃ z ∈ W.integerPoints, z ≠ 0 ∧
      height2 (fun i ↦ (z i : K)) ≤
        2 / √((finrank ℚ K : ℝ) * Real.pi) *
          Real.Gamma ((finrank ℚ K * finrank K W : ℝ) / 2 + 1) ^
            ((finrank ℚ K * finrank K W : ℝ)⁻¹) *
          |(discr K : ℝ)| ^ (1 / (2 * (finrank ℚ K : ℝ))) *
          W.subspaceHeight ^ (finrank K W : ℝ)⁻¹ := by
  cases nonempty_fintype ι
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  set D : ℕ := finrank ℚ K
  set m : ℕ := finrank K W
  set N : ℕ := D * m
  have hD : (0 : ℝ) < D := Nat.cast_pos.mpr finrank_pos
  have hfin : finrank ℝ W.euclideanSpan = N := W.finrank_euclideanSpan
  have : Nontrivial W.euclideanSpan := by
    rw [← finrank_pos_iff (R := ℝ), hfin]
    exact Nat.mul_pos finrank_pos finrank_pos
  set T := W.mulMixedSubmodule (multSqrt K)
  have hT_det : LinearMap.det T ≠ 0 := by
    rw [W.det_mulMixedSubmodule, algebraNorm_multSqrt]
    positivity
  let eT : W.euclideanSpan ≃L[ℝ] W.euclideanSpan :=
    (T.equivOfDetNeZero hT_det).toContinuousLinearEquiv
  have heT : (eT.toLinearEquiv : W.euclideanSpan →ₗ[ℝ] W.euclideanSpan) = T := by
    dsimp only [eT]
    rw [LinearEquiv.toLinearEquiv_toContinuousLinearEquiv, LinearEquiv.coe_ofIsUnitDet]
  let L' : Submodule ℤ W.euclideanSpan := ZLattice.comap ℝ W.integerLattice eT.symm.toLinearMap
  -- Apply Minkowski's shortest-vector bound to the scaled lattice `T (W.integerLattice)`.
  obtain ⟨x, hxL', hx0, hx_norm⟩ := ZLattice.exists_ne_zero_mem_norm_le L'
  have hwL : eT.symm x ∈ W.integerLattice := by
    rwa [← SetLike.mem_coe, ZLattice.coe_comap] at hxL'
  set z : W.integerPoints := W.integerPointsEquivIntegerLattice.symm ⟨eT.symm x, hwL⟩
  have hz_ne : (z : ι → 𝓞 K) ≠ 0 := by
    intro hz0
    apply hx0
    have h0 : (⟨eT.symm x, hwL⟩ : W.integerLattice) = 0 :=
      (W.integerPointsEquivIntegerLattice.symm.map_eq_zero_iff).mp (Subtype.ext hz0)
    exact eT.symm.injective ((congrArg Subtype.val h0).trans (map_zero eT.symm).symm)
  have hTx :
      W.mulMixedSubmodule (multSqrt K) (W.integerPointsEquivIntegerLattice z : W.euclideanSpan) =
        x := by
    have hzw : (W.integerPointsEquivIntegerLattice z : W.euclideanSpan) = eT.symm x :=
      congrArg Subtype.val (W.integerPointsEquivIntegerLattice.apply_symm_apply ⟨eT.symm x, hwL⟩)
    rw [hzw]
    change T (eT.symm x) = x
    rw [← heT]
    exact eT.apply_symm_apply x
  have hcov_rpow := covolume_comap_mulMixedSubmodule_multSqrt_rpow hW eT heT
  rw [hfin, hcov_rpow] at hx_norm
  refine ⟨z, z.property, hz_ne, ?_⟩
  calc height2 (fun i ↦ ((z : ι → 𝓞 K) i : K))
      ≤ ‖x‖ / √(D : ℝ) := hTx ▸ height2_le_norm_mulMixedSubmodule_multSqrt_div W z
    _ ≤ (2 / √Real.pi * Real.Gamma ((N : ℝ) / 2 + 1) ^ ((N : ℝ)⁻¹) *
          (|(discr K : ℝ)| ^ (1 / (2 * (D : ℝ))) * W.subspaceHeight ^ ((m : ℝ)⁻¹))) /
          √(D : ℝ) := div_le_div_of_nonneg_right hx_norm (Real.sqrt_nonneg _)
    _ = 2 / √((D : ℝ) * Real.pi) *
          Real.Gamma ((D * m : ℝ) / 2 + 1) ^ ((D * m : ℝ)⁻¹) *
          |(discr K : ℝ)| ^ (1 / (2 * (D : ℝ))) *
          W.subspaceHeight ^ ((m : ℝ)⁻¹) := by
        rw [Nat.cast_mul, Real.sqrt_mul hD.le]
        ring

end MinkowskiBall

end NumberField

section Rat

variable {ι : Type*} [Finite ι] [LinearOrder ι]

/-- **Siegel's lemma for a rational subspace, in the Euclidean height.**
Every nonzero subspace `V` of `ℚ^ι` of dimension `m` contains a nonzero integral point
`z ∈ V.intPoints` with `height2 z ≤ √m * V.subspaceHeight ^ (1 / m)`. -/
theorem exists_ne_zero_mem_intPoints_height2_le {V : Submodule ℚ (ι → ℚ)} (hV : V ≠ ⊥) :
    ∃ z ∈ V.intPoints, z ≠ 0 ∧
      height2 (fun i ↦ (z i : ℚ)) ≤
        √(finrank ℚ V : ℝ) * V.subspaceHeight ^ (finrank ℚ V : ℝ)⁻¹ := by
  obtain ⟨z, hzV, hz0, hle⟩ := exists_ne_zero_mem_integerPoints_height2_le_sqrt hV
  let w : V.intPoints := V.integerPointsEquivIntPoints ⟨z, hzV⟩
  have hw0 : (w : ι → ℤ) ≠ 0 := by
    intro h
    apply hz0
    have : (⟨z, hzV⟩ : V.integerPoints) = 0 :=
      (V.integerPointsEquivIntPoints.map_eq_zero_iff).mp (Subtype.ext h)
    exact congrArg Subtype.val this
  have hcoe : (fun i ↦ ((w : ι → ℤ) i : ℚ)) = (fun i ↦ (z i : ℚ)) := by
    ext i
    simp [w, Rat.ringOfIntegersEquiv_apply_coe, RingOfIntegers.coe_eq_algebraMap]
  refine ⟨w, w.property, hw0, ?_⟩
  rw [hcoe]
  simpa [discr_rat, finrank_self] using hle

end Rat

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
  exact ⟨x i, hx.ne_zero i, hxker i, by simpa only [Nat.cast_sub hp.le] using hi⟩

end Rational

section NumberField

variable {K m ι : Type*} [Field K] [NumberField K]

section Ordered

variable [Fintype ι] [LinearOrder ι]

private theorem exists_ker_ne_zero_of_subspace {A : Matrix m ι K} (hA : A.rank < Fintype.card ι)
    (f : (ι → K) → ℝ) {B C : ℝ}
    (h : LinearMap.ker A.mulVecLin ≠ ⊥ →
      ∃ x ∈ (LinearMap.ker A.mulVecLin).integerPoints, x ≠ 0 ∧ f (fun j ↦ (x j : K)) ≤ B)
    (hBC : finrank K (LinearMap.ker A.mulVecLin) = Fintype.card ι - A.rank →
      (LinearMap.ker A.mulVecLin).subspaceHeight =
        (Submodule.span K (Set.range A.row)).subspaceHeight → B = C) :
    ∃ x : ι → 𝓞 K, x ≠ 0 ∧ A *ᵥ (fun j ↦ (x j : K)) = 0 ∧ f (fun j ↦ (x j : K)) ≤ C := by
  have hfin := A.finrank_ker_mulVecLin
  have hW : LinearMap.ker A.mulVecLin ≠ ⊥ := fun hbot ↦ by
    have : finrank K (LinearMap.ker A.mulVecLin) = 0 := by simp [hbot]
    omega
  obtain ⟨x, hxW, hx0, hle⟩ := h hW
  rw [Submodule.mem_integerPoints, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hxW
  exact ⟨x, hx0, hxW, hle.trans_eq (hBC hfin A.subspaceHeight_ker_mulVecLin)⟩

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
              ((Fintype.card ι : ℝ) - A.rank)⁻¹ :=
  exists_ker_ne_zero_of_subspace hA absoluteProjectiveTupleHeight
    (LinearMap.ker A.mulVecLin).exists_ne_zero_mem_integerPoints_absHeight_le
    fun hfin hH ↦ by rw [hfin, hH, ← Nat.cast_sub hA.le]

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
              ((Fintype.card ι : ℝ) - A.rank)⁻¹ :=
  exists_ker_ne_zero_of_subspace hA height2
    (LinearMap.ker A.mulVecLin).exists_ne_zero_mem_integerPoints_height2_le
    fun hfin hH ↦ by rw [hfin, hH, ← Nat.cast_sub hA.le]

/-- **Gamma-free Euclidean Siegel lemma for a matrix over a number field.** If `A : Matrix m ι K`
has rank `R < #ι`, then `A x = 0` has a nonzero integral solution `x : ι → 𝓞 K` satisfying
`H₂(x) ≤ √(#ι - R) * |discr K| ^ (1 / (2 * D)) * H₂(rowSpace A) ^ (1 / (#ι - R))`. -/
theorem exists_ne_zero_mulVec_eq_zero_height2_le_sqrt {A : Matrix m ι K}
    (hA : A.rank < Fintype.card ι) :
    ∃ x : ι → 𝓞 K, x ≠ 0 ∧ A *ᵥ (fun j ↦ (x j : K)) = 0 ∧
      height2 (fun j ↦ (x j : K)) ≤
        √((Fintype.card ι - A.rank : ℕ) : ℝ) * |(discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹ *
          (Submodule.span K (Set.range A.row)).subspaceHeight ^
            ((Fintype.card ι : ℝ) - A.rank)⁻¹ :=
  exists_ker_ne_zero_of_subspace hA height2
    (LinearMap.ker A.mulVecLin).exists_ne_zero_mem_integerPoints_height2_le_sqrt
    fun hfin hH ↦ by rw [hfin, hH, ← Nat.cast_sub hA.le]

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
  have hrank_le : A.rank ≤ Fintype.card m := A.rank_le_card_height
  have hrank_lt : A.rank < Fintype.card ι := hrank_le.trans_lt hm
  obtain ⟨x, hx0, hAx, hxle⟩ := exists_ne_zero_mulVec_eq_zero_height2_le_sqrt hrank_lt
  refine ⟨x, hx0, hAx, hxle.trans ?_⟩
  set U := Submodule.span K (Set.range A.row)
  have hsqrt : √((Fintype.card ι - A.rank : ℕ) : ℝ) ≤ √(Fintype.card ι : ℝ) :=
    Real.sqrt_le_sqrt (Nat.cast_le.2 (Nat.sub_le _ _))
  have hexp :
      ((Fintype.card ι : ℝ) - A.rank)⁻¹ ≤ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹ := by
    rw [← Nat.cast_sub hrank_lt.le, ← Nat.cast_sub hm.le]
    exact inv_anti₀ (Nat.cast_pos.2 (Nat.sub_pos_of_lt hm))
      (Nat.cast_le.2 (Nat.sub_le_sub_left hrank_le _))
  have hpos_exp : 0 ≤ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹ := by
    rw [← Nat.cast_sub hm.le]; positivity
  have hrpow := (Real.rpow_le_rpow_of_exponent_le (Submodule.one_le_subspaceHeight U) hexp).trans
    (Real.rpow_le_rpow (Submodule.subspaceHeight_pos U).le
      (Submodule.subspaceHeight_span_range_le_prod hA) hpos_exp)
  exact mul_le_mul (mul_le_mul_of_nonneg_right hsqrt (by positivity)) hrpow
    (Real.rpow_nonneg (Submodule.subspaceHeight_pos U).le _) (by positivity)

end NumberField

section Rat

variable {m ι : Type*} [Fintype m] [Fintype ι]

/-- **Siegel's lemma for a rational linear system, in the Euclidean height.**
For any matrix `A : Matrix m ι ℚ` of `#m < #ι` nonzero rows (without row independence), `A *ᵥ z = 0`
has a nonzero integer solution `z : ι → ℤ` with
`height2 z ≤ √(#ι) * (∏ i, height2 (A.row i)) ^ (1 / (#ι - #m))`. -/
theorem exists_ne_zero_int_mulVec_eq_zero_height2_le {A : Matrix m ι ℚ} (hA : ∀ i, A.row i ≠ 0)
    (hlt : Fintype.card m < Fintype.card ι) :
    ∃ z : ι → ℤ, z ≠ 0 ∧ A *ᵥ (fun i ↦ (z i : ℚ)) = 0 ∧
      height2 (fun i ↦ (z i : ℚ)) ≤
        √(Fintype.card ι : ℝ) *
          (∏ i, height2 (A.row i)) ^ ((Fintype.card ι : ℝ) - Fintype.card m)⁻¹ := by
  obtain ⟨z, hz0, hmul, hle⟩ := exists_ne_zero_mulVec_eq_zero_height2_le_of_card_lt hA hlt
  let w : ι → ℤ := fun i ↦ Rat.ringOfIntegersEquiv (z i)
  have hcoe : (fun i ↦ (w i : ℚ)) = (fun i ↦ (z i : ℚ)) := by
    ext i
    simp [w, Rat.ringOfIntegersEquiv_apply_coe, RingOfIntegers.coe_eq_algebraMap]
  have hw0 : w ≠ 0 := by
    intro h
    apply hz0
    ext1 i
    exact Rat.ringOfIntegersEquiv.injective (by simpa [w] using congrFun h i)
  refine ⟨w, hw0, hcoe.symm ▸ hmul, ?_⟩
  rw [hcoe]
  simpa [discr_rat, finrank_self] using hle

end Rat

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
