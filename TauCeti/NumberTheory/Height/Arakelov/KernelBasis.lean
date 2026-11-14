/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima
public import TauCeti.LinearAlgebra.Matrix.Rank
public import TauCeti.NumberTheory.Height.Arakelov.Subspace.Covolume
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Slice

import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.NumberTheory.GeometryOfNumbers.MinkowskiSecond
import TauCeti.NumberTheory.Height.Extraction

/-!
# Integral bases of bounded height for subspaces and matrix kernels over number fields

Let `K` be a number field of degree `D = [K : ℚ]` with `r₁` real places, `r₂` complex places, and
discriminant `discr K`, and let `W` be a `K`-subspace of `ι → K` of dimension `k`. Inside the
`D * k`-dimensional Euclidean Minkowski span `W.euclideanSpan`, the saturated lattice
`W.integerLattice` (`W ∩ 𝓞_K^ι`) has covolume `((2⁻¹) ^ r₂ * √|discr K|) ^ k * W.subspaceHeight ^ D`
(`Submodule.covolume_integerLattice`).

Combining Minkowski's second theorem
(`ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume`) with the local archimedean
slice volumes from `TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Slice` bounds the product of
the `D * k` real successive minima of `W.integerLattice`:

* for the cube-and-polydisc slice `W.supSlice` (of volume at least `2 ^ (k * r₁) * π ^ (k * r₂)`),
  `∏ i, λ_i ≤ (2 / π) ^ (k * r₂) * √|discr K| ^ k * W.subspaceHeight ^ D`;
* for the Euclidean ball slice `W.euclideanBallSlice` (of volume `ω_k ^ r₁ * ω_{2k} ^ r₂`),
  `∏ i, λ_i ≤ (2 ^ k / ω_k) ^ r₁ * (2 ^ k / ω_{2k}) ^ r₂ * √|discr K| ^ k * W.subspaceHeight ^ D`.

Selecting `k` `K`-linearly independent vectors from a simultaneous real-minima family via
`TauCeti.exists_linearIndependent_prod_absoluteProjectiveTupleHeight_le` and
`TauCeti.exists_linearIndependent_prod_height2_le` (with the `j`-th chosen among the first
`D * j + 1` real minima) produces an integral `K`-basis `x_0, …, x_{k - 1} ∈ W ∩ 𝓞_K^ι` of `W`
whose product of absolute heights is at most the `D`-th root of the successive-minima bound.
Neither freeness of `W ∩ 𝓞_K^ι` over `𝓞 K` nor linear independence of the defining rows of a matrix
`A : Matrix m ι K` is assumed: for `W = LinearMap.ker A.mulVecLin`, Hodge duality identifies
`W.subspaceHeight` with `(span K (range A.row)).subspaceHeight`
(`Matrix.subspaceHeight_ker_mulVecLin`) and `finrank K W = #ι - A.rank`
(`Matrix.finrank_ker_mulVecLin`).

Over `ℚ` (`D = 1`, `r₂ = 0`, `discr ℚ = 1`), the sup-height bound specializes to
`∏ j, H(x_j) ≤ W.subspaceHeight`, recovering the rational Bombieri–Vaaler bound of
`TauCeti.NumberTheory.Height.Arakelov.BombieriVaaler`.

## Main results

* `Submodule.exists_linearIndependent_integerPoints_le_successiveMin_supSlice` and
  `Submodule.exists_linearIndependent_integerPoints_le_successiveMin_euclideanBallSlice`:
  extraction of `k` `K`-linearly independent integral points of `W` from the successive minima of
  `W.integerLattice`, with index bound `(s j : ℕ) ≤ [K : ℚ] * j` and height product at most
  `(∏ i, λ_i) ^ ([K : ℚ] : ℝ)⁻¹`.
* `Submodule.prod_successiveMin_integerLattice_supSlice_le` and
  `Submodule.prod_successiveMin_integerLattice_euclideanBallSlice_le`: upper bounds on the product
  of successive minima of `W.integerLattice` with respect to `W.supSlice` and
  `W.euclideanBallSlice`.
* `Submodule.exists_linearIndependent_integerPoints_prod_absoluteProjectiveTupleHeight_le`,
  `Submodule.exists_basis_integerPoints_prod_absoluteProjectiveTupleHeight_le`,
  `Submodule.exists_linearIndependent_integerPoints_prod_height2_le`, and
  `Submodule.exists_basis_integerPoints_prod_height2_le`: `K`-linearly independent integral tuples
  and `K`-bases of `W` of bounded sup height and Euclidean height.
* `Matrix.subspaceHeight_ker_mulVecLin`: the absolute Euclidean height of
  `LinearMap.ker A.mulVecLin` equals that of the row space `span K (range A.row)`.
* `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_absoluteProjectiveTupleHeight_le`,
  `Matrix.exists_basis_ker_mulVecLin_prod_absoluteProjectiveTupleHeight_le`,
  `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_height2_le`, and
  `Matrix.exists_basis_ker_mulVecLin_prod_height2_le`: Bombieri–Vaaler's kernel-basis Siegel lemma
  over number fields in both sup height and Euclidean height.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §2.8, §2.9 (Theorem 2.9.4, Corollary 2.9.7, Proposition 2.9.18), and Appendix C, Theorem C.3.8.
* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32,
  Theorems 1, 2, and 8.
-/

public section

noncomputable section

open MeasureTheory Metric Module NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding Set TauCeti

namespace Submodule

section Extraction

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} (W : Submodule K (ι → K))

/-- Injective `ℝ`-linear coordinate map from `W.euclideanSpan` into `ι → mixedSpace K`, used to
transport `ℝ`-linear independence from `W.euclideanSpan` to `mixedEmbedding` images. -/
private def spanToMixedPi : W.euclideanSpan →ₗ[ℝ] (ι → mixedSpace K) :=
  (LinearMap.pi fun i ↦
    (euclidean.toMixed K).toLinearMap.comp
      ((LinearMap.proj i).comp
        (WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)).toLinearMap)).comp
    W.euclideanSpan.subtype

private theorem injective_spanToMixedPi : Function.Injective (spanToMixedPi W) :=
  fun _ _ h ↦ Subtype.ext <| WithLp.ofLp_injective 2 <| funext fun i ↦
    (euclidean.toMixed K).injective (congrFun h i)

private theorem spanToMixedPi_eq_mixedEmbedding [Finite ι] {a : W.euclideanSpan}
    (ha : a ∈ W.integerLattice) :
    spanToMixedPi W a =
      (LinearMap.piMap fun _ : ι ↦ (mixedEmbedding K).toRatAlgHom.toLinearMap) fun i ↦
        (((W.integerPointsEquivIntegerLattice.symm ⟨a, ha⟩ :
          W.integerPoints) : ι → 𝓞 K) i : K) := by
  ext1 i
  exact (mixedEmbedding_integerPointsEquivIntegerLattice_symm_apply W ⟨a, ha⟩ i).symm

variable [Fintype ι]

open Classical in
/-- **Basis extraction from successive minima, sup height.** From the `[K : ℚ] * finrank K W`
successive minima of `W.integerLattice` with respect to `W.supSlice`, one extracts `finrank K W`
`K`-linearly independent tuples in `W.integerPoints` at indices `(s j : ℕ) ≤ [K : ℚ] * j` bounded
at every infinite place by the `s j`-th minimum and whose product of absolute sup heights is at
most `(∏ i, λ_i) ^ ([K : ℚ] : ℝ)⁻¹`. -/
theorem exists_linearIndependent_integerPoints_le_successiveMin_supSlice :
    ∃ (x : Fin (finrank K W) → ι → 𝓞 K)
      (s : Fin (finrank K W) → Fin (finrank ℝ W.euclideanSpan)),
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      (∀ j, x j ∈ W.integerPoints) ∧
      (∀ j, (s j : ℕ) ≤ finrank ℚ K * j) ∧
      (∀ j i (w : InfinitePlace K),
        w (x j i : K) ≤ ZLattice.successiveMin W.integerLattice W.supSlice (s j)) ∧
      ∏ j, absoluteProjectiveTupleHeight (fun i ↦ (x j i : K)) ≤
        (∏ i, ZLattice.successiveMin W.integerLattice W.supSlice i) ^ (finrank ℚ K : ℝ)⁻¹ := by
  have h0 := W.zero_mem_interior_supSlice
  obtain ⟨a, ha, haL⟩ :=
    ZLattice.exists_linearIndependent_gauge_eq_successiveMin W.integerLattice h0
  let e : Fin (finrank ℚ K * finrank K W) ≃o Fin (finrank ℝ W.euclideanSpan) :=
    Fin.castOrderIso W.finrank_euclideanSpan.symm
  let u : Fin (finrank ℚ K * finrank K W) → ι → 𝓞 K :=
    fun l ↦ (W.integerPointsEquivIntegerLattice.symm ⟨a (e l), (haL (e l)).1⟩ : W.integerPoints)
  let c : Fin (finrank ℚ K * finrank K W) → ℝ :=
    fun l ↦ ZLattice.successiveMin W.integerLattice W.supSlice (e l)
  let f : (ι → K) →ₗ[ℚ] (ι → mixedSpace K) :=
    LinearMap.piMap fun _ ↦ (mixedEmbedding K).toRatAlgHom.toLinearMap
  have hfu : (fun l ↦ f fun i ↦ (u l i : K)) = fun l ↦ spanToMixedPi W (a (e l)) := by
    ext1 l
    exact (spanToMixedPi_eq_mixedEmbedding W (haL (e l)).1).symm
  have hu_li : LinearIndependent ℝ fun l ↦ f fun i ↦ (u l i : K) := by
    rw [hfu]
    exact (ha.comp _ e.injective).map' (spanToMixedPi W)
      (LinearMap.ker_eq_bot.2 (injective_spanToMixedPi W))
  have hc_mono : Monotone c := (ZLattice.monotone_successiveMin W.integerLattice h0).comp e.monotone
  have hle (l : Fin (finrank ℚ K * finrank K W)) (i : ι) (w : InfinitePlace K) :
      w (u l i : K) ≤ c l := by
    simpa only [u, c, ← (haL (e l)).2] using
      W.apply_le_gauge_supSlice_of_mem_integerLattice (haL (e l)).1 i w
  obtain ⟨s, hs_li, hs_idx, hs_prod⟩ :=
    exists_linearIndependent_prod_absoluteProjectiveTupleHeight_le hu_li hc_mono hle
  have hprod : ∏ l, c l = ∏ i, ZLattice.successiveMin W.integerLattice W.supSlice i :=
    e.toEquiv.prod_comp fun i ↦ ZLattice.successiveMin W.integerLattice W.supSlice i
  exact ⟨fun j ↦ u (s j), fun j ↦ e (s j), hs_li,
    fun j ↦ (W.integerPointsEquivIntegerLattice.symm _).2,
    fun j ↦ hs_idx j, fun j i w ↦ hle (s j) i w, hprod ▸ hs_prod⟩

open Classical in
/-- **Basis extraction from successive minima, Euclidean height.** From the `[K : ℚ] * finrank K W`
successive minima of `W.integerLattice` with respect to `W.euclideanBallSlice`, one extracts
`finrank K W` `K`-linearly independent tuples in `W.integerPoints` at indices
`(s j : ℕ) ≤ [K : ℚ] * j` bounded in local Euclidean norm at every infinite place by the `s j`-th
minimum and whose product of absolute Euclidean heights `height2` is at most
`(∏ i, λ_i) ^ ([K : ℚ] : ℝ)⁻¹`. -/
theorem exists_linearIndependent_integerPoints_le_successiveMin_euclideanBallSlice :
    ∃ (x : Fin (finrank K W) → ι → 𝓞 K)
      (s : Fin (finrank K W) → Fin (finrank ℝ W.euclideanSpan)),
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      (∀ j, x j ∈ W.integerPoints) ∧
      (∀ j, (s j : ℕ) ≤ finrank ℚ K * j) ∧
      (∀ j (w : InfinitePlace K),
        √(∑ i, ‖w.embedding (x j i : K)‖ ^ 2) ≤
          ZLattice.successiveMin W.integerLattice W.euclideanBallSlice (s j)) ∧
      ∏ j, height2 (fun i ↦ (x j i : K)) ≤
        (∏ i, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice i) ^
          (finrank ℚ K : ℝ)⁻¹ := by
  have h0 := W.zero_mem_interior_euclideanBallSlice
  obtain ⟨a, ha, haL⟩ :=
    ZLattice.exists_linearIndependent_gauge_eq_successiveMin W.integerLattice h0
  let e : Fin (finrank ℚ K * finrank K W) ≃o Fin (finrank ℝ W.euclideanSpan) :=
    Fin.castOrderIso W.finrank_euclideanSpan.symm
  let u : Fin (finrank ℚ K * finrank K W) → ι → 𝓞 K :=
    fun l ↦ (W.integerPointsEquivIntegerLattice.symm ⟨a (e l), (haL (e l)).1⟩ : W.integerPoints)
  let c : Fin (finrank ℚ K * finrank K W) → ℝ :=
    fun l ↦ ZLattice.successiveMin W.integerLattice W.euclideanBallSlice (e l)
  let f : (ι → K) →ₗ[ℚ] (ι → mixedSpace K) :=
    LinearMap.piMap fun _ ↦ (mixedEmbedding K).toRatAlgHom.toLinearMap
  have hfu : (fun l ↦ f fun i ↦ (u l i : K)) = fun l ↦ spanToMixedPi W (a (e l)) := by
    ext1 l
    exact (spanToMixedPi_eq_mixedEmbedding W (haL (e l)).1).symm
  have hu_li : LinearIndependent ℝ fun l ↦ f fun i ↦ (u l i : K) := by
    rw [hfu]
    exact (ha.comp _ e.injective).map' (spanToMixedPi W)
      (LinearMap.ker_eq_bot.2 (injective_spanToMixedPi W))
  have hc_mono : Monotone c := (ZLattice.monotone_successiveMin W.integerLattice h0).comp e.monotone
  have hle (l : Fin (finrank ℚ K * finrank K W)) (w : InfinitePlace K) :
      √(∑ i, ‖w.embedding (u l i : K)‖ ^ 2) ≤ c l := by
    simpa only [u, c, ← (haL (e l)).2] using
      W.sqrt_sum_norm_embedding_sq_le_gauge_euclideanBallSlice (haL (e l)).1 w
  obtain ⟨s, hs_li, hs_idx, hs_prod⟩ := exists_linearIndependent_prod_height2_le hu_li hc_mono hle
  have hprod :
      ∏ l, c l = ∏ i, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice i :=
    e.toEquiv.prod_comp fun i ↦ ZLattice.successiveMin W.integerLattice W.euclideanBallSlice i
  exact ⟨fun j ↦ u (s j), fun j ↦ e (s j), hs_li,
    fun j ↦ (W.integerPointsEquivIntegerLattice.symm _).2,
    fun j ↦ hs_idx j, fun j w ↦ hle (s j) w, hprod ▸ hs_prod⟩

end Extraction

section SubspaceBounds

section Helpers

variable {K : Type*} [Field K] [NumberField K]

/-- Cancelling `2 ^ ([K : ℚ] * k)` against `((2⁻¹) ^ r₂) ^ k` via `[K : ℚ] = r₁ + 2 * r₂`. -/
private theorem two_pow_mul_two_inv_pow (k : ℕ) :
    (2 : ℝ) ^ (finrank ℚ K * k) * ((2⁻¹ : ℝ) ^ nrComplexPlaces K) ^ k =
      (2 : ℝ) ^ (k * nrRealPlaces K) * (2 : ℝ) ^ (k * nrComplexPlaces K) := by
  have hdeg : finrank ℚ K * k =
      k * nrRealPlaces K + k * nrComplexPlaces K + k * nrComplexPlaces K := by
    rw [← card_add_two_mul_card_eq_rank (K := K)]
    ring
  rw [hdeg, pow_add, pow_add, ← pow_mul, mul_comm (nrComplexPlaces K) k, mul_assoc,
    ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow, mul_one]

private theorem rpow_sqrt_abs_discr (k : ℕ) :
    (√|(discr K : ℝ)| ^ k) ^ (finrank ℚ K : ℝ)⁻¹ =
      |(discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K)) := by
  have hd : 0 ≤ |(discr K : ℝ)| := abs_nonneg _
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ k, ← Real.rpow_mul hd, ← Real.rpow_mul hd]
  congr 1
  ring

private theorem pow_rpow_inv_nat {a : ℝ} (ha : 0 ≤ a) (n D : ℕ) :
    (a ^ n) ^ (D : ℝ)⁻¹ = a ^ ((n : ℝ) / D) := by
  rw [← Real.rpow_natCast a n, ← Real.rpow_mul ha, div_eq_mul_inv]

end Helpers

section SuccessiveMinBounds

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]
  (W : Submodule K (ι → K))

open Classical in
/-- **Product of successive minima of `W.integerLattice` for `W.supSlice`.** Minkowski's second
theorem, Schmidt's covolume identity, and the cube-and-polydisc slice lower bound yield
`∏ i, λ_i ≤ (2 / π) ^ (k * r₂) * √|discr K| ^ k * W.subspaceHeight ^ [K : ℚ]`. -/
theorem prod_successiveMin_integerLattice_supSlice_le :
    ∏ i, ZLattice.successiveMin W.integerLattice W.supSlice i ≤
      (2 / Real.pi) ^ (finrank K W * nrComplexPlaces K) *
        √|(discr K : ℝ)| ^ finrank K W * W.subspaceHeight ^ finrank ℚ K := by
  have hmink :
      (∏ i, ZLattice.successiveMin W.integerLattice W.supSlice i) *
          volume.real (W.supSlice : Set W.euclideanSpan) ≤
        (2 : ℝ) ^ (finrank ℚ K * finrank K W) *
          (((2⁻¹ : ℝ) ^ nrComplexPlaces K * √|(discr K : ℝ)|) ^ finrank K W *
            W.subspaceHeight ^ finrank ℚ K) := by
    rw [← W.finrank_euclideanSpan, ← W.covolume_integerLattice]
    exact ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume
      W.integerLattice volume (K := W.supSlice) (fun _ ↦ W.neg_mem_supSlice.2)
  have hprod_nn : 0 ≤ ∏ i, ZLattice.successiveMin W.integerLattice W.supSlice i :=
    Finset.prod_nonneg fun i _ ↦ ZLattice.successiveMin_nonneg _ _ i
  have hvol_pos :
      0 < (2 : ℝ) ^ (finrank K W * nrRealPlaces K) *
        Real.pi ^ (finrank K W * nrComplexPlaces K) := by
    positivity
  have hle :=
    (mul_le_mul_of_nonneg_left W.two_pow_mul_pi_pow_le_volume_real_supSlice hprod_nn).trans hmink
  have hpi :
      (2 / Real.pi) ^ (finrank K W * nrComplexPlaces K) *
          Real.pi ^ (finrank K W * nrComplexPlaces K) =
        (2 : ℝ) ^ (finrank K W * nrComplexPlaces K) := by
    rw [← mul_pow, div_mul_cancel₀ _ Real.pi_ne_zero]
  have hrhs :
      (2 : ℝ) ^ (finrank ℚ K * finrank K W) *
          (((2⁻¹ : ℝ) ^ nrComplexPlaces K * √|(discr K : ℝ)|) ^ finrank K W *
            W.subspaceHeight ^ finrank ℚ K) =
        ((2 / Real.pi) ^ (finrank K W * nrComplexPlaces K) *
            √|(discr K : ℝ)| ^ finrank K W * W.subspaceHeight ^ finrank ℚ K) *
          ((2 : ℝ) ^ (finrank K W * nrRealPlaces K) *
            Real.pi ^ (finrank K W * nrComplexPlaces K)) := by
    calc (2 : ℝ) ^ (finrank ℚ K * finrank K W) *
            (((2⁻¹ : ℝ) ^ nrComplexPlaces K * √|(discr K : ℝ)|) ^ finrank K W *
              W.subspaceHeight ^ finrank ℚ K)
        = ((2 : ℝ) ^ (finrank ℚ K * finrank K W) *
            ((2⁻¹ : ℝ) ^ nrComplexPlaces K) ^ finrank K W) *
            (√|(discr K : ℝ)| ^ finrank K W * W.subspaceHeight ^ finrank ℚ K) := by
          rw [mul_pow]; ring
      _ = (2 : ℝ) ^ (finrank K W * nrRealPlaces K) *
            ((2 / Real.pi) ^ (finrank K W * nrComplexPlaces K) *
              Real.pi ^ (finrank K W * nrComplexPlaces K)) *
            (√|(discr K : ℝ)| ^ finrank K W * W.subspaceHeight ^ finrank ℚ K) := by
          rw [two_pow_mul_two_inv_pow, hpi]
      _ = _ := by ring
  exact le_of_mul_le_mul_right (hle.trans_eq hrhs) hvol_pos

open Classical in
/-- **Product of successive minima of `W.integerLattice` for `W.euclideanBallSlice`.** Minkowski's
second theorem, Schmidt's covolume identity, and `W.volume_real_euclideanBallSlice` yield
`∏ i, λ_i ≤ (2 ^ k / ω_k) ^ r₁ * (2 ^ k / ω_{2k}) ^ r₂ * √|discr K| ^ k * W.subspaceHeight ^ D`. -/
theorem prod_successiveMin_integerLattice_euclideanBallSlice_le :
    ∏ i, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice i ≤
      (2 ^ finrank K W /
          volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1)) ^ nrRealPlaces K *
        (2 ^ finrank K W /
          volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1)) ^
          nrComplexPlaces K *
        √|(discr K : ℝ)| ^ finrank K W * W.subspaceHeight ^ finrank ℚ K := by
  let ω₁ := volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1)
  let ω₂ := volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1)
  have hω₁ : 0 < ω₁ := by
    dsimp only [ω₁]
    rw [TauCeti.volume_real_unitBall]
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  have hω₂ : 0 < ω₂ := by
    dsimp only [ω₂]
    rw [TauCeti.volume_real_unitBall]
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  have hmink :
      (∏ i, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice i) *
          (ω₁ ^ nrRealPlaces K * ω₂ ^ nrComplexPlaces K) ≤
        (2 : ℝ) ^ (finrank ℚ K * finrank K W) *
          (((2⁻¹ : ℝ) ^ nrComplexPlaces K * √|(discr K : ℝ)|) ^ finrank K W *
            W.subspaceHeight ^ finrank ℚ K) := by
    dsimp only [ω₁, ω₂]
    rw [← W.volume_real_euclideanBallSlice, ← W.finrank_euclideanSpan, ← W.covolume_integerLattice]
    exact ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume
      W.integerLattice volume (K := W.euclideanBallSlice) (fun _ ↦ W.neg_mem_euclideanBallSlice.2)
  have hc₁ : (2 ^ finrank K W / ω₁) ^ nrRealPlaces K * ω₁ ^ nrRealPlaces K =
      (2 : ℝ) ^ (finrank K W * nrRealPlaces K) := by
    rw [← mul_pow, div_mul_cancel₀ _ hω₁.ne', pow_mul]
  have hc₂ : (2 ^ finrank K W / ω₂) ^ nrComplexPlaces K * ω₂ ^ nrComplexPlaces K =
      (2 : ℝ) ^ (finrank K W * nrComplexPlaces K) := by
    rw [← mul_pow, div_mul_cancel₀ _ hω₂.ne', pow_mul]
  have hrhs :
      (2 : ℝ) ^ (finrank ℚ K * finrank K W) *
          (((2⁻¹ : ℝ) ^ nrComplexPlaces K * √|(discr K : ℝ)|) ^ finrank K W *
            W.subspaceHeight ^ finrank ℚ K) =
        ((2 ^ finrank K W / ω₁) ^ nrRealPlaces K *
            (2 ^ finrank K W / ω₂) ^ nrComplexPlaces K *
            √|(discr K : ℝ)| ^ finrank K W * W.subspaceHeight ^ finrank ℚ K) *
          (ω₁ ^ nrRealPlaces K * ω₂ ^ nrComplexPlaces K) := by
    calc (2 : ℝ) ^ (finrank ℚ K * finrank K W) *
            (((2⁻¹ : ℝ) ^ nrComplexPlaces K * √|(discr K : ℝ)|) ^ finrank K W *
              W.subspaceHeight ^ finrank ℚ K)
        = ((2 : ℝ) ^ (finrank ℚ K * finrank K W) *
            ((2⁻¹ : ℝ) ^ nrComplexPlaces K) ^ finrank K W) *
            (√|(discr K : ℝ)| ^ finrank K W * W.subspaceHeight ^ finrank ℚ K) := by
          rw [mul_pow]; ring
      _ = ((2 ^ finrank K W / ω₁) ^ nrRealPlaces K * ω₁ ^ nrRealPlaces K) *
            ((2 ^ finrank K W / ω₂) ^ nrComplexPlaces K * ω₂ ^ nrComplexPlaces K) *
            (√|(discr K : ℝ)| ^ finrank K W * W.subspaceHeight ^ finrank ℚ K) := by
          rw [two_pow_mul_two_inv_pow, hc₁, hc₂]
      _ = _ := by ring
  exact le_of_mul_le_mul_right (hmink.trans_eq hrhs) (by positivity)

end SuccessiveMinBounds

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι] [LinearOrder ι]
  (W : Submodule K (ι → K))

/-- **Basis form of Siegel's lemma for a subspace, sup height** (Bombieri–Vaaler, Bombieri–Gubler).
Any `K`-subspace `W` of `ι → K` of dimension `k` contains `k` `K`-linearly independent integral
points `x j ∈ W ∩ 𝓞_K^ι` whose product of absolute sup heights satisfies
`∏ j, H(x j) ≤ (2 / π) ^ (k * r₂ / D) * |discr K| ^ (k / (2 * D)) * W.subspaceHeight`,
where `D = [K : ℚ]`. -/
theorem exists_linearIndependent_integerPoints_prod_absoluteProjectiveTupleHeight_le :
    ∃ x : Fin (finrank K W) → ι → 𝓞 K,
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      (∀ j, x j ∈ W.integerPoints) ∧
      ∏ j, absoluteProjectiveTupleHeight (fun i ↦ (x j i : K)) ≤
        (2 / Real.pi) ^ ((finrank K W * nrComplexPlaces K : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) *
          W.subspaceHeight := by
  classical
  cases nonempty_fintype ι
  obtain ⟨x, _, hx_li, hx_mem, -, -, hx_prod⟩ :=
    W.exists_linearIndependent_integerPoints_le_successiveMin_supSlice
  have hmin_nn : 0 ≤ ∏ i, ZLattice.successiveMin W.integerLattice W.supSlice i :=
    Finset.prod_nonneg fun i _ ↦ ZLattice.successiveMin_nonneg _ _ i
  have hH_nn : 0 ≤ W.subspaceHeight := (Submodule.subspaceHeight_pos W).le
  refine ⟨x, hx_li, hx_mem, hx_prod.trans ?_⟩
  calc (∏ i, ZLattice.successiveMin W.integerLattice W.supSlice i) ^ (finrank ℚ K : ℝ)⁻¹
      ≤ ((2 / Real.pi) ^ (finrank K W * nrComplexPlaces K) *
            √|(discr K : ℝ)| ^ finrank K W * W.subspaceHeight ^ finrank ℚ K) ^
          (finrank ℚ K : ℝ)⁻¹ :=
        Real.rpow_le_rpow hmin_nn W.prod_successiveMin_integerLattice_supSlice_le (by positivity)
    _ = (2 / Real.pi) ^ ((finrank K W * nrComplexPlaces K : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) *
          W.subspaceHeight := by
        rw [Real.mul_rpow (by positivity) (pow_nonneg hH_nn _),
          Real.mul_rpow (by positivity) (by positivity),
          pow_rpow_inv_nat (by positivity), Nat.cast_mul, rpow_sqrt_abs_discr,
          Real.pow_rpow_inv_natCast hH_nn finrank_pos.ne']

/-- `Basis` packaging of
`Submodule.exists_linearIndependent_integerPoints_prod_absoluteProjectiveTupleHeight_le`: `W` admits
a `K`-basis `b` with coordinates in `𝓞 K` satisfying the sup-height product bound. -/
theorem exists_basis_integerPoints_prod_absoluteProjectiveTupleHeight_le :
    ∃ b : Basis (Fin (finrank K W)) K W,
      (∀ j i, (b j : ι → K) i ∈ range (algebraMap (𝓞 K) K)) ∧
      ∏ j, absoluteProjectiveTupleHeight (b j : ι → K) ≤
        (2 / Real.pi) ^ ((finrank K W * nrComplexPlaces K : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) *
          W.subspaceHeight := by
  cases nonempty_fintype ι
  obtain ⟨x, hx_li, hx_mem, hx_le⟩ :=
    W.exists_linearIndependent_integerPoints_prod_absoluteProjectiveTupleHeight_le
  let v : Fin (finrank K W) → W := fun j ↦ ⟨fun i ↦ (x j i : K), mem_integerPoints.mp (hx_mem j)⟩
  have hv_li : LinearIndependent K v := LinearIndependent.of_comp W.subtype hx_li
  let b : Basis (Fin (finrank K W)) K W :=
    basisOfLinearIndependentOfCardEqFinrank' v hv_li (Fintype.card_fin _)
  have hb (j : Fin (finrank K W)) : (b j : ι → K) = fun i ↦ (x j i : K) := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  exact ⟨b, fun j i ↦ ⟨x j i, (hb j ▸ rfl : (x j i : K) = (b j : ι → K) i)⟩,
    by simpa only [hb] using hx_le⟩

/-- **Basis form of Siegel's lemma for a subspace, Euclidean height** (Bombieri–Vaaler,
Bombieri–Gubler). Any `K`-subspace `W` of `ι → K` of dimension `k` contains `k` `K`-linearly
independent integral points `x j ∈ W ∩ 𝓞_K^ι` whose product of absolute Euclidean heights `height2`
is bounded in terms of the unit-ball volumes `ω_k` and `ω_{2k}`, `discr K`, and
`W.subspaceHeight`. -/
theorem exists_linearIndependent_integerPoints_prod_height2_le :
    ∃ x : Fin (finrank K W) → ι → 𝓞 K,
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      (∀ j, x j ∈ W.integerPoints) ∧
      ∏ j, height2 (fun i ↦ (x j i : K)) ≤
        (2 ^ finrank K W /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1)) ^
          ((nrRealPlaces K : ℝ) / finrank ℚ K) *
        (2 ^ finrank K W /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1)) ^
          ((nrComplexPlaces K : ℝ) / finrank ℚ K) *
        |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) *
        W.subspaceHeight := by
  classical
  cases nonempty_fintype ι
  set ω₁ := volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1)
  set ω₂ := volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1)
  obtain ⟨x, _, hx_li, hx_mem, -, -, hx_prod⟩ :=
    W.exists_linearIndependent_integerPoints_le_successiveMin_euclideanBallSlice
  have hmin_nn : 0 ≤ ∏ i, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice i :=
    Finset.prod_nonneg fun i _ ↦ ZLattice.successiveMin_nonneg _ _ i
  have hH_nn : 0 ≤ W.subspaceHeight := (Submodule.subspaceHeight_pos W).le
  refine ⟨x, hx_li, hx_mem, hx_prod.trans ?_⟩
  calc (∏ i, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice i) ^ (finrank ℚ K : ℝ)⁻¹
      ≤ ((2 ^ finrank K W / ω₁) ^ nrRealPlaces K *
            (2 ^ finrank K W / ω₂) ^ nrComplexPlaces K *
            √|(discr K : ℝ)| ^ finrank K W * W.subspaceHeight ^ finrank ℚ K) ^
          (finrank ℚ K : ℝ)⁻¹ :=
        Real.rpow_le_rpow hmin_nn
          W.prod_successiveMin_integerLattice_euclideanBallSlice_le (by positivity)
    _ = (2 ^ finrank K W / ω₁) ^ ((nrRealPlaces K : ℝ) / finrank ℚ K) *
          (2 ^ finrank K W / ω₂) ^ ((nrComplexPlaces K : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) *
          W.subspaceHeight := by
        rw [Real.mul_rpow (by positivity) (pow_nonneg hH_nn _),
          Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity),
          pow_rpow_inv_nat (by positivity), pow_rpow_inv_nat (by positivity),
          rpow_sqrt_abs_discr, Real.pow_rpow_inv_natCast hH_nn finrank_pos.ne']

/-- `Basis` packaging of `Submodule.exists_linearIndependent_integerPoints_prod_height2_le`: `W`
admits a `K`-basis `b` with coordinates in `𝓞 K` satisfying the Euclidean-height product bound. -/
theorem exists_basis_integerPoints_prod_height2_le :
    ∃ b : Basis (Fin (finrank K W)) K W,
      (∀ j i, (b j : ι → K) i ∈ range (algebraMap (𝓞 K) K)) ∧
      ∏ j, height2 (b j : ι → K) ≤
        (2 ^ finrank K W /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1)) ^
          ((nrRealPlaces K : ℝ) / finrank ℚ K) *
        (2 ^ finrank K W /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1)) ^
          ((nrComplexPlaces K : ℝ) / finrank ℚ K) *
        |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) *
        W.subspaceHeight := by
  cases nonempty_fintype ι
  obtain ⟨x, hx_li, hx_mem, hx_le⟩ := W.exists_linearIndependent_integerPoints_prod_height2_le
  let v : Fin (finrank K W) → W := fun j ↦ ⟨fun i ↦ (x j i : K), mem_integerPoints.mp (hx_mem j)⟩
  have hv_li : LinearIndependent K v := LinearIndependent.of_comp W.subtype hx_li
  let b : Basis (Fin (finrank K W)) K W :=
    basisOfLinearIndependentOfCardEqFinrank' v hv_li (Fintype.card_fin _)
  have hb (j : Fin (finrank K W)) : (b j : ι → K) = fun i ↦ (x j i : K) := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  exact ⟨b, fun j i ↦ ⟨x j i, (hb j ▸ rfl : (x j i : K) = (b j : ι → K) i)⟩,
    by simpa only [hb] using hx_le⟩

end SubspaceBounds

end Submodule

namespace Matrix

open Submodule

variable {K : Type*} [Field K] [NumberField K] {m ι : Type*} [Fintype ι]
  [LinearOrder ι] (A : Matrix m ι K)

/-- By Hodge duality of Arakelov heights, the absolute Euclidean height of the kernel of a matrix
`A` equals the absolute Euclidean height of its row space `span K (range A.row)`, without any
rank, row-independence, or row-finiteness assumption on `A`. -/
theorem subspaceHeight_ker_mulVecLin :
    (LinearMap.ker A.mulVecLin).subspaceHeight = (span K (range A.row)).subspaceHeight := by
  have hker : LinearMap.ker A.mulVecLin = (span K (range A.row)).euclideanDual := by
    ext x
    rw [LinearMap.mem_ker, mulVecLin_apply, mem_euclideanDual_span]
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    simp only [funext_iff, mulVec_apply, Pi.zero_apply]
  rw [hker, subspaceHeight_euclideanDual]

/-- **Kernel-basis Siegel lemma over number fields, sup height** (Bombieri–Vaaler,
Bombieri–Gubler). For any `m × ι` matrix `A` over `K` (without assuming row independence), the
linear system `A x = 0` admits `k = #ι - A.rank` `K`-linearly independent solutions `x j` in
`𝓞_K^ι` satisfying
`∏ j, H(x j) ≤ (2 / π) ^ (k * r₂ / [K : ℚ]) * |discr K| ^ (k / (2 * [K : ℚ])) * H₂(rowSpace A)`. -/
theorem exists_linearIndependent_mulVec_eq_zero_prod_absoluteProjectiveTupleHeight_le :
    ∃ x : Fin (Fintype.card ι - A.rank) → ι → 𝓞 K,
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      (∀ j, A *ᵥ (fun i ↦ (x j i : K)) = 0) ∧
      ∏ j, absoluteProjectiveTupleHeight (fun i ↦ (x j i : K)) ≤
        (2 / Real.pi) ^
          (((Fintype.card ι - A.rank : ℕ) * nrComplexPlaces K : ℝ) / finrank ℚ K) *
        |(discr K : ℝ)| ^ (((Fintype.card ι - A.rank : ℕ) : ℝ) / (2 * finrank ℚ K)) *
        (span K (range A.row)).subspaceHeight := by
  set W := LinearMap.ker A.mulVecLin
  obtain ⟨z, hz_li, hz_mem, hz_le⟩ :=
    W.exists_linearIndependent_integerPoints_prod_absoluteProjectiveTupleHeight_le
  set e := finCongr A.finrank_ker_mulVecLin
  refine ⟨fun j ↦ z (e.symm j), hz_li.comp _ e.symm.injective, fun j ↦ ?_, ?_⟩
  · exact LinearMap.mem_ker.mp (mem_integerPoints.mp (hz_mem (e.symm j)))
  · rw [e.symm.prod_comp fun l ↦ absoluteProjectiveTupleHeight fun i ↦ (z l i : K)]
    simpa only [W, A.finrank_ker_mulVecLin, A.subspaceHeight_ker_mulVecLin] using hz_le

/-- `Basis` packaging of
`Matrix.exists_linearIndependent_mulVec_eq_zero_prod_absoluteProjectiveTupleHeight_le`: the kernel
`LinearMap.ker A.mulVecLin` admits a `K`-basis `b` indexed by `Fin (#ι - A.rank)` with coordinates
in `𝓞 K` satisfying the sup-height product bound. -/
theorem exists_basis_ker_mulVecLin_prod_absoluteProjectiveTupleHeight_le :
    ∃ b : Basis (Fin (Fintype.card ι - A.rank)) K (LinearMap.ker A.mulVecLin),
      (∀ j i, (b j : ι → K) i ∈ range (algebraMap (𝓞 K) K)) ∧
      ∏ j, absoluteProjectiveTupleHeight (b j : ι → K) ≤
        (2 / Real.pi) ^
          (((Fintype.card ι - A.rank : ℕ) * nrComplexPlaces K : ℝ) / finrank ℚ K) *
        |(discr K : ℝ)| ^ (((Fintype.card ι - A.rank : ℕ) : ℝ) / (2 * finrank ℚ K)) *
        (span K (range A.row)).subspaceHeight := by
  obtain ⟨b, hb_int, hb_le⟩ :=
    (LinearMap.ker A.mulVecLin).exists_basis_integerPoints_prod_absoluteProjectiveTupleHeight_le
  set e := finCongr A.finrank_ker_mulVecLin
  refine ⟨b.reindex e, fun j i ↦ by simpa only [Basis.reindex_apply] using hb_int (e.symm j) i, ?_⟩
  rw [show (∏ j, absoluteProjectiveTupleHeight ((b.reindex e j : LinearMap.ker A.mulVecLin) :
      ι → K)) = ∏ l, absoluteProjectiveTupleHeight (b l : ι → K) by
    simpa only [Basis.reindex_apply] using
      e.symm.prod_comp fun l ↦ absoluteProjectiveTupleHeight (b l : ι → K)]
  simpa only [A.finrank_ker_mulVecLin, A.subspaceHeight_ker_mulVecLin] using hb_le

/-- **Kernel-basis Siegel lemma over number fields, Euclidean height** (Bombieri–Vaaler,
Bombieri–Gubler). For any `m × ι` matrix `A` over `K` (without assuming row independence), the
linear system `A x = 0` admits `k = #ι - A.rank` `K`-linearly independent solutions `x j` in
`𝓞_K^ι` whose product of absolute Euclidean heights `height2` is bounded in terms of `ω_k`,
`ω_{2k}`, `discr K`, and `(span K (range A.row)).subspaceHeight`. -/
theorem exists_linearIndependent_mulVec_eq_zero_prod_height2_le :
    ∃ x : Fin (Fintype.card ι - A.rank) → ι → 𝓞 K,
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      (∀ j, A *ᵥ (fun i ↦ (x j i : K)) = 0) ∧
      ∏ j, height2 (fun i ↦ (x j i : K)) ≤
        (2 ^ (Fintype.card ι - A.rank) /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (Fintype.card ι - A.rank))) 1)) ^
          ((nrRealPlaces K : ℝ) / finrank ℚ K) *
        (2 ^ (Fintype.card ι - A.rank) /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * (Fintype.card ι - A.rank)))) 1)) ^
          ((nrComplexPlaces K : ℝ) / finrank ℚ K) *
        |(discr K : ℝ)| ^ (((Fintype.card ι - A.rank : ℕ) : ℝ) / (2 * finrank ℚ K)) *
        (span K (range A.row)).subspaceHeight := by
  set W := LinearMap.ker A.mulVecLin
  obtain ⟨z, hz_li, hz_mem, hz_le⟩ := W.exists_linearIndependent_integerPoints_prod_height2_le
  set e := finCongr A.finrank_ker_mulVecLin
  refine ⟨fun j ↦ z (e.symm j), hz_li.comp _ e.symm.injective, fun j ↦ ?_, ?_⟩
  · exact LinearMap.mem_ker.mp (mem_integerPoints.mp (hz_mem (e.symm j)))
  · rw [e.symm.prod_comp fun l ↦ height2 fun i ↦ (z l i : K)]
    refine hz_le.trans_eq ?_
    dsimp only [W]
    rw [A.finrank_ker_mulVecLin, A.subspaceHeight_ker_mulVecLin]

/-- `Basis` packaging of `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_height2_le`: the
kernel `LinearMap.ker A.mulVecLin` admits a `K`-basis `b` indexed by `Fin (#ι - A.rank)` with
coordinates in `𝓞 K` satisfying the Euclidean-height product bound. -/
theorem exists_basis_ker_mulVecLin_prod_height2_le :
    ∃ b : Basis (Fin (Fintype.card ι - A.rank)) K (LinearMap.ker A.mulVecLin),
      (∀ j i, (b j : ι → K) i ∈ range (algebraMap (𝓞 K) K)) ∧
      ∏ j, height2 (b j : ι → K) ≤
        (2 ^ (Fintype.card ι - A.rank) /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (Fintype.card ι - A.rank))) 1)) ^
          ((nrRealPlaces K : ℝ) / finrank ℚ K) *
        (2 ^ (Fintype.card ι - A.rank) /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * (Fintype.card ι - A.rank)))) 1)) ^
          ((nrComplexPlaces K : ℝ) / finrank ℚ K) *
        |(discr K : ℝ)| ^ (((Fintype.card ι - A.rank : ℕ) : ℝ) / (2 * finrank ℚ K)) *
        (span K (range A.row)).subspaceHeight := by
  obtain ⟨b, hb_int, hb_le⟩ :=
    (LinearMap.ker A.mulVecLin).exists_basis_integerPoints_prod_height2_le
  set e := finCongr A.finrank_ker_mulVecLin
  refine ⟨b.reindex e, fun j i ↦ by simpa only [Basis.reindex_apply] using hb_int (e.symm j) i, ?_⟩
  rw [show (∏ j, height2 ((b.reindex e j : LinearMap.ker A.mulVecLin) : ι → K)) =
      ∏ l, height2 (b l : ι → K) by
    simpa only [Basis.reindex_apply] using
      e.symm.prod_comp fun l ↦ height2 (b l : ι → K)]
  refine hb_le.trans_eq ?_
  rw [A.finrank_ker_mulVecLin, A.subspaceHeight_ker_mulVecLin]

end Matrix

end
