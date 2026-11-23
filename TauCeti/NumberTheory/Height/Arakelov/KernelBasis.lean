/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima
public import TauCeti.NumberTheory.Height.Arakelov.BombieriVaaler
public import TauCeti.NumberTheory.Height.Arakelov.Comparison
public import TauCeti.NumberTheory.Height.Arakelov.Subspace.Covolume
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.PlaceDecomposition

import TauCeti.LinearAlgebra.LinearIndependent.Extraction.Estimates
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.MeasureTheory.Measure.Haar.EuclideanSpace
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.NumberTheory.GeometryOfNumbers.MinkowskiSecond

/-!
# Kernel bases and subspace bases of bounded height over number fields

Let `K` be a number field of degree `D = [K : ℚ]` with `r₁` real places and `r₂` complex places,
and let `W` be a `K`-subspace of `ι → K` of dimension `k`. Inside `W.euclideanSpan` (of real
dimension `D * k`), `W ∩ 𝓞_K^ι` embeds as the full `ℤ`-lattice `W.integerLattice`, of covolume
`((2⁻¹) ^ r₂ * √|discr K|) ^ k * H₂(W) ^ D` by `Submodule.covolume_integerLattice`.

For any convex body `B` in `W.euclideanSpan` with `0` in its interior, `W.integerLattice` contains
`D * k` `ℝ`-linearly independent vectors attaining the successive minima of `B`
(`ZLattice.exists_linearIndependent_gauge_eq_successiveMin`). Field-tower extraction
(`TauCeti.exists_linearIndependent_comp_finrank_mul_prod_le_rpow_inv`) selects a `K`-basis
`z 0, …, z (k - 1)` of `W` in `W ∩ 𝓞_K^ι` at real minimum indices `s j ≤ D * j`, bounding the
product of their gauges by the `D`-th root of the product of all `D * k` successive minima
(`Submodule.exists_linearIndependent_integerPoints_prod_gauge_le_successiveMin`).

Combining this extraction with Minkowski's second theorem
(`ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume`) and the slice volume bounds
of `PlaceDecomposition.lean` yields integral `K`-bases of `W` (and, via Hodge duality, of `ker A`
for any `A : Matrix m ι K` without assuming row independence or freeness over `𝓞 K`):

* For `W.supSlice` (volume `≥ 2 ^ (r₁ * k) * π ^ (r₂ * k)`), an integral `K`-basis with
  `∏ j, H_abs(z j) ≤ (2 / π) ^ (k * r₂ / D) * |discr K| ^ (k / (2 * D)) * H₂(W)`.
* For `W.euclideanBallSlice` (volume `ω_k ^ r₁ * ω_{2k} ^ r₂`), an integral `K`-basis with
  `∏ j, H₂(z j) ≤ ((2 ^ k / ω_k) ^ r₁ * (2 ^ k / ω_{2k}) ^ r₂) ^ (1 / D) *`
  `|discr K| ^ (k / (2 * D)) * H₂(W)`, and, via the inscribed cube in the unit ball,
  `∏ j, H₂(z j) ≤ (√k * |discr K| ^ (1 / (2 * D))) ^ k * H₂(W)`.

Over `ℚ`, for an integer matrix `A` with linearly independent rows, the primitive solutions of
`Matrix.exists_linearIndependent_mulVec_eq_zero_prod_norm_le` recover `√det(A Aᵀ) / minorGcd A` in
`absoluteProjectiveTupleHeight` (`r₂ = 0`, `discr ℚ = 1`).

## Main results

* `Submodule.absoluteProjectiveTupleHeight_le_gauge_supSlice`,
  `Submodule.height2_le_gauge_euclideanBallSlice`: gauge-to-height bounds on `W.integerPoints`.
* `Submodule.exists_linearIndependent_integerPoints_prod_gauge_le_successiveMin`,
  `Submodule.exists_linearIndependent_integerPoints_prod_absHeight_le_successiveMin`,
  `Submodule.exists_linearIndependent_integerPoints_prod_height2_le_successiveMin`: field-tower
  extraction of integral `K`-bases from real successive minima.
* `Submodule.exists_linearIndependent_integerPoints_prod_absHeight_le`,
  `Submodule.exists_linearIndependent_integerPoints_prod_height2_le`,
  `Submodule.exists_linearIndependent_integerPoints_prod_height2_le_sqrt_pow`: integral `K`-bases of
  `W` with bounded product of absolute sup or Euclidean heights.
* `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_absHeight_le`,
  `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_height2_le`,
  `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_height2_le_sqrt_pow`,
  `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_absHeight_le_rat`: Bombieri–Vaaler
  kernel-basis height bounds over number fields and over `ℚ`.

## References

* W. M. Schmidt, *On heights of algebraic subspaces and diophantine approximations*, Ann. of Math.
  **85** (1967), 430–472, §3, Theorem 1.
* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32,
  Theorems 1, 2, and 8.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §2.8, §2.9 (Theorem 2.9.4, Corollary 2.9.7, Proposition 2.9.18), and Appendix C, Theorem C.3.8.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §6.1 and §13.
-/

public section

noncomputable section

open Height MeasureTheory Metric Module NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding Set TauCeti TauCeti.NumberField.mixedEmbedding
open scoped BigOperators Matrix

namespace Submodule

/-! ### Gauge bounds for heights of integral points -/

section GaugeBounds

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- At every coordinate `i` and infinite place `w`, the archimedean valuation of an integral point
`z` of `W` is bounded by the Minkowski gauge of `W.supSlice` at its image in `W.euclideanSpan`. -/
theorem apply_le_gauge_supSlice (W : Submodule K (ι → K)) (z : W.integerPoints) (i : ι)
    (w : InfinitePlace K) :
    w ((z : ι → 𝓞 K) i) ≤
      gauge (W.supSlice : Set W.euclideanSpan) (W.integerPointsEquivIntegerLattice z) := by
  simpa only [W.coe_integerPointsEquivIntegerLattice_apply, WithLp.ofLp_toLp,
    ContinuousLinearEquiv.apply_symm_apply, normAtPlace_apply] using
    W.normAtPlace_le_gauge_supSlice (W.integerPointsEquivIntegerLattice z) w i

/-- The absolute projective sup height of a nonzero integral point `z` of `W` is at most the gauge
of `W.supSlice` at its image in `W.euclideanSpan`. -/
theorem absoluteProjectiveTupleHeight_le_gauge_supSlice (W : Submodule K (ι → K))
    {z : W.integerPoints} (hz : (z : ι → 𝓞 K) ≠ 0) :
    absoluteProjectiveTupleHeight (fun i ↦ ((z : ι → 𝓞 K) i : K)) ≤
      gauge (W.supSlice : Set W.euclideanSpan) (W.integerPointsEquivIntegerLattice z) :=
  absoluteProjectiveTupleHeight_le_of_forall_le hz fun i w ↦ W.apply_le_gauge_supSlice z i w

/-- At every infinite place `w`, the Euclidean norm of an integral point `z` of `W` is bounded by
the Minkowski gauge of `W.euclideanBallSlice` at its image in `W.euclideanSpan`. -/
theorem sqrt_sum_norm_embedding_sq_le_gauge_euclideanBallSlice (W : Submodule K (ι → K))
    (z : W.integerPoints) (w : InfinitePlace K) :
    √(∑ i : ι, ‖w.embedding ((z : ι → 𝓞 K) i)‖ ^ 2) ≤
      gauge (W.euclideanBallSlice : Set W.euclideanSpan)
        (W.integerPointsEquivIntegerLattice z) := by
  have h := W.sum_normAtPlace_sq_le_gauge_euclideanBallSlice_sq
    (W.integerPointsEquivIntegerLattice z) w
  simp only [W.coe_integerPointsEquivIntegerLattice_apply, WithLp.ofLp_toLp,
    ContinuousLinearEquiv.apply_symm_apply, normAtPlace_apply, ← w.norm_embedding_eq] at h
  exact (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq (gauge_nonneg _))

/-- The absolute Euclidean height `height2` of any integral point `z` of `W` is at most the gauge of
`W.euclideanBallSlice` at its image in `W.euclideanSpan`. -/
theorem height2_le_gauge_euclideanBallSlice (W : Submodule K (ι → K)) (z : W.integerPoints) :
    height2 (fun i ↦ ((z : ι → 𝓞 K) i : K)) ≤
      gauge (W.euclideanBallSlice : Set W.euclideanSpan) (W.integerPointsEquivIntegerLattice z) :=
  height2_le_of_forall_le fun w ↦ W.sqrt_sum_norm_embedding_sq_le_gauge_euclideanBallSlice z w

end GaugeBounds

/-! ### Extraction of `K`-bases from real successive minima -/

section Extraction

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

open scoped Classical in
/-- **Field-tower extraction from successive minima.** For a `K`-subspace `W` of `ι → K` and a
convex body `B` in `W.euclideanSpan` with `0` in its interior, there exist an integral `K`-basis `z`
of `W` in `W.integerPoints` and indices `s j ≤ [K : ℚ] * j` such that `z j` attains `s j`-th real
successive minimum of `W.integerLattice` with respect to `B` and the product of the gauges of `z j`
is at most the `[K : ℚ]`-th root of the product of all `[K : ℚ] * finrank K W` successive minima. -/
theorem exists_linearIndependent_integerPoints_prod_gauge_le_successiveMin
    (W : Submodule K (ι → K)) {B : ConvexBody W.euclideanSpan}
    (hB : 0 ∈ interior (B : Set W.euclideanSpan)) :
    ∃ (z : Fin (finrank K W) → W.integerPoints)
      (s : Fin (finrank K W) → Fin (finrank ℝ W.euclideanSpan)),
      LinearIndependent K (fun j i ↦ ((z j : ι → 𝓞 K) i : K)) ∧
      span K (Set.range fun j i ↦ ((z j : ι → 𝓞 K) i : K)) = W ∧
      (∀ j, (s j : ℕ) ≤ finrank ℚ K * j) ∧
      (∀ j, gauge (B : Set W.euclideanSpan) (W.integerPointsEquivIntegerLattice (z j)) =
        ZLattice.successiveMin W.integerLattice B (s j)) ∧
      ∏ j, gauge (B : Set W.euclideanSpan) (W.integerPointsEquivIntegerLattice (z j)) ≤
        (∏ m, ZLattice.successiveMin W.integerLattice B m) ^ (finrank ℚ K : ℝ)⁻¹ := by
  obtain ⟨a, ha, haL⟩ := ZLattice.exists_linearIndependent_gauge_eq_successiveMin
    W.integerLattice hB
  set e := finCongr W.finrank_euclideanSpan
  let z₀ : Fin (finrank ℚ K * finrank K W) → W.integerPoints :=
    fun l ↦ W.integerPointsEquivIntegerLattice.symm ⟨a (e.symm l), (haL (e.symm l)).1⟩
  let u : Fin (finrank ℚ K * finrank K W) → ι → K := fun l i ↦ ((z₀ l : ι → 𝓞 K) i : K)
  let f : (ι → K) →ₗ[ℚ] ι → mixedSpace K :=
    LinearMap.piMap fun _ ↦ (mixedEmbedding K).toRatAlgHom.toLinearMap
  let g : W.euclideanSpan →ₗ[ℝ] ι → mixedSpace K :=
    (LinearMap.piMap fun _ ↦ (euclidean.toMixed K).toLinearMap).comp
      ((WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)).toLinearMap.comp
        W.euclideanSpan.subtype)
  have hg : Function.Injective g := fun x y hxy ↦
    W.euclideanSpan.subtype_injective <|
      (WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)).injective <|
        funext fun i ↦ (euclidean.toMixed K).injective (congrFun hxy i)
  have hfu : f ∘ u = g ∘ (a ∘ e.symm) := funext fun l ↦ funext fun i ↦
    W.mixedEmbedding_integerPointsEquivIntegerLattice_symm_apply
      ⟨a (e.symm l), (haL (e.symm l)).1⟩ i
  have hu : LinearIndependent ℝ (f ∘ u) :=
    hfu ▸ (ha.comp _ e.symm.injective).map' g (LinearMap.ker_eq_bot.2 hg)
  set c : Fin (finrank ℚ K * finrank K W) → ℝ :=
    fun l ↦ ZLattice.successiveMin W.integerLattice B (e.symm l)
  have hc : Monotone c := fun _ _ h₁₂ ↦
    ZLattice.monotone_successiveMin W.integerLattice hB (Fin.le_def.2 h₁₂)
  have hbeq (l) :
      gauge (B : Set W.euclideanSpan) (W.integerPointsEquivIntegerLattice (z₀ l)) = c l := by
    simp only [z₀, c, W.integerPointsEquivIntegerLattice.apply_symm_apply, (haL _).2]
  obtain ⟨s₀, hs_li, hs_le, hs_prod⟩ :=
    exists_linearIndependent_comp_finrank_mul_prod_le_rpow_inv (K := K) (u := u) hu
      (fun _ ↦ gauge_nonneg _) (fun l ↦ (hbeq l).le) hc
  have hspan : span K (Set.range (u ∘ s₀)) = W :=
    eq_of_le_of_finrank_eq
      (span_le.2 (Set.range_subset_iff.2 fun j ↦ mem_integerPoints.1 (z₀ (s₀ j)).property))
      ((finrank_span_eq_card hs_li).trans (Fintype.card_fin _))
  refine ⟨fun j ↦ z₀ (s₀ j), fun j ↦ e.symm (s₀ j), hs_li, hspan, hs_le, fun j ↦ hbeq (s₀ j), ?_⟩
  rwa [e.symm.prod_comp (ZLattice.successiveMin W.integerLattice B)] at hs_prod

open scoped Classical in
/-- **Basis extraction for `W.supSlice`.** A `K`-subspace `W` of `ι → K` has an integral `K`-basis
`z` in `W.integerPoints` whose absolute projective sup heights have product at most the `[K : ℚ]`-th
root of the product of the real successive minima of `W.integerLattice` with respect to
`W.supSlice`. -/
theorem exists_linearIndependent_integerPoints_prod_absHeight_le_successiveMin
    (W : Submodule K (ι → K)) :
    ∃ z : Fin (finrank K W) → ι → 𝓞 K,
      LinearIndependent K (fun j i ↦ (z j i : K)) ∧
      span K (Set.range fun j i ↦ (z j i : K)) = W ∧
      (∀ j, z j ∈ W.integerPoints) ∧
      ∏ j, absoluteProjectiveTupleHeight (fun i ↦ (z j i : K)) ≤
        (∏ m, ZLattice.successiveMin W.integerLattice W.supSlice m) ^ (finrank ℚ K : ℝ)⁻¹ := by
  obtain ⟨z, _, hz_li, hz_span, _, _, hz_prod⟩ :=
    W.exists_linearIndependent_integerPoints_prod_gauge_le_successiveMin
      W.zero_mem_interior_supSlice
  refine ⟨fun j ↦ z j, hz_li, hz_span, fun j ↦ (z j).property,
    (Finset.prod_le_prod₀ (fun _ _ ↦ (absoluteProjectiveTupleHeight_pos _).le)
      fun j _ ↦ W.absoluteProjectiveTupleHeight_le_gauge_supSlice ?_).trans hz_prod⟩
  exact fun h0 ↦ hz_li.ne_zero j (RingOfIntegers.coe_tuple_eq_zero_iff.2 h0)

open scoped Classical in
/-- **Basis extraction for `W.euclideanBallSlice`.** A `K`-subspace `W` of `ι → K` has an integral
`K`-basis `z` in `W.integerPoints` whose Euclidean heights `height2` have product at most the
`[K : ℚ]`-th root of the product of the real successive minima of `W.integerLattice` with respect to
`W.euclideanBallSlice`. -/
theorem exists_linearIndependent_integerPoints_prod_height2_le_successiveMin
    (W : Submodule K (ι → K)) :
    ∃ z : Fin (finrank K W) → ι → 𝓞 K,
      LinearIndependent K (fun j i ↦ (z j i : K)) ∧
      span K (Set.range fun j i ↦ (z j i : K)) = W ∧
      (∀ j, z j ∈ W.integerPoints) ∧
      ∏ j, height2 (fun i ↦ (z j i : K)) ≤
        (∏ m, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice m) ^
          (finrank ℚ K : ℝ)⁻¹ := by
  obtain ⟨z, _, hz_li, hz_span, _, _, hz_prod⟩ :=
    W.exists_linearIndependent_integerPoints_prod_gauge_le_successiveMin
      W.zero_mem_interior_euclideanBallSlice
  exact ⟨fun j ↦ z j, hz_li, hz_span, fun j ↦ (z j).property,
    (Finset.prod_le_prod₀ (fun _ _ ↦ height2_nonneg _)
      fun j _ ↦ W.height2_le_gauge_euclideanBallSlice (z j)).trans hz_prod⟩

end Extraction

/-! ### Inscribed-cube lower bound for unit-ball volumes -/

section UnitBallCube

/-- Across all archimedean places of `K`, the unit-ball volume factor is bounded by `√k ^ k`. -/
private theorem unitBall_factor_rpow_le_sqrt_pow (K : Type*) [Field K] [NumberField K] (k : ℕ) :
    (((2 : ℝ) ^ k / volume.real (ball (0 : EuclideanSpace ℝ (Fin k)) 1)) ^ nrRealPlaces K *
      ((2 : ℝ) ^ k / volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * k))) 1)) ^
        nrComplexPlaces K) ^ (finrank ℚ K : ℝ)⁻¹ ≤
      √(k : ℝ) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [measureReal_def, volume_eq_one_of_subsingleton
      (nonempty_ball.2 one_pos : (ball (0 : EuclideanSpace ℝ (Fin 0)) 1).Nonempty)]
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hsqrt_pos : 0 < √(k : ℝ) := Real.sqrt_pos.2 hk_pos
  have hω_pos (m : ℕ) : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hreal :
      (2 : ℝ) ^ k / volume.real (ball (0 : EuclideanSpace ℝ (Fin k)) 1) ≤ √(k : ℝ) ^ k := by
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    have h1 := EuclideanSpace.two_mul_div_sqrt_card_pow_le_volume_real_ball
      (0 : EuclideanSpace ℝ (Fin k)) zero_le_one
    rw [mul_one, Fintype.card_fin, div_pow] at h1
    exact (div_le_iff₀ (hω_pos k)).2
      (((div_le_iff₀ (pow_pos hsqrt_pos k)).1 h1).trans_eq (mul_comm _ _))
  have hcomplex :
      (2 : ℝ) ^ k / volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * k))) 1) ≤
        √(k : ℝ) ^ (2 * k) := by
    have : Nonempty (Fin (2 * k)) := ⟨⟨0, Nat.mul_pos two_pos hk⟩⟩
    have h2 := EuclideanSpace.two_mul_div_sqrt_card_pow_le_volume_real_ball
      (0 : EuclideanSpace ℝ (Fin (2 * k))) zero_le_one
    rw [mul_one, Fintype.card_fin] at h2
    have hlhs : (2 / √((2 * k : ℕ) : ℝ)) ^ (2 * k) = (2 : ℝ) ^ k / √(k : ℝ) ^ (2 * k) := by
      rw [pow_mul, pow_mul (√(k : ℝ)) 2 k, Real.sq_sqrt hk_pos.le, ← div_pow]
      congr 1
      rw [div_pow, Nat.cast_mul, Nat.cast_ofNat, Real.sq_sqrt (by positivity)]
      field_simp [hk_pos.ne']
    rw [hlhs] at h2
    exact (div_le_iff₀ (hω_pos (2 * k))).2
      (((div_le_iff₀ (pow_pos hsqrt_pos (2 * k))).1 h2).trans_eq (mul_comm _ _))
  have hprod :
      ((2 : ℝ) ^ k / volume.real (ball (0 : EuclideanSpace ℝ (Fin k)) 1)) ^ nrRealPlaces K *
        ((2 : ℝ) ^ k / volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * k))) 1)) ^
          nrComplexPlaces K ≤ (√(k : ℝ) ^ k) ^ finrank ℚ K := by
    refine (mul_le_mul (pow_le_pow_left₀ (by positivity) hreal _)
      (pow_le_pow_left₀ (by positivity) hcomplex _) (by positivity) (by positivity)).trans_eq ?_
    rw [← pow_mul, ← pow_mul, ← pow_add, ← card_add_two_mul_card_eq_rank (K := K), ← pow_mul]
    congr 1; ring
  exact (Real.rpow_le_rpow (by positivity) hprod (by positivity)).trans_eq
    (Real.pow_rpow_inv_natCast (by positivity) (Module.finrank_pos (R := ℚ) (M := K)).ne')

end UnitBallCube

/-! ### Subspace basis height bounds -/

section SubspaceBounds

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- Minkowski's second theorem on `W.integerLattice`, combined with `covolume_integerLattice` and
the `[K : ℚ]`-th root, for any symmetric convex body `B` of volume at least `V > 0`. -/
private theorem prod_successiveMin_rpow_inv_le {ι : Type*} [Fintype ι] [LinearOrder ι]
    (W : Submodule K (ι → K))
    {B : ConvexBody W.euclideanSpan} (hB_symm : ∀ x, x ∈ B → -x ∈ B) {c V : ℝ}
    (hV_pos : 0 < V) (hV_le : V ≤ volume.real (B : Set W.euclideanSpan)) (hc : 0 ≤ c)
    (hcV : c * V = (2 : ℝ) ^ (nrRealPlaces K * finrank K W) *
      (2 : ℝ) ^ (nrComplexPlaces K * finrank K W)) :
    (∏ m, ZLattice.successiveMin W.integerLattice B m) ^ (finrank ℚ K : ℝ)⁻¹ ≤
      c ^ (finrank ℚ K : ℝ)⁻¹ *
        |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) * W.subspaceHeight := by
  set k := finrank K W with ← hk_def
  set D := finrank ℚ K with ← hD_def
  set r₁ := nrRealPlaces K
  set r₂ := nrComplexPlaces K with ← hr₂_def
  have hD_pos : 0 < D := Module.finrank_pos
  have hD : D = r₁ + 2 * r₂ := (card_add_two_mul_card_eq_rank (K := K)).symm
  have htwo :
      (2 : ℝ) ^ (D * k) * ((2⁻¹ : ℝ) ^ r₂) ^ k = (2 : ℝ) ^ (r₁ * k) * (2 : ℝ) ^ (r₂ * k) := by
    rw [hD, add_mul, pow_add, ← pow_mul (2⁻¹ : ℝ), two_mul r₂, add_mul, pow_add (2 : ℝ) (r₂ * k),
      mul_assoc, mul_assoc, ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow, mul_one]
  have hprod_min : ∏ m, ZLattice.successiveMin W.integerLattice B m ≤
      c * √|(discr K : ℝ)| ^ k * W.subspaceHeight ^ D := by
    refine le_of_mul_le_mul_right ?_ hV_pos
    refine (mul_le_mul_of_nonneg_left hV_le
      (Finset.prod_nonneg fun _ _ ↦ ZLattice.successiveMin_nonneg _ _ _)).trans
      ((ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume
        W.integerLattice volume (K := B) hB_symm).trans_eq ?_)
    simp only [W.finrank_euclideanSpan, W.covolume_integerLattice, hk_def, hD_def, hr₂_def]
    rw [mul_pow ((2⁻¹ : ℝ) ^ r₂), ← mul_assoc ((2 : ℝ) ^ (D * k)),
      ← mul_assoc ((2 : ℝ) ^ (D * k)), htwo, ← hcV]
    ring
  refine (Real.rpow_le_rpow (Finset.prod_nonneg fun _ _ ↦ ZLattice.successiveMin_nonneg _ _ _)
    hprod_min (by positivity)).trans_eq ?_
  rw [Real.mul_rpow (by positivity) (pow_nonneg (Submodule.subspaceHeight_pos W).le D),
    Real.mul_rpow hc (by positivity),
    Real.pow_rpow_inv_natCast (Submodule.subspaceHeight_pos W).le hD_pos.ne',
    Real.sqrt_eq_rpow, ← Real.rpow_natCast _ k, ← Real.rpow_mul (abs_nonneg _),
    ← Real.rpow_mul (abs_nonneg _)]
  congr 2; congr 1; ring

variable {ι : Type*} [Finite ι] [LinearOrder ι]

open scoped Classical in
/-- **Bombieri–Vaaler subspace basis theorem over a number field, sup height.** A `K`-subspace `W`
of `ι → K` of dimension `k` has a `K`-basis `z 0, …, z (k - 1)` in `W ∩ 𝓞_K^ι` satisfying
`∏ j, H_abs(z j) ≤ (2 / π) ^ (k * r₂ / D) * |discr K| ^ (k / (2 * D)) * H₂(W)`,
where `D = [K : ℚ]` and `r₂ = nrComplexPlaces K`. No freeness of `W ∩ 𝓞_K^ι` over `𝓞 K` is
assumed, and the bound includes `k = 0`. -/
theorem exists_linearIndependent_integerPoints_prod_absHeight_le (W : Submodule K (ι → K)) :
    ∃ z : Fin (finrank K W) → ι → 𝓞 K,
      LinearIndependent K (fun j i ↦ (z j i : K)) ∧
      span K (Set.range fun j i ↦ (z j i : K)) = W ∧
      (∀ j, z j ∈ W.integerPoints) ∧
      ∏ j, absoluteProjectiveTupleHeight (fun i ↦ (z j i : K)) ≤
        (2 / Real.pi) ^ ((finrank K W * nrComplexPlaces K : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) * W.subspaceHeight := by
  cases nonempty_fintype ι
  obtain ⟨z, hz_li, hz_span, hz_mem, hz_min⟩ :=
    W.exists_linearIndependent_integerPoints_prod_absHeight_le_successiveMin
  refine ⟨z, hz_li, hz_span, hz_mem, hz_min.trans ?_⟩
  refine (W.prod_successiveMin_rpow_inv_le (fun _ hx ↦ W.neg_mem_supSlice.2 hx)
    (V := (2 : ℝ) ^ (nrRealPlaces K * finrank K W) * Real.pi ^ (nrComplexPlaces K * finrank K W))
    (c := (2 / Real.pi) ^ (nrComplexPlaces K * finrank K W))
    (by positivity) W.two_pow_mul_pi_pow_le_volume_real_supSlice (by positivity) ?_).trans_eq ?_
  · rw [mul_comm ((2 / Real.pi) ^ _), mul_assoc, ← mul_pow, mul_div_cancel₀ _ Real.pi_ne_zero]
  · rw [← Real.rpow_natCast (2 / Real.pi), ← Real.rpow_mul (by positivity)]
    congr 3; push_cast; ring

open scoped Classical in
/-- **Bombieri–Vaaler subspace basis theorem over a number field, Euclidean height.** A `K`-subspace
`W` of `ι → K` of dimension `k` has a `K`-basis `z 0, …, z (k - 1)` in `W ∩ 𝓞_K^ι` satisfying
`∏ j, H₂(z j) ≤ ((2 ^ k / ω_k) ^ r₁ * (2 ^ k / ω_{2k}) ^ r₂) ^ (1 / D) *`
`|discr K| ^ (k / (2 * D)) * H₂(W)`, where `ω_a` is the volume of the Euclidean unit ball in
`ℝ^a`. -/
theorem exists_linearIndependent_integerPoints_prod_height2_le (W : Submodule K (ι → K)) :
    ∃ z : Fin (finrank K W) → ι → 𝓞 K,
      LinearIndependent K (fun j i ↦ (z j i : K)) ∧
      span K (Set.range fun j i ↦ (z j i : K)) = W ∧
      (∀ j, z j ∈ W.integerPoints) ∧
      ∏ j, height2 (fun i ↦ (z j i : K)) ≤
        (((2 : ℝ) ^ finrank K W /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank K W))) 1)) ^ nrRealPlaces K *
          ((2 : ℝ) ^ finrank K W /
            volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * finrank K W))) 1)) ^
              nrComplexPlaces K) ^ (finrank ℚ K : ℝ)⁻¹ *
          |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) * W.subspaceHeight := by
  cases nonempty_fintype ι
  obtain ⟨z, hz_li, hz_span, hz_mem, hz_min⟩ :=
    W.exists_linearIndependent_integerPoints_prod_height2_le_successiveMin
  have hω_pos (m : ℕ) : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hωk := hω_pos (finrank K W)
  have hω2k := hω_pos (2 * finrank K W)
  refine ⟨z, hz_li, hz_span, hz_mem, hz_min.trans <|
    W.prod_successiveMin_rpow_inv_le (fun _ hx ↦ W.neg_mem_euclideanBallSlice.2 hx)
      (by positivity) W.volume_real_euclideanBallSlice.symm.le (by positivity) ?_⟩
  rw [mul_mul_mul_comm, ← mul_pow, ← mul_pow, div_mul_cancel₀ _ hωk.ne',
    div_mul_cancel₀ _ hω2k.ne', ← pow_mul, ← pow_mul, mul_comm (finrank K W),
    mul_comm (finrank K W)]

/-- **Gamma-free Euclidean subspace basis bound.** Bounding each unit-ball volume from below by its
inscribed hypercube gives an integral `K`-basis `z` of `W` satisfying
`∏ j, H₂(z j) ≤ (√k * |discr K| ^ (1 / (2 * D))) ^ k * H₂(W)`. -/
theorem exists_linearIndependent_integerPoints_prod_height2_le_sqrt_pow
    (W : Submodule K (ι → K)) :
    ∃ z : Fin (finrank K W) → ι → 𝓞 K,
      LinearIndependent K (fun j i ↦ (z j i : K)) ∧
      span K (Set.range fun j i ↦ (z j i : K)) = W ∧
      (∀ j, z j ∈ W.integerPoints) ∧
      ∏ j, height2 (fun i ↦ (z j i : K)) ≤
        (√(finrank K W : ℝ) * |(discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹) ^ finrank K W *
          W.subspaceHeight := by
  obtain ⟨z, hz_li, hz_span, hz_mem, hz_le⟩ :=
    W.exists_linearIndependent_integerPoints_prod_height2_le
  refine ⟨z, hz_li, hz_span, hz_mem, hz_le.trans ?_⟩
  have hdiscr : |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) =
      (|(discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹) ^ finrank K W := by
    rw [← Real.rpow_natCast _ (finrank K W), ← Real.rpow_mul (abs_nonneg _), div_eq_inv_mul]
  rw [hdiscr, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (unitBall_factor_rpow_le_sqrt_pow K (finrank K W)) (by positivity))
    (Submodule.subspaceHeight_pos W).le

end SubspaceBounds

end Submodule

/-! ### Kernel basis height bounds for matrices -/

namespace Matrix

open Submodule

section NumberField

variable {K : Type*} [Field K] [NumberField K] {m ι : Type*} [Fintype ι] [LinearOrder ι]

private theorem exists_ker_basis_of_subspace (A : Matrix m ι K) (f : (ι → K) → ℝ) {B C : ℝ}
    (h : ∃ z : Fin (finrank K (LinearMap.ker A.mulVecLin)) → ι → 𝓞 K,
      LinearIndependent K (fun j i ↦ (z j i : K)) ∧
      span K (Set.range fun j i ↦ (z j i : K)) = LinearMap.ker A.mulVecLin ∧
      (∀ j, z j ∈ (LinearMap.ker A.mulVecLin).integerPoints) ∧
      ∏ j, f (fun i ↦ (z j i : K)) ≤ B)
    (hBC : finrank K (LinearMap.ker A.mulVecLin) = Fintype.card ι - A.rank →
      (LinearMap.ker A.mulVecLin).subspaceHeight = (span K (Set.range A.row)).subspaceHeight →
      B = C) :
    ∃ x : Fin (Fintype.card ι - A.rank) → ι → 𝓞 K,
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      span K (Set.range fun j i ↦ (x j i : K)) = LinearMap.ker A.mulVecLin ∧
      (∀ j, A *ᵥ (fun i ↦ (x j i : K)) = 0) ∧
      ∏ j, f (fun i ↦ (x j i : K)) ≤ C := by
  obtain ⟨z, hz_li, hz_span, hz_mem, hz_le⟩ := h
  have hfin := A.finrank_ker_mulVecLin
  set e := finCongr hfin
  have hrange : (Set.range fun j i ↦ (z (e.symm j) i : K)) = Set.range fun j i ↦ (z j i : K) := by
    ext; simp [e.symm.surjective.exists]
  refine ⟨fun j ↦ z (e.symm j), hz_li.comp _ e.symm.injective, hrange ▸ hz_span, fun j ↦ ?_, ?_⟩
  · simpa [Submodule.mem_integerPoints, LinearMap.mem_ker, mulVecLin_apply] using hz_mem (e.symm j)
  · rw [e.symm.prod_comp fun j ↦ f fun i ↦ (z j i : K),
      ← hBC hfin (subspaceHeight_ker_mulVecLin A)]
    exact hz_le

open scoped Classical in
/-- **Siegel's kernel basis theorem over a number field, sup height** (Bombieri–Vaaler). Let `A` be
an `m × ι` matrix over a number field `K` of degree `D = [K : ℚ]` with `r₂` complex places, and let
`k = #ι - A.rank`. Without assuming row independence or freeness of the integral kernel over `𝓞 K`,
`ker A` has a `K`-basis `x 0, …, x (k - 1)` in `𝓞_K^ι` satisfying
`∏ j, H_abs(x j) ≤ (2 / π) ^ (k * r₂ / D) * |discr K| ^ (k / (2 * D)) * H₂(rowSpace A)`. -/
theorem exists_linearIndependent_mulVec_eq_zero_prod_absHeight_le (A : Matrix m ι K) :
    ∃ x : Fin (Fintype.card ι - A.rank) → ι → 𝓞 K,
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      span K (Set.range fun j i ↦ (x j i : K)) = LinearMap.ker A.mulVecLin ∧
      (∀ j, A *ᵥ (fun i ↦ (x j i : K)) = 0) ∧
      ∏ j, absoluteProjectiveTupleHeight (fun i ↦ (x j i : K)) ≤
        (2 / Real.pi) ^
            (((Fintype.card ι - A.rank : ℕ) * nrComplexPlaces K : ℝ) / finrank ℚ K) *
          |(discr K : ℝ)| ^ (((Fintype.card ι - A.rank : ℕ) : ℝ) / (2 * finrank ℚ K)) *
          (span K (Set.range A.row)).subspaceHeight :=
  exists_ker_basis_of_subspace A absoluteProjectiveTupleHeight
    (LinearMap.ker A.mulVecLin).exists_linearIndependent_integerPoints_prod_absHeight_le
    fun hfin hH ↦ by rw [hfin, hH]

open scoped Classical in
/-- **Siegel's kernel basis theorem over a number field, Euclidean height** (Bombieri–Vaaler). For
any `m × ι` matrix `A` over `K` and `k = #ι - A.rank`, `ker A` has a `K`-basis `x` in `𝓞_K^ι`
satisfying
`∏ j, H₂(x j) ≤ ((2 ^ k / ω_k) ^ r₁ * (2 ^ k / ω_{2k}) ^ r₂) ^ (1 / D) *`
`|discr K| ^ (k / (2 * D)) * H₂(rowSpace A)`. -/
theorem exists_linearIndependent_mulVec_eq_zero_prod_height2_le (A : Matrix m ι K) :
    ∃ x : Fin (Fintype.card ι - A.rank) → ι → 𝓞 K,
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      span K (Set.range fun j i ↦ (x j i : K)) = LinearMap.ker A.mulVecLin ∧
      (∀ j, A *ᵥ (fun i ↦ (x j i : K)) = 0) ∧
      ∏ j, height2 (fun i ↦ (x j i : K)) ≤
        (((2 : ℝ) ^ (Fintype.card ι - A.rank) /
            volume.real
              (ball (0 : EuclideanSpace ℝ (Fin (Fintype.card ι - A.rank))) 1)) ^ nrRealPlaces K *
          ((2 : ℝ) ^ (Fintype.card ι - A.rank) /
            volume.real
              (ball (0 : EuclideanSpace ℝ (Fin (2 * (Fintype.card ι - A.rank)))) 1)) ^
              nrComplexPlaces K) ^ (finrank ℚ K : ℝ)⁻¹ *
          |(discr K : ℝ)| ^ (((Fintype.card ι - A.rank : ℕ) : ℝ) / (2 * finrank ℚ K)) *
          (span K (Set.range A.row)).subspaceHeight :=
  exists_ker_basis_of_subspace A height2
    (LinearMap.ker A.mulVecLin).exists_linearIndependent_integerPoints_prod_height2_le
    fun hfin hH ↦ by rw [hfin, hH]

/-- **Gamma-free Euclidean kernel basis theorem over a number field.** For any `m × ι` matrix `A`
over `K` and `k = #ι - A.rank`, `ker A` has a `K`-basis `x` in `𝓞_K^ι` satisfying
`∏ j, H₂(x j) ≤ (√k * |discr K| ^ (1 / (2 * D))) ^ k * H₂(rowSpace A)`. -/
theorem exists_linearIndependent_mulVec_eq_zero_prod_height2_le_sqrt_pow (A : Matrix m ι K) :
    ∃ x : Fin (Fintype.card ι - A.rank) → ι → 𝓞 K,
      LinearIndependent K (fun j i ↦ (x j i : K)) ∧
      span K (Set.range fun j i ↦ (x j i : K)) = LinearMap.ker A.mulVecLin ∧
      (∀ j, A *ᵥ (fun i ↦ (x j i : K)) = 0) ∧
      ∏ j, height2 (fun i ↦ (x j i : K)) ≤
        (√((Fintype.card ι - A.rank : ℕ) : ℝ) * |(discr K : ℝ)| ^ (2 * finrank ℚ K : ℝ)⁻¹) ^
            (Fintype.card ι - A.rank) *
          (span K (Set.range A.row)).subspaceHeight :=
  exists_ker_basis_of_subspace A height2
    (LinearMap.ker A.mulVecLin).exists_linearIndependent_integerPoints_prod_height2_le_sqrt_pow
    fun hfin hH ↦ by rw [hfin, hH]

end NumberField

section Rational

variable {ι : Type*} [Fintype ι] {p : ℕ}

/-- **Bombieri–Vaaler Theorem 2 over `ℚ` in terms of `absoluteProjectiveTupleHeight`.** For a
`p × ι` integer matrix `A` with linearly independent rows, the primitive integral solutions from
`Matrix.exists_linearIndependent_mulVec_eq_zero_prod_norm_le` form a `ℚ`-basis of the rational
kernel of `A` whose absolute projective heights satisfy
`∏ l, H_abs(x l) ≤ √det(A Aᵀ) / minorGcd A`. -/
theorem exists_linearIndependent_mulVec_eq_zero_prod_absHeight_le_rat {A : Matrix (Fin p) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) :
    ∃ x : Fin (Fintype.card ι - p) → ι → ℤ,
      LinearIndependent ℚ (fun l i ↦ (x l i : ℚ)) ∧
      span ℚ (Set.range fun l i ↦ (x l i : ℚ)) =
        LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin ∧
      (∀ l, A *ᵥ x l = 0) ∧
      (∀ l, Finset.univ.gcd (x l) = 1) ∧
      ∏ l, absoluteProjectiveTupleHeight (fun i ↦ (x l i : ℚ)) ≤
        √((A * Aᵀ).det : ℝ) / (A.minorGcd : ℝ) := by
  obtain ⟨x, hx_li, hx_ker, hx_gcd, hx_le⟩ :=
    exists_linearIndependent_mulVec_eq_zero_prod_norm_le hA
  have hx_rat : LinearIndependent ℚ (fun l i ↦ (x l i : ℚ)) :=
    (Matrix.linearIndependent_map_algebraMap_row_iff (R := ℤ) (S := ℚ) (A := Matrix.of x)).2 hx_li
  have hker_mem (l : Fin (Fintype.card ι - p)) :
      (fun i ↦ (x l i : ℚ)) ∈ LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin := by
    rw [LinearMap.mem_ker, mulVecLin_apply]
    ext j
    simpa [Matrix.mulVec, dotProduct] using congrArg ((↑) : ℤ → ℚ) (congrFun (hx_ker l) j)
  have hfin : finrank ℚ (LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin) = Fintype.card ι - p := by
    simpa only [Fintype.card_fin] using finrank_ker_mulVecLin_of_linearIndependent_rows hA
  have hspan :
      span ℚ (Set.range fun l i ↦ (x l i : ℚ)) =
        LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin :=
    eq_of_le_of_finrank_eq (span_le.2 (Set.range_subset_iff.2 hker_mem))
      ((finrank_span_eq_card hx_rat).trans ((Fintype.card_fin _).trans hfin.symm))
  refine ⟨x, hx_rat, hspan, hx_ker, hx_gcd,
    (Finset.prod_le_prod₀ (fun _ _ ↦ (absoluteProjectiveTupleHeight_pos _).le)
      fun l _ ↦ ?_).trans hx_le⟩
  have : Nonempty ι := Fintype.card_pos_iff.1 (Nat.pos_of_ne_zero fun h0 ↦ by
    have := l.isLt; omega)
  rw [← Function.comp_def ((↑) : ℤ → ℚ) (x l), absoluteProjectiveTupleHeight_eq, finrank_self,
    Nat.cast_one, inv_one, Real.rpow_one, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (hx_gcd l)]
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ |x l i|)
  rw [← hi]
  simpa only [Int.cast_abs, ← Int.norm_eq_abs] using norm_le_pi_norm (x l) i

end Rational

end Matrix

end
