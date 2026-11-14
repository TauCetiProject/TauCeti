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

import TauCeti.InformationTheory.Coding.GeneratorParityCheck
import TauCeti.LinearAlgebra.LinearIndependent.Extraction.Estimates
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.NumberTheory.GeometryOfNumbers.MinkowskiSecond

/-!
# Kernel bases and subspace bases of bounded height over number fields

Let `K` be a number field of degree `D = [K : ℚ]` with `r₁` real places and `r₂` complex places,
and let `W` be a `K`-subspace of `ι → K` of dimension `k`. Inside the `D * k`-dimensional Euclidean
Minkowski span `W.euclideanSpan`, the saturated integral intersection `W ∩ 𝓞_K^ι` embeds as the
full `ℤ`-lattice `W.integerLattice`, of covolume `((2⁻¹) ^ r₂ * √|discr K|) ^ k * H₂(W) ^ D` by
Schmidt's identity (`Submodule.covolume_integerLattice`).

For any convex body `B` in `W.euclideanSpan` with `0` in its interior, `W.integerLattice` contains
`D * k` `ℝ`-linearly independent vectors simultaneously attaining the successive minima of `B`
(`ZLattice.exists_linearIndependent_gauge_eq_successiveMin`). Because a `K`-span of `j` vectors has
`ℚ`-dimension at most `D * j`, field-tower extraction
(`TauCeti.exists_linearIndependent_comp_finrank_mul_prod_le_rpow_inv`) selects a `K`-basis
`z 0, …, z (k - 1)` of `W` in `W ∩ 𝓞_K^ι` with `z j` chosen at real minimum index `s j ≤ D * j`, so
that blockwise monotonicity bounds the product of their gauges by the `D`-th root of the product of
all `D * k` real successive minima
(`Submodule.exists_linearIndependent_integerPoints_prod_gauge_le_successiveMin`).

Combining this extraction with Minkowski's second theorem
(`ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume`) and the placewise central
slice volume estimates of `PlaceDecomposition.lean` yields integral `K`-bases of `W` (and, by
Hodge duality of subspace heights, of `ker A` for any matrix `A : Matrix m ι K` without assuming
row independence or freeness of the integral kernel over `𝓞 K`) bounded in both height
normalizations:

* For `W.supSlice`, Vaaler's cube and polydisc slicing gives volume at least
  `2 ^ (r₁ * k) * π ^ (r₂ * k)`, yielding an integral `K`-basis with
  `∏ j, H_abs(z j) ≤ (2 / π) ^ (k * r₂ / D) * |discr K| ^ (k / (2 * D)) * H₂(W)`.
* For `W.euclideanBallSlice`, the orthogonal decomposition across places gives exact volume
  `ω_k ^ r₁ * ω_{2k} ^ r₂` (where `ω_a` is the volume of the Euclidean unit ball in `ℝ^a`),
  yielding an integral `K`-basis with
  `∏ j, H₂(z j) ≤ ((2 ^ k / ω_k) ^ r₁ * (2 ^ k / ω_{2k}) ^ r₂) ^ (1 / D) *`
  `|discr K| ^ (k / (2 * D)) * H₂(W)`,
  and, via the inscribed cube of side `2 / √a` in the unit ball of `ℝ^a`, the Gamma-free bound
  `∏ j, H₂(z j) ≤ (√k * |discr K| ^ (1 / (2 * D))) ^ k * H₂(W)`.

Over `ℚ`, for an integer matrix `A` with linearly independent rows, the primitive integer solutions
of `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_norm_le` already have coprime coordinates,
so their sup norms coincide with their absolute projective heights and recover the sharper bound
`√det(A Aᵀ) / minorGcd A` without the complex-place `(2 / π)` factor (`r₂ = 0`, `discr ℚ = 1`).

## Main results

* `Submodule.absoluteProjectiveTupleHeight_le_gauge_supSlice`,
  `Submodule.height2_le_gauge_euclideanBallSlice`: gauge-to-height bounds for integral points of `W`
  against `W.supSlice` and `W.euclideanBallSlice`.
* `Submodule.exists_linearIndependent_integerPoints_prod_gauge_le_successiveMin`: field-tower
  extraction of a `K`-basis of `W` in `W.integerPoints` from the real successive minima of any
  convex body `B` in `W.euclideanSpan` containing `0` in its interior, together with its
  specializations `Submodule.exists_linearIndependent_integerPoints_prod_absHeight_le_successiveMin`
  and `Submodule.exists_linearIndependent_integerPoints_prod_height2_le_successiveMin`.
* `Submodule.exists_linearIndependent_integerPoints_prod_absHeight_le`,
  `Submodule.exists_linearIndependent_integerPoints_prod_height2_le`,
  `Submodule.exists_linearIndependent_integerPoints_prod_height2_le_sqrt_pow`: existence of a
  `K`-basis of `W` in `W ∩ 𝓞_K^ι` with bounded product of absolute sup or Euclidean heights.
* `Matrix.subspaceHeight_ker_mulVecLin`: Hodge-duality identity equating the subspace height of
  `ker A` with that of the row space of `A`, with no rank assumption on `A`.
* `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_absHeight_le`,
  `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_height2_le`,
  `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_height2_le_sqrt_pow`: Bombieri–Vaaler
  kernel-basis height bounds for arbitrary matrices over number fields, with no row-independence or
  freeness assumption, and `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_absHeight_le_rat`
  for full-row-rank integer matrices over `ℚ`.

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
open scoped BigOperators Matrix Pointwise

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
  have hfu : f ∘ u = g ∘ (a ∘ e.symm) := by
    ext1 l; ext1 i
    exact W.mixedEmbedding_integerPointsEquivIntegerLattice_symm_apply
      ⟨a (e.symm l), (haL (e.symm l)).1⟩ i
  have hu : LinearIndependent ℝ (f ∘ u) := by
    rw [hfu]
    exact (ha.comp _ e.symm.injective).map' g (LinearMap.ker_eq_bot.2 hg)
  set c : Fin (finrank ℚ K * finrank K W) → ℝ :=
    fun l ↦ ZLattice.successiveMin W.integerLattice B (e.symm l)
  have hc : Monotone c := fun l₁ l₂ h₁₂ ↦
    ZLattice.monotone_successiveMin W.integerLattice hB (Fin.le_def.2 h₁₂)
  have hbeq (l : Fin (finrank ℚ K * finrank K W)) :
      gauge (B : Set W.euclideanSpan) (W.integerPointsEquivIntegerLattice (z₀ l)) = c l := by
    change gauge (B : Set W.euclideanSpan)
      (W.integerPointsEquivIntegerLattice
        (W.integerPointsEquivIntegerLattice.symm ⟨a (e.symm l), (haL (e.symm l)).1⟩)) = _
    rw [W.integerPointsEquivIntegerLattice.apply_symm_apply]
    exact (haL (e.symm l)).2
  obtain ⟨s₀, hs_li, hs_le, hs_prod⟩ :=
    exists_linearIndependent_comp_finrank_mul_prod_le_rpow_inv (K := K) (u := u) hu
      (fun l ↦ gauge_nonneg _) (fun l ↦ (hbeq l).le) hc
  have hspan : span K (Set.range (u ∘ s₀)) = W :=
    eq_of_le_of_finrank_eq
      (span_le.2 (Set.range_subset_iff.2 fun j ↦ mem_integerPoints.1 (z₀ (s₀ j)).2))
      ((finrank_span_eq_card hs_li).trans (Fintype.card_fin _))
  have hc_prod : ∏ l, c l = ∏ m, ZLattice.successiveMin W.integerLattice B m :=
    e.symm.prod_comp (ZLattice.successiveMin W.integerLattice B)
  refine ⟨fun j ↦ z₀ (s₀ j), fun j ↦ e.symm (s₀ j), hs_li, hspan,
    hs_le, fun j ↦ hbeq (s₀ j), ?_⟩
  rwa [hc_prod] at hs_prod

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
  refine ⟨fun j ↦ z j, hz_li, hz_span, fun j ↦ (z j).2, ?_⟩
  refine (Finset.prod_le_prod₀ (fun _ _ ↦ (absoluteProjectiveTupleHeight_pos _).le)
    fun j _ ↦ W.absoluteProjectiveTupleHeight_le_gauge_supSlice ?_).trans hz_prod
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
  refine ⟨fun j ↦ z j, hz_li, hz_span, fun j ↦ (z j).2, ?_⟩
  exact (Finset.prod_le_prod₀ (fun _ _ ↦ height2_nonneg _)
    fun j _ ↦ W.height2_le_gauge_euclideanBallSlice (z j)).trans hz_prod

end Extraction

/-! ### Inscribed-cube lower bound for unit-ball volumes -/

section UnitBallCube

/-- An `m`-dimensional hypercube `[-1/√m, 1/√m]^m` (`0 < m`) lies in the closed Euclidean unit ball
of `ℝ^m`, giving the Gamma-free lower bound `(2 / √m) ^ m ≤ ω_m`. -/
private theorem two_div_sqrt_pow_le_volume_real_unitBall {m : ℕ} (hm : 0 < m) :
    (2 / √(m : ℝ)) ^ m ≤ volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hsqrt_pos : 0 < √(m : ℝ) := Real.sqrt_pos.2 hm_pos
  set r : ℝ := (√(m : ℝ))⁻¹
  let C : Set (Fin m → ℝ) := univ.pi fun _ : Fin m ↦ Icc (-r) r
  have hsub : C ⊆ (@WithLp.toLp 2 (Fin m → ℝ)) ⁻¹' closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
    intro x hx
    rw [mem_preimage, mem_closedBall_zero_iff]
    have hsq : ‖WithLp.toLp 2 x‖ ^ 2 ≤ 1 := by
      rw [PiLp.norm_sq_eq_of_L2]
      calc ∑ i : Fin m, ‖x i‖ ^ 2
          ≤ ∑ _ : Fin m, r ^ 2 := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            have hxi : |x i| ≤ r := abs_le.2 (hx i (mem_univ i))
            simpa [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hxi 2
        _ = (m : ℝ) * ((√(m : ℝ))⁻¹ ^ 2) := by simp [r]
        _ = 1 := by
          rw [inv_pow, Real.sq_sqrt hm_pos.le, mul_inv_cancel₀ hm_pos.ne']
    exact (abs_le_of_sq_le_sq' (by simpa using hsq) zero_le_one).2
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hnonneg : 0 ≤ 2 / √(m : ℝ) := div_nonneg zero_le_two hsqrt_pos.le
  have hC_vol : volume C = ENNReal.ofReal ((2 / √(m : ℝ)) ^ m) := by
    have hr2 : r - -r = 2 / √(m : ℝ) := by simp [r]; ring
    rw [volume_pi_pi]
    simp_rw [Real.volume_Icc, hr2]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hnonneg]
  have hball_eq :
      volume ((@WithLp.toLp 2 (Fin m → ℝ)) ⁻¹' closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) =
        volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := by
    rw [(PiLp.volume_preserving_toLp (Fin m)).measure_preimage
      measurableSet_closedBall.nullMeasurableSet, Measure.addHaar_closedBall_eq_addHaar_ball]
  have hle := (measure_mono hsub).trans_eq hball_eq
  rw [hC_vol] at hle
  have hreal := ENNReal.toReal_mono measure_ball_lt_top.ne hle
  rwa [ENNReal.toReal_ofReal (pow_nonneg hnonneg m), ← measureReal_def] at hreal

/-- Across all archimedean places of `K`, the unit-ball volume factor
`((2 ^ k / ω_k) ^ r₁ * (2 ^ k / ω_{2k}) ^ r₂) ^ (1 / D)` is bounded by `√k ^ k`, including at
`k = 0`. -/
private theorem unitBall_factor_rpow_le_sqrt_pow (K : Type*) [Field K] [NumberField K] (k : ℕ) :
    (((2 : ℝ) ^ k / volume.real (ball (0 : EuclideanSpace ℝ (Fin k)) 1)) ^ nrRealPlaces K *
      ((2 : ℝ) ^ k / volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * k))) 1)) ^
        nrComplexPlaces K) ^ (finrank ℚ K : ℝ)⁻¹ ≤
      √(k : ℝ) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hvol0 : volume.real (ball (0 : EuclideanSpace ℝ (Fin 0)) 1) = 1 := by
      simp [measureReal_def,
        volume_eq_one_of_subsingleton (nonempty_ball.2 one_pos :
          (ball (0 : EuclideanSpace ℝ (Fin 0)) 1).Nonempty)]
    simp [hvol0]
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hsqrt_pos : 0 < √(k : ℝ) := Real.sqrt_pos.2 hk_pos
  have hωk_pos : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin k)) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hω2k_pos : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * k))) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hreal :
      (2 : ℝ) ^ k / volume.real (ball (0 : EuclideanSpace ℝ (Fin k)) 1) ≤ √(k : ℝ) ^ k := by
    have h1 := two_div_sqrt_pow_le_volume_real_unitBall hk
    rw [div_pow] at h1
    exact (div_le_iff₀ hωk_pos).2
      (((div_le_iff₀ (pow_pos hsqrt_pos k)).1 h1).trans_eq (mul_comm _ _))
  have hcomplex :
      (2 : ℝ) ^ k / volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * k))) 1) ≤
        √(k : ℝ) ^ (2 * k) := by
    have h2 := two_div_sqrt_pow_le_volume_real_unitBall (Nat.mul_pos two_pos hk)
    have hlhs : (2 / √((2 * k : ℕ) : ℝ)) ^ (2 * k) = (2 : ℝ) ^ k / √(k : ℝ) ^ (2 * k) := by
      rw [pow_mul, pow_mul (√(k : ℝ)) 2 k, Real.sq_sqrt hk_pos.le, ← div_pow]
      congr 1
      rw [div_pow, Nat.cast_mul, Nat.cast_ofNat,
        Real.sq_sqrt (mul_nonneg zero_le_two hk_pos.le)]
      field_simp [hk_pos.ne']
    rw [hlhs] at h2
    exact (div_le_iff₀ hω2k_pos).2
      (((div_le_iff₀ (pow_pos hsqrt_pos (2 * k))).1 h2).trans_eq (mul_comm _ _))
  have hprod :
      ((2 : ℝ) ^ k / volume.real (ball (0 : EuclideanSpace ℝ (Fin k)) 1)) ^ nrRealPlaces K *
        ((2 : ℝ) ^ k / volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * k))) 1)) ^
          nrComplexPlaces K ≤
        (√(k : ℝ) ^ k) ^ finrank ℚ K := by
    calc _ ≤ (√(k : ℝ) ^ k) ^ nrRealPlaces K * (√(k : ℝ) ^ (2 * k)) ^ nrComplexPlaces K :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hreal _)
            (pow_le_pow_left₀ (by positivity) hcomplex _) (by positivity) (by positivity)
      _ = √(k : ℝ) ^ (k * (nrRealPlaces K + 2 * nrComplexPlaces K)) := by
          rw [← pow_mul, ← pow_mul, ← pow_add]
          congr 1
          ring
      _ = (√(k : ℝ) ^ k) ^ finrank ℚ K := by
          rw [card_add_two_mul_card_eq_rank, pow_mul]
  calc _ ≤ ((√(k : ℝ) ^ k) ^ finrank ℚ K) ^ (finrank ℚ K : ℝ)⁻¹ :=
        Real.rpow_le_rpow (by positivity) hprod (by positivity)
    _ = √(k : ℝ) ^ k :=
        Real.pow_rpow_inv_natCast (by positivity) (Module.finrank_pos (R := ℚ) (M := K)).ne'

end UnitBallCube

/-! ### Subspace basis height bounds -/

section SubspaceBounds

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι] [LinearOrder ι]

/-- Shared `2 ^ (D * k) * (2⁻¹) ^ (r₂ * k)` cancellation across `D = r₁ + 2 * r₂`. -/
private theorem two_pow_rank_mul_two_inv_pow (K : Type*) [Field K] [NumberField K] (k : ℕ) :
    (2 : ℝ) ^ (finrank ℚ K * k) * ((2⁻¹ : ℝ) ^ nrComplexPlaces K) ^ k =
      (2 : ℝ) ^ (nrRealPlaces K * k) * (2 : ℝ) ^ (nrComplexPlaces K * k) := by
  rw [← card_add_two_mul_card_eq_rank (K := K), add_mul, pow_add, ← pow_mul (2⁻¹ : ℝ),
    show 2 * nrComplexPlaces K * k = nrComplexPlaces K * k + nrComplexPlaces K * k by ring,
    pow_add (2 : ℝ) (nrComplexPlaces K * k), mul_assoc, mul_assoc, ← mul_pow,
    mul_inv_cancel₀ two_ne_zero, one_pow, mul_one]

/-- `D`-th root simplification for `((√|discr K|) ^ k) ^ D⁻¹ = |discr K| ^ (k / (2 * D))`. -/
private theorem sqrt_abs_discr_pow_rpow_inv (K : Type*) [Field K] [NumberField K] (k : ℕ) :
    (√|(discr K : ℝ)| ^ k) ^ (finrank ℚ K : ℝ)⁻¹ =
      |(discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ k, ← Real.rpow_mul (abs_nonneg _),
    ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  ring

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
  set k := finrank K W
  set D := finrank ℚ K
  set r₁ := nrRealPlaces K
  set r₂ := nrComplexPlaces K
  have hD_pos : 0 < D := Module.finrank_pos
  have hmink :
      (∏ m, ZLattice.successiveMin W.integerLattice W.supSlice m) *
          volume.real (W.supSlice : Set W.euclideanSpan) ≤
        (2 : ℝ) ^ (D * k) * (((2⁻¹ : ℝ) ^ r₂ * √|(discr K : ℝ)|) ^ k * W.subspaceHeight ^ D) :=
    (ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume W.integerLattice volume
      (K := W.supSlice) fun _ hx ↦ W.neg_mem_supSlice.2 hx).trans_eq
      (by rw [W.finrank_euclideanSpan, W.covolume_integerLattice])
  have hvol := W.two_pow_mul_pi_pow_le_volume_real_supSlice
  have hV_pos : 0 < (2 : ℝ) ^ (r₁ * k) * Real.pi ^ (r₂ * k) := by positivity
  have hprod_min :
      ∏ m, ZLattice.successiveMin W.integerLattice W.supSlice m ≤
        (2 / Real.pi) ^ (r₂ * k) * √|(discr K : ℝ)| ^ k * W.subspaceHeight ^ D := by
    refine le_of_mul_le_mul_right ?_ hV_pos
    calc (∏ m, ZLattice.successiveMin W.integerLattice W.supSlice m) *
          ((2 : ℝ) ^ (r₁ * k) * Real.pi ^ (r₂ * k))
        ≤ (∏ m, ZLattice.successiveMin W.integerLattice W.supSlice m) *
            volume.real (W.supSlice : Set W.euclideanSpan) :=
          mul_le_mul_of_nonneg_left hvol
            (Finset.prod_nonneg fun _ _ ↦ ZLattice.successiveMin_nonneg _ _ _)
      _ ≤ (2 : ℝ) ^ (D * k) *
            (((2⁻¹ : ℝ) ^ r₂ * √|(discr K : ℝ)|) ^ k * W.subspaceHeight ^ D) := hmink
      _ = ((2 / Real.pi) ^ (r₂ * k) * √|(discr K : ℝ)| ^ k * W.subspaceHeight ^ D) *
            ((2 : ℝ) ^ (r₁ * k) * Real.pi ^ (r₂ * k)) := by
          have htwo := two_pow_rank_mul_two_inv_pow K k
          have hpi : (2 / Real.pi) ^ (r₂ * k) * Real.pi ^ (r₂ * k) = (2 : ℝ) ^ (r₂ * k) := by
            rw [← mul_pow, div_mul_cancel₀ _ Real.pi_ne_zero]
          rw [mul_pow ((2⁻¹ : ℝ) ^ r₂), ← mul_assoc ((2 : ℝ) ^ (D * k)),
            ← mul_assoc ((2 : ℝ) ^ (D * k)), htwo]
          calc (2 : ℝ) ^ (r₁ * k) * (2 : ℝ) ^ (r₂ * k) * √|(discr K : ℝ)| ^ k *
                W.subspaceHeight ^ D
              = (2 : ℝ) ^ (r₁ * k) * ((2 / Real.pi) ^ (r₂ * k) * Real.pi ^ (r₂ * k)) *
                  √|(discr K : ℝ)| ^ k * W.subspaceHeight ^ D := by rw [hpi]
            _ = _ := by ring
  calc (∏ m, ZLattice.successiveMin W.integerLattice W.supSlice m) ^ (D : ℝ)⁻¹
      ≤ ((2 / Real.pi) ^ (r₂ * k) * √|(discr K : ℝ)| ^ k * W.subspaceHeight ^ D) ^ (D : ℝ)⁻¹ :=
        Real.rpow_le_rpow (Finset.prod_nonneg fun _ _ ↦ ZLattice.successiveMin_nonneg _ _ _)
          hprod_min (by positivity)
    _ = (2 / Real.pi) ^ ((k * r₂ : ℝ) / D) *
          |(discr K : ℝ)| ^ ((k : ℝ) / (2 * D)) * W.subspaceHeight := by
        rw [Real.mul_rpow (by positivity) (pow_nonneg (Submodule.subspaceHeight_pos W).le D),
          Real.mul_rpow (by positivity) (by positivity),
          sqrt_abs_discr_pow_rpow_inv K k,
          Real.pow_rpow_inv_natCast (Submodule.subspaceHeight_pos W).le hD_pos.ne',
          ← Real.rpow_natCast (2 / Real.pi), ← Real.rpow_mul (by positivity)]
        congr 3
        push_cast
        ring

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
  refine ⟨z, hz_li, hz_span, hz_mem, hz_min.trans ?_⟩
  set k := finrank K W
  set D := finrank ℚ K
  set r₁ := nrRealPlaces K
  set r₂ := nrComplexPlaces K
  set ωk := volume.real (ball (0 : EuclideanSpace ℝ (Fin k)) 1)
  set ω2k := volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * k))) 1)
  have hD_pos : 0 < D := Module.finrank_pos
  have hωk_pos : 0 < ωk :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hω2k_pos : 0 < ω2k :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hV_pos : 0 < ωk ^ r₁ * ω2k ^ r₂ := by positivity
  have hmink :
      (∏ m, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice m) *
          (ωk ^ r₁ * ω2k ^ r₂) ≤
        (2 : ℝ) ^ (D * k) * (((2⁻¹ : ℝ) ^ r₂ * √|(discr K : ℝ)|) ^ k * W.subspaceHeight ^ D) := by
    have h := ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume W.integerLattice
      volume (K := W.euclideanBallSlice) fun _ hx ↦ W.neg_mem_euclideanBallSlice.2 hx
    rw [W.volume_real_euclideanBallSlice] at h
    exact h.trans_eq (by rw [W.finrank_euclideanSpan, W.covolume_integerLattice])
  have hprod_min :
      ∏ m, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice m ≤
        ((2 : ℝ) ^ k / ωk) ^ r₁ * ((2 : ℝ) ^ k / ω2k) ^ r₂ *
          √|(discr K : ℝ)| ^ k * W.subspaceHeight ^ D := by
    refine le_of_mul_le_mul_right ?_ hV_pos
    calc (∏ m, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice m) *
          (ωk ^ r₁ * ω2k ^ r₂)
        ≤ (2 : ℝ) ^ (D * k) *
            (((2⁻¹ : ℝ) ^ r₂ * √|(discr K : ℝ)|) ^ k * W.subspaceHeight ^ D) := hmink
      _ = (((2 : ℝ) ^ k / ωk) ^ r₁ * ((2 : ℝ) ^ k / ω2k) ^ r₂ *
            √|(discr K : ℝ)| ^ k * W.subspaceHeight ^ D) * (ωk ^ r₁ * ω2k ^ r₂) := by
          have htwo := two_pow_rank_mul_two_inv_pow K k
          have hr₁ : ((2 : ℝ) ^ k / ωk) ^ r₁ * ωk ^ r₁ = (2 : ℝ) ^ (r₁ * k) := by
            rw [← mul_pow, div_mul_cancel₀ _ hωk_pos.ne', ← pow_mul, mul_comm k r₁]
          have hr₂ : ((2 : ℝ) ^ k / ω2k) ^ r₂ * ω2k ^ r₂ = (2 : ℝ) ^ (r₂ * k) := by
            rw [← mul_pow, div_mul_cancel₀ _ hω2k_pos.ne', ← pow_mul, mul_comm k r₂]
          rw [mul_pow ((2⁻¹ : ℝ) ^ r₂), ← mul_assoc ((2 : ℝ) ^ (D * k)),
            ← mul_assoc ((2 : ℝ) ^ (D * k)), htwo, ← hr₁, ← hr₂]
          ring
  calc (∏ m, ZLattice.successiveMin W.integerLattice W.euclideanBallSlice m) ^ (D : ℝ)⁻¹
      ≤ ((((2 : ℝ) ^ k / ωk) ^ r₁ * ((2 : ℝ) ^ k / ω2k) ^ r₂) *
          √|(discr K : ℝ)| ^ k * W.subspaceHeight ^ D) ^ (D : ℝ)⁻¹ := by
        refine Real.rpow_le_rpow (Finset.prod_nonneg fun _ _ ↦ ZLattice.successiveMin_nonneg _ _ _)
          ?_ (by positivity)
        simpa only [mul_assoc] using hprod_min
    _ = (((2 : ℝ) ^ k / ωk) ^ r₁ * ((2 : ℝ) ^ k / ω2k) ^ r₂) ^ (D : ℝ)⁻¹ *
          |(discr K : ℝ)| ^ ((k : ℝ) / (2 * D)) * W.subspaceHeight := by
        rw [Real.mul_rpow (by positivity) (pow_nonneg (Submodule.subspaceHeight_pos W).le D),
          Real.mul_rpow (by positivity) (by positivity),
          sqrt_abs_discr_pow_rpow_inv K k,
          Real.pow_rpow_inv_natCast (Submodule.subspaceHeight_pos W).le hD_pos.ne']

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
  have hdiscr :
      |(discr K : ℝ)| ^ ((finrank K W : ℝ) / (2 * finrank ℚ K)) =
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

variable {K : Type*} [Field K] [NumberField K] {m ι : Type*} [Finite m] [Fintype ι]

omit [Finite m] in
/-- Rank-nullity for `A.mulVecLin`: `finrank K (ker A) = #ι - A.rank`. -/
private theorem finrank_ker_mulVecLin_eq (A : Matrix m ι K) :
    finrank K (LinearMap.ker A.mulVecLin) = Fintype.card ι - A.rank := by
  have h := A.mulVecLin.finrank_range_add_finrank_ker
  rw [← Matrix.rank, Module.finrank_fintype_fun_eq_card] at h
  omega

/-- Hodge duality identifies the height of `ker A` with the height of the row space of `A`, without
any rank assumption on `A`. -/
theorem subspaceHeight_ker_mulVecLin [LinearOrder ι] (A : Matrix m ι K) :
    (LinearMap.ker A.mulVecLin).subspaceHeight = (span K (Set.range A.row)).subspaceHeight := by
  cases nonempty_fintype m
  rw [← checkedBy_def, checkedBy_eq_euclideanDual_generatedBy, subspaceHeight_euclideanDual,
    generatedBy_eq_span_rows]

variable [LinearOrder ι]

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
          (span K (Set.range A.row)).subspaceHeight := by
  set W := LinearMap.ker A.mulVecLin
  obtain ⟨z, hz_li, hz_span, hz_mem, hz_le⟩ :=
    W.exists_linearIndependent_integerPoints_prod_absHeight_le
  have hfin : finrank K W = Fintype.card ι - A.rank := finrank_ker_mulVecLin_eq A
  set e := finCongr hfin
  have hrange : (Set.range fun j i ↦ (z (e.symm j) i : K)) = Set.range fun j i ↦ (z j i : K) := by
    ext v; simp [e.symm.surjective.exists]
  refine ⟨fun j ↦ z (e.symm j), hz_li.comp _ e.symm.injective, hrange ▸ hz_span, fun j ↦ ?_, ?_⟩
  · simpa [W, Submodule.mem_integerPoints, LinearMap.mem_ker, mulVecLin_apply] using
      hz_mem (e.symm j)
  · rw [e.symm.prod_comp fun j ↦ absoluteProjectiveTupleHeight fun i ↦ (z j i : K),
      ← hfin, ← subspaceHeight_ker_mulVecLin A]
    exact hz_le

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
          (span K (Set.range A.row)).subspaceHeight := by
  set W := LinearMap.ker A.mulVecLin
  obtain ⟨z, hz_li, hz_span, hz_mem, hz_le⟩ :=
    W.exists_linearIndependent_integerPoints_prod_height2_le
  have hfin : finrank K W = Fintype.card ι - A.rank := finrank_ker_mulVecLin_eq A
  set e := finCongr hfin
  have hrange : (Set.range fun j i ↦ (z (e.symm j) i : K)) = Set.range fun j i ↦ (z j i : K) := by
    ext v; simp [e.symm.surjective.exists]
  refine ⟨fun j ↦ z (e.symm j), hz_li.comp _ e.symm.injective, hrange ▸ hz_span, fun j ↦ ?_, ?_⟩
  · simpa [W, Submodule.mem_integerPoints, LinearMap.mem_ker, mulVecLin_apply] using
      hz_mem (e.symm j)
  · rw [e.symm.prod_comp fun j ↦ height2 fun i ↦ (z j i : K),
      ← hfin, ← subspaceHeight_ker_mulVecLin A]
    exact hz_le

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
          (span K (Set.range A.row)).subspaceHeight := by
  set W := LinearMap.ker A.mulVecLin
  obtain ⟨z, hz_li, hz_span, hz_mem, hz_le⟩ :=
    W.exists_linearIndependent_integerPoints_prod_height2_le_sqrt_pow
  have hfin : finrank K W = Fintype.card ι - A.rank := finrank_ker_mulVecLin_eq A
  set e := finCongr hfin
  have hrange : (Set.range fun j i ↦ (z (e.symm j) i : K)) = Set.range fun j i ↦ (z j i : K) := by
    ext v; simp [e.symm.surjective.exists]
  refine ⟨fun j ↦ z (e.symm j), hz_li.comp _ e.symm.injective, hrange ▸ hz_span, fun j ↦ ?_, ?_⟩
  · simpa [W, Submodule.mem_integerPoints, LinearMap.mem_ker, mulVecLin_apply] using
      hz_mem (e.symm j)
  · rw [e.symm.prod_comp fun j ↦ height2 fun i ↦ (z j i : K),
      ← hfin, ← subspaceHeight_ker_mulVecLin A]
    exact hz_le

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
  refine ⟨x, hx_rat, hspan, hx_ker, hx_gcd, ?_⟩
  refine (Finset.prod_le_prod₀ (fun _ _ ↦ (absoluteProjectiveTupleHeight_pos _).le)
    fun l _ ↦ ?_).trans hx_le
  have : Nonempty ι := Fintype.card_pos_iff.1 (Nat.pos_of_ne_zero fun h0 ↦ by
    have := l.isLt; omega)
  have hcomp : (fun i ↦ (x l i : ℚ)) = ((↑) : ℤ → ℚ) ∘ x l := rfl
  rw [hcomp, absoluteProjectiveTupleHeight_eq, finrank_self, Nat.cast_one, inv_one, Real.rpow_one,
    Rat.mulHeight_eq_max_abs_of_gcd_eq_one (hx_gcd l)]
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ |x l i|)
  rw [← hi]
  simpa only [Int.cast_abs, ← Int.norm_eq_abs] using norm_le_pi_norm (x l) i

end Rational

end Matrix

end
