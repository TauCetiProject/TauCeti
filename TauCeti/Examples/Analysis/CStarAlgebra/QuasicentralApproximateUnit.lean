/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnit.Quasicentral
public import TauCeti.Analysis.Normed.Lp.Diagonal.Positive
public import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.Normed.Operator.Compact.HilbertAdjoint
import TauCeti.Analysis.Normed.Operator.Compact.StrongConvergence

/-!
# Coordinate projections, the unilateral shift, and Cesàro quasicentrality in `B(ℓ²)`

On the separable Hilbert space `ℓ²(ℕ, ℂ)`, the compact operators form a closed two-sided ideal
`compactIdeal` of the C⋆-algebra `ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)`. The finite-rank coordinate projections
`coordProj n` onto the first `n` coordinates form a monotone sequential approximate unit for
`compactIdeal`, yet fail to be quasicentral in `B(ℓ²)`: for the isometric unilateral shift
`unilateralShift`, the commutator `coordProj n * unilateralShift - unilateralShift * coordProj n`
is the rank-one operator `x ↦ -x (n - 1) • e_n` of norm `1` for every `n ≥ 1`.

Taking the Cesàro convex combinations
`cesaroProj N = N⁻¹ • ∑ k ∈ Finset.Icc 1 N, coordProj k`
preserves positivity, contractivity, compactness, and the approximate-unit property on
`compactIdeal`, while making the commutator with `unilateralShift` have exact operator norm `1 / N`
for every `N ≥ 1`, hence converge to `0` in norm. Even though the ambient algebra `B(ℓ²)` is
nonseparable, this gives a completely explicit convexified approximate unit of `K(ℓ²)` that is
quasicentral on the Toeplitz generator `unilateralShift`.
-/

public section

noncomputable section

open Filter Topology
open scoped lp ENNReal ComplexOrder

namespace TauCeti.QuasicentralApproximateUnitExample

private theorem two_pos : (0 : ℝ≥0∞) < 2 := by norm_num

private theorem lp_real_smul_eq_complex_smul (r : ℝ) (y : ℓ^2(ℕ, ℂ)) :
    r • y = (r : ℂ) • y := by
  rw [← smul_one_smul ℂ r y, Complex.real_smul, mul_one]

private theorem real_smul_eq_complex_smul (r : ℝ) (T : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)) :
    r • T = (r : ℂ) • T :=
  ContinuousLinearMap.ext fun x => lp_real_smul_eq_complex_smul r (T x)

/-- The closed two-sided ideal `K(ℓ²)` of compact operators in `B(ℓ²)`. -/
def compactIdeal : TwoSidedIdeal (ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)) :=
  TwoSidedIdeal.mk' {T : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ) | IsCompactOperator T}
    isCompactOperator_zero
    (fun hx hy => hx.add hy)
    (fun hx => hx.neg)
    (fun hx => hx.mul_left _)
    (fun hx => hx.mul_right _)

/-- Membership in `compactIdeal` is `IsCompactOperator`. -/
@[simp]
theorem mem_compactIdeal {T : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)} :
    T ∈ compactIdeal ↔ IsCompactOperator T := by
  simp [compactIdeal]

/-- The ideal `compactIdeal` of compact operators is norm-closed in `B(ℓ²)`. -/
instance isClosed_compactIdeal :
    IsClosed (compactIdeal : Set (ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ))) := by
  have hset : (compactIdeal : Set (ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ))) =
      {T : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ) | IsCompactOperator T} :=
    Set.ext fun _ => mem_compactIdeal
  rw [hset]
  exact isClosed_setOfPred_isCompactOperator

/-- The finite-rank orthogonal projection onto the first `n` coordinates of `ℓ²(ℕ, ℂ)`. -/
def coordProj (n : ℕ) : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ) :=
  lp.diagonalTruncation (p := 2) (1 : ℓ^∞(ℕ, ℂ)) (Finset.range n)

/-- Coordinates of `coordProj n x`. -/
@[simp]
theorem coordProj_apply (n : ℕ) (x : ℓ^2(ℕ, ℂ)) (i : ℕ) :
    coordProj n x i = if i < n then x i else 0 := by
  simp [coordProj]

/-- Action of `coordProj n` on a standard basis vector. -/
@[simp]
theorem coordProj_single (n i : ℕ) (a : ℂ) :
    coordProj n (lp.single 2 i a) = if i < n then lp.single 2 i a else 0 := by
  simp [coordProj]

/-- `coordProj 0` is the zero operator. -/
@[simp]
theorem coordProj_zero : coordProj 0 = 0 := by
  simp [coordProj]

/-- Each coordinate projection is positive in the Loewner order. -/
theorem coordProj_nonneg (n : ℕ) : 0 ≤ coordProj n := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, coordProj, lp.isPositive_diagonalTruncation_iff]
  intro i _
  simp

/-- The sequence `coordProj` is monotone in the Loewner order. -/
theorem monotone_coordProj : Monotone coordProj :=
  (lp.diagonalTruncation_mono (d := (1 : ℓ^∞(ℕ, ℂ))) fun _ => by simp).comp Finset.range_mono

/-- Each coordinate projection is bounded above by `1` in the Loewner order. -/
theorem coordProj_le_one (n : ℕ) : coordProj n ≤ 1 := by
  simpa [coordProj, ← ContinuousLinearMap.one_def] using
    lp.diagonalTruncation_le_diagonalCLM (d := (1 : ℓ^∞(ℕ, ℂ))) (fun _ => by simp) (Finset.range n)

/-- Each coordinate projection is a contraction. -/
theorem norm_coordProj_le_one (n : ℕ) : ‖coordProj n‖ ≤ 1 :=
  (CStarAlgebra.norm_le_norm_of_le_of_nonneg (coordProj_le_one n) (coordProj_nonneg n)).trans
    ContinuousLinearMap.norm_id_le

/-- The complementary projection `1 - coordProj n` is also a contraction. -/
theorem norm_one_sub_coordProj_le_one (n : ℕ) : ‖1 - coordProj n‖ ≤ 1 := by
  have h0 : 0 ≤ 1 - coordProj n := sub_nonneg.2 (coordProj_le_one n)
  have h1 : 1 - coordProj n ≤ 1 := sub_le_self 1 (coordProj_nonneg n)
  exact (CStarAlgebra.norm_le_norm_of_le_of_nonneg h1 h0).trans ContinuousLinearMap.norm_id_le

/-- Every coordinate projection `coordProj n` is a compact operator. -/
theorem isCompactOperator_coordProj (n : ℕ) : IsCompactOperator (coordProj n) := by
  have hrank : Module.Finite ℂ (LinearMap.range (coordProj n).toLinearMap) :=
    Module.rank_lt_aleph0_iff.mp
      ((lp.rank_diagonalTruncation_range_le (p := 2) (1 : ℓ^∞(ℕ, ℂ)) n).trans_lt
        Cardinal.natCast_lt_aleph0)
  exact LinearMap.HasFiniteRange.isCompactOperator (Module.Finite.iff_fg.mp hrank)

/-- `coordProj n` bundled as an element of `compactIdeal`. -/
def coordProjIdeal (n : ℕ) : compactIdeal :=
  ⟨coordProj n, mem_compactIdeal.2 (isCompactOperator_coordProj n)⟩

/-- Pointwise convergence `coordProj n x → x` on `ℓ²(ℕ, ℂ)`. -/
theorem tendsto_coordProj_apply (x : ℓ^2(ℕ, ℂ)) :
    Tendsto (fun n => coordProj n x) atTop (𝓝 x) := by
  simpa [coordProj, Function.comp_def] using
    (lp.tendsto_diagonalTruncation_apply ENNReal.ofNat_ne_top (1 : ℓ^∞(ℕ, ℂ)) x).comp
      tendsto_finset_range

/-- Left approximate-unit property of `coordProj` on compact operators. -/
theorem tendsto_coordProj_mul_of_isCompactOperator {K : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)}
    (hK : IsCompactOperator K) :
    Tendsto (fun n => coordProj n * K) atTop (𝓝 K) := by
  have hstrong (x : ℓ^2(ℕ, ℂ)) : Tendsto (fun n => (1 - coordProj n) x) atTop (𝓝 0) := by
    simpa [sub_apply] using (tendsto_const_nhds (x := x)).sub (tendsto_coordProj_apply x)
  have hrem : Tendsto (fun n => (1 - coordProj n) * K) atTop (𝓝 0) :=
    ContinuousLinearMap.tendsto_comp_zero_of_isCompactOperator norm_one_sub_coordProj_le_one
      hstrong K hK
  have hsub : (fun n => K - (1 - coordProj n) * K) = fun n => coordProj n * K := by
    ext n x i
    simp [sub_mul]
  simpa [hsub] using (tendsto_const_nhds (x := K)).sub hrem

/-- Right approximate-unit property of `coordProj` on compact operators. -/
theorem tendsto_mul_coordProj_of_isCompactOperator {K : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)}
    (hK : IsCompactOperator K) :
    Tendsto (fun n => K * coordProj n) atTop (𝓝 K) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hleft : Tendsto (fun n => ‖coordProj n * star K - star K‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_coordProj_mul_of_isCompactOperator hK.star)
  refine hleft.congr fun n => ?_
  rw [← norm_star (K * coordProj n - K), star_sub, star_mul,
    (coordProj_nonneg n).isSelfAdjoint.star_eq]

/-- The finite-rank coordinate projections form an increasing approximate unit for `compactIdeal`.
-/
theorem isIncreasingApproximateUnit_coordProjIdeal :
    (Filter.map coordProjIdeal atTop).IsIncreasingApproximateUnit where
  tendsto_mul_left b := by
    rw [tendsto_map'_iff]
    exact Topology.IsInducing.subtypeVal.tendsto_nhds_iff.2
      (by simpa [Function.comp_def, coordProjIdeal] using
        tendsto_mul_coordProj_of_isCompactOperator (mem_compactIdeal.1 b.2))
  tendsto_mul_right b := by
    rw [tendsto_map'_iff]
    exact Topology.IsInducing.subtypeVal.tendsto_nhds_iff.2
      (by simpa [Function.comp_def, coordProjIdeal] using
        tendsto_coordProj_mul_of_isCompactOperator (mem_compactIdeal.1 b.2))
  eventually_nonneg := eventually_map.2 (Eventually.of_forall coordProj_nonneg)
  eventually_norm := eventually_map.2 (Eventually.of_forall norm_coordProj_le_one)

private theorem injOn_pred_ge_one : ({j : ℕ | 1 ≤ j} : Set ℕ).InjOn (fun j => j - 1) := by
  intro a (ha : 1 ≤ a) b (hb : 1 ≤ b) (h : a - 1 = b - 1)
  omega

/-- The isometric unilateral shift on `ℓ²(ℕ, ℂ)`, sending `(x₀, x₁, …)` to `(0, x₀, x₁, …)`. -/
def unilateralShift : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun x =>
        ⟨{j : ℕ | 1 ≤ j}.indicator (x ∘ fun j => j - 1),
          (lp.memℓp x).indicator_comp injOn_pred_ge_one⟩
      map_add' := fun x y => by
        ext j
        simp only [lp.coeFn_add, Pi.add_apply, Function.comp_apply, Set.indicator_apply]
        split_ifs <;> simp
      map_smul' := fun c x => by
        ext j
        simp only [RingHom.id_apply, lp.coeFn_smul, Pi.smul_apply, Function.comp_apply,
          Set.indicator_apply]
        split_ifs <;> simp }
    1 fun x => by
      simpa only [one_mul] using
        lp.norm_le_of_forall_eq_indicator_comp (p := 2) (by simp) injOn_pred_ge_one fun _ => rfl

/-- Coordinates of `unilateralShift x`. -/
@[simp]
theorem unilateralShift_apply (x : ℓ^2(ℕ, ℂ)) (j : ℕ) :
    unilateralShift x j = if 1 ≤ j then x (j - 1) else 0 := by
  simp [unilateralShift, LinearMap.mkContinuous_apply, Set.indicator_apply]

/-- For every `n ≥ 1`, `[coordProj n, unilateralShift]` is the rank-one operator
`x ↦ lp.single 2 n (-x (n - 1))`. -/
theorem commutator_coordProj_unilateralShift_apply {n : ℕ} (hn : 1 ≤ n) (x : ℓ^2(ℕ, ℂ)) :
    (coordProj n * unilateralShift - unilateralShift * coordProj n) x =
      lp.single 2 n (-x (n - 1)) := by
  ext j
  change coordProj n (unilateralShift x) j - unilateralShift (coordProj n x) j =
    (lp.single 2 n (-x (n - 1)) : ℕ → ℂ) j
  rw [lp.coeFn_single, coordProj_apply, unilateralShift_apply, unilateralShift_apply,
    coordProj_apply]
  rcases lt_trichotomy j n with hlt | rfl | hgt
  · by_cases hj : 1 ≤ j
    · have hpred : j - 1 < n := by omega
      simp [hlt, hj, hpred, Pi.single_eq_of_ne hlt.ne]
    · simp [hlt, hj, Pi.single_eq_of_ne hlt.ne]
  · have hpred : j - 1 < j := by omega
    simp [hn, hpred]
  · have hj : 1 ≤ j := by omega
    have hnotlt : ¬ j < n := by omega
    have hpred : ¬ j - 1 < n := by omega
    simp [hnotlt, hj, hpred, Pi.single_eq_of_ne hgt.ne']

/-- For every `n ≥ 1`, the commutator `[coordProj n, unilateralShift]` has exact operator norm `1`.
-/
theorem norm_commutator_coordProj_unilateralShift {n : ℕ} (hn : 1 ≤ n) :
    ‖coordProj n * unilateralShift - unilateralShift * coordProj n‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [commutator_coordProj_unilateralShift_apply hn, lp.norm_single two_pos,
      norm_neg, one_mul]
    exact lp.norm_apply_le_norm (by simp) x (n - 1)
  · let u : ℓ^2(ℕ, ℂ) := lp.single 2 (n - 1) 1
    have hu_norm : ‖u‖ = 1 := by simp [u]
    have hval : ‖(coordProj n * unilateralShift - unilateralShift * coordProj n) u‖ = 1 := by
      rw [commutator_coordProj_unilateralShift_apply hn, lp.norm_single two_pos]
      simp [u]
    have hle := (coordProj n * unilateralShift - unilateralShift * coordProj n).le_opNorm u
    rw [hu_norm, mul_one, hval] at hle
    exact hle

/-- The approximate unit `coordProj` is not quasicentral in `B(ℓ²)`. -/
theorem not_tendsto_commutator_coordProj_unilateralShift :
    ¬ Tendsto (fun n => coordProj n * unilateralShift - unilateralShift * coordProj n)
        atTop (𝓝 0) := by
  intro h
  have hnorm : Tendsto (fun n => ‖coordProj n * unilateralShift - unilateralShift * coordProj n‖)
      atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.1 h
  have hev : ∀ᶠ n in atTop, (1 : ℝ) =
      ‖coordProj n * unilateralShift - unilateralShift * coordProj n‖ :=
    eventually_ge_atTop 1 |>.mono fun n hn => (norm_commutator_coordProj_unilateralShift hn).symm
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hnorm
  norm_num at h10

/-- The Cesàro convex combinations `N⁻¹ • ∑ k ∈ Finset.Icc 1 N, coordProj k`. -/
def cesaroProj (N : ℕ) : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ) :=
  (N : ℝ)⁻¹ • ∑ k ∈ Finset.Icc 1 N, coordProj k

/-- For `N ≥ 1`, `cesaroProj N` lies in the convex hull of the coordinate projections. -/
theorem cesaroProj_mem_convexHull {N : ℕ} (hN : 1 ≤ N) :
    cesaroProj N ∈ convexHull ℝ (Set.range coordProj) := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hmem := (convex_convexHull ℝ (Set.range coordProj)).sum_mem
    (t := Finset.Icc 1 N) (w := fun _ => (N : ℝ)⁻¹) (z := coordProj)
    (fun _ _ => by positivity)
    (by simp [Nat.card_Icc, hN_pos.ne'])
    (fun k _ => subset_convexHull ℝ (Set.range coordProj) ⟨k, rfl⟩)
  simpa [cesaroProj, Finset.smul_sum] using hmem

/-- Each Cesàro average `cesaroProj N` is positive. -/
theorem cesaroProj_nonneg (N : ℕ) : 0 ≤ cesaroProj N := by
  rw [cesaroProj, real_smul_eq_complex_smul]
  exact smul_nonneg (Complex.zero_le_real.2 (by positivity))
    (Finset.sum_nonneg fun k _ => coordProj_nonneg k)

/-- Each Cesàro average `cesaroProj N` is bounded above by `1`. -/
theorem cesaroProj_le_one (N : ℕ) : cesaroProj N ≤ 1 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [cesaroProj]
  · have hN_pos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
    let c : ℝ := (N : ℝ)⁻¹
    have hc : 0 ≤ c := by positivity
    have hsum_le : ∑ k ∈ Finset.Icc 1 N, coordProj k ≤
        ∑ _k ∈ Finset.Icc 1 N, (1 : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)) :=
      Finset.sum_le_sum fun k _ => coordProj_le_one k
    calc
      cesaroProj N = (c : ℂ) • ∑ k ∈ Finset.Icc 1 N, coordProj k := by
        change c • ∑ k ∈ Finset.Icc 1 N, coordProj k = _
        rw [real_smul_eq_complex_smul]
      _ ≤ (c : ℂ) • ∑ _k ∈ Finset.Icc 1 N, (1 : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)) :=
        smul_le_smul_of_nonneg_left hsum_le (Complex.zero_le_real.2 hc)
      _ = 1 := by
        rw [← real_smul_eq_complex_smul]
        simp [c, Nat.card_Icc, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hN_pos.ne']

/-- Each Cesàro average `cesaroProj N` is a contraction. -/
theorem norm_cesaroProj_le_one (N : ℕ) : ‖cesaroProj N‖ ≤ 1 :=
  (CStarAlgebra.norm_le_norm_of_le_of_nonneg (cesaroProj_le_one N) (cesaroProj_nonneg N)).trans
    ContinuousLinearMap.norm_id_le

/-- Each `1 - cesaroProj N` is a contraction. -/
theorem norm_one_sub_cesaroProj_le_one (N : ℕ) : ‖1 - cesaroProj N‖ ≤ 1 := by
  have h0 : 0 ≤ 1 - cesaroProj N := sub_nonneg.2 (cesaroProj_le_one N)
  have h1 : 1 - cesaroProj N ≤ 1 := sub_le_self 1 (cesaroProj_nonneg N)
  exact (CStarAlgebra.norm_le_norm_of_le_of_nonneg h1 h0).trans ContinuousLinearMap.norm_id_le

/-- Each Cesàro average `cesaroProj N` is a compact operator. -/
theorem isCompactOperator_cesaroProj (N : ℕ) : IsCompactOperator (cesaroProj N) := by
  have hsum : IsCompactOperator ⇑(∑ k ∈ Finset.Icc 1 N, coordProj k) := by
    induction (Finset.Icc 1 N) using Finset.induction_on with
    | empty => simpa using isCompactOperator_zero
    | insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact (isCompactOperator_coordProj k).add ih
  let c : ℝ := (N : ℝ)⁻¹
  have hcoe : ⇑(cesaroProj N) = (c : ℂ) • ⇑(∑ k ∈ Finset.Icc 1 N, coordProj k) := by
    change ⇑(c • ∑ k ∈ Finset.Icc 1 N, coordProj k) = _
    rw [real_smul_eq_complex_smul]
    rfl
  rw [hcoe]
  exact hsum.smul _

/-- `cesaroProj N` bundled as an element of `compactIdeal`. -/
def cesaroProjIdeal (N : ℕ) : compactIdeal :=
  ⟨cesaroProj N, mem_compactIdeal.2 (isCompactOperator_cesaroProj N)⟩

/-- Pointwise convergence `cesaroProj N x → x` on `ℓ²(ℕ, ℂ)`. -/
theorem tendsto_cesaroProj_apply (x : ℓ^2(ℕ, ℂ)) :
    Tendsto (fun N => cesaroProj N x) atTop (𝓝 x) := by
  refine lp.tendsto_apply_of_tendsto_apply_single (E := fun _ : ℕ => ℂ) (p := 2)
    ENNReal.ofNat_ne_top (g := ContinuousLinearMap.id ℂ ℓ^2(ℕ, ℂ)) (C := 1)
    (Eventually.of_forall norm_cesaroProj_le_one) (fun i a => ?_) x
  have hev : ∀ᶠ N : ℕ in atTop,
      (1 - (i : ℝ) / (N : ℝ)) • lp.single (E := fun _ : ℕ => ℂ) 2 i a =
        cesaroProj N (lp.single 2 i a) := by
    filter_upwards [eventually_ge_atTop (i + 1)] with N hN
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
    rw [cesaroProj, smul_apply, sum_apply]
    have hsplit : ∑ k ∈ Finset.Icc 1 N, coordProj k (lp.single 2 i a) =
        ∑ _k ∈ Finset.Icc (i + 1) N, lp.single 2 i a := by
      simp_rw [coordProj_single, ← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hsplit, Finset.sum_const, Nat.card_Icc, show N + 1 - (i + 1) = N - i by omega,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_sub (by omega : i ≤ N)]
    congr 1
    field_simp
  have hcoef : Tendsto (fun N : ℕ => 1 - (i : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    have hdiv : Tendsto (fun N : ℕ => (i : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hdiv
  have hlim : Tendsto (fun N : ℕ =>
      (1 - (i : ℝ) / (N : ℝ)) • lp.single (E := fun _ : ℕ => ℂ) 2 i a) atTop
      (𝓝 (lp.single (E := fun _ : ℕ => ℂ) 2 i a)) := by
    simpa using hcoef.smul (tendsto_const_nhds (x := lp.single (E := fun _ : ℕ => ℂ) 2 i a))
  simpa using hlim.congr' hev

/-- Left approximate-unit property of `cesaroProj` on compact operators. -/
theorem tendsto_cesaroProj_mul_of_isCompactOperator {K : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)}
    (hK : IsCompactOperator K) :
    Tendsto (fun N => cesaroProj N * K) atTop (𝓝 K) := by
  have hstrong (x : ℓ^2(ℕ, ℂ)) : Tendsto (fun N => (1 - cesaroProj N) x) atTop (𝓝 0) := by
    simpa [sub_apply] using (tendsto_const_nhds (x := x)).sub (tendsto_cesaroProj_apply x)
  have hrem : Tendsto (fun N => (1 - cesaroProj N) * K) atTop (𝓝 0) :=
    ContinuousLinearMap.tendsto_comp_zero_of_isCompactOperator norm_one_sub_cesaroProj_le_one
      hstrong K hK
  have hsub : (fun N => K - (1 - cesaroProj N) * K) = fun N => cesaroProj N * K := by
    ext N x i
    simp [sub_mul]
  simpa [hsub] using (tendsto_const_nhds (x := K)).sub hrem

/-- Right approximate-unit property of `cesaroProj` on compact operators. -/
theorem tendsto_mul_cesaroProj_of_isCompactOperator {K : ℓ^2(ℕ, ℂ) →L[ℂ] ℓ^2(ℕ, ℂ)}
    (hK : IsCompactOperator K) :
    Tendsto (fun N => K * cesaroProj N) atTop (𝓝 K) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hleft : Tendsto (fun N => ‖cesaroProj N * star K - star K‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_cesaroProj_mul_of_isCompactOperator hK.star)
  refine hleft.congr fun N => ?_
  rw [← norm_star (K * cesaroProj N - K), star_sub, star_mul,
    (cesaroProj_nonneg N).isSelfAdjoint.star_eq]

/-- The Cesàro averages form an increasing approximate unit for `compactIdeal`. -/
theorem isIncreasingApproximateUnit_cesaroProjIdeal :
    (Filter.map cesaroProjIdeal atTop).IsIncreasingApproximateUnit where
  tendsto_mul_left b := by
    rw [tendsto_map'_iff]
    exact Topology.IsInducing.subtypeVal.tendsto_nhds_iff.2
      (by simpa [Function.comp_def, cesaroProjIdeal] using
        tendsto_mul_cesaroProj_of_isCompactOperator (mem_compactIdeal.1 b.2))
  tendsto_mul_right b := by
    rw [tendsto_map'_iff]
    exact Topology.IsInducing.subtypeVal.tendsto_nhds_iff.2
      (by simpa [Function.comp_def, cesaroProjIdeal] using
        tendsto_cesaroProj_mul_of_isCompactOperator (mem_compactIdeal.1 b.2))
  eventually_nonneg := eventually_map.2 (Eventually.of_forall cesaroProj_nonneg)
  eventually_norm := eventually_map.2 (Eventually.of_forall norm_cesaroProj_le_one)

/-- Operator-level expansion of `[cesaroProj N, unilateralShift]` as the Cesàro average of the
rank-one commutators `[coordProj k, unilateralShift]`. -/
theorem commutator_cesaroProj_unilateralShift (N : ℕ) :
    cesaroProj N * unilateralShift - unilateralShift * cesaroProj N =
      (N : ℝ)⁻¹ • ∑ k ∈ Finset.Icc 1 N,
        (coordProj k * unilateralShift - unilateralShift * coordProj k) := by
  refine ContinuousLinearMap.ext fun x => ?_
  let c : ℝ := (N : ℝ)⁻¹
  have h1 : (cesaroProj N * unilateralShift) x =
      c • ∑ k ∈ Finset.Icc 1 N, coordProj k (unilateralShift x) := by
    simp [cesaroProj, c, sum_apply]
  have h2 : (unilateralShift * cesaroProj N) x =
      c • ∑ k ∈ Finset.Icc 1 N, unilateralShift (coordProj k x) := by
    have hcx : cesaroProj N x = (c : ℂ) • ∑ k ∈ Finset.Icc 1 N, coordProj k x := by
      change (c • ∑ k ∈ Finset.Icc 1 N, coordProj k) x = _
      rw [smul_apply, lp_real_smul_eq_complex_smul, sum_apply]
    calc
      (unilateralShift * cesaroProj N) x = unilateralShift (cesaroProj N x) := rfl
      _ = unilateralShift ((c : ℂ) • ∑ k ∈ Finset.Icc 1 N, coordProj k x) := by rw [hcx]
      _ = (c : ℂ) • unilateralShift (∑ k ∈ Finset.Icc 1 N, coordProj k x) := map_smul _ _ _
      _ = c • ∑ k ∈ Finset.Icc 1 N, unilateralShift (coordProj k x) := by
        rw [← lp_real_smul_eq_complex_smul, map_sum]
  calc
    (cesaroProj N * unilateralShift - unilateralShift * cesaroProj N) x
        = (cesaroProj N * unilateralShift) x - (unilateralShift * cesaroProj N) x := rfl
    _ = c • ∑ k ∈ Finset.Icc 1 N, coordProj k (unilateralShift x) -
          c • ∑ k ∈ Finset.Icc 1 N, unilateralShift (coordProj k x) := by rw [h1, h2]
    _ = c • ∑ k ∈ Finset.Icc 1 N,
          (coordProj k * unilateralShift - unilateralShift * coordProj k) x := by
        rw [← smul_sub, ← Finset.sum_sub_distrib]
        rfl
    _ = ((N : ℝ)⁻¹ • ∑ k ∈ Finset.Icc 1 N,
          (coordProj k * unilateralShift - unilateralShift * coordProj k)) x := by
        simp [c, sum_apply]

/-- Explicit formula for `[cesaroProj N, unilateralShift] x`. -/
theorem commutator_cesaroProj_unilateralShift_apply (N : ℕ) (x : ℓ^2(ℕ, ℂ)) :
    (cesaroProj N * unilateralShift - unilateralShift * cesaroProj N) x =
      (N : ℝ)⁻¹ • ∑ k ∈ Finset.Icc 1 N, lp.single 2 k (-x (k - 1)) := by
  rw [commutator_cesaroProj_unilateralShift, smul_apply, sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  exact commutator_coordProj_unilateralShift_apply (Finset.mem_Icc.1 hk).1 x

/-- For every `N ≥ 1`, the commutator `[cesaroProj N, unilateralShift]` has exact operator norm
`1 / N`. -/
theorem norm_commutator_cesaroProj_unilateralShift {N : ℕ} (hN : 1 ≤ N) :
    ‖cesaroProj N * unilateralShift - unilateralShift * cesaroProj N‖ = 1 / (N : ℝ) := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    rw [commutator_cesaroProj_unilateralShift_apply, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 hN_pos.le), one_div]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hN_pos.le)
    have hsq : ‖∑ k ∈ Finset.Icc 1 N, lp.single 2 k (-x (k - 1))‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      have horth := lp.norm_sum_single_sq (E := fun _ : ℕ => ℂ)
        (fun k => -x (k - 1)) (Finset.Icc 1 N)
      rw [horth]
      have hreindex : ∑ k ∈ Finset.Icc 1 N, ‖-x (k - 1)‖ ^ 2 =
          ∑ j ∈ Finset.range N, ‖x j‖ ^ 2 := by
        refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
        · intro k hk
          simp only [Finset.mem_Icc] at hk
          simp only [Finset.mem_range]
          omega
        · intro a ha b hb h
          simp only [Finset.mem_Icc] at ha hb
          omega
        · intro j hj
          simp only [Finset.mem_range] at hj
          exact ⟨j + 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩
        · intro k _
          simp
      rw [hreindex]
      simpa [Real.rpow_two] using lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) x (Finset.range N)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
  · let u : ℓ^2(ℕ, ℂ) := lp.single 2 0 1
    have hu_norm : ‖u‖ = 1 := by simp [u]
    have hval : ‖(cesaroProj N * unilateralShift - unilateralShift * cesaroProj N) u‖ =
        1 / (N : ℝ) := by
      rw [commutator_cesaroProj_unilateralShift_apply]
      have hsum : ∑ k ∈ Finset.Icc 1 N, lp.single 2 k (-u (k - 1)) = lp.single 2 1 (-1) := by
        rw [Finset.sum_eq_single 1]
        · simp [u]
        · intro k hk hk1
          have hk0 : k - 1 ≠ 0 := by
            have := (Finset.mem_Icc.1 hk).1
            omega
          simp [u, lp.single_apply, hk0]
        · intro h1
          exact absurd (Finset.mem_Icc.2 ⟨le_rfl, hN⟩) h1
      rw [hsum, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hN_pos.le), lp.norm_single two_pos]
      simp [one_div]
    have hle := (cesaroProj N * unilateralShift - unilateralShift * cesaroProj N).le_opNorm u
    rw [hu_norm, mul_one, hval] at hle
    exact hle

/-- The Cesàro commutators `[cesaroProj N, unilateralShift]` converge to `0` in operator norm. -/
theorem tendsto_commutator_cesaroProj_unilateralShift_zero :
    Tendsto (fun N => cesaroProj N * unilateralShift - unilateralShift * cesaroProj N)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hev : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) =
      ‖cesaroProj N * unilateralShift - unilateralShift * cesaroProj N‖ :=
    eventually_ge_atTop 1 |>.mono fun N hN => (norm_commutator_cesaroProj_unilateralShift hN).symm
  have hlim : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  exact hlim.congr' hev

end TauCeti.QuasicentralApproximateUnitExample
