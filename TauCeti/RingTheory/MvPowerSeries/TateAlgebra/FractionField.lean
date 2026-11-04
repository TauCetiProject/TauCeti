/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.AbsoluteValue.FractionRing
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs

import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Gauss-normed fraction field of a Tate algebra

`GaussFractionField σ K c` is Mathlib's fraction field of the native Tate algebra at
positive polyradius `c`, equipped with the extended Gauss norm through `WithAbs`. Its norm is
multiplicative and ultrametric, and both the Tate algebra and coefficient field embed isometrically.
For an empty variable type the coefficient embedding is an algebra equivalence.

This is the normed fraction field, not its completion: when `σ` is nonempty and `K` is
nontrivially normed, `GaussFractionField σ K c` is incomplete
(`TauCeti.MvPowerSeries.not_completeSpace_gaussFractionField`). Neither completeness of the
coefficient field nor finiteness of the variable type is needed for the construction.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.3.1, for the Gauss-normed
  fraction field used in weak stability.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries Filter
open scoped Topology

section NormedField

variable (σ K : Type*) [NormedField K] [IsUltrametricDist K]
    (c : σ → ℝ) [∀ i, Fact (0 < c i)]

local notation "Tate" => IsRestricted.subring (R := K) c

/-- The absolute value on the fraction field extending the native multiplicative Gauss norm. -/
noncomputable def gaussFractionNorm : AbsoluteValue (FractionRing Tate) ℝ :=
  fractionRingAbsoluteValue (R := Tate) (FractionRing Tate)
    (IsAbsoluteValue.toAbsoluteValue (norm : Tate → ℝ))

/-- The extended Gauss norm restricts to the original Gauss norm. -/
@[simp]
theorem gaussFractionNorm_algebraMap (f : Tate) :
    gaussFractionNorm σ K c (algebraMap Tate (FractionRing Tate) f) = ‖f‖ := by
  simp [gaussFractionNorm]

/-- The extended Gauss norm is nonarchimedean. -/
theorem isNonarchimedean_gaussFractionNorm : IsNonarchimedean (gaussFractionNorm σ K c) := by
  unfold gaussFractionNorm
  exact isNonarchimedean_fractionRingAbsoluteValue _ _
    (fun f g ↦ IsUltrametricDist.norm_add_le_max f g)

/-- The fraction field of a Tate algebra with the extended Gauss norm, without completion. -/
abbrev GaussFractionField := WithAbs (gaussFractionNorm σ K c)

instance : IsFractionRing Tate (GaussFractionField σ K c) :=
  IsFractionRing.of_algEquiv (WithAbs.algEquiv Tate (gaussFractionNorm σ K c)).symm

/-- The norm on the Tate algebra is unchanged by its embedding in the fraction field. -/
@[simp]
theorem norm_algebraMap_gaussFractionField (f : Tate) :
    ‖algebraMap Tate (GaussFractionField σ K c) f‖ = ‖f‖ := by
  rw [WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq, gaussFractionNorm_algebraMap]

/-- The Tate algebra embeds isometrically into its Gauss-normed fraction field. -/
theorem isometry_algebraMap_gaussFractionField :
    Isometry (algebraMap Tate (GaussFractionField σ K c)) :=
  (AddMonoidHomClass.isometry_iff_norm _).mpr (norm_algebraMap_gaussFractionField σ K c)

instance : IsUltrametricDist (GaussFractionField σ K c) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simpa only [WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_add] using
      isNonarchimedean_gaussFractionNorm σ K c x.ofAbs y.ofAbs

noncomputable instance : NormedAlgebra K (GaussFractionField σ K c) where
  norm_smul_le r x := by
    rw [Algebra.smul_def, norm_mul,
      IsScalarTower.algebraMap_apply K Tate (GaussFractionField σ K c),
      norm_algebraMap_gaussFractionField, norm_algebraMap_isRestrictedSubring]

section Empty

variable [IsEmpty σ]

/-- With no variables, every fraction is the image of a coefficient. -/
theorem algebraMap_gaussFractionField_surjective :
    Function.Surjective (algebraMap K (GaussFractionField σ K c)) := by
  intro x
  obtain ⟨f, g, hg, rfl⟩ := IsFractionRing.div_surjective Tate x
  obtain ⟨a, ha⟩ := C_surjective (f : _root_.MvPowerSeries σ K)
  obtain ⟨b, hb⟩ := C_surjective (g : _root_.MvPowerSeries σ K)
  have hf : f = algebraMap K Tate a := Subtype.ext ha.symm
  have hg : g = algebraMap K Tate b := Subtype.ext hb.symm
  refine ⟨a / b, ?_⟩
  simp only [hf, hg, ← IsScalarTower.algebraMap_apply, map_div₀]

/-- With no variables, the Gauss-normed fraction field is the coefficient field. -/
noncomputable def gaussFractionFieldIsEmptyAlgEquiv : GaussFractionField σ K c ≃ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K (GaussFractionField σ K c))
    ⟨(algebraMap K (GaussFractionField σ K c)).injective,
      algebraMap_gaussFractionField_surjective σ K c⟩).symm

/-- The inverse zero-variable comparison is the coefficient embedding. -/
@[simp]
theorem gaussFractionFieldIsEmptyAlgEquiv_symm_apply (a : K) :
    (gaussFractionFieldIsEmptyAlgEquiv σ K c).symm a =
      algebraMap K (GaussFractionField σ K c) a :=
  AlgEquiv.ofBijective_apply _
    ⟨(algebraMap K (GaussFractionField σ K c)).injective,
      algebraMap_gaussFractionField_surjective σ K c⟩ a

/-- The zero-variable comparison preserves the extended Gauss norm. -/
@[simp]
theorem norm_gaussFractionFieldIsEmptyAlgEquiv (x : GaussFractionField σ K c) :
    ‖gaussFractionFieldIsEmptyAlgEquiv σ K c x‖ = ‖x‖ := by
  simpa only [← gaussFractionFieldIsEmptyAlgEquiv_symm_apply, AlgEquiv.symm_apply_apply] using
    (norm_algebraMap' (GaussFractionField σ K c)
      (gaussFractionFieldIsEmptyAlgEquiv σ K c x)).symm

end Empty

end NormedField

section Incomplete

variable (σ K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
  [Nonempty σ] (c : σ → ℝ) [∀ i, Fact (0 < c i)]

local notation "Tate" => IsRestricted.subring (R := K) c

/-- Over a nontrivially normed ultrametric field `K` in at least one variable, the Gauss-normed
fraction field `GaussFractionField σ K c` is not complete: the Laurent series
`∑_{k ≥ 1} a ^ (k ^ 2) / Xᵢ ^ k` (`0 < ‖a‖ < min 1 (c i)`) is Cauchy for the extended Gauss norm
but represents no fraction of restricted power series. -/
theorem not_completeSpace_gaussFractionField :
    ¬CompleteSpace (GaussFractionField σ K c) := by
  classical
  intro hcomp
  let F := GaussFractionField σ K c
  let i₀ : σ := Classical.arbitrary σ
  have hc₀ : 0 < c i₀ := Fact.out
  obtain ⟨a, ha_pos, ha_lt⟩ := NormedField.exists_norm_lt K (lt_min one_pos hc₀)
  have ha1 : ‖a‖ < 1 := ha_lt.trans_le (min_le_left _ _)
  have hac : ‖a‖ < c i₀ := ha_lt.trans_le (min_le_right _ _)
  have hrat0 : 0 ≤ ‖a‖ / c i₀ := div_nonneg ha_pos.le hc₀.le
  have hrat1 : ‖a‖ / c i₀ < 1 := (div_lt_one hc₀).mpr hac
  let X₀ : Tate := ⟨X i₀, isRestricted_monomial c (Finsupp.single i₀ 1) (1 : K)⟩
  have hX₀_norm : ‖X₀‖ = c i₀ := norm_X i₀
  have hX₀_F_norm : ‖algebraMap Tate F X₀‖ = c i₀ := by
    rw [norm_algebraMap_gaussFractionField, hX₀_norm]
  have hX₀_F_ne : algebraMap Tate F X₀ ≠ 0 := by
    rw [← norm_pos_iff, hX₀_F_norm]
    exact hc₀
  let t (k : ℕ) : F :=
    algebraMap K F (a ^ ((k + 1) ^ 2)) / (algebraMap Tate F X₀) ^ (k + 1)
  have ht_norm (k : ℕ) : ‖t k‖ = ‖a‖ ^ ((k + 1) ^ 2) / c i₀ ^ (k + 1) := by
    simp only [t, norm_div, norm_algebraMap', norm_pow, hX₀_F_norm]
  have ht_anti : Antitone fun k ↦ ‖t k‖ := by
    refine antitone_nat_of_succ_le fun k ↦ ?_
    rw [ht_norm, ht_norm]
    have hexp : (k + 1 + 1) ^ 2 = (k + 1) ^ 2 + 1 + (2 * k + 2) := by ring
    rw [hexp, pow_add ‖a‖, pow_add ‖a‖ ((k + 1) ^ 2) 1, pow_one,
      pow_succ (c i₀) (k + 1)]
    calc ‖a‖ ^ ((k + 1) ^ 2) * ‖a‖ * ‖a‖ ^ (2 * k + 2) / (c i₀ ^ (k + 1) * c i₀)
        = (‖a‖ ^ ((k + 1) ^ 2) / c i₀ ^ (k + 1)) * ((‖a‖ / c i₀) * ‖a‖ ^ (2 * k + 2)) := by
          ring
      _ ≤ (‖a‖ ^ ((k + 1) ^ 2) / c i₀ ^ (k + 1)) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hpow1 : ‖a‖ ^ (2 * k + 2) ≤ 1 := pow_le_one₀ ha_pos.le ha1.le
          nlinarith
      _ = ‖a‖ ^ ((k + 1) ^ 2) / c i₀ ^ (k + 1) := mul_one _
  have ht_le_geom (k : ℕ) : ‖t k‖ ≤ (‖a‖ / c i₀) ^ (k + 1) := by
    rw [ht_norm, div_pow]
    refine div_le_div_of_nonneg_right ?_ (pow_pos hc₀ _).le
    exact pow_le_pow_of_le_one ha_pos.le ha1.le (Nat.le_self_pow two_ne_zero (k + 1))
  let s (N : ℕ) : F := ∑ k ∈ Finset.range N, t k
  have hs_diff {N M : ℕ} (hNM : N ≤ M) : ‖s M - s N‖ ≤ ‖t N‖ := by
    induction M, hNM using Nat.le_induction with
    | base =>
      rw [sub_self, norm_zero]
      exact norm_nonneg _
    | succ M hNM ih =>
      have hstep : s (M + 1) - s N = (s M - s N) + t M := by
        simp only [s, Finset.sum_range_succ]
        abel
      rw [hstep]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (ht_anti hNM))
  have hs_cauchy : CauchySeq s := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hlim : Tendsto (fun N ↦ (‖a‖ / c i₀) ^ (N + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hrat0 hrat1).comp (tendsto_add_atTop_nat 1)
    obtain ⟨N₀, hN₀⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
    refine ⟨N₀, fun m hm n hn ↦ ?_⟩
    rcases le_total n m with hnm | hmn
    · rw [dist_eq_norm]
      exact (hs_diff hnm).trans_lt ((ht_le_geom n).trans_lt (hN₀ n hn))
    · rw [dist_comm, dist_eq_norm]
      exact (hs_diff hmn).trans_lt ((ht_le_geom m).trans_lt (hN₀ m hm))
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hs_cauchy
  have hz_bound (N : ℕ) : ‖z - s N‖ ≤ ‖t N‖ :=
    le_of_tendsto ((hz.sub tendsto_const_nhds).norm)
      (eventually_atTop.mpr ⟨N, fun M hNM ↦ hs_diff hNM⟩)
  obtain ⟨P, Q, hQ_mem, rfl⟩ := IsFractionRing.div_surjective Tate z
  have hQ_ne : Q ≠ 0 := nonZeroDivisors.ne_zero hQ_mem
  have hQ_F_ne : algebraMap Tate F Q ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hQ_mem
  -- Choose a multi-index `μ₀` in the support of `Q` of minimal `i₀`-degree `d`.
  have hQ_supp : ∃ d : ℕ, ∃ μ : σ →₀ ℕ, μ i₀ = d ∧ coeff μ (Q : _root_.MvPowerSeries σ K) ≠ 0 := by
    have hQ_coe : (Q : _root_.MvPowerSeries σ K) ≠ 0 := fun h ↦ hQ_ne (Subtype.ext h)
    obtain ⟨μ, hμ⟩ := not_forall.mp (mt _root_.MvPowerSeries.ext hQ_coe)
    exact ⟨μ i₀, μ, rfl, by simpa using hμ⟩
  set d : ℕ := Nat.find hQ_supp
  obtain ⟨μ₀, hμ₀_deg, hμ₀_ne⟩ := Nat.find_spec hQ_supp
  have hQ_min (μ : σ →₀ ℕ) (hμ : coeff μ (Q : _root_.MvPowerSeries σ K) ≠ 0) : d ≤ μ i₀ :=
    Nat.find_min' hQ_supp ⟨μ, rfl, hμ⟩
  -- Numerator `P_N` of the partial sum `s N = P_N / X₀ ^ N`.
  let P_num (N : ℕ) : Tate :=
    ∑ k ∈ Finset.range N, algebraMap K Tate (a ^ ((k + 1) ^ 2)) * X₀ ^ (N - 1 - k)
  have hs_mul (N : ℕ) :
      s N * (algebraMap Tate F X₀) ^ N = algebraMap Tate F (P_num N) := by
    simp only [s, P_num, Finset.sum_mul, map_sum, map_mul, map_pow,
      ← IsScalarTower.algebraMap_apply K Tate F]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkN : k + 1 ≤ N := Finset.mem_range.mp hk
    have hsplit : N = (k + 1) + (N - 1 - k) := by omega
    dsimp only [t]
    rw [map_pow, div_eq_mul_inv, mul_assoc]
    refine congrArg (algebraMap K F a ^ ((k + 1) ^ 2) * ·) ?_
    nth_rw 1 [hsplit]
    rw [pow_add _ (k + 1) (N - 1 - k), inv_mul_cancel_left₀ (pow_ne_zero _ hX₀_F_ne)]
  -- For `N > d`, the `μ₀`-th coefficient of `P * X₀ ^ N - Q * P_num N` is `- a ^ (N ^ 2) * Q_μ₀`.
  have hcoeff_rem {N : ℕ} (hNd : d < N) :
      coeff μ₀ ((P * X₀ ^ N - Q * P_num N : Tate) : _root_.MvPowerSeries σ K) =
        -(a ^ (N ^ 2) * coeff μ₀ (Q : _root_.MvPowerSeries σ K)) := by
    have hd_eq : μ₀ i₀ = d := hμ₀_deg
    have hPX : coeff μ₀ ((P * X₀ ^ N : Tate) : _root_.MvPowerSeries σ K) = 0 := by
      dsimp only [X₀]
      rw [Subring.coe_mul, SubmonoidClass.coe_pow, X_pow_eq, coeff_mul_monomial]
      split_ifs with hle
      · exfalso
        have h := hle i₀
        rw [Finsupp.single_eq_same, hd_eq] at h
        omega
      · rfl
    have hQX_pos {m : ℕ} (hm : 0 < m) :
        coeff μ₀ ((Q : _root_.MvPowerSeries σ K) * (X i₀) ^ m) = 0 := by
      rw [X_pow_eq, coeff_mul_monomial]
      split_ifs with hle
      · rw [mul_one]
        by_contra hne
        have hmin_sub := hQ_min (μ₀ - Finsupp.single i₀ m) hne
        have hm_le : m ≤ d := by
          have h := hle i₀
          rwa [Finsupp.single_eq_same, hd_eq] at h
        simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same, hd_eq] at hmin_sub
        omega
      · rfl
    have hN_pos : 0 < N := (Nat.zero_le d).trans_lt hNd
    have hQP : coeff μ₀ ((Q * P_num N : Tate) : _root_.MvPowerSeries σ K) =
        a ^ (N ^ 2) * coeff μ₀ (Q : _root_.MvPowerSeries σ K) := by
      dsimp only [P_num, X₀]
      rw [Finset.mul_sum, AddSubmonoidClass.coe_finsetSum, map_sum, Finset.sum_eq_single (N - 1)]
      · have hzero : N - 1 - (N - 1) = 0 := Nat.sub_self _
        have hN1 : N - 1 + 1 = N := Nat.sub_add_cancel hN_pos
        rw [hzero, pow_zero, mul_one, hN1, Subring.coe_mul, coe_algebraMap_isRestrictedSubring,
          mul_comm, coeff_C_mul]
      · intro k hk hk_ne
        have hkN : k < N := Finset.mem_range.mp hk
        have hm : 0 < N - 1 - k := by omega
        rw [Subring.coe_mul, Subring.coe_mul, coe_algebraMap_isRestrictedSubring,
          SubmonoidClass.coe_pow, ← mul_assoc, mul_comm (Q : _root_.MvPowerSeries σ K), mul_assoc,
          coeff_C_mul, hQX_pos hm, mul_zero]
      · intro hnot
        exact absurd (Finset.mem_range.mpr (Nat.sub_lt hN_pos one_pos)) hnot
    rw [AddSubgroupClass.coe_sub, map_sub, hPX, hQP, zero_sub]
  -- Compare weighted coefficient lower bound with the approximation upper bound as `N → ∞`.
  let δ : ℝ := ‖coeff μ₀ (Q : _root_.MvPowerSeries σ K)‖ * μ₀.prod (c · ^ ·)
  have hδ_pos : 0 < δ := mul_pos (norm_pos_iff.mpr hμ₀_ne) (prod_pow_pos μ₀)
  have hbound_N {N : ℕ} (hNd : d < N) : δ ≤ (‖Q‖ / c i₀) * ‖a‖ ^ (2 * N + 1) := by
    let rem : Tate := P * X₀ ^ N - Q * P_num N
    have hrem_F : algebraMap Tate F rem =
        (algebraMap Tate F P / algebraMap Tate F Q - s N) *
          algebraMap Tate F Q * (algebraMap Tate F X₀) ^ N := by
      simp only [rem, map_sub, map_mul, map_pow, sub_mul, div_mul_cancel₀ _ hQ_F_ne]
      rw [mul_right_comm (s N), hs_mul, mul_comm (algebraMap Tate F (P_num N))]
    have hrem_upper : ‖rem‖ ≤ ‖a‖ ^ (N ^ 2) * ((‖Q‖ / c i₀) * ‖a‖ ^ (2 * N + 1)) := by
      rw [← norm_algebraMap_gaussFractionField σ K c rem, hrem_F, norm_mul, norm_mul,
        norm_pow, norm_algebraMap_gaussFractionField, hX₀_F_norm]
      calc ‖algebraMap Tate F P / algebraMap Tate F Q - s N‖ * ‖Q‖ * c i₀ ^ N
          ≤ ‖t N‖ * ‖Q‖ * c i₀ ^ N := by
            gcongr
            exact hz_bound N
        _ = (‖a‖ ^ ((N + 1) ^ 2) / (c i₀ ^ N * c i₀)) * ‖Q‖ * c i₀ ^ N := by
            rw [ht_norm, pow_succ (c i₀) N]
        _ = ‖a‖ ^ ((N + 1) ^ 2) * (‖Q‖ / c i₀) := by
            field_simp [hc₀.ne']
        _ = ‖a‖ ^ (N ^ 2) * ((‖Q‖ / c i₀) * ‖a‖ ^ (2 * N + 1)) := by
            have hexp : (N + 1) ^ 2 = N ^ 2 + (2 * N + 1) := by ring
            rw [hexp, pow_add]
            ring
    have hrem_lower : ‖a‖ ^ (N ^ 2) * δ ≤ ‖rem‖ := by
      have h := norm_coeff_mul_prod_le rem μ₀
      simpa only [rem, hcoeff_rem hNd, norm_neg, norm_mul, norm_pow, mul_assoc, δ] using h
    exact le_of_mul_le_mul_left (hrem_lower.trans hrem_upper) (pow_pos ha_pos (N ^ 2))
  have hlim0 : Tendsto (fun k : ℕ ↦ (‖Q‖ / c i₀) * ‖a‖ ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one ha_pos.le ha1)
  obtain ⟨K₀, hK₀⟩ := (hlim0.eventually (gt_mem_nhds hδ_pos)).exists_forall_of_atTop
  set N := max (d + 1) K₀
  have hNd : d < N := Nat.lt_of_succ_le (le_max_left _ _)
  have hK_le : K₀ ≤ N := le_max_right _ _
  have hNK : K₀ ≤ 2 * N + 1 := by omega
  exact (hbound_N hNd).not_gt (hK₀ (2 * N + 1) hNK)

end Incomplete

end TauCeti.MvPowerSeries
