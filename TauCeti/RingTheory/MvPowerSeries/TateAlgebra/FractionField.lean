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
Injective ring homomorphisms between Tate algebras extend across fractions to ring homomorphisms
between their Gauss-normed fraction fields (`RingHom.gaussFractionFieldMap`), preserving the
extended Gauss norm when the Tate-algebra map is norm-preserving
(`RingHom.norm_gaussFractionFieldMap`). For an empty variable type the coefficient embedding is an
algebra equivalence.

This is the normed fraction field, not its completion: when `σ` is nonempty and `K` is
nontrivially normed, `GaussFractionField σ K c` is incomplete
(`TauCeti.MvPowerSeries.not_completeSpace_gaussFractionField`). Neither completeness of the
coefficient field nor finiteness of the variable type is needed for the construction.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.3.1, for the Gauss-normed
  fraction field used in weak stability.
-/

public section

namespace MvPowerSeries

/-- If `μ₀` minimizes `μ i₀` over the support of `Q`, then for `μ₀ i₀ < N` the `μ₀`-th coefficient
of `P * X i₀ ^ N - Q * ∑_{k < N} C (f k) * X i₀ ^ (N - 1 - k)` is `- f (N - 1) * coeff μ₀ Q`. -/
private theorem coeff_mul_X_pow_sub_mul_sum_eq {σ R : Type*} [CommRing R]
    (P Q : MvPowerSeries σ R) (i₀ : σ) {μ₀ : σ →₀ ℕ}
    (hQ_min : ∀ μ, coeff μ Q ≠ 0 → μ₀ i₀ ≤ μ i₀) (f : ℕ → R) {N : ℕ} (hNd : μ₀ i₀ < N) :
    coeff μ₀ (P * X i₀ ^ N - Q * ∑ k ∈ Finset.range N, C (f k) * X i₀ ^ (N - 1 - k)) =
      -(f (N - 1) * coeff μ₀ Q) := by
  have hPX : coeff μ₀ (P * X i₀ ^ N) = 0 := by
    rw [X_pow_eq, coeff_mul_monomial]
    split_ifs with hle
    · exfalso
      have h := hle i₀
      rw [Finsupp.single_eq_same] at h
      omega
    · rfl
  have hQX_pos {m : ℕ} (hm : 0 < m) : coeff μ₀ (Q * X i₀ ^ m) = 0 := by
    rw [X_pow_eq, coeff_mul_monomial]
    split_ifs with hle
    · rw [mul_one]
      by_contra hne
      have hmin_sub := hQ_min (μ₀ - Finsupp.single i₀ m) hne
      have hm_le : m ≤ μ₀ i₀ := by
        have h := hle i₀
        rwa [Finsupp.single_eq_same] at h
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same] at hmin_sub
      omega
    · rfl
  have hN_pos : 0 < N := (Nat.zero_le _).trans_lt hNd
  have hQP : coeff μ₀ (Q * ∑ k ∈ Finset.range N, C (f k) * X i₀ ^ (N - 1 - k)) =
      f (N - 1) * coeff μ₀ Q := by
    rw [Finset.mul_sum, map_sum, Finset.sum_eq_single (N - 1)]
    · rw [Nat.sub_self, pow_zero, mul_one, mul_comm, coeff_C_mul]
    · intro k hk hk_ne
      have hkN : k < N := Finset.mem_range.mp hk
      have hm : 0 < N - 1 - k := by omega
      rw [← mul_assoc, mul_comm Q, mul_assoc, coeff_C_mul, hQX_pos hm, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (Nat.sub_lt hN_pos one_pos)) hnot
  rw [map_sub, hPX, hQP, zero_sub]

end MvPowerSeries

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
    (fun f g ↦ by
      simpa only [IsAbsoluteValue.toAbsoluteValue_apply] using
        IsUltrametricDist.norm_add_le_max f g)

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

end TauCeti.MvPowerSeries

namespace RingHom

open _root_.MvPowerSeries TauCeti.MvPowerSeries

variable {σ σ' K K' : Type*} [NormedField K] [IsUltrametricDist K]
  [NormedField K'] [IsUltrametricDist K']
  {c : σ → ℝ} {c' : σ' → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < c' i)]

/-- An injective ring homomorphism between Tate algebras extends across fractions to a ring
homomorphism between their Gauss-normed fraction fields. -/
noncomputable def gaussFractionFieldMap
    (φ : IsRestricted.subring (R := K) c →+* IsRestricted.subring (R := K') c')
    (hφ : Function.Injective φ) :
    GaussFractionField σ K c →+* GaussFractionField σ' K' c' :=
  IsFractionRing.lift (g := (algebraMap _ (GaussFractionField σ' K' c')).comp φ)
    ((IsFractionRing.injective (IsRestricted.subring (R := K') c')
      (GaussFractionField σ' K' c')).comp hφ)

/-- `gaussFractionFieldMap` extends `φ` along the fraction-field embeddings. -/
@[simp]
theorem gaussFractionFieldMap_algebraMap
    (φ : IsRestricted.subring (R := K) c →+* IsRestricted.subring (R := K') c')
    (hφ : Function.Injective φ) (f : IsRestricted.subring (R := K) c) :
    φ.gaussFractionFieldMap hφ (algebraMap _ (GaussFractionField σ K c) f) =
      algebraMap _ (GaussFractionField σ' K' c') (φ f) := by
  rw [gaussFractionFieldMap, IsFractionRing.lift_algebraMap, RingHom.comp_apply]

/-- Extending a norm-preserving homomorphism of Tate algebras preserves the extended Gauss norm. -/
theorem norm_gaussFractionFieldMap
    (φ : IsRestricted.subring (R := K) c →+* IsRestricted.subring (R := K') c')
    (hφ : Function.Injective φ) (hφ_norm : ∀ f, ‖φ f‖ = ‖f‖) (z : GaussFractionField σ K c) :
    ‖φ.gaussFractionFieldMap hφ z‖ = ‖z‖ := by
  obtain ⟨f, g, _, rfl⟩ := IsFractionRing.div_surjective (IsRestricted.subring (R := K) c) z
  rw [map_div₀, gaussFractionFieldMap_algebraMap, gaussFractionFieldMap_algebraMap, norm_div,
    norm_div, norm_algebraMap_gaussFractionField σ' K' c' _,
    norm_algebraMap_gaussFractionField σ' K' c' _, norm_algebraMap_gaussFractionField σ K c _,
    norm_algebraMap_gaussFractionField σ K c _, hφ_norm, hφ_norm]

/-- Extending a norm-preserving homomorphism of Tate algebras yields an isometry between their
Gauss-normed fraction fields. -/
theorem isometry_gaussFractionFieldMap
    (φ : IsRestricted.subring (R := K) c →+* IsRestricted.subring (R := K') c')
    (hφ : Function.Injective φ) (hφ_norm : ∀ f, ‖φ f‖ = ‖f‖) :
    Isometry (φ.gaussFractionFieldMap hφ) :=
  (AddMonoidHomClass.isometry_iff_norm _).mpr (φ.norm_gaussFractionFieldMap hφ hφ_norm)

end RingHom

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries Filter
open scoped Topology

section Incomplete

section Helpers

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]
  {c : σ → ℝ} [∀ i, Fact (0 < c i)]

local notation "Tate" => IsRestricted.subring (R := K) c

/-- In a complete `GaussFractionField σ K c`, for `0 < ‖a‖ < min 1 (c i₀)`, the Laurent series
`∑_{k ≥ 1} a ^ (k ^ 2) / Xᵢ₀ ^ k` converges to a limit `z` whose `N`-th remainder has norm at most
`‖a‖ ^ ((N + 1) ^ 2) / c i₀ ^ (N + 1)`. -/
private theorem exists_tendsto_sum_pow_sq_div_pow [CompleteSpace (GaussFractionField σ K c)]
    (i₀ : σ) {a : K} (ha_pos : 0 < ‖a‖) (ha1 : ‖a‖ < 1) (hac : ‖a‖ < c i₀) :
    let F := GaussFractionField σ K c
    let X₀ : Tate := ⟨X i₀, isRestricted_monomial c (Finsupp.single i₀ 1) (1 : K)⟩
    ∃ z : F, ∀ N : ℕ,
      ‖z - ∑ k ∈ Finset.range N,
          algebraMap K F (a ^ ((k + 1) ^ 2)) / (algebraMap Tate F X₀) ^ (k + 1)‖ ≤
        ‖a‖ ^ ((N + 1) ^ 2) / c i₀ ^ (N + 1) := by
  let F := GaussFractionField σ K c
  have hc₀ : 0 < c i₀ := Fact.out
  have hrat1 : ‖a‖ / c i₀ < 1 := (div_lt_one hc₀).mpr hac
  let X₀ : Tate := ⟨X i₀, isRestricted_monomial c (Finsupp.single i₀ 1) (1 : K)⟩
  have hX₀_F_norm : ‖algebraMap Tate F X₀‖ = c i₀ := by
    rw [norm_algebraMap_gaussFractionField, norm_X]
  let t (k : ℕ) : F :=
    algebraMap K F (a ^ ((k + 1) ^ 2)) / (algebraMap Tate F X₀) ^ (k + 1)
  have ht_norm (k : ℕ) : ‖t k‖ = ‖a‖ ^ ((k + 1) ^ 2) / c i₀ ^ (k + 1) := by
    simp only [t, norm_div, norm_algebraMap', norm_pow, hX₀_F_norm]
  have ht_anti : Antitone fun k ↦ ‖t k‖ := by
    refine antitone_nat_of_succ_le fun k ↦ ?_
    rw [ht_norm, ht_norm]
    have hexp : (k + 1 + 1) ^ 2 = (k + 1) ^ 2 + 1 + (2 * k + 2) := by ring
    rw [hexp, pow_add ‖a‖, pow_add ‖a‖ ((k + 1) ^ 2) 1, pow_one, pow_succ (c i₀) (k + 1)]
    calc ‖a‖ ^ ((k + 1) ^ 2) * ‖a‖ * ‖a‖ ^ (2 * k + 2) / (c i₀ ^ (k + 1) * c i₀)
        = (‖a‖ ^ ((k + 1) ^ 2) / c i₀ ^ (k + 1)) * ((‖a‖ / c i₀) * ‖a‖ ^ (2 * k + 2)) := by ring
      _ ≤ (‖a‖ ^ ((k + 1) ^ 2) / c i₀ ^ (k + 1)) * 1 :=
          mul_le_mul_of_nonneg_left
            ((mul_le_of_le_one_left (pow_nonneg ha_pos.le _) hrat1.le).trans
              (pow_le_one₀ ha_pos.le ha1.le))
            (by positivity)
      _ = ‖a‖ ^ ((k + 1) ^ 2) / c i₀ ^ (k + 1) := mul_one _
  have ht_le_geom (k : ℕ) : ‖t k‖ ≤ (‖a‖ / c i₀) ^ (k + 1) := by
    rw [ht_norm, div_pow]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_of_le_one ha_pos.le ha1.le (Nat.le_self_pow two_ne_zero (k + 1)))
      (pow_pos hc₀ _).le
  let s (N : ℕ) : F := ∑ k ∈ Finset.range N, t k
  have hs_diff {N M : ℕ} (hNM : N ≤ M) : ‖s M - s N‖ ≤ ‖t N‖ := by
    rw [← Finset.sum_Ico_eq_sub _ hNM]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk ↦
      ht_anti (Finset.mem_Ico.mp hk).1
  have hs_cauchy : CauchySeq s :=
    cauchySeq_of_le_geometric (‖a‖ / c i₀) (‖a‖ / c i₀) hrat1 fun k ↦ by
      rw [dist_comm, dist_eq_norm, Finset.sum_range_succ_sub_sum, ← pow_succ']
      exact ht_le_geom k
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hs_cauchy
  refine ⟨z, fun N ↦ ?_⟩
  rw [← ht_norm]
  exact le_of_tendsto ((hz.sub tendsto_const_nhds).norm)
    (eventually_atTop.mpr ⟨N, fun M hNM ↦ hs_diff hNM⟩)

/-- For `rem = P * X₀ ^ N - Q * P_num`, comparing the `μ₀`-th weighted coefficient of `rem` with
its Gauss-norm upper bound from approximating `P / Q` bounds the `μ₀`-th weighted coefficient of `Q`
by `(‖Q‖ / c i₀) * ‖a‖ ^ (2 * N + 1)`. -/
private theorem norm_coeff_mul_prod_le_of_norm_rem_le
    (i₀ : σ) {a : K} (ha_pos : 0 < ‖a‖) (P Q : Tate)
    {μ₀ : σ →₀ ℕ} (hQ_min : ∀ μ, coeff μ (Q : _root_.MvPowerSeries σ K) ≠ 0 → μ₀ i₀ ≤ μ i₀)
    {N : ℕ} (hNd : μ₀ i₀ < N)
    (rem : Tate)
    (hrem_def :
      let X₀ : Tate := ⟨X i₀, isRestricted_monomial c (Finsupp.single i₀ 1) (1 : K)⟩
      rem = P * X₀ ^ N -
        Q * ∑ k ∈ Finset.range N, algebraMap K Tate (a ^ ((k + 1) ^ 2)) * X₀ ^ (N - 1 - k))
    (hrem_norm : ‖rem‖ ≤ (‖a‖ ^ ((N + 1) ^ 2) / c i₀ ^ (N + 1)) * ‖Q‖ * c i₀ ^ N) :
    ‖coeff μ₀ (Q : _root_.MvPowerSeries σ K)‖ * μ₀.prod (c · ^ ·) ≤
      (‖Q‖ / c i₀) * ‖a‖ ^ (2 * N + 1) := by
  have hc₀ : 0 < c i₀ := Fact.out
  have hrem_upper : ‖rem‖ ≤ ‖a‖ ^ (N ^ 2) * ((‖Q‖ / c i₀) * ‖a‖ ^ (2 * N + 1)) := by
    calc ‖rem‖
        ≤ (‖a‖ ^ ((N + 1) ^ 2) / c i₀ ^ (N + 1)) * ‖Q‖ * c i₀ ^ N := hrem_norm
      _ = ‖a‖ ^ ((N + 1) ^ 2) * (‖Q‖ / c i₀) := by
          rw [pow_succ (c i₀) N]
          field_simp [hc₀.ne']
      _ = ‖a‖ ^ (N ^ 2) * ((‖Q‖ / c i₀) * ‖a‖ ^ (2 * N + 1)) := by
          have hexp : (N + 1) ^ 2 = N ^ 2 + (2 * N + 1) := by ring
          rw [hexp, pow_add]
          ring
  have hN_pos : 0 < N := (Nat.zero_le _).trans_lt hNd
  have hcoeff_rem : coeff μ₀ (rem : _root_.MvPowerSeries σ K) =
      -(a ^ (N ^ 2) * coeff μ₀ (Q : _root_.MvPowerSeries σ K)) := by
    rw [hrem_def]
    simp only [AddSubgroupClass.coe_sub, Subring.coe_mul, SubmonoidClass.coe_pow,
      AddSubmonoidClass.coe_finsetSum, coe_algebraMap_isRestrictedSubring]
    rw [coeff_mul_X_pow_sub_mul_sum_eq (P : _root_.MvPowerSeries σ K)
      (Q : _root_.MvPowerSeries σ K) i₀ hQ_min (fun k ↦ a ^ ((k + 1) ^ 2)) hNd,
      Nat.sub_add_cancel hN_pos]
  have hrem_lower :
      ‖a‖ ^ (N ^ 2) * (‖coeff μ₀ (Q : _root_.MvPowerSeries σ K)‖ * μ₀.prod (c · ^ ·)) ≤ ‖rem‖ := by
    simpa only [hcoeff_rem, norm_neg, norm_mul, norm_pow, mul_assoc] using
      norm_coeff_mul_prod_le rem μ₀
  exact le_of_mul_le_mul_left (hrem_lower.trans hrem_upper) (pow_pos ha_pos (N ^ 2))

end Helpers

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
  let X₀ : Tate := ⟨X i₀, isRestricted_monomial c (Finsupp.single i₀ 1) (1 : K)⟩
  have hX₀_F_norm : ‖algebraMap Tate F X₀‖ = c i₀ := by
    rw [norm_algebraMap_gaussFractionField, norm_X]
  have hX₀_F_ne : algebraMap Tate F X₀ ≠ 0 :=
    norm_ne_zero_iff.mp (hX₀_F_norm.trans_ne hc₀.ne')
  obtain ⟨z, hz_bound⟩ := exists_tendsto_sum_pow_sq_div_pow (c := c) i₀ ha_pos ha1 hac
  let s (N : ℕ) : F := ∑ k ∈ Finset.range N,
    algebraMap K F (a ^ ((k + 1) ^ 2)) / (algebraMap Tate F X₀) ^ (k + 1)
  obtain ⟨P, Q, hQ_mem, rfl⟩ := IsFractionRing.div_surjective Tate z
  have hQ_F_ne : algebraMap Tate F Q ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hQ_mem
  -- Choose a multi-index `μ₀` in the support of `Q` of minimal `i₀`-degree `d`.
  have hQ_supp : ∃ d : ℕ, ∃ μ : σ →₀ ℕ, μ i₀ = d ∧ coeff μ (Q : _root_.MvPowerSeries σ K) ≠ 0 := by
    have hQ_coe : (Q : _root_.MvPowerSeries σ K) ≠ 0 :=
      Subtype.coe_ne_coe.mpr (nonZeroDivisors.ne_zero hQ_mem)
    obtain ⟨μ, hμ⟩ := not_forall.mp (mt _root_.MvPowerSeries.ext hQ_coe)
    exact ⟨μ i₀, μ, rfl, by simpa using hμ⟩
  obtain ⟨μ₀, hμ₀_deg, hμ₀_ne⟩ := Nat.find_spec hQ_supp
  have hQ_min (μ : σ →₀ ℕ) (hμ : coeff μ (Q : _root_.MvPowerSeries σ K) ≠ 0) : μ₀ i₀ ≤ μ i₀ :=
    hμ₀_deg.trans_le (Nat.find_min' hQ_supp ⟨μ, rfl, hμ⟩)
  -- Numerator `P_num N` of the partial sum `s N = P_num N / X₀ ^ N`.
  let P_num (N : ℕ) : Tate :=
    ∑ k ∈ Finset.range N, algebraMap K Tate (a ^ ((k + 1) ^ 2)) * X₀ ^ (N - 1 - k)
  have hs_mul (N : ℕ) : s N * (algebraMap Tate F X₀) ^ N = algebraMap Tate F (P_num N) := by
    simp only [s, P_num, Finset.sum_mul, map_sum, map_mul, map_pow,
      ← IsScalarTower.algebraMap_apply K Tate F]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hsplit : N = (k + 1) + (N - 1 - k) := by
      have := Finset.mem_range.mp hk
      omega
    rw [div_eq_mul_inv, mul_assoc]
    refine congrArg (algebraMap K F a ^ ((k + 1) ^ 2) * ·) ?_
    nth_rw 1 [hsplit]
    rw [pow_add _ (k + 1) (N - 1 - k), inv_mul_cancel_left₀ (pow_ne_zero _ hX₀_F_ne)]
  -- Compare weighted coefficient lower bound with the approximation upper bound as `N → ∞`.
  let δ : ℝ := ‖coeff μ₀ (Q : _root_.MvPowerSeries σ K)‖ * μ₀.prod (c · ^ ·)
  have hδ_pos : 0 < δ := mul_pos (norm_pos_iff.mpr hμ₀_ne) (prod_pow_pos μ₀)
  have hbound_N {N : ℕ} (hNd : μ₀ i₀ < N) : δ ≤ (‖Q‖ / c i₀) * ‖a‖ ^ (2 * N + 1) := by
    let rem : Tate := P * X₀ ^ N - Q * P_num N
    have hrem_F : algebraMap Tate F rem =
        (algebraMap Tate F P / algebraMap Tate F Q - s N) *
          algebraMap Tate F Q * (algebraMap Tate F X₀) ^ N := by
      simp only [rem, map_sub, map_mul, map_pow, sub_mul, div_mul_cancel₀ _ hQ_F_ne]
      rw [mul_right_comm (s N), hs_mul, mul_comm (algebraMap Tate F (P_num N))]
    refine norm_coeff_mul_prod_le_of_norm_rem_le i₀ ha_pos P Q hQ_min hNd rem rfl ?_
    rw [← norm_algebraMap_gaussFractionField σ K c rem, hrem_F, norm_mul, norm_mul, norm_pow,
      norm_algebraMap_gaussFractionField, hX₀_F_norm]
    gcongr
    exact hz_bound N
  have hlim0 : Tendsto (fun k : ℕ ↦ (‖Q‖ / c i₀) * ‖a‖ ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one ha_pos.le ha1)
  obtain ⟨K₀, hK₀⟩ := (hlim0.eventually (gt_mem_nhds hδ_pos)).exists_forall_of_atTop
  set N := max (μ₀ i₀ + 1) K₀
  have hNd : μ₀ i₀ < N := Nat.lt_of_succ_le (le_max_left _ _)
  have hK_le : K₀ ≤ N := le_max_right _ _
  exact (hbound_N hNd).not_gt (hK₀ (2 * N + 1) (by omega))

end Incomplete

end TauCeti.MvPowerSeries
