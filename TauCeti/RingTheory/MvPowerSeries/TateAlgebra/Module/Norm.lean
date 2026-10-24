/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Basic

/-!
# Gauss norms on module-valued restricted series

The existing restricted coefficient families carry the weighted supremum norm at every
positive real polyradius. Coefficient projections are bounded, bounded maps of coefficient
modules induce bounded maps of restricted families, and convolution by a scalar restricted
series satisfies the Gauss norm inequality. These estimates equip module-valued series with
the norm needed for bounded analytic operations and presentations of coefficient modules.

Complete coefficient groups give complete restricted families. The construction allows
arbitrary variable sets and normed additive coefficient groups. Neither completeness nor an
ultrametric norm is needed for the additive norm; the latter is required for the convolution
estimate. For ring-valued coefficients, the existing comparison
with scalar restricted series preserves the Gauss norm.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

noncomputable section

namespace TauCeti.MvPowerSeries.IsRestrictedFamily

open Filter Finset _root_.MvPowerSeries

variable {σ E F R : Type*} [NormedAddCommGroup E] {c : σ → ℝ}
  [hc : ∀ i, Fact (0 < c i)]

/-- The Gauss norm of a restricted coefficient family at positive polyradii. -/
instance instGaussNormedAddCommGroup : NormedAddCommGroup (IsRestrictedFamily.addSubgroup E c) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun a := ⨆ t, ‖(a : (σ →₀ ℕ) → E) t‖ * t.prod (c · ^ ·)
      map_zero' := by simp
      add_le' a b := by
        refine ciSup_le fun t ↦ ?_
        calc
          _ ≤ (‖(a : (σ →₀ ℕ) → E) t‖ + ‖(b : (σ →₀ ℕ) → E) t‖) *
              t.prod (c · ^ ·) := mul_le_mul_of_nonneg_right (norm_add_le _ _)
                (prod_pow_pos t).le
          _ ≤ _ := by
            rw [add_mul]
            exact add_le_add
              (le_ciSup
                (isRestrictedFamily_iff.mp (mem_addSubgroup.mp a.2)).bddAbove_range_of_cofinite t)
              (le_ciSup
                (isRestrictedFamily_iff.mp (mem_addSubgroup.mp b.2)).bddAbove_range_of_cofinite t)
      neg' a := by simp
      eq_zero_of_map_eq_zero' a ha := by
        apply ext
        intro t
        have h := le_ciSup
          (isRestrictedFamily_iff.mp (mem_addSubgroup.mp a.2)).bddAbove_range_of_cofinite t
        rw [ha] at h
        simpa using norm_eq_zero.mp (nonpos_of_mul_nonpos_left h (prod_pow_pos t)
          |>.antisymm (norm_nonneg _)) }

/-- The uniformity on restricted families is the Gauss uniformity. -/
instance : UniformSpace (IsRestrictedFamily.addSubgroup E c) :=
  instGaussNormedAddCommGroup.toMetricSpace.toUniformSpace

/-- The topology on restricted families is the Gauss topology. -/
instance : TopologicalSpace (IsRestrictedFamily.addSubgroup E c) :=
  instGaussNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace

/-- The norm is the supremum of the weighted coefficient norms. Restrictedness ensures that
this supremum is bounded. -/
theorem norm_eq_iSup (a : IsRestrictedFamily.addSubgroup E c) :
    ‖a‖ = ⨆ t, ‖(a : (σ →₀ ℕ) → E) t‖ * t.prod (c · ^ ·) := (rfl)

/-- A weighted coefficient norm is bounded by the Gauss norm of the family. -/
theorem norm_coeff_mul_prod_le (a : IsRestrictedFamily.addSubgroup E c) (t : σ →₀ ℕ) :
    ‖(a : (σ →₀ ℕ) → E) t‖ * t.prod (c · ^ ·) ≤ ‖a‖ :=
  le_ciSup (isRestrictedFamily_iff.mp (mem_addSubgroup.mp a.2)).bddAbove_range_of_cofinite t

/-- A bound on the Gauss norm is equivalent to the same bound on every weighted coefficient. -/
theorem norm_le_iff {a : IsRestrictedFamily.addSubgroup E c} {B : ℝ} :
    ‖a‖ ≤ B ↔ ∀ t, ‖(a : (σ →₀ ℕ) → E) t‖ * t.prod (c · ^ ·) ≤ B :=
  ⟨fun h t ↦ (norm_coeff_mul_prod_le a t).trans h, fun h ↦ ciSup_le h⟩

/-- Coefficient projections have bound the inverse of the monomial weight. -/
theorem norm_coeff_le (a : IsRestrictedFamily.addSubgroup E c) (t : σ →₀ ℕ) :
    ‖(a : (σ →₀ ℕ) → E) t‖ ≤ (t.prod (c · ^ ·))⁻¹ * ‖a‖ := by
  rw [inv_mul_eq_div, le_div_iff₀ (prod_pow_pos t)]
  exact norm_coeff_mul_prod_le a t

/-- A family supported at one exponent has the weighted norm of that coefficient. -/
@[simp]
theorem norm_single [DecidableEq σ] (t : σ →₀ ℕ) (e : E) :
    ‖(⟨Pi.single t e, mem_addSubgroup.mpr (isRestrictedFamily_single c t e)⟩ :
      IsRestrictedFamily.addSubgroup E c)‖ = ‖e‖ * t.prod (c · ^ ·) := by
  classical
  apply le_antisymm
  · apply norm_le_iff.mpr
    intro s
    by_cases h : s = t
    · subst s
      simp
    · simp [Pi.single_eq_of_ne h, mul_nonneg (norm_nonneg e) (prod_pow_pos t).le]
  · simpa using norm_coeff_mul_prod_le
      (⟨Pi.single t e, mem_addSubgroup.mpr (isRestrictedFamily_single c t e)⟩ :
        IsRestrictedFamily.addSubgroup E c) t

/-- Coefficients are uniformly continuous for the Gauss norm. -/
theorem uniformContinuous_coeff (t : σ →₀ ℕ) :
    UniformContinuous fun a : IsRestrictedFamily.addSubgroup E c ↦
      (a : (σ →₀ ℕ) → E) t :=
  AddMonoidHomClass.uniformContinuous_of_bound
    ((Pi.evalAddMonoidHom _ t).comp (IsRestrictedFamily.addSubgroup E c).subtype)
    _ fun a ↦ norm_coeff_le a t

/-- Complete coefficient groups give complete restricted families for the Gauss norm. -/
instance [CompleteSpace E] : CompleteSpace (IsRestrictedFamily.addSubgroup E c) := by
  refine Metric.complete_of_cauchySeq_tendsto fun A hA ↦ ?_
  have hcoeff (t : σ →₀ ℕ) : CauchySeq fun k ↦ (A k : (σ →₀ ℕ) → E) t :=
    (uniformContinuous_coeff t).comp_cauchySeq hA
  choose a ha using fun t ↦ cauchySeq_tendsto_of_complete (hcoeff t)
  -- The Cauchy estimates pass to the coefficientwise limit uniformly in the exponent.
  have hunif : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ t,
      ‖(A k : (σ →₀ ℕ) → E) t - a t‖ * t.prod (c · ^ ·) ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hA ε hε
    refine ⟨N, fun k hk t ↦ le_of_tendsto
      (((tendsto_const_nhds.sub (ha t)).norm).mul_const (t.prod (c · ^ ·)))
      (eventually_atTop.mpr ⟨N, fun l hl ↦ ?_⟩)⟩
    have h := norm_coeff_mul_prod_le (A k - A l) t
    rw [AddSubgroup.coe_sub, Pi.sub_apply] at h
    exact h.trans ((dist_eq_norm _ _).symm.trans_le (hN k hk l hl).le)
  -- A uniform limit of families vanishing at infinity again vanishes at infinity.
  have hres : IsRestrictedFamily c a := by
    rw [isRestrictedFamily_iff]
    refine tendsto_order.mpr ⟨fun b hb ↦ .of_forall fun t ↦
      hb.trans_le (mul_nonneg (norm_nonneg _) (prod_pow_pos t).le), fun ε hε ↦ ?_⟩
    obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
    filter_upwards [(isRestrictedFamily_iff.mp (mem_addSubgroup.mp (A N).2)).eventually
      (gt_mem_nhds (half_pos hε))] with t ht
    calc
      ‖a t‖ * t.prod (c · ^ ·) ≤ ‖(A N : (σ →₀ ℕ) → E) t‖ * t.prod (c · ^ ·) +
          ‖(A N : (σ →₀ ℕ) → E) t - a t‖ * t.prod (c · ^ ·) := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (norm_le_norm_add_norm_sub _ _) (prod_pow_pos t).le
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le ht (hN N le_rfl t)
      _ = ε := add_halves ε
  refine ⟨⟨a, mem_addSubgroup.mpr hres⟩, Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk ↦ (?_ : _ ≤ ε / 2).trans_lt (half_lt_self hε)⟩
  rw [dist_eq_norm, norm_le_iff]
  intro t
  simpa only [AddSubgroup.coe_sub, Pi.sub_apply] using hN k hk t

/-- The Gauss norm is ultrametric whenever the coefficient norm is. -/
instance [IsUltrametricDist E] : IsUltrametricDist (IsRestrictedFamily.addSubgroup E c) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun a b ↦
    norm_le_iff.mpr fun t ↦ calc
      _ ≤ max ‖(a : (σ →₀ ℕ) → E) t‖ ‖(b : (σ →₀ ℕ) → E) t‖ *
          t.prod (c · ^ ·) := mul_le_mul_of_nonneg_right
            (IsUltrametricDist.norm_add_le_max _ _) (prod_pow_pos t).le
      _ = max (‖(a : (σ →₀ ℕ) → E) t‖ * t.prod (c · ^ ·))
          (‖(b : (σ →₀ ℕ) → E) t‖ * t.prod (c · ^ ·)) :=
            max_mul_of_nonneg _ _ (prod_pow_pos t).le
      _ ≤ _ := max_le_max (norm_coeff_mul_prod_le a t) (norm_coeff_mul_prod_le b t)

section Scalar

variable [SeminormedRing R] [Module R E] [IsBoundedSMul R E]

/-- Coefficientwise scalar multiplication is bounded for the Gauss norm. -/
instance : IsBoundedSMul R (IsRestrictedFamily.addSubgroup E c) :=
  IsBoundedSMul.of_norm_smul_le fun r a ↦ norm_le_iff.mpr fun t ↦ by
    rw [coe_smul]
    calc
      _ ≤ (‖r‖ * ‖(a : (σ →₀ ℕ) → E) t‖) * t.prod (c · ^ ·) :=
        mul_le_mul_of_nonneg_right (norm_smul_le _ _) (prod_pow_pos t).le
      _ ≤ ‖r‖ * ‖a‖ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (norm_coeff_mul_prod_le a t) (norm_nonneg r)

variable [NormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]

/-- A coefficient map bounded by `C` induces a map of restricted families with the same bound. -/
theorem norm_mapLinearMap_le (φ : E →ₗ[R] F) {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖) (a : IsRestrictedFamily.addSubgroup E c) :
    ‖mapLinearMap φ hφ a‖ ≤ C * ‖a‖ :=
  norm_le_iff.mpr fun t ↦ by
    rw [coe_mapLinearMap]
    calc
      _ ≤ (C * ‖(a : (σ →₀ ℕ) → E) t‖) * t.prod (c · ^ ·) :=
        mul_le_mul_of_nonneg_right (hφ _) (prod_pow_pos t).le
      _ ≤ C * ‖a‖ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (norm_coeff_mul_prod_le a t) hC

/-- The map induced by a bounded coefficient linear map is uniformly continuous. -/
theorem uniformContinuous_mapLinearMap (φ : E →ₗ[R] F) {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖) :
    UniformContinuous (mapLinearMap (c := c) φ hφ) :=
  AddMonoidHomClass.uniformContinuous_of_bound (mapLinearMap (c := c) φ hφ) C
    (norm_mapLinearMap_le φ hC hφ)

end Scalar

/-- Over a normed field, restricted families with normed-space coefficients form a normed space
for the coefficientwise scalar action. -/
instance {K : Type*} [NormedField K] [NormedSpace K E] :
    NormedSpace K (IsRestrictedFamily.addSubgroup E c) where
  norm_smul_le := norm_smul_le

section Convolution

variable [NormedRing R] [IsUltrametricDist R] [IsUltrametricDist E]
  [Module R E] [IsBoundedSMul R E]

/-- Convolution by a scalar restricted series satisfies the Gauss norm inequality. -/
theorem norm_isRestrictedSubring_smul_le (f : IsRestricted.subring (R := R) c)
    (a : IsRestrictedFamily.addSubgroup E c) : ‖f • a‖ ≤ ‖f‖ * ‖a‖ := by
  classical
  apply norm_le_iff.mpr
  intro t
  rw [coe_isRestrictedSubring_smul, convSMul_apply]
  have ht := (prod_pow_pos (c := c) t).le
  calc
    _ ≤ ((Finset.antidiagonal t).sup' (HasAntidiagonal.nonempty_antidiagonal t)
        fun p ↦ ‖_root_.MvPowerSeries.coeff p.1 (f : MvPowerSeries σ R) • (a : (σ →₀ ℕ) → E) p.2‖) *
          t.prod (c · ^ ·) := mul_le_mul_of_nonneg_right
            ((HasAntidiagonal.nonempty_antidiagonal t).norm_sum_le_sup'_norm _) ht
    _ ≤ ‖f‖ * ‖a‖ := by
      rw [Finset.sup'_mul₀ ht]
      apply Finset.sup'_le
      intro p hp
      rw [← mem_antidiagonal.mp hp, prod_pow_add]
      calc
        _ ≤ (‖_root_.MvPowerSeries.coeff p.1 (f : MvPowerSeries σ R)‖ *
            ‖(a : (σ →₀ ℕ) → E) p.2‖) *
            (p.1.prod (c · ^ ·) * p.2.prod (c · ^ ·)) :=
          mul_le_mul_of_nonneg_right (norm_smul_le _ _)
            (mul_nonneg (prod_pow_pos p.1).le (prod_pow_pos p.2).le)
        _ = (‖_root_.MvPowerSeries.coeff p.1 (f : MvPowerSeries σ R)‖ *
            p.1.prod (c · ^ ·)) * (‖(a : (σ →₀ ℕ) → E) p.2‖ *
            p.2.prod (c · ^ ·)) := mul_mul_mul_comm _ _ _ _
        _ ≤ ‖f‖ * ‖a‖ := mul_le_mul
          (_root_.MvPowerSeries.norm_coeff_mul_prod_le f p.1)
          (norm_coeff_mul_prod_le a p.2)
            (mul_nonneg (norm_nonneg _) (prod_pow_pos p.2).le) (norm_nonneg f)

/-- Restricted scalar series act by bounded scalar multiplication on restricted families. -/
instance : IsBoundedSMul (IsRestricted.subring (R := R) c)
    (IsRestrictedFamily.addSubgroup E c) :=
  IsBoundedSMul.of_norm_smul_le norm_isRestrictedSubring_smul_le

/-- The existing ring-valued coefficient comparison preserves the Gauss norm. -/
@[simp]
theorem norm_subringLinearEquiv (f : IsRestricted.subring (R := R) c) :
    ‖subringLinearEquiv f‖ = ‖f‖ := by
  rw [norm_eq_iSup, _root_.MvPowerSeries.norm_eq_gaussNorm, gaussNorm]
  simp only [coe_subringLinearEquiv]

end Convolution

end TauCeti.MvPowerSeries.IsRestrictedFamily
