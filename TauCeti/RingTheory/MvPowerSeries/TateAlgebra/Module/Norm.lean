/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Basic

/-!
# Gauss norms on module-valued restricted series

The wrapper `IsRestrictedFamily.Gauss c E` equips the existing restricted families with the
weighted supremum seminorm at every positive real polyradius. Coefficient projections are
bounded, bounded maps of coefficient modules induce bounded maps of restricted families, and
convolution by a scalar restricted series satisfies the Gauss norm inequality. These estimates
equip module-valued series with the norm needed for bounded analytic operations and
presentations of coefficient modules.

Complete coefficient groups give complete restricted families. The construction allows arbitrary
variable sets and seminormed additive coefficient groups. It is a norm for normed coefficients.
Neither completeness nor an ultrametric norm is needed for the additive norm; the latter is
required for the convolution estimate. For ring-valued coefficients, the existing comparison
with scalar restricted series preserves the Gauss norm.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

noncomputable section

namespace TauCeti.MvPowerSeries.IsRestrictedFamily

open Filter Finset _root_.MvPowerSeries

variable {σ E F R : Type*} [SeminormedAddCommGroup E] {c : σ → ℝ}

/-- Restricted coefficient families with their Gauss topology at polyradius `c`. The wrapper keeps
this topology separate from the pointwise topology inherited by the algebraic subgroup. -/
structure Gauss (c : σ → ℝ) (E : Type*) [SeminormedAddCommGroup E] where
  /-- Regard an algebraic restricted family as a Gauss-topological family. -/
  ofAddSubgroup ::
  /-- The underlying algebraic restricted family. -/
  toAddSubgroup : IsRestrictedFamily.addSubgroup E c

namespace Gauss

instance : CoeFun (Gauss c E) (fun _ ↦ (σ →₀ ℕ) → E) :=
  ⟨fun a ↦ a.toAddSubgroup⟩

/-- Gauss families are determined by their coefficients. -/
@[ext]
theorem ext {a b : Gauss c E} (h : ∀ t, a t = b t) : a = b := by
  cases a
  cases b
  congr 1
  exact IsRestrictedFamily.ext h

@[simp]
theorem toAddSubgroup_ofAddSubgroup (a : IsRestrictedFamily.addSubgroup E c) :
    (ofAddSubgroup a).toAddSubgroup = a := (rfl)

@[simp]
theorem ofAddSubgroup_toAddSubgroup (a : Gauss c E) :
    ofAddSubgroup a.toAddSubgroup = a := (rfl)

@[simp]
theorem ofAddSubgroup_apply (a : IsRestrictedFamily.addSubgroup E c)
    (t : σ →₀ ℕ) : ofAddSubgroup a t = a.1 t := (rfl)

instance : AddCommGroup (Gauss c E) :=
  Equiv.addCommGroup
    { toFun := toAddSubgroup
      invFun := ofAddSubgroup
      left_inv := ofAddSubgroup_toAddSubgroup
      right_inv := toAddSubgroup_ofAddSubgroup }

@[simp]
theorem toAddSubgroup_add (a b : Gauss c E) :
    (a + b).toAddSubgroup = a.toAddSubgroup + b.toAddSubgroup := (rfl)

@[simp]
theorem zero_apply (t : σ →₀ ℕ) : (0 : Gauss c E) t = 0 := (rfl)

@[simp]
theorem neg_apply (a : Gauss c E) (t : σ →₀ ℕ) : (-a) t = -a t := (rfl)

@[simp]
theorem sub_apply (a b : Gauss c E) (t : σ →₀ ℕ) : (a - b) t = a t - b t := (rfl)

theorem add_apply (a b : Gauss c E) (t : σ →₀ ℕ) : (a + b) t = a t + b t := by
  simpa only [AddSubgroup.coe_add, Pi.add_apply] using
    congrArg (fun f : IsRestrictedFamily.addSubgroup E c ↦
      (f : (σ →₀ ℕ) → E) t) (toAddSubgroup_add a b)

/-- The Gauss-topological family and the existing algebraic subgroup have the same addition. -/
def toAddSubgroupAddEquiv :
    Gauss c E ≃+ IsRestrictedFamily.addSubgroup E c where
  toFun := toAddSubgroup
  invFun := ofAddSubgroup
  left_inv := ofAddSubgroup_toAddSubgroup
  right_inv := toAddSubgroup_ofAddSubgroup
  map_add' := toAddSubgroup_add

@[simp]
theorem toAddSubgroupAddEquiv_apply (a : Gauss c E) :
    toAddSubgroupAddEquiv a = a.toAddSubgroup := (rfl)

@[simp]
theorem toAddSubgroupAddEquiv_symm_apply
    (a : IsRestrictedFamily.addSubgroup E c) :
    toAddSubgroupAddEquiv.symm a = ofAddSubgroup a := (rfl)

section Module

variable (R : Type*) [SeminormedRing R] [Module R E] [IsBoundedSMul R E]

instance : Module R (Gauss c E) :=
  (toAddSubgroupAddEquiv (σ := σ) (E := E)).module R

/-- Forgetting the Gauss topology preserves the coefficient-module action. -/
def toAddSubgroupLinearEquiv :
    Gauss c E ≃ₗ[R] IsRestrictedFamily.addSubgroup E c :=
  (toAddSubgroupAddEquiv (σ := σ) (E := E)).linearEquiv R

@[simp]
theorem toAddSubgroupLinearEquiv_apply (a : Gauss c E) :
    toAddSubgroupLinearEquiv R a = a.toAddSubgroup := (rfl)

@[simp]
theorem toAddSubgroupLinearEquiv_symm_apply
    (a : IsRestrictedFamily.addSubgroup E c) :
    (toAddSubgroupLinearEquiv (σ := σ) R).symm a = ofAddSubgroup a := (rfl)

@[simp]
theorem smul_apply (r : R) (a : Gauss c E) (t : σ →₀ ℕ) :
    (r • a) t = r • a t := by
  simpa only [toAddSubgroupLinearEquiv_apply, coe_smul, Pi.smul_apply] using
    congrArg (fun b : IsRestrictedFamily.addSubgroup E c ↦ b.1 t)
      ((toAddSubgroupLinearEquiv R).map_smul r a)

/-- Include finite-support coefficient families in the Gauss-topological carrier. -/
noncomputable def ofFinsupp (c : σ → ℝ) : ((σ →₀ ℕ) →₀ E) →ₗ[R] Gauss c E :=
  (toAddSubgroupLinearEquiv R).symm.toLinearMap.comp
    (IsRestrictedFamily.ofFinsupp R c)

@[simp]
theorem ofFinsupp_apply (a : (σ →₀ ℕ) →₀ E) (t : σ →₀ ℕ) :
    ofFinsupp R c a t = a t := by
  simp only [ofFinsupp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    toAddSubgroupLinearEquiv_symm_apply, coe_ofFinsupp]

variable {R}

/-- A bounded coefficient map induces a linear map of Gauss families. -/
def mapLinearMap {F : Type*} [SeminormedAddCommGroup F] [Module R F]
    [IsBoundedSMul R F] (φ : E →ₗ[R] F) {C : ℝ} (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖) :
    Gauss c E →ₗ[R] Gauss c F :=
  (toAddSubgroupLinearEquiv R).symm.toLinearMap.comp
    ((IsRestrictedFamily.mapLinearMap φ hφ).comp (toAddSubgroupLinearEquiv R).toLinearMap)

@[simp]
theorem mapLinearMap_apply {F : Type*} [SeminormedAddCommGroup F] [Module R F]
    [IsBoundedSMul R F] (φ : E →ₗ[R] F) {C : ℝ} (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖)
    (a : Gauss c E) (t : σ →₀ ℕ) : mapLinearMap φ hφ a t = φ (a t) := by
  simp [mapLinearMap, IsRestrictedFamily.coe_mapLinearMap]

end Module

variable [hc : ∀ i, Fact (0 < c i)]

/-- Restricted families carry the weighted Gauss seminorm. -/
instance instSeminormedAddCommGroup : SeminormedAddCommGroup (Gauss c E) :=
  AddGroupSeminorm.toSeminormedAddCommGroup
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
                (isRestrictedFamily_iff.mp
                  (mem_addSubgroup.mp a.toAddSubgroup.2)).bddAbove_range_of_cofinite t)
              (le_ciSup
                (isRestrictedFamily_iff.mp
                  (mem_addSubgroup.mp b.toAddSubgroup.2)).bddAbove_range_of_cofinite t)
      neg' a := by simp }

/-- The norm is the supremum of the weighted coefficient norms. Restrictedness ensures that
this supremum is bounded. -/
theorem norm_eq_iSup (a : Gauss c E) :
    ‖a‖ = ⨆ t, ‖(a : (σ →₀ ℕ) → E) t‖ * t.prod (c · ^ ·) := (rfl)

/-- A weighted coefficient norm is bounded by the Gauss norm of the family. -/
theorem norm_coeff_mul_prod_le (a : Gauss c E) (t : σ →₀ ℕ) :
    ‖(a : (σ →₀ ℕ) → E) t‖ * t.prod (c · ^ ·) ≤ ‖a‖ :=
  le_ciSup (isRestrictedFamily_iff.mp
    (mem_addSubgroup.mp a.toAddSubgroup.2)).bddAbove_range_of_cofinite t

/-- The Gauss seminorm is a norm when the coefficient seminorm is a norm. -/
instance instNormedAddCommGroup {F : Type*} [NormedAddCommGroup F] :
    NormedAddCommGroup (Gauss c F) :=
  NormedAddCommGroup.ofSeparation fun a ha ↦ by
    apply ext
    intro t
    have h := norm_coeff_mul_prod_le a t
    rw [ha] at h
    simpa using norm_eq_zero.mp (nonpos_of_mul_nonpos_left h (prod_pow_pos t)
      |>.antisymm (norm_nonneg _))

/-- A bound on the Gauss norm is equivalent to the same bound on every weighted coefficient. -/
theorem norm_le_iff {a : Gauss c E} {B : ℝ} :
    ‖a‖ ≤ B ↔ ∀ t, ‖(a : (σ →₀ ℕ) → E) t‖ * t.prod (c · ^ ·) ≤ B :=
  ⟨fun h t ↦ (norm_coeff_mul_prod_le a t).trans h, fun h ↦ ciSup_le h⟩

/-- Coefficient projections have bound the inverse of the monomial weight. -/
theorem norm_coeff_le (a : Gauss c E) (t : σ →₀ ℕ) :
    ‖(a : (σ →₀ ℕ) → E) t‖ ≤ (t.prod (c · ^ ·))⁻¹ * ‖a‖ := by
  rw [inv_mul_eq_div, le_div_iff₀ (prod_pow_pos t)]
  exact norm_coeff_mul_prod_le a t

/-- Coefficients are uniformly continuous for the Gauss norm. -/
theorem uniformContinuous_coeff (t : σ →₀ ℕ) :
    UniformContinuous fun a : Gauss c E ↦
      (a : (σ →₀ ℕ) → E) t :=
  AddMonoidHomClass.uniformContinuous_of_bound
    ((Pi.evalAddMonoidHom _ t).comp
      ((IsRestrictedFamily.addSubgroup E c).subtype.comp toAddSubgroupAddEquiv.toAddMonoidHom))
    _ fun a ↦ norm_coeff_le a t

/-- Complete coefficient groups give complete restricted families for the Gauss norm. -/
instance [CompleteSpace E] : CompleteSpace (Gauss c E) := by
  refine Metric.complete_of_cauchySeq_tendsto fun A hA ↦ ?_
  have hcoeff (t : σ →₀ ℕ) : CauchySeq fun k ↦ (A k : (σ →₀ ℕ) → E) t :=
    (uniformContinuous_coeff t).comp_cauchySeq hA
  obtain ⟨a, hres, hunif⟩ := exists_weighted_coefficient_limit
    (fun k ↦ (A k : (σ →₀ ℕ) → E)) hcoeff
    (fun k ↦ isRestrictedFamily_iff.mp (mem_addSubgroup.mp (A k).toAddSubgroup.2)) (by
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hA ε hε
      refine ⟨N, fun k hk l hl t ↦ ?_⟩
      have h := norm_coeff_mul_prod_le (A k - A l) t
      rw [sub_apply, ofAddSubgroup_apply] at h
      exact h.trans_lt ((dist_eq_norm _ _).symm.trans_lt (hN k hk l hl)))
  refine ⟨ofAddSubgroup ⟨a, mem_addSubgroup.mpr (isRestrictedFamily_iff.mpr hres)⟩,
    Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk ↦ (?_ : _ ≤ ε / 2).trans_lt (half_lt_self hε)⟩
  rw [dist_eq_norm, norm_le_iff]
  intro t
  simpa only [sub_apply, ofAddSubgroup_apply] using hN k hk t

/-- The Gauss norm is ultrametric whenever the coefficient norm is. -/
instance [IsUltrametricDist E] : IsUltrametricDist (Gauss c E) :=
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

/-- A single-coefficient family has its weighted coefficient norm. -/
@[simp]
theorem norm_ofFinsupp_single (t : σ →₀ ℕ) (e : E) :
    ‖ofFinsupp R c (Finsupp.single t e)‖ = ‖e‖ * t.prod (c · ^ ·) := by
  classical
  apply le_antisymm
  · apply norm_le_iff.mpr
    intro s
    by_cases h : s = t
    · subst s
      simp
    · simp [h, mul_nonneg (norm_nonneg e) (prod_pow_pos t).le]
  · simpa using norm_coeff_mul_prod_le (ofFinsupp R c (Finsupp.single t e)) t

/-- Coefficientwise scalar multiplication is bounded for the Gauss norm. -/
instance : IsBoundedSMul R (Gauss c E) :=
  IsBoundedSMul.of_norm_smul_le fun (r : R) (a : Gauss c E) ↦ norm_le_iff.mpr fun t ↦ by
    rw [smul_apply]
    calc
      _ ≤ (‖r‖ * ‖(a : (σ →₀ ℕ) → E) t‖) * t.prod (c · ^ ·) :=
        mul_le_mul_of_nonneg_right (norm_smul_le _ _) (prod_pow_pos t).le
      _ ≤ ‖r‖ * ‖a‖ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (norm_coeff_mul_prod_le a t) (norm_nonneg r)

variable [SeminormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]

/-- A coefficient map bounded by `C` induces a map of restricted families with the same bound. -/
theorem norm_mapLinearMap_le (φ : E →ₗ[R] F) {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖) (a : Gauss c E) :
    ‖mapLinearMap φ hφ a‖ ≤ C * ‖a‖ :=
  norm_le_iff.mpr fun t ↦ by
    rw [mapLinearMap_apply]
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
    NormedSpace K (Gauss c E) where
  norm_smul_le := norm_smul_le

section Convolution

variable [NormedRing R] [IsUltrametricDist R] [IsUltrametricDist E]
  [Module R E] [IsBoundedSMul R E]

/-- The scalar restricted series act on Gauss families by convolution. -/
instance : Module (IsRestricted.subring (R := R) c) (Gauss c E) :=
  toAddSubgroupAddEquiv.module _

omit hc in
@[simp]
theorem isRestrictedSubring_smul_apply (f : IsRestricted.subring (R := R) c)
    (a : Gauss c E) (t : σ →₀ ℕ) :
    (f • a) t = MvPowerSeries.convSMul (f : MvPowerSeries σ R) a.toAddSubgroup t := (rfl)

/-- Convolution by a scalar restricted series satisfies the Gauss norm inequality. -/
theorem norm_isRestrictedSubring_smul_le (f : IsRestricted.subring (R := R) c)
    (a : Gauss c E) : ‖f • a‖ ≤ ‖f‖ * ‖a‖ := by
  classical
  apply norm_le_iff.mpr
  intro t
  rw [isRestrictedSubring_smul_apply, convSMul_apply]
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
    (Gauss c E) :=
  IsBoundedSMul.of_norm_smul_le norm_isRestrictedSubring_smul_le

/-- The existing ring-valued coefficient comparison preserves the Gauss norm. -/
@[simp]
theorem norm_subringLinearEquiv (f : IsRestricted.subring (R := R) c) :
    ‖ofAddSubgroup (IsRestrictedFamily.subringLinearEquiv f)‖ = ‖f‖ := by
  rw [norm_eq_iSup, _root_.MvPowerSeries.norm_eq_gaussNorm, gaussNorm]
  simp only [coe_subringLinearEquiv]

end Convolution

end Gauss
end TauCeti.MvPowerSeries.IsRestrictedFamily
