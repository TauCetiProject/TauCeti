/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Expand
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Basic

/-!
# `q`-adic expansion components in coefficient submodules

Let `K` be an ultrametric normed field, `K'` an ultrametric normed commutative `K`-algebra,
`E ⊆ K'` a `K`-submodule, and `r, c : σ → ℝ` polyradii with `r i > 0` and `r i ^ q = c i`
(`q ≠ 0`).

For any restricted power series `z ∈ K'{X / r}` whose coefficients all lie in `E` and any exponent
remainder `ν : σ →₀ ℕ`, extracting the `ν`-th `q`-adic component `coeff (q • α + ν) z` produces a
restricted coefficient family `restrictedExpandComponentFamily hq hr ν E z hz` in
`IsRestrictedFamily.addSubgroup E c`. When `∀ i, ν i < q`, extracting this component is
`K{X / c}`-linear along `restrictedExpand q` composed with `restrictedMap (algebraMap K K')`
(`restrictedExpandComponentFamily_restrictedExpand_mul`). When `c` is positive and `0 ≤ C`,
composing with `IsRestrictedFamily.toSubringDualOfBound` produces Gauss-norm-bounded
`K{X / c}`-linear projections back to `K{X / c}`
(`norm_toSubringDualOfBound_restrictedExpandComponentFamily_le`), and for any `c`, such projections
separate nonzero series in `K'{X / r}` with coefficients in `E` whenever bounded `K`-linear
functionals on `E` separate points
(`exists_toSubringDualOfBound_restrictedExpandComponentFamily_ne_zero`).
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {σ K K' : Type*} [NormedField K] [NormedCommRing K'] [IsUltrametricDist K']
  [NormedAlgebra K K']

/-- For `z ∈ K'{X / r}` whose coefficients all lie in a `K`-submodule `E ⊆ K'`, its `ν`-th `q`-adic
expansion component (`q ≠ 0`, `r i ^ q = c i`) packaged as an element of
`IsRestrictedFamily.addSubgroup E c`. -/
noncomputable def restrictedExpandComponentFamily
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K')
    (z : IsRestricted.subring (R := K') r)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) :
    IsRestrictedFamily.addSubgroup E c :=
  ⟨fun α ↦ ⟨coeff α (restrictedExpandComponent hq hr ν z : _root_.MvPowerSeries σ K'), by
      rw [coeff_restrictedExpandComponent]; exact hz (q • α + ν)⟩,
    IsRestrictedFamily.mem_addSubgroup.mpr <|
      ((isRestrictedFamily_coeff_iff _).mpr (restrictedExpandComponent hq hr ν z).2).of_norm_le
        (C := 1) fun _ ↦ (one_mul _).symm.le⟩

@[simp]
theorem coe_restrictedExpandComponentFamily_apply
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K')
    (z : IsRestricted.subring (R := K') r)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) (α : σ →₀ ℕ) :
    (((restrictedExpandComponentFamily hq hr ν E z hz : (σ →₀ ℕ) → E) α : E) : K') =
      coeff (q • α + ν) (z : _root_.MvPowerSeries σ K') :=
  coeff_restrictedExpandComponent hq hr ν α z

theorem coe_coeff_restrictedExpandComponentFamily
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K')
    (z : IsRestricted.subring (R := K') r)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) (α : σ →₀ ℕ) :
    ((IsRestrictedFamily.coeff K α (restrictedExpandComponentFamily hq hr ν E z hz) : E) : K') =
      coeff α (restrictedExpandComponent hq hr ν z : _root_.MvPowerSeries σ K') := by
  simp

/-- `restrictedExpandComponentFamily` depends only on the restricted series `z`, not on the
coefficient-membership proof. -/
theorem restrictedExpandComponentFamily_congr
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K')
    {z₁ z₂ : IsRestricted.subring (R := K') r} (h : z₁ = z₂)
    {hz₁ : ∀ α, coeff α (z₁ : _root_.MvPowerSeries σ K') ∈ E}
    {hz₂ : ∀ α, coeff α (z₂ : _root_.MvPowerSeries σ K') ∈ E} :
    restrictedExpandComponentFamily hq hr ν E z₁ hz₁ =
      restrictedExpandComponentFamily hq hr ν E z₂ hz₂ := by
  subst h; rfl

@[simp]
theorem restrictedExpandComponentFamily_zero
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K')
    {hz : ∀ α, coeff α ((0 : IsRestricted.subring (R := K') r) : _root_.MvPowerSeries σ K') ∈ E} :
    restrictedExpandComponentFamily hq hr ν E 0 hz = 0 :=
  IsRestrictedFamily.ext fun _ ↦ Subtype.ext (by simp)

theorem restrictedExpandComponentFamily_add
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K')
    (z₁ z₂ : IsRestricted.subring (R := K') r)
    (hz₁ : ∀ α, coeff α (z₁ : _root_.MvPowerSeries σ K') ∈ E)
    (hz₂ : ∀ α, coeff α (z₂ : _root_.MvPowerSeries σ K') ∈ E)
    {hz₁₂ : ∀ α, coeff α ((z₁ + z₂ : IsRestricted.subring (R := K') r) :
      _root_.MvPowerSeries σ K') ∈ E} :
    restrictedExpandComponentFamily hq hr ν E (z₁ + z₂) hz₁₂ =
      restrictedExpandComponentFamily hq hr ν E z₁ hz₁ +
        restrictedExpandComponentFamily hq hr ν E z₂ hz₂ :=
  IsRestrictedFamily.ext fun _ ↦ Subtype.ext (by simp)

/-- Extracting the `ν`-th `q`-adic component commutes with finite sums. -/
theorem restrictedExpandComponentFamily_sum
    {ι : Type*} {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K') (s : Finset ι)
    (z : ι → IsRestricted.subring (R := K') r)
    (hz : ∀ i, ∀ α, coeff α (z i : _root_.MvPowerSeries σ K') ∈ E)
    {hz_sum : ∀ α, coeff α ((∑ i ∈ s, z i : IsRestricted.subring (R := K') r) :
      _root_.MvPowerSeries σ K') ∈ E} :
    restrictedExpandComponentFamily hq hr ν E (∑ i ∈ s, z i) hz_sum =
      ∑ i ∈ s, restrictedExpandComponentFamily hq hr ν E (z i) (hz i) := by
  refine IsRestrictedFamily.ext fun α ↦ Subtype.ext ?_
  simp [AddSubmonoidClass.coe_finsetSum]

/-- Multiplying a series `z ∈ K'{X / r}` with coefficients in a `K`-submodule `E ⊆ K'` by the
`q`-adic expansion of `t ∈ K{X / c}` preserves coefficient membership in `E`. -/
theorem coeff_restrictedExpand_restrictedMap_mul_mem [IsUltrametricDist K]
    {c r : σ → ℝ} {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (h_iso : ∀ a : K, ‖algebraMap K K' a‖ ≤ 1 * ‖a‖)
    (E : Submodule K K') (t : IsRestricted.subring (R := K) c)
    {z : IsRestricted.subring (R := K') r}
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) (α : σ →₀ ℕ) :
    coeff α ((restrictedExpand q hq hr (restrictedMap (algebraMap K K') h_iso t) * z :
      IsRestricted.subring (R := K') r) : _root_.MvPowerSeries σ K') ∈ E := by
  classical
  rw [Subring.coe_mul, coeff_mul]
  refine E.sum_mem fun pq _ ↦ ?_
  rw [coe_restrictedExpand, coe_restrictedMap, ← _root_.MvPowerSeries.map_expand, coeff_map,
    ← Algebra.smul_def]
  exact E.smul_mem _ (hz pq.2)

/-- When `∀ i, ν i < q`, extracting the `ν`-th `q`-adic component in `E` is `K{X / c}`-linear
with respect to multiplication by expanded series `restrictedExpand q ... (restrictedMap ... t)`. -/
theorem restrictedExpandComponentFamily_restrictedExpand_mul [IsUltrametricDist K]
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) {ν : σ →₀ ℕ} (hν : ∀ i, ν i < q)
    (h_iso : ∀ a : K, ‖algebraMap K K' a‖ ≤ 1 * ‖a‖) (E : Submodule K K')
    (t : IsRestricted.subring (R := K) c) (z : IsRestricted.subring (R := K') r)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E)
    {hz_mul : ∀ α, coeff α ((restrictedExpand q hq hr
        (restrictedMap (algebraMap K K') h_iso t) * z :
      IsRestricted.subring (R := K') r) : _root_.MvPowerSeries σ K') ∈ E} :
    restrictedExpandComponentFamily hq hr ν E
        (restrictedExpand q hq hr (restrictedMap (algebraMap K K') h_iso t) * z) hz_mul =
      t • restrictedExpandComponentFamily hq hr ν E z hz := by
  classical
  refine IsRestrictedFamily.ext fun α ↦ Subtype.ext ?_
  have hcomp := congrArg (coeff α ∘ Subtype.val)
    (restrictedExpandComponent_restrictedExpand_mul hq hr hν
      (restrictedMap (algebraMap K K') h_iso t) z)
  simp only [Function.comp_apply, coeff_restrictedExpandComponent, Subring.coe_mul, coeff_mul,
    coe_restrictedMap, coeff_map] at hcomp
  rw [coe_restrictedExpandComponentFamily_apply, Subring.coe_mul, coeff_mul, hcomp,
    IsRestrictedFamily.coe_isRestrictedSubring_smul, convSMul_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun pq _ ↦ ?_
  rw [SetLike.val_smul, Algebra.smul_def, coe_restrictedExpandComponentFamily_apply]

/-- Every nonzero restricted series `z ∈ K'{X / r}` with coefficients in `E` has a `q`-adic
component `restrictedExpandComponentFamily hq hr ν E z hz` (`∀ i, ν i < q`) with at least one
nonzero coefficient in `E`. -/
theorem exists_coeff_restrictedExpandComponentFamily_ne_zero
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (E : Submodule K K')
    {z : IsRestricted.subring (R := K') r} (hz_ne : z ≠ 0)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) :
    ∃ (ν : σ →₀ ℕ) (_ : ∀ i, ν i < q) (μ : σ →₀ ℕ),
      ((restrictedExpandComponentFamily hq hr ν E z hz : (σ →₀ ℕ) → E) μ) ≠ 0 := by
  classical
  have : ∀ i, Fact (0 < c i) := fun i ↦ ⟨hr i ▸ pow_pos Fact.out q⟩
  obtain ⟨ν, hν, hν_norm⟩ := exists_norm_restrictedExpandComponent_mul_prod_eq hq hr z
  have hcomp_ne : restrictedExpandComponent hq hr ν z ≠ 0 := fun h0 ↦ by
    rw [h0, norm_zero, zero_mul] at hν_norm
    exact hz_ne (norm_eq_zero.mp hν_norm.symm)
  obtain ⟨μ, hμ_ne⟩ :
      ∃ μ, coeff μ (restrictedExpandComponent hq hr ν z : _root_.MvPowerSeries σ K') ≠ 0 := by
    by_contra! hall
    exact hcomp_ne (Subtype.ext (MvPowerSeries.ext fun μ ↦ by
      rw [ZeroMemClass.coe_zero, map_zero]; exact hall μ))
  refine ⟨ν, hν, μ, Subtype.coe_ne_coe.mp ?_⟩
  simpa [coeff_restrictedExpandComponent] using hμ_ne

/-- Gauss-norm bound on
`toSubringDualOfBound φ hφ (restrictedExpandComponentFamily hq hr ν E z hz)`. -/
theorem norm_toSubringDualOfBound_restrictedExpandComponentFamily_le [IsUltrametricDist K]
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K')
    (φ : E →ₗ[K] K) {C : ℝ} (hC : 0 ≤ C) (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖)
    (z : IsRestricted.subring (R := K') r)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) :
    ‖IsRestrictedFamily.toSubringDualOfBound φ hφ
        (restrictedExpandComponentFamily hq hr ν E z hz)‖ ≤
      (C / ν.prod (r · ^ ·)) * ‖z‖ := by
  calc ‖IsRestrictedFamily.toSubringDualOfBound φ hφ
          (restrictedExpandComponentFamily hq hr ν E z hz)‖
      ≤ C * ‖restrictedExpandComponent hq hr ν z‖ := by
        refine norm_le_mul_of_norm_coeff_le fun α ↦ ?_
        rw [IsRestrictedFamily.coeff_coe_toSubringDualOfBound, coeff_restrictedExpandComponent,
          ← coe_restrictedExpandComponentFamily_apply hq hr ν E z hz α,
          ← AddSubgroupClass.coe_norm]
        exact hφ _
    _ ≤ C * (‖z‖ / ν.prod (r · ^ ·)) :=
        mul_le_mul_of_nonneg_left ((le_div_iff₀ (prod_pow_pos ν)).mpr
          (norm_restrictedExpandComponent_mul_prod_le hq hr ν z)) hC
    _ = (C / ν.prod (r · ^ ·)) * ‖z‖ := by ring

/-- When bounded `K`-linear functionals separate points of `E`, any nonzero restricted series
`z ∈ K'{X / r}` whose coefficients lie in `E` has a nonzero projection
`toSubringDualOfBound φ hφ (restrictedExpandComponentFamily hq hr ν E z hz)` for some remainder `ν`
(`∀ i, ν i < q`) and some bounded `φ : E →ₗ[K] K`. -/
theorem exists_toSubringDualOfBound_restrictedExpandComponentFamily_ne_zero [IsUltrametricDist K]
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (E : Submodule K K')
    (hsep : ∀ x : E, x ≠ 0 → ∃ (φ : E →ₗ[K] K) (C : ℝ), (∀ e, ‖φ e‖ ≤ C * ‖e‖) ∧ φ x ≠ 0)
    {z : IsRestricted.subring (R := K') r} (hz_ne : z ≠ 0)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) :
    ∃ (ν : σ →₀ ℕ) (_ : ∀ i, ν i < q) (φ : E →ₗ[K] K) (C : ℝ) (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖),
      IsRestrictedFamily.toSubringDualOfBound φ hφ
        (restrictedExpandComponentFamily hq hr ν E z hz) ≠ 0 := by
  obtain ⟨ν, hν, μ, hμE_ne⟩ :=
    exists_coeff_restrictedExpandComponentFamily_ne_zero hq hr E hz_ne hz
  obtain ⟨φ, C, hφ, hf_ne⟩ := hsep _ hμE_ne
  refine ⟨ν, hν, φ, C, hφ, fun h0 ↦ ?_⟩
  have hcoeff0 : coeff μ (IsRestrictedFamily.toSubringDualOfBound φ hφ
      (restrictedExpandComponentFamily hq hr ν E z hz) : _root_.MvPowerSeries σ K) = 0 := by
    rw [h0, ZeroMemClass.coe_zero, map_zero]
  rw [IsRestrictedFamily.coeff_coe_toSubringDualOfBound] at hcoeff0
  exact hf_ne hcoeff0

end TauCeti.MvPowerSeries
