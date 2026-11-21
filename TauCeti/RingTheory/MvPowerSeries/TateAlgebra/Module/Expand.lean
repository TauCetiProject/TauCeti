/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Expand
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Basic
public import TauCeti.Topology.MetricSpace.Algebra

/-!
# `q`-adic expansion components in coefficient submodules

Let `K` be a ring (normed ultrametric for the multiplication and dual results), `K'` an ultrametric
normed `K`-module or `K`-algebra, `E ⊆ K'` a `K`-submodule, and `r, c : σ → ℝ` polyradii with
`r i > 0` and `r i ^ q = c i` (`q ≠ 0`).

For any restricted power series `z ∈ K'{X / r}` whose coefficients all lie in `E` and any exponent
remainder `ν : σ →₀ ℕ`, extracting the `ν`-th `q`-adic component `coeff (q • α + ν) z` produces a
restricted coefficient family `restrictedExpandComponentFamily hq hr ν E z hz` in
`IsRestrictedFamily.addSubgroup E c`. When `∀ i, ν i < q`, extracting this component is
`K{X / c}`-linear along `restrictedExpand q` composed with `restrictedMap (algebraMap K K')`
(`restrictedExpandComponentFamily_restrictedExpand_mul`). Composing with
`IsRestrictedFamily.toSubringDualOfBound` for a bounded `K`-linear functional `φ : E →ₗ[K] K` with
bound `‖φ e‖ ≤ C * ‖e‖` (`C : ℝ`) produces Gauss-norm-bounded `K{X / c}`-linear projections back to
`K{X / c}` (`norm_toSubringDualOfBound_restrictedExpandComponentFamily_le`), and such projections
separate nonzero series in `K'{X / r}` with coefficients in `E` whenever bounded `K`-linear
functionals on `E` separate points
(`exists_toSubringDualOfBound_restrictedExpandComponentFamily_ne_zero`).

These component-dual projections feed the purely inseparable steps of weak stability
(`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.WeaklyStable`) and the Japanese property
(`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Japanese`).
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

section ComponentFamily

variable {σ K K' : Type*} [Ring K] [NormedRing K'] [IsUltrametricDist K']
  [Module K K'] {c r : σ → ℝ} {q : ℕ}

/-- For `z ∈ K'{X / r}` whose coefficients all lie in a `K`-submodule `E ⊆ K'`, its `ν`-th `q`-adic
expansion component (`q ≠ 0`, `r i ^ q = c i`) packaged as an element of
`IsRestrictedFamily.addSubgroup E c`. -/
noncomputable def restrictedExpandComponentFamily [∀ i, Fact (0 < r i)] (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K')
    (z : IsRestricted.subring (R := K') r)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) :
    IsRestrictedFamily.addSubgroup E c :=
  ⟨fun α ↦ ⟨coeff α (restrictedExpandComponent hq hr ν z : _root_.MvPowerSeries σ K'),
      (coeff_restrictedExpandComponent hq hr ν α z).symm ▸ hz (q • α + ν)⟩,
    IsRestrictedFamily.mem_addSubgroup.mpr <|
      ((isRestrictedFamily_coeff_iff _).mpr (restrictedExpandComponent hq hr ν
          z).property).of_norm_le
        (C := 1) fun _ ↦ (one_mul _).symm.le⟩

@[simp]
theorem coe_restrictedExpandComponentFamily_apply [∀ i, Fact (0 < r i)] (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K')
    (z : IsRestricted.subring (R := K') r)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) (α : σ →₀ ℕ) :
    (((restrictedExpandComponentFamily hq hr ν E z hz : (σ →₀ ℕ) → E) α : E) : K') =
      coeff (q • α + ν) (z : _root_.MvPowerSeries σ K') :=
  coeff_restrictedExpandComponent hq hr ν α z

/-- `restrictedExpandComponentFamily` depends only on the restricted series `z`, not on the
coefficient-membership proof. -/
theorem restrictedExpandComponentFamily_congr [∀ i, Fact (0 < r i)] (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K')
    {z₁ z₂ : IsRestricted.subring (R := K') r} (h : z₁ = z₂)
    {hz₁ : ∀ α, coeff α (z₁ : _root_.MvPowerSeries σ K') ∈ E}
    {hz₂ : ∀ α, coeff α (z₂ : _root_.MvPowerSeries σ K') ∈ E} :
    restrictedExpandComponentFamily hq hr ν E z₁ hz₁ =
      restrictedExpandComponentFamily hq hr ν E z₂ hz₂ := by
  subst h; rfl

@[simp]
theorem restrictedExpandComponentFamily_zero [∀ i, Fact (0 < r i)] (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K')
    {hz : ∀ α, coeff α ((0 : IsRestricted.subring (R := K') r) : _root_.MvPowerSeries σ K') ∈ E} :
    restrictedExpandComponentFamily hq hr ν E 0 hz = 0 :=
  IsRestrictedFamily.ext fun _ ↦ Subtype.ext (by simp)

theorem restrictedExpandComponentFamily_add [∀ i, Fact (0 < r i)] (hq : q ≠ 0)
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
theorem restrictedExpandComponentFamily_sum {ι : Type*} [∀ i, Fact (0 < r i)] (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K') (s : Finset ι)
    (z : ι → IsRestricted.subring (R := K') r)
    (hz : ∀ i, ∀ α, coeff α (z i : _root_.MvPowerSeries σ K') ∈ E)
    {hz_sum : ∀ α, coeff α ((∑ i ∈ s, z i : IsRestricted.subring (R := K') r) :
      _root_.MvPowerSeries σ K') ∈ E} :
    restrictedExpandComponentFamily hq hr ν E (∑ i ∈ s, z i) hz_sum =
      ∑ i ∈ s, restrictedExpandComponentFamily hq hr ν E (z i) (hz i) :=
  IsRestrictedFamily.ext fun _ ↦ Subtype.ext (by simp [AddSubmonoidClass.coe_finsetSum])

/-- Every nonzero restricted series `z ∈ K'{X / r}` with coefficients in `E` has a `q`-adic
component `restrictedExpandComponentFamily hq hr ν E z hz` (`∀ i, ν i < q`) with at least one
nonzero coefficient in `E`. -/
theorem exists_coeff_restrictedExpandComponentFamily_ne_zero [∀ i, Fact (0 < r i)] (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (E : Submodule K K')
    {z : IsRestricted.subring (R := K') r} (hz_ne : z ≠ 0)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) :
    ∃ (ν : σ →₀ ℕ) (_ : ∀ i, ν i < q) (μ : σ →₀ ℕ),
      ((restrictedExpandComponentFamily hq hr ν E z hz : (σ →₀ ℕ) → E) μ) ≠ 0 := by
  classical
  have : ∀ i, Fact (0 < c i) := fun i ↦ ⟨hr i ▸ pow_pos Fact.out q⟩
  obtain ⟨ν, hν, hν_norm⟩ := exists_norm_restrictedExpandComponent_mul_prod_eq hq hr z
  have hcomp_ne : restrictedExpandComponent hq hr ν z ≠ 0 := fun h0 ↦
    hz_ne (norm_eq_zero.mp (by simpa [h0] using hν_norm.symm))
  have ⟨μ, hμ_ne⟩ :
      ∃ μ, coeff μ (restrictedExpandComponent hq hr ν z : _root_.MvPowerSeries σ K') ≠ 0 := by
    by_contra! hall
    exact hcomp_ne (Subtype.ext (MvPowerSeries.ext fun μ ↦ by simpa using hall μ))
  exact ⟨ν, hν, μ, Subtype.coe_ne_coe.mp (by simpa [coeff_restrictedExpandComponent] using hμ_ne)⟩

end ComponentFamily

section AlgebraMul

variable {σ K K' : Type*} [NormedCommRing K] [IsUltrametricDist K]
  [NormedCommRing K'] [IsUltrametricDist K'] [Algebra K K'] {c r : σ → ℝ} {q : ℕ}

/-- Multiplying a series `z ∈ K'{X / r}` with coefficients in a `K`-submodule `E ⊆ K'` by the
`q`-adic expansion of `t ∈ K{X / c}` preserves coefficient membership in `E`. -/
theorem coeff_restrictedExpand_restrictedMap_mul_mem (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) {C : ℝ} (hφ : ∀ a : K, ‖algebraMap K K' a‖ ≤ C * ‖a‖)
    (E : Submodule K K') (t : IsRestricted.subring (R := K) c)
    {z : IsRestricted.subring (R := K') r}
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) (α : σ →₀ ℕ) :
    coeff α ((restrictedExpand q hq hr (restrictedMap (algebraMap K K') hφ t) * z :
      IsRestricted.subring (R := K') r) : _root_.MvPowerSeries σ K') ∈ E := by
  classical
  rw [Subring.coe_mul, coeff_mul]
  refine E.sum_mem fun pq _ ↦ ?_
  rw [coe_restrictedExpand, coe_restrictedMap, ← _root_.MvPowerSeries.map_expand, coeff_map,
    ← Algebra.smul_def]
  exact E.smul_mem _ (hz pq.2)

/-- When `∀ i, ν i < q`, extracting the `ν`-th `q`-adic component in `E` is `K{X / c}`-linear
with respect to multiplication by expanded series `restrictedExpand q ... (restrictedMap ... t)`. -/
theorem restrictedExpandComponentFamily_restrictedExpand_mul [IsBoundedSMul K K']
    [∀ i, Fact (0 < r i)] (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) {ν : σ →₀ ℕ} (hν : ∀ i, ν i < q)
    {C : ℝ} (hφ : ∀ a : K, ‖algebraMap K K' a‖ ≤ C * ‖a‖) (E : Submodule K K')
    (t : IsRestricted.subring (R := K) c) (z : IsRestricted.subring (R := K') r)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E)
    {hz_mul : ∀ α, coeff α ((restrictedExpand q hq hr
        (restrictedMap (algebraMap K K') hφ t) * z :
      IsRestricted.subring (R := K') r) : _root_.MvPowerSeries σ K') ∈ E} :
    restrictedExpandComponentFamily hq hr ν E
        (restrictedExpand q hq hr (restrictedMap (algebraMap K K') hφ t) * z) hz_mul =
      t • restrictedExpandComponentFamily hq hr ν E z hz := by
  classical
  refine IsRestrictedFamily.ext fun α ↦ Subtype.ext ?_
  have hcomp := congrArg (coeff α ∘ Subtype.val)
    (restrictedExpandComponent_restrictedExpand_mul hq hr hν
      (restrictedMap (algebraMap K K') hφ t) z)
  simp only [Function.comp_apply, coeff_restrictedExpandComponent, Subring.coe_mul, coeff_mul,
    coe_restrictedMap, coeff_map] at hcomp
  rw [coe_restrictedExpandComponentFamily_apply, Subring.coe_mul, coeff_mul, hcomp,
    IsRestrictedFamily.coe_isRestrictedSubring_smul, convSMul_apply, Submodule.coe_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by
    rw [SetLike.val_smul, Algebra.smul_def, coe_restrictedExpandComponentFamily_apply]

end AlgebraMul

section Dual

variable {σ K K' : Type*} [NormedRing K] [IsUltrametricDist K]
  [NormedRing K'] [IsUltrametricDist K'] [Module K K'] [IsBoundedSMul K K'] {c r : σ → ℝ} {q : ℕ}

/-- Gauss-norm bound on
`toSubringDualOfBound φ hφ (restrictedExpandComponentFamily hq hr ν E z hz)`. -/
theorem norm_toSubringDualOfBound_restrictedExpandComponentFamily_le
    [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)] (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i)
    (ν : σ →₀ ℕ) (E : Submodule K K') (φ : E →ₗ[K] K) {C : ℝ}
    (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖) (z : IsRestricted.subring (R := K') r)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) :
    ‖IsRestrictedFamily.toSubringDualOfBound φ hφ
        (restrictedExpandComponentFamily hq hr ν E z hz)‖ ≤
      (C / ν.prod (r · ^ ·)) * ‖z‖ := by
  rcases le_or_gt 0 C with hC | hC
  · calc ‖IsRestrictedFamily.toSubringDualOfBound φ hφ
            (restrictedExpandComponentFamily hq hr ν E z hz)‖
        ≤ C * ‖restrictedExpandComponent hq hr ν z‖ := norm_le_mul_of_norm_coeff_le fun α ↦ by
          rw [IsRestrictedFamily.coeff_coe_toSubringDualOfBound, coeff_restrictedExpandComponent,
            ← coe_restrictedExpandComponentFamily_apply hq hr ν E z hz α,
            ← AddSubgroupClass.coe_norm]
          exact hφ _
      _ ≤ C * (‖z‖ / ν.prod (r · ^ ·)) := mul_le_mul_of_nonneg_left
          ((le_div_iff₀ (prod_pow_pos ν)).mpr
            (norm_restrictedExpandComponent_mul_prod_le hq hr ν z)) hC
      _ = (C / ν.prod (r · ^ ·)) * ‖z‖ := by ring
  · have hz0 : z = 0 := Subtype.ext <| _root_.MvPowerSeries.ext fun α ↦ by
      by_contra hα
      have hpos : 0 < ‖(⟨coeff α (z : _root_.MvPowerSeries σ K'), hz α⟩ : E)‖ :=
        norm_pos_iff.mpr (Subtype.coe_ne_coe.mp hα)
      linarith [norm_nonneg (φ ⟨coeff α (z : _root_.MvPowerSeries σ K'), hz α⟩),
        hφ ⟨coeff α (z : _root_.MvPowerSeries σ K'), hz α⟩, mul_neg_of_neg_of_pos hC hpos]
    simp [hz0]

/-- When bounded `K`-linear functionals separate points of `E`, any nonzero restricted series
`z ∈ K'{X / r}` whose coefficients lie in `E` has a nonzero projection
`toSubringDualOfBound φ hφ (restrictedExpandComponentFamily hq hr ν E z hz)` for some remainder `ν`
(`∀ i, ν i < q`) and some bounded `φ : E →ₗ[K] K`. -/
theorem exists_toSubringDualOfBound_restrictedExpandComponentFamily_ne_zero
    [∀ i, Fact (0 < r i)] (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) (E : Submodule K K')
    (hsep : ∀ x : E, x ≠ 0 → ∃ (φ : E →ₗ[K] K) (C : ℝ), (∀ e, ‖φ e‖ ≤ C * ‖e‖) ∧ φ x ≠ 0)
    {z : IsRestricted.subring (R := K') r} (hz_ne : z ≠ 0)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) :
    ∃ (ν : σ →₀ ℕ) (_ : ∀ i, ν i < q) (φ : E →ₗ[K] K) (C : ℝ) (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖),
      IsRestrictedFamily.toSubringDualOfBound φ hφ
        (restrictedExpandComponentFamily hq hr ν E z hz) ≠ 0 := by
  obtain ⟨ν, hν, μ, hμE_ne⟩ :=
    exists_coeff_restrictedExpandComponentFamily_ne_zero hq hr E hz_ne hz
  obtain ⟨φ, C, hφ, hf_ne⟩ := hsep _ hμE_ne
  exact ⟨ν, hν, φ, C, hφ, fun h0 ↦ hf_ne <| by
    simpa [h0] using (IsRestrictedFamily.coeff_coe_toSubringDualOfBound φ hφ
      (restrictedExpandComponentFamily hq hr ν E z hz) μ).symm⟩

end Dual

end TauCeti.MvPowerSeries
