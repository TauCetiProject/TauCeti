/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Analysis.Normed.Field.FrobeniusRoot
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Expand
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Basic

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Frobenius roots of restricted power series and component-dual projections

Let `K` be an ultrametric normed field of exponential characteristic `p`, `e : ℕ`, `c : σ → ℝ` a
positive polyradius, and `r i = c i ^ (p ^ e)⁻¹` so that `r i ^ p ^ e = c i`.

1. Applying `FrobeniusRoot.root K p e` and `FrobeniusRoot.val K p e` coefficientwise identifies the
   restricted-series rings `K{X / c}` and `(FrobeniusRoot K p e){X / r}` as rings
   (`TauCeti.MvPowerSeries.frobeniusRootRestrictedEquiv`).
2. Combining coefficientwise scalar extension along `algebraMap K (FrobeniusRoot K p e)` with
   `restrictedExpand (p ^ e)` gives an isometric ring homomorphism
   `TauCeti.MvPowerSeries.frobeniusRootRestrictedHom : K{X / c} →+* (FrobeniusRoot K p e){X / r}`
   whose image of `f` is the `p ^ e`-th power of `frobeniusRootRestrictedEquiv p e hr f`.
3. Given an ultrametric normed `K`-algebra `K'`, a `K`-submodule `E ⊆ K'`, an exponent remainder
   `ν : σ →₀ ℕ` (`∀ i, ν i < q`), and a bounded `K`-linear functional `φ : E →ₗ[K] K` (or a
   continuous functional `f_dual : StrongDual K E` when `K` is nontrivially normed), extracting the
   `ν`-th `q`-adic component into `IsRestrictedFamily.addSubgroup E c`
   (`TauCeti.MvPowerSeries.restrictedExpandComponentFamily`) and applying `φ` coefficientwise
   (`TauCeti.MvPowerSeries.IsRestrictedFamily.toSubringDualOfBound`,
   `TauCeti.MvPowerSeries.IsRestrictedFamily.toSubringDual`) produces `K{X / c}`-linear maps back to
   `K{X / c}` that are bounded in Gauss norm and jointly separate nonzero series in `K'{X / r}`
   whose coefficients lie in `E`.

Both characteristic-free weak stability of `GaussFractionField` and the Japanese property of
restricted power series factor their positive-characteristic inseparable step through these maps.

## Main definitions and results

* `TauCeti.MvPowerSeries.frobeniusRootRestrictedEquiv`: coefficientwise Frobenius-root ring
  isomorphism `K{X / c} ≃+* (FrobeniusRoot K p e){X / r}`.
* `TauCeti.MvPowerSeries.frobeniusRootRestrictedHom`: isometric ring homomorphism
  `K{X / c} →+* (FrobeniusRoot K p e){X / r}` satisfying `frobeniusRootRestrictedEquiv_pow`.
* `TauCeti.MvPowerSeries.restrictedExpandComponentFamily`: `ν`-th `q`-adic component of a restricted
  series with coefficients in `E`, packaged in `IsRestrictedFamily.addSubgroup E c`.
* `TauCeti.MvPowerSeries.IsRestrictedFamily.toSubringDualOfBound` and
  `TauCeti.MvPowerSeries.IsRestrictedFamily.toSubringDual`: `K{X / c}`-linear functionals induced by
  bounded or continuous `K`-linear functionals on `E`, together with their separation lemmas
  `exists_toSubringDualOfBound_restrictedExpandComponentFamily_ne_zero` and
  `exists_toSubringDual_restrictedExpandComponentFamily_ne_zero`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§3.5.3 and 5.3.1.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries Filter
open scoped Topology

section FrobeniusRoot

variable {σ : Type*} {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Applying `FrobeniusRoot.root K p e` coefficientwise identifies `K{X / c}` with
`(FrobeniusRoot K p e){X / r}` as a ring when `r i = c i ^ (p ^ e)⁻¹`. -/
noncomputable def frobeniusRootRestrictedEquiv (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹)) :
    IsRestricted.subring (R := K) c ≃+* IsRestricted.subring (R := FrobeniusRoot K p e) r where
  toFun f :=
    ⟨MvPowerSeries.map (FrobeniusRoot.root K p e) (f : _root_.MvPowerSeries σ K), by
      let qR : ℝ := ((p ^ e : ℕ) : ℝ)
      have hq_inv : 0 < qR⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr (pow_pos (expChar_pos K p) e))
      have hlim := (Real.continuousAt_rpow_const 0 qR⁻¹ (Or.inr hq_inv.le)).tendsto.comp f.2
      rw [Real.zero_rpow hq_inv.ne'] at hlim
      refine hlim.congr fun μ ↦ ?_
      dsimp only [Function.comp_apply, qR]
      rw [Real.mul_rpow (norm_nonneg _) (prod_pow_pos μ).le, coeff_map, FrobeniusRoot.norm_root,
        μ.prod_pow_rpow (fun i _ ↦ (Fact.out : 0 < c i).le)]
      congr 1
      exact Finset.prod_congr rfl fun i _ ↦ by simp only [hr]⟩
  invFun g :=
    ⟨MvPowerSeries.map (FrobeniusRoot.val K p e) (g : _root_.MvPowerSeries σ (FrobeniusRoot K p e)),
      by
      let qR : ℝ := ((p ^ e : ℕ) : ℝ)
      have hq : 0 < qR := Nat.cast_pos.mpr (pow_pos (expChar_pos K p) e)
      have hr_nonneg (i : σ) : 0 ≤ r i := by
        rw [hr]; exact Real.rpow_nonneg (Fact.out : 0 < c i).le _
      have hlim := (Real.continuousAt_rpow_const 0 qR (Or.inr hq.le)).tendsto.comp g.2
      rw [Real.zero_rpow hq.ne'] at hlim
      refine hlim.congr fun μ ↦ ?_
      dsimp only [Function.comp_apply, qR]
      have hval_norm (x : FrobeniusRoot K p e) : ‖x‖ ^ qR = ‖FrobeniusRoot.val K p e x‖ := by
        rw [FrobeniusRoot.norm_def, ← Real.rpow_mul (norm_nonneg _), inv_mul_cancel₀ hq.ne',
          Real.rpow_one]
      have hprod_nonneg : 0 ≤ μ.prod (r · ^ ·) :=
        Finset.prod_nonneg fun i _ ↦ pow_nonneg (hr_nonneg i) _
      rw [Real.mul_rpow (norm_nonneg _) hprod_nonneg, coeff_map, hval_norm,
        μ.prod_pow_rpow (fun i _ ↦ hr_nonneg i)]
      congr 1
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      dsimp only [qR]
      rw [hr, ← Real.rpow_mul (Fact.out : 0 < c i).le, inv_mul_cancel₀ hq.ne', Real.rpow_one]⟩
  left_inv f := Subtype.ext <| by
    dsimp only
    rw [MvPowerSeries.map_map]
    have hcomp : (FrobeniusRoot.val K p e).comp (FrobeniusRoot.root K p e) = RingHom.id K :=
      RingHom.ext FrobeniusRoot.val_root
    rw [hcomp, MvPowerSeries.map_id, RingHom.id_apply]
  right_inv g := Subtype.ext <| by
    dsimp only
    rw [MvPowerSeries.map_map]
    have hcomp : (FrobeniusRoot.root K p e).comp (FrobeniusRoot.val K p e) = RingHom.id _ :=
      RingHom.ext FrobeniusRoot.root_val
    rw [hcomp, MvPowerSeries.map_id, RingHom.id_apply]
  map_mul' f g := Subtype.ext (map_mul (MvPowerSeries.map (FrobeniusRoot.root K p e)) f.1 g.1)
  map_add' f g := Subtype.ext (map_add (MvPowerSeries.map (FrobeniusRoot.root K p e)) f.1 g.1)

@[simp]
theorem coe_frobeniusRootRestrictedEquiv (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (f : IsRestricted.subring (R := K) c) :
    (frobeniusRootRestrictedEquiv p e hr f : _root_.MvPowerSeries σ (FrobeniusRoot K p e)) =
      MvPowerSeries.map (FrobeniusRoot.root K p e) (f : _root_.MvPowerSeries σ K) :=
  (rfl)

@[simp]
theorem coe_frobeniusRootRestrictedEquiv_symm (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (g : IsRestricted.subring (R := FrobeniusRoot K p e) r) :
    ((frobeniusRootRestrictedEquiv p e hr).symm g : _root_.MvPowerSeries σ K) =
      MvPowerSeries.map (FrobeniusRoot.val K p e)
        (g : _root_.MvPowerSeries σ (FrobeniusRoot K p e)) :=
  (rfl)

/-- The isometric ring homomorphism `K{X / c} →+* (FrobeniusRoot K p e){X / r}`
(`r i ^ p ^ e = c i`) obtained by composing coefficientwise `e`-fold Frobenius scalar extension
with `p ^ e`-adic variable expansion. -/
noncomputable def frobeniusRootRestrictedHom (p : ℕ) [ExpChar K p] (e : ℕ) {c r : σ → ℝ}
    (hr_pow : ∀ i, r i ^ p ^ e = c i) :
    IsRestricted.subring (R := K) c →+* IsRestricted.subring (R := FrobeniusRoot K p e) r :=
  (restrictedExpand (p ^ e) (pow_pos (expChar_pos K p) e).ne' hr_pow).toRingHom.comp
    (restrictedMap (algebraMap K (FrobeniusRoot K p e)) (C := 1) fun a ↦ by
      rw [one_mul, FrobeniusRoot.norm_algebraMap])

theorem frobeniusRootRestrictedHom_apply (p : ℕ) [ExpChar K p] (e : ℕ) {c r : σ → ℝ}
    (hr_pow : ∀ i, r i ^ p ^ e = c i) (f : IsRestricted.subring (R := K) c) :
    frobeniusRootRestrictedHom p e hr_pow f =
      restrictedExpand (p ^ e) (pow_pos (expChar_pos K p) e).ne' hr_pow
        (restrictedMap (algebraMap K (FrobeniusRoot K p e)) (C := 1)
          (fun a ↦ by rw [one_mul, FrobeniusRoot.norm_algebraMap]) f) :=
  (rfl)

theorem coe_frobeniusRootRestrictedHom (p : ℕ) [ExpChar K p] (e : ℕ) {c r : σ → ℝ}
    (hr_pow : ∀ i, r i ^ p ^ e = c i) (f : IsRestricted.subring (R := K) c) :
    (frobeniusRootRestrictedHom p e hr_pow f : _root_.MvPowerSeries σ (FrobeniusRoot K p e)) =
      MvPowerSeries.map (algebraMap K (FrobeniusRoot K p e))
        (MvPowerSeries.expand (p ^ e) (pow_pos (expChar_pos K p) e).ne'
          (f : _root_.MvPowerSeries σ K)) := by
  rw [frobeniusRootRestrictedHom_apply, coe_restrictedExpand, coe_restrictedMap,
    MvPowerSeries.map_expand]

@[simp]
theorem norm_frobeniusRootRestrictedHom (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    (hr_pow : ∀ i, r i ^ p ^ e = c i) (f : IsRestricted.subring (R := K) c) :
    ‖frobeniusRootRestrictedHom p e hr_pow f‖ = ‖f‖ := by
  rw [frobeniusRootRestrictedHom_apply, norm_restrictedExpand,
    norm_restrictedMap _ _ FrobeniusRoot.norm_algebraMap]

theorem frobeniusRootRestrictedHom_injective (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    (hr_pow : ∀ i, r i ^ p ^ e = c i) :
    Function.Injective (frobeniusRootRestrictedHom (K := K) p e hr_pow) :=
  ((AddMonoidHomClass.isometry_iff_norm _).mpr (norm_frobeniusRootRestrictedHom p e hr_pow))
    |>.injective

/-- The `p ^ e`-th power of `frobeniusRootRestrictedEquiv p e hr f` is
`frobeniusRootRestrictedHom p e hr_pow f`. -/
theorem frobeniusRootRestrictedEquiv_pow {p : ℕ} [ExpChar K p] {e : ℕ}
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)]
    (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹)) (hr_pow : ∀ i, r i ^ p ^ e = c i)
    (f : IsRestricted.subring (R := K) c) :
    frobeniusRootRestrictedEquiv p e hr f ^ p ^ e = frobeniusRootRestrictedHom p e hr_pow f := by
  have hp : p ≠ 0 := (expChar_pos K p).ne'
  have hhom : (iterateFrobenius (FrobeniusRoot K p e) p e).comp (FrobeniusRoot.root K p e) =
      algebraMap K (FrobeniusRoot K p e) := RingHom.ext FrobeniusRoot.root_pow_expChar_pow
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, coe_frobeniusRootRestrictedEquiv, coe_frobeniusRootRestrictedHom,
    ← MvPowerSeries.map_iterateFrobenius_expand p hp _ e, ← MvPowerSeries.map_expand,
    MvPowerSeries.map_map, hhom]

end FrobeniusRoot

section ComponentFamily

variable {σ : Type*} {K : Type*} {K' : Type*} [NormedField K] [NormedField K']
  [IsUltrametricDist K'] [NormedAlgebra K K']

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

theorem coe_coeff_restrictedExpandComponentFamily
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K')
    (z : IsRestricted.subring (R := K') r)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) (α : σ →₀ ℕ) :
    ((IsRestrictedFamily.coeff K α (restrictedExpandComponentFamily hq hr ν E z hz) : E) : K') =
      coeff α (restrictedExpandComponent hq hr ν z : _root_.MvPowerSeries σ K') := by
  rw [IsRestrictedFamily.coeff_apply]
  rfl

theorem restrictedExpandComponentFamily_zero
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K')
    (hz : ∀ α, coeff α ((0 : IsRestricted.subring (R := K') r) : _root_.MvPowerSeries σ K') ∈ E) :
    restrictedExpandComponentFamily hq hr ν E 0 hz = 0 := by
  refine IsRestrictedFamily.ext fun α ↦ Subtype.ext ?_
  rw [AddSubgroup.coe_zero, Pi.zero_apply, ZeroMemClass.coe_zero,
    ← IsRestrictedFamily.coeff_apply (R := K), coe_coeff_restrictedExpandComponentFamily,
    restrictedExpandComponent_zero, ZeroMemClass.coe_zero, map_zero]

theorem restrictedExpandComponentFamily_add
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K')
    (z₁ z₂ : IsRestricted.subring (R := K') r)
    (hz₁ : ∀ α, coeff α (z₁ : _root_.MvPowerSeries σ K') ∈ E)
    (hz₂ : ∀ α, coeff α (z₂ : _root_.MvPowerSeries σ K') ∈ E) :
    restrictedExpandComponentFamily hq hr ν E (z₁ + z₂)
        (fun α ↦ by rw [Subring.coe_add, map_add]; exact E.add_mem (hz₁ α) (hz₂ α)) =
      restrictedExpandComponentFamily hq hr ν E z₁ hz₁ +
        restrictedExpandComponentFamily hq hr ν E z₂ hz₂ := by
  refine IsRestrictedFamily.ext fun α ↦ Subtype.ext ?_
  rw [AddSubgroup.coe_add, Pi.add_apply, Submodule.coe_add,
    ← IsRestrictedFamily.coeff_apply (R := K), ← IsRestrictedFamily.coeff_apply (R := K),
    ← IsRestrictedFamily.coeff_apply (R := K), coe_coeff_restrictedExpandComponentFamily,
    coe_coeff_restrictedExpandComponentFamily, coe_coeff_restrictedExpandComponentFamily,
    restrictedExpandComponent_add, Subring.coe_add, map_add]

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

theorem restrictedExpandComponentFamily_restrictedExpand_mul [IsUltrametricDist K]
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) {ν : σ →₀ ℕ} (hν : ∀ i, ν i < q)
    (h_iso : ∀ a : K, ‖algebraMap K K' a‖ ≤ 1 * ‖a‖) (E : Submodule K K')
    (t : IsRestricted.subring (R := K) c) (z : IsRestricted.subring (R := K') r)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) :
    restrictedExpandComponentFamily hq hr ν E
        (restrictedExpand q hq hr (restrictedMap (algebraMap K K') h_iso t) * z)
        (coeff_restrictedExpand_restrictedMap_mul_mem hq hr h_iso E t hz) =
      t • restrictedExpandComponentFamily hq hr ν E z hz := by
  classical
  refine IsRestrictedFamily.ext fun α ↦ Subtype.ext ?_
  rw [← IsRestrictedFamily.coeff_apply (R := K), coe_coeff_restrictedExpandComponentFamily,
    restrictedExpandComponent_restrictedExpand_mul hq hr hν _ z,
    ← IsRestrictedFamily.coeff_apply (R := K), IsRestrictedFamily.coeff_apply,
    IsRestrictedFamily.coe_isRestrictedSubring_smul, convSMul_apply, Submodule.coe_sum,
    Subring.coe_mul, coeff_mul]
  refine Finset.sum_congr rfl fun pq _ ↦ ?_
  rw [SetLike.val_smul, Algebra.smul_def, coeff_restrictedMap,
    ← IsRestrictedFamily.coeff_apply (R := K), coe_coeff_restrictedExpandComponentFamily]

/-- Applying a bounded `K`-linear functional `φ : E →ₗ[K] K` (`‖φ e‖ ≤ C * ‖e‖`) coefficientwise
to an `E`-valued restricted family produces a `K{X / c}`-linear functional on
`IsRestrictedFamily.addSubgroup E c`. -/
noncomputable def IsRestrictedFamily.toSubringDualOfBound [IsUltrametricDist K]
    {E : Submodule K K'} {c : σ → ℝ} (φ : E →ₗ[K] K) {C : ℝ} (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖) :
    Module.Dual (IsRestricted.subring (R := K) c) (IsRestrictedFamily.addSubgroup E c) :=
  IsRestrictedFamily.subringLinearEquiv.symm.toLinearMap.comp
    { toFun := IsRestrictedFamily.mapLinearMap φ hφ
      map_add' := map_add _
      map_smul' t v := by
        rw [RingHom.id_apply]
        exact IsRestrictedFamily.mapLinearMap_isRestrictedSubring_smul φ hφ t v }

@[simp]
theorem coeff_coe_toSubringDualOfBound [IsUltrametricDist K] {E : Submodule K K'} {c : σ → ℝ}
    (φ : E →ₗ[K] K) {C : ℝ} (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖)
    (v : IsRestrictedFamily.addSubgroup E c) (α : σ →₀ ℕ) :
    coeff α (IsRestrictedFamily.toSubringDualOfBound φ hφ v : _root_.MvPowerSeries σ K) =
      φ (IsRestrictedFamily.coeff K α v) := by
  rw [IsRestrictedFamily.toSubringDualOfBound, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    IsRestrictedFamily.coeff_coe_subringLinearEquiv_symm_apply]
  simp [IsRestrictedFamily.coeff_apply]

/-- Every nonzero restricted series `z ∈ K'{X / r}` with coefficients in `E` has a `q`-adic
component `restrictedExpandComponentFamily hq hr ν E z hz` (`∀ i, ν i < q`) with at least one
nonzero coefficient in `E`. -/
theorem exists_coeff_restrictedExpandComponentFamily_ne_zero
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (E : Submodule K K')
    {z : IsRestricted.subring (R := K') r} (hz_ne : z ≠ 0)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) :
    ∃ (ν : σ →₀ ℕ) (_ : ∀ i, ν i < q) (μ : σ →₀ ℕ),
      IsRestrictedFamily.coeff K μ (restrictedExpandComponentFamily hq hr ν E z hz) ≠ 0 := by
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
  rw [ZeroMemClass.coe_zero, coe_coeff_restrictedExpandComponentFamily]
  exact hμ_ne

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
  rw [coeff_coe_toSubringDualOfBound] at hcoeff0
  exact hf_ne hcoeff0

end ComponentFamily

section ComponentDual

variable {σ : Type*} {K : Type*} {K' : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NormedField K'] [IsUltrametricDist K'] [NormedAlgebra K K']

/-- Applying a continuous `K`-linear functional `f_dual : StrongDual K E` coefficientwise to an
`E`-valued restricted family produces a `K{X / c}`-linear functional on
`IsRestrictedFamily.addSubgroup E c`. -/
noncomputable def IsRestrictedFamily.toSubringDual {E : Submodule K K'} {c : σ → ℝ}
    (f_dual : StrongDual K E) :
    Module.Dual (IsRestricted.subring (R := K) c) (IsRestrictedFamily.addSubgroup E c) :=
  IsRestrictedFamily.toSubringDualOfBound f_dual.toLinearMap f_dual.le_opNorm

@[simp]
theorem coeff_coe_toSubringDual {E : Submodule K K'} {c : σ → ℝ} (f_dual : StrongDual K E)
    (v : IsRestrictedFamily.addSubgroup E c) (α : σ →₀ ℕ) :
    coeff α (IsRestrictedFamily.toSubringDual f_dual v : _root_.MvPowerSeries σ K) =
      f_dual (IsRestrictedFamily.coeff K α v) :=
  coeff_coe_toSubringDualOfBound f_dual.toLinearMap f_dual.le_opNorm v α

/-- Gauss-norm bound on `toSubringDual f_dual (restrictedExpandComponentFamily hq hr ν E z hz)`. -/
theorem norm_toSubringDual_restrictedExpandComponentFamily_le
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (ν : σ →₀ ℕ) (E : Submodule K K') (f_dual : StrongDual K E)
    (z : IsRestricted.subring (R := K') r)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) :
    ‖IsRestrictedFamily.toSubringDual f_dual (restrictedExpandComponentFamily hq hr ν E z hz)‖ ≤
      (‖f_dual‖ / ν.prod (r · ^ ·)) * ‖z‖ := by
  calc ‖IsRestrictedFamily.toSubringDual f_dual (restrictedExpandComponentFamily hq hr ν E z hz)‖
      ≤ ‖f_dual‖ * ‖restrictedExpandComponent hq hr ν z‖ := by
        refine norm_le_mul_of_norm_coeff_le fun α ↦ ?_
        rw [coeff_coe_toSubringDual, ← coe_coeff_restrictedExpandComponentFamily hq hr ν E z hz α,
          ← AddSubgroupClass.coe_norm]
        exact f_dual.le_opNorm _
    _ ≤ ‖f_dual‖ * (‖z‖ / ν.prod (r · ^ ·)) :=
        mul_le_mul_of_nonneg_left ((le_div_iff₀ (prod_pow_pos ν)).mpr
          (norm_restrictedExpandComponent_mul_prod_le hq hr ν z)) (norm_nonneg _)
    _ = (‖f_dual‖ / ν.prod (r · ^ ·)) * ‖z‖ := by ring

/-- When `StrongDual K E` separates points of `E`, any nonzero restricted series `z ∈ K'{X / r}`
whose coefficients lie in `E` has a nonzero projection
`toSubringDual f_dual (restrictedExpandComponentFamily hq hr ν E z hz)` for some remainder `ν`
(`∀ i, ν i < q`) and some `f_dual : StrongDual K E`. -/
theorem exists_toSubringDual_restrictedExpandComponentFamily_ne_zero
    {c r : σ → ℝ} [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (E : Submodule K K') [SeparatingDual K E]
    {z : IsRestricted.subring (R := K') r} (hz_ne : z ≠ 0)
    (hz : ∀ α, coeff α (z : _root_.MvPowerSeries σ K') ∈ E) :
    ∃ (ν : σ →₀ ℕ) (_ : ∀ i, ν i < q) (f_dual : StrongDual K E),
      IsRestrictedFamily.toSubringDual f_dual
        (restrictedExpandComponentFamily hq hr ν E z hz) ≠ 0 := by
  obtain ⟨ν, hν, μ, hμE_ne⟩ :=
    exists_coeff_restrictedExpandComponentFamily_ne_zero hq hr E hz_ne hz
  obtain ⟨f_dual, hf_ne⟩ := SeparatingDual.exists_ne_zero (R := K) hμE_ne
  refine ⟨ν, hν, f_dual, fun h0 ↦ ?_⟩
  have hcoeff0 : coeff μ (IsRestrictedFamily.toSubringDual f_dual
      (restrictedExpandComponentFamily hq hr ν E z hz) : _root_.MvPowerSeries σ K) = 0 := by
    rw [h0, ZeroMemClass.coe_zero, map_zero]
  rw [coeff_coe_toSubringDual] at hcoeff0
  exact hf_ne hcoeff0

end ComponentDual

end TauCeti.MvPowerSeries
