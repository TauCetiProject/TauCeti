/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Basic

import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Trace.Basic
import TauCeti.GroupTheory.Index.NSmul
import TauCeti.NumberTheory.LocalField.NormedField
import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded
import TauCeti.NumberTheory.LocalField.UnitsDecomposition
import TauCeti.RingTheory.Norm.Henselian

/-!
# Open norm groups of finite local-field extensions

The norm group of a finite separable extension of nonarchimedean local fields is open and has
finite index. Openness is a local property of the field norm. Choose an element of trace one and
restrict the norm to the affine line through `1` in that direction. This one-variable polynomial
has derivative `1` at the origin, so the inverse function theorem shows that its image contains a
neighbourhood of `1`.

For finite index, the valuation--unit decomposition `Kˣ ≃ ℤ × 𝒪[K]ˣ` separates the two
parts. The norm group contains a deep open unit-filtration subgroup, while norms of elements from
the base field contain the degree multiples in the valuation factor. Their product has finite
index.

## Main results

* `TauCeti.isOpen_normGroup`: `N_{L/K}(Lˣ)` is open in `Kˣ`.
* `TauCeti.finiteIndex_normGroup`: `N_{L/K}(Lˣ)` has finite index in `Kˣ`.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section

noncomputable section

open Filter IsNonarchimedeanLocalField Polynomial ValuativeRel

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

/-- The norm group of a finite separable extension contains a neighbourhood of `1`; since it is a
subgroup, this makes it open. -/
private theorem normGroup_mem_nhds_one : (normGroup K L : Set Kˣ) ∈ nhds (1 : Kˣ) := by
  classical
  -- For `x` of trace one, the norm on the line `t ↦ 1 + t x` is a polynomial `P` with value and
  -- derivative both `1` at `0`, so the inverse function theorem puts a neighbourhood of `1` in
  -- its range.
  obtain ⟨x, hx⟩ := Algebra.trace_surjective K L 1
  let b := Module.Free.chooseBasis K L
  let M := Algebra.leftMulMatrix b (-x)
  let P : K[X] := M.charpolyRev
  have hPeval (t : K) : P.eval t = Algebra.norm K (1 + t • x) := by
    rw [Algebra.eval_charpolyRev_leftMulMatrix, smul_neg, sub_neg_eq_add]
  have hPzero : P.eval 0 = 1 := by simp [P]
  have hPderiv : P.derivative.eval 0 = 1 := by
    simp only [P, ← coeff_zero_eq_eval_zero, coeff_derivative, zero_add,
      Matrix.coeff_charpolyRev_eq_neg_trace]
    simp only [M, map_neg, Matrix.trace_neg, neg_neg]
    simpa using (Algebra.trace_eq_matrix_trace b x).symm.trans hx
  have hrange_norm : Set.range (fun t : K ↦ P.eval t) ∈
      @nhds K (normalizedNormedFieldTopology K) 1 := by
    let _ := normalizedNontriviallyNormedField K
    let _ := normalizedNormedField_completeSpace K
    have hmap := (P.hasStrictDerivAt 0).map_nhds_eq (hPderiv ▸ one_ne_zero)
    simp only [hPzero] at hmap
    rw [← hmap]
    exact range_mem_map
  have hrange : Set.range (fun t : K ↦ P.eval t) ∈ nhds (1 : K) := by
    rw [normalizedNormedField_topology_eq K] at hrange_norm
    exact hrange_norm
  have hpreimage : Units.val ⁻¹' Set.range (fun t : K ↦ P.eval t) ∈ nhds (1 : Kˣ) :=
    Units.continuous_val.continuousAt hrange
  refine mem_of_superset hpreimage fun y hy ↦ ?_
  rw [Set.mem_preimage, Set.mem_range] at hy
  obtain ⟨t, ht⟩ := hy
  have hne : 1 + t • x ≠ 0 := by
    intro h
    have hy0 : (y : K) = 0 := by rw [← ht, hPeval, h, Algebra.norm_zero]
    exact y.ne_zero hy0
  refine mem_normGroup_iff.2 ⟨Units.mk0 (1 + t • x) hne, ?_⟩
  rw [Units.val_mk0, ← hPeval, ht]

/-- **Norm groups of finite separable local-field extensions are open.** -/
theorem isOpen_normGroup : IsOpen (normGroup K L : Set Kˣ) :=
  (normGroup K L).isOpen_of_mem_nhds normGroup_mem_nhds_one

/-- **Norm groups of finite separable local-field extensions have finite index.** -/
theorem finiteIndex_normGroup : (normGroup K L).FiniteIndex := by
  have hnhds : (normGroup K L : Set Kˣ) ∈ nhds (1 : Kˣ) :=
    (isOpen_normGroup (K := K) (L := L)).mem_nhds (normGroup K L).one_mem
  obtain ⟨i, -, hi⟩ := hasBasis_nhds_one_unitFiltration.mem_iff.mp hnhds
  let m := i + 1
  have hm : unitFiltration K m ≤ normGroup K L :=
    (unitFiltration_antitone (Nat.le_succ i)).trans hi
  obtain ⟨ϖ, hϖ⟩ := normalizedValuation_surjective (K := K) (.ofAdd 1)
  let n := Module.finrank K L
  have hn : n ≠ 0 := (Module.finrank_pos : 0 < Module.finrank K L).ne'
  let Hℤ := (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range
  have hpow : (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ) =
      AddMonoidHom.toMultiplicative (nsmulAddMonoidHom (α := ℤ) n) := by
    ext
    simp
  have hHℤindex : Hℤ.index = n := by
    simp only [Hℤ]
    rw [hpow, MonoidHom.coe_toMultiplicative_range, AddSubgroup.index_toSubgroup,
      AddSubgroup.index_range_nsmul]
    simp
  have hHℤ : Hℤ.FiniteIndex := ⟨hHℤindex.trans_ne hn⟩
  let U := unitFiltration K 0
  let HU := (unitFiltration K m).subgroupOf U
  have hrel : (unitFiltration K m).IsFiniteRelIndex U :=
    (unitFiltration_isFiniteRelIndex_succ m 0).trans
      unitFiltration_one_isFiniteRelIndex_zero
  have hHU : HU.FiniteIndex :=
    (Subgroup.isFiniteRelIndex_iff_finiteIndex (H := unitFiltration K m) (K := U)).mp hrel
  have hH : (Hℤ.prod HU).FiniteIndex := ⟨by
    rw [Subgroup.index_prod]
    exact mul_ne_zero hHℤ.index_ne_zero hHU.index_ne_zero⟩
  let e : Multiplicative ℤ × U →* Kˣ := (unitsEquivIntProd K ϖ hϖ).symm
  have hT : ((Hℤ.prod HU).map e).FiniteIndex :=
    Subgroup.FiniteIndex.map_of_surjective _ (unitsEquivIntProd K ϖ hϖ).symm.surjective
  apply Subgroup.finiteIndex_of_le (H := (Hℤ.prod HU).map e)
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨hz, hu⟩ := hz
  obtain ⟨k, hk⟩ := hz
  rw [MonoidHom.coe_ofClass, unitsEquivIntProd_symm_apply, ← hk]
  apply mul_mem
  · refine mem_normGroup_iff.2
      ⟨Units.map (algebraMap K L : K →* L) (ϖ ^ k.toAdd), ?_⟩
    rw [Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val,
      MonoidHom.coe_ofClass, Algebra.norm_algebraMap, powMonoidHom_apply, toAdd_pow, nsmul_eq_mul,
      ← zpow_natCast, ← zpow_mul, mul_comm]
  · exact hm hu

end TauCeti
