/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Determinant

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Relative index of a `ℤ`-lattice in its preimage under an endomorphism

Let `L` be a `ℤ`-lattice in a finite-dimensional real normed space `V`, and let `F : V →ₗ[ℝ] V`
be a linear endomorphism preserving `L` (`∀ z ∈ L, F z ∈ L`). Then the index of `L` in its
preimage `F⁻¹(L)` equals `|det F|`: when `F` is injective this follows by comparing a `ℤ`-basis
of `L` with its preimage under `F`, while when `F` is not injective `F.det = 0` and `F⁻¹(L)`
contains a real line, so the quotient `F⁻¹(L) / L` is infinite and the index is `0`.

When `V` is a finite-dimensional complex normed space and `F : V →ₗ[ℂ] V` is `ℂ`-linear, the
determinant of `F` as an `ℝ`-linear map is `Complex.normSq F.det = F.det * starRingEnd ℂ F.det`,
so the index of `L` in `F⁻¹(L)` equals `F.det * starRingEnd ℂ F.det`.

## Main results

* `IsZLattice.relIndex_comap_eq_abs_det`: for an `ℝ`-linear endomorphism `F` preserving a
  `ℤ`-lattice `L`, `(L.toAddSubgroup.relIndex (L.toAddSubgroup.comap F.toAddMonoidHom) : ℝ) =
  |F.det|`.
* `IsZLattice.relIndex_comap_eq_det_mul_conj_det`: for a `ℂ`-linear endomorphism `F` preserving a
  `ℤ`-lattice `L`, `(L.toAddSubgroup.relIndex (L.toAddSubgroup.comap F.toAddMonoidHom) : ℂ) =
  F.det * starRingEnd ℂ F.det`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Shimura/Uniformisation/HolomorphicFamilies.lean` (`relIndex_comap_eq_det_mul_conj_det`).
-/

public section

open Module LinearMap AddSubgroup

namespace IsZLattice

private theorem relIndex_comap_eq_zero_of_not_injective {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] {F : V →ₗ[ℝ] V}
    (hF_not_inj : ¬ Function.Injective F) :
    L.toAddSubgroup.relIndex (L.toAddSubgroup.comap F.toAddMonoidHom) = 0 := by
  by_contra h_ne
  obtain ⟨v, hv_ker, hv_ne⟩ : ∃ v : V, F v = 0 ∧ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hF_not_inj ((injective_iff_map_eq_zero F).mpr h)
  let K := L.toAddSubgroup.comap F.toAddMonoidHom
  let n : ℕ := L.toAddSubgroup.relIndex K
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h_ne
  have _ : Finite (K ⧸ L.toAddSubgroup.addSubgroupOf K) := Nat.finite_of_card_ne_zero h_ne
  have h_mem (t : ℝ) : t • v ∈ L := by
    let x : K := ⟨((n : ℝ)⁻¹ * t) • v, by simp [K, hv_ker]⟩
    have hq : n • (x : K ⧸ L.toAddSubgroup.addSubgroupOf K) = 0 := by
      simp [n, AddSubgroup.relIndex, AddSubgroup.index]
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at hq
    have hx : (n • x : V) = t • v := by
      change n • (((n : ℝ)⁻¹ * t) • v) = t • v
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel_left₀ hn]
    simpa [AddSubgroup.mem_addSubgroupOf, hx] using hq
  have h_cont : Continuous fun t : ℝ ↦ (⟨t • v, h_mem t⟩ : L) :=
    (continuous_id.smul continuous_const).subtype_mk h_mem
  have h_eq : (⟨(1 : ℝ) • v, h_mem 1⟩ : L) = ⟨(0 : ℝ) • v, h_mem 0⟩ :=
    TotallyDisconnectedSpace.eq_of_continuous _ h_cont 1 0
  exact hv_ne (by simpa using congrArg Subtype.val h_eq)

/-- Let `L` be a `ℤ`-lattice in a finite-dimensional real normed space `V` and `F : V →ₗ[ℝ] V`
an `ℝ`-linear endomorphism with `F(L) ⊆ L`. Then the index of `L` in `F⁻¹(L)` equals `|F.det|`. -/
theorem relIndex_comap_eq_abs_det {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {F : V →ₗ[ℝ] V} (hF_mem : ∀ z ∈ L, F z ∈ L) :
    (L.toAddSubgroup.relIndex (L.toAddSubgroup.comap F.toAddMonoidHom) : ℝ) = |F.det| := by
  by_cases hF_inj : Function.Injective F
  · have _ : Module.Finite ℤ L := ZLattice.module_finite ℝ L
    have _ : Module.Free ℤ L := ZLattice.module_free ℝ L
    let b : Basis (Fin (finrank ℤ L)) ℤ L := finBasis ℤ L
    let Φ : V ≃ₗ[ℤ] V := (LinearEquiv.ofInjectiveEndo F hF_inj).restrictScalars ℤ
    let b' : Basis (Fin (finrank ℤ L)) ℤ (L.comap Φ.toLinearMap) := b.map (Φ.ofSubmodule' L).symm
    let M : Matrix (Fin (finrank ℤ L)) (Fin (finrank ℤ L)) ℤ :=
      b'.toMatrix fun i ↦ ⟨b i, hF_mem (b i) (b i).property⟩
    have h_index : L.toAddSubgroup.relIndex (L.toAddSubgroup.comap F.toAddMonoidHom) =
        M.det.natAbs :=
      AddSubgroup.relIndex_eq_natAbs_det L.toAddSubgroup
        (L.toAddSubgroup.comap F.toAddMonoidHom) hF_mem b b'
    let bℝ : Basis (Fin (finrank ℤ L)) ℝ V := b.ofZLatticeBasis ℝ
    have h_matrix : M.map (Int.cast : ℤ → ℝ) = toMatrix bℝ bℝ F := by
      ext i j
      have h_image : Φ.ofSubmodule' L ⟨(b j : V), hF_mem (b j) (b j).property⟩ =
          ⟨F (b j), hF_mem (b j) (b j).property⟩ := rfl
      simpa [bℝ, M, b', Basis.toMatrix_apply, toMatrix_apply, h_image] using
        (b.ofZLatticeBasis_repr_apply ℝ L ⟨F (b j), hF_mem (b j) (b j).property⟩ i).symm
    have h_det : (M.det : ℝ) = F.det := by
      rw [Int.cast_det, h_matrix, det_toMatrix]
    rw [h_index, Nat.cast_natAbs, Int.cast_abs, h_det]
  · have h_det : F.det = 0 := by
      by_contra h_ne
      let bV := finBasis ℝ V
      have h_unit : IsUnit (toMatrix bV bV F).det := by
        rw [det_toMatrix]
        exact IsUnit.mk0 _ h_ne
      exact hF_inj (LinearEquiv.ofIsUnitDet h_unit).injective
    rw [relIndex_comap_eq_zero_of_not_injective L hF_inj, h_det, Nat.cast_zero, abs_zero]

/-- Let `L` be a `ℤ`-lattice in a finite-dimensional complex normed space `V` and `F : V →ₗ[ℂ] V`
a `ℂ`-linear endomorphism with `F(L) ⊆ L`. Then the index of `L` in `F⁻¹(L)` equals
`F.det * starRingEnd ℂ F.det` (i.e., `|F.det|²`). -/
theorem relIndex_comap_eq_det_mul_conj_det {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] {F : V →ₗ[ℂ] V} (hF_mem : ∀ z ∈ L, F z ∈ L) :
    (L.toAddSubgroup.relIndex (L.toAddSubgroup.comap F.toAddMonoidHom) : ℂ) =
      F.det * starRingEnd ℂ F.det := by
  have _ : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  have h_real : (L.toAddSubgroup.relIndex (L.toAddSubgroup.comap F.toAddMonoidHom) : ℝ) =
      |(F.restrictScalars ℝ).det| :=
    relIndex_comap_eq_abs_det L (F := F.restrictScalars ℝ) hF_mem
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    abs_of_nonneg (Complex.normSq_nonneg _)] at h_real
  rw [Complex.mul_conj, ← h_real, Complex.ofReal_natCast]

end IsZLattice
