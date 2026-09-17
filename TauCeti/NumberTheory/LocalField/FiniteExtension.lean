/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import TauCeti.NumberTheory.LocalField.NormedField

/-!
# Finite extensions of a nonarchimedean local field are local fields

Let `K` be a nonarchimedean local field and let `M` be a field that is a finite-dimensional
`K`-algebra, with no topology or valuative relation assumed on `M`. Since `K` is complete for its
normalized absolute value (`TauCeti.normalizedNormedField`), the spectral norm of `M/K` is a
multiplicative ultrametric norm on `M` extending that absolute value, and it is the only absolute
value on `M` that does so. This file equips `M` with the resulting normed field, its topology,
and the valuative relation of the norm, and proves that with these structures `M` is a
nonarchimedean local field whose valuation extends that of `K`.

All structures are named definitions rather than global instances, so that a field already
carrying a compatible topology or valuative relation acquires no diamond. They are meant to be
installed locally, as in `letI := finiteExtensionValuativeRel K M`.

## Main definitions

* `TauCeti.finiteExtensionNormedField K M`: the spectral norm of `M/K` as a normed field.
* `TauCeti.finiteExtensionNormedFieldTopology K M`: the topology of that norm.
* `TauCeti.finiteExtensionValuativeRel K M`: the valuative relation of that norm.

## Main results

* `TauCeti.finiteExtensionNormedField_norm_algebraMap`: the norm extends the normalized absolute
  value of `K`.
* `TauCeti.finiteExtensionNormedField_norm_unique`: it is the only absolute value on `M` doing so.
* `TauCeti.finiteExtensionNormedField_completeSpace`: `M` is complete for the norm.
* `TauCeti.finiteExtension_valuativeExtension`: the valuative relation on `M` extends that of `K`.
* `TauCeti.finiteExtension_isValuativeTopology`: the norm topology is the valuative topology.
* `TauCeti.finiteExtension_isNonarchimedeanLocalField`: `M` is a nonarchimedean local field.

## Implementation notes

The norm is Mathlib's `spectralNorm.normedField`, applied after locally installing
`normalizedNontriviallyNormedField K`; the needed completeness and ultrametricity of `K` are
`normalizedNormedField_completeSpace` and `normalizedNormedField_isUltrametricDist`. The
valuative topology comes from Mathlib's `NormedField.toValued`, and local compactness of `M`
from `FiniteDimensional.proper`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4 (Theorem 4.8) and §6.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §2.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (M : Type*) [Field M] [Algebra K M] [Module.Finite K M]

/-- The normed-field structure on a finite extension `M` of a nonarchimedean local field `K`
given by the spectral norm of `M/K` with respect to the normalized absolute value of `K`. -/
@[expose, implicit_reducible]
def finiteExtensionNormedField : NormedField M :=
  letI := normalizedNontriviallyNormedField K
  haveI := normalizedNormedField_completeSpace K
  haveI := normalizedNormedField_isUltrametricDist K
  spectralNorm.normedField K M

/-- The topology on a finite extension `M` of a nonarchimedean local field `K` induced by the
norm of `finiteExtensionNormedField K M`. -/
@[expose, implicit_reducible]
def finiteExtensionNormedFieldTopology : TopologicalSpace M :=
  (finiteExtensionNormedField K M).toUniformSpace.toTopologicalSpace

/-- The norm of `finiteExtensionNormedField K M` is the spectral norm of `M/K`. -/
theorem finiteExtensionNormedField_norm_def (x : M) :
    letI := finiteExtensionNormedField K M
    letI := normalizedNontriviallyNormedField K
    ‖x‖ = spectralNorm K M x := (rfl)

variable {K M} in
/-- The norm of `finiteExtensionNormedField K M` extends the normalized absolute value of `K`. -/
@[simp]
theorem finiteExtensionNormedField_norm_algebraMap (x : K) :
    letI := finiteExtensionNormedField K M
    ‖algebraMap K M x‖ = normalizedAbsoluteValue K x := by
  let _ := normalizedNontriviallyNormedField K
  rw [finiteExtensionNormedField_norm_def, spectralNorm_extends]
  exact normalizedNormedField_norm_def x

variable {M} in
/-- The norm of `finiteExtensionNormedField K M` is the only real absolute value on `M` extending
the normalized absolute value of `K`. -/
theorem finiteExtensionNormedField_norm_unique {f : AbsoluteValue M ℝ}
    (hf : ∀ x : K, f (algebraMap K M x) = normalizedAbsoluteValue K x) (x : M) :
    letI := finiteExtensionNormedField K M
    f x = ‖x‖ := by
  let _ := normalizedNontriviallyNormedField K
  have := normalizedNormedField_completeSpace K
  have := normalizedNormedField_isUltrametricDist K
  rw [finiteExtensionNormedField_norm_def]
  exact spectralNorm_unique_field_norm_ext hf x

/-- The norm of `finiteExtensionNormedField K M` is ultrametric. -/
theorem finiteExtensionNormedField_isUltrametricDist :
    letI := finiteExtensionNormedField K M
    IsUltrametricDist M := by
  let _ := finiteExtensionNormedField K M
  let _ := normalizedNontriviallyNormedField K
  have := normalizedNormedField_isUltrametricDist K
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm

/-- A finite extension of a nonarchimedean local field is complete for the norm of
`finiteExtensionNormedField K M`. -/
theorem finiteExtensionNormedField_completeSpace :
    letI := finiteExtensionNormedField K M
    CompleteSpace M := by
  let _ := normalizedNontriviallyNormedField K
  have := normalizedNormedField_completeSpace K
  have := normalizedNormedField_isUltrametricDist K
  exact spectralNorm.completeSpace K M

/-- The valuative relation on a finite extension `M` of a nonarchimedean local field `K` defined
by the norm of `finiteExtensionNormedField K M`: `x ≤ᵥ y` exactly when `‖x‖ ≤ ‖y‖`. -/
@[expose, implicit_reducible]
def finiteExtensionValuativeRel : ValuativeRel M :=
  letI := finiteExtensionNormedField K M
  haveI := finiteExtensionNormedField_isUltrametricDist K M
  ValuativeRel.ofValuation (NormedField.valuation (K := M))

variable {K M} in
/-- The relation `finiteExtensionValuativeRel K M` compares norms. -/
@[simp]
theorem finiteExtensionValuativeRel_vle_iff (x y : M) :
    letI := finiteExtensionValuativeRel K M
    letI := finiteExtensionNormedField K M
    x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ :=
  -- `ValuativeRel.ofValuation` defines `x ≤ᵥ y` as `‖x‖₊ ≤ ‖y‖₊` for `NormedField.valuation`.
  NNReal.coe_le_coe

/-- The valuative relation `finiteExtensionValuativeRel K M` extends the valuative relation
of `K`. -/
theorem finiteExtension_valuativeExtension :
    letI := finiteExtensionValuativeRel K M
    ValuativeExtension K M := by
  let _ := finiteExtensionValuativeRel K M
  refine ⟨fun a b => ?_⟩
  rw [finiteExtensionValuativeRel_vle_iff, finiteExtensionNormedField_norm_algebraMap,
    finiteExtensionNormedField_norm_algebraMap, NNRat.cast_le,
    normalizedAbsoluteValue_le_normalizedAbsoluteValue_iff, (valuation K).vle_iff_le]

/-- The norm topology `finiteExtensionNormedFieldTopology K M` is the valuative topology of
`finiteExtensionValuativeRel K M`. -/
theorem finiteExtension_isValuativeTopology :
    @IsValuativeTopology M _ (finiteExtensionValuativeRel K M)
      (finiteExtensionNormedFieldTopology K M) := by
  let _ := finiteExtensionNormedField K M
  let _ := finiteExtensionValuativeRel K M
  have := finiteExtensionNormedField_isUltrametricDist K M
  have := Valuation.Compatible.ofValuation (NormedField.valuation (K := M))
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle NormedField.valuation
    fun {s} => NormedField.toValued.is_topological_valuation s

/-- A finite extension `M` of a nonarchimedean local field `K`, with the topology and valuative
relation of the spectral norm, is a nonarchimedean local field. -/
theorem finiteExtension_isNonarchimedeanLocalField :
    @IsNonarchimedeanLocalField M _ (finiteExtensionValuativeRel K M)
      (finiteExtensionNormedFieldTopology K M) := by
  let _ := finiteExtensionNormedField K M
  let _ := finiteExtensionValuativeRel K M
  let _ := normalizedNontriviallyNormedField K
  have := normalizedNormedField_isUltrametricDist K
  have := normalizedNormedField_completeSpace K
  have := finiteExtensionNormedField_isUltrametricDist K M
  have := finiteExtension_isValuativeTopology K M
  -- Local compactness: `K` is locally compact for its norm, so the finite-dimensional normed
  -- `K`-space `M` is proper.
  have : @LocallyCompactSpace K (normalizedNormedFieldTopology K) := by
    rw [normalizedNormedField_topology_eq]
    infer_instance
  let _ := spectralNorm.normedSpace K M
  have : ProperSpace M := FiniteDimensional.proper K M
  -- Nontriviality: an element of `K` of valuation strictly between `0` and `1` keeps its
  -- absolute value in `M`.
  have : ValuativeRel.IsNontrivial M := by
    have := Valuation.Compatible.ofValuation (NormedField.valuation (K := M))
    refine (isNontrivial_iff_isNontrivial NormedField.valuation).2 ?_
    obtain ⟨y, hy0, hy1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
    refine ⟨⟨algebraMap K M y, by simpa using hy0, fun h => ?_⟩⟩
    have h' : ‖algebraMap K M y‖ = 1 := by simpa using congrArg NNReal.toReal h
    rw [finiteExtensionNormedField_norm_algebraMap] at h'
    exact ((normalizedAbsoluteValue_lt_one_iff y).2 hy1).ne (mod_cast h')
  exact { }

end TauCeti
