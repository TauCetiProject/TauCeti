/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic

/-!
# Finite extensions of a nonarchimedean local field are local fields

For a finite extension `M/K` of a nonarchimedean local field, the spectral-norm structures from
`TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic` make `M` complete and locally compact,
and hence a nonarchimedean local field. The algebraic-extension construction and uniqueness
results need only algebraicity; this file supplies the consequences that need finite dimension.

## Main results

* `TauCeti.algebraicExtensionNormedField_completeSpace`: completeness of the spectral norm on a
  finite extension.
* `TauCeti.finiteExtension_isNonarchimedeanLocalField`: the constructed topology and valuative
  relation make the finite extension a nonarchimedean local field.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §6.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §2.
-/

public section

open ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (M : Type*) [Field M] [Algebra K M] [Module.Finite K M]

/-- A finite extension of a nonarchimedean local field is complete for the norm of
`algebraicExtensionNormedField K M`. -/
theorem algebraicExtensionNormedField_completeSpace :
    letI := algebraicExtensionNormedField K M
    CompleteSpace M := by
  let _ := normalizedNontriviallyNormedField K
  have := normalizedNormedField_completeSpace K
  have := normalizedNormedField_isUltrametricDist K
  exact spectralNorm.completeSpace K M

/-- A finite extension `M` of a nonarchimedean local field `K`, with the topology and valuative
relation of the spectral norm, is a nonarchimedean local field. -/
theorem finiteExtension_isNonarchimedeanLocalField :
    @IsNonarchimedeanLocalField M _ (algebraicExtensionValuativeRel K M)
      (algebraicExtensionNormedFieldTopology K M) := by
  let _ := algebraicExtensionNormedField K M
  let _ := algebraicExtensionValuativeRel K M
  let _ := normalizedNontriviallyNormedField K
  have := normalizedNormedField_isUltrametricDist K
  have := normalizedNormedField_completeSpace K
  have := algebraicExtensionNormedField_isUltrametricDist K M
  have := algebraicExtension_isValuativeTopology K M
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
    rw [algebraicExtensionNormedField_norm_algebraMap] at h'
    exact ((normalizedAbsoluteValue_lt_one_iff y).2 hy1).ne (mod_cast h')
  exact { }

end TauCeti
