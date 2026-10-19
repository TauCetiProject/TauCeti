/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Manifold
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Basic

/-!
# Toric maps of analytic realizations are holomorphic

A morphism of regular fans `f : FanHom Φ Ψ` induces the continuous map
`TauCeti.Toric.FanHom.analyticMap` between their analytic realizations. This file proves that it is
holomorphic for the complex manifold structures of the two realizations.

Holomorphy is local. On the chart of a cone `σ` of `Φ`, the glued map is the pullback of complex
points along the map of dual semigroups into the chart of the least target cone `υ`, followed by the
inclusion of that chart. For extending bases of `σ` and `υ`, the inclusion of the chart of `σ` is a
biholomorphism onto its open image, the pullback is holomorphic because it carries monomials to
monomials, and the inclusion of the chart of `υ` is holomorphic.

## Main declarations

* `TauCeti.Toric.FanHom.contMDiff_analyticMap`: the map of analytic realizations induced by a
  morphism of regular fans is holomorphic.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.3.
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric.FanHom

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i}
  {Ψ : Fan i'} (f : FanHom Φ Ψ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

/-- The map between the analytic realizations of two regular fans induced by a fan morphism is
holomorphic, for their complex manifold structures modelled on `ℂ ^ n` and `ℂ ^ n'`, where `n` and
`n'` are the ranks of the two lattices. -/
theorem contMDiff_analyticMap (n : ℕ∞ω) :
    letI := Φ.analyticChartedSpace hΦ
    letI := Ψ.analyticChartedSpace hΨ
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N') → ℂ) n
      (f.analyticMap hΦ hΨ) := by
  let _ := Φ.analyticChartedSpace hΦ
  let _ := Ψ.analyticChartedSpace hΨ
  intro p
  obtain ⟨σ, x, rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ p
  let υ : Ψ.cones := ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩
  have hσ := (Fan.isRegular_iff.mp hΦ) σ.1 σ.2
  have hυ := (Fan.isRegular_iff.mp hΨ) υ.1 υ.2
  obtain ⟨l, B, hB⟩ := hσ.exists_basis_sum
  obtain ⟨l', C, hC⟩ := hυ.exists_basis_sum
  have : Finite (ToricRay σ.1) := ToricRay.finite_of_fg hσ.fg
  have : Finite (ToricRay υ.1) := ToricRay.finite_of_fg hυ.fg
  let κ := Finite.equivFin (ToricRay σ.1)
  let κ' := Finite.equivFin (ToricRay υ.1)
  let g := (Φ.analyticChartGenerators σ).2
  let g' := (Ψ.analyticChartGenerators υ).2
  let _ := affinePointTopology g
  let _ := coneChartedSpace Φ.lattice hσ.toIsToricCone hB κ g
  let _ := affinePointTopology g'
  let _ := coneChartedSpace Ψ.lattice hυ.toIsToricCone hC κ' g'
  let P := Φ.analyticAffineChartPartialDiffeomorph hΦ σ hB κ g n
  have hP : P.target = range (Φ.analyticAffineChartι hΦ σ) :=
    Φ.analyticAffineChartPartialDiffeomorph_target hΦ σ hB κ g n
  -- On the image of the chart of `σ`, the glued map is the pullback into the chart of `υ`,
  -- conjugated by the two chart inclusions.
  have hloc := (Ψ.contMDiff_analyticAffineChartι hΨ υ hC κ' g' n).comp_contMDiffOn
    ((AffineSemigroupComplexPoint.contMDiff_comap Φ.lattice hσ.toIsToricCone hB κ Ψ.lattice
      hυ.toIsToricCone hC κ' g g'
      (dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice
        (f.mapsTo_leastCone σ.2)) n).comp_contMDiffOn P.symm.contMDiffOn)
  have hmem : P.target ∈ 𝓝 (Φ.analyticAffineChartι hΦ σ x) :=
    P.open_target.mem_nhds (hP ▸ mem_range_self x)
  refine (hloc.contMDiffAt hmem).congr_of_eventuallyEq ?_
  filter_upwards [hmem] with z hz
  obtain ⟨y, rfl⟩ := hP ▸ hz
  have hPy : P.symm (Φ.analyticAffineChartι hΦ σ y) = y := by
    rw [← Φ.analyticAffineChartPartialDiffeomorph_apply hΦ σ hB κ g n y]
    exact P.left_inv ((Φ.analyticAffineChartPartialDiffeomorph_source hΦ σ hB κ g n).symm ▸
      mem_univ y)
  rw [analyticMap_analyticAffineChartι, Function.comp_apply, Function.comp_apply, hPy]
  exact congrArg (Ψ.analyticAffineChartι hΨ υ) (f.analyticChartMap_apply _ y)

end TauCeti.Toric.FanHom
