/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Comparison.Naturality
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Holomorphic

/-!
# The complex manifold of algebraic toric complex points

The complex points of the scheme of a regular fan carry the affine-chart topology, not the
Zariski topology. Pulling the atlas of the analytic realization back along the chartwise
comparison makes this carrier a complex manifold. The pulled-back structure agrees locally with
the independently defined regular affine-chart structures for any extending basis and finite
generating family: every algebraic affine chart inclusion is a local biholomorphism.

The comparison is a biholomorphism, and the scheme-theoretic map on complex points induced by
a fan morphism is holomorphic. The comparison intertwines this map with the analytic toric map.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.Toric

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (hΦ : Φ.IsRegular)

namespace Fan

/-- The complex atlas on algebraic complex points of a regular fan, pulled back from its
analytic realization. Its affine charts have the regular-coordinate complex structures. -/
@[instance_reducible]
noncomputable def algebraicComplexPointChartedSpace :
    ChartedSpace (Fin (Module.finrank ℤ N) → ℂ) Φ.AlgebraicComplexPoint :=
  letI := Φ.analyticChartedSpace hΦ
  (algebraicAnalyticHomeomorph hΦ).isLocalHomeomorph.chartedSpaceComap

/-- The algebraic complex points of a regular fan form a complex manifold. -/
theorem isManifold_algebraicComplexPoint (n : ℕ∞ω) :
    letI := algebraicComplexPointChartedSpace hΦ
    IsManifold 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n Φ.AlgebraicComplexPoint := by
  let := Φ.analyticChartedSpace hΦ
  have := Φ.isManifold_analyticRealization hΦ n
  exact (algebraicAnalyticHomeomorph hΦ).isLocalHomeomorph.isManifold_chartedSpaceComap

/-- The algebraic–analytic comparison is a biholomorphism for the affine-chart complex
structures, at every smoothness order. -/
noncomputable def algebraicAnalyticDiffeomorph (n : ℕ∞ω) :
    letI := algebraicComplexPointChartedSpace hΦ
    letI := Φ.analyticChartedSpace hΦ
    Φ.AlgebraicComplexPoint ≃ₘ^n⟮𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ),
      𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ)⟯ Φ.analyticRealization hΦ := by
  letI := Φ.analyticChartedSpace hΦ
  letI := algebraicComplexPointChartedSpace hΦ
  exact ((algebraicAnalyticHomeomorph hΦ).isLocalHomeomorph.isLocalDiffeomorph_chartedSpaceComap
    (n := n)).diffeomorphOfBijective (algebraicAnalyticHomeomorph hΦ).bijective

/-- The biholomorphism is the existing chartwise algebraic–analytic comparison. -/
@[simp]
theorem coe_algebraicAnalyticDiffeomorph (n : ℕ∞ω) :
    letI := algebraicComplexPointChartedSpace hΦ
    letI := Φ.analyticChartedSpace hΦ
    ⇑(algebraicAnalyticDiffeomorph hΦ n) = algebraicAnalyticEquiv hΦ := by
  simp only [algebraicAnalyticDiffeomorph, coe_diffeomorphOfBijective,
    coe_algebraicAnalyticHomeomorph]

/-- The inverse biholomorphism is the inverse chartwise comparison. -/
@[simp]
theorem coe_algebraicAnalyticDiffeomorph_symm (n : ℕ∞ω) :
    letI := algebraicComplexPointChartedSpace hΦ
    letI := Φ.analyticChartedSpace hΦ
    ⇑(algebraicAnalyticDiffeomorph hΦ n).symm = (algebraicAnalyticEquiv hΦ).symm := by
  let := algebraicComplexPointChartedSpace hΦ
  let := Φ.analyticChartedSpace hΦ
  funext x
  apply (algebraicAnalyticEquiv hΦ).injective
  rw [← coe_algebraicAnalyticDiffeomorph hΦ n, Diffeomorph.apply_symm_apply,
    coe_algebraicAnalyticDiffeomorph, Equiv.apply_symm_apply]

/-- Every algebraic affine chart inclusion is a local biholomorphism for the independently
defined regular-cone structure of any extending basis and finite generating family. In particular,
its local inverse is holomorphic, so these chart inclusions, which cover all algebraic complex
points, characterize the pulled-back complex structure in both directions. -/
theorem isLocalDiffeomorph_ofAffinePoint (σ : Φ.cones) {k l s : ℕ}
    {B : Module.Basis (ToricRay σ.1 ⊕ Fin l) ℤ N}
    (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ))) (κ : ToricRay σ.1 ≃ Fin k)
    (g : AddGeneratingFamily (dualSemigroup Φ.lattice σ.1) s) (n : ℕ∞ω) :
    letI := affinePointTopology g
    letI := coneChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) σ.1 σ.2).toIsToricCone hB κ g
    letI := algebraicComplexPointChartedSpace hΦ
    IsLocalDiffeomorph 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ))
      𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n (AlgebraicComplexPoint.ofAffinePoint σ) := by
  let := affinePointTopology g
  let := coneChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) σ.1 σ.2).toIsToricCone hB κ g
  let := Φ.analyticChartedSpace hΦ
  let := algebraicComplexPointChartedSpace hΦ
  let e := Φ.analyticAffineChartPartialDiffeomorph hΦ σ hB κ g n
  let d := (algebraicAnalyticDiffeomorph hΦ n).symm
  intro x
  have hx : x ∈ e.source := by simp [e]
  have hc := (e.isLocalDiffeomorphAt _ _ _ hx).comp _ _ (d.isLocalDiffeomorph (e x))
  convert hc using 1
  apply funext
  intro y
  simpa only [Function.comp_apply, e, d, analyticAffineChartPartialDiffeomorph_apply,
    coe_algebraicAnalyticDiffeomorph_symm] using
      (algebraicAnalyticEquiv_symm_analyticAffineChartι hΦ σ y).symm

end Fan

namespace FanHom

variable {N' V' : Type} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i' : N' →+ V'} {Ψ : Fan i'} (f : FanHom Φ Ψ) (hΨ : Ψ.IsRegular)

/-- A morphism of regular fans acts holomorphically on the complex points of their schemes. -/
theorem contMDiff_algebraicComplexPointMap (n : ℕ∞ω) :
    letI := Fan.algebraicComplexPointChartedSpace hΦ
    letI := Fan.algebraicComplexPointChartedSpace hΨ
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ)
      𝓘(ℂ, Fin (Module.finrank ℤ N') → ℂ) n f.algebraicComplexPointMap := by
  let := Φ.analyticChartedSpace hΦ
  let := Ψ.analyticChartedSpace hΨ
  let := Fan.algebraicComplexPointChartedSpace hΦ
  let := Fan.algebraicComplexPointChartedSpace hΨ
  exact ((Fan.algebraicAnalyticDiffeomorph hΨ n).symm.contMDiff.comp
    ((f.contMDiff_analyticMap hΦ hΨ n).comp
      (Fan.algebraicAnalyticDiffeomorph hΦ n).contMDiff)).congr fun p ↦ by
        simp only [Function.comp_apply, Fan.coe_algebraicAnalyticDiffeomorph,
          Fan.coe_algebraicAnalyticDiffeomorph_symm, ← f.algebraicAnalyticEquiv_naturality,
          Equiv.symm_apply_apply]

end FanHom

end TauCeti.Toric
