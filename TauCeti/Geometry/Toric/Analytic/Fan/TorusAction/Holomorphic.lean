/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Cone.TorusAction.Holomorphic
public import TauCeti.Geometry.Toric.Analytic.Fan.Manifold
public import TauCeti.Geometry.Toric.Analytic.Fan.TorusAction.Basic

/-!
# The torus action on a fan realization is holomorphic

The coordinate-free complex torus acts on the analytic realization of a regular fan by translating
points of the affine charts. This file proves that the action map
`ComplexTorus N × X_Φ → X_Φ` is holomorphic, for the complex structure of the realization and the
complex structure of the torus given by any free presentation of its character lattice.

Holomorphy is local. Near a point of the image of the affine chart of a cone `σ`, the action is the
affine torus action on that chart, conjugated by the inclusion of the chart, which is a
biholomorphism onto its open image. The affine action is holomorphic for the complex structure of
an integral basis extending the primitive ray generators of `σ`.

## Main declarations

* `TauCeti.Toric.Fan.contMDiffSMul_complexTorus_analyticRealization`: the complex torus acts
  holomorphically on the analytic realization of a regular fan.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1–3.2.
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} {ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] [Fintype ι]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular) (e : IntegralCharacter N ≃+ (ι →₀ ℤ))

/-- The coordinate-free complex torus acts holomorphically on the analytic realization of a
regular fan. The torus carries the complex structure of a free presentation of its character
lattice, and the realization its complex manifold structure modelled on `ℂ ^ n`. -/
theorem contMDiffSMul_complexTorus_analyticRealization (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    letI := Φ.analyticChartedSpace hΦ
    ContMDiffSMul 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n (ComplexTorus N)
      (Φ.analyticRealization hΦ) := by
  let _ := complexTorusChartedSpace e
  let _ := Φ.analyticChartedSpace hΦ
  refine ⟨fun p ↦ ?_⟩
  obtain ⟨σ, x, hx⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ p.2
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  obtain ⟨l, B, hB⟩ := hσ.exists_basis_sum
  have : Finite (ToricRay σ.1) := ToricRay.finite_of_fg hσ.fg
  let κ := Finite.equivFin (ToricRay σ.1)
  let g := (analyticChartGenerators Φ σ).2
  let _ := affinePointTopology g
  let _ := coneChartedSpace Φ.lattice hσ.toIsToricCone hB κ g
  let P := Φ.analyticAffineChartPartialDiffeomorph hΦ σ hB κ g n
  have hP : P.target = range (Φ.analyticAffineChartι hΦ σ) :=
    Φ.analyticAffineChartPartialDiffeomorph_target hΦ σ hB κ g n
  -- On the image of the chart, the action is the affine action conjugated by the chart inclusion.
  have hsmul : ContMDiff (𝓘(ℂ, ι → ℂ).prod 𝓘(ℂ, (Fin _ → ℂ) × (Fin l → ℂ)))
      𝓘(ℂ, (Fin _ → ℂ) × (Fin l → ℂ)) n
      fun q : ComplexTorus N × AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) ↦
        q.1 • q.2 :=
    (contMDiffSMul_complexTorus_coneChartedSpace Φ.lattice hσ.toIsToricCone hB κ g e
      n).contMDiff_smul
  have hsymm : ContMDiffOn (𝓘(ℂ, ι → ℂ).prod 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ))
      (𝓘(ℂ, ι → ℂ).prod 𝓘(ℂ, (Fin _ → ℂ) × (Fin l → ℂ))) n
      (fun q : ComplexTorus N × Φ.analyticRealization hΦ ↦ (q.1, P.symm q.2))
      (univ ×ˢ P.target) :=
    contMDiffOn_fst.prodMk (P.symm.contMDiffOn.comp contMDiffOn_snd fun _ hq ↦ hq.2)
  have hloc := (Φ.contMDiff_analyticAffineChartι hΦ σ hB κ g n).comp_contMDiffOn
    (hsmul.comp_contMDiffOn hsymm)
  have hmem : univ ×ˢ P.target ∈ 𝓝 p :=
    (isOpen_univ.prod P.open_target).mem_nhds ⟨mem_univ _, hP ▸ ⟨x, hx⟩⟩
  refine (hloc.contMDiffAt hmem).congr_of_eventuallyEq ?_
  filter_upwards [hmem] with ⟨t, z⟩ hz
  obtain ⟨y, rfl⟩ := hP ▸ hz.2
  have hPy : P.symm (Φ.analyticAffineChartι hΦ σ y) = y := by
    rw [← Φ.analyticAffineChartPartialDiffeomorph_apply hΦ σ hB κ g n y]
    exact P.left_inv ((Φ.analyticAffineChartPartialDiffeomorph_source hΦ σ hB κ g n).symm ▸
      mem_univ y)
  simp only [Function.comp_apply, hPy, smul_analyticAffineChartι]
  -- The torus action on the chart is, by construction, the action on its complex points.
  rfl

end TauCeti.Toric.Fan
