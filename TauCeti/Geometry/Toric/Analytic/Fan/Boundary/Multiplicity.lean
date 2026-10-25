/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Cone.RaySlice
public import TauCeti.Geometry.Toric.Analytic.Fan.Boundary.NormalForm

/-!
# Simple local equations for toric boundary components

At every point of a boundary component of a regular toric fan, there is a holomorphic defining
equation and a holomorphic transverse curve through the point on which that equation is exactly
the parameter. Consequently its restriction to that curve has a simple zero. This makes the
multiplicity-one assertion explicit, including at intersections with other boundary components.

The local equation is the dual basis character of the ray in an extending-basis affine chart.
The curve is `coneChartRaySlice`, transported by the affine chart inclusion; its whole image
lies in the domain of the equation. This uses the coordinate-hyperplane description in
`analyticAffineChartι_mem_analyticBoundaryComponent_iff`, not just a set-theoretic choice of a
function vanishing on the component.

## References

* W. Fulton, *Introduction to Toric Varieties*, §3.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §4.1.
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)

/-- Every boundary component has a holomorphic local defining equation of multiplicity one:
through each of its points there is a holomorphic transverse curve on which the equation is
the parameter itself. This holds also where several components meet. -/
theorem exists_contMDiffOn_analyticBoundaryComponent_eq_zero_transverse_curve
    (ρ : Φ.Ray) {x : Φ.analyticRealization hΦ}
    (hx : x ∈ Φ.analyticBoundaryComponent hΦ ρ) :
    letI := Φ.analyticChartedSpace hΦ
    ∃ (U : Set (Φ.analyticRealization hΦ)) (F : Φ.analyticRealization hΦ → ℂ)
      (γ : ℂ → Φ.analyticRealization hΦ),
      IsOpen U ∧ x ∈ U ∧
      ContMDiffOn 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, ℂ) ∞ F U ∧
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) ∞ γ ∧
      γ 0 = x ∧ (∀ t, γ t ∈ U) ∧
      (∀ y ∈ U, y ∈ Φ.analyticBoundaryComponent hΦ ρ ↔ F y = 0) ∧
      (∀ t, F (γ t) = t) := by
  classical
  let := Φ.analyticChartedSpace hΦ
  obtain ⟨σ, x', rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ x
  -- Read the bundled chart point as its affine algebra homomorphism before applying slice APIs.
  let x0 : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) := x'
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  obtain ⟨l, B, hB⟩ := hσ.exists_basis_sum
  have := ToricRay.finite_of_fg hσ.fg
  let κ := Finite.equivFin (ToricRay σ.1)
  let g := (Φ.analyticChartGenerators σ).2
  let := affinePointTopology g
  let := coneChartedSpace Φ.lattice hσ.toIsToricCone hB κ g
  obtain ⟨hρ, hxρ⟩ :=
    (Φ.analyticAffineChartι_mem_analyticBoundaryComponent_iff hΦ σ hB ρ x').mp hx
  let r := ρ.toToricRay Φ σ hρ
  -- Transport the dual coordinate and its slice through the biholomorphic chart inclusion.
  let m := dualSemigroupCoord Φ.lattice hσ.toIsToricCone hB (Sum.inl r)
  let P := Φ.analyticAffineChartPartialDiffeomorph hΦ σ hB κ g ∞
  let f : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) → ℂ :=
    fun z ↦ z (MonoidAlgebra.single (Multiplicative.ofAdd m) 1)
  let F := f ∘ P.symm
  let γ := Φ.analyticAffineChartι hΦ σ ∘ coneChartRaySlice Φ.lattice hσ.toIsToricCone hB x0 r
  have hP (z : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) :
      P.symm (Φ.analyticAffineChartι hΦ σ z) = z :=
    Φ.analyticAffineChartPartialDiffeomorph_symm_analyticAffineChartι hΦ σ hB κ g ∞ z
  have hF (z : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) :
      F (Φ.analyticAffineChartι hΦ σ z) = f z := congrArg f (hP z)
  have hf : ContMDiff 𝓘(ℂ, (Fin (Nat.card (ToricRay σ.1)) → ℂ) × (Fin l → ℂ))
      𝓘(ℂ, ℂ) ∞ f := contMDiff_apply_single Φ.lattice hσ.toIsToricCone hB κ g m ∞
  -- The inverse-chart computation identifies the zero locus and gives the exact transverse value.
  refine ⟨P.target, F, γ, P.open_target, ?_,
    hf.comp_contMDiffOn P.symm.contMDiffOn, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Φ.analyticAffineChartPartialDiffeomorph_target]
    exact mem_range_self x'
  · exact (Φ.contMDiff_analyticAffineChartι hΦ σ hB κ g ∞).comp
      (contMDiff_coneChartRaySlice Φ.lattice hσ.toIsToricCone hB κ g x' r ∞)
  · have hx0 : (coneChartEquiv Φ.lattice hσ.toIsToricCone hB x0).1 r = 0 := hxρ
    have hslice : coneChartRaySlice Φ.lattice hσ.toIsToricCone hB x0 r 0 = x0 := by
      rw [← hx0, coneChartEquiv_fst_apply, coneChartRaySlice_self]
    exact congrArg (Φ.analyticAffineChartι hΦ σ) hslice
  · intro t
    rw [Φ.analyticAffineChartPartialDiffeomorph_target]
    exact mem_range_self _
  · intro y hy
    rw [Φ.analyticAffineChartPartialDiffeomorph_target] at hy
    obtain ⟨z, rfl⟩ := hy
    rw [Φ.analyticAffineChartι_mem_analyticBoundaryComponent_iff hΦ σ hB ρ z,
      exists_prop_of_true hρ]
    exact (congrArg (fun c : ℂ ↦ c = 0)
      ((coneChartEquiv_fst_apply Φ.lattice hσ.toIsToricCone hB z r).trans (hF z).symm)).to_iff
  · intro t
    have h := hF (coneChartRaySlice Φ.lattice hσ.toIsToricCone hB x0 r t)
    refine h.trans ?_
    simp only [f, m, ← coneChartEquiv_fst_apply,
      coneChartEquiv_coneChartRaySlice, Function.update_self]

end TauCeti.Toric.Fan
