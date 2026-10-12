/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import TauCeti.Geometry.Toric.Analytic.Character.Action
public import TauCeti.Geometry.Toric.Analytic.Cone.Manifold
public import TauCeti.Geometry.Toric.Analytic.Torus.Manifold

/-!
# The torus action on a regular affine chart is holomorphic

The coordinate-free complex torus `ComplexTorus N` acts on the complex points of the affine toric
scheme of a toric cone `σ`: a torus point `t` multiplies the value of a complex point on the
monomial of `m` in the dual semigroup by the character value `t m`. For a regular cone, the torus
carries the complex structure of a free presentation of its character lattice and the affine chart
carries the complex structure of an extending basis. This file proves that the action map
`ComplexTorus N × U_σ → U_σ` is holomorphic for these structures.

Since a map into the affine chart is holomorphic exactly when its values on all monomials are, it
suffices that `(t, x) ↦ t m * x(m)` is holomorphic, which holds because character evaluation is
holomorphic on the torus and monomials are holomorphic on the chart.

## Main declarations

* `TauCeti.Toric.contMDiffSMul_complexTorus_coneChartedSpace`: the torus acts holomorphically on
  the complex points of a regular cone.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.3 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.3 and 3.1.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.Toric

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] [Fintype ι]
  {i : N →+ V} {σ : PointedCone ℝ V} {s k l : ℕ}
  (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
  {B : Module.Basis (ToricRay σ ⊕ Fin l) ℤ N} (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ)))
  (κ : ToricRay σ ≃ Fin k) (g : AddGeneratingFamily (dualSemigroup hi σ) s)
  (e : IntegralCharacter N ≃+ (ι →₀ ℤ))

/-- The coordinate-free complex torus acts holomorphically on the complex points of the affine
toric scheme of a regular cone. The torus carries the complex structure of a free presentation of
its character lattice, and the affine chart that of an integral basis extending the primitive ray
generators. -/
theorem contMDiffSMul_complexTorus_coneChartedSpace (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    let _ := affinePointTopology g
    let _ := coneChartedSpace hi hσ hB κ g
    ContMDiffSMul 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) n (ComplexTorus N)
      (AffineSemigroupComplexPoint (dualSemigroup hi σ)) := by
  let _ := complexTorusChartedSpace e
  let _ := affinePointTopology g
  let _ := coneChartedSpace hi hσ hB κ g
  refine ⟨(contMDiff_iff_forall_contMDiff_apply_single hi hσ hB κ g).2 fun m ↦ ?_⟩
  simp only [AffineSemigroupComplexPoint.ambient_smul_apply_single]
  refine ContMDiff.mul ?_ ((contMDiff_apply_single hi hσ hB κ g m n).comp contMDiff_snd)
  -- The value of a torus point on `m` is the evaluation of the character `m`.
  exact ((Units.contMDiff_val (n := n)).comp
    ((contMDiff_characterEvaluation e m n).comp contMDiff_fst)).congr fun p ↦ by simp

end TauCeti.Toric
