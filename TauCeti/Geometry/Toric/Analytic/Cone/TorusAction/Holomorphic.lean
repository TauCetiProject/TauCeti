/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import TauCeti.Geometry.Toric.Analytic.Cone.Manifold
public import TauCeti.Geometry.Toric.Analytic.Cone.TorusAction.Basic
public import TauCeti.Geometry.Toric.Analytic.Torus.Manifold

/-!
# Holomorphy of the torus action on a regular affine toric chart

The coordinate-free complex torus acts on the complex points of every affine toric scheme.
For a regular cone, this action is jointly holomorphic when the torus and the affine chart carry
their named complex structures.  In an extending integral basis, each target coordinate is the
product of a holomorphic character evaluation on the torus with one ambient cone-chart coordinate.

This is the affine input for gluing the torus action on the analytic realization of a finite
regular fan.  It is stated for arbitrary presentations of the character lattice and arbitrary
finite monomial presentations of the affine complex points, so later gluing does not depend on
either coordinate choice.

## Main declarations

* `TauCeti.Toric.contMDiff_smul_coneChartedSpace`: the coordinate-free complex-torus action on a
  regular affine toric chart is holomorphic to every differentiability order.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1, 3.1 and 3.2.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.Toric

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] {i : N →+ V} {σ : PointedCone ℝ V} {s k l : ℕ}

/-- The coordinate-free complex-torus action on the complex points of a regular cone is
holomorphic.  The source is the product of the torus and affine-chart structures determined by
`e`, `g`, `hB`, and `κ`; the target has the affine-chart structure determined by `g`, `hB`, and
`κ`. -/
theorem contMDiff_smul_coneChartedSpace (e : IntegralCharacter N ≃+ (ι →₀ ℤ))
    (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    {B : Module.Basis (ToricRay σ ⊕ Fin l) ℤ N}
    (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ)))
    (κ : ToricRay σ ≃ Fin k)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s) (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    let _ := affinePointTopology g
    let _ := coneChartedSpace hi hσ hB κ g
    ContMDiff (𝓘(ℂ, ι → ℂ).prod 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)))
      𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) n
      (fun p : ComplexTorus N × AffineSemigroupComplexPoint (dualSemigroup hi σ) ↦ p.1 • p.2) := by
  let _ := complexTorusChartedSpace e
  let _ := affinePointTopology g
  let _ := coneChartedSpace hi hσ hB κ g
  have hcone : ContMDiff 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ))
      𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) n (coneChartAmbient hi hσ hB κ) :=
    contMDiff_coneChartAmbient hi hσ hB κ g n
  rw [contMDiff_prod_module_iff] at hcone
  have hconeFst := hcone.1
  rw [contMDiff_pi_space] at hconeFst
  have hconeSnd := hcone.2
  rw [contMDiff_pi_space] at hconeSnd
  have hfst : ContMDiff (𝓘(ℂ, ι → ℂ).prod 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)))
      𝓘(ℂ, ι → ℂ) n
      (fun p : ComplexTorus N × AffineSemigroupComplexPoint (dualSemigroup hi σ) ↦ p.1) :=
    contMDiff_fst
  have hsnd : ContMDiff (𝓘(ℂ, ι → ℂ).prod 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)))
      𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) n
      (fun p : ComplexTorus N × AffineSemigroupComplexPoint (dualSemigroup hi σ) ↦ p.2) :=
    contMDiff_snd
  apply contMDiff_of_comp_coneChartAmbient hi hσ hB κ
    (𝓘(ℂ, ι → ℂ).prod 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ))) g
    (fun p : ComplexTorus N × AffineSemigroupComplexPoint (dualSemigroup hi σ) ↦ p.1 • p.2) n
  rw [contMDiff_prod_module_iff]
  constructor
  · rw [contMDiff_pi_space]
    intro a
    simp only [Function.comp_apply]
    have hT :=
      (contMDiff_characterEvaluation e (B.coord (Sum.inl (κ.symm a))).toAddMonoidHom n).comp hfst
    have hT' := Units.contMDiff_val.comp hT
    have hX : ContMDiff (𝓘(ℂ, ι → ℂ).prod 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)))
        𝓘(ℂ, ℂ) n
        (fun p : ComplexTorus N × AffineSemigroupComplexPoint (dualSemigroup hi σ) ↦
          (coneChartAmbient hi hσ hB κ p.2).1 a) :=
      (hconeFst a).comp hsnd
    refine ((contMDiff_mul 𝓘(ℂ) n).comp (hT'.prodMk hX)).congr fun p ↦ ?_
    rw [coneChartAmbient_fst_apply, coneChartEquiv_smul_fst]
    simp [Function.comp_apply]
  · rw [contMDiff_pi_space]
    intro c
    simp only [Function.comp_apply]
    have hT :=
      (contMDiff_characterEvaluation e (B.coord (Sum.inr c)).toAddMonoidHom n).comp hfst
    have hT' := Units.contMDiff_val.comp hT
    have hX : ContMDiff (𝓘(ℂ, ι → ℂ).prod 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)))
        𝓘(ℂ, ℂ) n
        (fun p : ComplexTorus N × AffineSemigroupComplexPoint (dualSemigroup hi σ) ↦
          (coneChartAmbient hi hσ hB κ p.2).2 c) :=
      (hconeSnd c).comp hsnd
    refine ((contMDiff_mul 𝓘(ℂ) n).comp (hT'.prodMk hX)).congr fun p ↦ ?_
    rw [coneChartAmbient_snd_apply, coneChartEquiv_smul_snd]
    simp [Function.comp_apply]

end TauCeti.Toric
