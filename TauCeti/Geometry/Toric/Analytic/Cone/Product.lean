/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import TauCeti.Geometry.Toric.Analytic.AffinePoint.Product
public import TauCeti.Geometry.Toric.Analytic.Cone.Manifold
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Product

/-!
# Holomorphic products of affine toric charts

The inverse affine product comparison multiplies the monomial values of its two arguments.
It is holomorphic for the complex structures of arbitrary extending bases of the two factor
cones and of their product. This allows the product comparison of fan realizations to be
upgraded from a homeomorphism to a biholomorphism without choosing compatible bases.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2 and 3.1.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.Toric.AffineSemigroupComplexPoint

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'}
  (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
  (hσ : IsToricCone i σ) (hτ : IsToricCone i' τ)
  {k l k' l' k'' l'' s s' s'' : ℕ}
  {B : Module.Basis (ToricRay σ ⊕ Fin l) ℤ N}
  {C : Module.Basis (ToricRay τ ⊕ Fin l') ℤ N'}
  {D : Module.Basis (ToricRay (σ.prod τ) ⊕ Fin l'') ℤ (N × N')}
  (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ)))
  (hC : ∀ ρ, IsPrimitiveGenerator i' ρ (C (Sum.inl ρ)))
  (hD : ∀ ρ, IsPrimitiveGenerator (i.prodMap i') ρ (D (Sum.inl ρ)))
  (κ : ToricRay σ ≃ Fin k) (κ' : ToricRay τ ≃ Fin k')
  (κ'' : ToricRay (σ.prod τ) ≃ Fin k'')

/-- Combining two affine complex points by multiplying their monomial values is holomorphic
for the complex structures of any extending bases, including an independently chosen basis
of the product cone. -/
theorem contMDiff_prodEquiv_symm
    (g : AddGeneratingFamily (dualSemigroup hi σ) s)
    (g' : AddGeneratingFamily (dualSemigroup hi' τ) s')
    (g'' : AddGeneratingFamily (dualSemigroup (hi.prod hi') (σ.prod τ)) s'')
    (n : ℕ∞ω) :
    letI := affinePointTopology g
    letI := coneChartedSpace hi hσ hB κ g
    letI := affinePointTopology g'
    letI := coneChartedSpace hi' hτ hC κ' g'
    letI := affinePointTopology g''
    letI := coneChartedSpace (hi.prod hi') (hσ.prod hτ) hD κ'' g''
    ContMDiff
      (𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)).prod
        𝓘(ℂ, (Fin k' → ℂ) × (Fin l' → ℂ)))
      𝓘(ℂ, (Fin k'' → ℂ) × (Fin l'' → ℂ)) n
      (prodEquiv (dualSemigroupProdEquiv hi hi' σ τ)).symm := by
  let _ := affinePointTopology g
  let _ := coneChartedSpace hi hσ hB κ g
  let _ := affinePointTopology g'
  let _ := coneChartedSpace hi' hτ hC κ' g'
  let _ := affinePointTopology g''
  let _ := coneChartedSpace (hi.prod hi') (hσ.prod hτ) hD κ'' g''
  refine (contMDiff_iff_forall_contMDiff_apply_single (hi.prod hi') (hσ.prod hτ)
    hD κ'' g'').2 fun m ↦ ?_
  simp only [prodEquiv_symm_apply_single]
  exact ((contMDiff_apply_single hi hσ hB κ g _ n).comp contMDiff_fst).mul
    ((contMDiff_apply_single hi' hτ hC κ' g' _ n).comp contMDiff_snd)

end TauCeti.Toric.AffineSemigroupComplexPoint
