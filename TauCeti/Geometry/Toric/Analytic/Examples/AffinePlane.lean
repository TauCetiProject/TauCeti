/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Examples.AffinePlane
public import TauCeti.Geometry.Toric.Analytic.Examples.AffineRay
public import TauCeti.Geometry.Toric.Analytic.Fan.Product.Manifold

/-!
# The analytic affine plane

The standard product fan of two positive rays realizes as the ordinary complex affine plane.
The equivalence is the fan product comparison followed by the standard coordinate on each
affine-line factor, so both coordinates retain their interpretation as toric characters.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
-/

public section

open scoped ContDiff Manifold
open Multiplicative

namespace TauCeti.Toric

/-- The analytic realization of the standard affine-plane fan is biholomorphic to `ℂ × ℂ`.
The two coordinates are those of its affine-line factors. -/
noncomputable def affinePlaneDiffeomorph (n : ℕ∞ω) :
    letI := affinePlaneFan.analyticChartedSpace isRegular_affinePlaneFan
    Diffeomorph 𝓘(ℂ, Fin (Module.finrank ℤ ((Fin 1 → ℤ) × (Fin 1 → ℤ))) → ℂ)
      (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ))
      (affinePlaneFan.analyticRealization isRegular_affinePlaneFan) (ℂ × ℂ) n := by
  letI := affinePlaneFan.analyticChartedSpace isRegular_affinePlaneFan
  letI := affineRayFan.analyticChartedSpace isRegular_affineRayFan
  let d := affineRayFanDiffeomorph n
  -- The product changes both model vector spaces; `Diffeomorph.prodCongr` requires the second
  -- factor to keep its model vector space, so assemble the product from its component maps.
  let dprod : Diffeomorph
      (𝓘(ℂ, Fin (Module.finrank ℤ (Fin 1 → ℤ)) → ℂ).prod
        𝓘(ℂ, Fin (Module.finrank ℤ (Fin 1 → ℤ)) → ℂ))
      (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ))
      ((affineRayFan.analyticRealization isRegular_affineRayFan) ×
        (affineRayFan.analyticRealization isRegular_affineRayFan)) (ℂ × ℂ) n :=
    { toEquiv := d.toEquiv.prodCongr d.toEquiv
      contMDiff_toFun := (d.contMDiff.comp contMDiff_fst).prodMk
        (d.contMDiff.comp contMDiff_snd)
      contMDiff_invFun := (d.symm.contMDiff.comp contMDiff_fst).prodMk
        (d.symm.contMDiff.comp contMDiff_snd) }
  exact (affineRayFan.analyticProdDiffeomorph affineRayFan
    isRegular_affineRayFan isRegular_affineRayFan n).trans dprod

/-- In affine-plane coordinates, the product comparison evaluates the standard character
coordinate on each factor. -/
@[simp]
theorem affinePlaneDiffeomorph_apply (n : ℕ∞ω)
    (x : affinePlaneFan.analyticRealization isRegular_affinePlaneFan) :
    letI := affinePlaneFan.analyticChartedSpace isRegular_affinePlaneFan
    affinePlaneDiffeomorph n x =
      Prod.map (affineRayFanDiffeomorph n) (affineRayFanDiffeomorph n)
        (affineRayFan.analyticProdHomeomorph affineRayFan
          isRegular_affineRayFan isRegular_affineRayFan x) := by
  simp only [affinePlaneDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    Fan.coe_analyticProdDiffeomorph]
  rfl

/-- On the maximal product chart, the two affine-plane coordinates are the standard character
evaluations of the two affine-ray chart points. -/
theorem affinePlaneDiffeomorph_analyticAffineChartι (n : ℕ∞ω)
    (x y : AffineSemigroupComplexPoint
      (dualSemigroup (isIntegralLattice_intCast 1) affineRayCone)) :
    let z := (affineRayFan.analyticAffineChartProdHomeomorph affineRayFan
      affineRayFanMaxCone affineRayFanMaxCone).symm (x, y)
    affinePlaneDiffeomorph n
      (affinePlaneFan.analyticAffineChartι isRegular_affinePlaneFan
        (affineRayFan.prodCone affineRayFan affineRayFanMaxCone affineRayFanMaxCone) z) =
      (x (MonoidAlgebra.single (ofAdd affineRayCharacter) 1),
        y (MonoidAlgebra.single (ofAdd affineRayCharacter) 1)) := by
  dsimp only
  rw [affinePlaneDiffeomorph_apply,
    Fan.analyticProdHomeomorph_analyticAffineChartι]
  simp only [Homeomorph.apply_symm_apply, Prod.map_apply,
    affineRayFanDiffeomorph_analyticAffineChartι]

end TauCeti.Toric
