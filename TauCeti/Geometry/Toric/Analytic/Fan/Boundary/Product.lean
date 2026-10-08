/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Ray
public import TauCeti.Geometry.Toric.Analytic.Fan.Boundary.Naturality
public import TauCeti.Geometry.Toric.Analytic.Fan.Product.Manifold

/-!
# Boundary components of products of analytic toric varieties

Under the canonical biholomorphism from the realization of a product fan to the product of the
two realizations, a boundary component coming from the first factor is the product of that
factor's component with the whole second realization. The analogous statement holds for the
second factor. Together with the decomposition of product-fan rays, these formulas account for
every boundary component of a product.

The nonemptiness hypotheses are necessary to include a factor ray in the product fan: if either
fan is empty, then its product with any fan is empty and has no rays.

## Main declarations

* `TauCeti.Toric.Fan.preimage_analyticProdComparison_boundaryComponent_prod_univ`:
  the pullback formula for a component from the first factor.
* `TauCeti.Toric.Fan.preimage_analyticProdComparison_univ_prod_boundaryComponent`:
  the pullback formula for a component from the second factor.
* `TauCeti.Toric.Fan.image_analyticProdHomeomorph_analyticBoundaryComponent_prodRayInl` and
  `TauCeti.Toric.Fan.image_analyticProdHomeomorph_analyticBoundaryComponent_prodRayInr`:
  the corresponding image formulas.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§2.1--2.2.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1--3.2.
-/

public section

open Set

namespace TauCeti.Toric.Fan

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} (Phi : Fan i) (Psi : Fan i')
  (hPhi : Phi.IsRegular) (hPsi : Psi.IsRegular)

/-- Under the product comparison, the inverse image of a first-factor boundary component times
the whole second realization is the boundary component indexed by the included first-factor
ray. -/
@[simp]
theorem preimage_analyticProdComparison_boundaryComponent_prod_univ
    (hPsi0 : Nonempty Psi.cones) (rho : Phi.Ray) :
    Phi.analyticProdComparison Psi hPhi hPsi ⁻¹'
        (Phi.analyticBoundaryComponent hPhi rho ×ˢ
          (Set.univ : Set (Psi.analyticRealization hPsi))) =
      (Phi.prod Psi).analyticBoundaryComponent (Fan.IsRegular.prod Phi Psi hPhi hPsi)
        (Phi.prodRayInl Psi hPsi0 rho) := by
  ext x
  obtain ⟨xi, hx⟩ := (Phi.prod Psi).exists_mem_analyticConeOrbit
    (Fan.IsRegular.prod Phi Psi hPhi hPsi) x
  obtain ⟨sigma, tau, rfl⟩ := Phi.exists_prodCone_eq Psi xi
  simp only [mem_preimage, mem_prod, mem_univ, and_true, analyticProdComparison_apply]
  rw [
    (FanHom.fst Phi Psi).analyticMap_mem_analyticBoundaryComponent_iff
      (Fan.IsRegular.prod Phi Psi hPhi hPsi) hPhi hx,
    FanHom.fst_leastCone_prodCone,
    (Phi.prod Psi).mem_analyticBoundaryComponent_iff (Fan.IsRegular.prod Phi Psi hPhi hPsi) hx,
    Phi.prodRayInl_toCone_le_prodCone_iff Psi hPsi0]
  exact Subtype.coe_le_coe

/-- Under the product comparison, the inverse image of the whole first realization times a
second-factor boundary component is the boundary component indexed by the included second-factor
ray. -/
@[simp]
theorem preimage_analyticProdComparison_univ_prod_boundaryComponent
    (hPhi0 : Nonempty Phi.cones) (rho : Psi.Ray) :
    Phi.analyticProdComparison Psi hPhi hPsi ⁻¹'
        ((Set.univ : Set (Phi.analyticRealization hPhi)) ×ˢ
          Psi.analyticBoundaryComponent hPsi rho) =
      (Phi.prod Psi).analyticBoundaryComponent (Fan.IsRegular.prod Phi Psi hPhi hPsi)
        (Phi.prodRayInr Psi hPhi0 rho) := by
  ext x
  obtain ⟨xi, hx⟩ := (Phi.prod Psi).exists_mem_analyticConeOrbit
    (Fan.IsRegular.prod Phi Psi hPhi hPsi) x
  obtain ⟨sigma, tau, rfl⟩ := Phi.exists_prodCone_eq Psi xi
  simp only [mem_preimage, mem_prod, mem_univ, true_and, analyticProdComparison_apply]
  rw [
    (FanHom.snd Phi Psi).analyticMap_mem_analyticBoundaryComponent_iff
      (Fan.IsRegular.prod Phi Psi hPhi hPsi) hPsi hx,
    FanHom.snd_leastCone_prodCone,
    (Phi.prod Psi).mem_analyticBoundaryComponent_iff (Fan.IsRegular.prod Phi Psi hPhi hPsi) hx,
    Phi.prodRayInr_toCone_le_prodCone_iff Psi hPhi0]
  exact Subtype.coe_le_coe

/-- The product biholomorphism carries a boundary component from the first factor onto that
component times the whole second realization. -/
theorem image_analyticProdHomeomorph_analyticBoundaryComponent_prodRayInl
    (hPsi0 : Nonempty Psi.cones) (rho : Phi.Ray) :
    Phi.analyticProdHomeomorph Psi hPhi hPsi ''
        (Phi.prod Psi).analyticBoundaryComponent (Fan.IsRegular.prod Phi Psi hPhi hPsi)
          (Phi.prodRayInl Psi hPsi0 rho) =
      Phi.analyticBoundaryComponent hPhi rho ×ˢ Set.univ := by
  have hpre := Phi.preimage_analyticProdComparison_boundaryComponent_prod_univ
    Psi hPhi hPsi hPsi0 rho
  rw [← Phi.coe_analyticProdHomeomorph Psi hPhi hPsi] at hpre
  exact ((Set.preimage_eq_iff_eq_image
    (Phi.analyticProdHomeomorph Psi hPhi hPsi).bijective).mp
      hpre).symm

/-- The product biholomorphism carries a boundary component from the second factor onto the whole
first realization times that component. -/
theorem image_analyticProdHomeomorph_analyticBoundaryComponent_prodRayInr
    (hPhi0 : Nonempty Phi.cones) (rho : Psi.Ray) :
    Phi.analyticProdHomeomorph Psi hPhi hPsi ''
        (Phi.prod Psi).analyticBoundaryComponent (Fan.IsRegular.prod Phi Psi hPhi hPsi)
          (Phi.prodRayInr Psi hPhi0 rho) =
      Set.univ ×ˢ Psi.analyticBoundaryComponent hPsi rho := by
  have hpre := Phi.preimage_analyticProdComparison_univ_prod_boundaryComponent
    Psi hPhi hPsi hPhi0 rho
  rw [← Phi.coe_analyticProdHomeomorph Psi hPhi hPsi] at hpre
  exact ((Set.preimage_eq_iff_eq_image
    (Phi.analyticProdHomeomorph Psi hPhi hPsi).bijective).mp
      hpre).symm

end TauCeti.Toric.Fan
