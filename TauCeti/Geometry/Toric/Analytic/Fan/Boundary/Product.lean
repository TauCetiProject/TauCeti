/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Product.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Boundary.Naturality

/-!
# Boundary components of product toric realizations

Under the canonical homeomorphism between the realization of a product of regular fans and the
product of their realizations, boundary components are products. The corresponding formulas for
distinguished points and torus orbits are in `TauCeti.Geometry.Toric.Analytic.Fan.Orbit.Product`.

This homeomorphism is the underlying map of the canonical complex-manifold equivalence
`TauCeti.Toric.Fan.analyticProdDiffeomorph`, established in `Product.Manifold`.
The lemma `TauCeti.Toric.Fan.coe_analyticProdDiffeomorph` identifies the maps definitionally,
so rewriting with it applies the formulas below to the biholomorphism as well.
For canonical product rays, supply the cone identifications from `Product.Ray` directly.

A ray of the product fan is a ray of one factor times the zero cone of the other, by
`TauCeti.Toric.Fan.prodRayEquiv`. Its boundary component is the product of the component of
that factor ray with the whole realization of the other factor, so the boundary components of a
product are exactly the pullbacks of the boundary components of its two factors.

The boundary statements take the product ray together with the identification of its cone, so
they need no nonemptiness hypothesis; `TauCeti.Toric.Fan.toCone_prodRayEquiv_symm_inl` and
`TauCeti.Toric.Fan.toCone_prodRayEquiv_symm_inr` supply that identification for the rays
given by `TauCeti.Toric.Fan.prodRayEquiv`.

## Main declarations

* `TauCeti.Toric.Fan.image_analyticProdHomeomorph_analyticBoundaryComponent_of_eq_prod_bot` and
  `TauCeti.Toric.Fan.image_analyticProdHomeomorph_analyticBoundaryComponent_of_eq_bot_prod`:
  boundary components of the product are products of a factor component with a whole factor.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4, 2.1 and 3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1--3.2 and 4.1.
-/

public section

open Set

namespace TauCeti.Toric.Fan

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} (Φ : Fan i) (Ψ : Fan i')
  (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

/-- The boundary component of a product ray `ρ × 0` is the preimage of the component of `ρ` times
the whole second factor. -/
theorem preimage_analyticProdHomeomorph_analyticBoundaryComponent_prod_univ {ρ : Φ.Ray}
    {ξ : (Φ.prod Ψ).Ray} (h : ξ.toCone.1 = ρ.toCone.1.prod ⊥) :
    Φ.analyticProdHomeomorph Ψ hΦ hΨ ⁻¹' (Φ.analyticBoundaryComponent hΦ ρ ×ˢ univ) =
      (Φ.prod Ψ).analyticBoundaryComponent (Fan.IsRegular.prod Φ Ψ hΦ hΨ) ξ := by
  ext x
  obtain ⟨ζ, hx⟩ := (Φ.prod Ψ).exists_mem_analyticConeOrbit _ x
  obtain ⟨σ, τ, rfl⟩ := Φ.exists_prodCone_eq Ψ ζ
  simp [(FanHom.fst Φ Ψ).analyticMap_mem_analyticBoundaryComponent_iff _ hΦ hx,
    (Φ.prod Ψ).mem_analyticBoundaryComponent_iff _ hx, ← Subtype.coe_le_coe, h,
    Submodule.le_prod_iff]

/-- The boundary component of a product ray `0 × ρ` is the preimage of the whole first factor
times the component of `ρ`. -/
theorem preimage_analyticProdHomeomorph_analyticBoundaryComponent_univ_prod {ρ : Ψ.Ray}
    {ξ : (Φ.prod Ψ).Ray} (h : ξ.toCone.1 = (⊥ : PointedCone ℝ V).prod ρ.toCone.1) :
    Φ.analyticProdHomeomorph Ψ hΦ hΨ ⁻¹' (univ ×ˢ Ψ.analyticBoundaryComponent hΨ ρ) =
      (Φ.prod Ψ).analyticBoundaryComponent (Fan.IsRegular.prod Φ Ψ hΦ hΨ) ξ := by
  ext x
  obtain ⟨ζ, hx⟩ := (Φ.prod Ψ).exists_mem_analyticConeOrbit _ x
  obtain ⟨σ, τ, rfl⟩ := Φ.exists_prodCone_eq Ψ ζ
  simp [(FanHom.snd Φ Ψ).analyticMap_mem_analyticBoundaryComponent_iff _ hΨ hx,
    (Φ.prod Ψ).mem_analyticBoundaryComponent_iff _ hx, ← Subtype.coe_le_coe, h,
    Submodule.le_prod_iff]

/-- **Boundary components of a product, first factor.** The product homeomorphism carries the
boundary component of a product ray `ρ × 0` onto the component of `ρ` times the whole second
factor. -/
theorem image_analyticProdHomeomorph_analyticBoundaryComponent_of_eq_prod_bot {ρ : Φ.Ray}
    {ξ : (Φ.prod Ψ).Ray} (h : ξ.toCone.1 = ρ.toCone.1.prod ⊥) :
    Φ.analyticProdHomeomorph Ψ hΦ hΨ ''
        (Φ.prod Ψ).analyticBoundaryComponent (Fan.IsRegular.prod Φ Ψ hΦ hΨ) ξ =
      Φ.analyticBoundaryComponent hΦ ρ ×ˢ univ := by
  rw [← Φ.preimage_analyticProdHomeomorph_analyticBoundaryComponent_prod_univ Ψ hΦ hΨ h,
    Homeomorph.image_preimage]

/-- **Boundary components of a product, second factor.** The product homeomorphism carries the
boundary component of a product ray `0 × ρ` onto the whole first factor times the component of
`ρ`. -/
theorem image_analyticProdHomeomorph_analyticBoundaryComponent_of_eq_bot_prod {ρ : Ψ.Ray}
    {ξ : (Φ.prod Ψ).Ray} (h : ξ.toCone.1 = (⊥ : PointedCone ℝ V).prod ρ.toCone.1) :
    Φ.analyticProdHomeomorph Ψ hΦ hΨ ''
        (Φ.prod Ψ).analyticBoundaryComponent (Fan.IsRegular.prod Φ Ψ hΦ hΨ) ξ =
      univ ×ˢ Ψ.analyticBoundaryComponent hΨ ρ := by
  rw [← Φ.preimage_analyticProdHomeomorph_analyticBoundaryComponent_univ_prod Ψ hΦ hΨ h,
    Homeomorph.image_preimage]

end TauCeti.Toric.Fan
