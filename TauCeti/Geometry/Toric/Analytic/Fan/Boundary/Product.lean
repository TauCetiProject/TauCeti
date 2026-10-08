/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Boundary.Naturality
public import TauCeti.Geometry.Toric.Analytic.Fan.Product

/-!
# Orbits and boundary components of product toric realizations

Under the canonical homeomorphism between the realization of a product of regular fans and the
product of their realizations, torus orbits and boundary components are products. The orbit of
a product cone `σ × τ` is the product of the orbits of `σ` and `τ`, and the distinguished point
of `σ × τ` is the pair of distinguished points.

A ray of the product fan is a ray of one factor times the zero cone of the other, by
`TauCeti.Toric.Fan.prodRayEquiv`. Its boundary component is the product of the component of
that factor ray with the whole realization of the other factor, so the boundary components of a
product are exactly the pullbacks of the boundary components of its two factors.

The boundary statements take the product ray together with the identification of its cone, so
they need no nonemptiness hypothesis; `TauCeti.Toric.Fan.coe_toCone_prodRayEquiv_symm_inl` and
`TauCeti.Toric.Fan.coe_toCone_prodRayEquiv_symm_inr` supply that identification for the rays
given by `TauCeti.Toric.Fan.prodRayEquiv`.

## Main declarations

* `TauCeti.Toric.Fan.analyticProdHomeomorph_analyticDistinguishedPoint`: distinguished points of
  product cones are pairs of distinguished points.
* `TauCeti.Toric.Fan.image_analyticProdHomeomorph_analyticConeOrbit_prodCone`: the orbit of a
  product cone is the product of the factor orbits.
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

/-- The distinguished point of a product cone corresponds to the pair of distinguished points of
its factors. -/
@[simp]
theorem analyticProdHomeomorph_analyticDistinguishedPoint (σ : Φ.cones) (τ : Ψ.cones) :
    Φ.analyticProdHomeomorph Ψ hΦ hΨ
        ((Φ.prod Ψ).analyticDistinguishedPoint (Fan.IsRegular.prod Φ Ψ hΦ hΨ)
          (Φ.prodCone Ψ σ τ)) =
      (Φ.analyticDistinguishedPoint hΦ σ, Ψ.analyticDistinguishedPoint hΨ τ) := by
  simp only [coe_analyticProdHomeomorph, analyticProdComparison_apply,
    FanHom.analyticMap_analyticDistinguishedPoint, FanHom.fst_leastCone_prodCone,
    FanHom.snd_leastCone_prodCone]

/-- A point of the product realization lies in the orbit of a product cone exactly when its two
components lie in the orbits of the factor cones. -/
theorem analyticProdHomeomorph_mem_prod_analyticConeOrbit_iff {σ : Φ.cones} {τ : Ψ.cones}
    {x : (Φ.prod Ψ).analyticRealization (Fan.IsRegular.prod Φ Ψ hΦ hΨ)} :
    Φ.analyticProdHomeomorph Ψ hΦ hΨ x ∈
        Φ.analyticConeOrbit hΦ σ ×ˢ Ψ.analyticConeOrbit hΨ τ ↔
      x ∈ (Φ.prod Ψ).analyticConeOrbit (Fan.IsRegular.prod Φ Ψ hΦ hΨ) (Φ.prodCone Ψ σ τ) := by
  -- A point of the orbit of `σ' × τ'` maps into the product of the factor orbits.
  have hmem {σ' : Φ.cones} {τ' : Ψ.cones} {y : (Φ.prod Ψ).analyticRealization _}
      (hy : y ∈ (Φ.prod Ψ).analyticConeOrbit _ (Φ.prodCone Ψ σ' τ')) :
      Φ.analyticProdHomeomorph Ψ hΦ hΨ y ∈
        Φ.analyticConeOrbit hΦ σ' ×ˢ Ψ.analyticConeOrbit hΨ τ' := by
    rw [coe_analyticProdHomeomorph, analyticProdComparison_apply]
    exact ⟨((FanHom.fst Φ Ψ).analyticMap_mem_analyticConeOrbit_iff _ hΦ hy).2
        (FanHom.fst_leastCone_prodCone σ' τ'),
      ((FanHom.snd Φ Ψ).analyticMap_mem_analyticConeOrbit_iff _ hΨ hy).2
        (FanHom.snd_leastCone_prodCone σ' τ')⟩
  refine ⟨fun h ↦ ?_, hmem⟩
  obtain ⟨ξ, hx⟩ := (Φ.prod Ψ).exists_mem_analyticConeOrbit _ x
  obtain ⟨σ', τ', rfl⟩ := Φ.exists_prodCone_eq Ψ ξ
  -- Orbits of a regular fan are disjoint, so the factor cones are `σ` and `τ`.
  rwa [Φ.eq_of_mem_analyticConeOrbit hΦ h.1 (hmem hx).1,
    Ψ.eq_of_mem_analyticConeOrbit hΨ h.2 (hmem hx).2]

/-- The orbit of a product cone is the preimage of the product of the factor orbits. -/
theorem preimage_analyticProdHomeomorph_prod_analyticConeOrbit (σ : Φ.cones) (τ : Ψ.cones) :
    Φ.analyticProdHomeomorph Ψ hΦ hΨ ⁻¹'
        (Φ.analyticConeOrbit hΦ σ ×ˢ Ψ.analyticConeOrbit hΨ τ) =
      (Φ.prod Ψ).analyticConeOrbit (Fan.IsRegular.prod Φ Ψ hΦ hΨ) (Φ.prodCone Ψ σ τ) := by
  ext x
  exact Φ.analyticProdHomeomorph_mem_prod_analyticConeOrbit_iff Ψ hΦ hΨ

/-- **Orbits of a product.** The product homeomorphism carries the orbit of a product cone onto
the product of the orbits of its factors. -/
theorem image_analyticProdHomeomorph_analyticConeOrbit_prodCone (σ : Φ.cones) (τ : Ψ.cones) :
    Φ.analyticProdHomeomorph Ψ hΦ hΨ ''
        (Φ.prod Ψ).analyticConeOrbit (Fan.IsRegular.prod Φ Ψ hΦ hΨ) (Φ.prodCone Ψ σ τ) =
      Φ.analyticConeOrbit hΦ σ ×ˢ Ψ.analyticConeOrbit hΨ τ := by
  rw [← Φ.preimage_analyticProdHomeomorph_prod_analyticConeOrbit Ψ hΦ hΨ σ τ,
    Homeomorph.image_preimage]

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
