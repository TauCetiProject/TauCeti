/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Character
public import TauCeti.Geometry.Toric.Analytic.Fan.Product.Basic

/-!
# Characters of product toric realizations

An integral character `m` of the product lattice `N × N'` splits as the sum of its restrictions
`m ∘ inl` and `m ∘ inr` to the two lattice factors. When these restrictions are nonnegative on the
cones of two regular fans `Φ` and `Ψ`, the character is nonnegative on the cones of `Φ.prod Ψ`,
and under the canonical product homeomorphism its holomorphic character function is the product
of the character functions of the two restrictions. This is the character formula of the product
of two toric realizations, alongside the corresponding orbit formula
`TauCeti.Toric.Fan.image_analyticProdHomeomorph_analyticConeOrbit_prodCone`.

## Main declarations

* `TauCeti.Toric.Fan.analyticCharacter_prod`: the character function of the product realization
  at a point is the product of the factor character functions at its two components.
* `TauCeti.Toric.Fan.analyticCharacter_analyticProdHomeomorph_symm`: the same formula, evaluated
  at the point of the product realization with prescribed components.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2 and 3.1.
-/

public section

namespace TauCeti.Toric.Fan

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} (Φ : Fan i) (Ψ : Fan i')
  (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (m : IntegralCharacter (N × N'))
  (h₁ : ∀ σ : Φ.cones, m.comp (AddMonoidHom.inl N N') ∈ dualSemigroup Φ.lattice σ.1)
  (h₂ : ∀ τ : Ψ.cones, m.comp (AddMonoidHom.inr N N') ∈ dualSemigroup Ψ.lattice τ.1)

/-- Under the canonical product homeomorphism, the character function of a character of the
product lattice is the product of the character functions of its restrictions to the two
lattice factors. -/
-- Not a simp lemma: the factor hypotheses `h₁` and `h₂` enter the left-hand side only through a
-- proof, so `simp` cannot instantiate them.
theorem analyticCharacter_prod (x : (Φ.prod Ψ).analyticRealization (IsRegular.prod Φ Ψ hΦ hΨ)) :
    (Φ.prod Ψ).analyticCharacter (IsRegular.prod Φ Ψ hΦ hΨ) m
        (Φ.mem_dualSemigroup_prod_of_comp_inl_of_comp_inr Ψ h₁ h₂) x =
      Φ.analyticCharacter hΦ _ h₁ (Φ.analyticProdHomeomorph Ψ hΦ hΨ x).1 *
        Ψ.analyticCharacter hΨ _ h₂ (Φ.analyticProdHomeomorph Ψ hΦ hΨ x).2 := by
  simp only [coe_analyticProdHomeomorph, analyticProdComparison_apply,
    FanHom.analyticCharacter_analyticMap, ← analyticCharacter_add]
  -- The product character is the sum of its two restrictions pulled back along the projections.
  congr 2
  ext x
  simp [← map_add]

/-- The character function of a character of the product lattice, at the point of the product
realization with components `a` and `b`, is the product of the character functions of its two
restrictions at `a` and `b`. -/
theorem analyticCharacter_analyticProdHomeomorph_symm (a : Φ.analyticRealization hΦ)
    (b : Ψ.analyticRealization hΨ) :
    (Φ.prod Ψ).analyticCharacter (IsRegular.prod Φ Ψ hΦ hΨ) m
        (Φ.mem_dualSemigroup_prod_of_comp_inl_of_comp_inr Ψ h₁ h₂)
        ((Φ.analyticProdHomeomorph Ψ hΦ hΨ).symm (a, b)) =
      Φ.analyticCharacter hΦ _ h₁ a * Ψ.analyticCharacter hΨ _ h₂ b := by
  rw [analyticCharacter_prod, Homeomorph.apply_symm_apply]

end TauCeti.Toric.Fan
