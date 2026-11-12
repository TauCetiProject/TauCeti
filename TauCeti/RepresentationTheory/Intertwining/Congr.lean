/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTwist

/-!
# Linear equivalences between spaces of intertwining maps

A multiplicity space `Hom_G(ρ, σ)` is only ever determined up to the representations it compares,
so the comparisons of such spaces come from two operations on the pair `(ρ, σ)`.

* Replacing `ρ` and `σ` by equivalent representations: an equivalence `e₁ : ρ ≃ ρ'` and an
  equivalence `e₂ : σ ≃ σ'` give `Hom_G(ρ, σ) ≃ Hom_G(ρ', σ')`, `f ↦ e₂ ∘ f ∘ e₁⁻¹`. This is the
  unbundled form of `CategoryTheory.Iso.homCongr`, as a linear equivalence.
* Twisting both representations by the same linear character `χ : G →* kˣ`: a linear map
  intertwines `ρ` and `σ` exactly when it intertwines `charTwist χ ρ` and `charTwist χ σ`, because
  the scalars `χ g` are units and occur on both sides. So the two spaces of intertwining maps are
  literally the same linear maps.

## Main definitions

* `Representation.Equiv.intertwiningMapCongr`: transport of intertwining maps along equivalences
  of the source and of the target.
* `Representation.IntertwiningMap.charTwistLinearEquiv`: intertwining maps between two
  representations are the intertwining maps between their twists by a common linear character.
-/

public section

namespace Representation

variable {k G V V' W W' : Type*} [CommSemiring k] [Monoid G]
  [AddCommMonoid V] [Module k V] [AddCommMonoid V'] [Module k V']
  [AddCommMonoid W] [Module k W] [AddCommMonoid W'] [Module k W']
  {ρ : Representation k G V} {ρ' : Representation k G V'}
  {σ : Representation k G W} {σ' : Representation k G W'}

namespace Equiv

/-- **Transport of intertwining maps along equivalences**: equivalences `e₁ : ρ ≃ ρ'` and
`e₂ : σ ≃ σ'` identify the intertwining maps `ρ → σ` with the intertwining maps `ρ' → σ'` by
`f ↦ e₂ ∘ f ∘ e₁⁻¹`. -/
def intertwiningMapCongr (e₁ : Equiv ρ ρ') (e₂ : Equiv σ σ') :
    IntertwiningMap ρ σ ≃ₗ[k] IntertwiningMap ρ' σ' where
  toFun f := e₂.toIntertwiningMap.comp (f.comp e₁.symm.toIntertwiningMap)
  invFun f := e₂.symm.toIntertwiningMap.comp (f.comp e₁.toIntertwiningMap)
  map_add' f g := IntertwiningMap.ext <| LinearMap.ext fun v => by simp
  map_smul' c f := IntertwiningMap.ext <| LinearMap.ext fun v => by simp
  left_inv f := IntertwiningMap.ext <| LinearMap.ext fun v => by simp
  right_inv f := IntertwiningMap.ext <| LinearMap.ext fun v => by simp

@[simp]
theorem intertwiningMapCongr_apply (e₁ : Equiv ρ ρ') (e₂ : Equiv σ σ') (f : IntertwiningMap ρ σ)
    (v : V') : intertwiningMapCongr e₁ e₂ f v = e₂ (f (e₁.symm v)) :=
  (rfl)

@[simp]
theorem intertwiningMapCongr_symm_apply (e₁ : Equiv ρ ρ') (e₂ : Equiv σ σ')
    (f : IntertwiningMap ρ' σ') (v : V) :
    (intertwiningMapCongr e₁ e₂).symm f v = e₂.symm (f (e₁ v)) :=
  (rfl)

end Equiv

namespace IntertwiningMap

variable (χ : G →* kˣ)

/-- A linear map that intertwines the twists of `ρ` and `σ` by a common linear character
intertwines `ρ` and `σ`: the unit `χ g` occurs on both sides and cancels. -/
private theorem isIntertwining_of_charTwist (f : V →ₗ[k] W)
    (hf : ∀ g, f ∘ₗ charTwist χ ρ g = charTwist χ σ g ∘ₗ f) (g : G) :
    f ∘ₗ ρ g = σ g ∘ₗ f := LinearMap.ext fun v => by
  have h := congr(((χ g)⁻¹ : kˣ) • $(hf g) v)
  simpa [charTwist_apply_apply, ← Units.smul_def] using h

/-- **Intertwining maps are unchanged by a common twist**: a linear map intertwines `ρ` and `σ`
exactly when it intertwines `charTwist χ ρ` and `charTwist χ σ`, so the two spaces of
intertwining maps are identified, keeping the underlying linear map. -/
def charTwistLinearEquiv :
    IntertwiningMap ρ σ ≃ₗ[k] IntertwiningMap (charTwist χ ρ) (charTwist χ σ) where
  toFun f := ⟨f.toLinearMap, fun g => LinearMap.ext fun v => by
    simp [f.isIntertwining]⟩
  invFun f := ⟨f.toLinearMap, isIntertwining_of_charTwist χ f.toLinearMap f.isIntertwining'⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_charTwistLinearEquiv (f : IntertwiningMap ρ σ) :
    ⇑(charTwistLinearEquiv χ f) = ⇑f :=
  (rfl)

@[simp]
theorem coe_charTwistLinearEquiv_symm (f : IntertwiningMap (charTwist χ ρ) (charTwist χ σ)) :
    ⇑((charTwistLinearEquiv χ).symm f) = ⇑f :=
  (rfl)

end IntertwiningMap

end Representation
