/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.LinearAlgebra.Finsupp.SignReversal

/-!
# Linear maps between free modules with integer matrices

For integers `κ p q` indexed by `p : α` and `q : β`, with `β` finite, and any ring `R`,
`Finsupp.intMatrixMap R κ` is the `R`-linear map from `α →₀ R` to `β →₀ R` whose matrix is `κ`:
it sends `single p a` to the finitely supported function `q ↦ a * κ p q`. Since its entries are
integers, it commutes with every change of coefficients along an additive map, and multiplying the
entries by signs at the source and at the target conjugates it by sign reversals. Morse boundaries
and the maps between Morse chain modules over a ring are maps of this kind.

## Main definitions

* `Finsupp.intMatrixMap R κ`: the `R`-linear map from `α →₀ R` to `β →₀ R` with integer matrix
  `κ`.

## Main results

* `Finsupp.intMatrixMap_apply`, `Finsupp.intMatrixMap_single_apply`: its values.
* `Finsupp.mapRange_intMatrixMap`: it commutes with changes of coefficients.
* `Finsupp.intMatrixMap_eq_signReversal_comp`: multiplying the entries by signs on `S₀` and on
  `S₁` conjugates it by the sign reversals `Finsupp.signReversal` on `S₀` and on `S₁`.
-/

public section

namespace Finsupp

variable {α β : Type*} [Finite β] (R : Type*) [Ring R]

/-- The **`R`-linear map with integer matrix `κ`**, from the free `R`-module on `α` to that on the
finite type `β`: it sends `single p a` to the function `q ↦ a * κ p q`. -/
noncomputable def intMatrixMap (κ : α → β → ℤ) : (α →₀ R) →ₗ[R] (β →₀ R) :=
  linearCombination R fun p ↦ equivFunOnFinite.symm fun q ↦ (κ p q : R)

variable {R} (κ : α → β → ℤ)

/-- The coefficient of `q` in the image of `c` is the sum over `p` of `c p` times `κ p q`. -/
theorem intMatrixMap_apply (c : α →₀ R) (q : β) :
    intMatrixMap R κ c q = c.sum fun p a ↦ a * (κ p q : R) :=
  linearCombination_equivFunOnFinite_symm_apply _ c q

/-- The coefficient of `q` in the image of `single p a` is `a * κ p q`. -/
@[simp]
theorem intMatrixMap_single_apply (p : α) (a : R) (q : β) :
    intMatrixMap R κ (single p a) q = a * (κ p q : R) :=
  linearCombination_equivFunOnFinite_symm_single_apply _ p q a

/-- **Change of coefficients.** An additive map `g : R → R'`, for instance a ring homomorphism,
applied to the coefficients intertwines the maps with integer matrix `κ` over `R` and over `R'`:
`g` commutes with integer multiples. -/
theorem mapRange_intMatrixMap {R' F : Type*} [Ring R'] [FunLike F R R']
    [AddMonoidHomClass F R R'] (g : F) (c : α →₀ R) :
    mapRange g (map_zero g) (intMatrixMap R κ c) =
      intMatrixMap R' κ (mapRange g (map_zero g) c) := by
  ext q
  rw [mapRange_apply, intMatrixMap_apply, intMatrixMap_apply,
    sum_mapRange_index (fun _ ↦ zero_mul _), map_finsuppSum]
  simp only [← zsmul_eq_mul', map_zsmul]

/-- **Changing the signs of the entries conjugates the map.** If `κ'` is `κ` with the entry at
`(p, q)` multiplied by `-1` for `p ∈ S₀` and by `-1` for `q ∈ S₁`, then the map with matrix `κ'` is
that with matrix `κ` composed on both sides with the sign reversals on `S₀` and on `S₁`. -/
theorem intMatrixMap_eq_signReversal_comp (S₀ : Set α) [DecidablePred (· ∈ S₀)] (S₁ : Set β)
    [DecidablePred (· ∈ S₁)] {κ' : α → β → ℤ}
    (h : ∀ p q, κ' p q = (if p ∈ S₀ then -1 else 1) * (if q ∈ S₁ then -1 else 1) * κ p q) :
    intMatrixMap R κ' =
      (signReversal R S₁).toLinearMap ∘ₗ intMatrixMap R κ ∘ₗ (signReversal R S₀).toLinearMap := by
  refine lhom_ext fun p a ↦ ext fun q ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [intMatrixMap_single_apply, signReversal_single, signReversal_apply, h]
  by_cases hp : p ∈ S₀ <;> by_cases hq : q ∈ S₁ <;> simp [hp, hq]

end Finsupp
