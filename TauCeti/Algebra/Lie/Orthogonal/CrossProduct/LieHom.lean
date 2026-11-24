/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.CrossProduct

/-!
# Lie algebra homomorphisms out of `so(3)`

Under the hat map `u ↦ û` (`TauCeti.soThreeEquiv`), the standard basis vectors `e₀, e₁, e₂` of
`R³` give a basis `ê₀, ê₁, ê₂` of `so(3)`, and since `e₀ ⨯₃ e₁ = e₂` and cyclically, its brackets
are

`⁅ê₀, ê₁⁆ = ê₂`, `⁅ê₁, ê₂⁆ = ê₀`, `⁅ê₂, ê₀⁆ = ê₁`.

These relations present `so(3)`: for any three elements `a₀, a₁, a₂` of a Lie algebra `L`
satisfying the same cyclic relations, the linear map `û ↦ u₀ a₀ + u₁ a₁ + u₂ a₂` is a Lie algebra
homomorphism (`TauCeti.soThreeLieHom`), and it is the only one sending `êᵢ` to `aᵢ`
(`TauCeti.lieHom_ext_soThree`). It is injective exactly when `a₀, a₁, a₂` are linearly
independent (`TauCeti.soThreeLieHom_injective_iff`).

Over `ℝ`, `so(3)` is isomorphic to the Lie algebra `𝔰𝔲(2)` of `SU(2)`, so a triple satisfying the
cyclic relations is what a real Lie algebra needs in order to receive `𝔰𝔲(2)`.

## Main definitions

* `TauCeti.soThreeLieHom a h₀ h₁ h₂`: the Lie algebra homomorphism `so(3) → L` with `êᵢ ↦ aᵢ`.

## Main results

* `TauCeti.soThreeLieHom_soThreeEquiv`: it sends `û` to `∑ᵢ uᵢ • aᵢ`.
* `TauCeti.lieHom_ext_soThree`: Lie algebra homomorphisms out of `so(3)` agreeing on the `êᵢ` are
  equal.
* `TauCeti.soThreeLieHom_injective_iff`: it is injective exactly when the `aᵢ` are linearly
  independent.
-/

public section

open LieAlgebra.Orthogonal Matrix

namespace TauCeti

variable {R L : Type*} [CommRing R] [NoZeroDivisors R] [NeZero (2 : R)] [LieRing L]
  [LieAlgebra R L]

/-- The **Lie algebra homomorphism out of `so(3)` determined by a triple** `a₀, a₁, a₂` satisfying
the cyclic relations `⁅a₀, a₁⁆ = a₂`, `⁅a₁, a₂⁆ = a₀`, `⁅a₂, a₀⁆ = a₁` of the basis `ê₀, ê₁, ê₂`:
it sends `û` to `u₀ a₀ + u₁ a₁ + u₂ a₂`, so `êᵢ ↦ aᵢ`. -/
def soThreeLieHom (a : Fin 3 → L) (h₀ : ⁅a 0, a 1⁆ = a 2) (h₁ : ⁅a 1, a 2⁆ = a 0)
    (h₂ : ⁅a 2, a 0⁆ = a 1) : so (Fin 3) R →ₗ⁅R⁆ L :=
  { Fintype.linearCombination R a ∘ₗ (soThreeEquiv R).symm.toLinearMap with
    map_lie' := by
      intro A C
      obtain ⟨u, rfl⟩ := (soThreeEquiv R).surjective A
      obtain ⟨v, rfl⟩ := (soThreeEquiv R).surjective C
      -- Expand both sides in the `aᵢ`; the reversed brackets are the negatives of the given ones.
      have h₀' : ⁅a 1, a 0⁆ = -a 2 := by rw [← lie_skew, h₀]
      have h₁' : ⁅a 2, a 1⁆ = -a 0 := by rw [← lie_skew, h₁]
      have h₂' : ⁅a 0, a 2⁆ = -a 1 := by rw [← lie_skew, h₂]
      simp only [LinearMap.toFun_eq_coe, lie_soThreeEquiv, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply,
        Fintype.linearCombination_apply, Fin.sum_univ_three,
        cross_apply, lie_add, add_lie, smul_lie, lie_smul, lie_self, h₀, h₁, h₂, h₀', h₁', h₂',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, smul_zero, smul_neg]
      module }

variable {a : Fin 3 → L} {h₀ : ⁅a 0, a 1⁆ = a 2} {h₁ : ⁅a 1, a 2⁆ = a 0}
  {h₂ : ⁅a 2, a 0⁆ = a 1}

/-- The homomorphism `soThreeLieHom` is the linear combination of the `aᵢ` with the coefficients
`u` of `A = û`. -/
theorem soThreeLieHom_apply (A : so (Fin 3) R) :
    soThreeLieHom a h₀ h₁ h₂ A = Fintype.linearCombination R a ((soThreeEquiv R).symm A) :=
  (rfl)

/-- The homomorphism `soThreeLieHom` sends `û` to `∑ᵢ uᵢ • aᵢ`. -/
@[simp]
theorem soThreeLieHom_soThreeEquiv (u : Fin 3 → R) :
    soThreeLieHom a h₀ h₁ h₂ (soThreeEquiv R u) = ∑ i, u i • a i := by
  rw [soThreeLieHom_apply, LinearEquiv.symm_apply_apply, Fintype.linearCombination_apply]

/-- The homomorphism `soThreeLieHom` sends the basis element `êᵢ` to `aᵢ`. -/
theorem soThreeLieHom_soThreeEquiv_single (i : Fin 3) :
    soThreeLieHom a h₀ h₁ h₂ (soThreeEquiv R (Pi.single i 1)) = a i := by
  rw [soThreeLieHom_apply, LinearEquiv.symm_apply_apply, Fintype.linearCombination_apply_single,
    one_smul]

/-- **Lie algebra homomorphisms out of `so(3)` are determined by the images of `ê₀, ê₁, ê₂`.** -/
@[ext]
theorem lieHom_ext_soThree {f g : so (Fin 3) R →ₗ⁅R⁆ L}
    (h : ∀ i, f (soThreeEquiv R (Pi.single i 1)) = g (soThreeEquiv R (Pi.single i 1))) :
    f = g :=
  -- The `êᵢ` are the image of the standard basis under the hat map.
  LieHom.ext <| LinearMap.congr_fun <|
    ((Pi.basisFun R (Fin 3)).map (soThreeEquiv R)).ext (f₁ := (f : so (Fin 3) R →ₗ[R] L))
      (f₂ := g) fun i ↦ by simpa using h i

/-- **`soThreeLieHom` is injective exactly when `a₀, a₁, a₂` are linearly independent.** -/
theorem soThreeLieHom_injective_iff :
    Function.Injective (soThreeLieHom a h₀ h₁ h₂ : so (Fin 3) R → L) ↔ LinearIndependent R a := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  -- `soThreeLieHom` is the linear combination of the `aᵢ` after the linear equivalence
  -- `(soThreeEquiv R).symm`.
  have h : (soThreeLieHom a h₀ h₁ h₂ : so (Fin 3) R → L) =
      Fintype.linearCombination R a ∘ (soThreeEquiv R).symm :=
    funext soThreeLieHom_apply
  rw [h, Function.Injective.of_comp_iff' _ (soThreeEquiv R).symm.bijective]

end TauCeti
