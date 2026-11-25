/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.LinearAlgebra.TensorProduct.Hom

/-!
# Base change of the defining map of an Azumaya algebra

Let `A` be an algebra over a commutative ring `R` which is finitely generated and projective as an
`R`-module, and `S` a commutative `R`-algebra. The defining map of an Azumaya algebra,
`AlgHom.mulLeftRight R A : A ⊗[R] Aᵐᵒᵖ → End_R(A)`, `a ⊗ b ↦ (x ↦ a x b)`, commutes with base
change to `S`: under the identifications `S ⊗[R] (A ⊗[R] Aᵐᵒᵖ) ≅ (S ⊗[R] A) ⊗[S] (S ⊗[R] A)ᵐᵒᵖ`
(`TauCeti.Brauer.mulLeftRightBaseChangeEquiv`) and `S ⊗[R] End_R(A) ≅ End_S(S ⊗[R] A)`, which holds
because `A` is finite projective (`LinearMap.isBaseChange_baseChangeHom`), it becomes the defining
map of `S ⊗[R] A` over `S`
(`TauCeti.Brauer.mulLeftRight_comp_mulLeftRightBaseChangeEquiv`). Hence if the defining map of `A`
is bijective, so is that of `S ⊗[R] A`
(`TauCeti.Brauer.bijective_mulLeftRight_baseChange`), and `S ⊗[R] A` is Azumaya over `S` as soon
as it is faithful over `S` (`TauCeti.Brauer.isAzumaya_baseChange_of_faithfulSMul`).

## Main results

* `TauCeti.Brauer.mulLeftRight_comp_mulLeftRightBaseChangeEquiv`: the defining map commutes with
  base change.
* `TauCeti.Brauer.bijective_mulLeftRight_baseChange`: its bijectivity is stable under base change.
* `TauCeti.Brauer.isAzumaya_baseChange_of_faithfulSMul`: the base change of an Azumaya algebra is
  Azumaya when it is faithful.
-/

public section

open TensorProduct

namespace TauCeti.Brauer

universe u v w

variable (R : Type u) (A : Type v) (S : Type w) [CommRing R] [Ring A] [Algebra R A]
  [CommRing S] [Algebra R S]

/-- The identification `S ⊗[R] (A ⊗[R] Aᵐᵒᵖ) ≅ (S ⊗[R] A) ⊗[S] (S ⊗[R] A)ᵐᵒᵖ` of `S`-modules,
sending `s ⊗ (a ⊗ op b)` to `(s ⊗ a) ⊗ op (1 ⊗ b)`. -/
noncomputable def mulLeftRightBaseChangeEquiv :
    S ⊗[R] (A ⊗[R] Aᵐᵒᵖ) ≃ₗ[S] (S ⊗[R] A) ⊗[S] (S ⊗[R] A)ᵐᵒᵖ :=
  AlgebraTensorModule.distribBaseChange R S A Aᵐᵒᵖ ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl S (S ⊗[R] A))
      ((LinearEquiv.baseChange R S _ _ (MulOpposite.opLinearEquiv R).symm) ≪≫ₗ
        MulOpposite.opLinearEquiv S)

@[simp]
theorem mulLeftRightBaseChangeEquiv_tmul (s : S) (a : A) (b : Aᵐᵒᵖ) :
    mulLeftRightBaseChangeEquiv R A S (s ⊗ₜ (a ⊗ₜ b)) =
      (s ⊗ₜ a) ⊗ₜ MulOpposite.op ((1 : S) ⊗ₜ b.unop) := by
  simp [mulLeftRightBaseChangeEquiv, AlgebraTensorModule.distribBaseChange]

variable [Module.Finite R A] [Module.Projective R A]

/-- **The defining map of an Azumaya algebra commutes with base change.** For `A` finite
projective over `R`, the defining map of `S ⊗[R] A` over `S`, precomposed with
`mulLeftRightBaseChangeEquiv`, is the base change of the defining map of `A` followed by the
identification `S ⊗[R] End_R(A) ≅ End_S(S ⊗[R] A)`. -/
theorem mulLeftRight_comp_mulLeftRightBaseChangeEquiv :
    (AlgHom.mulLeftRight S (S ⊗[R] A)).toLinearMap ∘ₗ
        (mulLeftRightBaseChangeEquiv R A S).toLinearMap =
      (LinearMap.isBaseChange_baseChangeHom R S A A).equiv.toLinearMap ∘ₗ
        (AlgHom.mulLeftRight R A).toLinearMap.baseChange S := by
  ext a b x
  simp [IsBaseChange.equiv_tmul]

/-- **Bijectivity of the defining map is stable under base change.** For `A` finite projective
over `R` with `A ⊗[R] Aᵐᵒᵖ → End_R(A)` bijective, the defining map
`(S ⊗[R] A) ⊗[S] (S ⊗[R] A)ᵐᵒᵖ → End_S(S ⊗[R] A)` is bijective. -/
theorem bijective_mulLeftRight_baseChange (h : Function.Bijective (AlgHom.mulLeftRight R A)) :
    Function.Bijective (AlgHom.mulLeftRight S (S ⊗[R] A)) := by
  let e := LinearEquiv.ofBijective (AlgHom.mulLeftRight R A).toLinearMap h
  have key : (AlgHom.mulLeftRight S (S ⊗[R] A) : _ → _) =
      (LinearMap.isBaseChange_baseChangeHom R S A A).equiv ∘ e.baseChange R S _ _ ∘
        (mulLeftRightBaseChangeEquiv R A S).symm := by
    funext x
    obtain ⟨y, rfl⟩ := (mulLeftRightBaseChangeEquiv R A S).surjective x
    have := congr($(mulLeftRight_comp_mulLeftRightBaseChangeEquiv R A S) y)
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      AlgHom.toLinearMap_apply] at this
    simp only [Function.comp_apply, LinearEquiv.symm_apply_apply]
    exact this
  rw [key]
  exact (LinearEquiv.bijective _).comp ((LinearEquiv.bijective _).comp (LinearEquiv.bijective _))

/-- **Base change of an Azumaya algebra, given faithfulness.** If `A` is finite projective over
`R` with bijective defining map, for instance Azumaya, and `S ⊗[R] A` is faithful over `S`, then
`S ⊗[R] A` is Azumaya over `S`: finiteness and projectivity are preserved by base change, and the
defining map stays bijective (`bijective_mulLeftRight_baseChange`). -/
theorem isAzumaya_baseChange_of_faithfulSMul (h : Function.Bijective (AlgHom.mulLeftRight R A))
    [FaithfulSMul S (S ⊗[R] A)] : IsAzumaya S (S ⊗[R] A) where
  toProjective := inferInstance
  toFinite := inferInstance
  bij := bijective_mulLeftRight_baseChange R A S h

end TauCeti.Brauer
