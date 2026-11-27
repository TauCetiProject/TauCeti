/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.CharacterModule.MulOpposite
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic

/-!
# Characters of a balanced tensor product

For a right module `P` and a left module `M` over a ring `A`, characters of
`P ⊗_A M` correspond to right `A`-linear maps from `P` to the character
module of `M`. The correspondence turns precomposition by `i ⊗ 1` into
precomposition by `i`. In particular, `i ⊗ 1` is injective exactly when
every map into the character module extends along `i`.

This is the character pairing in Lambek, *A module is flat if and only if its
character module is injective*, Proposition 1 and the following discussion,
p. 241. Mathlib's `CharacterModule.homEquiv` treats ordinary tensor products.
-/

public section

open MulOpposite
open scoped CharacterModule

namespace TauCeti.BalancedTensorProduct

variable {A P Q M : Type*} [Ring A]
  [AddCommGroup P] [Module Aᵐᵒᵖ P] [AddCommGroup Q] [Module Aᵐᵒᵖ Q]
  [AddCommGroup M] [Module A M]

private def curryCharacter (χ : CharacterModule (BalancedTensorProduct ℤ A P M)) :
    P →ₗ[Aᵐᵒᵖ] CharacterModule M :=
  let c (p : P) : CharacterModule M :=
    (AddMonoidHom.ofClass χ).comp (mk ℤ A p).toAddMonoidHom
  have hc (p : P) (m : M) : c p m = χ (tmul ℤ A p m) :=
    congrArg χ (mk_apply ℤ A p m)
  { toFun := c
    map_add' p q := CharacterModule.ext M fun m ↦ by
      -- Evaluation of a sum of characters is pointwise.
      change c (p + q) m = c p m + c q m
      simp only [hc, add_tmul, map_add]
    map_smul' a p := CharacterModule.ext M fun m ↦ by
      rw [RingHom.id_apply, CharacterModule.mulOpposite_smul_apply, hc, hc]
      exact congrArg χ (by simpa only [op_unop] using balance ℤ A a.unop p m) }

private theorem curryCharacter_apply (χ : CharacterModule (BalancedTensorProduct ℤ A P M))
    (p : P) (m : M) : curryCharacter χ p m = χ (tmul ℤ A p m) :=
  congrArg χ (mk_apply ℤ A p m)

private def uncurryCharacter (g : P →ₗ[Aᵐᵒᵖ] CharacterModule M) :
    CharacterModule (BalancedTensorProduct ℤ A P M) :=
  let eval (m : M) : CharacterModule M →+ AddCircle (1 : ℚ) := AddMonoidHom.eval m
  let b := LinearMap.mk₂ ℤ (fun p m ↦ g p m)
    (fun p q m ↦ (congrArg (eval m) (g.map_add p q)).trans (map_add (eval m) _ _))
    (fun z p m ↦ (congrArg (eval m) (map_zsmul g z p)).trans (map_zsmul (eval m) z (g p)))
    (fun p m n ↦ map_add (g p) m n)
    (fun z p m ↦ map_zsmul (g p) z m)
  have hb (p : P) (m : M) : b p m = g p m := LinearMap.mk₂_apply ℤ _ p m
  (lift b (fun a p m ↦ by
    simp only [hb, map_smul, CharacterModule.mulOpposite_smul_apply, unop_op])).toAddMonoidHom

private theorem uncurryCharacter_tmul (g : P →ₗ[Aᵐᵒᵖ] CharacterModule M)
    (p : P) (m : M) : uncurryCharacter g (tmul ℤ A p m) = g p m := by
  -- Evaluation of the additive character uses the underlying linear lift.
  change lift _ _ (tmul ℤ A p m) = g p m
  exact (lift_tmul _ _ p m).trans (LinearMap.mk₂_apply ℤ _ p m)

/-- The character `χ` of a balanced tensor product gives the right-module map
`p ↦ (m ↦ χ (p ⊗ m))`, and every right-module map into the character module of
`M` arises uniquely this way. -/
def characterModuleEquiv : CharacterModule (BalancedTensorProduct ℤ A P M) ≃+
    (P →ₗ[Aᵐᵒᵖ] CharacterModule M) where
  toFun := curryCharacter
  invFun := uncurryCharacter
  left_inv χ := by
    apply CharacterModule.ext
    intro t
    induction t using induction_on with
    | ht p m => rw [uncurryCharacter_tmul, curryCharacter_apply]
    | ha x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv g := LinearMap.ext fun p ↦ CharacterModule.ext M fun m ↦
    (curryCharacter_apply _ _ _).trans (uncurryCharacter_tmul g p m)
  map_add' χ ψ := LinearMap.ext fun p ↦ CharacterModule.ext M fun _ ↦ (rfl)

/-- Currying a character evaluates it on a pure tensor. -/
@[simp]
theorem characterModuleEquiv_apply (χ : CharacterModule (BalancedTensorProduct ℤ A P M))
    (p : P) (m : M) : characterModuleEquiv χ p m = χ (tmul ℤ A p m) :=
  curryCharacter_apply χ p m

/-- The character corresponding to a right-module map evaluates a pure tensor by applying
the map to the right-module entry and then evaluating at the left-module entry. -/
@[simp]
theorem characterModuleEquiv_symm_apply_tmul (g : P →ₗ[Aᵐᵒᵖ] CharacterModule M)
    (p : P) (m : M) : characterModuleEquiv.symm g (tmul ℤ A p m) = g p m :=
  uncurryCharacter_tmul g p m

/-- The character correspondence is natural in maps of right modules. -/
theorem characterModuleEquiv_dual_map (i : P →ₗ[Aᵐᵒᵖ] Q)
    (χ : CharacterModule (BalancedTensorProduct ℤ A Q M)) :
    characterModuleEquiv
        (CharacterModule.dual
          (map (A := A) (i.restrictScalars ℤ) (LinearMap.id : M →ₗ[ℤ] M)
            (fun a p ↦ i.map_smul (op a) p) (fun _ _ ↦ rfl)) χ) =
      characterModuleEquiv χ ∘ₗ i := by
  apply LinearMap.ext
  intro p
  apply CharacterModule.ext M
  intro m
  rw [characterModuleEquiv_apply, LinearMap.comp_apply, characterModuleEquiv_apply]
  exact congrArg χ (map_tmul (i.restrictScalars ℤ) (LinearMap.id : M →ₗ[ℤ] M)
    (fun a p ↦ i.map_smul (op a) p) (fun _ _ ↦ rfl) p m)

/-- A balanced tensor map `i ⊗ 1` is injective if and only if every map to the character
module of the fixed left module extends along `i` (Lambek, Proposition 1). -/
theorem injective_map_id_iff_surjective_lcomp (i : P →ₗ[Aᵐᵒᵖ] Q) :
    Function.Injective
      (map (A := A) (i.restrictScalars ℤ) (LinearMap.id : M →ₗ[ℤ] M)
        (fun a p ↦ i.map_smul (op a) p) (fun _ _ ↦ rfl)) ↔
      Function.Surjective (i.lcomp ℤ (CharacterModule M)) := by
  rw [← CharacterModule.dual_surjective_iff_injective]
  constructor
  · intro h g
    obtain ⟨χ, hχ⟩ := h (characterModuleEquiv.symm g)
    refine ⟨characterModuleEquiv χ, ?_⟩
    rw [LinearMap.lcomp_apply', ← characterModuleEquiv_dual_map, hχ, AddEquiv.apply_symm_apply]
  · intro h χ
    obtain ⟨g, hg⟩ := h (characterModuleEquiv χ)
    refine ⟨characterModuleEquiv.symm g, characterModuleEquiv.injective ?_⟩
    rw [characterModuleEquiv_dual_map, AddEquiv.apply_symm_apply]
    simpa only [LinearMap.lcomp_apply'] using hg

end TauCeti.BalancedTensorProduct
