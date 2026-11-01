/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Affine equivalences

This file records computations with affine equivalences. In particular, identifying the
commutator of two homotheties as a translation supports affine representations that detect
infinite-order elements, such as those used for Euclidean triangle groups.

## Main definitions

* `AffineEquiv.semidirectSubgroup`: for a group `W` of linear automorphisms of a module `V` and a
  `W`-stable additive subgroup `L`, the affine automorphisms with linear part in `W` and
  translation part in `L`, a copy of the semidirect product `L ⋊ W` in the affine group.

## Main results

* `AffineEquiv.apply_eq_linear_add`: an affine equivalence between modules is its linear part
  followed by the translation by the image of `0`.
* `TauCeti.AffineEquiv.commutatorElement_homothetyUnitsMulHom_zero_one`: the commutator of
  homotheties about `0` and `1` is a translation.
-/

public section

open scoped commutatorElement

namespace AffineEquiv

variable {k V₁ V₂ : Type*} [Ring k] [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂]
  [Module k V₂]

/-- An affine equivalence between modules is its linear part followed by the translation by
`f 0`; this is `AffineMap.decomp` evaluated at a point. -/
theorem apply_eq_linear_add (f : V₁ ≃ᵃ[k] V₂) (x : V₁) : f x = f.linear x + f 0 :=
  congrFun f.toAffineMap.decomp x

/-- The translation part of the inverse of an affine automorphism `f` of a module is
`f⁻¹ 0 = f.linear⁻¹ (-f 0)`. -/
theorem inv_apply_zero (f : V₁ ≃ᵃ[k] V₁) : f⁻¹ 0 = f.linear⁻¹ (-f 0) := by
  have h := apply_eq_linear_add f.symm (f 0)
  rw [f.symm_apply_apply 0] at h
  rw [map_neg, ← linearHom_apply, ← map_inv, linearHom_apply]
  exact eq_neg_of_add_eq_zero_right h.symm

/-- **The semidirect product `L ⋊ W` in the affine group.** For a group `W` of linear automorphisms
of a module `V` and an additive subgroup `L` stable under `W`, the affine automorphisms of `V`
whose linear part lies in `W` and whose translation part `f 0` lies in `L`. -/
def semidirectSubgroup (W : Subgroup (V₁ ≃ₗ[k] V₁)) (L : AddSubgroup V₁)
    (hL : ∀ w ∈ W, ∀ v ∈ L, w v ∈ L) : Subgroup (V₁ ≃ᵃ[k] V₁) where
  carrier := {f | f.linear ∈ W ∧ f 0 ∈ L}
  one_mem' := ⟨by rw [← linearHom_apply, map_one]; exact one_mem W, by simp [zero_mem L]⟩
  mul_mem' := by
    rintro f g ⟨hf, hf0⟩ ⟨hg, hg0⟩
    refine ⟨by rw [← linearHom_apply, map_mul]; exact mul_mem hf hg, ?_⟩
    rw [coe_mul, Function.comp_apply, apply_eq_linear_add f (g 0)]
    exact add_mem (hL _ hf _ hg0) hf0
  inv_mem' := by
    rintro f ⟨hf, hf0⟩
    have hlin : f⁻¹.linear = f.linear⁻¹ := by rw [← linearHom_apply, map_inv, linearHom_apply]
    refine ⟨hlin ▸ inv_mem hf, ?_⟩
    rw [inv_apply_zero]
    exact hL _ (inv_mem hf) _ (neg_mem hf0)

@[simp]
theorem mem_semidirectSubgroup_iff {W : Subgroup (V₁ ≃ₗ[k] V₁)} {L : AddSubgroup V₁}
    {hL : ∀ w ∈ W, ∀ v ∈ L, w v ∈ L} {f : V₁ ≃ᵃ[k] V₁} :
    f ∈ semidirectSubgroup W L hL ↔ f.linear ∈ W ∧ f 0 ∈ L :=
  Iff.rfl

end AffineEquiv

namespace TauCeti

namespace AffineEquiv

variable {K : Type*} [Field K]

/-- The commutator of homotheties with ratios `ω` and `η` about `0` and `1`, respectively, is
translation by `(ω - 1) * (1 - η)`. -/
@[simp]
theorem commutatorElement_homothetyUnitsMulHom_zero_one (ω η : Kˣ) :
    ⁅_root_.AffineEquiv.homothetyUnitsMulHom (0 : K) ω,
        _root_.AffineEquiv.homothetyUnitsMulHom (1 : K) η⁆ =
      _root_.AffineEquiv.constVAdd K K (((ω : K) - 1) * (1 - η)) := by
  rw [commutatorElement_def, ← map_inv, ← map_inv]
  ext z
  simp only [_root_.AffineEquiv.coe_mul, Function.comp_apply,
    _root_.AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply, vsub_eq_sub,
    vadd_eq_add, smul_eq_mul, Units.val_inv_eq_inv_val, _root_.AffineEquiv.constVAdd_apply]
  field_simp
  ring

end AffineEquiv

end TauCeti
