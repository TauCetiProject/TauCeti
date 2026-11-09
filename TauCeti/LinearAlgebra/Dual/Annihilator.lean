/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Pulling back annihilators

Over a field, pulling back functionals that annihilate a subspace gives exactly the
annihilator of its inverse image. This is the extension-of-functionals statement needed
when a Hom cocycle space is computed using an embedding into an injective module.

Equivalently, every functional on `V` vanishing on the inverse image of `S` is the
pullback of a functional on the quotient `W ⧸ S`. Conversely, over any commutative ring, a
functional factoring through a quotient `V ⧸ U` annihilates `U`
(`Submodule.comp_mkQ_mem_dualAnnihilator`).

For complementary submodules `p` and `q`, over any commutative ring, restriction to `p`
identifies the annihilator of `q` with the dual of `p`
(`Submodule.dualAnnihilatorEquivOfIsCompl`); the inverse extends a functional by zero on `q`.
-/

public section

namespace Submodule

/-- A functional factoring through the quotient `V ⧸ U` annihilates `U`. -/
theorem comp_mkQ_mem_dualAnnihilator {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (U : Submodule R V) (ψ : Module.Dual R (V ⧸ U)) : ψ ∘ₗ U.mkQ ∈ U.dualAnnihilator := by
  rw [← U.range_dualMap_mkQ_eq, ← LinearMap.dualMap_apply']
  exact LinearMap.mem_range_self _ ψ

section IsCompl

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (p q : Submodule R V)

/-- For complementary submodules `p` and `q`, restriction to `p` identifies the functionals
annihilating `q` with the functionals on `p`. The inverse extends a functional on `p` by zero
on `q`. -/
noncomputable def dualAnnihilatorEquivOfIsCompl (h : IsCompl p q) :
    q.dualAnnihilator ≃ₗ[R] Module.Dual R p :=
  q.dualQuotEquivDualAnnihilator.symm ≪≫ₗ (q.quotientEquivOfIsCompl p h.symm).symm.dualMap

/-- The identification of `q.dualAnnihilator` with `Module.Dual R p` restricts a functional
to `p`. -/
@[simp]
theorem dualAnnihilatorEquivOfIsCompl_apply (h : IsCompl p q) (φ : q.dualAnnihilator) (x : p) :
    dualAnnihilatorEquivOfIsCompl p q h φ x = (φ : Module.Dual R V) x := by
  -- The inverse of the quotient map sends `x ∈ p` back to its class in `V ⧸ q`.
  have hx : (q.quotientEquivOfIsCompl p h.symm).symm x = Quotient.mk (x : V) :=
    (LinearEquiv.symm_apply_eq _).2 (quotientEquivOfIsCompl_apply_mk_right h.symm x).symm
  rw [dualAnnihilatorEquivOfIsCompl, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply, hx,
    dualQuotEquivDualAnnihilator_symm_apply_mk]
  -- Mathlib's `FunLike` instance on `q.dualAnnihilator` is defined by `coe φ := φ.val` and has
  -- no evaluation lemma, so the remaining coercion step holds by that field.
  rfl

/-- The inverse of `Submodule.dualAnnihilatorEquivOfIsCompl` extends a functional on `p` by
zero on `q`. -/
@[simp]
theorem coe_dualAnnihilatorEquivOfIsCompl_symm_apply (h : IsCompl p q) (ψ : Module.Dual R p) :
    ((dualAnnihilatorEquivOfIsCompl p q h).symm ψ : Module.Dual R V) = LinearMap.ofIsCompl h ψ 0 :=
  (LinearMap.ofIsCompl_eq h
    (fun x ↦ by rw [← dualAnnihilatorEquivOfIsCompl_apply p q h, LinearEquiv.apply_symm_apply])
    fun x ↦
      ((mem_dualAnnihilator _).1 ((dualAnnihilatorEquivOfIsCompl p q h).symm ψ).2 x x.2).symm).symm

end IsCompl

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- Pullback of functionals annihilating `S` gives all functionals annihilating its
inverse image. Neither the map nor either vector space needs to be finite-dimensional. -/
@[simp]
theorem dualAnnihilator_map_dualMap_eq (S : Submodule k W) (f : V →ₗ[k] W) :
    S.dualAnnihilator.map f.dualMap = (S.comap f).dualAnnihilator := by
  rw [← S.range_dualMap_mkQ_eq, ← LinearMap.range_comp, LinearMap.dualMap_comp_dualMap,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker, LinearMap.ker_comp, ker_mkQ]

end Submodule
