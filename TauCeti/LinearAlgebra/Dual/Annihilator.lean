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

The linear algebra of Lagrange multipliers follows over a field: if `DF` does not map `ker D` onto
its codomain, then some nonzero functional `f` makes `f ∘ DF` a pullback `g ∘ D`
(`LinearMap.exists_ne_zero_comp_eq_comp_of_map_ker_ne_top`).
-/

public section

namespace Submodule

/-- A functional factoring through the quotient `V ⧸ U` annihilates `U`. -/
theorem comp_mkQ_mem_dualAnnihilator {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (U : Submodule R V) (ψ : Module.Dual R (V ⧸ U)) : ψ ∘ₗ U.mkQ ∈ U.dualAnnihilator :=
  (mem_dualAnnihilator _).mpr fun w hw ↦ by
    rw [LinearMap.comp_apply, mkQ_apply, (Quotient.mk_eq_zero U).mpr hw, map_zero]

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
  rw [← S.range_dualMap_mkQ_eq, ← LinearMap.range_comp,
    LinearMap.dualMap_comp_dualMap,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker, LinearMap.ker_comp,
    Submodule.ker_mkQ]

end Submodule

namespace LinearMap

variable {k V W U : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]

/-- **Lagrange multipliers**, linear-algebra form. If `DF` does not map the kernel of `D` onto its
codomain, then some nonzero functional `f` and some functional `g` satisfy `f ∘ DF = g ∘ D`. -/
theorem exists_ne_zero_comp_eq_comp_of_map_ker_ne_top {D : V →ₗ[k] W} {DF : V →ₗ[k] U}
    (h : (ker D).map DF ≠ ⊤) :
    ∃ f : Module.Dual k U, f ≠ 0 ∧ ∃ g : Module.Dual k W, f ∘ₗ DF = g ∘ₗ D := by
  obtain ⟨f, hf0, hf⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 h) inferInstance
  have hmem : f ∘ₗ DF ∈ (ker D).dualAnnihilator := by
    refine (Submodule.mem_dualAnnihilator _).2 fun v hv ↦ ?_
    have hv' : f (DF v) ∈ ((ker D).map DF).map f := ⟨DF v, ⟨v, hv, rfl⟩, rfl⟩
    rwa [hf, Submodule.mem_bot] at hv'
  rw [← range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨g, hg⟩ := hmem
  exact ⟨f, hf0, g, hg.symm⟩

end LinearMap
