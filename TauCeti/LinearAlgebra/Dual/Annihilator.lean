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

The dual map `f^* : N^* → M^*` of a linear map `f : M → N` exchanges kernel and cokernel up to
duality. Over any commutative ring, `ker f^*` is the space of functionals vanishing on `range f`,
which is `(coker f)^*` (`LinearMap.kerDualMapEquiv`). Over a field, `coker f^* = M^* ⧸ range f^*`
is `(ker f)^*` by restriction (`LinearMap.cokerDualMapEquiv`).
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

open Module

section CommRing

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)

/-- The kernel of the dual map `f^*` is the dual of the cokernel of `f`: a functional on `N`
vanishing on `range f` is a functional on `N ⧸ range f`. -/
noncomputable def kerDualMapEquiv : ker f.dualMap ≃ₗ[R] Dual R (N ⧸ range f) :=
  (LinearEquiv.ofEq _ _ f.ker_dualMap_eq_dualAnnihilator_range).trans
    (range f).dualQuotEquivDualAnnihilator.symm

@[simp]
theorem kerDualMapEquiv_apply_mk (φ : ker f.dualMap) (n : N) :
    f.kerDualMapEquiv φ (Submodule.Quotient.mk n) = (φ : Dual R N) n :=
  (rfl)

@[simp]
theorem coe_kerDualMapEquiv_symm (ψ : Dual R (N ⧸ range f)) :
    (f.kerDualMapEquiv.symm ψ : Dual R N) = ψ ∘ₗ (range f).mkQ :=
  (rfl)

end CommRing

section Field

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] (f : M →ₗ[K] N)

/-- The cokernel of the dual map `f^*` is the dual of the kernel of `f`: the class of a functional
on `M` modulo `range f^*` is its restriction to `ker f`. -/
noncomputable def cokerDualMapEquiv : (Dual K M ⧸ range f.dualMap) ≃ₗ[K] Dual K (ker f) :=
  (Submodule.quotEquivOfEq _ _ f.range_dualMap_eq_dualAnnihilator_ker).trans
    (Subspace.quotAnnihilatorEquiv (ker f))

@[simp]
theorem cokerDualMapEquiv_mk_apply (θ : Dual K M) (u : ker f) :
    f.cokerDualMapEquiv (Submodule.Quotient.mk θ) u = θ u :=
  (rfl)

/-- The `finrank` of the kernel of `f^*` equals the `finrank` of the cokernel of `f`. When the
cokernel is finite-dimensional this says the two spaces have the same dimension. -/
theorem finrank_ker_dualMap_eq_finrank_quotient_range :
    finrank K (ker f.dualMap) = finrank K (N ⧸ range f) :=
  f.kerDualMapEquiv.finrank_eq.trans Subspace.dual_finrank_eq

/-- The `finrank` of the cokernel of `f^*` equals the `finrank` of the kernel of `f`. When the
kernel is finite-dimensional this says the two spaces have the same dimension. -/
theorem finrank_quotient_range_dualMap :
    finrank K (Dual K M ⧸ range f.dualMap) = finrank K (ker f) :=
  f.cokerDualMapEquiv.finrank_eq.trans Subspace.dual_finrank_eq

end Field

end LinearMap
