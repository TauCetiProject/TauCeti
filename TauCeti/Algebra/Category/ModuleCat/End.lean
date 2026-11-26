/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import TauCeti.CategoryTheory.Functor.RingEquivEnd

/-!
# Endomorphisms in `ModuleCat`

An automorphism of a ring as a module over itself sends one to a unit. Consequently,
the scalar comparing the images of one under two isomorphisms is a unit as well.

A natural number `e` kills a module `M` exactly when the endomorphism `e • 𝟙 M` vanishes
(`ModuleCat.nsmul_id_eq_zero_iff`).

An `R`-linear, additive, fully faithful functor `F : ModuleCat A ⥤ ModuleCat B`, for instance a
Morita equivalence, identifies the endomorphism algebras:
`Module.End A M ≃ₐ[R] Module.End B (F M)`
(`CategoryTheory.Functor.FullyFaithful.moduleEndAlgEquiv`, with `moduleEndAlgEquiv_apply` and
`moduleEndAlgEquiv_symm_apply`).
-/

public noncomputable section

open CategoryTheory

namespace ModuleCat

universe u

variable {R : Type u} [Ring R]

/-- An automorphism of the rank-one free module sends one to a unit. -/
theorem isUnit_apply_one_of_isIso (f : ModuleCat.of R R ⟶ ModuleCat.of R R) [IsIso f] :
    IsUnit (f 1) :=
  (((Module.End.isUnit_iff _).2 (ConcreteCategory.bijective_of_isIso f)).map
    (RingEquiv.moduleEndSelf R).symm).unop

/-- The scalar comparing the images of one under two module isomorphisms is a unit. -/
theorem isUnit_of_apply_one_eq_smul {M : ModuleCat R}
    (f g : ModuleCat.of R R ⟶ M) [IsIso f] [IsIso g] {a : R}
    (h : g 1 = a • f 1) : IsUnit a := by
  have hu := isUnit_apply_one_of_isIso (g ≫ inv f)
  simpa only [CategoryTheory.comp_apply, h, map_smul, IsIso.hom_inv_id_apply,
    smul_eq_mul, mul_one] using hu

/-- A natural number `e` kills a module `M`, in the sense that `e • 𝟙 M = 0`, exactly when
`e • x = 0` for every element `x` of `M`. -/
theorem nsmul_id_eq_zero_iff {M : ModuleCat R} {e : ℕ} : e • 𝟙 M = 0 ↔ ∀ x : M, e • x = 0 :=
  ⟨fun h x ↦ by simpa using congr($h x), fun h ↦ by ext x; simpa using h x⟩

end ModuleCat

universe v w

open scoped ModuleCat.Algebra

namespace CategoryTheory.Functor.FullyFaithful

variable (R : Type*) [CommSemiring R] {A B : Type*} [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  {F : ModuleCat.{v} A ⥤ ModuleCat.{w} B} [F.Additive] [F.Linear R] (hF : F.FullyFaithful)

/-- An `R`-linear fully faithful functor `F` between module categories, for instance a Morita
equivalence, identifies the endomorphism algebra of a module `M` with that of `F M`. -/
noncomputable def moduleEndAlgEquiv (M : ModuleCat.{v} A) :
    Module.End A M ≃ₐ[R] Module.End B (F.obj M) :=
  AlgEquiv.ofRingEquiv (f := (ModuleCat.endRingEquiv M).symm.trans
    ((hF.ringEquivEnd M).trans (ModuleCat.endRingEquiv (F.obj M)))) fun r ↦ by
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, ModuleCat.endRingEquiv_apply,
      Functor.FullyFaithful.ringEquivEnd_apply_asHom]
    -- The endomorphism `algebraMap R _ r` of `M` is `r • 𝟙 M`, and `F` is `R`-linear.
    change (F.map (r • 𝟙 M)).hom = _
    rw [F.map_smul, F.map_id, ModuleCat.hom_smul, ModuleCat.hom_id,
      Module.algebraMap_end_eq_smul_id]

@[simp]
theorem moduleEndAlgEquiv_apply (M : ModuleCat.{v} A) (f : Module.End A M) :
    hF.moduleEndAlgEquiv R M f = (F.map (ModuleCat.ofHom f)).hom := by
  simp only [moduleEndAlgEquiv, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply,
    ModuleCat.endRingEquiv_apply, Functor.FullyFaithful.ringEquivEnd_apply_asHom]
  -- `((ModuleCat.endRingEquiv M).symm f).asHom` is `ModuleCat.ofHom f` by definition of
  -- `ModuleCat.endRingEquiv`, which has no simp lemma in this form.
  rfl

@[simp]
theorem moduleEndAlgEquiv_symm_apply (M : ModuleCat.{v} A) (g : Module.End B (F.obj M)) :
    (hF.moduleEndAlgEquiv R M).symm g = (hF.preimage (ModuleCat.ofHom g)).hom := by
  rw [AlgEquiv.symm_apply_eq, moduleEndAlgEquiv_apply]
  exact congrArg ModuleCat.Hom.hom (hF.map_preimage (ModuleCat.ofHom g)).symm

end CategoryTheory.Functor.FullyFaithful

