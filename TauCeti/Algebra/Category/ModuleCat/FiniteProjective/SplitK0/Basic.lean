/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Equivalence
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange

/-!
# Basic split `K₀` theory of finitely generated projective modules

For a possibly noncommutative ring `R`, this file develops the basic theory of `SplitK0` of
`(finiteProjectiveModules R).FullSubcategory`:

* normal form `[P] - n • [R]`
  (`TauCeti.SplitK0.exists_eq_of_sub_nsmul_finiteProjectiveModulesRegular`),
* Morita invariance (`CategoryTheory.Equivalence.finiteProjectiveModulesSplitK0Equiv`),
* ring-isomorphism invariance (`RingEquiv.finiteProjectiveModulesSplitK0Equiv`), and its agreement
  with restriction of scalars along the inverse ring isomorphism.

## References

* C. A. Weibel, *The K-book*, Chapter II, §2, Lemma 2.1, p. 5.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u u'

namespace TauCeti.SplitK0

variable {R : Type u} [Ring R]

/-- The class of `Fin n → R` in `SplitK0` is `n` times `[R]`. -/
@[simp] theorem of_finFreeObj (n : ℕ) :
    SplitK0.of.{u} (FiniteProjectiveModules.finFreeObj R n) =
      n • SplitK0.of.{u} (finiteProjectiveModulesRegular R) := by
  induction n with
  | zero =>
    rw [zero_smul]
    refine of_eq_zero_of_isZero (IsZero.of_full_of_faithful_of_isZero (finiteProjectiveModules R).ι
      _ ?_)
    change IsZero (FiniteProjectiveModules.finFreeObj R 0).obj
    rw [FiniteProjectiveModules.finFreeObj_obj]
    exact ModuleCat.isZero_of_subsingleton _
  | succ n ih =>
    let e : (Fin (n + 1) → R) ≃ₗ[R] R × (Fin n → R) :=
      { toFun := fun f ↦ (f 0, Fin.tail f)
        invFun := fun p ↦ Fin.cons p.1 p.2
        left_inv := fun f ↦ Fin.cons_self_tail f
        right_inv := fun _ ↦ Prod.ext (by simp) (by simp)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hcongr := of_congr.{u} (X := FiniteProjectiveModules.finFreeObj R (n + 1))
      (Y := finiteProjectiveModulesRegular R ⊞ FiniteProjectiveModules.finFreeObj R n)
      ((finiteProjectiveModules R).fullyFaithfulι.preimageIso
        (e.trans (FiniteProjectiveModules.biprodLinearEquiv (finiteProjectiveModulesRegular R)
          (FiniteProjectiveModules.finFreeObj R n)).symm).toModuleIso)
    rw [hcongr, of_biprod, ih, succ_nsmul']

/-- Every element of `SplitK0 (finiteProjectiveModules R).FullSubcategory` has the form
`[P] - n • [R]` (Weibel, *The K-book*, Lemma II.2.1). -/
theorem exists_eq_of_sub_nsmul_finiteProjectiveModulesRegular
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    ∃ (P : (finiteProjectiveModules R).FullSubcategory) (n : ℕ),
      x = SplitK0.of.{u} P - n • SplitK0.of.{u} (finiteProjectiveModulesRegular R) := by
  obtain ⟨P₁, P₂, rfl⟩ := SplitK0.exists_eq_sub.{u} x
  obtain ⟨Q, n, ⟨e⟩⟩ := FiniteProjectiveModules.exists_biprod_iso_fin P₂
  refine ⟨P₁ ⊞ Q, n, ?_⟩
  rw [SplitK0.of_biprod.{u}, ← of_finFreeObj, ← SplitK0.of_congr.{u} e, SplitK0.of_biprod.{u}]
  abel

end TauCeti.SplitK0

namespace CategoryTheory.Equivalence

open TauCeti

variable {A : Type u} [Ring A] {B : Type u'} [Ring B] (e : ModuleCat.{u} A ≌ ModuleCat.{u'} B)

/-- **Morita invariance of `SplitK0` of finitely generated projective modules.** -/
noncomputable def finiteProjectiveModulesSplitK0Equiv :
    SplitK0.{u} (finiteProjectiveModules A).FullSubcategory ≃+
      SplitK0.{u'} (finiteProjectiveModules B).FullSubcategory :=
  SplitK0.mapEquiv.{u, u'} e.finiteProjectiveModulesEquivalence

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_of (P) :
    e.finiteProjectiveModulesSplitK0Equiv (SplitK0.of.{u} P) =
      SplitK0.of.{u'} (e.finiteProjectiveModulesEquivalence.functor.obj P) :=
  SplitK0.mapEquiv_of.{u, u'} _ P

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_symm_of (Q) :
    e.finiteProjectiveModulesSplitK0Equiv.symm (SplitK0.of.{u'} Q) =
      SplitK0.of.{u} (e.finiteProjectiveModulesEquivalence.inverse.obj Q) :=
  SplitK0.mapEquiv_symm_of.{u, u'} _ Q

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_toAddMonoidHom :
    (e.finiteProjectiveModulesSplitK0Equiv :
        SplitK0.{u} (finiteProjectiveModules A).FullSubcategory →+
          SplitK0.{u'} (finiteProjectiveModules B).FullSubcategory) =
      SplitK0.map.{u, u'} e.finiteProjectiveModulesEquivalence.functor :=
  SplitK0.mapEquiv_toAddMonoidHom.{u, u'} _

end CategoryTheory.Equivalence

namespace RingEquiv

open TauCeti

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- A ring isomorphism `e : R ≃+* S` induces an isomorphism on `SplitK0` by extension of scalars. -/
noncomputable def finiteProjectiveModulesSplitK0Equiv (e : R ≃+* S) :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      SplitK0.{u} (finiteProjectiveModules S).FullSubcategory :=
  AddMonoidHom.toAddEquiv
    (SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars)
    (SplitK0.map.{u, u} e.symm.toRingHom.finiteProjectiveModulesExtendScalars)
    (AddMonoidHom.ext fun _ ↦ by simp) (AddMonoidHom.ext fun _ ↦ by simp)

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_apply (e : R ≃+* S) (x) :
    e.finiteProjectiveModulesSplitK0Equiv x =
      SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars x := (rfl)

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_symm (e : R ≃+* S) :
    e.finiteProjectiveModulesSplitK0Equiv.symm = e.symm.finiteProjectiveModulesSplitK0Equiv := (rfl)

/-- On `SplitK0`, extension of scalars along a ring isomorphism `e : R ≃+* S` agrees with
restriction of scalars along `e.symm`. -/
theorem splitK0Map_finiteProjectiveModulesExtendScalars_eq_restrictScalars (e : R ≃+* S) :
    SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars =
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.finiteProjectiveModulesSplitK0Equiv
        : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory →+
          SplitK0.{u} (finiteProjectiveModules S).FullSubcategory) :=
  SplitK0.hom_ext fun P ↦ by
    simpa using SplitK0.of_congr.{u} <| ObjectProperty.isoMk _ <|
      eqToIso (e.toRingHom.finiteProjectiveModulesExtendScalars_obj_obj P) ≪≫
        (BalancedExtension.functorRingEquivIso.{u, u, u} e).app P.obj ≪≫
        eqToIso ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          e).symm.finiteProjectiveModulesEquivalence_functor_obj_obj P).symm

/-- On `SplitK0`, the isomorphism induced by extension of scalars along a ring isomorphism
`e : R ≃+* S` agrees with restriction of scalars along `e.symm`. -/
theorem finiteProjectiveModulesSplitK0Equiv_eq_restrictScalars (e : R ≃+* S) :
    e.finiteProjectiveModulesSplitK0Equiv =
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.finiteProjectiveModulesSplitK0Equiv :=
  AddEquiv.toAddMonoidHom_injective
    (splitK0Map_finiteProjectiveModulesExtendScalars_eq_restrictScalars e)

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_refl (R : Type u) [Ring R] :
    (RingEquiv.refl R).finiteProjectiveModulesSplitK0Equiv = AddEquiv.refl _ := by ext; simp

theorem finiteProjectiveModulesSplitK0Equiv_trans (e : R ≃+* S) (e' : S ≃+* T) :
    (e.trans e').finiteProjectiveModulesSplitK0Equiv =
      e.finiteProjectiveModulesSplitK0Equiv.trans e'.finiteProjectiveModulesSplitK0Equiv := by
  ext; simp [RingEquiv.toRingHom_trans]

end RingEquiv
