/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.ExtendScalars
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.RingEquiv
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.Algebra.Category.ModuleCat.Matrix

import TauCeti.Algebra.Group.Prod
import TauCeti.LinearAlgebra.FreeModule.PID
import TauCeti.RingTheory.LocalRing.Module

/-!
# Split `K₀` of finitely generated projective modules: Morita invariance, products, and rank

For a possibly noncommutative ring `R`, this file develops the categorical and group-level API of
`SplitK0 (finiteProjectiveModules R).FullSubcategory`. The right-module specialization
`TauCeti.AlgebraicK0` builds on this file in
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.AlgebraicK0`.

## Main definitions and results

* `TauCeti.FiniteProjectiveModules.freeObj`, `TauCeti.FiniteProjectiveModules.finFreeObj`,
  `TauCeti.FiniteProjectiveModules.selfObj`, and `exists_biprod_iso_fin`: standard free objects and
  free complements `P ⊞ Q ≅ Rⁿ` (`exists_eq_of_sub_nsmul_selfObj`: classes `[P] - n • [R]`).
* `TauCeti.finiteProjectiveModulesSplitK0Equiv`: comparison with `ExactK0`.
* `CategoryTheory.Equivalence.finiteProjectiveModulesSplitK0Equiv`,
  `RingEquiv.finiteProjectiveModulesSplitK0Equiv`, `map_finiteProjectiveModulesExtendScalars_eq`:
  Morita and ring-isomorphism invariance, and agreement with restriction along `e.symm`.
* `TauCeti.finiteProjectiveModulesProdSplitK0Equiv`: `K₀(proj (R × S)) ≃+ K₀(proj R) × K₀(proj S)`.
* `TauCeti.finiteProjectiveModulesToMatrixFunctor`,
  `TauCeti.finiteProjectiveModulesMatrixSplitK0Equiv`, and
  `TauCeti.finiteProjectiveModulesMatrixFinSplitK0Equiv`: index-independent matrix Morita
  isomorphisms `K₀(proj R) ≃+ K₀(proj M_ι(R))` and `K₀(proj R) ≃+ K₀(proj M_n(R))`.
* `TauCeti.finiteProjectiveModulesFinrankSplitK0EquivOfFree` and specializations to division rings,
  principal left-ideal domains, and local rings: the rank isomorphism `K₀(proj R) ≃+ ℤ`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2,
  Definition 2.1, Lemma 2.1, Examples 2.1.1–2.1.2, Proposition 2.4, and §2.8.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u u'

namespace TauCeti

/-! ### Free complements and standard generators in `(finiteProjectiveModules R).FullSubcategory` -/

namespace FiniteProjectiveModules

section Basic

variable (R : Type u) [Ring R]

/-- The finite free module `ι → R` as an object of `(finiteProjectiveModules R).FullSubcategory`. -/
def freeObj (ι : Type u) [_root_.Finite ι] : (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R (ι → R), finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩

@[simp] theorem freeObj_obj (ι : Type u) [_root_.Finite ι] :
    (freeObj R ι).obj = ModuleCat.of R (ι → R) := (rfl)

/-- The finite free module `Fin n → R` as an object of
`(finiteProjectiveModules R).FullSubcategory`. -/
def finFreeObj (n : ℕ) : (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R (Fin n → R), finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩

@[simp] theorem finFreeObj_obj (n : ℕ) : (finFreeObj R n).obj = ModuleCat.of R (Fin n → R) := (rfl)

/-- The regular left `R`-module `R` in `(finiteProjectiveModules R).FullSubcategory`. -/
def selfObj : (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R R, finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩

@[simp] theorem selfObj_obj : (selfObj R).obj = ModuleCat.of R R := (rfl)

end Basic

/-- **Categorical free-complement theorem.** Every object `P` of
`(finiteProjectiveModules R).FullSubcategory` admits a complement `Q` in the same subcategory and a
natural number `n` with `P ⊞ Q ≅ Rⁿ`. -/
theorem exists_biprod_iso_fin {R : Type u} [Ring R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    ∃ (Q : (finiteProjectiveModules R).FullSubcategory) (n : ℕ),
      Nonempty (P ⊞ Q ≅ finFreeObj R n) := by
  obtain ⟨N, _, _, hfin, hproj, n, ⟨e⟩⟩ := Module.Projective.exists_prod_linearEquiv_fin R P.obj
  let Q : (finiteProjectiveModules R).FullSubcategory :=
    ⟨ModuleCat.of R N, finiteProjectiveModules_iff.mpr ⟨hfin, hproj⟩⟩
  exact ⟨Q, n, ⟨(finiteProjectiveModules R).fullyFaithfulι.preimageIso
    ((biprodLinearEquiv P Q).trans e).toModuleIso⟩⟩

end FiniteProjectiveModules

namespace SplitK0

/-- The class of the finite free module `Fin n → R` in `SplitK0` is `n` times `[R]`. -/
@[simp] theorem of_finFreeObj {R : Type u} [Ring R] (n : ℕ) :
    SplitK0.of.{u} (FiniteProjectiveModules.finFreeObj R n) =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) :=
  of_eq_nsmul_of_linearEquiv_fin (X := FiniteProjectiveModules.finFreeObj R n)
    (R' := FiniteProjectiveModules.selfObj R) (.refl R (Fin n → R)) (.refl R R)

/-- The class of the finite free module `ι → R` in `SplitK0` is `Fintype.card ι` times `[R]`. -/
@[simp] theorem of_freeObj {R : Type u} [Ring R] (ι : Type u) [Fintype ι] :
    SplitK0.of.{u} (FiniteProjectiveModules.freeObj R ι) =
      Fintype.card ι • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) :=
  of_eq_nsmul_of_linearEquiv_fin (X := FiniteProjectiveModules.freeObj R ι)
    (R' := FiniteProjectiveModules.selfObj R)
    (LinearEquiv.funCongrLeft R R (Fintype.equivFin ι).symm) (.refl R R)

/-- Every element of `SplitK0 (finiteProjectiveModules R).FullSubcategory` has the form
`[P] - n • [R]` for some finitely generated projective `R`-module `P` and `n : ℕ`
(Weibel, *The K-book*, Lemma II.2.1). -/
theorem exists_eq_of_sub_nsmul_selfObj {R : Type u} [Ring R]
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    ∃ (P : (finiteProjectiveModules R).FullSubcategory) (n : ℕ),
      x = SplitK0.of.{u} P - n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) := by
  obtain ⟨P₁, P₂, rfl⟩ := SplitK0.exists_eq_sub.{u} x
  obtain ⟨Q, n, ⟨e⟩⟩ := FiniteProjectiveModules.exists_biprod_iso_fin P₂
  refine ⟨P₁ ⊞ Q, n, ?_⟩
  have hQ : SplitK0.of.{u} P₂ + SplitK0.of.{u} Q =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) := by
    rw [← SplitK0.of_biprod.{u}, SplitK0.of_congr.{u} e, of_finFreeObj]
  rw [SplitK0.of_biprod.{u}, ← hQ]; abel

/-- Extension of scalars along `f : R →+* S` sends the class of the regular module `R` to the class
of the regular module `S`. -/
@[simp] theorem of_finiteProjectiveModulesExtendScalars_selfObj {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) :
    SplitK0.of.{u} (f.finiteProjectiveModulesExtendScalars.obj
        (FiniteProjectiveModules.selfObj R)) =
      SplitK0.of.{u} (FiniteProjectiveModules.selfObj S) :=
  (SplitK0.map_of.{u, u} f.finiteProjectiveModulesExtendScalars
    (FiniteProjectiveModules.selfObj R)).symm.trans <|
    map_finiteProjectiveModulesExtendScalars_of_linearEquiv_pi (f := f)
      (FiniteProjectiveModules.selfObj R) (FiniteProjectiveModules.selfObj S)
      (LinearEquiv.funUnique Unit R R).symm (LinearEquiv.funUnique Unit S S).symm

/-- Extension of scalars along `f : R →+* S` sends `[R]` to `[S]`. -/
theorem map_finiteProjectiveModulesExtendScalars_selfObj {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) :
    SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars
        (SplitK0.of.{u} (FiniteProjectiveModules.selfObj R)) =
      SplitK0.of.{u} (FiniteProjectiveModules.selfObj S) := by simp

end SplitK0

/-! ### Comparison between `SplitK0` and `ExactK0` of finitely generated projective modules -/

private theorem split_conflation_finiteProjectiveModules (R : Type u) [Ring R]
    {S : ShortComplex (finiteProjectiveModules R).FullSubcategory}
    (hS : (finiteProjectiveModulesExactStructure R).Conflation S) : Nonempty S.Splitting := by
  rw [finiteProjectiveModulesExactStructure_eq_split] at hS
  exact (ExactStructure.split_conflation S).mp hS

/-- **Comparison between split and exact `K₀` of finitely generated projective modules.** Every
short exact sequence splits (`TauCeti.finiteProjectiveModulesExactStructure_eq_split`), so
`TauCeti.ExactK0.fromSplit` is an isomorphism. -/
noncomputable def finiteProjectiveModulesSplitK0Equiv (R : Type u) [Ring R] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      ExactK0.{u} (finiteProjectiveModulesExactStructure R) :=
  ExactK0.fromSplitEquiv.{u} (split_conflation_finiteProjectiveModules R)

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_of (R : Type u) [Ring R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesSplitK0Equiv R (SplitK0.of.{u} P) = ExactK0.of.{u} P :=
  (ExactK0.fromSplitEquiv_apply.{u} (split_conflation_finiteProjectiveModules R)
    (SplitK0.of.{u} P)).trans (ExactK0.fromSplit_of.{u} P)

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_symm_of (R : Type u) [Ring R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    (finiteProjectiveModulesSplitK0Equiv R).symm (ExactK0.of.{u} P) = SplitK0.of.{u} P :=
  ExactK0.fromSplitEquiv_symm_of.{u} (split_conflation_finiteProjectiveModules R) P

/-- `TauCeti.finiteProjectiveModulesSplitK0Equiv` intertwines extension of scalars on `SplitK0` and
`ExactK0`. -/
theorem finiteProjectiveModulesSplitK0Equiv_comp_map_extendScalars {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) :
    (finiteProjectiveModulesSplitK0Equiv S).toAddMonoidHom.comp
        (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars) =
      f.finiteProjectiveModulesK0Extend.comp
        (finiteProjectiveModulesSplitK0Equiv R).toAddMonoidHom := SplitK0.hom_ext fun _ ↦ by simp

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_map_extendScalars {R S : Type u} [Ring R]
    [Ring S] (f : R →+* S) (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesSplitK0Equiv S
        (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars x) =
      f.finiteProjectiveModulesK0Extend (finiteProjectiveModulesSplitK0Equiv R x) :=
  DFunLike.congr_fun (finiteProjectiveModulesSplitK0Equiv_comp_map_extendScalars f) x

end TauCeti

/-! ### Morita invariance and ring-isomorphism invariance on `SplitK0` -/

namespace CategoryTheory.Equivalence

open TauCeti

variable {A : Type u} [Ring A] {B : Type u'} [Ring B] (e : ModuleCat.{u} A ≌ ModuleCat.{u'} B)

/-- **Morita invariance of `SplitK0` of finitely generated projective modules.** An equivalence
`e : ModuleCat A ≌ ModuleCat B` induces an isomorphism on `SplitK0` of finitely generated
projective modules. -/
noncomputable def finiteProjectiveModulesSplitK0Equiv :
    SplitK0.{u} (finiteProjectiveModules A).FullSubcategory ≃+
      SplitK0.{u'} (finiteProjectiveModules B).FullSubcategory :=
  SplitK0.mapEquiv.{u, u'} e.finiteProjectiveModulesEquivalence

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_of
    (P : (finiteProjectiveModules A).FullSubcategory) :
    e.finiteProjectiveModulesSplitK0Equiv (SplitK0.of.{u} P) =
      SplitK0.of.{u'} (e.finiteProjectiveModulesEquivalence.functor.obj P) :=
  SplitK0.mapEquiv_of.{u, u'} _ P

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_symm_of
    (Q : (finiteProjectiveModules B).FullSubcategory) :
    e.finiteProjectiveModulesSplitK0Equiv.symm (SplitK0.of.{u'} Q) =
      SplitK0.of.{u} (e.finiteProjectiveModulesEquivalence.inverse.obj Q) :=
  SplitK0.mapEquiv_symm_of.{u, u'} _ Q

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_toAddMonoidHom :
    (e.finiteProjectiveModulesSplitK0Equiv :
        SplitK0.{u} (finiteProjectiveModules A).FullSubcategory →+
          SplitK0.{u'} (finiteProjectiveModules B).FullSubcategory) =
      SplitK0.map.{u, u'} e.finiteProjectiveModulesEquivalence.functor :=
  SplitK0.mapEquiv_toAddMonoidHom.{u, u'} _

/-- `TauCeti.finiteProjectiveModulesSplitK0Equiv` intertwines Morita equivalences on `SplitK0` and
on `ExactK0`. -/
@[simp] theorem finiteProjectiveModulesSplitK0Equiv_apply_splitK0Equiv
    (x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) :
    TauCeti.finiteProjectiveModulesSplitK0Equiv B (e.finiteProjectiveModulesSplitK0Equiv x) =
      e.finiteProjectiveModulesK0Equiv (TauCeti.finiteProjectiveModulesSplitK0Equiv A x) :=
  DFunLike.congr_fun (SplitK0.hom_ext
    (f := (TauCeti.finiteProjectiveModulesSplitK0Equiv B).toAddMonoidHom.comp
      e.finiteProjectiveModulesSplitK0Equiv.toAddMonoidHom)
    (g := e.finiteProjectiveModulesK0Equiv.toAddMonoidHom.comp
      (TauCeti.finiteProjectiveModulesSplitK0Equiv A).toAddMonoidHom) fun _ ↦ by simp) x

end CategoryTheory.Equivalence

namespace RingEquiv

open TauCeti

section Basic

variable {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)

/-- A ring isomorphism `e : R ≃+* S` induces an isomorphism on `SplitK0` of finitely generated
projective modules by extension of scalars along `e` and `e.symm`. -/
noncomputable def finiteProjectiveModulesSplitK0Equiv :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      SplitK0.{u} (finiteProjectiveModules S).FullSubcategory :=
  AddMonoidHom.toAddEquiv
    (SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars)
    (SplitK0.map.{u, u} e.symm.toRingHom.finiteProjectiveModulesExtendScalars)
    (AddMonoidHom.ext fun x ↦ by simp) (AddMonoidHom.ext fun x ↦ by simp)

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_apply
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    e.finiteProjectiveModulesSplitK0Equiv x =
      SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars x := (rfl)

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_symm :
    e.finiteProjectiveModulesSplitK0Equiv.symm = e.symm.finiteProjectiveModulesSplitK0Equiv := (rfl)

/-- **Extension and restriction of scalars agree along a ring isomorphism.** For `e : R ≃+* S`,
extension of scalars along `e.toRingHom` induces the same map on `SplitK0` as restriction of scalars
along `e.symm` (`(ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm`). -/
theorem map_finiteProjectiveModulesExtendScalars_eq :
    SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars =
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          e).symm.finiteProjectiveModulesSplitK0Equiv :
        SplitK0.{u} (finiteProjectiveModules R).FullSubcategory →+
          SplitK0.{u} (finiteProjectiveModules S).FullSubcategory) := by
  refine SplitK0.hom_ext fun P ↦ ?_
  rw [SplitK0.map_of, Equivalence.finiteProjectiveModulesSplitK0Equiv_toAddMonoidHom,
    SplitK0.map_of]
  exact SplitK0.of_congr <| ObjectProperty.isoMk _ <|
    eqToIso (e.toRingHom.finiteProjectiveModulesExtendScalars_obj_obj P) ≪≫
      (BalancedExtension.functorRingEquivIso.{u, u, u} e).app P.obj ≪≫
      eqToIso ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        e).symm.finiteProjectiveModulesEquivalence_functor_obj_obj P).symm

theorem finiteProjectiveModulesSplitK0Equiv_eq_restrictScalars :
    e.finiteProjectiveModulesSplitK0Equiv =
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        e).symm.finiteProjectiveModulesSplitK0Equiv :=
  AddEquiv.toAddMonoidHom_injective (map_finiteProjectiveModulesExtendScalars_eq e)

end Basic

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_refl (R : Type u) [Ring R] :
    (RingEquiv.refl R).finiteProjectiveModulesSplitK0Equiv = AddEquiv.refl _ := by ext x; simp

theorem finiteProjectiveModulesSplitK0Equiv_trans {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (e : R ≃+* S) (e' : S ≃+* T) :
    (e.trans e').finiteProjectiveModulesSplitK0Equiv =
      e.finiteProjectiveModulesSplitK0Equiv.trans e'.finiteProjectiveModulesSplitK0Equiv := by
  ext x; simp [RingEquiv.toRingHom_trans]

end RingEquiv

namespace TauCeti

/-! ### Zero ring, binary product rings, matrix rings, and rank isomorphisms on `SplitK0` -/

/-- Over a subsingleton (zero) ring, every module is a zero object, so `SplitK0` of finitely
generated projective modules is trivial. -/
instance {R : Type u} [Ring R] [Subsingleton R] :
    Subsingleton (SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) := by
  have hzero : ∀ x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory, x = 0 := by
    refine DFunLike.congr_fun (SplitK0.hom_ext (f := AddMonoidHom.id _) (g := 0) fun P ↦ ?_)
    have : Subsingleton P.obj := ⟨fun x y ↦ by
      rw [← one_smul R x, Subsingleton.elim (1 : R) 0, zero_smul,
        ← one_smul R y, Subsingleton.elim (1 : R) 0, zero_smul]⟩
    exact SplitK0.of_eq_zero_of_isZero (IsZero.of_full_of_faithful_of_isZero
      (finiteProjectiveModules R).ι P (ModuleCat.isZero_of_subsingleton P.obj))
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

section ProdRing

section Aux

variable {E A B : Type u} [Ring E] [Ring A] [Ring B]

private theorem split_restrictScalars_finiteProjective (p : E →+* A) (j : A →+ E)
    (hpj : ∀ a, p (j a) = a) (hmul_left : ∀ e a, e * j a = j (p e * a)) :
    finiteProjectiveModules A ≤
      (finiteProjectiveModules E).inverseImage (ModuleCat.restrictScalars p) := by
  rw [RingHom.finiteProjectiveModules_le_inverseImage_restrictScalars_iff]
  let : Module E A := p.toModule
  let i : A →ₗ[E] E := { toAddHom := j.toAddHom, map_smul' e a := (hmul_left e a).symm }
  let q : E →ₗ[E] A := { toAddHom := p.toAddMonoidHom.toAddHom, map_smul' := p.map_mul }
  exact ⟨Module.Finite.of_surjective q fun a ↦ ⟨j a, hpj a⟩,
    Module.Projective.of_split i q (LinearMap.ext hpj)⟩

private noncomputable def splitRestrictFunctor (p : E →+* A) (j : A →+ E)
    (hpj : ∀ a, p (j a) = a) (hmul_left : ∀ e a, e * j a = j (p e * a)) :
    (finiteProjectiveModules A).FullSubcategory ⥤ (finiteProjectiveModules E).FullSubcategory :=
  (finiteProjectiveModules E).lift ((finiteProjectiveModules A).ι ⋙ ModuleCat.restrictScalars.{u} p)
    fun M ↦ split_restrictScalars_finiteProjective p j hpj hmul_left M.obj M.property

private theorem additive_splitRestrictFunctor (p : E →+* A) (j : A →+ E)
    (hpj : ∀ a, p (j a) = a) (hmul_left : ∀ e a, e * j a = j (p e * a)) :
    (splitRestrictFunctor p j hpj hmul_left).Additive := by
  have : (splitRestrictFunctor p j hpj hmul_left ⋙ (finiteProjectiveModules E).ι).Additive :=
    inferInstanceAs ((finiteProjectiveModules A).ι ⋙ ModuleCat.restrictScalars.{u} p).Additive
  exact Functor.additive_of_comp_faithful _ (finiteProjectiveModules E).ι

private theorem of_extendScalars_splitRestrict_orth_eq_zero (p : E →+* A) (p' : E →+* B)
    (j : B →+ E) (hp'j : ∀ b, p' (j b) = b) (hmul_left : ∀ x b, x * j b = j (p' x * b))
    (e : E) (hp : p e = 1) (hp' : p' e = 0) (N : (finiteProjectiveModules B).FullSubcategory) :
    SplitK0.of.{u}
        (p.finiteProjectiveModulesExtendScalars.obj
          ((splitRestrictFunctor p' j hp'j hmul_left).obj N)) = 0 := by
  let Z : ModuleCat.{u} A :=
    ModuleCat.of A (BalancedExtension p ((ModuleCat.restrictScalars.{u} p').obj N.obj))
  have : Subsingleton Z :=
    BalancedExtension.subsingleton_restrictScalars_of_orth p p' e hp hp' N.obj
  exact SplitK0.of_eq_zero_of_isZero <| IsZero.of_full_of_faithful_of_isZero
    (finiteProjectiveModules A).ι _ <| (ModuleCat.isZero_of_subsingleton Z).of_iso
      (eqToIso (p.finiteProjectiveModulesExtendScalars_obj_obj _))

end Aux

variable (R S : Type u) [Ring R] [Ring S]

private noncomputable def prodInlFunctor :
    (finiteProjectiveModules R).FullSubcategory ⥤
      (finiteProjectiveModules (R × S)).FullSubcategory :=
  splitRestrictFunctor (RingHom.fst R S) (AddMonoidHom.inl R S) (by simp) AddMonoidHom.mul_inl

private instance : (prodInlFunctor R S).Additive := additive_splitRestrictFunctor _ _ _ _

private noncomputable def prodInrFunctor :
    (finiteProjectiveModules S).FullSubcategory ⥤
      (finiteProjectiveModules (R × S)).FullSubcategory :=
  splitRestrictFunctor (RingHom.snd R S) (AddMonoidHom.inr R S) (by simp) AddMonoidHom.mul_inr

private instance : (prodInrFunctor R S).Additive := additive_splitRestrictFunctor _ _ _ _

/-- **`SplitK0` of finitely generated projective modules commutes with binary products of rings.**
The forward map applies extension of scalars along `RingHom.fst R S` and `RingHom.snd R S`, and the
inverse adds restriction of scalars along the two projections. -/
noncomputable def finiteProjectiveModulesProdSplitK0Equiv :
    SplitK0.{u} (finiteProjectiveModules (R × S)).FullSubcategory ≃+
      SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ×
        SplitK0.{u} (finiteProjectiveModules S).FullSubcategory :=
  AddEquiv.ofProdCoprod
    (SplitK0.map.{u, u} (RingHom.fst R S).finiteProjectiveModulesExtendScalars)
    (SplitK0.map.{u, u} (RingHom.snd R S).finiteProjectiveModulesExtendScalars)
    (SplitK0.map.{u, u} (prodInlFunctor R S))
    (SplitK0.map.{u, u} (prodInrFunctor R S))
    (SplitK0.hom_ext fun P ↦ by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.prod_apply, AddMonoidHom.coprod_apply,
        SplitK0.map_of, AddMonoidHom.id_apply]
      let e₁ := ((ModuleCat.restrictScalars.{u} (RingHom.fst R S)).mapIso
        (eqToIso ((RingHom.fst R S).finiteProjectiveModulesExtendScalars_obj_obj
          P).symm)).toLinearEquiv
      let e₂ := ((ModuleCat.restrictScalars.{u} (RingHom.snd R S)).mapIso
        (eqToIso ((RingHom.snd R S).finiteProjectiveModulesExtendScalars_obj_obj
          P).symm)).toLinearEquiv
      exact (SplitK0.of_eq_add_of_linearEquiv_prod
        ((BalancedExtension.prodModuleLinearEquiv R S P.obj).trans (e₁.prodCongr e₂))).symm)
    (SplitK0.hom_ext fun M ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.id_apply]
      exact SplitK0.of_extendScalars_obj
        (BalancedExtension.restrictScalarsSelfEquiv (RingHom.fst R S) (AddMonoidHom.inl R S)
          (by simp) M.obj))
    (SplitK0.hom_ext fun N ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.zero_apply]
      exact of_extendScalars_splitRestrict_orth_eq_zero (RingHom.fst R S) (RingHom.snd R S)
        (AddMonoidHom.inr R S) (by simp) AddMonoidHom.mul_inr (1, 0) rfl rfl N)
    (SplitK0.hom_ext fun M ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.zero_apply]
      exact of_extendScalars_splitRestrict_orth_eq_zero (RingHom.snd R S) (RingHom.fst R S)
        (AddMonoidHom.inl R S) (by simp) AddMonoidHom.mul_inl (0, 1) rfl rfl M)
    (SplitK0.hom_ext fun N ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.id_apply]
      exact SplitK0.of_extendScalars_obj
        (BalancedExtension.restrictScalarsSelfEquiv (RingHom.snd R S) (AddMonoidHom.inr R S)
          (by simp) N.obj))

@[simp] theorem finiteProjectiveModulesProdSplitK0Equiv_apply
    (x : SplitK0.{u} (finiteProjectiveModules (R × S)).FullSubcategory) :
    finiteProjectiveModulesProdSplitK0Equiv R S x =
      (SplitK0.map.{u, u} (RingHom.fst R S).finiteProjectiveModulesExtendScalars x,
        SplitK0.map.{u, u} (RingHom.snd R S).finiteProjectiveModulesExtendScalars x) :=
  AddEquiv.ofProdCoprod_apply _ _ _ _ _ _ _ _ _ x

theorem finiteProjectiveModulesProdSplitK0Equiv_selfObj :
    finiteProjectiveModulesProdSplitK0Equiv R S
        (SplitK0.of.{u} (FiniteProjectiveModules.selfObj (R × S))) =
      (SplitK0.of.{u} (FiniteProjectiveModules.selfObj R),
        SplitK0.of.{u} (FiniteProjectiveModules.selfObj S)) := by simp

end ProdRing

section MatrixMorita

variable (R : Type u) [Ring R]

section Index

variable (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The canonical functor sending a finitely generated projective `R`-module `P` to the finitely
generated projective `Matrix ι ι R`-module `ι → P`, manifestly independent of any choice of index
in `ι`. -/
noncomputable def finiteProjectiveModulesToMatrixFunctor :
    (finiteProjectiveModules R).FullSubcategory ⥤
      (finiteProjectiveModules (Matrix ι ι R)).FullSubcategory :=
  (finiteProjectiveModules (Matrix ι ι R)).lift
    ((finiteProjectiveModules R).ι ⋙ ModuleCat.toMatrixModCat R ι) fun P ↦ by
      obtain ⟨i⟩ := ‹Nonempty ι›
      have h := congrFun
        (ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModules_inverseImage P.obj
      exact (ObjectProperty.prop_inverseImage_iff _ _ P.obj).mp (h.symm ▸ P.property)

instance : (finiteProjectiveModulesToMatrixFunctor R ι).Additive := by
  have : (finiteProjectiveModulesToMatrixFunctor R ι ⋙
      (finiteProjectiveModules (Matrix ι ι R)).ι).Additive :=
    inferInstanceAs ((finiteProjectiveModules R).ι ⋙ ModuleCat.toMatrixModCat R ι).Additive
  exact Functor.additive_of_comp_faithful _ (finiteProjectiveModules (Matrix ι ι R)).ι

@[simp] theorem finiteProjectiveModulesToMatrixFunctor_obj_obj
    (P : (finiteProjectiveModules R).FullSubcategory) :
    ((finiteProjectiveModulesToMatrixFunctor R ι).obj P).obj =
      (ModuleCat.toMatrixModCat R ι).obj P.obj := (rfl)

/-- For any index `i : ι`, `TauCeti.finiteProjectiveModulesToMatrixFunctor` induces the same map on
`SplitK0` as `ModuleCat.matrixEquivalence R i`. -/
theorem map_finiteProjectiveModulesToMatrixFunctor_eq (i : ι) :
    SplitK0.map.{u, u} (finiteProjectiveModulesToMatrixFunctor R ι) =
      ((ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModulesSplitK0Equiv :
        SplitK0.{u} (finiteProjectiveModules R).FullSubcategory →+
          SplitK0.{u} (finiteProjectiveModules (Matrix ι ι R)).FullSubcategory) := by
  rw [Equivalence.finiteProjectiveModulesSplitK0Equiv_toAddMonoidHom]
  exact SplitK0.map_congr.{u, u} fun P ↦ ⟨ObjectProperty.isoMk _ (eqToIso
    ((ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModulesEquivalence_functor_obj_obj
      P).symm)⟩

/-- **Matrix Morita invariance of `SplitK0`.** Sending `P` to the column module `ι → P` induces an
isomorphism `SplitK0 (finiteProjectiveModules R).FullSubcategory ≃+
SplitK0 (finiteProjectiveModules (Matrix ι ι R)).FullSubcategory` whose underlying map is
independent of any choice of index in `ι`. -/
noncomputable def finiteProjectiveModulesMatrixSplitK0Equiv :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      SplitK0.{u} (finiteProjectiveModules (Matrix ι ι R)).FullSubcategory :=
  AddEquiv.ofBijective (SplitK0.map.{u, u} (finiteProjectiveModulesToMatrixFunctor R ι)) <| by
    obtain ⟨i⟩ := ‹Nonempty ι›
    rw [map_finiteProjectiveModulesToMatrixFunctor_eq R ι i]
    exact (ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModulesSplitK0Equiv.bijective

theorem finiteProjectiveModulesMatrixSplitK0Equiv_apply
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesMatrixSplitK0Equiv R ι x =
      SplitK0.map.{u, u} (finiteProjectiveModulesToMatrixFunctor R ι) x := (rfl)

@[simp] theorem finiteProjectiveModulesMatrixSplitK0Equiv_of
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesMatrixSplitK0Equiv R ι (SplitK0.of.{u} P) =
      SplitK0.of.{u} ((finiteProjectiveModulesToMatrixFunctor R ι).obj P) :=
  SplitK0.map_of.{u, u} _ P

/-- For every `i : ι`, `TauCeti.finiteProjectiveModulesMatrixSplitK0Equiv` agrees with the
Morita equivalence induced by `ModuleCat.matrixEquivalence R i`. -/
theorem finiteProjectiveModulesMatrixSplitK0Equiv_eq (i : ι) :
    finiteProjectiveModulesMatrixSplitK0Equiv R ι =
      (ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModulesSplitK0Equiv :=
  AddEquiv.toAddMonoidHom_injective (map_finiteProjectiveModulesToMatrixFunctor_eq R ι i)

/-- Under `TauCeti.finiteProjectiveModulesMatrixSplitK0Equiv`, `|ι|` copies of `[R]` map to the
class of the regular module `[Matrix ι ι R]`. -/
@[simp] theorem finiteProjectiveModulesMatrixSplitK0Equiv_card_nsmul_selfObj :
    finiteProjectiveModulesMatrixSplitK0Equiv R ι
        (Fintype.card ι • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R)) =
      SplitK0.of.{u} (FiniteProjectiveModules.selfObj (Matrix ι ι R)) := by
  rw [← SplitK0.of_freeObj (R := R) ι, finiteProjectiveModulesMatrixSplitK0Equiv_of]
  exact SplitK0.of_congr (ObjectProperty.isoMk _
    (matrixOfColumnModuleLinearEquiv R ι).toModuleIso)

end Index

section Fin

variable (n : ℕ) [NeZero n]

/-- **Matrix Morita invariance of `SplitK0` for `n × n` matrices (`n ≠ 0`)** over an arbitrary
universe-polymorphic ring `R : Type u`. -/
noncomputable def finiteProjectiveModulesMatrixFinSplitK0Equiv :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      SplitK0.{u} (finiteProjectiveModules (Matrix (Fin n) (Fin n) R)).FullSubcategory :=
  (finiteProjectiveModulesMatrixSplitK0Equiv R (ULift.{u} (Fin n))).trans
    (Matrix.reindexRingEquiv R Equiv.ulift).finiteProjectiveModulesSplitK0Equiv

theorem finiteProjectiveModulesMatrixFinSplitK0Equiv_apply
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesMatrixFinSplitK0Equiv R n x =
      (Matrix.reindexRingEquiv R Equiv.ulift).finiteProjectiveModulesSplitK0Equiv
        (finiteProjectiveModulesMatrixSplitK0Equiv R (ULift.{u} (Fin n)) x) := (rfl)

@[simp] theorem finiteProjectiveModulesMatrixFinSplitK0Equiv_of
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesMatrixFinSplitK0Equiv R n (SplitK0.of.{u} P) =
      SplitK0.of.{u}
        ((Matrix.reindexRingEquiv R
            Equiv.ulift).toRingHom.finiteProjectiveModulesExtendScalars.obj
          ((finiteProjectiveModulesToMatrixFunctor R (ULift.{u} (Fin n))).obj P)) := by
  simp [finiteProjectiveModulesMatrixFinSplitK0Equiv_apply]

@[simp] theorem finiteProjectiveModulesMatrixFinSplitK0Equiv_nsmul_selfObj :
    finiteProjectiveModulesMatrixFinSplitK0Equiv R n
        (n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R)) =
      SplitK0.of.{u} (FiniteProjectiveModules.selfObj (Matrix (Fin n) (Fin n) R)) := by
  have h := finiteProjectiveModulesMatrixSplitK0Equiv_card_nsmul_selfObj R (ULift.{u} (Fin n))
  simp only [Fintype.card_ulift, Fintype.card_fin] at h
  rw [finiteProjectiveModulesMatrixFinSplitK0Equiv_apply, h,
    RingEquiv.finiteProjectiveModulesSplitK0Equiv_apply,
    SplitK0.map_finiteProjectiveModulesExtendScalars_selfObj]

end Fin

end MatrixMorita

section Finrank

section OfFree

variable (R : Type u) [Ring R] [StrongRankCondition R]

@[simp] theorem FiniteProjectiveModules.finrank_selfObj :
    Module.finrank R (FiniteProjectiveModules.selfObj R).obj = 1 :=
  ModuleCat.finrank_of_self R

variable (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj)

private noncomputable def finrankSplitK0Invariant :
    SplitK0.AdditiveInvariant (finiteProjectiveModules R).FullSubcategory ℤ where
  obj P := (Module.finrank R P.obj : ℤ)
  map_iso P Q e :=
    congrArg Nat.cast (((finiteProjectiveModules R).ι.mapIso e).toLinearEquiv.finrank_eq)
  map_biprod P Q := by
    have := hfree P; have := hfree Q
    exact_mod_cast (FiniteProjectiveModules.biprodLinearEquiv P Q).finrank_eq.trans
      Module.finrank_prod

/-- **Rank isomorphism `K₀(proj R) ≃+ ℤ` when finitely generated projective modules are free.**
Over a ring `R` satisfying `StrongRankCondition R` in which every finitely generated projective
left `R`-module is free, `Module.finrank` descends to an isomorphism sending `[P]` to `finrank R P`
and `[R]` to `1`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivOfFree :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+ ℤ :=
  AddMonoidHom.toAddEquiv
    (SplitK0.lift.{u} (finrankSplitK0Invariant R hfree))
    (zmultiplesHom (SplitK0.{u} (finiteProjectiveModules R).FullSubcategory)
      (SplitK0.of.{u} (FiniteProjectiveModules.selfObj R)))
    (SplitK0.hom_ext fun P ↦ by
      have := hfree P
      simp only [AddMonoidHom.comp_apply, SplitK0.lift_of, finrankSplitK0Invariant,
        zmultiplesHom_apply, natCast_zsmul, AddMonoidHom.id_apply]
      exact (SplitK0.of_eq_nsmul_of_linearEquiv_fin (X := P)
        (R' := FiniteProjectiveModules.selfObj R)
        (Module.finBasis R P.obj).equivFun (.refl R R)).symm)
    (AddMonoidHom.ext_int <| by simp [finrankSplitK0Invariant])

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivOfFree_of
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesFinrankSplitK0EquivOfFree R hfree (SplitK0.of.{u} P) =
      (Module.finrank R P.obj : ℤ) :=
  SplitK0.lift_of.{u} _ P

theorem finiteProjectiveModulesFinrankSplitK0EquivOfFree_selfObj :
    finiteProjectiveModulesFinrankSplitK0EquivOfFree R hfree
        (SplitK0.of.{u} (FiniteProjectiveModules.selfObj R)) = 1 := by simp

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivOfFree_symm_apply (n : ℤ) :
    (finiteProjectiveModulesFinrankSplitK0EquivOfFree R hfree).symm n =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) := (rfl)

end OfFree

/-- Over a division ring `D`, `Module.finrank` induces `K₀(proj D) ≃+ ℤ`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivDivisionRing (D : Type u)
    [DivisionRing D] : SplitK0.{u} (finiteProjectiveModules D).FullSubcategory ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree D fun _ ↦ inferInstance

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivDivisionRing_of (D : Type u)
    [DivisionRing D] (P : (finiteProjectiveModules D).FullSubcategory) :
    finiteProjectiveModulesFinrankSplitK0EquivDivisionRing D (SplitK0.of.{u} P) =
      (Module.finrank D P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree_of D _ P

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivDivisionRing_symm_apply (D : Type u)
    [DivisionRing D] (n : ℤ) :
    (finiteProjectiveModulesFinrankSplitK0EquivDivisionRing D).symm n =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj D) := (rfl)

section PID

variable (R : Type u) [Ring R] [Nontrivial R] [NoZeroDivisors R] [IsPrincipalIdealRing R]

/-- Over a nontrivial principal left-ideal ring without zero divisors, `Module.finrank` induces
`K₀(proj R) ≃+ ℤ`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivPID :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree R fun P ↦
    Module.Free.of_injective_of_projective_of_isPrincipalIdealRing
      (LinearMap.id : P.obj →ₗ[R] P.obj) Function.injective_id

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivPID_of
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesFinrankSplitK0EquivPID R (SplitK0.of.{u} P) =
      (Module.finrank R P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree_of R _ P

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivPID_symm_apply (n : ℤ) :
    (finiteProjectiveModulesFinrankSplitK0EquivPID R).symm n =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) := (rfl)

end PID

section LocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Over a commutative local ring `R`, `Module.finrank` induces `K₀(proj R) ≃+ ℤ`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivLocalRing :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree R fun _ ↦
    Module.free_of_projective_of_isLocalRing

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivLocalRing_of
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesFinrankSplitK0EquivLocalRing R (SplitK0.of.{u} P) =
      (Module.finrank R P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree_of R _ P

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivLocalRing_symm_apply (n : ℤ) :
    (finiteProjectiveModulesFinrankSplitK0EquivLocalRing R).symm n =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) := (rfl)

end LocalRing

end Finrank

end TauCeti
