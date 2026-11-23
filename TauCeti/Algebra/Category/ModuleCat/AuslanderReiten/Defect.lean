/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Module.AuslanderReiten.Defect
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.MatlisDualTranspose
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.YonedaExt.Injective
public import TauCeti.CategoryTheory.Exact.YonedaExt.Projective

/-!
# The defects of a short exact sequence of modules

Let `R` be a commutative ring and `A` an `R`-algebra. The defects of a map of `A`-modules
(`TauCeti/Algebra/Module/AuslanderReiten/Defect.lean`) are cokernels of `R`-linear maps between
`Hom` spaces of `ModuleCat A`. For a short exact sequence whose middle term is injective or
projective they are identified with `Ext¹` and with stable `Hom` spaces:

* for `N ⟶ I ⟶ N'` with `I` injective, the contravariant defect at `Y` is `Ext¹(Y, N)` and the
  covariant defect at `τX = D Tr X` is `Hom(N, τX)` modulo the injectively trivial maps;
* for `K ⟶ P ⟶ M` with `P` projective, the contravariant defect at `Y` is `Hom(Y, M)` modulo the
  maps through projectives and the covariant defect at `τX` is `Ext¹(M, τX)`.

These are the categorical sides of Auslander's defect formula, used for the two
Auslander–Reiten formulas.

## Implementation notes

The covariant defects are taken at the translate `τX` only. For a general `A`-module `W` with a
compatible native `R`-action, the `Hom` spaces `N ⟶ ModuleCat.of A W` carry two `R`-module
structures, from `W` and from the `R`-linear structure of `ModuleCat A`, which agree only
propositionally (see `TauCeti/Algebra/Category/ModuleCat/AuslanderReiten/MatlisDualTranspose.lean`).

## Main definitions

* `ModuleCat.contravariantDefectEquivHomQuotient` and `ModuleCat.covariantDefectEquivHomQuotient`:
  the defects as cokernels of `R`-linear maps between `Hom` spaces of `ModuleCat A`.
* `ModuleCat.contravariantDefectEquivExt1` and `ModuleCat.covariantDefectEquivCostableHom`: the
  defects of a short exact sequence with injective middle term.
* `ModuleCat.contravariantDefectEquivStableHom` and `ModuleCat.covariantDefectEquivExt1`: the
  defects of a short exact sequence with projective middle term.

## Main results

* `ModuleCat.contravariantDefectEquivStableHom_map` and
  `ModuleCat.contravariantDefectEquivStableHom_comap`: naturality of the contravariant
  identification in the sequence and in the test module.
* `ModuleCat.covariantDefectEquivExt1_map` and `ModuleCat.covariantDefectEquivExt1_homCokernelMap`:
  naturality of the covariant identification in the sequence and in the presented module.

## References

* H. Krause, *A short proof for Auslander's defect formula*, Linear Algebra Appl. **365** (2003),
  267–270.
-/

public section

namespace ModuleCat

open CategoryTheory TauCeti TauCeti.ExactStructure LinearMap
open scoped ModuleCat.Algebra

universe u v w t

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-! ### Defects as cokernels of `Hom` maps -/

/-- The contravariant defect of a map `g : M ⟶ N` of `A`-modules at `Y`, as the cokernel of the
`R`-linear map `Hom(Y, M) → Hom(Y, N)` between `Hom` spaces of `ModuleCat A`. -/
noncomputable def contravariantDefectEquivHomQuotient {M N : ModuleCat.{t} A} (g : M ⟶ N)
    (Y : ModuleCat.{t} A) :
    contravariantDefect R g.hom Y ≃ₗ[R] ((Y ⟶ N) ⧸ LinearMap.range (Linear.rightComp R Y g)) :=
  (Submodule.Quotient.equiv _ _ (homLinearEquiv (S := R)) (by
    rw [← LinearMap.range_comp,
      show (homLinearEquiv (S := R) : (Y ⟶ N) ≃ₗ[R] (Y →ₗ[A] N)).toLinearMap ∘ₗ
          Linear.rightComp R Y g =
        g.hom.compRight R ∘ₗ (homLinearEquiv (S := R) : (Y ⟶ M) ≃ₗ[R] (Y →ₗ[A] M)).toLinearMap
        from LinearMap.ext fun _ ↦ rfl,
      LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)])).symm

/-- The class of `g' : Y → N` in the contravariant defect is the class of the morphism `g'`. -/
@[simp]
theorem contravariantDefectEquivHomQuotient_mk {M N : ModuleCat.{t} A} (g : M ⟶ N)
    {Y : ModuleCat.{t} A} (g' : Y →ₗ[A] N) :
    contravariantDefectEquivHomQuotient R g Y (Submodule.Quotient.mk g') =
      Submodule.Quotient.mk (ofHom g') := by
  simp only [contravariantDefectEquivHomQuotient, Submodule.Quotient.equiv_symm,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  rfl

/-! ### Sequences with injective middle term -/

section Injective

variable {N N' : ModuleCat.{t} A} (e : (ExactStructure.abelian _).Extension N' N)
  (he : (ExactStructure.abelian _).isInjective e.obj)

/-- **The contravariant defect is `Ext¹`.** For a short exact sequence `N ⟶ I ⟶ N'` of
`A`-modules with `I` injective, the cokernel of `Hom_A(Y, I) → Hom_A(Y, N')` is `Ext¹(Y, N)`,
through `u ↦ u^* [N ⟶ I ⟶ N']`. -/
noncomputable def contravariantDefectEquivExt1 (Y : ModuleCat.{t} A) :
    contravariantDefect R e.g.hom Y ≃ₗ[R] (ExactStructure.abelian _).Ext1 Y N :=
  contravariantDefectEquivHomQuotient R e.g Y ≪≫ₗ e.homQuotientEquivExt1 he R Y

/-- The class of `g : Y → N'` in the contravariant defect is the base change `g^* [N ⟶ I ⟶ N']`.
-/
@[simp]
theorem contravariantDefectEquivExt1_mk {Y : ModuleCat.{t} A} (g : Y →ₗ[A] N') :
    contravariantDefectEquivExt1 R e he Y (Submodule.Quotient.mk g) =
      (Ext1.mk e).pullback (ofHom g) := by
  simp only [contravariantDefectEquivExt1, LinearEquiv.trans_apply,
    contravariantDefectEquivHomQuotient_mk, Extension.homQuotientEquivExt1_mk]

end Injective

/-! ### Sequences with projective middle term -/

section Projective

variable {M K : ModuleCat.{t} A} (e : (ExactStructure.abelian _).Extension M K)
  (he : (ExactStructure.abelian _).isProjective e.obj)

/-- **The contravariant defect is stable `Hom`.** For a short exact sequence `K ⟶ P ⟶ M` of
`A`-modules with `P` projective, the cokernel of `Hom_A(Y, P) → Hom_A(Y, M)` is the `Hom` space
from `Y` to `M` modulo the maps factoring through projectives. -/
noncomputable def contravariantDefectEquivStableHom (Y : ModuleCat.{t} A) :
    contravariantDefect R e.g.hom Y ≃ₗ[R]
      ((ExactStructure.abelian _).projectiveStableFunctor.obj Y ⟶
        (ExactStructure.abelian _).projectiveStableFunctor.obj M) :=
  contravariantDefectEquivHomQuotient R e.g Y ≪≫ₗ e.homQuotientEquivStableHom he R Y

/-- The class of `g : Y → M` in the contravariant defect is its stable class. -/
@[simp]
theorem contravariantDefectEquivStableHom_mk {Y : ModuleCat.{t} A} (g : Y →ₗ[A] M) :
    contravariantDefectEquivStableHom R e he Y (Submodule.Quotient.mk g) =
      (ExactStructure.abelian _).projectiveStableFunctor.map (ofHom g) := by
  simp only [contravariantDefectEquivStableHom, LinearEquiv.trans_apply,
    contravariantDefectEquivHomQuotient_mk, Extension.homQuotientEquivStableHom_mk]

/-- **Naturality of the contravariant defect as stable `Hom` in the sequence.** For a morphism
`(a₂, f)` from `K ⟶ P ⟶ M` to `K' ⟶ P' ⟶ M'`, postcomposition with `f` on defects is
postcomposition with the stable class of `f`. -/
theorem contravariantDefectEquivStableHom_map {M' K' : ModuleCat.{t} A}
    (e' : (ExactStructure.abelian _).Extension M' K')
    (he' : (ExactStructure.abelian _).isProjective e'.obj) {a₂ : e.obj ⟶ e'.obj} {f : M ⟶ M'}
    (h : f.hom ∘ₗ e.g.hom = e'.g.hom ∘ₗ a₂.hom) {Y : ModuleCat.{t} A}
    (x : contravariantDefect R e.g.hom Y) :
    contravariantDefectEquivStableHom R e' he' Y (contravariantDefectMap R h Y x) =
      contravariantDefectEquivStableHom R e he Y x ≫
        (ExactStructure.abelian _).projectiveStableFunctor.map f := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [contravariantDefectMap_mk, contravariantDefectEquivStableHom_mk,
    contravariantDefectEquivStableHom_mk, ← Functor.map_comp]
  rfl

/-- **Naturality of the contravariant defect as stable `Hom` in the test module.** Precomposition
with `t : Y ⟶ Y'` on defects is precomposition with the stable class of `t`. -/
theorem contravariantDefectEquivStableHom_comap {Y Y' : ModuleCat.{t} A} (s : Y ⟶ Y')
    (x : contravariantDefect R e.g.hom Y') :
    contravariantDefectEquivStableHom R e he Y (contravariantDefectComap R e.g.hom s.hom x) =
      (ExactStructure.abelian _).projectiveStableFunctor.map s ≫
        contravariantDefectEquivStableHom R e he Y' x := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [contravariantDefectComap_mk, contravariantDefectEquivStableHom_mk,
    contravariantDefectEquivStableHom_mk, ← Functor.map_comp]
  rfl

end Projective

/-! ### Covariant defects at the translate `D Tr X` -/

section Translate

variable (E : Type w) [AddCommGroup E] [Module R E] {X : ModuleCat.{max u v w} A}
  (P : FiniteProjectivePresentation X)

/-- The covariant defect of a map `f : N ⟶ N'` at `τX = D Tr X`, as the cokernel of the
`R`-linear map `Hom(N', τX) → Hom(N, τX)` between `Hom` spaces of `ModuleCat A`. -/
noncomputable def covariantDefectEquivHomQuotient {N N' : ModuleCat.{max u v w} A} (f : N ⟶ N') :
    covariantDefect R f.hom (MatlisDual R E (AuslanderReitenTranspose P.p)) ≃ₗ[R]
      ((N ⟶ matlisDualTranspose R E P) ⧸
        LinearMap.range (Linear.leftComp R (matlisDualTranspose R E P) f)) :=
  Submodule.Quotient.equiv _ _ (matlisDualTransposeHomEquiv R E P N).symm (by
    rw [← LinearMap.range_comp,
      show (matlisDualTransposeHomEquiv R E P N).symm.toLinearMap ∘ₗ
          f.hom.lcomp R (MatlisDual R E (AuslanderReitenTranspose P.p)) =
        Linear.leftComp R (matlisDualTranspose R E P) f ∘ₗ
          (matlisDualTransposeHomEquiv R E P N').symm.toLinearMap
        from LinearMap.ext fun _ ↦ by ext; simp; rfl,
      LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)])

/-- The class of `u : N → D Tr X` in the covariant defect is the class of the morphism `u`. -/
@[simp]
theorem covariantDefectEquivHomQuotient_mk {N N' : ModuleCat.{max u v w} A} (f : N ⟶ N')
    (u : N →ₗ[A] MatlisDual R E (AuslanderReitenTranspose P.p)) :
    covariantDefectEquivHomQuotient R E P f (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ((matlisDualTransposeHomEquiv R E P N).symm u) :=
  (rfl)

section Injective

variable {N N' : ModuleCat.{max u v w} A} (e : (ExactStructure.abelian _).Extension N' N)
  (he : (ExactStructure.abelian _).isInjective e.obj)

/-- **The covariant defect at `τX` is costable `Hom`.** For a short exact sequence `N ⟶ I ⟶ N'`
with `I` injective, the cokernel of `Hom_A(I, τX) → Hom_A(N, τX)` is `(A/ℐ)(N, τX)`. -/
noncomputable def covariantDefectEquivCostableHom :
    covariantDefect R e.f.hom (MatlisDual R E (AuslanderReitenTranspose P.p)) ≃ₗ[R]
      ((ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj N ⟶
        (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj
          (matlisDualTranspose R E P)) :=
  covariantDefectEquivHomQuotient R E P e.f ≪≫ₗ e.homQuotientEquivCostableHom he R _

/-- The class of `u : N → D Tr X` in the covariant defect is the class of `u` modulo `ℐ`. -/
@[simp]
theorem covariantDefectEquivCostableHom_mk
    (u : N →ₗ[A] MatlisDual R E (AuslanderReitenTranspose P.p)) :
    covariantDefectEquivCostableHom R E P e he (Submodule.Quotient.mk u) =
      (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.map
        ((matlisDualTransposeHomEquiv R E P N).symm u) := by
  simp [covariantDefectEquivCostableHom]

end Injective

section Projective

variable {M K : ModuleCat.{max u v w} A} (e : (ExactStructure.abelian _).Extension M K)
  (he : (ExactStructure.abelian _).isProjective e.obj)

/-- **The covariant defect at `τX` is `Ext¹`.** For a short exact sequence `K ⟶ P ⟶ M` with `P`
projective, the cokernel of `Hom_A(P, τX) → Hom_A(K, τX)` is `Ext¹(M, τX)`, through
`v ↦ v_* [K ⟶ P ⟶ M]`. -/
noncomputable def covariantDefectEquivExt1 :
    covariantDefect R e.f.hom (MatlisDual R E (AuslanderReitenTranspose P.p)) ≃ₗ[R]
      (ExactStructure.abelian _).Ext1 M (matlisDualTranspose R E P) :=
  covariantDefectEquivHomQuotient R E P e.f ≪≫ₗ e.homQuotientEquivExt1OfIsProjective he R _

/-- The class of `v : K → τX` in the covariant defect is the cobase change `v_* [K ⟶ P ⟶ M]`. -/
@[simp]
theorem covariantDefectEquivExt1_mk (v : K →ₗ[A] MatlisDual R E (AuslanderReitenTranspose P.p)) :
    covariantDefectEquivExt1 R E P e he (Submodule.Quotient.mk v) =
      (Ext1.mk e).pushout ((matlisDualTransposeHomEquiv R E P K).symm v) := by
  simp [covariantDefectEquivExt1]

/-- **Naturality of the covariant defect at `τX` in the sequence.** For a morphism `(a₁, a₂, f)`
from `K ⟶ P ⟶ M` to `K' ⟶ P' ⟶ M'`, precomposition with `a₁` on defects is base change along
`f`. -/
theorem covariantDefectEquivExt1_map {M' K' : ModuleCat.{max u v w} A}
    (e' : (ExactStructure.abelian _).Extension M' K')
    (he' : (ExactStructure.abelian _).isProjective e'.obj) {a₁ : K ⟶ K'} {a₂ : e.obj ⟶ e'.obj}
    {f : M ⟶ M'} (h₁ : e.f ≫ a₂ = a₁ ≫ e'.f) (h₂ : e.g ≫ f = a₂ ≫ e'.g)
    (y : covariantDefect R e'.f.hom (MatlisDual R E (AuslanderReitenTranspose P.p))) :
    covariantDefectEquivExt1 R E P e he
        (covariantDefectMap R (φ := e.f.hom) (φ' := e'.f.hom) (a₁ := a₁.hom) (a₂ := a₂.hom)
          (congrArg Hom.hom h₁) _ y) =
      (covariantDefectEquivExt1 R E P e' he' y).pullback f := by
  induction y using Submodule.Quotient.induction_on with
  | _ v =>
    rw [covariantDefectMap_mk, covariantDefectEquivExt1_mk, covariantDefectEquivExt1_mk,
      Ext1.pushout_pullback, ← Ext1.pushout_mk_eq_pullback_mk a₂ h₁ h₂.symm, Ext1.pushout_pushout]
    congr 1
    ext
    simp
    rfl

/-- **Naturality of the covariant defect at `τX` in the presented module.** For a lift `(t₀, t₁)`
of a map `X → X'` to the presentations, postcomposition with `D Tr(t)` on defects is cobase
change along `D Tr(t) : τX → τX'`. -/
theorem covariantDefectEquivExt1_homCokernelMap {X' : ModuleCat.{max u v w} A}
    (P' : FiniteProjectivePresentation X') {t₀ : P.P₀ →ₗ[A] P'.P₀} {t₁ : P.P₁ →ₗ[A] P'.P₁}
    (ht₁ : t₀ ∘ₗ P.p = P'.p ∘ₗ t₁)
    (y : covariantDefect R e.f.hom (MatlisDual R E (AuslanderReitenTranspose P.p))) :
    covariantDefectEquivExt1 R E P' e he
        (homCokernelMap R e.f.hom (MatlisDual.mapOp (AuslanderReitenTranspose.map t₀ t₁ ht₁)) y) =
      (covariantDefectEquivExt1 R E P e he y).pushout (matlisDualTransposeMap R E P P' ht₁) := by
  induction y using Submodule.Quotient.induction_on with
  | _ v =>
    rw [homCokernelMap_mk, covariantDefectEquivExt1_mk, covariantDefectEquivExt1_mk,
      Ext1.pushout_pushout]
    congr 1
    ext x
    refine (MatlisDual.equivLinearMap R E _).injective (LinearMap.ext fun y ↦ ?_)
    simp only [LinearMap.comp_apply, matlisDualTransposeHomEquiv_symm_apply, hom_comp,
      MatlisDual.mapOp_apply]
    exact (matlisDualTransposeMap_apply R E P P' ht₁ (v x) y).symm

end Projective

end Translate

end ModuleCat
