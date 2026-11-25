/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Category.ModuleCat.Algebra
public import TauCeti.Algebra.Module.AuslanderReiten.Defect.Basic
public import TauCeti.Algebra.Module.AuslanderReiten.TensorCokernel
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.YonedaExt.Injective
public import TauCeti.CategoryTheory.Exact.YonedaExt.Projective

/-!
# The defects of a short exact sequence of modules

Let `R` be a commutative ring and `A` an `R`-algebra. The defects of a map of `A`-modules
(`TauCeti/Algebra/Module/AuslanderReiten/Defect/Basic.lean`) are cokernels of `R`-linear maps
between `Hom` spaces of `ModuleCat A`. For a short exact sequence whose middle term is injective or
projective they are identified with `Ext¹` and with stable `Hom` spaces:

* for `N ⟶ I ⟶ N'` with `I` injective, the contravariant defect at `Y` is `Ext¹(Y, N)` and the
  covariant defect at `W` is `Hom(N, W)` modulo the injectively trivial maps;
* for `K ⟶ P ⟶ M` with `P` projective, the contravariant defect at `Y` is `Hom(Y, M)` modulo the
  maps through projectives and the covariant defect at `W` is `Ext¹(M, W)`.

These are the categorical sides of Auslander's defect formula, used for the two
Auslander–Reiten formulas, with `W` the translate `D Tr X`.

## Implementation notes

The covariant defect at an `A`-module `W` uses its native `R`-action. The `Hom` spaces of
`ModuleCat A` carry the `R`-action of its `R`-linear structure, and on `N ⟶ ModuleCat.of A W` the
two agree only propositionally. The covariant comparisons therefore take a bundled module `B`
with an `A`-linear equivalence `W ≃ₗ[A] B`, compared on morphisms by
`ModuleCat.homLinearEquivOfLinearEquiv`; for `D Tr X` this is `ModuleCat.matlisDualTransposeEquiv`.

## Main definitions

* `ModuleCat.contravariantDefectEquivHomQuotient` and `ModuleCat.covariantDefectEquivHomQuotient`:
  the defects as cokernels of `R`-linear maps between `Hom` spaces of `ModuleCat A`, through
  `ModuleCat.homLinearEquiv_comp_rightComp` and
  `ModuleCat.homLinearEquivOfLinearEquiv_symm_comp_lcomp`.
* `ModuleCat.contravariantDefectEquivExt1` and `ModuleCat.covariantDefectEquivCostableHom`: the
  defects of a short exact sequence with injective middle term.
* `ModuleCat.contravariantDefectEquivStableHom` and `ModuleCat.covariantDefectEquivExt1`: the
  defects of a short exact sequence with projective middle term.

## Main results

* `ModuleCat.contravariantDefectEquivStableHom_map` and
  `ModuleCat.contravariantDefectEquivStableHom_comap`: naturality of the contravariant
  identification in the sequence and in the test module.
* `ModuleCat.covariantDefectEquivExt1_map` and `ModuleCat.covariantDefectEquivExt1_homCokernelMap`:
  naturality of the covariant identification in the sequence and in the test module.

## References

* H. Krause, *A short proof for Auslander's defect formula*, Linear Algebra Appl. **365** (2003),
  267–270.
-/

public section

namespace ModuleCat

open CategoryTheory TauCeti TauCeti.ExactStructure LinearMap
open scoped ModuleCat.Algebra

universe u v t

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- The underlying linear maps of a short exact sequence of `A`-modules form an exact sequence. -/
theorem _root_.TauCeti.ExactStructure.Extension.function_exact {M K : ModuleCat.{t} A}
    (e : (ExactStructure.abelian (ModuleCat.{t} A)).Extension M K) :
    Function.Exact e.f.hom e.g.hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp e.shortExact.exact

/-! ### Defects as cokernels of `Hom` maps -/

/-- The contravariant defect of a map `g : M ⟶ N` of `A`-modules at `Y`, as the cokernel of the
`R`-linear map `Hom(Y, M) → Hom(Y, N)` between `Hom` spaces of `ModuleCat A`. -/
noncomputable def contravariantDefectEquivHomQuotient {M N : ModuleCat.{t} A} (g : M ⟶ N)
    (Y : ModuleCat.{t} A) :
    contravariantDefect R g.hom Y ≃ₗ[R] ((Y ⟶ N) ⧸ LinearMap.range (Linear.rightComp R Y g)) :=
  (Submodule.Quotient.equiv _ _ (homLinearEquiv (S := R)) (by
    rw [← LinearMap.range_comp, homLinearEquiv_comp_rightComp,
      LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)])).symm

/-- The class of `g' : Y → N` in the contravariant defect is the class of the morphism `g'`. -/
@[simp]
theorem contravariantDefectEquivHomQuotient_mk {M N : ModuleCat.{t} A} (g : M ⟶ N)
    {Y : ModuleCat.{t} A} (g' : Y →ₗ[A] N) :
    contravariantDefectEquivHomQuotient R g Y (Submodule.Quotient.mk g') =
      Submodule.Quotient.mk (ofHom g') := by
  simp only [contravariantDefectEquivHomQuotient, Submodule.Quotient.equiv_symm,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  -- `homLinearEquiv.symm g'` is `ofHom g'` by definition.
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
  -- `ofHom` of a composite of linear maps is the composite of morphisms, by definition.
  rfl

/-- **Naturality of the contravariant defect as stable `Hom` in the test module.** Precomposition
with `s : Y ⟶ Y'` on defects is precomposition with the stable class of `s`. -/
theorem contravariantDefectEquivStableHom_comap {Y Y' : ModuleCat.{t} A} (s : Y ⟶ Y')
    (x : contravariantDefect R e.g.hom Y') :
    contravariantDefectEquivStableHom R e he Y (contravariantDefectComap R e.g.hom s.hom x) =
      (ExactStructure.abelian _).projectiveStableFunctor.map s ≫
        contravariantDefectEquivStableHom R e he Y' x := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [contravariantDefectComap_mk, contravariantDefectEquivStableHom_mk,
    contravariantDefectEquivStableHom_mk, ← Functor.map_comp]
  -- `ofHom` of a composite of linear maps is the composite of morphisms, by definition.
  rfl

end Projective

/-! ### Covariant defects

The covariant defect at a module `W` uses the native `R`-action of `W`, while `Hom` spaces of
`ModuleCat A` carry the `R`-action of its `R`-linear structure. For a bundled module `B` with an
`A`-linear equivalence `W ≃ B`, `ModuleCat.homLinearEquivOfLinearEquiv` compares the two, and the
covariant defect at `W` is described through morphisms into `B`. For `τX = D Tr X` this is the
identity on carriers (`ModuleCat.matlisDualTransposeEquiv`). -/

section Covariant

variable {W : Type t} [AddCommGroup W] [Module A W] [Module R W] [IsScalarTower R A W]
  {B : ModuleCat.{t} A} (eW : W ≃ₗ[A] B)

/-- The covariant defect of a map `f : N ⟶ N'` of `A`-modules at `W`, as the cokernel of the
`R`-linear map `Hom(N', B) → Hom(N, B)` between `Hom` spaces of `ModuleCat A`. -/
noncomputable def covariantDefectEquivHomQuotient {N N' : ModuleCat.{t} A} (f : N ⟶ N') :
    covariantDefect R f.hom W ≃ₗ[R] ((N ⟶ B) ⧸ LinearMap.range (Linear.leftComp R B f)) :=
  Submodule.Quotient.equiv _ _ (homLinearEquivOfLinearEquiv R eW N).symm (by
    rw [← LinearMap.range_comp, homLinearEquivOfLinearEquiv_symm_comp_lcomp,
      LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)])

/-- The class of `u : N → W` in the covariant defect is the class of the morphism `eW ∘ u`. -/
@[simp]
theorem covariantDefectEquivHomQuotient_mk {N N' : ModuleCat.{t} A} (f : N ⟶ N')
    (u : N →ₗ[A] W) :
    covariantDefectEquivHomQuotient R eW f (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (ofHom (eW.toLinearMap ∘ₗ u)) := by
  simp [covariantDefectEquivHomQuotient]

section Injective

variable {N N' : ModuleCat.{t} A} (e : (ExactStructure.abelian _).Extension N' N)
  (he : (ExactStructure.abelian _).isInjective e.obj)

/-- **The covariant defect is costable `Hom`.** For a short exact sequence `N ⟶ I ⟶ N'` with `I`
injective, the cokernel of `Hom_A(I, W) → Hom_A(N, W)` is `(A/ℐ)(N, B)`. -/
noncomputable def covariantDefectEquivCostableHom :
    covariantDefect R e.f.hom W ≃ₗ[R]
      ((ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj N ⟶
        (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.obj B) :=
  covariantDefectEquivHomQuotient R eW e.f ≪≫ₗ e.homQuotientEquivCostableHom he R _

/-- The class of `u : N → W` in the covariant defect is the class of `eW ∘ u` modulo `ℐ`. -/
@[simp]
theorem covariantDefectEquivCostableHom_mk (u : N →ₗ[A] W) :
    covariantDefectEquivCostableHom R eW e he (Submodule.Quotient.mk u) =
      (ExactStructure.abelian _).injectivelyTrivialIdeal.quotientFunctor.map
        (ofHom (eW.toLinearMap ∘ₗ u)) := by
  simp [covariantDefectEquivCostableHom]

end Injective

section Projective

variable {M K : ModuleCat.{t} A} (e : (ExactStructure.abelian _).Extension M K)
  (he : (ExactStructure.abelian _).isProjective e.obj)

/-- **The covariant defect is `Ext¹`.** For a short exact sequence `K ⟶ P ⟶ M` with `P` projective,
the cokernel of `Hom_A(P, W) → Hom_A(K, W)` is `Ext¹(M, B)`, through `v ↦ v_* [K ⟶ P ⟶ M]`. -/
noncomputable def covariantDefectEquivExt1 :
    covariantDefect R e.f.hom W ≃ₗ[R] (ExactStructure.abelian _).Ext1 M B :=
  covariantDefectEquivHomQuotient R eW e.f ≪≫ₗ e.homQuotientEquivExt1OfIsProjective he R _

/-- The class of `v : K → W` in the covariant defect is the cobase change of `[K ⟶ P ⟶ M]` along
`eW ∘ v`. -/
@[simp]
theorem covariantDefectEquivExt1_mk (v : K →ₗ[A] W) :
    covariantDefectEquivExt1 R eW e he (Submodule.Quotient.mk v) =
      (Ext1.mk e).pushout (ofHom (eW.toLinearMap ∘ₗ v)) := by
  simp [covariantDefectEquivExt1]

/-- **Naturality of the covariant defect as `Ext¹` in the sequence.** For a morphism `(a₁, a₂, f)`
from `K ⟶ P ⟶ M` to `K' ⟶ P' ⟶ M'`, precomposition with `a₁` on defects is base change along
`f`. -/
theorem covariantDefectEquivExt1_map {M' K' : ModuleCat.{t} A}
    (e' : (ExactStructure.abelian _).Extension M' K')
    (he' : (ExactStructure.abelian _).isProjective e'.obj) {a₁ : K ⟶ K'} {a₂ : e.obj ⟶ e'.obj}
    {f : M ⟶ M'} (h₁ : e.f ≫ a₂ = a₁ ≫ e'.f) (h₂ : e.g ≫ f = a₂ ≫ e'.g)
    (y : covariantDefect R e'.f.hom W) :
    covariantDefectEquivExt1 R eW e he
        (covariantDefectMap R (φ := e.f.hom) (φ' := e'.f.hom) (a₁ := a₁.hom) (a₂ := a₂.hom)
          (congrArg Hom.hom h₁) W y) =
      (covariantDefectEquivExt1 R eW e' he' y).pullback f := by
  induction y using Submodule.Quotient.induction_on with
  | _ v =>
    rw [covariantDefectMap_mk, covariantDefectEquivExt1_mk, covariantDefectEquivExt1_mk,
      Ext1.pushout_pullback, ← Ext1.pushout_mk_eq_pullback_mk a₂ h₁ h₂.symm, Ext1.pushout_pushout]
    congr 1

/-- **Naturality of the covariant defect as `Ext¹` in the test module.** For `g : W → W'` and
`W' ≃ B'`, postcomposition with `g` on defects is cobase change along the induced `B ⟶ B'`. -/
theorem covariantDefectEquivExt1_homCokernelMap {W' : Type t} [AddCommGroup W'] [Module A W']
    [Module R W'] [IsScalarTower R A W'] {B' : ModuleCat.{t} A} (eW' : W' ≃ₗ[A] B')
    (g : W →ₗ[A] W') (y : covariantDefect R e.f.hom W) :
    covariantDefectEquivExt1 R eW' e he (homCokernelMap R e.f.hom g y) =
      (covariantDefectEquivExt1 R eW e he y).pushout
        (ofHom (eW'.toLinearMap ∘ₗ g ∘ₗ eW.symm.toLinearMap)) := by
  induction y using Submodule.Quotient.induction_on with
  | _ v =>
    rw [homCokernelMap_mk, covariantDefectEquivExt1_mk, covariantDefectEquivExt1_mk,
      Ext1.pushout_pushout]
    congr 1
    ext
    simp

end Projective

end Covariant

end ModuleCat
