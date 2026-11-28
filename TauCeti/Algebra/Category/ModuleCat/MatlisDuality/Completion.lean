/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.Artinian
public import TauCeti.Algebra.Category.ModuleCat.Lcomp
public import TauCeti.CategoryTheory.ObjectProperty.Kernels
public import TauCeti.RingTheory.MatlisDuality.Completion.Basic
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Abelian.Subcategory
import TauCeti.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.CategoryTheory.ObjectProperty.Equivalence
import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.AdicCompletion.Small

/-!
# Categorical Matlis duality over the completion

Let `R` be a commutative Noetherian local ring with maximal ideal `𝔪`, residue field `κ`, and
`𝔪`-adic completion `R̂`, and let `ι : κ →ₗ[R] E` be an injective envelope of `κ`. Because `E` is
an injective `R`-module and (with its canonical `R̂`-action) also an injective `R̂`-module
(`TauCeti.IsInjectiveEnvelope.adicCompletion`), the Matlis dual functors

* `TauCeti.IsInjectiveEnvelope.matlisDualAdicCompletion : (ModuleCat R)ᵒᵖ ⥤ ModuleCat R̂`
  (`M ↦ Hom_R(M, E)`), and
* `TauCeti.IsInjectiveEnvelope.matlisDualOfAdicCompletion : (ModuleCat R̂)ᵒᵖ ⥤ ModuleCat R`
  (`N ↦ Hom_{R̂}(N, E)`)

are contravariant additive functors that turn every short exact sequence into a short exact
sequence (`TauCeti.IsInjectiveEnvelope.shortExact_map_matlisDualAdicCompletion` and
`TauCeti.IsInjectiveEnvelope.shortExact_map_matlisDualOfAdicCompletion`).

Restricting to Artinian `R`-modules and finitely generated `R̂`-modules yields the exact Matlis
anti-equivalence
`TauCeti.IsInjectiveEnvelope.adicCompletionMatlisDuality`
between `(CategoryTheory.isArtinianObject (C := ModuleCat R)).FullSubcategoryᵒᵖ` and
`FGModuleCat R̂`, together with short-exactness equivalences in both directions
(`TauCeti.IsInjectiveEnvelope.shortExact_map_adicCompletionMatlisDuality_functor_iff` and
`TauCeti.IsInjectiveEnvelope.shortExact_map_adicCompletionMatlisDuality_inverse_iff`).

## Main definitions

* `TauCeti.IsInjectiveEnvelope.matlisDualAdicCompletion`: the contravariant Matlis dual functor
  `Hom_R(-, E)` from `ModuleCat R` to `ModuleCat R̂`.
* `TauCeti.IsInjectiveEnvelope.matlisDualOfAdicCompletion`: the contravariant Matlis dual functor
  `Hom_{R̂}(-, E)` from `ModuleCat R̂` to `ModuleCat R`.
* `TauCeti.IsInjectiveEnvelope.adicCompletionMatlisDuality`: the contravariant equivalence
  between Artinian `R`-modules and finitely generated `R̂`-modules.

## Main results

* `TauCeti.IsInjectiveEnvelope.shortExact_map_matlisDualAdicCompletion` and
  `TauCeti.IsInjectiveEnvelope.shortExact_map_matlisDualOfAdicCompletion`: both Matlis dual
  functors reverse short exact sequences of modules.
* `TauCeti.IsInjectiveEnvelope.shortExact_map_adicCompletionMatlisDuality_functor`,
  `TauCeti.IsInjectiveEnvelope.shortExact_map_adicCompletionMatlisDuality_inverse`, and their
  `_iff` forms: the Matlis anti-equivalence reverses short exact sequences in both directions.

## References

* The Stacks Project, Remark 47.7.9, Tag 0EGL.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Theorem 3.2.13.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite TauCeti

namespace TauCeti.IsInjectiveEnvelope

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {E : Type v} [AddCommGroup E] [Module R E]
  {ι : ResidueField R →ₗ[R] E} (hι : IsInjectiveEnvelope ι)

include hι

section Functors

/-- The Matlis dual `Hom_R(M, E)` of a bundled `R`-module `M`, as a bundled `R̂`-module via the
canonical completion action on `E`. -/
def matlisDualAdicCompletionObj (M : ModuleCat.{w} R) :
    ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R) :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompObj R (_root_.AdicCompletion (maximalIdeal R) R) E M

/-- The underlying `R̂`-module of `matlisDualAdicCompletionObj hι M` is `M →ₗ[R] E`. -/
def matlisDualAdicCompletionObjEquiv (M : ModuleCat.{w} R) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    hι.matlisDualAdicCompletionObj M ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R] (M →ₗ[R] E) :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompObjEquiv R (_root_.AdicCompletion (maximalIdeal R) R) E M

/-- Precomposition along an `R`-linear morphism `M ⟶ M'` induces an `R̂`-linear morphism between
their Matlis duals. -/
def matlisDualAdicCompletionMap {M M' : ModuleCat.{w} R} (g : M ⟶ M') :
    hι.matlisDualAdicCompletionObj M' ⟶ hι.matlisDualAdicCompletionObj M :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompMap R (_root_.AdicCompletion (maximalIdeal R) R) E g

@[simp]
theorem matlisDualAdicCompletionObjEquiv_map_apply {M M' : ModuleCat.{w} R} (g : M ⟶ M')
    (φ : hι.matlisDualAdicCompletionObj M') (x : M) :
    hι.matlisDualAdicCompletionObjEquiv M (hι.matlisDualAdicCompletionMap g φ) x =
      hι.matlisDualAdicCompletionObjEquiv M' φ (g x) :=
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompObjEquiv_map_apply R (_root_.AdicCompletion (maximalIdeal R) R) E g φ x

/-- The contravariant Matlis dual functor `Hom_R(-, E)` from `ModuleCat R` to `ModuleCat R̂`. -/
def matlisDualAdicCompletion :
    (ModuleCat.{w} R)ᵒᵖ ⥤ ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R) :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompFunctor R (_root_.AdicCompletion (maximalIdeal R) R) E

@[simp]
theorem matlisDualAdicCompletion_obj (M : (ModuleCat.{w} R)ᵒᵖ) :
    hι.matlisDualAdicCompletion.obj M = hι.matlisDualAdicCompletionObj M.unop :=
  (rfl)

-- `eqToHom` is required in the statement because `matlisDualAdicCompletion` is not `@[expose]`.
@[simp]
theorem matlisDualAdicCompletion_map {M M' : (ModuleCat.{w} R)ᵒᵖ} (g : M ⟶ M') :
    hι.matlisDualAdicCompletion.map g =
      eqToHom (hι.matlisDualAdicCompletion_obj M) ≫
        hι.matlisDualAdicCompletionMap g.unop ≫
        eqToHom (hι.matlisDualAdicCompletion_obj M').symm :=
  (rfl)

theorem matlisDualAdicCompletionMap_add {M M' : ModuleCat.{w} R} (g h : M ⟶ M') :
    hι.matlisDualAdicCompletionMap (g + h) =
      hι.matlisDualAdicCompletionMap g + hι.matlisDualAdicCompletionMap h :=
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompMap_add R (_root_.AdicCompletion (maximalIdeal R) R) E g h

instance : (hι.matlisDualAdicCompletion :
    (ModuleCat.{w} R)ᵒᵖ ⥤ ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)).Additive
    where
  map_add := hι.matlisDualAdicCompletionMap_add _ _

/-- The Matlis dual `Hom_{R̂}(N, E)` of a bundled `R̂`-module `N`, as a bundled `R`-module. -/
def matlisDualOfAdicCompletionObj
    (N : ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R)) :
    ModuleCat.{max v w} R :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompObj (_root_.AdicCompletion (maximalIdeal R) R) R E N

/-- The underlying `R`-module of `matlisDualOfAdicCompletionObj hι N` is `N →ₗ[R̂] E`. -/
def matlisDualOfAdicCompletionObjEquiv
    (N : ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R)) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    hι.matlisDualOfAdicCompletionObj N ≃ₗ[R]
      (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompObjEquiv (_root_.AdicCompletion (maximalIdeal R) R) R E N

/-- Precomposition along an `R̂`-linear morphism `N ⟶ N'` induces an `R`-linear morphism between
their Matlis duals. -/
def matlisDualOfAdicCompletionMap
    {N N' : ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R)} (g : N ⟶ N') :
    hι.matlisDualOfAdicCompletionObj N' ⟶ hι.matlisDualOfAdicCompletionObj N :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompMap (_root_.AdicCompletion (maximalIdeal R) R) R E g

@[simp]
theorem matlisDualOfAdicCompletionObjEquiv_map_apply
    {N N' : ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R)} (g : N ⟶ N')
    (φ : hι.matlisDualOfAdicCompletionObj N') (x : N) :
    hι.matlisDualOfAdicCompletionObjEquiv N (hι.matlisDualOfAdicCompletionMap g φ) x =
      hι.matlisDualOfAdicCompletionObjEquiv N' φ (g x) :=
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompObjEquiv_map_apply (_root_.AdicCompletion (maximalIdeal R) R) R E g φ x

/-- The contravariant Matlis dual functor `Hom_{R̂}(-, E)` from `ModuleCat R̂` to `ModuleCat R`. -/
def matlisDualOfAdicCompletion :
    (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ ⥤ ModuleCat.{max v w} R :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompFunctor (_root_.AdicCompletion (maximalIdeal R) R) R E

@[simp]
theorem matlisDualOfAdicCompletion_obj
    (N : (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ) :
    hι.matlisDualOfAdicCompletion.obj N = hι.matlisDualOfAdicCompletionObj N.unop :=
  (rfl)

@[simp]
theorem matlisDualOfAdicCompletion_map
    {N N' : (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ} (g : N ⟶ N') :
    hι.matlisDualOfAdicCompletion.map g =
      eqToHom (hι.matlisDualOfAdicCompletion_obj N) ≫
        hι.matlisDualOfAdicCompletionMap g.unop ≫
        eqToHom (hι.matlisDualOfAdicCompletion_obj N').symm :=
  (rfl)

theorem matlisDualOfAdicCompletionMap_add
    {N N' : ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R)} (g h : N ⟶ N') :
    hι.matlisDualOfAdicCompletionMap (g + h) =
      hι.matlisDualOfAdicCompletionMap g + hι.matlisDualOfAdicCompletionMap h :=
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompMap_add (_root_.AdicCompletion (maximalIdeal R) R) R E g h

instance : (hι.matlisDualOfAdicCompletion :
    (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ ⥤ ModuleCat.{max v w} R).Additive
    where
  map_add := hι.matlisDualOfAdicCompletionMap_add _ _

section SmallFunctors

variable [Small.{v} R]

/-- **Exactness of `Hom_R(-, E)`**: applying `matlisDualAdicCompletion` reverses every short exact
sequence of `R`-modules into a short exact sequence of `R̂`-modules. -/
theorem shortExact_map_matlisDualAdicCompletion {S : ShortComplex (ModuleCat.{w} R)}
    (hS : S.ShortExact) : (S.op.map hι.matlisDualAdicCompletion).ShortExact := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hι.moduleInjective
  exact hS.op_map_of_lcomp hι.matlisDualAdicCompletion
    (fun M ↦ hι.matlisDualAdicCompletionObjEquiv M)
    (fun g φ x ↦ ModuleCat.lcompObjEquiv_map_apply R _ E g φ x)

/-- **Exactness of `Hom_{R̂}(-, E)`**: applying `matlisDualOfAdicCompletion` reverses every short
exact sequence of `R̂`-modules into a short exact sequence of `R`-modules. -/
theorem shortExact_map_matlisDualOfAdicCompletion
    {T : ShortComplex (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))}
    (hT : T.ShortExact) :
    (T.op.map hι.matlisDualOfAdicCompletion).ShortExact := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hι.adicCompletion.moduleInjective
  exact hT.op_map_of_lcomp hι.matlisDualOfAdicCompletion
    (fun N ↦ hι.matlisDualOfAdicCompletionObjEquiv N)
    (fun g φ x ↦ ModuleCat.lcompObjEquiv_map_apply _ R E g φ x)

end SmallFunctors

end Functors

section EvalIso

variable [Small.{v} R]

/-- General Matlis biduality for a bundled Artinian `R`-module `M`, as an isomorphism
`M ≅ Hom_{R̂}(Hom_R(M, E), E)`. -/
def evalIsoAdicCompletionOfIsArtinian (M : ModuleCat.{max v w} R) (hM : IsArtinian R M) :
    M ≅ hι.matlisDualOfAdicCompletionObj (hι.matlisDualAdicCompletionObj M) :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hM
  ModuleCat.lcompEvalIso R (_root_.AdicCompletion (maximalIdeal R) R) E M
    (hι.evalEquivAdicCompletionOfIsArtinian M)

@[simp]
theorem evalIsoAdicCompletionOfIsArtinian_hom_apply (M : ModuleCat.{max v w} R)
    (hM : IsArtinian R M) (m : M) (f : hι.matlisDualAdicCompletionObj M) :
    hι.matlisDualOfAdicCompletionObjEquiv _
        ((hι.evalIsoAdicCompletionOfIsArtinian M hM).hom m) f =
      hι.matlisDualAdicCompletionObjEquiv M f m :=
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hM
  ModuleCat.lcompEvalIso_hom_apply R (_root_.AdicCompletion (maximalIdeal R) R) E M
    (hι.evalEquivAdicCompletionOfIsArtinian M)
    (hι.evalEquivAdicCompletionOfIsArtinian_apply_apply M) m f

/-- General Matlis biduality for a bundled finitely generated `R̂`-module `N`, as an isomorphism
`N ≅ Hom_R(Hom_{R̂}(N, E), E)`. -/
def evalIsoOfFiniteAdicCompletion
    (N : ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R))
    (hN : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N) :
    N ≅ hι.matlisDualAdicCompletionObj (hι.matlisDualOfAdicCompletionObj N) :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hN
  ModuleCat.lcompEvalIso (_root_.AdicCompletion (maximalIdeal R) R) R E N
    (hι.evalEquivOfFiniteAdicCompletion N)

@[simp]
theorem evalIsoOfFiniteAdicCompletion_hom_apply
    (N : ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R))
    (hN : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N)
    (x : N) (f : hι.matlisDualOfAdicCompletionObj N) :
    hι.matlisDualAdicCompletionObjEquiv _ ((hι.evalIsoOfFiniteAdicCompletion N hN).hom x) f =
      hι.matlisDualOfAdicCompletionObjEquiv N f x :=
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hN
  ModuleCat.lcompEvalIso_hom_apply (_root_.AdicCompletion (maximalIdeal R) R) R E N
    (hι.evalEquivOfFiniteAdicCompletion N)
    (hι.evalEquivOfFiniteAdicCompletion_apply_apply N) x f

/-- `evalIsoAdicCompletionOfIsArtinian` is natural in `M`. -/
theorem evalIsoAdicCompletionOfIsArtinian_hom_naturality {M M' : ModuleCat.{max v w} R}
    (g : M ⟶ M') (hM : IsArtinian R M) (hM' : IsArtinian R M') :
    g ≫ (hι.evalIsoAdicCompletionOfIsArtinian M' hM').hom =
      (hι.evalIsoAdicCompletionOfIsArtinian M hM).hom ≫
        hι.matlisDualOfAdicCompletionMap (hι.matlisDualAdicCompletionMap g) :=
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hM
  have := hM'
  ModuleCat.lcompEvalIso_hom_naturality R (_root_.AdicCompletion (maximalIdeal R) R) E g
    (hι.evalEquivAdicCompletionOfIsArtinian M)
    (hι.evalEquivAdicCompletionOfIsArtinian_apply_apply M)
    (hι.evalEquivAdicCompletionOfIsArtinian M')
    (hι.evalEquivAdicCompletionOfIsArtinian_apply_apply M')

/-- `evalIsoOfFiniteAdicCompletion` is natural in `N`. -/
theorem evalIsoOfFiniteAdicCompletion_hom_naturality
    {N N' : ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)} (g : N ⟶ N')
    (hN : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N)
    (hN' : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N') :
    g ≫ (hι.evalIsoOfFiniteAdicCompletion N' hN').hom =
      (hι.evalIsoOfFiniteAdicCompletion N hN).hom ≫
        hι.matlisDualAdicCompletionMap (hι.matlisDualOfAdicCompletionMap g) :=
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hN
  have := hN'
  ModuleCat.lcompEvalIso_hom_naturality (_root_.AdicCompletion (maximalIdeal R) R) R E g
    (hι.evalEquivOfFiniteAdicCompletion N)
    (hι.evalEquivOfFiniteAdicCompletion_apply_apply N)
    (hι.evalEquivOfFiniteAdicCompletion N')
    (hι.evalEquivOfFiniteAdicCompletion_apply_apply N')

/-- Triangle identity: evaluation on `Hom_R(M, E)` is precomposition with the inverse of
evaluation on `M`. -/
theorem evalIsoOfFiniteAdicCompletion_matlisDualAdicCompletionObj_hom
    (M : ModuleCat.{max v w} R) (hM : IsArtinian R M)
    (hM' : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R)
      (hι.matlisDualAdicCompletionObj M)) :
    (hι.evalIsoOfFiniteAdicCompletion (hι.matlisDualAdicCompletionObj M) hM').hom =
      hι.matlisDualAdicCompletionMap (hι.evalIsoAdicCompletionOfIsArtinian M hM).inv :=
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hM
  have := hM'
  ModuleCat.lcompEvalIso_lcompObj_hom R (_root_.AdicCompletion (maximalIdeal R) R) E M
    (hι.evalEquivAdicCompletionOfIsArtinian M)
    (hι.evalEquivAdicCompletionOfIsArtinian_apply_apply M)
    (hι.evalEquivOfFiniteAdicCompletion (hι.matlisDualAdicCompletionObj M))
    (hι.evalEquivOfFiniteAdicCompletion_apply_apply (hι.matlisDualAdicCompletionObj M))

end EvalIso

section Equivalence

variable [Small.{v} R]

/-- **General Matlis duality over the completion**: `Hom_R(-, E)` and `Hom_{R̂}(-, E)` form a
contravariant equivalence between Artinian `R`-modules and finitely generated `R̂`-modules, whose
unit and counit are evaluation. -/
def adicCompletionMatlisDuality :
    (isArtinianObject (C := ModuleCat.{max v w} R)).FullSubcategoryᵒᵖ ≌
      FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R) :=
  ObjectProperty.antiEquivalence (isArtinianObject (C := ModuleCat.{max v w} R))
    (ModuleCat.isFG.{max v w} (_root_.AdicCompletion (maximalIdeal R) R))
    hι.matlisDualAdicCompletion hι.matlisDualOfAdicCompletion
    (fun M hM ↦ by
      let := AdicCompletion.torsionModule hι.mem_primaryComponent
      have : IsArtinian R M := (ModuleCat.isArtinianObject_iff _).mp hM
      have : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) :=
        hι.finite_adicCompletion_linearMap_of_isArtinian
      exact (ModuleCat.isFG_iff _).mpr
        (Module.Finite.equiv (hι.matlisDualAdicCompletionObjEquiv M).symm))
    (fun N hN ↦ by
      have : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N :=
        (ModuleCat.isFG_iff _).mp hN
      let := AdicCompletion.torsionModule hι.mem_primaryComponent
      have : IsArtinian R (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :=
        hι.isArtinian_adicCompletion_linearMap_of_finite N
      exact (ModuleCat.isArtinianObject_iff _).mpr
        (isArtinian_of_linearEquiv (hι.matlisDualOfAdicCompletionObjEquiv N).symm))
    (fun M hM ↦ hι.evalIsoAdicCompletionOfIsArtinian M ((ModuleCat.isArtinianObject_iff _).mp hM))
    (fun hX hX' g ↦ hι.evalIsoAdicCompletionOfIsArtinian_hom_naturality g
      ((ModuleCat.isArtinianObject_iff _).mp hX) ((ModuleCat.isArtinianObject_iff _).mp hX'))
    (fun N hN ↦ hι.evalIsoOfFiniteAdicCompletion N ((ModuleCat.isFG_iff _).mp hN))
    (fun hY hY' g ↦ hι.evalIsoOfFiniteAdicCompletion_hom_naturality g
      ((ModuleCat.isFG_iff _).mp hY) ((ModuleCat.isFG_iff _).mp hY'))
    (fun M hM ↦ by
      have : IsArtinian R M := (ModuleCat.isArtinianObject_iff _).mp hM
      let := AdicCompletion.torsionModule hι.mem_primaryComponent
      have : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) :=
        hι.finite_adicCompletion_linearMap_of_isArtinian
      have hM' : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R)
          (hι.matlisDualAdicCompletionObj M) :=
        Module.Finite.equiv (hι.matlisDualAdicCompletionObjEquiv M).symm
      exact hι.evalIsoOfFiniteAdicCompletion_matlisDualAdicCompletionObj_hom M
        ((ModuleCat.isArtinianObject_iff _).mp hM) hM')

@[simp]
theorem adicCompletionMatlisDuality_functor_obj_obj
    (M : (isArtinianObject (C := ModuleCat.{max v w} R)).FullSubcategoryᵒᵖ) :
    (hι.adicCompletionMatlisDuality.functor.obj M).obj =
      hι.matlisDualAdicCompletionObj M.unop.obj :=
  (rfl)

@[simp]
theorem adicCompletionMatlisDuality_functor_map_hom
    {M M' : (isArtinianObject (C := ModuleCat.{max v w} R)).FullSubcategoryᵒᵖ} (g : M ⟶ M') :
    (hι.adicCompletionMatlisDuality.functor.map g).hom =
      eqToHom (hι.adicCompletionMatlisDuality_functor_obj_obj M) ≫
        hι.matlisDualAdicCompletionMap g.unop.hom ≫
        eqToHom (hι.adicCompletionMatlisDuality_functor_obj_obj M').symm := by
  simp [adicCompletionMatlisDuality, ObjectProperty.antiEquivalence]

@[simp]
theorem adicCompletionMatlisDuality_inverse_obj_unop_obj
    (N : FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)) :
    (hι.adicCompletionMatlisDuality.inverse.obj N).unop.obj =
      hι.matlisDualOfAdicCompletionObj N.obj :=
  (rfl)

@[simp]
theorem adicCompletionMatlisDuality_inverse_map_unop_hom
    {N N' : FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)} (g : N ⟶ N') :
    (hι.adicCompletionMatlisDuality.inverse.map g).unop.hom =
      eqToHom (hι.adicCompletionMatlisDuality_inverse_obj_unop_obj N') ≫
        hι.matlisDualOfAdicCompletionMap g.hom ≫
        eqToHom (hι.adicCompletionMatlisDuality_inverse_obj_unop_obj N).symm := by
  simp [adicCompletionMatlisDuality, ObjectProperty.antiEquivalence]

/-- The inverse of the unit of `adicCompletionMatlisDuality` is evaluation
`M → Hom_{R̂}(Hom_R(M, E), E)`. -/
@[simp]
theorem adicCompletionMatlisDuality_unitIso_inv_app
    (M : (isArtinianObject (C := ModuleCat.{max v w} R)).FullSubcategoryᵒᵖ) :
    (hι.adicCompletionMatlisDuality.unitIso.inv.app M).unop.hom =
      (hι.evalIsoAdicCompletionOfIsArtinian M.unop.obj
        ((ModuleCat.isArtinianObject_iff _).mp M.unop.property)).hom ≫
        eqToHom ((congrArg hι.matlisDualOfAdicCompletionObj
          (hι.adicCompletionMatlisDuality_functor_obj_obj M)).symm.trans
          (hι.adicCompletionMatlisDuality_inverse_obj_unop_obj _).symm) :=
  (rfl)

/-- The inverse of the counit of `adicCompletionMatlisDuality` is evaluation
`N → Hom_R(Hom_{R̂}(N, E), E)`. -/
@[simp]
theorem adicCompletionMatlisDuality_counitIso_inv_app
    (N : FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)) :
    (hι.adicCompletionMatlisDuality.counitIso.inv.app N).hom =
      (hι.evalIsoOfFiniteAdicCompletion N.obj ((ModuleCat.isFG_iff _).mp N.property)).hom ≫
        eqToHom ((congrArg hι.matlisDualAdicCompletionObj
          (hι.adicCompletionMatlisDuality_inverse_obj_unop_obj N)).symm.trans
          (hι.adicCompletionMatlisDuality_functor_obj_obj _).symm) :=
  (rfl)

/-- Applying `adicCompletionMatlisDuality.functor` reverses a short exact sequence of Artinian
`R`-modules into a short exact sequence of finitely generated `R̂`-modules. -/
theorem shortExact_map_adicCompletionMatlisDuality_functor
    {S : ShortComplex (isArtinianObject (C := ModuleCat.{max v w} R)).FullSubcategory}
    (hS : S.ShortExact) :
    (S.op.map hι.adicCompletionMatlisDuality.functor).ShortExact :=
  hS.op.map_of_exact hι.adicCompletionMatlisDuality.functor

/-- A short complex of Artinian `R`-modules is short exact iff its image under
`adicCompletionMatlisDuality.functor` is short exact. -/
theorem shortExact_map_adicCompletionMatlisDuality_functor_iff
    {S : ShortComplex (isArtinianObject (C := ModuleCat.{max v w} R)).FullSubcategory} :
    (S.op.map hι.adicCompletionMatlisDuality.functor).ShortExact ↔ S.ShortExact :=
  (CategoryTheory.ShortExact.shortExact_map_iff hι.adicCompletionMatlisDuality.functor).trans
    S.shortExact_iff_op.symm

/-- Applying `adicCompletionMatlisDuality.inverse` reverses a short exact sequence of finitely
generated `R̂`-modules into a short exact sequence of Artinian `R`-modules. -/
theorem shortExact_map_adicCompletionMatlisDuality_inverse
    {T : ShortComplex (FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R))}
    (hT : T.ShortExact) :
    (T.map hι.adicCompletionMatlisDuality.inverse).unop.ShortExact :=
  (hT.map_of_exact hι.adicCompletionMatlisDuality.inverse).unop

/-- A short complex of finitely generated `R̂`-modules is short exact iff its dual under
`adicCompletionMatlisDuality.inverse` is short exact. -/
theorem shortExact_map_adicCompletionMatlisDuality_inverse_iff
    {T : ShortComplex (FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R))} :
    (T.map hι.adicCompletionMatlisDuality.inverse).unop.ShortExact ↔ T.ShortExact :=
  (ShortComplex.shortExact_iff_unop _).symm.trans
    (CategoryTheory.ShortExact.shortExact_map_iff hι.adicCompletionMatlisDuality.inverse)

end Equivalence

end TauCeti.IsInjectiveEnvelope
