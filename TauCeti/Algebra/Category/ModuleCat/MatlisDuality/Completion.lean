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
import TauCeti.CategoryTheory.ObjectProperty.Equivalence
import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.AdicCompletion.Small

/-!
# Categorical Matlis duality over the completion

Let `R` be a commutative Noetherian local ring with maximal ideal `𝔪`, residue field `κ`, and
`𝔪`-adic completion `R̂`, and let `ι : κ →ₗ[R] E` be an injective envelope of `κ` with
`E : Type v`. Without any universe-smallness hypothesis on `R`, the canonical `R̂`-module
structure on `E` gives contravariant additive functors that preserve finite limits:

* `TauCeti.IsInjectiveEnvelope.matlisDualAdicCompletion : (ModuleCat R)ᵒᵖ ⥤ ModuleCat R̂`
  (`M ↦ Hom_R(M, E)`), and
* `TauCeti.IsInjectiveEnvelope.matlisDualOfAdicCompletion : (ModuleCat R̂)ᵒᵖ ⥤ ModuleCat R`
  (`N ↦ Hom_{R̂}(N, E)`).

When `[Small.{v} R]` holds, `E` is an injective `R`-module and (with its canonical `R̂`-action)
also an injective `R̂`-module (`TauCeti.IsInjectiveEnvelope.adicCompletion`), so both Matlis dual
functors also preserve finite colimits and homology (`CategoryTheory.Functor.PreservesHomology`),
turning every short exact sequence into a short exact sequence
(`TauCeti.IsInjectiveEnvelope.shortExact_map_matlisDualAdicCompletion` and
`TauCeti.IsInjectiveEnvelope.shortExact_map_matlisDualOfAdicCompletion`).

Under `[Small.{v} R]`, restricting to Artinian `R`-modules and finitely generated `R̂`-modules
yields the exact Matlis anti-equivalence `TauCeti.IsInjectiveEnvelope.adicCompletionMatlisDuality`
between `(CategoryTheory.isArtinianObject (C := ModuleCat R)).FullSubcategoryᵒᵖ` and
`FGModuleCat R̂`, whose inverse unit (unopped) and inverse counit components are evaluation, with
transport-free linear identifications `adicCompletionMatlisDualityFunctorObjEquiv` and
`adicCompletionMatlisDualityInverseObjEquiv` on the functor objects. By Mathlib's generic
exact-equivalence transport (`CategoryTheory.ShortExact.map_of_exact`,
`CategoryTheory.ShortExact.shortExact_map_iff`), both functors of the equivalence preserve and
reflect short exact sequences.

## Main definitions

* `TauCeti.IsInjectiveEnvelope.matlisDualAdicCompletion`: the contravariant Matlis dual functor
  `Hom_R(-, E)` from `ModuleCat R` to `ModuleCat R̂` (does not require `[Small.{v} R]`).
* `TauCeti.IsInjectiveEnvelope.matlisDualOfAdicCompletion`: the contravariant Matlis dual functor
  `Hom_{R̂}(-, E)` from `ModuleCat R̂` to `ModuleCat R` (does not require `[Small.{v} R]`).
* `TauCeti.IsInjectiveEnvelope.adicCompletionMatlisDuality`: assuming `[Small.{v} R]`, the
  contravariant equivalence between Artinian `R`-modules and finitely generated `R̂`-modules.

## Main results

Assuming `[Small.{v} R]` for `E : Type v`:

* `PreservesFiniteColimits` and `CategoryTheory.Functor.PreservesHomology` instances for both
  `matlisDualAdicCompletion` and `matlisDualOfAdicCompletion`.
* `TauCeti.IsInjectiveEnvelope.shortExact_map_matlisDualAdicCompletion` and
  `TauCeti.IsInjectiveEnvelope.shortExact_map_matlisDualOfAdicCompletion`: both Matlis dual
  functors reverse short exact sequences of modules.

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

/-- The contravariant Matlis dual functor `Hom_R(-, E)` from `ModuleCat R` to `ModuleCat R̂`. -/
def matlisDualAdicCompletion :
    (ModuleCat.{w} R)ᵒᵖ ⥤ ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R) :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompFunctor R (_root_.AdicCompletion (maximalIdeal R) R) E

/-- The Matlis dual `Hom_R(M, E)` of a bundled `R`-module `M`, as a bundled `R̂`-module via the
canonical completion action on `E`, realized as `hι.matlisDualAdicCompletion.obj (op M)`. -/
abbrev matlisDualAdicCompletionObj (M : ModuleCat.{w} R) :
    ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R) :=
  hι.matlisDualAdicCompletion.obj (op M)

/-- Precomposition along an `R`-linear morphism `M ⟶ M'` induces an `R̂`-linear morphism between
their Matlis duals. -/
abbrev matlisDualAdicCompletionMap {M M' : ModuleCat.{w} R} (g : M ⟶ M') :
    hι.matlisDualAdicCompletionObj M' ⟶ hι.matlisDualAdicCompletionObj M :=
  hι.matlisDualAdicCompletion.map g.op

/-- The underlying `R̂`-module of `hι.matlisDualAdicCompletion.obj (op M)` is `M →ₗ[R] E`. -/
def matlisDualAdicCompletionObjEquiv (M : ModuleCat.{w} R) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    hι.matlisDualAdicCompletion.obj (op M) ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      (M →ₗ[R] E) :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompObjEquiv R (_root_.AdicCompletion (maximalIdeal R) R) E M

@[simp]
theorem matlisDualAdicCompletionObjEquiv_map_apply {M M' : ModuleCat.{w} R} (g : M ⟶ M')
    (φ : hι.matlisDualAdicCompletionObj M') (x : M) :
    hι.matlisDualAdicCompletionObjEquiv M (hι.matlisDualAdicCompletionMap g φ) x =
      hι.matlisDualAdicCompletionObjEquiv M' φ (g x) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact ModuleCat.lcompObjEquiv_map_apply R (_root_.AdicCompletion (maximalIdeal R) R) E g φ x

@[simp]
theorem matlisDualAdicCompletionObjEquiv_functor_map_apply {M M' : (ModuleCat.{w} R)ᵒᵖ}
    (g : M ⟶ M') (φ : hι.matlisDualAdicCompletion.obj M) (x : M'.unop) :
    hι.matlisDualAdicCompletionObjEquiv M'.unop (hι.matlisDualAdicCompletion.map g φ) x =
      hι.matlisDualAdicCompletionObjEquiv M.unop φ (g.unop x) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact ModuleCat.lcompObjEquiv_functor_map_apply R (_root_.AdicCompletion (maximalIdeal R) R) E
    g φ x

theorem matlisDualAdicCompletion_obj (M : (ModuleCat.{w} R)ᵒᵖ) :
    hι.matlisDualAdicCompletion.obj M = hι.matlisDualAdicCompletionObj M.unop :=
  rfl

theorem matlisDualAdicCompletion_map {M M' : (ModuleCat.{w} R)ᵒᵖ} (g : M ⟶ M') :
    hι.matlisDualAdicCompletion.map g = hι.matlisDualAdicCompletionMap g.unop :=
  rfl

theorem matlisDualAdicCompletionMap_add {M M' : ModuleCat.{w} R} (g h : M ⟶ M') :
    hι.matlisDualAdicCompletionMap (g + h) =
      hι.matlisDualAdicCompletionMap g + hι.matlisDualAdicCompletionMap h := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact (ModuleCat.lcompFunctor R (_root_.AdicCompletion (maximalIdeal R) R) E).map_add

instance :
    (hι.matlisDualAdicCompletion :
      (ModuleCat.{w} R)ᵒᵖ ⥤
        ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)).Additive := by
  dsimp only [matlisDualAdicCompletion]
  infer_instance

instance :
    PreservesFiniteLimits (hι.matlisDualAdicCompletion :
      (ModuleCat.{w} R)ᵒᵖ ⥤
        ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)) := by
  dsimp only [matlisDualAdicCompletion]
  infer_instance

/-- The contravariant Matlis dual functor `Hom_{R̂}(-, E)` from `ModuleCat R̂` to
`ModuleCat R`. -/
def matlisDualOfAdicCompletion :
    (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ ⥤ ModuleCat.{max v w} R :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompFunctor (_root_.AdicCompletion (maximalIdeal R) R) R E

/-- The Matlis dual `Hom_{R̂}(N, E)` of a bundled `R̂`-module `N`, as a bundled `R`-module,
realized as `hι.matlisDualOfAdicCompletion.obj (op N)`. -/
abbrev matlisDualOfAdicCompletionObj
    (N : ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R)) :
    ModuleCat.{max v w} R :=
  hι.matlisDualOfAdicCompletion.obj (op N)

/-- Precomposition along an `R̂`-linear morphism `N ⟶ N'` induces an `R`-linear morphism between
their Matlis duals. -/
abbrev matlisDualOfAdicCompletionMap
    {N N' : ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R)} (g : N ⟶ N') :
    hι.matlisDualOfAdicCompletionObj N' ⟶ hι.matlisDualOfAdicCompletionObj N :=
  hι.matlisDualOfAdicCompletion.map g.op

/-- The underlying `R`-module of `hι.matlisDualOfAdicCompletion.obj (op N)` is
`N →ₗ[R̂] E`. -/
def matlisDualOfAdicCompletionObjEquiv
    (N : ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R)) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    hι.matlisDualOfAdicCompletion.obj (op N) ≃ₗ[R]
      (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.lcompObjEquiv (_root_.AdicCompletion (maximalIdeal R) R) R E N

@[simp]
theorem matlisDualOfAdicCompletionObjEquiv_map_apply
    {N N' : ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R)} (g : N ⟶ N')
    (φ : hι.matlisDualOfAdicCompletionObj N') (x : N) :
    hι.matlisDualOfAdicCompletionObjEquiv N (hι.matlisDualOfAdicCompletionMap g φ) x =
      hι.matlisDualOfAdicCompletionObjEquiv N' φ (g x) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact ModuleCat.lcompObjEquiv_map_apply (_root_.AdicCompletion (maximalIdeal R) R) R E g φ x

@[simp]
theorem matlisDualOfAdicCompletionObjEquiv_functor_map_apply
    {N N' : (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ} (g : N ⟶ N')
    (φ : hι.matlisDualOfAdicCompletion.obj N) (x : N'.unop) :
    hι.matlisDualOfAdicCompletionObjEquiv N'.unop (hι.matlisDualOfAdicCompletion.map g φ) x =
      hι.matlisDualOfAdicCompletionObjEquiv N.unop φ (g.unop x) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact ModuleCat.lcompObjEquiv_functor_map_apply (_root_.AdicCompletion (maximalIdeal R) R) R E
    g φ x

theorem matlisDualOfAdicCompletion_obj
    (N : (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ) :
    hι.matlisDualOfAdicCompletion.obj N = hι.matlisDualOfAdicCompletionObj N.unop :=
  rfl

theorem matlisDualOfAdicCompletion_map
    {N N' : (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ} (g : N ⟶ N') :
    hι.matlisDualOfAdicCompletion.map g = hι.matlisDualOfAdicCompletionMap g.unop :=
  rfl

theorem matlisDualOfAdicCompletionMap_add
    {N N' : ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R)} (g h : N ⟶ N') :
    hι.matlisDualOfAdicCompletionMap (g + h) =
      hι.matlisDualOfAdicCompletionMap g + hι.matlisDualOfAdicCompletionMap h := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact (ModuleCat.lcompFunctor (_root_.AdicCompletion (maximalIdeal R) R) R E).map_add

instance :
    (hι.matlisDualOfAdicCompletion :
      (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ ⥤
        ModuleCat.{max v w} R).Additive := by
  dsimp only [matlisDualOfAdicCompletion]
  infer_instance

instance :
    PreservesFiniteLimits (hι.matlisDualOfAdicCompletion :
      (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ ⥤
        ModuleCat.{max v w} R) := by
  dsimp only [matlisDualOfAdicCompletion]
  infer_instance

section SmallFunctors

variable [Small.{v} R]

instance :
    PreservesFiniteColimits (hι.matlisDualAdicCompletion :
      (ModuleCat.{w} R)ᵒᵖ ⥤
        ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hι.moduleInjective
  dsimp only [matlisDualAdicCompletion]
  infer_instance

instance :
    (hι.matlisDualAdicCompletion :
      (ModuleCat.{w} R)ᵒᵖ ⥤
        ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)).PreservesHomology :=
  inferInstance

instance :
    PreservesFiniteColimits (hι.matlisDualOfAdicCompletion :
      (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ ⥤
        ModuleCat.{max v w} R) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hι.adicCompletion.moduleInjective
  dsimp only [matlisDualOfAdicCompletion]
  infer_instance

instance :
    (hι.matlisDualOfAdicCompletion :
      (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ ⥤
        ModuleCat.{max v w} R).PreservesHomology :=
  inferInstance

/-- **Exactness of `Hom_R(-, E)`**: assuming `[Small.{v} R]` for `E : Type v`, applying
`matlisDualAdicCompletion` reverses every short exact sequence of `R`-modules into a short exact
sequence of `R̂`-modules. -/
theorem shortExact_map_matlisDualAdicCompletion {S : ShortComplex (ModuleCat.{w} R)}
    (hS : S.ShortExact) : (S.op.map hι.matlisDualAdicCompletion).ShortExact :=
  hS.op.map_of_exact hι.matlisDualAdicCompletion

/-- **Exactness of `Hom_{R̂}(-, E)`**: assuming `[Small.{v} R]` for `E : Type v`, applying
`matlisDualOfAdicCompletion` reverses every short exact sequence of `R̂`-modules into a short exact
sequence of `R`-modules. -/
theorem shortExact_map_matlisDualOfAdicCompletion
    {T : ShortComplex (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))}
    (hT : T.ShortExact) :
    (T.op.map hι.matlisDualOfAdicCompletion).ShortExact :=
  hT.op.map_of_exact hι.matlisDualOfAdicCompletion

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
  ModuleCat.lcompBidualIsoOfLinearEquiv R (_root_.AdicCompletion (maximalIdeal R) R) E M
    (hι.evalEquivAdicCompletionOfIsArtinian M)

@[simp]
theorem evalIsoAdicCompletionOfIsArtinian_hom_apply (M : ModuleCat.{max v w} R)
    (hM : IsArtinian R M) (m : M) (f : hι.matlisDualAdicCompletionObj M) :
    hι.matlisDualOfAdicCompletionObjEquiv _
        ((hι.evalIsoAdicCompletionOfIsArtinian M hM).hom m) f =
      hι.matlisDualAdicCompletionObjEquiv M f m :=
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hM
  ModuleCat.lcompBidualIsoOfLinearEquiv_hom_apply R (_root_.AdicCompletion (maximalIdeal R) R) E M
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
  ModuleCat.lcompBidualIsoOfLinearEquiv (_root_.AdicCompletion (maximalIdeal R) R) R E N
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
  ModuleCat.lcompBidualIsoOfLinearEquiv_hom_apply (_root_.AdicCompletion (maximalIdeal R) R) R E N
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
  ModuleCat.lcompBidualIsoOfLinearEquiv_hom_naturality
    R (_root_.AdicCompletion (maximalIdeal R) R) E g
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
  ModuleCat.lcompBidualIsoOfLinearEquiv_hom_naturality
    (_root_.AdicCompletion (maximalIdeal R) R) R E g
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
  ModuleCat.lcompBidualIsoOfLinearEquiv_lcompObj_hom
    R (_root_.AdicCompletion (maximalIdeal R) R) E M
    (hι.evalEquivAdicCompletionOfIsArtinian M)
    (hι.evalEquivAdicCompletionOfIsArtinian_apply_apply M)
    (hι.evalEquivOfFiniteAdicCompletion (hι.matlisDualAdicCompletionObj M))
    (hι.evalEquivOfFiniteAdicCompletion_apply_apply (hι.matlisDualAdicCompletionObj M))

end EvalIso

section Equivalence

variable [Small.{v} R]

private theorem evalIsoAdicCompletionOfIsArtinian_fullSubcategory_naturality
    {X X' : ModuleCat.{max v w} R} (hX : isArtinianObject X) (hX' : isArtinianObject X')
    (g : X ⟶ X') :
    g ≫ (hι.evalIsoAdicCompletionOfIsArtinian X'
        ((ModuleCat.isArtinianObject_iff _).mp hX')).hom =
      (hι.evalIsoAdicCompletionOfIsArtinian X ((ModuleCat.isArtinianObject_iff _).mp hX)).hom ≫
        hι.matlisDualOfAdicCompletion.map (hι.matlisDualAdicCompletion.map g.op).op :=
  hι.evalIsoAdicCompletionOfIsArtinian_hom_naturality g
    ((ModuleCat.isArtinianObject_iff _).mp hX) ((ModuleCat.isArtinianObject_iff _).mp hX')

private theorem evalIsoOfFiniteAdicCompletion_fullSubcategory_naturality
    {Y Y' : ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)}
    (hY : ModuleCat.isFG (_root_.AdicCompletion (maximalIdeal R) R) Y)
    (hY' : ModuleCat.isFG (_root_.AdicCompletion (maximalIdeal R) R) Y')
    (g : Y ⟶ Y') :
    g ≫ (hι.evalIsoOfFiniteAdicCompletion Y' ((ModuleCat.isFG_iff _).mp hY')).hom =
      (hι.evalIsoOfFiniteAdicCompletion Y ((ModuleCat.isFG_iff _).mp hY)).hom ≫
        hι.matlisDualAdicCompletion.map (hι.matlisDualOfAdicCompletion.map g.op).op :=
  hι.evalIsoOfFiniteAdicCompletion_hom_naturality g
    ((ModuleCat.isFG_iff _).mp hY) ((ModuleCat.isFG_iff _).mp hY')

/-- **General Matlis duality over the completion**: assuming `[Small.{v} R]` for `E : Type v`,
`Hom_R(-, E)` and `Hom_{R̂}(-, E)` form a contravariant equivalence between Artinian `R`-modules
and finitely generated `R̂`-modules, whose inverse unit component on the Artinian side (unopped,
`(hι.adicCompletionMatlisDuality.unitIso.inv.app M).unop`) and inverse counit component on the
finite side (`hι.adicCompletionMatlisDuality.counitIso.inv.app N`) are evaluation. -/
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
    (fun M hM ↦
      hι.evalIsoAdicCompletionOfIsArtinian M ((ModuleCat.isArtinianObject_iff _).mp hM))
    (hι.evalIsoAdicCompletionOfIsArtinian_fullSubcategory_naturality)
    (fun N hN ↦ hι.evalIsoOfFiniteAdicCompletion N ((ModuleCat.isFG_iff _).mp hN))
    (hι.evalIsoOfFiniteAdicCompletion_fullSubcategory_naturality)
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

/-- The underlying `R̂`-module of `hι.adicCompletionMatlisDuality.functor.obj M` is
`M.unop.obj →ₗ[R] E`. -/
def adicCompletionMatlisDualityFunctorObjEquiv
    (M : (isArtinianObject (C := ModuleCat.{max v w} R)).FullSubcategoryᵒᵖ) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    hι.adicCompletionMatlisDuality.functor.obj M ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      (M.unop.obj →ₗ[R] E) :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  hι.matlisDualAdicCompletionObjEquiv M.unop.obj

/-- The underlying `R`-module of `(hι.adicCompletionMatlisDuality.inverse.obj N).unop.obj` is
`N →ₗ[R̂] E`. -/
def adicCompletionMatlisDualityInverseObjEquiv
    (N : FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    (hι.adicCompletionMatlisDuality.inverse.obj N).unop.obj ≃ₗ[R]
      (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  hι.matlisDualOfAdicCompletionObjEquiv N.obj

theorem adicCompletionMatlisDuality_functor_obj_obj
    (M : (isArtinianObject (C := ModuleCat.{max v w} R)).FullSubcategoryᵒᵖ) :
    (hι.adicCompletionMatlisDuality.functor.obj M).obj =
      hι.matlisDualAdicCompletionObj M.unop.obj := by
  dsimp only [adicCompletionMatlisDuality]
  exact ObjectProperty.antiEquivalence_functor_obj_obj M

theorem adicCompletionMatlisDuality_inverse_obj_unop_obj
    (N : FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)) :
    (hι.adicCompletionMatlisDuality.inverse.obj N).unop.obj =
      hι.matlisDualOfAdicCompletionObj N.obj := by
  dsimp only [adicCompletionMatlisDuality]
  exact ObjectProperty.antiEquivalence_inverse_obj_unop_obj N

/-- Applying `adicCompletionMatlisDuality.functor` to a morphism acts as precomposition. -/
@[simp]
theorem adicCompletionMatlisDualityFunctorObjEquiv_map_apply
    {M M' : (isArtinianObject (C := ModuleCat.{max v w} R)).FullSubcategoryᵒᵖ} (g : M ⟶ M')
    (φ : hι.adicCompletionMatlisDuality.functor.obj M) (x : M'.unop.obj) :
    hι.adicCompletionMatlisDualityFunctorObjEquiv M'
        ((hι.adicCompletionMatlisDuality.functor.map g).hom φ) x =
      hι.adicCompletionMatlisDualityFunctorObjEquiv M φ (g.unop.hom x) := by
  dsimp only [adicCompletionMatlisDuality, adicCompletionMatlisDualityFunctorObjEquiv]
  rw [ObjectProperty.antiEquivalence_functor_map_hom]
  exact hι.matlisDualAdicCompletionObjEquiv_map_apply g.unop.hom φ x

/-- Applying `adicCompletionMatlisDuality.inverse` to a morphism acts as precomposition. -/
@[simp]
theorem adicCompletionMatlisDualityInverseObjEquiv_map_apply
    {N N' : FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)} (g : N ⟶ N')
    (φ : (hι.adicCompletionMatlisDuality.inverse.obj N').unop.obj) (x : N) :
    hι.adicCompletionMatlisDualityInverseObjEquiv N
        ((hι.adicCompletionMatlisDuality.inverse.map g).unop.hom φ) x =
      hι.adicCompletionMatlisDualityInverseObjEquiv N' φ (g.hom x) := by
  dsimp only [adicCompletionMatlisDuality, adicCompletionMatlisDualityInverseObjEquiv]
  rw [ObjectProperty.antiEquivalence_inverse_map_unop_hom]
  exact hι.matlisDualOfAdicCompletionObjEquiv_map_apply g.hom φ x

/-- The unop of the inverse of the unit of `adicCompletionMatlisDuality` is evaluation
`M → Hom_{R̂}(Hom_R(M, E), E)`. -/
@[simp]
theorem adicCompletionMatlisDuality_unitIso_inv_app_apply
    (M : (isArtinianObject (C := ModuleCat.{max v w} R)).FullSubcategoryᵒᵖ) (m : M.unop.obj)
    (f : hι.adicCompletionMatlisDuality.functor.obj M) :
    hι.adicCompletionMatlisDualityInverseObjEquiv _
        ((ConcreteCategory.hom
          (X := M.unop.obj)
          (Y := (hι.adicCompletionMatlisDuality.inverse.obj
            (hι.adicCompletionMatlisDuality.functor.obj M)).unop.obj)
          (hι.adicCompletionMatlisDuality.unitIso.inv.app M).unop.hom) m) f =
      hι.adicCompletionMatlisDualityFunctorObjEquiv M f m := by
  dsimp only [adicCompletionMatlisDuality, adicCompletionMatlisDualityInverseObjEquiv,
    adicCompletionMatlisDualityFunctorObjEquiv]
  rw [ObjectProperty.antiEquivalence_unitIso_inv_app_unop_hom]
  exact hι.evalIsoAdicCompletionOfIsArtinian_hom_apply M.unop.obj
    ((ModuleCat.isArtinianObject_iff _).mp M.unop.property) m f

/-- The unop of the forward unit of `adicCompletionMatlisDuality` is the inverse of evaluation. -/
@[simp]
theorem adicCompletionMatlisDuality_unitIso_hom_app_apply
    (M : (isArtinianObject (C := ModuleCat.{max v w} R)).FullSubcategoryᵒᵖ)
    (φ : (hι.adicCompletionMatlisDuality.inverse.obj
      (hι.adicCompletionMatlisDuality.functor.obj M)).unop.obj)
    (f : hι.adicCompletionMatlisDuality.functor.obj M) :
    hι.adicCompletionMatlisDualityFunctorObjEquiv M f
        ((ConcreteCategory.hom
          (X := (hι.adicCompletionMatlisDuality.inverse.obj
            (hι.adicCompletionMatlisDuality.functor.obj M)).unop.obj)
          (Y := M.unop.obj)
          (hι.adicCompletionMatlisDuality.unitIso.hom.app M).unop.hom) φ) =
      hι.adicCompletionMatlisDualityInverseObjEquiv _ φ f := by
  rw [← hι.adicCompletionMatlisDuality_unitIso_inv_app_apply M]
  have hcomp : (hι.adicCompletionMatlisDuality.unitIso.inv.app M).unop.hom
      ((hι.adicCompletionMatlisDuality.unitIso.hom.app M).unop.hom φ) = φ := by
    change ((hι.adicCompletionMatlisDuality.unitIso.hom.app M).unop ≫
      (hι.adicCompletionMatlisDuality.unitIso.inv.app M).unop).hom φ = φ
    rw [← CategoryTheory.unop_comp, Iso.inv_hom_id_app]
    rfl
  rw [hcomp]

/-- The inverse of the counit of `adicCompletionMatlisDuality` is evaluation
`N → Hom_R(Hom_{R̂}(N, E), E)`. -/
@[simp]
theorem adicCompletionMatlisDuality_counitIso_inv_app_apply
    (N : FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)) (x : N)
    (f : (hι.adicCompletionMatlisDuality.inverse.obj N).unop.obj) :
    hι.adicCompletionMatlisDualityFunctorObjEquiv _
        ((ConcreteCategory.hom
          (X := N.obj)
          (Y := (hι.adicCompletionMatlisDuality.functor.obj
            (hι.adicCompletionMatlisDuality.inverse.obj N)).obj)
          (hι.adicCompletionMatlisDuality.counitIso.inv.app N).hom) x) f =
      hι.adicCompletionMatlisDualityInverseObjEquiv N f x := by
  dsimp only [adicCompletionMatlisDuality, adicCompletionMatlisDualityFunctorObjEquiv,
    adicCompletionMatlisDualityInverseObjEquiv]
  rw [ObjectProperty.antiEquivalence_counitIso_inv_app_hom]
  exact hι.evalIsoOfFiniteAdicCompletion_hom_apply N.obj ((ModuleCat.isFG_iff _).mp N.property) x f

/-- The forward counit of `adicCompletionMatlisDuality` is the inverse of evaluation. -/
@[simp]
theorem adicCompletionMatlisDuality_counitIso_hom_app_apply
    (N : FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R))
    (φ : hι.adicCompletionMatlisDuality.functor.obj
      (hι.adicCompletionMatlisDuality.inverse.obj N))
    (f : (hι.adicCompletionMatlisDuality.inverse.obj N).unop.obj) :
    hι.adicCompletionMatlisDualityInverseObjEquiv N f
        ((ConcreteCategory.hom
          (X := (hι.adicCompletionMatlisDuality.functor.obj
            (hι.adicCompletionMatlisDuality.inverse.obj N)).obj)
          (Y := N.obj)
          (hι.adicCompletionMatlisDuality.counitIso.hom.app N).hom) φ) =
      hι.adicCompletionMatlisDualityFunctorObjEquiv _ φ f := by
  rw [← hι.adicCompletionMatlisDuality_counitIso_inv_app_apply N]
  have hcomp : (hι.adicCompletionMatlisDuality.counitIso.inv.app N).hom
      ((hι.adicCompletionMatlisDuality.counitIso.hom.app N).hom φ) = φ := by
    change ((hι.adicCompletionMatlisDuality.counitIso.hom.app N) ≫
      (hι.adicCompletionMatlisDuality.counitIso.inv.app N)).hom φ = φ
    rw [Iso.hom_inv_id_app]
    rfl
  rw [hcomp]

end Equivalence

end TauCeti.IsInjectiveEnvelope
