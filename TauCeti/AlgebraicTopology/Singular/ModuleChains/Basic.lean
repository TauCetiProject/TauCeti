/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic
public import TauCeti.AlgebraicTopology.TopologicalSimplex
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Singular chains with coefficients in a ring, on elements

For a ring `k`, the simplicial singular chain complex with coefficients in `k` is the complex of
`k`-modules whose `n`-chains are the formal `k`-combinations of singular `n`-simplices.  This file
gives the element-level interface to it: the chain `simplexChain σ a` of a simplex with a
coefficient, the extensionality of linear maps out of the chains (and, for integer coefficients,
of additive maps), the linear map with prescribed values on simplices, the push-forward and the
boundary of a simplex, the chains of points and paths (`TauCeti.pointChain`,
`TauCeti.pathChain`), and the augmentation, the sum of the coefficients of a `0`-chain, natural
and vanishing on boundaries.

## Main definitions

* `TauCeti.singularChains k`: the simplicial singular chain complex functor with coefficients in
  the ring `k`.
* `TauCeti.simplexChain σ a`: the chain of a singular simplex `σ` with coefficient `a`.
* `TauCeti.chainsDesc f`: the linear map out of the singular `n`-chains with the given values on
  singular simplices.
* `TauCeti.singularAugment k X`: the augmentation of the simplicial singular chains.
* `ContinuousMap.firstHomologyMap`: the induced linear map on first integral singular homology.

## Main results

* `TauCeti.singularChains_linearMap_ext`, `TauCeti.singularChains_addMonoidHom_ext`: linear maps,
  and additive maps out of the chains with integer coefficients, are determined on simplices.
* `TauCeti.singularChains_d_simplexChain`: the boundary of a simplex.
* `TauCeti.singularAugment_map`, `TauCeti.singularAugment_d`: the augmentation is natural and
  vanishes on boundaries.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial

universe u

namespace TauCeti

variable (k : Type u) [Ring k]

/-- The **simplicial singular chain complex** functor with coefficients in the ring `k`. -/
abbrev singularChains : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} k) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{u} k)).obj (ModuleCat.of k k)

section Singular

variable {k}

/-- The chain of a singular simplex, with coefficient `a`. -/
abbrev simplexChain {X : TopCat.{u}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) (a : k) :
    ((singularChains k).obj X).X n :=
  (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of k k) σ a

/-- Linear maps out of simplicial singular chains agree when they agree on simplices. -/
theorem singularChains_linearMap_ext {X : TopCat.{u}} {n : ℕ} {V : Type u} [AddCommGroup V]
    [Module k V] {L L' : ((singularChains k).obj X).X n →ₗ[k] V}
    (h : ∀ σ, L (simplexChain σ 1) = L' (simplexChain σ 1)) : L = L' := by
  have : ModuleCat.ofHom L = ModuleCat.ofHom L' := by
    refine SSet.chainComplex_hom_ext fun σ ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    exact h σ
  exact congrArg ModuleCat.Hom.hom this

/-- The chain of a simplex with coefficient `a` is `a` times the chain of the simplex. -/
theorem simplexChain_eq_smul {X : TopCat.{u}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) (a : k) :
    simplexChain σ a = a • simplexChain σ 1 := by
  calc simplexChain σ a = simplexChain σ (a • (1 : k)) := by rw [smul_eq_mul, mul_one]
    _ = a • simplexChain σ 1 := map_smul _ a 1

/-- Pushing the chain of a simplex forward along a continuous map gives the chain of the
pushed-forward simplex, with the same coefficient. -/
-- Not a simp lemma: `TauCeti.singularChainComplexFunctor_obj_map` rewrites the chain map inside
-- the left-hand side first, so the `simpNF` linter rejects it.
theorem singularChains_map_f_simplexChain {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (a : k) :
    ((singularChains k).map f).f n (simplexChain σ a) =
      simplexChain ((TopCat.toSSet.map f).app _ σ) a := by
  -- `singularChains k` is defined through `TopCat.toSSet`; its map on chains is, by definition,
  -- the simplicial chain map of `TopCat.toSSet.map f`, on which `ι_chainComplexMap_f` applies.
  change (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of k k)).f n
    ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of k k) σ a) =
      (TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of k k) _ a
  rw [← ModuleCat.comp_apply, SSet.ι_chainComplexMap_f]

/-- The linear map out of the singular `n`-chains with the given values on singular simplices. -/
def chainsDesc {X : TopCat.{u}} {n : ℕ} {V : Type u} [AddCommGroup V] [Module k V]
    (f : (TopCat.toSSet.obj X) _⦋n⦌ → V) : ((singularChains k).obj X).X n →ₗ[k] V :=
  (Cofan.IsColimit.desc ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of k k) n)
    (fun s ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton k V (f s)))).hom

/-- The linear map with given values on simplices takes the chain of a simplex with coefficient
`a` to `a` times the value on the simplex. -/
@[simp]
theorem chainsDesc_simplexChain {X : TopCat.{u}} {n : ℕ} {V : Type u} [AddCommGroup V]
    [Module k V] (f : (TopCat.toSSet.obj X) _⦋n⦌ → V) (s : (TopCat.toSSet.obj X) _⦋n⦌) (a : k) :
    chainsDesc f (simplexChain s a) = a • f s := by
  have h := Cofan.IsColimit.fac
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of k k) n)
    (fun s ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton k V (f s))) s
  simp only [SSet.chainComplexXCofan, Cofan.inj, Cofan.mk_ι_app] at h
  exact congrArg (fun g ↦ g.hom a) h

/-- The linear map with given values on simplices takes the chain of a simplex to the value on
the simplex. -/
theorem chainsDesc_simplexChain_one {X : TopCat.{u}} {n : ℕ} {V : Type u} [AddCommGroup V]
    [Module k V] (f : (TopCat.toSSet.obj X) _⦋n⦌ → V) (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    chainsDesc f (simplexChain s (1 : k)) = f s := by
  rw [chainsDesc_simplexChain, one_smul]

end Singular

/-- Additive maps out of the singular chains with integer coefficients agree when they agree on
simplices. -/
theorem singularChains_addMonoidHom_ext {X : TopCat.{0}} {n : ℕ} {V : Type} [AddCommGroup V]
    {f g : ((singularChains ℤ).obj X).X n →+ V}
    (h : ∀ s, f (simplexChain s 1) = g (simplexChain s 1)) : f = g :=
  -- An additive map is linear for the module structure of the chains, which is only
  -- propositionally equal to `AddCommGroup.toIntModule` (so `AddMonoidHom.toIntLinearMap` does
  -- not apply).
  let lin (φ : ((singularChains ℤ).obj X).X n →+ V) : ((singularChains ℤ).obj X).X n →ₗ[ℤ] V :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' a c := (congrArg φ (int_smul_eq_zsmul _ a c)).trans (map_zsmul φ a c) }
  AddMonoidHom.ext fun c ↦ LinearMap.congr_fun
    (singularChains_linearMap_ext (L := lin f) (L' := lin g) h) c

/-- The augmentation of the simplicial singular chains: the sum of the coefficients. -/
def singularAugment (X : TopCat.{u}) : ((singularChains k).obj X).X 0 →ₗ[k] k :=
  chainsDesc fun _ ↦ (1 : k)

variable {k} in
/-- The augmentation of the chain of a `0`-simplex with coefficient `a` is `a`. -/
@[simp]
theorem singularAugment_simplexChain (X : TopCat.{u}) (σ : (TopCat.toSSet.obj X) _⦋0⦌)
    (a : k) : singularAugment k X (simplexChain σ a) = a := by
  rw [singularAugment, chainsDesc_simplexChain, smul_eq_mul, mul_one]

variable {k}

/-- The augmentation of the simplicial singular chains is natural. -/
-- Not a simp lemma: `TauCeti.singularChainComplexFunctor_obj_map` rewrites the chain map inside
-- the left-hand side first, so the `simpNF` linter rejects it.
theorem singularAugment_map {X Y : TopCat.{u}} (f : X ⟶ Y) (x : ((singularChains k).obj X).X 0) :
    singularAugment k Y (((singularChains k).map f).f 0 x) = singularAugment k X x := by
  have := singularChains_linearMap_ext
    (L := singularAugment k Y ∘ₗ (((singularChains k).map f).f 0).hom)
    (L' := singularAugment k X) fun σ ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, singularChains_map_f_simplexChain,
        singularAugment_simplexChain]
  exact LinearMap.congr_fun this x

/-- The boundary of a singular simplex is the alternating sum of its faces. -/
@[simp]
theorem singularChains_d_simplexChain {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌) (a : k) :
    ((singularChains k).obj X).d (n + 1) n (simplexChain σ a) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • simplexChain ((TopCat.toSSet.obj X).δ i σ) a := by
  have h := congrArg (fun g ↦ g.hom a)
    (SSet.ιChainComplex_d (R := ModuleCat.of k k) (TopCat.toSSet.obj X) (n := n) σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply] at h
  exact h

/-- The augmentation of the simplicial singular chains vanishes on boundaries. -/
@[simp]
theorem singularAugment_d (X : TopCat.{u}) (x : ((singularChains k).obj X).X 1) :
    singularAugment k X (((singularChains k).obj X).d 1 0 x) = 0 := by
  have := singularChains_linearMap_ext
    (L := singularAugment k X ∘ₗ (((singularChains k).obj X).d 1 0).hom) (L' := 0) fun σ ↦ by
      rw [LinearMap.comp_apply, singularChains_d_simplexChain, map_sum]
      simp [Fin.sum_univ_succ, singularAugment_simplexChain]
  exact LinearMap.congr_fun this x

section Paths

open unitInterval

variable (k)

/-- The chain of the singular `0`-simplex at a point. -/
abbrev pointChain {X : TopCat.{u}} (p : X) : ((singularChains k).obj X).X 0 :=
  simplexChain (TopCat.toSSetObj₀Equiv.symm p) 1

/-- The chain of the singular `1`-simplex of a map from the unit interval
(`TauCeti.TopCat.simplex₁`). -/
abbrev pathChain {X : TopCat.{u}} (g : C(I, X)) : ((singularChains k).obj X).X 1 :=
  simplexChain (TopCat.simplex₁ g) 1

variable {k}

/-- The boundary of the chain of a path is the difference of the chains of its endpoints. -/
theorem singularChains_d_pathChain {X : TopCat.{u}} (g : C(I, X)) :
    ((singularChains k).obj X).d 1 0 (pathChain k g) =
      pointChain k (g 1) - pointChain k (g 0) := by
  rw [singularChains_d_simplexChain (n := 0), Fin.sum_univ_two, TopCat.δ_zero_simplex₁,
    TopCat.δ_one_simplex₁]
  simp [sub_eq_add_neg]

/-- Pushing the chain of a path forward along a continuous map gives the chain of the composite. -/
-- Not a simp lemma: `TauCeti.singularChainComplexFunctor_obj_map` rewrites the chain map inside
-- the left-hand side first, so the `simpNF` linter rejects it.
theorem singularChains_map_f_pathChain {X Y : TopCat.{u}} (f : X ⟶ Y) (g : C(I, X)) :
    ((singularChains k).map f).f 1 (pathChain k g) =
      pathChain k ((ConcreteCategory.hom f).comp g) := by
  rw [singularChains_map_f_simplexChain, TopCat.toSSet_map_app_simplex₁]

end Paths

end TauCeti

namespace ContinuousMap

open TauCeti

/-- The map induced on first integral singular homology by a continuous map. -/
abbrev firstHomologyMap {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] (g : C(Y, Z)) :
    ((singularChains ℤ).obj (TopCat.of Y)).homology 1 →ₗ[ℤ]
      ((singularChains ℤ).obj (TopCat.of Z)).homology 1 :=
  (HomologicalComplex.homologyMap ((singularChains ℤ).map (TopCat.ofHom g)) 1).hom

/-- First integral singular homology respects composition of continuous maps. -/
theorem firstHomologyMap_comp {Y Z W : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    [TopologicalSpace W] (g : C(Z, W)) (g' : C(Y, Z)) (x) :
    firstHomologyMap (g.comp g') x = firstHomologyMap g (firstHomologyMap g' x) := by
  rw [firstHomologyMap, TopCat.ofHom_comp, Functor.map_comp, HomologicalComplex.homologyMap_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply]

end ContinuousMap
