/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Module.Projective
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Simplicial chains with varying coefficients

This file records how the coproduct inclusion associated to a simplex behaves under the
simplicial operators and under a morphism of coefficient objects, and how the degreewise
components of the chain maps induced by maps of simplicial sets compose with each other and with
changes of coefficients.  It also records that
simplicial chain modules with semisimple coefficients are semisimple, and those with projective
coefficients are projective, both as modules and, for coefficients in any preadditive category
with coproducts, as objects of that category.

For a module `V` over a ring `k`, the simplicial `n`-chains
`(X.chainComplex (ModuleCat.of k V)).X n` are the finitely supported functions from the
`n`-simplices of `X` to `V` (`SSet.chainsLinearEquivFinsupp`): a chain is a finite sum
`∑ vᵢ σᵢ` of simplices `σᵢ` with coefficients `vᵢ ∈ V`. Under this identification, the chain
maps induced by maps of simplicial sets push coefficient functions forward along the map on
simplices (`SSet.chainsLinearEquivFinsupp_chainComplexMap_f`), and changing the coefficients
along a linear map applies it to the coefficient functions
(`SSet.chainsLinearEquivFinsupp_chainComplexFunctor_map`).

## Implementation notes

The equivalence `SSet.chainsLinearEquivFinsupp` generalizes, to any simplicial set and any module
of coefficients, the Tau Ceti equivalence `TauCeti.singularChainsLinearEquivFinsupp` between
singular chains with coefficients in a ring and finitely supported functions, which it replaces.
Like it, it is built from the description of the chains as a coproduct,
`SSet.isColimitChainComplexXCofan`, in Mathlib's
`Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic` (Joël Riou and Andrew Yang).
-/

public section

noncomputable section

open CategoryTheory Limits

open scoped Simplicial

universe w v u

namespace TauCeti.SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  {X : _root_.SSet.{w}} {R R' : C}

/-- Mapping the coefficient object of simplicial chains applies the coefficient morphism before
the coproduct inclusion associated to each simplex. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_chainComplexFunctor_map_app_f (f : R ⟶ R') {n : ℕ} (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ (((_root_.SSet.chainComplexFunctor C).map f).app X).f n =
      f ≫ X.ιChainComplex x := by
  dsimp [_root_.SSet.chainComplexFunctor, _root_.SSet.ιChainComplex,
    _root_.SSet.chainComplex]
  simp

/-- The degreewise components of the chain maps induced by maps of simplicial sets compose like
the maps themselves. -/
@[reassoc]
lemma chainComplexMap_f_comp {X Y Z : _root_.SSet.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (R : C) (n : ℕ) :
    (_root_.SSet.chainComplexMap f R).f n ≫ (_root_.SSet.chainComplexMap g R).f n =
      (_root_.SSet.chainComplexMap (f ≫ g) R).f n := by
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp]

/-- The chain maps induced by maps of simplicial sets commute, degreewise, with changes of
coefficients. -/
@[reassoc]
lemma chainComplexMap_f_chainComplexFunctor_map_app_f {X Y : _root_.SSet.{w}} (f : X ⟶ Y)
    (u : R ⟶ R') (n : ℕ) :
    (_root_.SSet.chainComplexMap f R).f n ≫
        (((_root_.SSet.chainComplexFunctor C).map u).app Y).f n =
      (((_root_.SSet.chainComplexFunctor C).map u).app X).f n ≫
        (_root_.SSet.chainComplexMap f R').f n := by
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, NatTrans.naturality]

end TauCeti.SSet

namespace SSet

/-- The summand inclusion of a simplex `x`, followed by a simplicial operator of the simplicial
object `[n] ↦ ∐_{X _⦋n⦌} R` whose chain complex is `X.chainComplex R`, is the summand inclusion of
the image of `x`. -/
@[reassoc]
lemma ιChainComplex_map {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
    {X : SSet.{w}} {R : C} {m n : ℕ} (x : X _⦋n⦌) (f : ⦋m⦌ ⟶ ⦋n⦌) :
    X.ιChainComplex (R := R) x ≫
        (((SimplicialObject.whiskering _ _).obj (sigmaConst.obj R)).obj X).map f.op =
      X.ιChainComplex (X.map f.op x) := by
  simp [ιChainComplex]

/-- The simplicial chain modules `Cₙ(X; M) = ⨁ M` with semisimple coefficients `M` are
semisimple. -/
instance isSemisimpleModule_chainComplex_X {k : Type w} [Ring k] (X : SSet.{w})
    (M : ModuleCat.{w} k) [IsSemisimpleModule k M] (n : ℕ) :
    IsSemisimpleModule k ((X.chainComplex M).X n) := by
  classical
  -- `Cₙ(X; M)` is by definition the coproduct of copies of `M` indexed by the `n`-simplices.
  exact .congr ((ModuleCat.coprodIsoDirectSum fun _ : X _⦋n⦌ ↦ M).toLinearEquiv.trans
    (finsuppLequivDFinsupp k).symm)

/-- The simplicial chain modules `Cₙ(X; M) = ⨁ M` with projective coefficients `M` are
projective. -/
instance projective_chainComplex_X {k : Type*} [Ring k] (X : SSet.{w})
    (M : ModuleCat.{w} k) [Module.Projective k M] (n : ℕ) :
    Module.Projective k ((X.chainComplex M).X n) := by
  classical
  -- `Cₙ(X; M)` is by definition the coproduct of copies of `M` indexed by the `n`-simplices.
  exact .of_equiv' (ModuleCat.coprodIsoDirectSum fun _ : X _⦋n⦌ ↦ M).toLinearEquiv.symm

/-- The simplicial chains `Cₙ(X; R) = ∐ R` with coefficients in a projective object `R` of a
preadditive category with coproducts are projective. -/
instance projective_chainComplex_X_of_projective {C : Type u} [Category.{v} C]
    [HasCoproducts.{w} C] [Preadditive C] (X : SSet.{w}) (R : C) [Projective R] (n : ℕ) :
    Projective ((X.chainComplex R).X n) where
  factors {E _} f e _ := by
    let g : (X.chainComplex R).X n ⟶ E := Cofan.IsColimit.desc (X.isColimitChainComplexXCofan R n)
      fun x ↦ Projective.factorThru (X.ιChainComplex x ≫ f) e
    refine ⟨g, X.chainComplex_hom_ext fun x ↦ ?_⟩
    -- The cofan defining the chains has the summand inclusions `X.ιChainComplex x` as its
    -- injections, so `Cofan.IsColimit.fac` computes `g` on each summand.
    have hg : X.ιChainComplex x ≫ g = Projective.factorThru (X.ιChainComplex x ≫ f) e :=
      Cofan.IsColimit.fac _ _ x
    rw [reassoc_of% hg, Projective.factorThru_comp]

/-! ### Simplicial chains as finitely supported functions -/

section Chains

variable (X : SSet.{w}) {k : Type*} [Ring k]

variable {V W : Type w} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] {n : ℕ}

/-- Linear maps out of the simplicial `n`-chains agree when they agree on every simplex with
every coefficient. -/
theorem chainComplex_linearMap_ext {U : Type w} [AddCommGroup U] [Module k U]
    {L L' : (X.chainComplex (ModuleCat.of k V)).X n →ₗ[k] U}
    (h : ∀ σ v, L (X.ιChainComplex (R := ModuleCat.of k V) σ v) =
      L' (X.ιChainComplex (R := ModuleCat.of k V) σ v)) : L = L' := by
  have : ModuleCat.ofHom L = ModuleCat.ofHom L' :=
    chainComplex_hom_ext fun σ ↦ ModuleCat.hom_ext (LinearMap.ext (h σ))
  exact congrArg ModuleCat.Hom.hom this

variable (V n) in
/-- The coefficient function of a simplicial chain, as a linear map. -/
private def chainsToFinsupp : (X.chainComplex (ModuleCat.of k V)).X n →ₗ[k] (X _⦋n⦌ →₀ V) :=
  (Cofan.IsColimit.desc (X.isColimitChainComplexXCofan (ModuleCat.of k V) n)
    fun σ ↦ ModuleCat.ofHom (Finsupp.lsingle σ)).hom

private theorem chainsToFinsupp_ιChainComplex (σ : X _⦋n⦌) (v : V) :
    X.chainsToFinsupp V n (X.ιChainComplex (R := ModuleCat.of k V) σ v) = Finsupp.single σ v := by
  have h := Cofan.IsColimit.fac (X.isColimitChainComplexXCofan (ModuleCat.of k V) n)
    (fun σ ↦ ModuleCat.ofHom (Finsupp.lsingle σ)) σ
  simp only [chainComplexXCofan, Cofan.inj, Cofan.mk_ι_app] at h
  exact congrArg (fun g ↦ g.hom v) h

variable (V n) in
/-- The simplicial chain with a given coefficient function, as a linear map. -/
private def finsuppToChains : (X _⦋n⦌ →₀ V) →ₗ[k] (X.chainComplex (ModuleCat.of k V)).X n :=
  Finsupp.lsum ℕ fun σ ↦ (X.ιChainComplex (R := ModuleCat.of k V) σ).hom

private theorem finsuppToChains_single (σ : X _⦋n⦌) (v : V) :
    X.finsuppToChains V n (Finsupp.single σ v) = X.ιChainComplex (R := ModuleCat.of k V) σ v :=
  Finsupp.sum_single_index (map_zero _)

variable (V n) in
/-- **The simplicial `n`-chains are the finitely supported functions on `n`-simplices**: the linear
equivalence sending the chain of a simplex `σ` with coefficient `v` to the function supported at
`σ` with value `v`. -/
def chainsLinearEquivFinsupp :
    (X.chainComplex (ModuleCat.of k V)).X n ≃ₗ[k] (X _⦋n⦌ →₀ V) :=
  LinearEquiv.ofLinearMap (X.chainsToFinsupp V n) (X.finsuppToChains V n)
    (Finsupp.lhom_ext' fun σ ↦ LinearMap.ext fun v ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
        finsuppToChains_single, chainsToFinsupp_ιChainComplex]
      simp)
    (X.chainComplex_linearMap_ext fun σ v ↦ by
      rw [LinearMap.comp_apply, chainsToFinsupp_ιChainComplex, finsuppToChains_single,
        LinearMap.id_apply])

/-- The chain of a simplex `σ` with coefficient `v` is the function supported at `σ` with value
`v`. -/
@[simp]
theorem chainsLinearEquivFinsupp_ιChainComplex (σ : X _⦋n⦌) (v : V) :
    X.chainsLinearEquivFinsupp V n (X.ιChainComplex (R := ModuleCat.of k V) σ v) =
      Finsupp.single σ v :=
  X.chainsToFinsupp_ιChainComplex σ v

/-- The function supported at a simplex `σ` with value `v` is the chain of `σ` with coefficient
`v`. -/
@[simp]
theorem chainsLinearEquivFinsupp_symm_single (σ : X _⦋n⦌) (v : V) :
    (X.chainsLinearEquivFinsupp V n).symm (Finsupp.single σ v) =
      X.ιChainComplex (R := ModuleCat.of k V) σ v := by
  rw [LinearEquiv.symm_apply_eq, chainsLinearEquivFinsupp_ιChainComplex]

/-- The chain map induced by a map of simplicial sets pushes the coefficient functions forward
along the map on simplices. -/
theorem chainsLinearEquivFinsupp_chainComplexMap_f {Y : SSet.{w}} (f : X ⟶ Y)
    (c : (X.chainComplex (ModuleCat.of k V)).X n) :
    Y.chainsLinearEquivFinsupp V n ((chainComplexMap f (ModuleCat.of k V)).f n c) =
      Finsupp.mapDomain (f.app _) (X.chainsLinearEquivFinsupp V n c) := by
  have := X.chainComplex_linearMap_ext
    (L := (Y.chainsLinearEquivFinsupp V n).toLinearMap ∘ₗ
      ((chainComplexMap f (ModuleCat.of k V)).f n).hom)
    (L' := Finsupp.lmapDomain V k (f.app _) ∘ₗ (X.chainsLinearEquivFinsupp V n).toLinearMap)
    fun σ v ↦ by
      have h : (chainComplexMap f (ModuleCat.of k V)).f n
          (X.ιChainComplex (R := ModuleCat.of k V) σ v) =
          Y.ιChainComplex (R := ModuleCat.of k V) (f.app _ σ) v :=
        congrArg (fun g ↦ g.hom v) (ι_chainComplexMap_f X Y f (ModuleCat.of k V) σ)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
        h, chainsLinearEquivFinsupp_ιChainComplex,
        chainsLinearEquivFinsupp_ιChainComplex, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact LinearMap.congr_fun this c

/-- Changing the coefficients along a linear map `ψ` applies `ψ` to the coefficient functions. -/
theorem chainsLinearEquivFinsupp_chainComplexFunctor_map {ψ : V →ₗ[k] W}
    (c : (X.chainComplex (ModuleCat.of k V)).X n) :
    X.chainsLinearEquivFinsupp W n
        ((((chainComplexFunctor (ModuleCat.{w} k)).map (ModuleCat.ofHom ψ)).app X).f n c) =
      Finsupp.mapRange ψ ψ.map_zero (X.chainsLinearEquivFinsupp V n c) := by
  have := X.chainComplex_linearMap_ext
    (L := (X.chainsLinearEquivFinsupp W n).toLinearMap ∘ₗ
      ((((chainComplexFunctor (ModuleCat.{w} k)).map (ModuleCat.ofHom ψ)).app X).f n).hom)
    (L' := Finsupp.mapRange.linearMap ψ ∘ₗ (X.chainsLinearEquivFinsupp V n).toLinearMap)
    fun σ v ↦ by
      have h : (((chainComplexFunctor (ModuleCat.{w} k)).map (ModuleCat.ofHom ψ)).app X).f n
          (X.ιChainComplex (R := ModuleCat.of k V) σ v) =
          X.ιChainComplex (R := ModuleCat.of k W) σ (ψ v) :=
        congrArg (fun g ↦ g.hom v)
          (TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f (X := X)
            (ModuleCat.ofHom ψ) σ)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
        h, chainsLinearEquivFinsupp_ιChainComplex,
        chainsLinearEquivFinsupp_ιChainComplex, Finsupp.mapRange.linearMap_apply,
        Finsupp.mapRange_single]
  exact LinearMap.congr_fun this c

end Chains

end SSet
