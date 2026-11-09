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
changes of coefficients. It also records that simplicial chain modules with semisimple
coefficients are semisimple, and those with projective coefficients are projective, both as
modules and, for coefficients in any preadditive category with coproducts, as objects of that
category.

For a module `V` over a ring `k`, the simplicial `n`-chains
`(X.chainComplex (ModuleCat.of k V)).X n` are the finitely supported functions from the
`n`-simplices of `X` to `V` (`SSet.chainsLinearEquivFinsupp`): a chain is a finite sum
`∑ vᵢ σᵢ` of simplices `σᵢ` with coefficients `vᵢ ∈ V`. Under this identification, the chain
maps induced by maps of simplicial sets push coefficient functions forward along the map on
simplices (`SSet.chainsLinearEquivFinsupp_chainComplexMap_f`), and changing the coefficients
along a linear map applies it to the coefficient functions
(`SSet.chainsLinearEquivFinsupp_chainComplexFunctor_map`).

## Implementation notes

The equivalence `SSet.chainsLinearEquivFinsupp` composes Mathlib's identification of a coproduct
in `ModuleCat` with a direct sum (`ModuleCat.coprodIsoDirectSum`) with the equivalence between
direct sums and finitely supported functions (`finsuppLEquivDirectSum`). The simplicial chain
complex and its description as a coproduct come from Mathlib's
`Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic` (Joël Riou and Andrew Yang).
-/

public section

noncomputable section

open CategoryTheory Limits

open scoped Simplicial

universe w v u

namespace SSet

section

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  {X : SSet.{w}} {R R' : C}

/-- Mapping the coefficient object of simplicial chains applies the coefficient morphism before
the coproduct inclusion associated to each simplex. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_chainComplexFunctor_map_app_f (f : R ⟶ R') {n : ℕ} (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ (((chainComplexFunctor C).map f).app X).f n =
      f ≫ X.ιChainComplex x := by
  dsimp [chainComplexFunctor, ιChainComplex, chainComplex]
  simp

/-- The degreewise components of the chain maps induced by maps of simplicial sets compose like
the maps themselves. -/
@[reassoc]
lemma chainComplexMap_f_comp {X Y Z : SSet.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (R : C) (n : ℕ) :
    (chainComplexMap f R).f n ≫ (chainComplexMap g R).f n =
      (chainComplexMap (f ≫ g) R).f n := by
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp]

/-- The chain maps induced by maps of simplicial sets commute, degreewise, with changes of
coefficients. -/
@[reassoc]
lemma chainComplexMap_f_chainComplexFunctor_map_app_f {X Y : SSet.{w}} (f : X ⟶ Y)
    (u : R ⟶ R') (n : ℕ) :
    (chainComplexMap f R).f n ≫ (((chainComplexFunctor C).map u).app Y).f n =
      (((chainComplexFunctor C).map u).app X).f n ≫ (chainComplexMap f R').f n := by
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, NatTrans.naturality]

/-- The summand inclusion of a simplex `x`, followed by a simplicial operator of the simplicial
object `[n] ↦ ∐_{X _⦋n⦌} R` whose chain complex is `X.chainComplex R`, is the summand inclusion of
the image of `x`. -/
@[reassoc]
lemma ιChainComplex_map {m n : ℕ} (x : X _⦋n⦌) (f : ⦋m⦌ ⟶ ⦋n⦌) :
    X.ιChainComplex (R := R) x ≫
        (((SimplicialObject.whiskering _ _).obj (sigmaConst.obj R)).obj X).map f.op =
      X.ιChainComplex (X.map f.op x) := by
  simp [ιChainComplex]

end

/-- The simplicial chain modules `Cₙ(X; M) = ⨁ M` with semisimple coefficients `M` are
semisimple. -/
instance isSemisimpleModule_chainComplex_X {k : Type*} [Ring k] (X : SSet.{w})
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
  factors f e _ := ⟨Cofan.IsColimit.desc (X.isColimitChainComplexXCofan R n)
      fun x ↦ Projective.factorThru (X.ιChainComplex x ≫ f) e,
    -- The injections of the cofan defining the chains are the summand inclusions
    -- `X.ιChainComplex x`, so `Cofan.IsColimit.fac` computes the lift on each summand.
    X.chainComplex_hom_ext fun x ↦
      (Cofan.IsColimit.fac_assoc _ _ x _).trans (Projective.factorThru_comp _ _)⟩

/-! ### Simplicial chains as finitely supported functions -/

section Chains

variable (X : SSet.{w}) {k : Type*} [Ring k]

variable {V W : Type w} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] {n : ℕ}

variable (V n) in
open scoped Classical in
/-- **The simplicial `n`-chains are the finitely supported functions on `n`-simplices**: the linear
equivalence sending the chain of a simplex `σ` with coefficient `v` to the function supported at
`σ` with value `v`. -/
def chainsLinearEquivFinsupp :
    (X.chainComplex (ModuleCat.of k V)).X n ≃ₗ[k] (X _⦋n⦌ →₀ V) :=
  (ModuleCat.coprodIsoDirectSum fun _ : X _⦋n⦌ ↦ ModuleCat.of k V).toLinearEquiv.trans
    (finsuppLEquivDirectSum k V (X _⦋n⦌)).symm

/-- The chain of a simplex `σ` with coefficient `v` is the function supported at `σ` with value
`v`. -/
@[simp]
theorem chainsLinearEquivFinsupp_ιChainComplex (σ : X _⦋n⦌) (v : V) :
    X.chainsLinearEquivFinsupp V n (X.ιChainComplex (R := ModuleCat.of k V) σ v) =
      Finsupp.single σ v := by
  rw [chainsLinearEquivFinsupp, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply, ιChainComplex,
    ModuleCat.ι_coprodIsoDirectSum_hom_apply, finsuppLEquivDirectSum_symm_lof]

/-- The function supported at a simplex `σ` with value `v` is the chain of `σ` with coefficient
`v`. -/
@[simp]
theorem chainsLinearEquivFinsupp_symm_single (σ : X _⦋n⦌) (v : V) :
    (X.chainsLinearEquivFinsupp V n).symm (Finsupp.single σ v) =
      X.ιChainComplex (R := ModuleCat.of k V) σ v := by
  rw [LinearEquiv.symm_apply_eq, chainsLinearEquivFinsupp_ιChainComplex]

/-- Linear maps out of the simplicial `n`-chains agree when they agree on every simplex with
every coefficient. -/
theorem chainComplex_linearMap_ext {U : Type*} [AddCommMonoid U] [Module k U]
    {L L' : (X.chainComplex (ModuleCat.of k V)).X n →ₗ[k] U}
    (h : ∀ σ (v : V), L (X.ιChainComplex (R := ModuleCat.of k V) σ v) =
      L' (X.ιChainComplex (R := ModuleCat.of k V) σ v)) : L = L' := by
  have : L ∘ₗ (X.chainsLinearEquivFinsupp V n).symm.toLinearMap =
      L' ∘ₗ (X.chainsLinearEquivFinsupp V n).symm.toLinearMap :=
    Finsupp.lhom_ext fun σ v ↦ by simpa using h σ v
  simpa using congrArg (· ∘ₗ (X.chainsLinearEquivFinsupp V n).toLinearMap) this

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
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← ConcreteCategory.comp_apply,
        ι_chainComplexMap_f]
      rw [chainsLinearEquivFinsupp_ιChainComplex, chainsLinearEquivFinsupp_ιChainComplex]
      simp
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
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← ConcreteCategory.comp_apply,
        ιChainComplex_chainComplexFunctor_map_app_f]
      rw [ConcreteCategory.comp_apply, chainsLinearEquivFinsupp_ιChainComplex,
        chainsLinearEquivFinsupp_ιChainComplex]
      simp
  exact LinearMap.congr_fun this c

end Chains

end SSet
