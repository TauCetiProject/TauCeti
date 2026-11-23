/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic

/-!
# The action of a coefficient module on twisted singular chains

Let `K` be a local system of modules over a commutative ring `R` on a space `X`, and let `M` be an
`R`-module. Tensoring with `M` sends the chains twisted by `K` to the chains twisted by `M ⊗ K`,
the tensor product of the constant system `M` with `K`: the chain map
`M ⊗ C(X; K) ⟶ C(X; M ⊗ K)` sends `m ⊗ (σ, b)` to `(σ, m ⊗ b)`
(`TauCeti.LocalCoefficientSystem.twistedChainComplexAction`). It is built on the simplicial
modules, because `M ⊗ -` preserves the coproduct of simplex summands, and transferred to chain
complexes along Mathlib's `AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso`.

The action is natural in `K` (`TauCeti.LocalCoefficientSystem.twistedChainComplexAction_naturality`)
and in the space (`TauCeti.LocalCoefficientSystem.twistedChainComplexAction_space_naturality`),
through the comparison `TauCeti.LocalCoefficientSystem.pullbackConstantTensorIso`. It is the action
along which twisted cochains with values in `M` cap twisted chains.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Chapters VII–VIII.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex
open scoped Simplicial

universe v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type (max v w)} [CommRing R] {X : TopCat.{v}}

variable (M : ModuleCat.{max v w} R) (K : LocalCoefficientSystem.{max v w, v, max v w} R X)

/-- Tensoring with `M` preserves the coproduct decomposition of twisted chains. -/
private def isColimitTensorLeftTwistedChains (n : SimplexCategoryᵒᵖ) :
    IsColimit ((tensorLeft M).mapCocone (Cofan.mk ((twistedChains K).obj n) (ιTwistedChains K))) :=
  isColimitOfPreserves (tensorLeft M) (isColimitCofanTwistedChains K n)

private lemma tensorLeft_twistedChains_hom_ext {n : SimplexCategoryᵒᵖ} {A : ModuleCat.{max v w} R}
    {f g : M ⊗ (twistedChains K).obj n ⟶ A}
    (h : ∀ σ, (M ◁ ιTwistedChains K σ) ≫ f = (M ◁ ιTwistedChains K σ) ≫ g) : f = g :=
  (isColimitTensorLeftTwistedChains M K n).hom_ext fun ⟨σ⟩ ↦ h σ

/-- The degree-`n` component of the action: `m ⊗ (σ, b) ↦ (σ, m ⊗ b)`. -/
private def twistedChainsActionApp (n : SimplexCategoryᵒᵖ) :
    M ⊗ (twistedChains K).obj n ⟶ (twistedChains ((constantFunctor X).obj M ⊗ K)).obj n :=
  (isColimitTensorLeftTwistedChains M K n).desc
    { pt := _
      ι := Discrete.natTrans fun σ ↦ ιTwistedChains ((constantFunctor X).obj M ⊗ K) σ.as }

@[reassoc]
private lemma whiskerLeft_ιTwistedChains_twistedChainsActionApp (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    (M ◁ ιTwistedChains K σ) ≫ twistedChainsActionApp M K n =
      ιTwistedChains ((constantFunctor X).obj M ⊗ K) σ :=
  (isColimitTensorLeftTwistedChains M K n).fac _ ⟨σ⟩

/-- The action of `M` on the simplicial module of chains twisted by `K`, with values in the chains
twisted by `M ⊗ K`. -/
private def twistedChainsAction :
    ((SimplicialObject.whiskering _ _).obj (tensorLeft M)).obj (twistedChains K) ⟶
      twistedChains ((constantFunctor X).obj M ⊗ K) where
  app := twistedChainsActionApp M K
  naturality {m n} α := by
    apply tensorLeft_twistedChains_hom_ext
    intro σ
    -- the transport of `M ⊗ K` is the identity of `M` tensored with the transport of `K`
    have h : ((constantFunctor X).obj M ⊗ K).map (vertexTransport α σ) =
        M ◁ K.map (vertexTransport α σ) := by
      simp [Monoidal.tensorObj_map]
    dsimp only [Functor.whiskeringRight_obj_obj, Functor.comp_map, curriedTensor_obj_map]
    rw [← whiskerLeft_comp_assoc, ιTwistedChains_map, whiskerLeft_comp_assoc,
      whiskerLeft_ιTwistedChains_twistedChainsActionApp, ← h,
      whiskerLeft_ιTwistedChains_twistedChainsActionApp_assoc]
    exact (ιTwistedChains_map _ α σ).symm

/-- **The action of the coefficient module `M` on twisted chains**: the chain map
`M ⊗ C(X; K) ⟶ C(X; M ⊗ K)` sending `m ⊗ (σ, b)` to `(σ, m ⊗ b)`, where `M ⊗ K` is the tensor
product of the constant system `M` with `K`. It is the action along which twisted cochains with
values in `M` cap twisted chains. -/
def twistedChainComplexAction :
    ((tensorLeft M).mapHomologicalComplex _).obj K.twistedChainComplex ⟶
      ((constantFunctor X).obj M ⊗ K).twistedChainComplex :=
  ((tensorLeft M).mapHomologicalComplex _).map
      (twistedChainComplexIsoAlternatingFaceMapComplex K).hom ≫
    (alternatingFaceMapComplexCompMapHomologicalComplexIso (tensorLeft M)).hom.app
      (twistedChains K) ≫
      (alternatingFaceMapComplex _).map (twistedChainsAction M K) ≫
        (twistedChainComplexIsoAlternatingFaceMapComplex _).inv

/-- On the summand of a simplex, the action of `M` sends `m ⊗ b` to the coefficient `m ⊗ b` of the
same simplex. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_ιTwistedChainComplex_twistedChainComplexAction_f (q : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋q⦌) :
    (M ◁ ιTwistedChainComplex K q σ) ≫ (twistedChainComplexAction M K).f q =
      ιTwistedChainComplex ((constantFunctor X).obj M ⊗ K) q σ := by
  have hf : (twistedChainComplexAction M K).f q =
      (M ◁ (twistedChainComplexIsoAlternatingFaceMapComplex K).hom.f q) ≫
        twistedChainsActionApp M K _ ≫
          (twistedChainComplexIsoAlternatingFaceMapComplex _).inv.f q := by
    simp [twistedChainComplexAction, twistedChainsAction]
  rw [hf, ← whiskerLeft_comp_assoc, ιTwistedChainComplex_isoAlternatingFaceMapComplex_hom_f,
    whiskerLeft_ιTwistedChains_twistedChainsActionApp_assoc]
  exact ιTwistedChains_isoAlternatingFaceMapComplex_inv_f _ q σ

variable {M K} in
/-- Two chain maps out of `M ⊗ C(X; K)` agree in a degree as soon as they agree on every
simplex summand. -/
lemma tensorLeft_twistedChainComplex_hom_ext {q : ℕ} {A : ModuleCat.{max v w} R}
    {f g : M ⊗ K.twistedChainComplex.X q ⟶ A}
    (h : ∀ σ, (M ◁ ιTwistedChainComplex K q σ) ≫ f = (M ◁ ιTwistedChainComplex K q σ) ≫ g) :
    f = g :=
  (isColimitOfPreserves (tensorLeft M) (isColimitTwistedChainComplexXCofan K q)).hom_ext
    fun ⟨σ⟩ ↦ h σ

variable {M K} {K' : LocalCoefficientSystem.{max v w, v, max v w} R X}

/-- The action of `M` commutes with changes of the local coefficient system `K`. -/
@[reassoc]
lemma twistedChainComplexAction_naturality (θ : K ⟶ K') :
    twistedChainComplexAction M K ≫
        twistedChainComplexCoefficientMap ((constantFunctor X).obj M ◁ θ) =
      ((tensorLeft M).mapHomologicalComplex _).map (twistedChainComplexCoefficientMap θ) ≫
        twistedChainComplexAction M K' := by
  ext q : 1
  apply tensorLeft_twistedChainComplex_hom_ext
  intro σ
  have h₁ : (M ◁ ιTwistedChainComplex K q σ) ≫ (twistedChainComplexAction M K ≫
      twistedChainComplexCoefficientMap ((constantFunctor X).obj M ◁ θ)).f q =
        (M ◁ θ.app (initialVertex σ)) ≫
          ιTwistedChainComplex ((constantFunctor X).obj M ⊗ K') q σ := by
    rw [comp_f]
    exact (whiskerLeft_ιTwistedChainComplex_twistedChainComplexAction_f_assoc M K q σ _).trans
      (ιTwistedChainComplex_twistedChainComplexCoefficientMap_f _ q σ)
  have h₂ : (M ◁ ιTwistedChainComplex K q σ) ≫
      (((tensorLeft M).mapHomologicalComplex _).map (twistedChainComplexCoefficientMap θ) ≫
        twistedChainComplexAction M K').f q =
        (M ◁ θ.app (initialVertex σ)) ≫
          ιTwistedChainComplex ((constantFunctor X).obj M ⊗ K') q σ := by
    rw [comp_f, Functor.mapHomologicalComplex_map_f, curriedTensor_obj_map,
      ← whiskerLeft_comp_assoc, ιTwistedChainComplex_twistedChainComplexCoefficientMap_f,
      whiskerLeft_comp_assoc, whiskerLeft_ιTwistedChainComplex_twistedChainComplexAction_f]
  exact h₁.trans h₂.symm

section Space

variable {Y : TopCat.{v}} (f : X ⟶ Y) (M : ModuleCat.{max v w} R)
  (K : LocalCoefficientSystem.{max v w, v, max v w} R Y)

/-- The action of `M` commutes with continuous maps: acting on the chains of `X` twisted by the
pullback of `K` and pushing forward along `f` is pushing forward and acting on the chains of `Y`
twisted by `K`. -/
@[reassoc]
lemma twistedChainComplexAction_space_naturality :
    twistedChainComplexAction M ((pullback f.hom).obj K) ≫
        twistedChainComplexCoefficientMap (pullbackConstantTensorIso f.hom M K).hom ≫
          twistedChainComplexMap f ((constantFunctor Y).obj M ⊗ K) =
      ((tensorLeft M).mapHomologicalComplex _).map (twistedChainComplexMap f K) ≫
        twistedChainComplexAction M K := by
  ext q : 1
  apply tensorLeft_twistedChainComplex_hom_ext
  intro σ
  have h₁ : (M ◁ ιTwistedChainComplex ((pullback f.hom).obj K) q σ) ≫
      (twistedChainComplexAction M ((pullback f.hom).obj K) ≫
        twistedChainComplexCoefficientMap (pullbackConstantTensorIso f.hom M K).hom ≫
          twistedChainComplexMap f ((constantFunctor Y).obj M ⊗ K)).f q =
        ιTwistedChainComplex ((constantFunctor Y).obj M ⊗ K) q ((TopCat.toSSet.map f).app _ σ) := by
    rw [comp_f, comp_f]
    refine (whiskerLeft_ιTwistedChainComplex_twistedChainComplexAction_f_assoc _ _ q σ _).trans ?_
    refine (ιTwistedChainComplex_twistedChainComplexCoefficientMap_f_assoc _ q σ _).trans ?_
    rw [pullbackConstantTensorIso_hom_app]
    exact (Category.id_comp _).trans (ιTwistedChainComplex_twistedChainComplexMap_f f _ q σ)
  have h₂ : (M ◁ ιTwistedChainComplex ((pullback f.hom).obj K) q σ) ≫
      (((tensorLeft M).mapHomologicalComplex _).map (twistedChainComplexMap f K) ≫
        twistedChainComplexAction M K).f q =
        ιTwistedChainComplex ((constantFunctor Y).obj M ⊗ K) q ((TopCat.toSSet.map f).app _ σ) := by
    rw [comp_f, Functor.mapHomologicalComplex_map_f, curriedTensor_obj_map,
      ← whiskerLeft_comp_assoc, ιTwistedChainComplex_twistedChainComplexMap_f]
    exact whiskerLeft_ιTwistedChainComplex_twistedChainComplexAction_f M K q _
  exact h₁.trans h₂.symm

end Space

end TauCeti.LocalCoefficientSystem
