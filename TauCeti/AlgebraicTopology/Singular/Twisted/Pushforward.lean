/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic

/-!
# Pushing chains of a simply connected space into chains with local coefficients

Let `L` be a local coefficient system on `X` and `f : Z ⟶ X` a map from a simply connected space,
with a base point `z₀ : Z`.  A singular simplex `σ` of `Z` together with a coefficient
`a ∈ L(f z₀)` gives a twisted simplex of `X`: the simplex `f ∘ σ` with the coefficient transported
from `f z₀` to its initial vertex along the path class inside the image of `f`
(`ContinuousMap.pathClass`).  Extended to integral chains of `Z`, this is the **twisted
pushforward** `twistedPushforward L f z₀`.  Since `Z` is simply connected, `f^* L` is trivialized
by these transports, and the twisted pushforward is the composite of this trivialization with the
pushforward of twisted chains along `f`.

It is the tool to turn a natural transformation between singular chain theories, given on
contractible models, into one between the corresponding theories with local coefficients: a model
chain is pushed forward along a simplex or cube, carrying the coefficient of the generator.

## Main definitions

* `TauCeti.LocalCoefficientSystem.twistedPushforward L f z₀ n`: the twisted pushforward of
  integral singular `n`-chains of `Z`.

## Main results

* `TauCeti.LocalCoefficientSystem.twistedPushforward_simplexChain`: its value on a simplex.
* `TauCeti.LocalCoefficientSystem.twistedPushforward_d`: it commutes with the boundaries.
* `TauCeti.LocalCoefficientSystem.twistedPushforward_map`: change of the source along a map of
  simply connected spaces, with change of base point.
* `TauCeti.LocalCoefficientSystem.twistedChainComplexMap_twistedPushforward`,
  `TauCeti.LocalCoefficientSystem.twistedChainComplexCoefficientMap_twistedPushforward`:
  naturality in the space and in the coefficient system.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter XIV.
-/

public section

noncomputable section

open CategoryTheory Limits SimplexCategory

open scoped Simplicial

universe u v

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] {X Z : TopCat.{v}} [SimplyConnectedSpace Z]

variable (L : LocalCoefficientSystem.{u, v, v} R X) (f : Z ⟶ X) (z₀ : Z)

/-- The **twisted pushforward** of integral singular chains of a simply connected space `Z`
along `f : Z ⟶ X`: a simplex `σ` with a coefficient `a ∈ L(f z₀)` goes to the twisted simplex
`f ∘ σ` with the coefficient transported from `f z₀` to its initial vertex. -/
def twistedPushforward (n : ℕ) :
    ((singularChains (ULift.{v} ℤ)).obj Z).X n →ₗ[ULift.{v} ℤ]
      (L.obj (FundamentalGroupoid.mk (f z₀)) →ₗ[R] (twistedChainComplex L).X n) :=
  chainsDesc fun σ ↦ (ιTwistedChainComplex L n ((TopCat.toSSet.map f).app _ σ)).hom ∘ₗ
    (L.map (f.hom.pathClass z₀ (TopCat.simplexMap σ (toTopInitialVertex _)))).hom

variable {L f z₀}

/-- The twisted pushforward of a simplex. -/
@[simp]
theorem twistedPushforward_simplexChain {n : ℕ} (σ : (TopCat.toSSet.obj Z) _⦋n⦌)
    (r : ULift.{v} ℤ) (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    twistedPushforward L f z₀ n (simplexChain σ r) a =
      r.down • ιTwistedChainComplex L n ((TopCat.toSSet.map f).app _ σ)
        (L.map (f.hom.pathClass z₀ (TopCat.simplexMap σ (toTopInitialVertex _))) a) := by
  rw [twistedPushforward, chainsDesc_simplexChain]
  rfl

/-- Transport between the initial vertices of a simplex and of a reindexing of it is the path
class inside the simplex. -/
theorem vertexTransport_eq_pathClass {Y : TopCat.{v}} {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)
    (σ : (TopCat.toSSet.obj Y).obj m) :
    vertexTransport α σ = (TopCat.simplexMap σ).pathClass (toTopInitialVertex m.unop)
      (toTop.map α.unop (toTopInitialVertex n.unop)) := by
  obtain ⟨q⟩ := PathConnectedSpace.joined (toTopInitialVertex m.unop)
    (toTop.map α.unop (toTopInitialVertex n.unop))
  rw [vertexTransport_eq_mk α σ q, ContinuousMap.pathClass_eq_mk]

/-- An additive map, as a linear map over the lifted integers. -/
private def intLinear {M N : Type*} [AddCommGroup M] [AddCommGroup N] (g : M →+ N) :
    M →ₗ[ULift.{v} ℤ] N where
  toFun := g
  map_add' := g.map_add
  map_smul' r x := by simp only [ULift.smul_def, map_zsmul, RingHom.id_apply]

/-- Evaluation at an element, as a linear map over the lifted integers. -/
private def evalAt {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (a : M) : (M →ₗ[R] N) →ₗ[ULift.{v} ℤ] N :=
  intLinear ⟨⟨fun φ ↦ φ a, rfl⟩, fun _ _ ↦ rfl⟩

/-- The twisted pushforward of a simplex with coefficient `1`, as a morphism of modules. -/
theorem twistedPushforward_simplexChain_one {n : ℕ} (σ : (TopCat.toSSet.obj Z) _⦋n⦌) :
    twistedPushforward L f z₀ n (simplexChain σ 1) =
      (L.map (f.hom.pathClass z₀ (TopCat.simplexMap σ (toTopInitialVertex _))) ≫
        ιTwistedChainComplex L n ((TopCat.toSSet.map f).app _ σ)).hom := by
  rw [twistedPushforward, chainsDesc_simplexChain, one_smul]
  rfl

/-- The coefficient transport of the twisted pushforward composed with the vertex transport of a
face is the coefficient transport of the face. -/
private theorem pathClass_comp_vertexTransport {n : ℕ} (σ : (TopCat.toSSet.obj Z) _⦋n + 1⦌)
    (i : Fin (n + 2)) :
    f.hom.pathClass z₀ (TopCat.simplexMap σ (toTopInitialVertex _)) ≫
        vertexTransport (δ i).op ((TopCat.toSSet.map f).app _ σ) =
      f.hom.pathClass z₀ (TopCat.simplexMap ((TopCat.toSSet.obj Z).δ i σ)
        (toTopInitialVertex _)) := by
  rw [vertexTransport_eq_pathClass]
  -- `TopCat.simplexMap` of the pushed-forward simplex is `f ∘ TopCat.simplexMap σ` by definition
  -- (`TopCat.simplexMap_app`), which a rewrite cannot expose inside the dependent composite.
  exact (congrArg (f.hom.pathClass z₀ _ ≫ ·)
    (ContinuousMap.pathClass_comp f.hom (TopCat.simplexMap σ) _ _)).trans
      (ContinuousMap.pathClass_comp_pathClass _ _ _ _)

/-- The twisted pushforward commutes with the boundaries, on a simplex. -/
private theorem twistedPushforward_simplexChain_one_d {n : ℕ}
    (σ : (TopCat.toSSet.obj Z) _⦋n + 1⦌) :
    L.map (f.hom.pathClass z₀ (TopCat.simplexMap σ (toTopInitialVertex _))) ≫
        ιTwistedChainComplex L (n + 1) ((TopCat.toSSet.map f).app _ σ) ≫
          (twistedChainComplex L).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (L.map (f.hom.pathClass z₀ (TopCat.simplexMap ((TopCat.toSSet.obj Z).δ i σ)
          (toTopInitialVertex _))) ≫
          ιTwistedChainComplex L n
            ((TopCat.toSSet.map f).app _ ((TopCat.toSSet.obj Z).δ i σ))) := by
  -- The source of `ιTwistedChainComplex` is the fibre at the initial vertex of `f ∘ σ`, which is
  -- the fibre at `f (σ v₀)` only by definition, so the boundary formula is composed as a term.
  refine (congrArg (fun g ↦ L.map (f.hom.pathClass z₀ (TopCat.simplexMap σ
    (toTopInitialVertex _))) ≫ g)
      (ιTwistedChainComplex_d L n ((TopCat.toSSet.map f).app _ σ))).trans ?_
  refine (Preadditive.comp_sum _ _ _).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  exact (Preadditive.comp_zsmul _ _ _).trans (congrArg _ ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) ((L.map_comp _ _).symm.trans
      (congrArg L.map (pathClass_comp_vertexTransport σ i))))))

/-- The twisted pushforward commutes with the boundaries. -/
theorem twistedPushforward_d {n : ℕ} (y : ((singularChains (ULift.{v} ℤ)).obj Z).X (n + 1))
    (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    (twistedChainComplex L).d (n + 1) n (twistedPushforward L f z₀ (n + 1) y a) =
      twistedPushforward L f z₀ n (((singularChains (ULift.{v} ℤ)).obj Z).d (n + 1) n y) a := by
  have h := singularChains_linearMap_ext
    (L := intLinear ((twistedChainComplex L).d (n + 1) n).hom.toAddMonoidHom ∘ₗ evalAt a ∘ₗ
      twistedPushforward L f z₀ (n + 1))
    (L' := evalAt a ∘ₗ twistedPushforward L f z₀ n ∘ₗ
      (((singularChains (ULift.{v} ℤ)).obj Z).d (n + 1) n).hom) fun σ ↦ ?_
  · exact congrArg (fun g ↦ g y) h
  have hσ := congrArg (fun g ↦ g.hom a) (twistedPushforward_simplexChain_one_d (L := L) (f := f)
    (z₀ := z₀) σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply] at hσ
  change (twistedChainComplex L).d (n + 1) n (twistedPushforward L f z₀ (n + 1) _ a) =
    twistedPushforward L f z₀ n (((singularChains (ULift.{v} ℤ)).obj Z).d (n + 1) n _) a
  rw [twistedPushforward_simplexChain_one, singularChains_d_simplexChain, map_sum,
    LinearMap.sum_apply]
  simp only [map_zsmul, LinearMap.smul_apply, twistedPushforward_simplexChain_one]
  exact hσ

/-- **Change of source.** Pushing forward the image of a chain under a map `g : Z' ⟶ Z` of simply
connected spaces is pushing forward the chain along `g ≫ f`, from the base point `w₀` of `Z'`,
after transporting the coefficient from `f z₀` to `f (g w₀)`. -/
theorem twistedPushforward_map {Z' : TopCat.{v}} [SimplyConnectedSpace Z'] (g : Z' ⟶ Z)
    (w₀ : Z') {n : ℕ} (y : ((singularChains (ULift.{v} ℤ)).obj Z').X n)
    (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    twistedPushforward L f z₀ n (((singularChains (ULift.{v} ℤ)).map g).f n y) a =
      twistedPushforward L (g ≫ f) w₀ n y (L.map (f.hom.pathClass z₀ (g w₀)) a) := by
  have h := singularChains_linearMap_ext
    (L := evalAt a ∘ₗ twistedPushforward L f z₀ n ∘ₗ
      (((singularChains (ULift.{v} ℤ)).map g).f n).hom)
    (L' := evalAt (L.map (f.hom.pathClass z₀ (g w₀)) a) ∘ₗ twistedPushforward L (g ≫ f) w₀ n)
    fun σ ↦ ?_
  · exact congrArg (fun φ ↦ φ y) h
  change twistedPushforward L f z₀ n (((singularChains (ULift.{v} ℤ)).map g).f n _) a =
    twistedPushforward L (g ≫ f) w₀ n _ (L.map (f.hom.pathClass z₀ (g w₀)) a)
  rw [singularChains_map_f_simplexChain, twistedPushforward_simplexChain_one,
    twistedPushforward_simplexChain_one]
  have hp : f.hom.pathClass z₀ (TopCat.simplexMap ((TopCat.toSSet.map g).app _ σ)
      (toTopInitialVertex _)) = f.hom.pathClass z₀ (g w₀) ≫
        (g ≫ f).hom.pathClass w₀ (TopCat.simplexMap σ (toTopInitialVertex _)) :=
    -- `(g ≫ f).hom` is `f.hom.comp g.hom` by definition.
    ((congrArg (f.hom.pathClass z₀ (g w₀) ≫ ·) (ContinuousMap.pathClass_comp f.hom g.hom _ _)).trans
      (ContinuousMap.pathClass_comp_pathClass _ _ _ _)).symm
  rw [hp]
  exact congrArg (fun (φ : L.obj (FundamentalGroupoid.mk (f z₀)) ⟶
      L.obj (FundamentalGroupoid.mk (f (g (TopCat.simplexMap σ (toTopInitialVertex _)))))) ↦
    (φ ≫ ιTwistedChainComplex L n ((TopCat.toSSet.map (g ≫ f)).app _ σ)).hom a) (L.map_comp _ _)

/-- The twisted pushforward is natural in the space: pushing forward into `Y` along `h` after
pushing forward into `X` with coefficients in the pulled back system is pushing forward along
`f ≫ h`. -/
theorem twistedChainComplexMap_twistedPushforward {Y : TopCat.{v}}
    (L : LocalCoefficientSystem.{u, v, v} R Y) (h : X ⟶ Y) {n : ℕ}
    (y : ((singularChains (ULift.{v} ℤ)).obj Z).X n)
    (a : ((pullback h.hom).obj L).obj (FundamentalGroupoid.mk (f z₀))) :
    (twistedChainComplexMap h L).f n (twistedPushforward ((pullback h.hom).obj L) f z₀ n y a) =
      twistedPushforward L (f ≫ h) z₀ n y a := by
  have hy := singularChains_linearMap_ext
    (L := intLinear ((twistedChainComplexMap h L).f n).hom.toAddMonoidHom ∘ₗ evalAt a ∘ₗ
      twistedPushforward ((pullback h.hom).obj L) f z₀ n)
    (L' := evalAt (M := L.obj (FundamentalGroupoid.mk ((f ≫ h) z₀))) a ∘ₗ
      twistedPushforward L (f ≫ h) z₀ n) fun σ ↦ ?_
  · exact congrArg (fun φ ↦ φ y) hy
  change (twistedChainComplexMap h L).f n
      (twistedPushforward ((pullback h.hom).obj L) f z₀ n _ a) =
    twistedPushforward L (f ≫ h) z₀ n _ a
  rw [twistedPushforward_simplexChain_one, twistedPushforward_simplexChain_one,
    ← ModuleCat.comp_apply]
  exact congrArg (fun φ ↦ φ.hom a) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (ιTwistedChainComplex_twistedChainComplexMap_f h L n _)).trans
      (congrArg (fun p ↦ L.map p ≫ ιTwistedChainComplex L n ((TopCat.toSSet.map (f ≫ h)).app _ σ))
        (ContinuousMap.map_pathClass h.hom f.hom z₀ (TopCat.simplexMap σ (toTopInitialVertex _))))))

/-- The twisted pushforward is natural in the coefficient system. -/
theorem twistedChainComplexCoefficientMap_twistedPushforward
    {K : LocalCoefficientSystem.{u, v, v} R X} (η : L ⟶ K) {n : ℕ}
    (y : ((singularChains (ULift.{v} ℤ)).obj Z).X n)
    (a : L.obj (FundamentalGroupoid.mk (f z₀))) :
    (twistedChainComplexCoefficientMap η).f n (twistedPushforward L f z₀ n y a) =
      twistedPushforward K f z₀ n y (η.app _ a) := by
  have hy := singularChains_linearMap_ext
    (L := intLinear ((twistedChainComplexCoefficientMap η).f n).hom.toAddMonoidHom ∘ₗ
      evalAt a ∘ₗ twistedPushforward L f z₀ n)
    (L' := evalAt (η.app _ a) ∘ₗ twistedPushforward K f z₀ n) fun σ ↦ ?_
  · exact congrArg (fun φ ↦ φ y) hy
  change (twistedChainComplexCoefficientMap η).f n (twistedPushforward L f z₀ n _ a) =
    twistedPushforward K f z₀ n _ (η.app _ a)
  rw [twistedPushforward_simplexChain_one, twistedPushforward_simplexChain_one,
    ← ModuleCat.comp_apply, ← ModuleCat.comp_apply]
  exact congrArg (fun φ ↦ φ.hom a) ((Category.assoc _ _ _).trans
    (((congrArg (_ ≫ ·) (ιTwistedChainComplex_twistedChainComplexCoefficientMap_f η n _)).trans
      (Category.assoc _ _ _).symm).trans ((congrArg (· ≫ _) (η.naturality _)).trans
        (Category.assoc _ _ _))))

end LocalCoefficientSystem

end TauCeti
