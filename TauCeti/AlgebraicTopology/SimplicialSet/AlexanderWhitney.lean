/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import TauCeti.AlgebraicTopology.SimplicialObject.AlexanderWhitney
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# The Alexander–Whitney map

Let `C` be a preadditive monoidal category with `w`-small coproducts, and let `R` and `S` be
objects of `C`.  For simplicial sets `K` and `L`, the Alexander–Whitney map is the morphism
of chain complexes `SSet.alexanderWhitney K L R S` from `(K ⊗ L).chainComplex (R ⊗ S)`, the
simplicial chains of the product `K × L`, to `K.chainComplex R ⊗ L.chainComplex S`, the tensor
product of the simplicial chains of the factors.  On an `n`-simplex `(x, y)` of `K × L` it is
`∑_{p + q = n} x|[0, …, p] ⊗ y|[p, …, n]`,
the front `p`-face of `x` tensored with the back `q`-face of `y`, the faces being Mathlib's
`SimplexCategory.subinterval`.  The tensor product of chain complexes is Mathlib's monoidal
structure on `ChainComplex C ℕ`, whose differential is `d (a ⊗ b) = d a ⊗ b + (-1)^p a ⊗ d b`
for `a` of degree `p`.

It is the Alexander–Whitney map `CategoryTheory.SimplicialObject.alexanderWhitney` of the
simplicial objects of chains of `K` and of `L`, precomposed with the map sending the summand
`R ⊗ S` of a simplex `(x, y)` to the tensor product of the summands of `x` and of `y`.

The Alexander–Whitney map is one half of the Eilenberg–Zilber comparison between chains on a
product and tensor products of chains, and composing it with the diagonal gives the cup product
of cochains.  For the usual coefficients take `C := ModuleCat k` and `R = S = k`.

## Main definitions and results

* `SSet.alexanderWhitney`: the Alexander–Whitney chain map.
* `SSet.ιChainComplex_alexanderWhitney_f`: its value on a simplex.
* `SSet.alexanderWhitney_naturality`: it is natural in both simplicial sets.
* `SSet.alexanderWhitney_coefficient_naturality`: it is natural in both coefficient objects.

## References

* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
* C. Weibel, *An Introduction to Homological Algebra*, Section 8.5.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial HomologicalComplex

universe w v u

namespace SSet

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{w} C]

variable (K L : SSet.{w}) (R S : C)

/-- The comparison of simplicial objects from the chains of `K × L` with coefficients in `R ⊗ S` to
the degreewise tensor product of the chains of `K` and of `L`: the summand `R ⊗ S` of a simplex
`(x, y)` goes to the tensor product of the summands of `x` and of `y`. -/
private def chainsTensorComparison :
    ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj (R ⊗ S))).obj (K ⊗ L) ⟶
      ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj R)).obj K ⊗
        ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj S)).obj L where
  app m := Sigma.desc fun x ↦ Sigma.ι (fun _ : K.obj m ↦ R) x.1 ⊗ₘ Sigma.ι (fun _ : L.obj m ↦ S) x.2
  naturality m m' φ := Sigma.hom_ext _ _ fun x ↦ by
    -- The functors are `sigmaConst` after `K`, `L` and `K ⊗ L` only up to unfolding `sigmaConst`,
    -- so the coproduct lemmas are applied through `Eq.trans` rather than by rewriting.
    refine ((Sigma.ι_comp_map'_assoc (f := fun _ : (K ⊗ L).obj m' ↦ R ⊗ S)
      (g := fun _ : (K ⊗ L).obj m ↦ R ⊗ S) _ (fun _ ↦ 𝟙 _) x _).trans ((Category.id_comp _).trans
      (Sigma.ι_comp_desc (fun y : (K ⊗ L).obj m' ↦
        Sigma.ι (fun _ : K.obj m' ↦ R) y.1 ⊗ₘ Sigma.ι (fun _ : L.obj m' ↦ S) y.2) _))).trans
      (Eq.trans ?_ (Sigma.ι_comp_desc_assoc (fun y : (K ⊗ L).obj m ↦
        Sigma.ι (fun _ : K.obj m ↦ R) y.1 ⊗ₘ Sigma.ι (fun _ : L.obj m ↦ S) y.2) x _).symm)
    refine Eq.trans ?_ (tensorHom_comp_tensorHom _ _ _ _).symm
    exact congrArg₂ (· ⊗ₘ ·)
      ((Sigma.ι_comp_map' (f := fun _ : K.obj m' ↦ R) (g := fun _ : K.obj m ↦ R) _
        (fun _ ↦ 𝟙 _) x.1).trans (Category.id_comp _)).symm
      ((Sigma.ι_comp_map' (f := fun _ : L.obj m' ↦ S) (g := fun _ : L.obj m ↦ S) _
        (fun _ ↦ 𝟙 _) x.2).trans (Category.id_comp _)).symm

omit [MonoidalPreadditive C] in
@[reassoc]
private lemma ιChainComplex_chainsTensorComparison {n : ℕ} (x : (K ⊗ L) _⦋n⦌) :
    (K ⊗ L).ιChainComplex x ≫
        ((AlgebraicTopology.alternatingFaceMapComplex C).map
          (chainsTensorComparison K L R S)).f n =
      K.ιChainComplex x.1 ⊗ₘ L.ιChainComplex x.2 :=
  Sigma.ι_comp_desc _ _

/-- The inclusion of a summand into the tensor product of the alternating face map complexes of
the simplicial objects of chains of `K` and of `L` is the inclusion into the tensor product of
the chain complexes of `K` and of `L`. -/
private lemma ιTensorObj_chainComplex (p q n : ℕ) (h : p + q = n) :
    ιTensorObj ((AlgebraicTopology.alternatingFaceMapComplex C).obj
        (((SimplicialObject.whiskering _ _).obj (sigmaConst.obj R)).obj K))
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj
        (((SimplicialObject.whiskering _ _).obj (sigmaConst.obj S)).obj L)) p q n h =
      ιTensorObj (K.chainComplex R) (L.chainComplex S) p q n h := by
  dsimp only [chainComplex, chainComplexFunctor, Functor.postcompose₂_obj_obj_obj_obj,
    Functor.comp_obj]

/-- The Alexander–Whitney map `C(K × L; R ⊗ S) ⟶ C(K; R) ⊗ C(L; S)`, sending an `n`-simplex
`(x, y)` of `K × L` to `∑_{p + q = n} x|[0, …, p] ⊗ y|[p, …, n]`, the front `p`-face of `x`
tensored with the back `q`-face of `y` (`SSet.ιChainComplex_alexanderWhitney_f`).  It is the
Alexander–Whitney map `CategoryTheory.SimplicialObject.alexanderWhitney` of the simplicial objects
of chains of `K` and of `L`, precomposed with the map sending the summand of `(x, y)` to the tensor
product of the summands of `x` and of `y`; it is a morphism of chain complexes for the Koszul sign
convention on the tensor product. -/
def alexanderWhitney :
    (K ⊗ L).chainComplex (R ⊗ S) ⟶ K.chainComplex R ⊗ L.chainComplex S :=
  (AlgebraicTopology.alternatingFaceMapComplex C).map (chainsTensorComparison K L R S) ≫
    SimplicialObject.alexanderWhitney _ _

/-- The Alexander–Whitney map on the summand of an `n`-simplex `x` of `K × L`: the sum over
`p ≤ n` of the front `p`-face of `x.1` tensored with the back `(n - p)`-face of `x.2`. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_alexanderWhitney_f {n : ℕ} (x : (K ⊗ L) _⦋n⦌) :
    (K ⊗ L).ιChainComplex x ≫ (alexanderWhitney K L R S).f n =
      ∑ p : Fin (n + 1),
        (K.ιChainComplex (K.map (SimplexCategory.subinterval 0 p (by omega)).op x.1) ⊗ₘ
          L.ιChainComplex (L.map (SimplexCategory.subinterval p (n - p) (by omega)).op x.2)) ≫
            ιTensorObj _ _ (p : ℕ) (n - p) n (by omega) := by
  rw [alexanderWhitney, HomologicalComplex.comp_f, ιChainComplex_chainsTensorComparison_assoc,
    SimplicialObject.alexanderWhitney_f]
  -- The chains of `K` are the alternating face map complex of the simplicial object of chains
  -- only up to unfolding, so the sum is distributed by `Eq.trans` rather than by rewriting, and
  -- the two inclusions of the summand into the tensor product agree by `ιTensorObj_chainComplex`.
  refine (Preadditive.comp_sum _ _ _).trans (Finset.sum_congr rfl fun p _ ↦ ?_)
  refine (tensorHom_comp_tensorHom_assoc _ _ _ _ _).trans ?_
  rw [ιTensorObj_chainComplex]
  simp only [sigmaConst, Functor.whiskeringRight_obj_obj, Functor.comp_obj, ιChainComplex,
    Functor.comp_map, Sigma.ι_comp_map', Category.id_comp]

variable {K L} in
/-- The Alexander–Whitney map is natural in both simplicial sets. -/
@[reassoc]
lemma alexanderWhitney_naturality {K' L' : SSet.{w}} (f : K ⟶ K') (g : L ⟶ L') :
    chainComplexMap (f ⊗ₘ g) (R ⊗ S) ≫ alexanderWhitney K' L' R S =
      alexanderWhitney K L R S ≫ (chainComplexMap f R ⊗ₘ chainComplexMap g S) := by
  ext n x
  simp only [HomologicalComplex.comp_f, ι_chainComplexMap_f_assoc,
    ιChainComplex_alexanderWhitney_f_assoc, ιChainComplex_alexanderWhitney_f,
    Preadditive.sum_comp, Category.assoc]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp only [tensorHom_eq_mapBifunctorMap, ι_tensorHom, tensorHom_comp_tensorHom_assoc,
    ι_chainComplexMap_f, Monoidal.tensorHom_app, Monoidal.tensorObj_obj, tensorHom_app_apply,
    NatTrans.naturality_apply]

variable {R S} in
/-- The Alexander–Whitney map is natural in both coefficient objects. -/
@[reassoc]
lemma alexanderWhitney_coefficient_naturality {R' S' : C} (f : R ⟶ R') (g : S ⟶ S') :
    ((chainComplexFunctor C).map (f ⊗ₘ g)).app (K ⊗ L) ≫
        alexanderWhitney K L R' S' =
      alexanderWhitney K L R S ≫
        (((chainComplexFunctor C).map f).app K ⊗ₘ
          ((chainComplexFunctor C).map g).app L) := by
  ext n x
  simp only [HomologicalComplex.comp_f]
  rw [← Category.assoc, TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f,
    Category.assoc,
    ιChainComplex_alexanderWhitney_f, ιChainComplex_alexanderWhitney_f_assoc,
    Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [tensorHom_eq_mapBifunctorMap, ← Category.assoc, tensorHom_comp_tensorHom, Category.assoc,
    ι_tensorHom, ← Category.assoc, tensorHom_comp_tensorHom,
    TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f,
    TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f]

end SSet
