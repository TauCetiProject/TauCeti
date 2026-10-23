/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.TensorModels
public import TauCeti.AlgebraicTopology.Singular.Cubical.CrossProduct.Complex
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.CrossProduct

/-!
# The cubical cross product and the simplicial cross product

For a commutative ring `k` and spaces `X` and `Y`, there are two natural chain maps
`N(X; k) ⊗ N(Y; k) ⟶ C(X × Y; k)` from the tensor product of the normalized cubical chains to
the simplicial singular chains of the product:

* the cubical cross product `TauCeti.cubicalCrossProduct` followed by the comparison map
  `TauCeti.cubicalToSingular`;
* the tensor product of two comparison maps followed by the simplicial cross product, the shuffle
  map of Eilenberg and Mac Lane (`TopCat.shuffle`) with the coefficients `k ⊗ k` identified with
  `k` by the unitor (`TauCeti.singularCrossProduct`).

They agree on the augmentation in degree zero, and the singular chains of the product are acyclic on
the models of the tensor product (`TauCeti.cubicalTensorModelPresentation`), so by the method of
acyclic models they are naturally chain homotopic
(`TauCeti.cubicalSingularCrossProductHomotopy`), and equal on homology.

## Main definitions and results

* `TauCeti.cubicalCrossProductToSingular`, `TauCeti.singularCrossProductOfCubical`: the two
  natural chain maps, on pairs of spaces.
* `TauCeti.cubicalSingularCrossProductHomotopy`: the chain homotopy between them, natural in both
  spaces (`TauCeti.cubicalSingularCrossProductHomotopy_hom_naturality`).
* `TauCeti.homologyMap_cubicalCrossProductToSingularApp_eq_singularCrossProductOfCubicalApp`:
  they have the same map on homology.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII, for the cubical
  cross product and the comparison of the cubical and simplicial chains by acyclic models.
* S. Eilenberg and S. Mac Lane, *Acyclic models*, Amer. J. Math. 75 (1953).
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953), for the
  shuffle map.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory HomologicalComplex Limits TensorProduct Simplicial

universe u

namespace TauCeti

variable (k : Type u) [CommRing k]

variable (X Y : TopCat.{u}) in
/-- The cubical cross product followed by the comparison map to simplicial chains. -/
def cubicalCrossProductToSingularApp :
    (normalizedCubicalChainComplex k).obj X ⊗ (normalizedCubicalChainComplex k).obj Y ⟶
      (singularChains k).obj (X ⊗ Y) :=
  cubicalCrossProduct k X Y ≫ (cubicalToSingular k).app (X ⊗ Y)

variable (X Y : TopCat.{u}) in
/-- The tensor product of the two comparison maps followed by the simplicial cross product. -/
def singularCrossProductOfCubicalApp :
    (normalizedCubicalChainComplex k).obj X ⊗ (normalizedCubicalChainComplex k).obj Y ⟶
      (singularChains k).obj (X ⊗ Y) :=
  ((cubicalToSingular k).app X ⊗ₘ (cubicalToSingular k).app Y) ≫ singularCrossProduct k X Y

/-- The cubical cross product followed by the comparison map is a composite. -/
theorem cubicalCrossProductToSingularApp_def (X Y : TopCat.{u}) :
    cubicalCrossProductToSingularApp k X Y =
      cubicalCrossProduct k X Y ≫ (cubicalToSingular k).app (X ⊗ Y) :=
  (rfl)

/-- The tensor product of the comparison maps followed by the simplicial cross product is a
composite. -/
theorem singularCrossProductOfCubicalApp_def (X Y : TopCat.{u}) :
    singularCrossProductOfCubicalApp k X Y =
      ((cubicalToSingular k).app X ⊗ₘ (cubicalToSingular k).app Y) ≫
        singularCrossProduct k X Y :=
  (rfl)

/-- The cubical cross product followed by the comparison map to simplicial chains, as a natural
transformation of functors on pairs of spaces. -/
def cubicalCrossProductToSingular : cubicalTensor k ⟶ singularChainsProduct k where
  app X := cubicalCrossProductToSingularApp k X.1 X.2
  naturality {_ _} f :=
    (cubicalCrossProduct_naturality_assoc (R := k) f.1 f.2 _).trans
      ((congrArg (_ ≫ ·) ((cubicalToSingular k).naturality (f.1 ⊗ₘ f.2))).trans
        (Category.assoc _ _ _).symm)

/-- The component of `cubicalCrossProductToSingular` at a pair of spaces. -/
@[simp]
theorem cubicalCrossProductToSingular_app (X Y : TopCat.{u}) :
    (cubicalCrossProductToSingular k).app (X, Y) = cubicalCrossProductToSingularApp k X Y :=
  (rfl)

/-- The tensor product of the two comparison maps followed by the simplicial cross product, as a
natural transformation of functors on pairs of spaces. -/
def singularCrossProductOfCubical : cubicalTensor k ⟶ singularChainsProduct k where
  app X := singularCrossProductOfCubicalApp k X.1 X.2
  naturality {X Y} f := by
    rw [singularCrossProductOfCubicalApp_def, singularCrossProductOfCubicalApp_def]
    -- `(cubicalTensor k).map f` is `N f.1 ⊗ₘ N f.2` by definition of the functor
    refine (tensorHom_comp_tensorHom_assoc ((normalizedCubicalChainComplex k).map f.1)
      ((normalizedCubicalChainComplex k).map f.2) _ _ _).trans ?_
    rw [(cubicalToSingular k).naturality, (cubicalToSingular k).naturality,
      ← tensorHom_comp_tensorHom_assoc, singularCrossProduct_naturality, Category.assoc]
    rfl

/-- The component of `singularCrossProductOfCubical` at a pair of spaces. -/
@[simp]
theorem singularCrossProductOfCubical_app (X Y : TopCat.{u}) :
    (singularCrossProductOfCubical k).app (X, Y) = singularCrossProductOfCubicalApp k X Y :=
  (rfl)

/-- The augmentation of the image of the generators of degree zero under the cubical cross product
followed by the comparison is `1`. -/
private theorem singularAugment_cubicalCrossProductToSingular_gen (i : BidegreeIndex 0) :
    singularAugment k ((cubicalBidegreeModel.{u} 0 i).1 ⊗ (cubicalBidegreeModel.{u} 0 i).2)
      (((cubicalCrossProductToSingular k).app (cubicalBidegreeModel.{u} 0 i)).f 0
        (cubicalTensorGen k 0 i)) = 1 := by
  obtain rfl := BidegreeIndex.eq_mk_zero_zero i
  refine (singularAugment_cubicalToSingular (k := k) _ _).trans ?_
  rw [cubicalTensorGen_def]
  -- the cross product chain map on the summand `(0, 0)` is the cross product of chains
  have e₀ := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (ι_cubicalCrossProduct_f (R := k) (X := cubeModel.{u} 0) (Y := cubeModel.{u} 0) rfl))
    (NormalizedCubicalChain.ofCube (cubeModel.{u} 0) k (upCube 0) ⊗ₜ[k]
      NormalizedCubicalChain.ofCube (cubeModel.{u} 0) k (upCube 0))
  have e := cubicalCrossProductSummand_apply k (cubeModel.{u} 0) (cubeModel.{u} 0) 0 0 0 rfl
    (NormalizedCubicalChain.ofCube (cubeModel.{u} 0) k (upCube 0))
    (NormalizedCubicalChain.ofCube (cubeModel.{u} 0) k (upCube 0))
  refine (congrArg (cubicalAugment k _) (e₀.trans e)).trans ?_
  rw [NormalizedCubicalChain.crossProduct_ofCube]
  exact (congrArg (cubicalAugment k _) (NormalizedCubicalChain.cast_rfl k _)).trans
    (NormalizedCubicalChain.augment_ofCube k _)

/-- The augmentation of the tensor product of the comparison maps followed by the simplicial
cross product, on the tensor product of two identity `0`-cubes, is `1`. -/
private theorem singularAugment_singularCrossProduct_zeroCube :
    singularAugment k (cubeModel.{u} 0 ⊗ cubeModel.{u} 0)
      ((singularCrossProduct k (cubeModel.{u} 0) (cubeModel.{u} 0)).f 0
        ((HomologicalComplex.tensorHom ((cubicalToSingular k).app (cubeModel.{u} 0))
          ((cubicalToSingular k).app (cubeModel.{u} 0))).f 0
          ((ιTensorObj ((normalizedCubicalChainComplex.{u} k).obj (cubeModel.{u} 0))
            ((normalizedCubicalChainComplex.{u} k).obj (cubeModel.{u} 0)) 0 0 0 rfl).hom
            (NormalizedCubicalChain.ofCube (cubeModel.{u} 0) k (upCube 0) ⊗ₜ[k]
              NormalizedCubicalChain.ofCube (cubeModel.{u} 0) k (upCube 0))))) = 1 := by
  have e := HomologicalComplex.ι_tensorHom_apply ((cubicalToSingular k).app (cubeModel.{u} 0))
    ((cubicalToSingular k).app (cubeModel.{u} 0)) 0 0 0 rfl
    (NormalizedCubicalChain.ofCube (cubeModel.{u} 0) k (upCube 0))
    (NormalizedCubicalChain.ofCube (cubeModel.{u} 0) k (upCube 0))
  have c := cubicalToSingular_app_f_zero_ofZeroCube (k := k) (upCube.{u} 0)
  rw [c] at e
  exact (congrArg (fun z ↦ singularAugment k _ ((singularCrossProduct k _ _).f 0 z)) e).trans
    ((singularAugment_singularCrossProduct k _ _ _ _ 1 1).trans (one_mul 1))

/-- The augmentation of the image of the generators of degree zero under the tensor product of the
comparison maps followed by the simplicial cross product is `1`. -/
private theorem singularAugment_singularCrossProductOfCubical_gen (i : BidegreeIndex 0) :
    singularAugment k ((cubicalBidegreeModel.{u} 0 i).1 ⊗ (cubicalBidegreeModel.{u} 0 i).2)
      (((singularCrossProductOfCubical k).app (cubicalBidegreeModel.{u} 0 i)).f 0
        (cubicalTensorGen k 0 i)) = 1 := by
  obtain rfl := BidegreeIndex.eq_mk_zero_zero i
  rw [cubicalTensorGen_def]
  exact singularAugment_singularCrossProduct_zeroCube k

/-- The two natural chain maps from the tensor product of the cubical chains to the singular chains
of the product agree after augmentation in degree zero. -/
theorem singularAugment_cubicalCrossProductToSingular_eq_singularCrossProductOfCubical
    (X : TopCat.{u} × TopCat.{u})
    (x : ((cubicalTensor k).obj X).X 0) :
    singularAugment k (X.1 ⊗ X.2) (((cubicalCrossProductToSingular k).app X).f 0 x) =
      singularAugment k (X.1 ⊗ X.2) (((singularCrossProductOfCubical k).app X).f 0 x) := by
  exact (cubicalTensorModelPresentation.{u} k).augment_eq_of_gen
    (εG := fun X ↦ singularAugment k (X.1 ⊗ X.2))
    (fun f x ↦ singularAugment_map (f.1 ⊗ₘ f.2) x)
    (cubicalCrossProductToSingular k) (singularCrossProductOfCubical k)
    (fun i ↦ (singularAugment_cubicalCrossProductToSingular_gen k i).trans
      (singularAugment_singularCrossProductOfCubical_gen k i).symm) X x

/-- **The cubical and the simplicial cross product are naturally chain homotopic**: the cubical
cross product followed by the comparison map and the tensor product of the two comparison maps
followed by the simplicial cross product, `N(X; k) ⊗ N(Y; k) ⟶ C(X × Y; k)`, are chain homotopic.
The homotopy is natural in both spaces. -/
def cubicalSingularCrossProductHomotopy (X Y : TopCat.{u}) :
    Homotopy (cubicalCrossProductToSingularApp k X Y) (singularCrossProductOfCubicalApp k X Y) :=
  (cubicalTensorModelPresentation.{u} k).homotopy
    (isAcyclicOnMulti_singularChainsProduct_cubicalTensorModelPresentation k)
    (cubicalCrossProductToSingular k) (singularCrossProductOfCubical k)
    (singularAugment_cubicalCrossProductToSingular_eq_singularCrossProductOfCubical k) (X, Y)

/-- The homotopy between the two cross products is natural in both spaces. -/
theorem cubicalSingularCrossProductHomotopy_hom_naturality {X X' Y Y' : TopCat.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') (i j : ℕ) :
    (HomologicalComplex.tensorHom ((normalizedCubicalChainComplex k).map f)
        ((normalizedCubicalChainComplex k).map g)).f i ≫
        (cubicalSingularCrossProductHomotopy k X' Y').hom i j =
      (cubicalSingularCrossProductHomotopy k X Y).hom i j ≫
        ((singularChains k).map (f ⊗ₘ g)).f j :=
  AcyclicModels.MultiModelPresentation.homotopy_hom_naturality _ _
    (cubicalCrossProductToSingular k) (singularCrossProductOfCubical k)
    (singularAugment_cubicalCrossProductToSingular_eq_singularCrossProductOfCubical k)
    ((f, g) : (X, Y) ⟶ (X', Y')) i j

/-- **The cubical cross product is the simplicial cross product on homology**: the cubical cross
product followed by the comparison map and the tensor product of the two comparison maps followed by
the simplicial cross product induce the same map on homology. -/
theorem homologyMap_cubicalCrossProductToSingularApp_eq_singularCrossProductOfCubicalApp
    (X Y : TopCat.{u}) (n : ℕ) :
    HomologicalComplex.homologyMap (cubicalCrossProductToSingularApp k X Y) n =
      HomologicalComplex.homologyMap (singularCrossProductOfCubicalApp k X Y) n :=
  (cubicalSingularCrossProductHomotopy k X Y).homologyMap_eq n

end TauCeti

end

end
