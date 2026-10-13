/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.TensorModels
public import TauCeti.AlgebraicTopology.Singular.Cubical.CrossProduct.Complex
public import TauCeti.AlgebraicTopology.Singular.Shuffle

/-!
# The cubical cross product and the simplicial cross product

For a commutative ring `k` and spaces `X` and `Y`, there are two natural chain maps
`N(X; k) ⊗ N(Y; k) ⟶ C(X × Y; k)` from the tensor product of the normalized cubical chains to
the simplicial singular chains of the product:

* the cubical cross product `TauCeti.crossProductComplex` followed by the comparison map
  `TauCeti.cubicalToSingular`;
* the tensor product of two comparison maps followed by the simplicial cross product, the shuffle
  map of Eilenberg and Mac Lane (`TopCat.shuffle`) with the coefficients `k ⊗ k` identified with
  `k` by the unitor (`TauCeti.singularCrossProduct`).

They agree on the augmentation in degree zero, and the singular chains of the product are acyclic on
the models of the tensor product (`TauCeti.cubicalTensorModelPresentation`), so by the method of
acyclic models they are naturally chain homotopic
(`TauCeti.crossProductHomotopy`), and equal on homology.

## Main definitions and results

* `TauCeti.singularCrossProduct`: the simplicial cross product `C(X; k) ⊗ C(Y; k) ⟶ C(X × Y; k)`.
* `TauCeti.cubicalCrossProductToSingular`, `TauCeti.singularCrossProductOfCubical`: the two
  natural chain maps, on pairs of spaces.
* `TauCeti.crossProductHomotopy`: the chain homotopy between them, natural in both spaces
  (`TauCeti.crossProductHomotopy_hom_naturality`).
* `TauCeti.homologyMap_cubicalCrossProductToSingular`: they have the same map on homology.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory HomologicalComplex Limits TensorProduct Simplicial

universe u

namespace TauCeti

variable (k : Type u) [CommRing k]

/-- The **simplicial cross product** of singular chains with coefficients in `k`,
`C(X; k) ⊗ C(Y; k) ⟶ C(X × Y; k)`: the shuffle map with the coefficients `k ⊗ k` identified with
`k` by the unitor. -/
def singularCrossProduct (X Y : TopCat.{u}) :
    (singularChains k).obj X ⊗ (singularChains k).obj Y ⟶ (singularChains k).obj (X ⊗ Y) :=
  TopCat.shuffle X Y (𝟙_ (ModuleCat.{u} k)) (𝟙_ (ModuleCat.{u} k)) ≫
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).map
      (λ_ (𝟙_ (ModuleCat.{u} k))).hom).app (X ⊗ Y)

/-- The simplicial cross product is the shuffle map followed by the coefficient change along the
unitor. -/
theorem singularCrossProduct_def (X Y : TopCat.{u}) :
    singularCrossProduct k X Y =
      TopCat.shuffle X Y (𝟙_ (ModuleCat.{u} k)) (𝟙_ (ModuleCat.{u} k)) ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).map
          (λ_ (𝟙_ (ModuleCat.{u} k))).hom).app (X ⊗ Y) :=
  (rfl)

/-- The simplicial cross product is natural in both spaces. -/
theorem singularCrossProduct_naturality {X X' Y Y' : TopCat.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    HomologicalComplex.tensorHom ((singularChains k).map f) ((singularChains k).map g) ≫
        singularCrossProduct k X' Y' =
      singularCrossProduct k X Y ≫ (singularChains k).map (f ⊗ₘ g) := by
  have h1 := TopCat.shuffle_naturality (C := ModuleCat.{u} k) f g (𝟙_ _) (𝟙_ _)
  have h2 := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).map
    (λ_ (𝟙_ (ModuleCat.{u} k))).hom).naturality (f ⊗ₘ g)
  unfold singularCrossProduct
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h1).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm

variable (X Y : TopCat.{u}) in
/-- The cubical cross product followed by the comparison map to simplicial chains. -/
def cubicalCrossProductToSingularApp :
    (normalizedCubicalChainComplex k).obj X ⊗ (normalizedCubicalChainComplex k).obj Y ⟶
      (singularChains k).obj (X ⊗ Y) :=
  crossProductComplex k X Y ≫ (cubicalToSingular k).app (X ⊗ Y)

variable (X Y : TopCat.{u}) in
/-- The tensor product of the two comparison maps followed by the simplicial cross product. -/
def singularCrossProductOfCubicalApp :
    (normalizedCubicalChainComplex k).obj X ⊗ (normalizedCubicalChainComplex k).obj Y ⟶
      (singularChains k).obj (X ⊗ Y) :=
  HomologicalComplex.tensorHom ((cubicalToSingular k).app X) ((cubicalToSingular k).app Y) ≫
    singularCrossProduct k X Y

theorem cubicalCrossProductToSingularApp_def (X Y : TopCat.{u}) :
    cubicalCrossProductToSingularApp k X Y =
      crossProductComplex k X Y ≫ (cubicalToSingular k).app (X ⊗ Y) :=
  (rfl)

theorem singularCrossProductOfCubicalApp_def (X Y : TopCat.{u}) :
    singularCrossProductOfCubicalApp k X Y =
      HomologicalComplex.tensorHom ((cubicalToSingular k).app X) ((cubicalToSingular k).app Y) ≫
        singularCrossProduct k X Y :=
  (rfl)

/-- The cubical cross product followed by the comparison map to simplicial chains, as a natural
transformation of functors on pairs of spaces. -/
def cubicalCrossProductToSingular : cubicalTensor k ⟶ singularChainsProduct k where
  app X := cubicalCrossProductToSingularApp k X.1 X.2
  naturality {X Y} f := by
    have a := crossProductComplex_naturality (R := k) f.1 f.2
    have b := (cubicalToSingular k).naturality (f.1 ⊗ₘ f.2)
    simp only [cubicalCrossProductToSingularApp]
    calc HomologicalComplex.tensorHom ((normalizedCubicalChainComplex k).map f.1)
          ((normalizedCubicalChainComplex k).map f.2) ≫
          (crossProductComplex k Y.1 Y.2 ≫ (cubicalToSingular k).app (Y.1 ⊗ Y.2))
        = (HomologicalComplex.tensorHom ((normalizedCubicalChainComplex k).map f.1)
          ((normalizedCubicalChainComplex k).map f.2) ≫ crossProductComplex k Y.1 Y.2) ≫
          (cubicalToSingular k).app (Y.1 ⊗ Y.2) := (Category.assoc _ _ _).symm
      _ = (crossProductComplex k X.1 X.2 ≫ (normalizedCubicalChainComplex k).map (f.1 ⊗ₘ f.2)) ≫
          (cubicalToSingular k).app (Y.1 ⊗ Y.2) := congrArg (· ≫ _) a
      _ = crossProductComplex k X.1 X.2 ≫ ((normalizedCubicalChainComplex k).map (f.1 ⊗ₘ f.2) ≫
          (cubicalToSingular k).app (Y.1 ⊗ Y.2)) := Category.assoc _ _ _
      _ = crossProductComplex k X.1 X.2 ≫ ((cubicalToSingular k).app (X.1 ⊗ X.2) ≫
          (singularChains k).map (f.1 ⊗ₘ f.2)) := congrArg (_ ≫ ·) b
      _ = _ := (Category.assoc _ _ _).symm

/-- The tensor product of the two comparison maps followed by the simplicial cross product, as a
natural transformation of functors on pairs of spaces. -/
def singularCrossProductOfCubical : cubicalTensor k ⟶ singularChainsProduct k where
  app X := singularCrossProductOfCubicalApp k X.1 X.2
  naturality {X Y} f := by
    have e1 : HomologicalComplex.tensorHom ((normalizedCubicalChainComplex k).map f.1)
          ((normalizedCubicalChainComplex k).map f.2) ≫
        HomologicalComplex.tensorHom ((cubicalToSingular k).app Y.1)
          ((cubicalToSingular k).app Y.2) =
        HomologicalComplex.tensorHom ((cubicalToSingular k).app X.1)
          ((cubicalToSingular k).app X.2) ≫
        HomologicalComplex.tensorHom ((singularChains k).map f.1) ((singularChains k).map f.2) :=
      (tensorHom_comp_tensorHom _ _ _ _).trans
        ((congrArg₂ (fun a b ↦ a ⊗ₘ b) ((cubicalToSingular k).naturality f.1)
          ((cubicalToSingular k).naturality f.2)).trans
        (tensorHom_comp_tensorHom _ _ _ _).symm)
    have e2 := singularCrossProduct_naturality k f.1 f.2
    simp only [singularCrossProductOfCubicalApp]
    calc HomologicalComplex.tensorHom ((normalizedCubicalChainComplex k).map f.1)
          ((normalizedCubicalChainComplex k).map f.2) ≫
          (HomologicalComplex.tensorHom ((cubicalToSingular k).app Y.1)
            ((cubicalToSingular k).app Y.2) ≫ singularCrossProduct k Y.1 Y.2)
        = (HomologicalComplex.tensorHom ((normalizedCubicalChainComplex k).map f.1)
          ((normalizedCubicalChainComplex k).map f.2) ≫
          HomologicalComplex.tensorHom ((cubicalToSingular k).app Y.1)
            ((cubicalToSingular k).app Y.2)) ≫ singularCrossProduct k Y.1 Y.2 :=
          (Category.assoc _ _ _).symm
      _ = (HomologicalComplex.tensorHom ((cubicalToSingular k).app X.1)
          ((cubicalToSingular k).app X.2) ≫
          HomologicalComplex.tensorHom ((singularChains k).map f.1) ((singularChains k).map f.2)) ≫
          singularCrossProduct k Y.1 Y.2 := congrArg (· ≫ _) e1
      _ = HomologicalComplex.tensorHom ((cubicalToSingular k).app X.1)
          ((cubicalToSingular k).app X.2) ≫
          (HomologicalComplex.tensorHom ((singularChains k).map f.1) ((singularChains k).map f.2) ≫
          singularCrossProduct k Y.1 Y.2) := Category.assoc _ _ _
      _ = HomologicalComplex.tensorHom ((cubicalToSingular k).app X.1)
          ((cubicalToSingular k).app X.2) ≫
          (singularCrossProduct k X.1 X.2 ≫ (singularChains k).map (f.1 ⊗ₘ f.2)) :=
          congrArg (_ ≫ ·) e2
      _ = _ := (Category.assoc _ _ _).symm

/-- The simplicial cross product of two chains of single points has augmentation `1`. -/
theorem singularAugment_singularCrossProduct (X Y : TopCat.{u})
    (σ : (TopCat.toSSet.obj X) _⦋0⦌) (τ : (TopCat.toSSet.obj Y) _⦋0⦌) :
    singularAugment k (X ⊗ Y) ((singularCrossProduct k X Y).f 0
      ((ιTensorObj ((singularChains k).obj X) ((singularChains k).obj Y) 0 0 0 rfl).hom
        (simplexChain σ (1 : k) ⊗ₜ[k] simplexChain τ (1 : k)))) = 1 := by
  have h1 := TopCat.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_zero (C := ModuleCat.{u} k)
    (𝟙_ (ModuleCat.{u} k)) (𝟙_ (ModuleCat.{u} k)) σ τ
  have h2 := SSet.ιChainComplex_chainComplexFunctor_map_app_f (C := ModuleCat.{u} k)
    (λ_ (𝟙_ (ModuleCat.{u} k))).hom (X := TopCat.toSSet.obj (X ⊗ Y))
    ((Functor.LaxMonoidal.μ TopCat.toSSet X Y).app _
      ((σ, τ) : (TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y) _⦋0⦌))
  have e1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h1)
    ((1 : k) ⊗ₜ[k] (1 : k))
  have e2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h2)
    ((1 : k) ⊗ₜ[k] (1 : k))
  have e3 : (λ_ (𝟙_ (ModuleCat.{u} k))).hom.hom ((1 : k) ⊗ₜ[k] (1 : k)) = 1 := by simp
  have e4 : (singularCrossProduct k X Y).f 0
      ((ιTensorObj ((singularChains k).obj X) ((singularChains k).obj Y) 0 0 0 rfl).hom
        (simplexChain σ (1 : k) ⊗ₜ[k] simplexChain τ (1 : k))) =
      simplexChain ((Functor.LaxMonoidal.μ TopCat.toSSet X Y).app _
        ((σ, τ) : (TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y) _⦋0⦌)) (1 : k) :=
    (congrArg (fun z ↦ (((AlgebraicTopology.singularChainComplexFunctor
      (ModuleCat.{u} k)).map (λ_ (𝟙_ (ModuleCat.{u} k))).hom).app (X ⊗ Y)).f 0 z) e1).trans
      (e2.trans (congrArg _ e3))
  rw [e4]
  exact singularAugment_simplexChain _ _ _

/-- Every `0`-cube is the constant cube at its value. -/
theorem singularCube_zero_eq_point {X : TopCat.{u}} (c : SingularCube X 0) :
    c = SingularCube.point (c fun i ↦ i.elim0) :=
  ContinuousMap.ext fun t ↦ by
    simp only [SingularCube.point_apply]
    exact congrArg c (Subsingleton.elim _ _)

/-- The comparison map to simplicial chains sends a `0`-cube to the chain of the point. -/
theorem cubicalToSingular_app_f_zero_ofCube' {X : TopCat.{u}} (c : SingularCube X 0) :
    ((cubicalToSingular k).app X).f 0 (NormalizedCubicalChain.ofCube X k c) =
      simplexChain (TopCat.toSSetObj₀Equiv.symm (c fun i ↦ i.elim0)) (1 : k) := by
  have h := cubicalToSingular_app_f_zero_ofCube (k := k) (c fun i ↦ i.elim0)
  rw [← singularCube_zero_eq_point c] at h
  exact h

/-- The tensor product of morphisms of chain complexes on an element of a summand. -/
theorem tensorHom_f_ι_apply {K₁ K₂ L₁ L₂ : ChainComplex (ModuleCat.{u} k) ℕ} (f₁ : K₁ ⟶ L₁)
    (f₂ : K₂ ⟶ L₂) (n p q : ℕ) (h : p + q = n) (a : K₁.X p) (b : K₂.X q) :
    (HomologicalComplex.tensorHom f₁ f₂).f n ((ιTensorObj K₁ K₂ p q n h).hom (a ⊗ₜ[k] b)) =
      (ιTensorObj L₁ L₂ p q n h).hom (f₁.f p a ⊗ₜ[k] f₂.f q b) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (HomologicalComplex.ι_tensorHom f₁ f₂ p q n h))
    (a ⊗ₜ[k] b)

/-- The augmentation of the image of the generators of degree zero under the cubical cross product
followed by the comparison is `1`. -/
theorem singularAugment_cubicalCrossProductToSingular_gen (i : BidegreeIndex 0) :
    singularAugment k ((bidegreeModel.{u} 0 i).1 ⊗ (bidegreeModel.{u} 0 i).2)
      (((cubicalCrossProductToSingular k).app (bidegreeModel.{u} 0 i)).f 0
        (tensorGen k 0 i)) = 1 := by
  obtain ⟨⟨p, q⟩, h⟩ := i
  obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by
    have h' : p + q = 0 := h
    omega
  refine (singularAugment_cubicalToSingular (k := k) _ _).trans ?_
  rw [tensorGen_def]
  have e := ι_crossProductComplex_f_apply (R := k) (X := cubeModel.{u} 0) (Y := cubeModel.{u} 0) h
    (NormalizedCubicalChain.ofCube (cubeModel.{u} 0) k (upCube 0))
    (NormalizedCubicalChain.ofCube (cubeModel.{u} 0) k (upCube 0))
  refine (congrArg (cubicalAugment k _) e).trans ?_
  rw [NormalizedCubicalChain.crossProduct_ofCube]
  exact (congrArg (cubicalAugment k _) (NormalizedCubicalChain.cast_rfl k _)).trans
    (NormalizedCubicalChain.augment_ofCube k _)

/-- The augmentation of the tensor product of the comparison maps followed by the simplicial
cross product, on the tensor product of two identity `0`-cubes, is `1`. -/
theorem singularAugment_singularCrossProduct_zeroCube :
    singularAugment k (cubeModel.{u} 0 ⊗ cubeModel.{u} 0)
      ((singularCrossProduct k (cubeModel.{u} 0) (cubeModel.{u} 0)).f 0
        ((HomologicalComplex.tensorHom ((cubicalToSingular k).app (cubeModel.{u} 0))
          ((cubicalToSingular k).app (cubeModel.{u} 0))).f 0
          ((ιTensorObj ((normalizedCubicalChainComplex.{u} k).obj (cubeModel.{u} 0))
            ((normalizedCubicalChainComplex.{u} k).obj (cubeModel.{u} 0)) 0 0 0 rfl).hom
            (NormalizedCubicalChain.ofCube (cubeModel.{u} 0) k (upCube 0) ⊗ₜ[k]
              NormalizedCubicalChain.ofCube (cubeModel.{u} 0) k (upCube 0))))) = 1 := by
  have e := tensorHom_f_ι_apply (k := k) ((cubicalToSingular k).app (cubeModel.{u} 0))
    ((cubicalToSingular k).app (cubeModel.{u} 0)) 0 0 0 rfl
    (NormalizedCubicalChain.ofCube (cubeModel.{u} 0) k (upCube 0))
    (NormalizedCubicalChain.ofCube (cubeModel.{u} 0) k (upCube 0))
  have c := cubicalToSingular_app_f_zero_ofCube' (k := k) (upCube.{u} 0)
  rw [c] at e
  exact (congrArg (fun z ↦ singularAugment k _ ((singularCrossProduct k _ _).f 0 z)) e).trans
    (singularAugment_singularCrossProduct k _ _ _ _)

/-- The augmentation of the image of the generators of degree zero under the tensor product of the
comparison maps followed by the simplicial cross product is `1`. -/
theorem singularAugment_singularCrossProductOfCubical_gen (i : BidegreeIndex 0) :
    singularAugment k ((bidegreeModel.{u} 0 i).1 ⊗ (bidegreeModel.{u} 0 i).2)
      (((singularCrossProductOfCubical k).app (bidegreeModel.{u} 0 i)).f 0
        (tensorGen k 0 i)) = 1 := by
  obtain ⟨⟨p, q⟩, h⟩ := i
  obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by
    have h' : p + q = 0 := h
    omega
  rw [tensorGen_def]
  exact singularAugment_singularCrossProduct_zeroCube k

/-- The two natural chain maps from the tensor product of the cubical chains to the singular chains
of the product agree after augmentation in degree zero. -/
theorem singularAugment_cubicalCrossProductToSingular_eq (X : TopCat.{u} × TopCat.{u})
    (x : ((cubicalTensor k).obj X).X 0) :
    singularAugment k (X.1 ⊗ X.2) (((cubicalCrossProductToSingular k).app X).f 0 x) =
      singularAugment k (X.1 ⊗ X.2) (((singularCrossProductOfCubical k).app X).f 0 x) := by
  let B := cubicalTensorModelPresentation.{u} k
  conv_lhs => rw [← B.sum_coord X 0 x]
  conv_rhs => rw [← B.sum_coord X 0 x]
  rw [map_finsuppSum, map_finsuppSum, map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun s _ ↦ ?_
  rw [map_smul, map_smul, map_smul, map_smul]
  refine congrArg (_ • ·) ?_
  have n₁ := (AcyclicModels.NatLinear.ofHom (cubicalCrossProductToSingular k) 0).naturality s.2
    (B.gen 0 s.1)
  have n₂ := (AcyclicModels.NatLinear.ofHom (singularCrossProductOfCubical k) 0).naturality s.2
    (B.gen 0 s.1)
  simp only [AcyclicModels.NatLinear.ofHom_app] at n₁ n₂
  rw [n₁, n₂]
  refine Eq.trans (singularAugment_map (k := k) (s.2.1 ⊗ₘ s.2.2) _) ?_
  refine Eq.trans ?_ (singularAugment_map (k := k) (s.2.1 ⊗ₘ s.2.2) _).symm
  exact (singularAugment_cubicalCrossProductToSingular_gen k s.1).trans
    (singularAugment_singularCrossProductOfCubical_gen k s.1).symm

/-- **The cubical and the simplicial cross product are naturally chain homotopic**: the cubical
cross product followed by the comparison map and the tensor product of the two comparison maps
followed by the simplicial cross product, `N(X; k) ⊗ N(Y; k) ⟶ C(X × Y; k)`, are chain homotopic.
The homotopy is natural in both spaces. -/
def crossProductHomotopy (X Y : TopCat.{u}) :
    Homotopy (cubicalCrossProductToSingularApp k X Y) (singularCrossProductOfCubicalApp k X Y) :=
  (cubicalTensorModelPresentation.{u} k).homotopy (isAcyclicOnMulti_singularChainsProduct k)
    (cubicalCrossProductToSingular k) (singularCrossProductOfCubical k)
    (singularAugment_cubicalCrossProductToSingular_eq k) (X, Y)

/-- The homotopy between the two cross products is natural in both spaces. -/
theorem crossProductHomotopy_hom_naturality {X X' Y Y' : TopCat.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (i j : ℕ) :
    (HomologicalComplex.tensorHom ((normalizedCubicalChainComplex k).map f)
        ((normalizedCubicalChainComplex k).map g)).f i ≫ (crossProductHomotopy k X' Y').hom i j =
      (crossProductHomotopy k X Y).hom i j ≫ ((singularChains k).map (f ⊗ₘ g)).f j :=
  AcyclicModels.MultiModelPresentation.homotopy_hom_naturality _ _
    (cubicalCrossProductToSingular k) (singularCrossProductOfCubical k)
    (singularAugment_cubicalCrossProductToSingular_eq k) ((f, g) : (X, Y) ⟶ (X', Y')) i j

/-- **The cubical cross product is the simplicial cross product on homology**: the cubical cross
product followed by the comparison map and the tensor product of the two comparison maps followed by
the simplicial cross product induce the same map on homology. -/
theorem homologyMap_cubicalCrossProductToSingular (X Y : TopCat.{u}) (n : ℕ) :
    HomologicalComplex.homologyMap (cubicalCrossProductToSingularApp k X Y) n =
      HomologicalComplex.homologyMap (singularCrossProductOfCubicalApp k X Y) n :=
  (crossProductHomotopy k X Y).homologyMap_eq n

end TauCeti

end

end
