/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Models

/-!
# The comparison of cubical and simplicial singular chains

The normalized cubical chains and the simplicial singular chains of a topological space are
naturally chain homotopy equivalent (`TauCeti.cubicalSingularHomotopyEquiv`).  Both comparison
maps and both homotopies come from the method of acyclic models
(`TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.AcyclicModels`): each functor is free on
models, the topological simplices for the simplicial chains and the cubes for the cubical ones,
and each is acyclic on every contractible space
(`TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Models`).  In degree zero the comparison
maps send a point to the same point, so they are compatible with the augmentations.

This is the comparison through which the consequences of the simplicial theory (homotopy
invariance, the long exact sequence of a pair, excision) are transported to cubical chains.

## Main definitions

* `TauCeti.singularToCubical k`: the natural chain map from simplicial to normalized cubical
  singular chains.
* `TauCeti.cubicalToSingular k`: the natural chain map back.
* `TauCeti.cubicalSingularHomotopyEquiv k X`: the chain homotopy equivalence they form.

## Main results

* `TauCeti.cubicalAugment_singularToCubical` and `TauCeti.singularAugment_cubicalToSingular`: the
  comparison maps are compatible with the augmentations.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* S. Eilenberg and S. Mac Lane, *Acyclic models*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Finsupp Simplicial

universe u

namespace TauCeti

variable {k : Type u} [Ring k]

/-! ### Properties of the augmentations -/

/-- The augmentation of the simplicial singular chains is natural. -/
theorem singularAugment_map {X Y : TopCat.{u}} (f : X ⟶ Y) (x : ((singularChains k).obj X).X 0) :
    singularAugment k Y (((singularChains k).map f).f 0 x) = singularAugment k X x := by
  have := singularChains_linearMap_ext
    (L := singularAugment k Y ∘ₗ (((singularChains k).map f).f 0).hom)
    (L' := singularAugment k X) fun σ ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, singularChains_map_f_simplexChain,
        singularAugment_simplexChain]
  exact LinearMap.congr_fun this x

/-- The boundary of a singular simplex is the alternating sum of its faces. -/
theorem singularChains_d_simplexChain {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    ((singularChains k).obj X).d (n + 1) n (simplexChain σ 1) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • simplexChain ((TopCat.toSSet.obj X).δ i σ) 1 := by
  have h := congrArg (fun g ↦ g.hom (1 : k))
    (SSet.ιChainComplex_d (R := ModuleCat.of k k) (TopCat.toSSet.obj X) (n := n) σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply] at h
  exact h

/-- The augmentation of the simplicial singular chains vanishes on boundaries. -/
theorem singularAugment_d (X : TopCat.{u}) (x : ((singularChains k).obj X).X 1) :
    singularAugment k X (((singularChains k).obj X).d 1 0 x) = 0 := by
  have := singularChains_linearMap_ext
    (L := singularAugment k X ∘ₗ (((singularChains k).obj X).d 1 0).hom) (L' := 0) fun σ ↦ by
      rw [LinearMap.comp_apply, singularChains_d_simplexChain, map_sum]
      simp [Fin.sum_univ_succ, singularAugment_simplexChain]
  exact LinearMap.congr_fun this x

/-- The augmentation of the normalized cubical chains is natural. -/
theorem cubicalAugment_map {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : ((normalizedCubicalChainComplex k).obj X).X 0) :
    cubicalAugment k Y (((normalizedCubicalChainComplex k).map f).f 0 x) = cubicalAugment k X x :=
  LinearMap.congr_fun (NormalizedCubicalChain.augment_map k f.hom) x

/-- The augmentation of the normalized cubical chains vanishes on boundaries. -/
theorem cubicalAugment_d (X : TopCat.{u}) (x : ((normalizedCubicalChainComplex k).obj X).X 1) :
    cubicalAugment k X (((normalizedCubicalChainComplex k).obj X).d 1 0 x) = 0 :=
  (congrArg (cubicalAugment k X) (normalizedCubicalChainComplex_obj_d_apply X 0 x)).trans
    (LinearMap.congr_fun (NormalizedCubicalChain.augment_boundary k) x)

/-! ### The comparison maps -/

variable (k)

/-- The point of the `0`-cube. -/
def cubeModelPoint : cubeModel.{u} 0 := ULift.up fun i ↦ i.elim0

/-- The `0`-simplex at the point of the `0`-cube: the value on the model of the comparison map
from cubical to simplicial chains in degree zero. -/
def cubicalToSingularGen₀ : ((singularChains k).obj (cubeModel.{u} 0)).X 0 :=
  simplexChain (TopCat.toSSetObj₀Equiv.symm cubeModelPoint) 1

/-- The `0`-cube at the vertex of the `0`-simplex: the value on the model of the comparison map
from simplicial to cubical chains in degree zero. -/
def singularToCubicalGen₀ : ((normalizedCubicalChainComplex k).obj (simplexModel.{u} 0)).X 0 :=
  NormalizedCubicalChain.ofCube (simplexModel 0) k
    (SingularCube.point (SimplexCategory.toTopInitialVertex ⦋0⦌))

theorem singularAugment_extend_cubicalToSingularGen₀ (X : TopCat.{u})
    (x : ((normalizedCubicalChainComplex k).obj X).X 0) :
    singularAugment k X ((cubicalModelBasis k).extend (cubicalToSingularGen₀ k) X x) =
      cubicalAugment k X x :=
  (cubicalModelBasis k).augment_extend (fun f x ↦ cubicalAugment_map f x)
    (fun f x ↦ singularAugment_map f x) _
    ((singularAugment_simplexChain _ _ 1).trans (NormalizedCubicalChain.augment_ofCube k _).symm)
    X x

theorem cubicalAugment_extend_singularToCubicalGen₀ (X : TopCat.{u})
    (x : ((singularChains k).obj X).X 0) :
    cubicalAugment k X ((singularModelBasis k).extend (singularToCubicalGen₀ k) X x) =
      singularAugment k X x :=
  (singularModelBasis k).augment_extend (fun f x ↦ singularAugment_map f x)
    (fun f x ↦ cubicalAugment_map f x) _
    ((NormalizedCubicalChain.augment_ofCube k _).trans (singularAugment_simplexChain _ _ 1).symm)
    X x

/-- **The comparison map from normalized cubical to simplicial singular chains**: the natural
chain map sending a point to the same point, built by acyclic models. -/
def cubicalToSingular : normalizedCubicalChainComplex.{u} k ⟶ singularChains k :=
  (cubicalModelBasis k).chainMap (isAcyclicOn_singularChains cubeModel)
    (fun X x ↦ cubicalAugment_d X x) (cubicalToSingularGen₀ k)
    (singularAugment_extend_cubicalToSingularGen₀ k)

/-- **The comparison map from simplicial singular to normalized cubical chains**: the natural
chain map sending a point to the same point, built by acyclic models. -/
def singularToCubical : singularChains k ⟶ normalizedCubicalChainComplex.{u} k :=
  (singularModelBasis k).chainMap (isAcyclicOn_normalizedCubicalChainComplex simplexModel)
    (fun X x ↦ singularAugment_d X x) (singularToCubicalGen₀ k)
    (cubicalAugment_extend_singularToCubicalGen₀ k)

variable {k}

/-- The comparison map to simplicial chains is compatible with the augmentations. -/
theorem singularAugment_cubicalToSingular (X : TopCat.{u})
    (x : ((normalizedCubicalChainComplex k).obj X).X 0) :
    singularAugment k X (((cubicalToSingular k).app X).f 0 x) = cubicalAugment k X x := by
  exact singularAugment_extend_cubicalToSingularGen₀ k X x

/-- The comparison map to cubical chains is compatible with the augmentations. -/
theorem cubicalAugment_singularToCubical (X : TopCat.{u}) (x : ((singularChains k).obj X).X 0) :
    cubicalAugment k X (((singularToCubical k).app X).f 0 x) = singularAugment k X x := by
  exact cubicalAugment_extend_singularToCubicalGen₀ k X x

variable (k)

/-- The composite of the comparison maps on simplicial chains is homotopic to the identity. -/
def singularToCubicalCompHomotopy (X : TopCat.{u}) :
    Homotopy ((singularToCubical k).app X ≫ (cubicalToSingular k).app X) (𝟙 _) :=
  (singularModelBasis k).homotopy (isAcyclicOn_singularChains simplexModel)
    (singularToCubical k ≫ cubicalToSingular k) (𝟙 _) (fun X x ↦ by
      simp only [NatTrans.comp_app, HomologicalComplex.comp_f, ModuleCat.comp_apply,
        NatTrans.id_app, HomologicalComplex.id_f, ModuleCat.id_apply]
      rw [singularAugment_cubicalToSingular, cubicalAugment_singularToCubical]) X

/-- The composite of the comparison maps on cubical chains is homotopic to the identity. -/
def cubicalToSingularCompHomotopy (X : TopCat.{u}) :
    Homotopy ((cubicalToSingular k).app X ≫ (singularToCubical k).app X) (𝟙 _) :=
  (cubicalModelBasis k).homotopy (isAcyclicOn_normalizedCubicalChainComplex cubeModel)
    (cubicalToSingular k ≫ singularToCubical k) (𝟙 _) (fun X x ↦ by
      simp only [NatTrans.comp_app, HomologicalComplex.comp_f, ModuleCat.comp_apply,
        NatTrans.id_app, HomologicalComplex.id_f, ModuleCat.id_apply]
      rw [cubicalAugment_singularToCubical, singularAugment_cubicalToSingular]) X

/-- **Cubical and simplicial singular chains are naturally chain homotopy equivalent.** -/
def cubicalSingularHomotopyEquiv (X : TopCat.{u}) :
    HomotopyEquiv ((singularChains k).obj X) ((normalizedCubicalChainComplex k).obj X) where
  hom := (singularToCubical k).app X
  inv := (cubicalToSingular k).app X
  homotopyHomInvId := singularToCubicalCompHomotopy k X
  homotopyInvHomId := cubicalToSingularCompHomotopy k X

@[simp]
theorem cubicalSingularHomotopyEquiv_hom (X : TopCat.{u}) :
    (cubicalSingularHomotopyEquiv k X).hom = (singularToCubical k).app X :=
  (rfl)

@[simp]
theorem cubicalSingularHomotopyEquiv_inv (X : TopCat.{u}) :
    (cubicalSingularHomotopyEquiv k X).inv = (cubicalToSingular k).app X :=
  (rfl)

end TauCeti
