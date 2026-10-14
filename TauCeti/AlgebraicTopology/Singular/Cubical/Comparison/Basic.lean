/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Models

/-!
# The comparison of cubical and simplicial singular chains

The normalized cubical chains and the simplicial singular chains of a topological space are
naturally chain homotopy equivalent (`TauCeti.cubicalSingularHomotopyEquiv`).  Both comparison
maps and both homotopies come from the method of acyclic models
(`TauCeti.Algebra.Homology.AcyclicModels`): each functor is free on
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
* `TauCeti.singularCubicalHomologyIso k X n`, `TauCeti.singularCubicalHomologyNatIso k n`: cubical
  singular homology is naturally isomorphic to singular homology.

## Main results

* `TauCeti.cubicalAugment_singularToCubical` and `TauCeti.singularAugment_cubicalToSingular`: the
  comparison maps are compatible with the augmentations.
* `TauCeti.singularToCubical_app_f_zero_simplexChain` and
  `TauCeti.cubicalToSingular_app_f_zero_ofCube`: in degree zero the comparison maps send a point
  to the same point.

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

/-! ### The comparison maps -/

variable (k)

/-- **The comparison map from normalized cubical to simplicial singular chains**: the natural
chain map sending a point to the same point, built by acyclic models. -/
def cubicalToSingular : normalizedCubicalChainComplex.{u} k ⟶ singularChains k :=
  (cubicalModelPresentation k).chainMap (isAcyclicOn_singularChains_cubicalModelPresentation k)
    (fun X x ↦ cubicalAugment_d X x) (cubicalToSingularGen₀ k)
    (singularAugment_extend_cubicalToSingularGen₀ k)

/-- **The comparison map from simplicial singular to normalized cubical chains**: the natural
chain map sending a point to the same point, built by acyclic models. -/
def singularToCubical : singularChains k ⟶ normalizedCubicalChainComplex.{u} k :=
  (singularModelPresentation k).chainMap
    (isAcyclicOn_normalizedCubicalChainComplex_singularModelPresentation k)
    (fun X x ↦ singularAugment_d X x) (singularToCubicalGen₀ k)
    (cubicalAugment_extend_singularToCubicalGen₀ k)

variable {k}

/-- The comparison map to simplicial chains is compatible with the augmentations. -/
theorem singularAugment_cubicalToSingular (X : TopCat.{u})
    (x : ((normalizedCubicalChainComplex k).obj X).X 0) :
    singularAugment k X (((cubicalToSingular k).app X).f 0 x) = cubicalAugment k X x := by
  rw [cubicalToSingular, AcyclicModels.ModelPresentation.chainMap_app_f_zero_apply]
  exact singularAugment_extend_cubicalToSingularGen₀ k X x

/-- The comparison map to cubical chains is compatible with the augmentations. -/
theorem cubicalAugment_singularToCubical (X : TopCat.{u}) (x : ((singularChains k).obj X).X 0) :
    cubicalAugment k X (((singularToCubical k).app X).f 0 x) = singularAugment k X x := by
  rw [singularToCubical, AcyclicModels.ModelPresentation.chainMap_app_f_zero_apply]
  exact cubicalAugment_extend_singularToCubicalGen₀ k X x

variable (k)

/-- The composite of the comparison maps on simplicial chains is homotopic to the identity. -/
def singularToCubicalCompHomotopy (X : TopCat.{u}) :
    Homotopy ((singularToCubical k).app X ≫ (cubicalToSingular k).app X) (𝟙 _) :=
  (singularModelPresentation k).homotopy (isAcyclicOn_singularChains_singularModelPresentation k)
    (singularToCubical k ≫ cubicalToSingular k) (𝟙 _) (fun X x ↦ by
      simp only [NatTrans.comp_app, HomologicalComplex.comp_f, ModuleCat.comp_apply,
        NatTrans.id_app, HomologicalComplex.id_f, ModuleCat.id_apply]
      rw [singularAugment_cubicalToSingular, cubicalAugment_singularToCubical]) X

/-- The composite of the comparison maps on cubical chains is homotopic to the identity. -/
def cubicalToSingularCompHomotopy (X : TopCat.{u}) :
    Homotopy ((cubicalToSingular k).app X ≫ (singularToCubical k).app X) (𝟙 _) :=
  (cubicalModelPresentation k).homotopy
    (isAcyclicOn_normalizedCubicalChainComplex_cubicalModelPresentation k)
    (cubicalToSingular k ≫ singularToCubical k) (𝟙 _) (fun X x ↦ by
      simp only [NatTrans.comp_app, HomologicalComplex.comp_f, ModuleCat.comp_apply,
        NatTrans.id_app, HomologicalComplex.id_f, ModuleCat.id_apply]
      rw [cubicalAugment_singularToCubical, singularAugment_cubicalToSingular]) X

/-- The homotopy `singularToCubicalCompHomotopy` is natural. -/
theorem singularToCubicalCompHomotopy_hom_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (i j : ℕ) :
    ((singularChains k).map f).f i ≫ (singularToCubicalCompHomotopy k Y).hom i j =
      (singularToCubicalCompHomotopy k X).hom i j ≫ ((singularChains k).map f).f j :=
  AcyclicModels.ModelPresentation.homotopy_hom_naturality _ _ _ _ _ f i j

/-- The homotopy `cubicalToSingularCompHomotopy` is natural. -/
theorem cubicalToSingularCompHomotopy_hom_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (i j : ℕ) :
    ((normalizedCubicalChainComplex k).map f).f i ≫ (cubicalToSingularCompHomotopy k Y).hom i j =
      (cubicalToSingularCompHomotopy k X).hom i j ≫
        ((normalizedCubicalChainComplex k).map f).f j :=
  AcyclicModels.ModelPresentation.homotopy_hom_naturality _ _ _ _ _ f i j

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

variable {k}

/-! ### The comparison maps in degree zero -/

/-- **The comparison map to cubical chains sends a point to the point cube.** -/
theorem singularToCubical_app_f_zero_simplexChain {X : TopCat.{u}}
    (σ : (TopCat.toSSet.obj X) _⦋0⦌) :
    ((singularToCubical k).app X).f 0 (simplexChain σ 1) =
      NormalizedCubicalChain.ofCube X k (SingularCube.point (TopCat.toSSetObj₀Equiv σ)) := by
  refine (AcyclicModels.ModelPresentation.chainMap_app_f_zero_apply _ _ _ _ _ X _).trans ?_
  refine (singularModelPresentation_extend_simplexChain
    (G := normalizedCubicalChainComplex k) (singularToCubicalGen₀ k) σ).trans ?_
  rw [singularToCubicalGen₀_eq]
  refine (normalizedCubicalChainComplex_map_f_apply σ.down 0 _).trans ?_
  refine (NormalizedCubicalChain.map_ofCube k σ.down.hom _).trans ?_
  exact congrArg _ (ContinuousMap.ext fun t ↦ by
    simp only [ContinuousMap.comp_apply, SingularCube.point_apply]
    exact (congrArg σ.down.hom
      (Subsingleton.elim (α := SimplexCategory.toTop.{u}.obj ⦋0⦌) _ default)).trans rfl)

/-- **The comparison map to simplicial chains sends a point cube to the point.** -/
theorem cubicalToSingular_app_f_zero_ofCube {X : TopCat.{u}} (x : X) :
    ((cubicalToSingular k).app X).f 0
        (NormalizedCubicalChain.ofCube X k (SingularCube.point x)) =
      simplexChain (TopCat.toSSetObj₀Equiv.symm x) 1 := by
  refine (AcyclicModels.ModelPresentation.chainMap_app_f_zero_apply _ _ _ _ _ X _).trans ?_
  refine (cubicalModelPresentation_extend_ofCube_zero (G := singularChains k)
    (cubicalToSingularGen₀ k) _).trans ?_
  rw [cubicalToSingularGen₀_eq]
  refine (singularChains_map_f_simplexChain (k := k) _ _ 1).trans ?_
  refine congrArg (simplexChain · 1) ((TopCat.toSSet_map_app_toSSetObj₀Equiv_symm
    (cubeToHom (SingularCube.point x)) (cubeModelPoint.{u})).trans ?_)
  exact congrArg _ ((cubeToHom_apply _ _).trans (SingularCube.point_apply _ _))

/-- The comparison map to simplicial chains sends any `0`-cube to the chain of its point. -/
theorem cubicalToSingular_app_f_zero_ofZeroCube {X : TopCat.{u}} (c : SingularCube X 0) :
    ((cubicalToSingular k).app X).f 0 (NormalizedCubicalChain.ofCube X k c) =
      simplexChain (TopCat.toSSetObj₀Equiv.symm (c fun i ↦ i.elim0)) (1 : k) := by
  have h := cubicalToSingular_app_f_zero_ofCube (k := k) (c fun i ↦ i.elim0)
  rw [← SingularCube.eq_point c] at h
  exact h

/-! ### Quasi-isomorphisms and the homology comparison -/

/-- The comparison map to cubical chains is a quasi-isomorphism. -/
instance (X : TopCat.{u}) : QuasiIso ((singularToCubical k).app X) := by
  rw [← cubicalSingularHomotopyEquiv_hom]
  infer_instance

/-- The comparison map to simplicial chains is a quasi-isomorphism. -/
instance (X : TopCat.{u}) : QuasiIso ((cubicalToSingular k).app X) := by
  rw [← cubicalSingularHomotopyEquiv_inv]
  infer_instance

variable (k) in
/-- **Cubical singular homology is singular homology**: the isomorphism induced by the comparison
of cubical and simplicial chains. -/
def singularCubicalHomologyIso (X : TopCat.{u}) (n : ℕ) :
    ((singularChains k).obj X).homology n ≅ ((normalizedCubicalChainComplex k).obj X).homology n :=
  (cubicalSingularHomotopyEquiv k X).toHomologyIso n

@[simp]
theorem singularCubicalHomologyIso_hom (X : TopCat.{u}) (n : ℕ) :
    (singularCubicalHomologyIso k X n).hom =
      HomologicalComplex.homologyMap ((singularToCubical k).app X) n := by
  rw [← cubicalSingularHomotopyEquiv_hom]
  rfl

@[simp]
theorem singularCubicalHomologyIso_inv (X : TopCat.{u}) (n : ℕ) :
    (singularCubicalHomologyIso k X n).inv =
      HomologicalComplex.homologyMap ((cubicalToSingular k).app X) n := by
  rw [← cubicalSingularHomotopyEquiv_inv]
  rfl

/-- The comparison isomorphism on homology is natural. -/
@[reassoc]
theorem singularCubicalHomologyIso_hom_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap ((singularChains k).map f) n ≫
        (singularCubicalHomologyIso k Y n).hom =
      (singularCubicalHomologyIso k X n).hom ≫
        HomologicalComplex.homologyMap ((normalizedCubicalChainComplex k).map f) n := by
  simp only [singularCubicalHomologyIso_hom, ← HomologicalComplex.homologyMap_comp,
    (singularToCubical k).naturality]

variable (k) in
/-- **Cubical singular homology is naturally isomorphic to singular homology**, as functors on
topological spaces. -/
def singularCubicalHomologyNatIso (n : ℕ) :
    singularChains k ⋙ HomologicalComplex.homologyFunctor _ _ n ≅
      normalizedCubicalChainComplex k ⋙ HomologicalComplex.homologyFunctor _ _ n :=
  NatIso.ofComponents (fun X ↦ singularCubicalHomologyIso k X n)
    fun f ↦ singularCubicalHomologyIso_hom_naturality f n

@[simp]
theorem singularCubicalHomologyNatIso_app (n : ℕ) (X : TopCat.{u}) :
    (singularCubicalHomologyNatIso k n).app X = singularCubicalHomologyIso k X n :=
  (rfl)

end TauCeti
