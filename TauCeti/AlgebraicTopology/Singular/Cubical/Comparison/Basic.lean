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
* `TauCeti.cubicalToSingularGen k n`, `TauCeti.singularToCubicalGen k n`: the images of the
  identity cube of the model `Iⁿ` and of the identity simplex of the model `Δⁿ` under the
  comparison maps.
* `TauCeti.singularCubicalHomologyIso k X n`, `TauCeti.singularCubicalHomologyNatIso k n`: cubical
  singular homology is naturally isomorphic to singular homology.

## Main results

* `TauCeti.singularToCubical_app_f_simplexChain` and `TauCeti.cubicalToSingular_app_f_ofCube`: the
  comparison maps send a simplex, respectively a cube, to the image of the model generator under
  it, regarded as a map from the model.
* `TauCeti.singularToCubicalCompHomotopy_hom_simplexChain` and
  `TauCeti.cubicalToSingularCompHomotopy_hom_ofCube`: the natural homotopies, on a simplex or a
  cube, are the images of their values on the model generators.
* `TauCeti.cubicalAugment_singularToCubical` and `TauCeti.singularAugment_cubicalToSingular`: the
  comparison maps are compatible with the augmentations.
* `TauCeti.singularToCubical_app_f_zero_simplexChain` and
  `TauCeti.cubicalToSingular_app_f_zero_ofCube`: in degree zero the comparison maps send a point
  to the same point.
* `TauCeti.cubicalToSingularGen_zero` and `TauCeti.singularToCubicalGen_zero`: in degree zero the
  model generators are the point simplex and the point cube.
* `TauCeti.TopCat.isIso_singularHomologyMap_of_quasiIso`: a map inducing a quasi-isomorphism of
  normalized cubical chains induces isomorphisms on singular homology.

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

/-- The comparison with simplicial chains is natural: pushing forward the image of a cube is the
image of the pushed-forward cube. -/
theorem singularChains_map_cubicalToSingular {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ}
    (c : SingularCube X n) :
    ((singularChains k).map f).f n
        (((cubicalToSingular k).app X).f n
          (NormalizedCubicalChain.ofCube X k c)) =
      ((cubicalToSingular k).app Y).f n
        (NormalizedCubicalChain.ofCube Y k (f.hom.comp c)) := by
  have h := congrArg (fun φ ↦ φ.f n (NormalizedCubicalChain.ofCube X k c))
    ((cubicalToSingular k).naturality f)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp] at h
  -- The term `((normalizedCubicalChainComplex k).obj X).X n` is the module of normalized chains by
  -- definition, which `exact` sees but `rw` does not.
  exact h.symm.trans (congrArg (((cubicalToSingular k).app Y).f n).hom
    ((normalizedCubicalChainComplex_map_f_apply f n _).trans
      (NormalizedCubicalChain.map_ofCube _ f.hom c)))

section ModelChains

variable (k)

/-- The image, under the comparison with simplicial chains, of the identity cube of the model
`Iⁿ`. -/
def cubicalToSingularGen (n : ℕ) : ((singularChains k).obj (cubeModel.{u} n)).X n :=
  ((cubicalToSingular k).app (cubeModel.{u} n)).f n
    (NormalizedCubicalChain.ofCube (cubeModel.{u} n) k (upCube n))

/-- The image, under the comparison with simplicial chains, of the subcube `upCube n ∘ ι` of the
model `Iⁿ`. -/
def cubicalToSingularSubcube (n : ℕ) {m : ℕ} (ι : C(Fin m → unitInterval, Fin n → unitInterval)) :
    ((singularChains k).obj (cubeModel.{u} n)).X m :=
  ((cubicalToSingular k).app (cubeModel.{u} n)).f m
    (NormalizedCubicalChain.ofCube (cubeModel.{u} n) k ((upCube n).comp ι))

/-- The comparison with simplicial chains sends a cube to the image of the model generator under
the cube, regarded as a map from the model. -/
theorem cubicalToSingular_app_f_ofCube {X : TopCat.{u}} {n : ℕ} (c : SingularCube X n) :
    ((cubicalToSingular k).app X).f n (NormalizedCubicalChain.ofCube X k c) =
      ((singularChains k).map (cubeToHom c)).f n (cubicalToSingularGen k n) := by
  have h := singularChains_map_cubicalToSingular (k := k) (cubeToHom c) (upCube n)
  rw [cubeToHom_hom_comp_upCube] at h
  exact h.symm

/-- In degree zero, the model generator of the comparison to simplicial chains is the `0`-simplex
at the unique point of the `0`-cube. -/
@[simp]
theorem cubicalToSingularGen_zero :
    cubicalToSingularGen k 0 =
      simplexChain (TopCat.toSSetObj₀Equiv.symm ((upCube.{u} 0) fun i ↦ i.elim0)) 1 :=
  cubicalToSingular_app_f_zero_ofZeroCube (upCube 0)

/-- The image of the identity cube is the image of its subcube along the identity. -/
theorem cubicalToSingularSubcube_id (n : ℕ) :
    cubicalToSingularSubcube k n (ContinuousMap.id (Fin n → unitInterval)) =
      cubicalToSingularGen k n :=
  (rfl)

/-- The image of a degenerate subcube of the model is zero. -/
theorem cubicalToSingularSubcube_eq_zero {n m : ℕ}
    {ι : C(Fin m → unitInterval, Fin n → unitInterval)}
    (h : SingularCube.IsDegenerate ((upCube.{u} n).comp ι)) :
    cubicalToSingularSubcube k n ι = 0 := by
  unfold cubicalToSingularSubcube
  rw [NormalizedCubicalChain.ofCube_eq_zero k h]
  exact LinearMap.map_zero _

/-- Pushing forward the image of a subcube of the model along a map between models is the image of
the pushed-forward subcube. -/
theorem singularChains_map_cubicalToSingularSubcube {n m p : ℕ}
    (ι : C(Fin m → unitInterval, Fin n → unitInterval))
    (κ : C(Fin p → unitInterval, Fin m → unitInterval)) :
    ((singularChains k).map (cubeToHom ((upCube.{u} n).comp ι))).f p
        (cubicalToSingularSubcube k m κ) =
      cubicalToSingularSubcube k n (ι.comp κ) := by
  unfold cubicalToSingularSubcube
  rw [singularChains_map_cubicalToSingular, ← ContinuousMap.comp_assoc,
    cubeToHom_hom_comp_upCube, ContinuousMap.comp_assoc]

/-- The boundary of the image of the identity cube of the model `Iⁿ⁺¹` is the alternating sum of
the images of its faces. -/
theorem singularChains_d_cubicalToSingularGen (n : ℕ) :
    ((singularChains k).obj (cubeModel.{u} (n + 1))).d (n + 1) n
        (cubicalToSingularGen k (n + 1)) =
      ∑ i : Fin (n + 1), ((-1 : k) ^ (i : ℕ)) •
        (cubicalToSingularSubcube k (n + 1) (SingularCube.face i 0 (ContinuousMap.id _)) -
          cubicalToSingularSubcube k (n + 1) (SingularCube.face i 1 (ContinuousMap.id _))) := by
  unfold cubicalToSingularGen cubicalToSingularSubcube
  refine (HomologicalComplex.Hom.comm_apply ((cubicalToSingular k).app _) _ _ _).trans
    ((congrArg (((cubicalToSingular k).app _).f n).hom
      (normalizedCubicalChainComplex_obj_d_apply _ n _)).trans ?_)
  rw [NormalizedCubicalChain.boundary_ofCube]
  simp only [SingularCube.comp_face_id]
  -- The sums are over the same indices and the comparison is linear.
  exact (map_sum _ _ _).trans
    (Finset.sum_congr rfl fun i _ ↦ (map_smul _ _ _).trans (congrArg _ (map_sub _ _ _)))

/-- The image, under the comparison with cubical chains, of the identity simplex of the model
`Δⁿ`. -/
def singularToCubicalGen (n : ℕ) :
    ((normalizedCubicalChainComplex k).obj (simplexModel.{u} n)).X n :=
  ((singularToCubical k).app (simplexModel.{u} n)).f n (simplexChain (idSimplex n) 1)

/-- The comparison with cubical chains sends a simplex to the image of the model generator under
the simplex, regarded as a map from the model. -/
theorem singularToCubical_app_f_simplexChain {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ((singularToCubical k).app X).f n (simplexChain σ 1) =
      ((normalizedCubicalChainComplex k).map σ.down).f n (singularToCubicalGen k n) := by
  have h := congrArg (fun φ ↦ φ.f n (simplexChain (idSimplex n) (1 : k)))
    ((singularToCubical k).naturality σ.down)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp] at h
  have e : ((singularChains k).map σ.down).f n (simplexChain (idSimplex n) (1 : k)) =
      simplexChain σ 1 := by
    rw [singularChains_map_f_simplexChain, toSSet_map_down_idSimplex]
  rw [← e]
  unfold singularToCubicalGen
  -- Composites of `ModuleCat` morphisms are composites of linear maps by definition.
  exact h

/-- The chain homotopy `singularToCubicalCompHomotopy` evaluated on a simplex is the image of its
value on the identity simplex of the model under the simplex, regarded as a map from the model. -/
theorem singularToCubicalCompHomotopy_hom_simplexChain {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ((singularToCubicalCompHomotopy k X).hom n (n + 1)) (simplexChain σ 1) =
      ((singularChains k).map σ.down).f (n + 1)
        ((singularToCubicalCompHomotopy k (simplexModel.{u} n)).hom n (n + 1)
          (simplexChain (idSimplex n) 1)) := by
  have h := congrArg (fun φ ↦ φ (simplexChain (idSimplex n) (1 : k)))
    (congrArg ModuleCat.Hom.hom (singularToCubicalCompHomotopy_hom_naturality k σ.down n (n + 1)))
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  have e : ((singularChains k).map σ.down).f n (simplexChain (idSimplex n) (1 : k)) =
      simplexChain σ 1 := by
    rw [singularChains_map_f_simplexChain, toSSet_map_down_idSimplex]
  exact (congrArg ((singularToCubicalCompHomotopy k X).hom n (n + 1)).hom e.symm).trans h

/-- The chain homotopy `cubicalToSingularCompHomotopy` evaluated on a cube is the image of its
value on the identity cube of the model under the cube, regarded as a map from the model. -/
theorem cubicalToSingularCompHomotopy_hom_ofCube {X : TopCat.{u}} {n : ℕ} (c : SingularCube X n) :
    ((cubicalToSingularCompHomotopy k X).hom n (n + 1)) (NormalizedCubicalChain.ofCube X k c) =
      ((normalizedCubicalChainComplex k).map (cubeToHom c)).f (n + 1)
        ((cubicalToSingularCompHomotopy k (cubeModel.{u} n)).hom n (n + 1)
          (NormalizedCubicalChain.ofCube (cubeModel.{u} n) k (upCube n))) := by
  have h := congrArg (fun φ ↦ φ (NormalizedCubicalChain.ofCube (cubeModel.{u} n) k (upCube n)))
    (congrArg ModuleCat.Hom.hom (cubicalToSingularCompHomotopy_hom_naturality k (cubeToHom c) n
      (n + 1)))
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  have e : ((normalizedCubicalChainComplex k).map (cubeToHom c)).f n
      (NormalizedCubicalChain.ofCube (cubeModel.{u} n) k (upCube n)) =
      NormalizedCubicalChain.ofCube X k c :=
    (normalizedCubicalChainComplex_map_f_apply (cubeToHom c) n _).trans
      (by rw [NormalizedCubicalChain.map_ofCube, cubeToHom_hom_comp_upCube])
  exact (congrArg ((cubicalToSingularCompHomotopy k X).hom n (n + 1)).hom e.symm).trans h

/-- In degree zero, the model generator of the comparison to cubical chains is the point cube at the
vertex of the `0`-simplex. -/
@[simp]
theorem singularToCubicalGen_zero :
    singularToCubicalGen k 0 = NormalizedCubicalChain.ofCube (simplexModel.{u} 0) k
      (SingularCube.point (TopCat.toSSetObj₀Equiv (idSimplex.{u} 0))) :=
  singularToCubical_app_f_zero_simplexChain (idSimplex 0)

end ModelChains

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

namespace TopCat

/-- A map of spaces which induces a quasi-isomorphism of normalized cubical chains induces
isomorphisms on singular homology. -/
theorem isIso_singularHomologyMap_of_quasiIso {X Y : TopCat.{u}} (f : X ⟶ Y)
    [QuasiIso ((normalizedCubicalChainComplex k).map f)] (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map f) := by
  have h := singularCubicalHomologyIso_hom_naturality (k := k) f n
  rw [← Iso.eq_comp_inv] at h
  -- The singular homology functor sends a map to the homology map of its singular chain map.
  have hS : IsIso (HomologicalComplex.homologyMap ((singularChains k).map f) n) := by
    rw [h]
    infer_instance
  exact hS

end TopCat

end TauCeti
