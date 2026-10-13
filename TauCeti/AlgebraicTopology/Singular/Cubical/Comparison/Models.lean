/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Contractible
public import TauCeti.Topology.Homotopy.Cube.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.ChainComplex
public import TauCeti.AlgebraicTopology.Singular.Cubical.Cone
public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalization
public import TauCeti.Algebra.Homology.AcyclicModels

/-!
# The models of the cubical–simplicial comparison

The simplicial singular chains are free on the topological simplices `Δⁿ`, with generator the
identity simplex, and the normalized cubical chains are free on the cubes `Iⁿ` in the sense of
`TauCeti.AcyclicModels.ModelPresentation`, through the normalization of
`TauCeti.AlgebraicTopology.Singular.Cubical.Normalization`.  Both are acyclic on every
contractible space, in particular on both kinds of models: the cubical chains by the cone of
`TauCeti.AlgebraicTopology.Singular.Cubical.Cone`, the simplicial chains by the vanishing of the
singular homology of a contractible space and the computation of `H₀` of a connected simplicial
set.

## Main definitions

* `TauCeti.singularModelPresentation k`, `TauCeti.cubicalModelPresentation k`: the two functors
  are free on models.

## Main results

* `TauCeti.isAcyclicOn_singularChains`, `TauCeti.isAcyclicOn_normalizedCubicalChainComplex`:
  both functors are acyclic on families of contractible spaces.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Finsupp Simplicial

universe u

namespace TauCeti

/-! ### Singular simplices -/

/-- The underlying morphism of a pushed-forward singular simplex. -/
@[simp]
theorem toSSet_map_app_down {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) : ((TopCat.toSSet.map f).app _ σ).down = σ.down ≫ f := by
  have := TauCeti.TopCat.simplexMap_app f σ
  refine TopCat.ext fun x ↦ ?_
  exact congrArg (fun g ↦ g x) this

variable (k : Type u) [Ring k]

/-- The coefficients of a simplicial singular chain on the maps from the topological simplex. -/
def singularCoord (X : TopCat.{u}) (n : ℕ) :
    ((singularChains k).obj X).X n →ₗ[k] ((simplexModel.{u} n ⟶ X) →₀ k) :=
  chainsDesc fun σ ↦ single σ.down (1 : k)

variable {k} in
@[simp]
theorem singularCoord_simplexChain (X : TopCat.{u}) {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (a : k) : singularCoord k X n (simplexChain σ a) = single σ.down a := by
  rw [singularCoord, chainsDesc_simplexChain, smul_single, smul_eq_mul, mul_one]

/-- **The simplicial singular chains are free on the topological simplices.** -/
@[expose] def singularModelPresentation : AcyclicModels.ModelPresentation (singularChains k) where
  model := simplexModel
  gen n := simplexChain (idSimplex n) 1
  coord := singularCoord k
  coord_map {X Y} f n x := by
    have := singularChains_linearMap_ext
      (L := singularCoord k Y n ∘ₗ (((singularChains k).map f).f n).hom)
      (L' := lmapDomain k k (· ≫ f) ∘ₗ singularCoord k X n) fun σ ↦ by
        simp only [LinearMap.coe_comp, Function.comp_apply, singularChains_map_f_simplexChain,
          singularCoord_simplexChain, toSSet_map_app_down,
          lmapDomain_apply, mapDomain_single]
    exact LinearMap.congr_fun this x
  sum_coord X n x := by
    have := singularChains_linearMap_ext
      (L := linearCombination k (fun σ ↦ ((singularChains k).map σ).f n
        (simplexChain (idSimplex n) 1)) ∘ₗ singularCoord k X n) (L' := LinearMap.id) fun σ ↦ by
        simp only [LinearMap.coe_comp, Function.comp_apply, singularCoord_simplexChain,
          linearCombination_single, singularChains_map_f_simplexChain, one_smul,
          LinearMap.id_apply]
        exact congrArg (simplexChain · 1) (toSSet_map_down_idSimplex σ)
    simpa [linearCombination_apply] using LinearMap.congr_fun this x

@[simp]
theorem singularModelPresentation_model (n : ℕ) :
    (singularModelPresentation k).model n = simplexModel n :=
  (rfl)

theorem singularModelPresentation_gen (n : ℕ) :
    (singularModelPresentation k).gen n = simplexChain (idSimplex n) 1 :=
  (rfl)

theorem singularModelPresentation_coord (X : TopCat.{u}) (n : ℕ) :
    (singularModelPresentation k).coord X n = singularCoord k X n :=
  (rfl)

/-! ### The cubical models -/

/-- The cube `Iⁿ`, the model of the normalized cubical chains in degree `n`. -/
abbrev cubeModel (n : ℕ) : TopCat.{u} := TopCat.of (ULift.{u} (Fin n → unitInterval))

/-- The identity cube of the model, up to the universe lift. -/
def upCube (n : ℕ) : SingularCube (cubeModel.{u} n) n := ⟨ULift.up, continuous_uliftUp⟩

/-- A singular cube, as a map from the model. -/
def cubeToHom {X : TopCat.{u}} {n : ℕ} (c : SingularCube X n) : cubeModel.{u} n ⟶ X :=
  TopCat.ofHom (c.comp ⟨ULift.down, continuous_uliftDown⟩)

@[simp]
theorem cubeToHom_apply {X : TopCat.{u}} {n : ℕ} (c : SingularCube X n) (x : cubeModel.{u} n) :
    cubeToHom c x = c x.down :=
  (rfl)

@[simp]
theorem cubeToHom_comp {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ} (c : SingularCube X n) :
    cubeToHom (f.hom.comp c) = cubeToHom c ≫ f :=
  (rfl)

@[simp]
theorem cubeToHom_hom_comp_upCube {X : TopCat.{u}} {n : ℕ} (c : SingularCube X n) :
    (cubeToHom c).hom.comp (upCube n) = c :=
  (rfl)

/-- The coefficients of a normalized cubical chain on the maps from the cube: the coefficients of
its normalization. -/
def cubicalCoord (X : TopCat.{u}) (n : ℕ) :
    NormalizedCubicalChain X k n →ₗ[k] ((cubeModel.{u} n ⟶ X) →₀ k) :=
  lmapDomain k k cubeToHom ∘ₗ NormalizedCubicalChain.toCubicalChain X k n

variable {k} in
theorem mapDomain_cubeToHom_map {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ} (c : CubicalChain X k n) :
    mapDomain cubeToHom (CubicalChain.map k f.hom n c) =
      mapDomain (· ≫ f) (mapDomain cubeToHom c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, mapDomain_add, hc, hd]
  | single c a => simp [mapDomain_single]

variable {k} in
theorem cubicalCoord_map {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ}
    (x : NormalizedCubicalChain X k n) :
    cubicalCoord k Y n (NormalizedCubicalChain.map k f.hom n x) =
      mapDomain (· ≫ f) (cubicalCoord k X n x) := by
  simp only [cubicalCoord, LinearMap.coe_comp, Function.comp_apply,
    NormalizedCubicalChain.toCubicalChain_map, lmapDomain_apply, mapDomain_cubeToHom_map]

variable {k} in
theorem sum_cubicalCoord {X : TopCat.{u}} {n : ℕ} (x : NormalizedCubicalChain X k n) :
    (cubicalCoord k X n x).sum (fun σ a ↦ a • NormalizedCubicalChain.map k σ.hom n
      (NormalizedCubicalChain.ofCube (cubeModel n) k (upCube n))) = x := by
  rw [cubicalCoord, LinearMap.comp_apply, lmapDomain_apply]
  refine (sum_mapDomain_index (fun _ ↦ ?_) (fun _ _ _ ↦ ?_)).trans ?_
  · exact zero_smul k _
  · exact add_smul _ _ _
  · simp only [NormalizedCubicalChain.map_ofCube]
    exact NormalizedCubicalChain.sum_toCubicalChain k x

/-- **The normalized cubical chains are free on the cubes**, through the normalization. -/
@[expose] def cubicalModelPresentation :
    AcyclicModels.ModelPresentation (normalizedCubicalChainComplex.{u} k) where
  model := cubeModel
  gen n := NormalizedCubicalChain.ofCube (cubeModel n) k (upCube n)
  coord := cubicalCoord k
  coord_map f _ x := cubicalCoord_map f x
  sum_coord _ _ x := sum_cubicalCoord x

@[simp]
theorem cubicalModelPresentation_model (n : ℕ) :
    (cubicalModelPresentation k).model n = cubeModel n :=
  (rfl)

theorem cubicalModelPresentation_gen (n : ℕ) :
    (cubicalModelPresentation k).gen n = NormalizedCubicalChain.ofCube (cubeModel n) k (upCube n) :=
  (rfl)

theorem cubicalModelPresentation_coord (X : TopCat.{u}) (n : ℕ) :
    (cubicalModelPresentation k).coord X n = cubicalCoord k X n :=
  (rfl)

/-- The cube models are contractible. -/
instance (n : ℕ) : ContractibleSpace (cubeModel.{u} n) :=
  (Homeomorph.ulift (X := Fin n → unitInterval)).contractibleSpace

/-! ### Augmentations and acyclicity -/

/-- The augmentation of the normalized cubical chains. -/
abbrev cubicalAugment (X : TopCat.{u}) : ((normalizedCubicalChainComplex k).obj X).X 0 →ₗ[k] k :=
  NormalizedCubicalChain.augment X k

variable {k}

/-- **The normalized cubical chains are acyclic on contractible models.** -/
theorem isAcyclicOn_normalizedCubicalChainComplex (M : ℕ → TopCat.{u})
    [∀ n, ContractibleSpace (M n)] :
    AcyclicModels.IsAcyclicOn (normalizedCubicalChainComplex k) M (cubicalAugment k) where
  exists_d_eq_of_d_eq_zero n q z hz := by
    have hz' : NormalizedCubicalChain.boundary (M n) k q z = 0 :=
      (normalizedCubicalChainComplex_obj_d_apply _ _ z).symm.trans hz
    obtain ⟨g, hg⟩ := NormalizedCubicalChain.exists_boundary_eq_of_boundary_eq_zero k hz'
    exact ⟨g, (normalizedCubicalChainComplex_obj_d_apply _ _ g).trans hg⟩
  exists_d_eq_of_augment_eq_zero n z hz := by
    obtain ⟨g, hg⟩ := NormalizedCubicalChain.exists_boundary_eq_of_augment_eq_zero k hz
    exact ⟨g, (normalizedCubicalChainComplex_obj_d_apply _ _ g).trans hg⟩

/-- **The simplicial singular chains are acyclic on contractible models.** -/
theorem isAcyclicOn_singularChains (M : ℕ → TopCat.{u}) [∀ n, ContractibleSpace (M n)] :
    AcyclicModels.IsAcyclicOn (singularChains k) M (singularAugment k) where
  exists_d_eq_of_d_eq_zero n q z hz := singularChains_exists_d_eq_of_d_eq_zero (M n) q z hz
  exists_d_eq_of_augment_eq_zero n z hz := singularChains_exists_d_eq_of_augment_eq_zero (M n) z hz

variable (k) in
/-- The simplicial singular chains are acyclic on the models of the normalized cubical chains. -/
theorem isAcyclicOn_singularChains_cubicalModelPresentation :
    AcyclicModels.IsAcyclicOn (singularChains k) (cubicalModelPresentation k).model
      (singularAugment k) :=
  isAcyclicOn_singularChains cubeModel

variable (k) in
/-- The normalized cubical chains are acyclic on the models of the simplicial singular chains. -/
theorem isAcyclicOn_normalizedCubicalChainComplex_singularModelPresentation :
    AcyclicModels.IsAcyclicOn (normalizedCubicalChainComplex k) (singularModelPresentation k).model
      (cubicalAugment k) :=
  isAcyclicOn_normalizedCubicalChainComplex simplexModel

variable (k) in
/-- The simplicial singular chains are acyclic on their own models. -/
theorem isAcyclicOn_singularChains_singularModelPresentation :
    AcyclicModels.IsAcyclicOn (singularChains k) (singularModelPresentation k).model
      (singularAugment k) :=
  isAcyclicOn_singularChains simplexModel

variable (k) in
/-- The normalized cubical chains are acyclic on their own models. -/
theorem isAcyclicOn_normalizedCubicalChainComplex_cubicalModelPresentation :
    AcyclicModels.IsAcyclicOn (normalizedCubicalChainComplex k) (cubicalModelPresentation k).model
      (cubicalAugment k) :=
  isAcyclicOn_normalizedCubicalChainComplex cubeModel

/-! ### Properties of the cubical augmentation -/

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

/-! ### The degree-zero data of the comparison maps -/

variable (k)

/-- The point of the `0`-cube. -/
def cubeModelPoint : cubeModel.{u} 0 := ULift.up fun i ↦ i.elim0

/-- The `0`-simplex at the point of the `0`-cube: the value on the model of the comparison map
from cubical to simplicial chains in degree zero. -/
def cubicalToSingularGen₀ :
    ((singularChains k).obj ((cubicalModelPresentation.{u} k).model 0)).X 0 :=
  simplexChain (TopCat.toSSetObj₀Equiv.symm cubeModelPoint) 1

/-- The `0`-cube at the vertex of the `0`-simplex: the value on the model of the comparison map
from simplicial to cubical chains in degree zero. -/
def singularToCubicalGen₀ :
    ((normalizedCubicalChainComplex k).obj ((singularModelPresentation.{u} k).model 0)).X 0 :=
  NormalizedCubicalChain.ofCube (simplexModel 0) k
    (SingularCube.point (SimplexCategory.toTopInitialVertex ⦋0⦌))

theorem cubicalToSingularGen₀_eq :
    cubicalToSingularGen₀ k = simplexChain (TopCat.toSSetObj₀Equiv.symm cubeModelPoint) 1 :=
  (rfl)

theorem singularToCubicalGen₀_eq :
    singularToCubicalGen₀ k = NormalizedCubicalChain.ofCube (simplexModel 0) k
      (SingularCube.point (SimplexCategory.toTopInitialVertex ⦋0⦌)) :=
  (rfl)

/-- The comparison map to simplicial chains in degree zero preserves augmentations. -/
theorem singularAugment_extend_cubicalToSingularGen₀ (X : TopCat.{u})
    (x : ((normalizedCubicalChainComplex k).obj X).X 0) :
    singularAugment k X ((cubicalModelPresentation k).extend (cubicalToSingularGen₀ k) X x) =
      cubicalAugment k X x :=
  (cubicalModelPresentation k).augment_extend (fun f x ↦ cubicalAugment_map f x)
    (fun f x ↦ singularAugment_map f x) _
    ((singularAugment_simplexChain _ _ 1).trans (NormalizedCubicalChain.augment_ofCube k _).symm)
    X x

/-- The comparison map to cubical chains in degree zero preserves augmentations. -/
theorem cubicalAugment_extend_singularToCubicalGen₀ (X : TopCat.{u})
    (x : ((singularChains k).obj X).X 0) :
    cubicalAugment k X ((singularModelPresentation k).extend (singularToCubicalGen₀ k) X x) =
      singularAugment k X x :=
  (singularModelPresentation k).augment_extend (fun f x ↦ singularAugment_map f x)
    (fun f x ↦ cubicalAugment_map f x) _
    ((NormalizedCubicalChain.augment_ofCube k _).trans (singularAugment_simplexChain _ _ 1).symm)
    X x


/-! ### The maps determined on the models, on generators -/

variable {k}

/-- On the chain of a simplex, the map determined by an element `t` on the simplicial model is
the image of `t` under that simplex. -/
theorem singularModelPresentation_extend_simplexChain
    {G : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} k) ℕ}
    {m n : ℕ} (t : (G.obj ((singularModelPresentation k).model n)).X m) {X : TopCat.{u}}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (singularModelPresentation k).extend t X (simplexChain σ 1) = (G.map σ.down).f m t := by
  rw [AcyclicModels.ModelPresentation.extend_apply]
  -- `singularModelPresentation_coord` cannot be used by `rw` here: the coordinates are indexed by
  -- maps out of `(singularModelPresentation k).model n`, which is `simplexModel n` only
  -- definitionally, so the goal is restated with the coordinate type `simplexModel n ⟶ X`.
  change (singularCoord k X n (simplexChain σ 1)).sum _ = _
  rw [singularCoord_simplexChain]
  exact (sum_single_index (by simp)).trans (one_smul _ _)

/-- On the class of a point cube, the map determined by an element `t` on the `0`-cube is the
image of `t` under the corresponding map from the `0`-cube. -/
theorem cubicalModelPresentation_extend_ofCube_zero
    {G : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} k) ℕ} {m : ℕ}
    (t : (G.obj ((cubicalModelPresentation k).model 0)).X m) {X : TopCat.{u}}
    (c : SingularCube X 0) :
    (cubicalModelPresentation k).extend t X (NormalizedCubicalChain.ofCube X k c) =
      (G.map (cubeToHom c)).f m t := by
  refine (AcyclicModels.ModelPresentation.extend_apply _ t X _).trans ?_
  -- As above, the coordinates are restated with the coordinate type `cubeModel 0 ⟶ X`; the
  -- model `(cubicalModelPresentation k).model 0` is `cubeModel 0` only definitionally.
  change (cubicalCoord k X 0 (NormalizedCubicalChain.ofCube X k c)).sum _ = _
  have : cubicalCoord k X 0 (NormalizedCubicalChain.ofCube X k c) = single (cubeToHom c) 1 := by
    -- The only set of coordinates of the `0`-cube is `∅`, so normalization fixes the point cube.
    have h0 : (default : Finset (Fin 0)) = ∅ := Subsingleton.elim _ _
    simp [cubicalCoord, NormalizedCubicalChain.ofCube_def, Finset.univ_unique, mapDomain_single,
      h0]
  rw [this]
  exact (sum_single_index (by simp)).trans (one_smul _ _)

end TauCeti
