/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ContractibleChains
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

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Finsupp Simplicial

universe u

namespace TauCeti

variable (k : Type u) [Ring k]

/-- The coefficients of a simplicial singular chain on the maps from the topological simplex. -/
def singularCoord (X : TopCat.{u}) (n : ℕ) :
    ((singularChains k).obj X).X n →ₗ[k] ((simplexModel.{u} n ⟶ X) →₀ k) :=
  (Cofan.IsColimit.desc ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of k k) n)
    (fun σ ↦ ModuleCat.ofHom (lsingle σ.down) :
      ∀ _, ModuleCat.of k k ⟶ ModuleCat.of k ((simplexModel.{u} n ⟶ X) →₀ k))).hom

variable {k} in
@[simp]
theorem singularCoord_simplexChain (X : TopCat.{u}) {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (a : k) : singularCoord k X n (simplexChain σ a) = single σ.down a := by
  have h := Cofan.IsColimit.fac ((TopCat.toSSet.obj X).isColimitChainComplexXCofan
    (ModuleCat.of k k) n) (fun σ ↦ ModuleCat.ofHom (lsingle σ.down) :
      ∀ _, ModuleCat.of k k ⟶ ModuleCat.of k ((simplexModel.{u} n ⟶ X) →₀ k)) σ
  simp only [SSet.chainComplexXCofan, Cofan.inj, Cofan.mk_ι_app] at h
  exact congrArg (fun g ↦ g.hom a) h

/-- **The simplicial singular chains are free on the topological simplices.** -/
def singularModelPresentation : AcyclicModels.ModelPresentation (singularChains k) where
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

/-! ### The cubical models -/

/-- The cube `Iⁿ`, the model of the normalized cubical chains in degree `n`. -/
abbrev cubeModel (n : ℕ) : TopCat.{u} := TopCat.of (ULift.{u} (Fin n → unitInterval))

/-- The identity cube of the model, up to the universe lift. -/
def upCube (n : ℕ) : SingularCube (cubeModel.{u} n) n := ⟨ULift.up, continuous_uliftUp⟩

/-- A singular cube, as a map from the model. -/
def cubeToHom {X : TopCat.{u}} {n : ℕ} (c : SingularCube X n) : cubeModel.{u} n ⟶ X :=
  TopCat.ofHom (c.comp ⟨ULift.down, continuous_uliftDown⟩)

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
def cubicalModelPresentation :
    AcyclicModels.ModelPresentation (normalizedCubicalChainComplex.{u} k) where
  model := cubeModel
  gen n := NormalizedCubicalChain.ofCube (cubeModel n) k (upCube n)
  coord := cubicalCoord k
  coord_map f _ x := cubicalCoord_map f x
  sum_coord _ _ x := sum_cubicalCoord x

/-- The straight-line contraction of the cube `Iⁿ` onto its vertex `0`. -/
def cubeContraction (n : ℕ) :
    (ContinuousMap.const (Fin n → unitInterval) 0).Homotopy (ContinuousMap.id _) where
  toFun p j := ⟨(p.1 : ℝ) * p.2 j, unitInterval.mul_mem p.1.2 (p.2 j).2⟩
  continuous_toFun := by fun_prop
  map_zero_left x := by ext j; simp
  map_one_left x := by ext j; simp

instance (n : ℕ) : ContractibleSpace (Fin n → unitInterval) :=
  (contractible_iff_id_nullhomotopic _).2 ⟨0, ⟨(cubeContraction n).symm⟩⟩

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

end TauCeti
