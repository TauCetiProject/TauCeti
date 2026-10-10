/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.AlgebraicTopology.Singular.Basic
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.TopologicalSimplex
public import TauCeti.AlgebraicTopology.Singular.Cubical.ChainComplex
public import TauCeti.AlgebraicTopology.Singular.Cubical.Cone
public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalization
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.AcyclicModels

/-!
# The models of the cubical–simplicial comparison

The simplicial singular chains are free on the topological simplices `Δⁿ`, with generator the
identity simplex, and the normalized cubical chains are free on the cubes `Iⁿ` in the sense of
`TauCeti.AcyclicModels.ModelBasis`, through the normalization of
`TauCeti.AlgebraicTopology.Singular.Cubical.Normalization`.  Both are acyclic on every
contractible space, in particular on both kinds of models: the cubical chains by the cone of
`TauCeti.AlgebraicTopology.Singular.Cubical.Cone`, the simplicial chains by the vanishing of the
singular homology of a contractible space and the computation of `H₀` of a connected simplicial
set.

## Main definitions

* `TauCeti.singularChains k`: the simplicial singular chain complex functor with coefficients in
  the ring `k`.
* `TauCeti.singularModelBasis k`, `TauCeti.cubicalModelBasis k`: the two functors are free on
  models.
* `TauCeti.singularAugment`: the augmentation of the simplicial singular chains.

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

/-- The **simplicial singular chain complex** functor with coefficients in the ring `k`. -/
abbrev singularChains : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} k) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{u} k)).obj (ModuleCat.of k k)

/-- The topological `n`-simplex, the model of the simplicial singular chains in degree `n`. -/
abbrev simplexModel (n : ℕ) : TopCat.{u} := SimplexCategory.toTop.{u}.obj ⦋n⦌

/-- The identity singular simplex of the topological simplex. -/
def idSimplex (n : ℕ) : (TopCat.toSSet.obj (simplexModel.{u} n)) _⦋n⦌ := ULift.up (𝟙 _)

section Singular

variable {k}

/-- The chain of a singular simplex, with coefficient `a`. -/
abbrev simplexChain {X : TopCat.{u}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) (a : k) :
    ((singularChains k).obj X).X n :=
  (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of k k) σ a

/-- Linear maps out of simplicial singular chains agree when they agree on simplices. -/
theorem singularChains_linearMap_ext {X : TopCat.{u}} {n : ℕ} {V : Type u} [AddCommGroup V]
    [Module k V] {L L' : ((singularChains k).obj X).X n →ₗ[k] V}
    (h : ∀ σ, L (simplexChain σ 1) = L' (simplexChain σ 1)) : L = L' := by
  have : ModuleCat.ofHom L = ModuleCat.ofHom L' := by
    refine SSet.chainComplex_hom_ext fun σ ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    exact h σ
  exact congrArg ModuleCat.Hom.hom this

theorem simplexChain_eq_smul {X : TopCat.{u}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) (a : k) :
    simplexChain σ a = a • simplexChain σ 1 := by
  calc simplexChain σ a = simplexChain σ (a • (1 : k)) := by rw [smul_eq_mul, mul_one]
    _ = a • simplexChain σ 1 := map_smul _ a 1

theorem singularChains_map_f_simplexChain {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (a : k) :
    ((singularChains k).map f).f n (simplexChain σ a) =
      simplexChain ((TopCat.toSSet.map f).app _ σ) a := by
  change (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of k k)).f n
    ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of k k) σ a) =
      (TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of k k) _ a
  rw [← ModuleCat.comp_apply, SSet.ι_chainComplexMap_f]

/-- The underlying morphism of a pushed-forward singular simplex. -/
@[simp]
theorem toSSet_map_app_down {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) : ((TopCat.toSSet.map f).app _ σ).down = σ.down ≫ f := by
  have := TauCeti.TopCat.simplexMap_app f σ
  refine TopCat.ext fun x ↦ ?_
  exact congrArg (fun g ↦ g x) this

/-- A singular simplex is the push-forward of the identity simplex along itself. -/
theorem toSSet_map_down_idSimplex {X : TopCat.{u}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.map σ.down).app _ (idSimplex n) = σ := by
  refine ULift.ext ?_
  rw [toSSet_map_app_down, idSimplex, Category.id_comp]

end Singular

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
def singularModelBasis : AcyclicModels.ModelBasis (singularChains k) where
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
def cubicalModelBasis : AcyclicModels.ModelBasis (normalizedCubicalChainComplex.{u} k) where
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

/-- The augmentation of the simplicial singular chains: the sum of the coefficients. -/
def singularAugment (X : TopCat.{u}) : ((singularChains k).obj X).X 0 →ₗ[k] k :=
  (Cofan.IsColimit.desc ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of k k) 0)
    (fun _ ↦ 𝟙 (ModuleCat.of k k))).hom

variable {k} in
@[simp]
theorem singularAugment_simplexChain (X : TopCat.{u}) (σ : (TopCat.toSSet.obj X) _⦋0⦌)
    (a : k) : singularAugment k X (simplexChain σ a) = a := by
  have h := Cofan.IsColimit.fac ((TopCat.toSSet.obj X).isColimitChainComplexXCofan
    (ModuleCat.of k k) 0) (fun _ ↦ 𝟙 (ModuleCat.of k k)) σ
  simp only [SSet.chainComplexXCofan, Cofan.inj, Cofan.mk_ι_app] at h
  exact congrArg (fun g ↦ g.hom a) h

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

/-- The positive-degree cycles of the simplicial singular chains of a contractible space are
boundaries. -/
theorem singularChains_exists_d_eq_of_d_eq_zero (X : TopCat.{u}) [ContractibleSpace X] (q : ℕ)
    (z : ((singularChains k).obj X).X (q + 1))
    (hz : ((singularChains k).obj X).d (q + 1) q z = 0) :
    ∃ b, ((singularChains k).obj X).d (q + 2) (q + 1) b = z := by
  have hzero := isZero_singularHomologyFunctor_of_contractibleSpace (C := ModuleCat.{u} k)
    (ModuleCat.of k k) X (n := q + 1) (Nat.succ_ne_zero q)
  have hexact : ((singularChains k).obj X).ExactAt (q + 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 hzero
  rw [HomologicalComplex.exactAt_iff' _ (q + 2) (q + 1) q (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hexact
  exact hexact z hz

/-- In a connected simplicial set, the map from `0`-chains to the coproduct over the path
components followed by the codiagonal is the augmentation, and the codiagonal is injective. -/
private theorem singularAugment_eq_zero {X : TopCat.{u}} [PathConnectedSpace X]
    {z : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of k k)).X 0}
    (hz : singularAugment k X z = 0) :
    SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj X) (ModuleCat.of k k) z = 0 := by
  let D : (∐ fun _ : (TopCat.toSSet.obj X).π₀ ↦ ModuleCat.of k k) ⟶ ModuleCat.of k k :=
    Sigma.desc fun _ ↦ 𝟙 _
  have hD : SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj X) (ModuleCat.of k k) ≫ D =
      ModuleCat.ofHom (singularAugment k X) := by
    refine SSet.chainComplex_hom_ext fun σ ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    simp only [SSet.π₀.comp_fromChainComplexXZero_assoc, Sigma.ι_comp_desc, D]
    exact (singularAugment_simplexChain X σ 1).symm
  obtain ⟨c⟩ : Nonempty (TopCat.toSSet.obj X).π₀ := inferInstance
  let ιc : ModuleCat.of k k ⟶ ∐ fun _ : (TopCat.toSSet.obj X).π₀ ↦ ModuleCat.of k k :=
    Sigma.ι (fun _ : (TopCat.toSSet.obj X).π₀ ↦ ModuleCat.of k k) c
  have hsec : D ≫ ιc = 𝟙 _ := by
    refine Sigma.hom_ext _ _ fun c' ↦ ?_
    obtain rfl : c = c' := Subsingleton.elim _ _
    simp [D, ιc]
  set w := SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj X) (ModuleCat.of k k) z
  have h1 : D w = 0 := by
    have := congrArg (fun g ↦ g.hom z) hD
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at this
    exact this.trans hz
  calc w = (D ≫ ιc) w := by rw [hsec]; rfl
    _ = 0 := by rw [ModuleCat.comp_apply, h1, map_zero]

/-- A `0`-chain of augmentation zero of the simplicial singular chains of a path-connected space
is a boundary. -/
theorem singularChains_exists_d_eq_of_augment_eq_zero (X : TopCat.{u}) [PathConnectedSpace X]
    (z : ((singularChains k).obj X).X 0) (hz : singularAugment k X z = 0) :
    ∃ b, ((singularChains k).obj X).d 1 0 b = z := by
  have hexact := ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk _ _ (SSet.π₀.d_fromChainComplexXZero (TopCat.toSSet.obj X)
      (ModuleCat.of k k) 1))
    (SSet.isColimitCokernelCoforkChainComplexDOneZero _ _)
  rw [ShortComplex.moduleCat_exact_iff] at hexact
  exact hexact z (singularAugment_eq_zero hz)

/-- **The simplicial singular chains are acyclic on contractible models.** -/
theorem isAcyclicOn_singularChains (M : ℕ → TopCat.{u}) [∀ n, ContractibleSpace (M n)] :
    AcyclicModels.IsAcyclicOn (singularChains k) M (singularAugment k) where
  exists_d_eq_of_d_eq_zero n q z hz := singularChains_exists_d_eq_of_d_eq_zero (M n) q z hz
  exists_d_eq_of_augment_eq_zero n z hz := singularChains_exists_d_eq_of_augment_eq_zero (M n) z hz

end TauCeti
