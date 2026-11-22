/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Triangulation.Chains
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Cube.Generator

/-!
# The coordinate cube class

The positive ordered triangulation `TauCeti.SingularCube.orderedChain` of the identity cube of
`Iⁿ` is a relative singular cycle of the pair `(Iⁿ, ∂Iⁿ)`. With integer coefficients it is the
`n`-fold iterated shuffle product of the interval chain `t ↦ t` taken in coordinate order
(`TauCeti.iteratedIntegralShuffle_eq_orderedChain`), so its class is the coordinate-oriented
fundamental class of the cube. This file computes that class: it is `(-1) ^ (n (n + 1) / 2)` times
the selected generator `TauCeti.singularHomologyCubeBoundaryPairIso` of `Hₙ(Iⁿ, ∂Iⁿ; k)`, over
every ring `k` (`TauCeti.singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass`). In
particular it generates `Hₙ(Iⁿ, ∂Iⁿ; k)` (`TauCeti.bijective_smul_coordinateCubeClass`), and in
dimension one it is the class of `t ↦ t`, whose boundary is `[1] - [0]`
(`TauCeti.coordinateCubeClass_zero`).

The computation compares the triangulation with the acyclic-models comparison
`TauCeti.cubicalToSingular`, whose value on the identity cube is calibrated in
`TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Cube.Generator`. The raw cubical
chains, degenerate cubes included, form a functor `TauCeti.rawCubicalChainComplex k` which is free
on the cubes (`TauCeti.rawCubicalModelPresentation`). The sign-corrected triangulation
`TauCeti.orderedTriangulationNatTrans` and the normalization followed by the comparison are two
natural chain maps from it to the singular chains, agreeing on points, so the method of acyclic
models makes them naturally homotopic (`TauCeti.orderedTriangulationHomotopy`). By naturality the
homotopy carries cubes of a subspace to chains of the subspace, so for a pair `P` and a cube `c`
sending the boundary of the cube into the subspace, the relative triangulation cycle
`TopPair.orderedCycleOfCube k c hc` represents `(-1) ^ (m + 1)` times the image of the cubical class
of `c` (`TopPair.singularCubicalHomologyIso_inv_homologyπ_cubicalCycleOfCube`).

## Main definitions

* `TauCeti.rawCubicalChainComplex k`: the raw cubical chain complex functor.
* `TauCeti.rawCubicalChainComplexπ k`: the normalization quotient, a natural chain map to the
  normalized cubical chains.
* `TauCeti.orderedTriangulationNatTrans k`: the ordered triangulation as a natural chain map.
* `TauCeti.orderedTriangulationHomotopy k X`: the natural homotopy from the triangulation to the
  normalization followed by `TauCeti.cubicalToSingular`.
* `TopPair.orderedCycleOfCube k c hc`: the triangulation of a cube sending the boundary of the cube
  into the subspace, as a relative singular cycle.
* `TauCeti.coordinateCubeClass k m`: the coordinate cube class in `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; k)`.

## Main results

* `TauCeti.homologyMap_orderedTriangulationNatTrans_app`: on homology the triangulation is the
  normalization followed by the inverse of `TauCeti.singularCubicalHomologyIso`.
* `TopPair.singularCubicalHomologyIso_inv_homologyπ_cubicalCycleOfCube`: the relative form.
* `TauCeti.singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass`: the coordinate of the
  cube class is `(-1) ^ ((m + 1) (m + 2) / 2)`.

## References

* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
* S. Eilenberg and S. Mac Lane, *Acyclic models*, Amer. J. Math. 75 (1953).
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* A. Hatcher, *Algebraic Topology*, Proposition 3B.1 and the relative cross product after
  Theorem 3B.6.
-/

public section

noncomputable section

open CategoryTheory Limits Set Finsupp
open scoped unitInterval

universe u

namespace TauCeti

variable (k : Type u) [Ring k]

/-! ### The raw cubical chain complex functor -/

/-- The **raw cubical chain complex functor** with coefficients in `k`: the formal combinations of
all singular cubes, degenerate ones included, with the cubical boundary. -/
def rawCubicalChainComplex : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} k) ℕ where
  obj X := rawCubicalChainComplexObj X (ModuleCat.of k k)
  map {X Y} f := ChainComplex.ofHom
    (fun _ ↦ ModuleCat.ofHom (lmapDomain (ModuleCat.of k k) k f.hom.comp)) fun n ↦
      ModuleCat.hom_ext <| LinearMap.ext fun x ↦
        (rawCubicalChainComplexObj_d_apply Y _ n _).trans
          ((LinearMap.congr_fun (CubicalChain.lmapDomain_comp_boundary k _ f.hom n) x).symm.trans
            (congrArg (lmapDomain (ModuleCat.of k k) k f.hom.comp)
              (rawCubicalChainComplexObj_d_apply X _ n x).symm))
  map_id _ := HomologicalComplex.hom_ext _ _ fun _ ↦
    ModuleCat.hom_ext (LinearMap.ext fun _ ↦ mapDomain_id)
  map_comp f g := HomologicalComplex.hom_ext _ _ fun _ ↦
    ModuleCat.hom_ext (LinearMap.ext fun x ↦
      mapDomain_comp (f := f.hom.comp) (g := g.hom.comp) (v := x))

variable {k}

/-- A singular cube, as a raw cubical chain with coefficient one. -/
def rawCubicalChainOfCube {X : TopCat.{u}} {n : ℕ} (c : SingularCube X n) :
    ((rawCubicalChainComplex k).obj X).X n :=
  single c (1 : k)

/-- Two linear maps out of the raw cubical `n`-chains agree if they agree on every cube. -/
@[ext]
theorem rawCubicalChainComplex_X_linearMap_ext {X : TopCat.{u}} {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module k M] {f₁ f₂ : ((rawCubicalChainComplex k).obj X).X n →ₗ[k] M}
    (h : ∀ c : SingularCube X n, f₁ (rawCubicalChainOfCube c) = f₂ (rawCubicalChainOfCube c)) :
    f₁ = f₂ :=
  lhom_ext' (φ := f₁) (ψ := f₂) fun c ↦ LinearMap.ext_ring (h c)

/-- A continuous map sends the raw chain of a cube `c` to that of `f ∘ c`. -/
@[simp]
theorem rawCubicalChainComplex_map_f_rawCubicalChainOfCube {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ}
    (c : SingularCube X n) :
    ((rawCubicalChainComplex k).map f).f n (rawCubicalChainOfCube c) =
      rawCubicalChainOfCube (f.hom.comp c) :=
  mapDomain_single (f := f.hom.comp) (a := c) (b := (1 : k))

/-- The boundary of the raw chain of a cube is the signed sum of the raw chains of its faces. -/
theorem rawCubicalChainComplex_d_rawCubicalChainOfCube {X : TopCat.{u}} {n : ℕ}
    (c : SingularCube X (n + 1)) :
    ((rawCubicalChainComplex k).obj X).d (n + 1) n (rawCubicalChainOfCube c) =
      ∑ i : Fin (n + 1), (-1 : k) ^ (i : ℕ) •
        (rawCubicalChainOfCube (SingularCube.face i 0 c) -
          rawCubicalChainOfCube (SingularCube.face i 1 c)) := by
  refine (rawCubicalChainComplexObj_d_apply X (ModuleCat.of k k) n (single c (1 : k))).trans
    ((CubicalChain.boundary_single (M := ModuleCat.of k k) k c (1 : k)).trans
      (Finset.sum_congr rfl fun i _ ↦ ?_))
  rw [← Int.cast_smul_eq_zsmul k, Int.cast_pow, Int.cast_neg, Int.cast_one]
  -- The raw chain of a cube is the finitely supported function with value one at the cube.
  rfl

variable (k)

/-- **The raw cubical chains are free on the cubes**: a chain is the combination of the images of
the identity cube of `Iⁿ` under the cubes of its support. -/
def rawCubicalModelPresentation : AcyclicModels.ModelPresentation (rawCubicalChainComplex k) where
  model := cubeModel
  gen n := rawCubicalChainOfCube (upCube n)
  coord X n := (lmapDomain k k cubeToHom : (SingularCube X n →₀ k) →ₗ[k] ((cubeModel n ⟶ X) →₀ k))
  coord_map {X Y} f n x := (mapDomain_comp (f := f.hom.comp) (g := cubeToHom) (v := x)).symm.trans
    (mapDomain_comp (f := cubeToHom) (g := fun s : cubeModel n ⟶ X ↦ s ≫ f) (v := x))
  sum_coord X n x := by
    let F := fun s : cubeModel n ⟶ X ↦
      ((rawCubicalChainComplex k).map s).f n (rawCubicalChainOfCube (upCube n))
    have h : linearCombination k F ∘ₗ
        (lmapDomain k k cubeToHom :
          ((rawCubicalChainComplex k).obj X).X n →ₗ[k] ((cubeModel n ⟶ X) →₀ k)) =
            LinearMap.id :=
      rawCubicalChainComplex_X_linearMap_ext fun c ↦
        (congrArg (linearCombination k F) (mapDomain_single (f := cubeToHom) (a := c)
          (b := (1 : k)))).trans ((linearCombination_single k 1 _).trans ((one_smul k _).trans
            (rawCubicalChainComplex_map_f_rawCubicalChainOfCube _ _)))
    exact (linearCombination_apply k _).symm.trans (LinearMap.congr_fun h x)

/-- The normalization quotient from the raw to the normalized cubical chains, as a natural chain
map. -/
def rawCubicalChainComplexπ : rawCubicalChainComplex k ⟶ normalizedCubicalChainComplex k where
  app X := ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (CubicalChain.degenerate X k n).mkQ)
    fun n ↦ ModuleCat.hom_ext <| LinearMap.ext fun x ↦
      (normalizedCubicalChainComplex_obj_d_apply X n _).trans
        ((NormalizedCubicalChain.boundary_mk k x).trans
          (congrArg Submodule.Quotient.mk (rawCubicalChainComplexObj_d_apply X _ n x).symm))
  naturality _ Y f := HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext <|
    rawCubicalChainComplex_X_linearMap_ext fun c ↦
      (congrArg (CubicalChain.degenerate Y k n).mkQ
        (rawCubicalChainComplex_map_f_rawCubicalChainOfCube f c)).trans
      ((congrArg Submodule.Quotient.mk (CubicalChain.map_single k f.hom c (1 : k))).symm.trans
        (NormalizedCubicalChain.map_mk k f.hom _).symm)

variable {k}

/-- The normalization quotient sends the raw chain of a cube to its normalized class. -/
@[simp]
theorem rawCubicalChainComplexπ_app_f_rawCubicalChainOfCube {X : TopCat.{u}} {n : ℕ}
    (c : SingularCube X n) :
    ((rawCubicalChainComplexπ k).app X).f n (rawCubicalChainOfCube c) =
      (normalizedCubicalChainComplexXEquiv X n).symm (NormalizedCubicalChain.ofCube X k c) :=
  (NormalizedCubicalChain.ofCube_def k c).symm

variable (k)

/-- The sign-corrected ordered triangulation `CubicalChain.orderedTriangulationChainMap`, as a
natural chain map from the raw cubical chains to the simplicial singular chains. -/
def orderedTriangulationNatTrans : rawCubicalChainComplex k ⟶ singularChains k where
  app X := CubicalChain.orderedTriangulationChainMap X (ModuleCat.of k k)
  naturality X Y f := HomologicalComplex.hom_ext _ _ fun n ↦
    ModuleCat.hom_ext <| LinearMap.ext fun x ↦
      (ConcreteCategory.congr_hom
        (CubicalChain.orderedTriangulationChainMap_f Y (ModuleCat.of k k) n)
          (((rawCubicalChainComplex k).map f).f n x)).trans
      ((LinearMap.congr_fun
        (CubicalChain.nativeOrderedTriangulation_naturality (ModuleCat.of k k) f n) x).symm.trans
      (congrArg (((singularChains k).map f).f n).hom (ConcreteCategory.congr_hom
        (CubicalChain.orderedTriangulationChainMap_f X (ModuleCat.of k k) n) x).symm))

variable {k}

/-- The triangulation sends the raw chain of an `n`-cube to `(-1) ^ n` times its positive ordered
triangulation. -/
@[simp]
theorem orderedTriangulationNatTrans_app_f_rawCubicalChainOfCube {X : TopCat.{u}} {n : ℕ}
    (c : SingularCube X n) :
    ((orderedTriangulationNatTrans k).app X).f n (rawCubicalChainOfCube c) =
      (-1 : k) ^ n • (SingularCube.orderedChain c (ModuleCat.of k k)).hom 1 := by
  refine (ConcreteCategory.congr_hom
    (CubicalChain.orderedTriangulationChainMap_f X (ModuleCat.of k k) n) (single c (1 : k))).trans
      ((CubicalChain.nativeOrderedTriangulation_apply (ModuleCat.of k k) n
        (single c (1 : k))).trans ?_)
  rw [CubicalChain.orderedTriangulation_single, ← Int.cast_smul_eq_zsmul k, Int.cast_pow,
    Int.cast_neg, Int.cast_one]

variable (k)

/-- The ordered triangulation and the normalization followed by the acyclic-models comparison
`TauCeti.cubicalToSingular` agree after augmentation in degree zero: both send a point cube to the
point. -/
theorem singularAugment_orderedTriangulationNatTrans (X : TopCat.{u})
    (x : ((rawCubicalChainComplex k).obj X).X 0) :
    singularAugment k X (((orderedTriangulationNatTrans k).app X).f 0 x) =
      singularAugment k X
        (((rawCubicalChainComplexπ k ≫ cubicalToSingular k).app X).f 0 x) := by
  refine (congrArg (singularAugment k X) (ConcreteCategory.congr_hom
    (CubicalChain.orderedTriangulationChainMap_f X (ModuleCat.of k k) 0) x)).trans
      ((LinearMap.congr_fun (singularAugment_nativeOrderedTriangulation (R := k) (X := X))
        x).trans ?_)
  rw [NatTrans.comp_app, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    singularAugment_cubicalToSingular]
  exact (NormalizedCubicalChain.augment_mk _ x).symm

/-- **The ordered triangulation is naturally homotopic to the acyclic-models comparison**: on raw
cubical chains, `CubicalChain.orderedTriangulationChainMap` is homotopic to the normalization
followed by `TauCeti.cubicalToSingular`, by a homotopy natural in the space
(`TauCeti.orderedTriangulationHomotopy_hom_naturality`). -/
def orderedTriangulationHomotopy (X : TopCat.{u}) :
    Homotopy ((orderedTriangulationNatTrans k).app X)
      ((rawCubicalChainComplexπ k ≫ cubicalToSingular k).app X) :=
  (rawCubicalModelPresentation k).homotopy (isAcyclicOn_singularChains cubeModel) _ _
    (singularAugment_orderedTriangulationNatTrans k) X

variable {k}

/-- The homotopy `TauCeti.orderedTriangulationHomotopy` is natural. -/
theorem orderedTriangulationHomotopy_hom_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (i j : ℕ) :
    ((rawCubicalChainComplex k).map f).f i ≫ (orderedTriangulationHomotopy k Y).hom i j =
      (orderedTriangulationHomotopy k X).hom i j ≫ ((singularChains k).map f).f j :=
  AcyclicModels.ModelPresentation.homotopy_hom_naturality _ _ _ _ _ f i j

variable (k) in
/-- **On homology the ordered triangulation is the cubical–simplicial comparison**: the map
induced by the triangulation of raw cubes is the normalization followed by the inverse of
`TauCeti.singularCubicalHomologyIso`. -/
theorem homologyMap_orderedTriangulationNatTrans_app (X : TopCat.{u}) (n : ℕ) :
    HomologicalComplex.homologyMap ((orderedTriangulationNatTrans k).app X) n =
      HomologicalComplex.homologyMap ((rawCubicalChainComplexπ k).app X) n ≫
        (singularCubicalHomologyIso k X n).inv := by
  rw [(orderedTriangulationHomotopy k X).homologyMap_eq, NatTrans.comp_app,
    HomologicalComplex.homologyMap_comp, singularCubicalHomologyIso_inv]

end TauCeti

namespace TopPair

open TauCeti

variable (k : Type u) [Ring k] {P : TopPair.{u}}

/-! ### The relative triangulation cycle of a cube -/

/-- The positive ordered triangulation of a singular cube of the ambient space of `P`, as a relative
singular chain. -/
def orderedChainOfCube {m : ℕ} (c : SingularCube P.fst m) :
    (P.singularChainComplex (ModuleCat.of k k)).X m :=
  (singularRelπ k P).f m ((SingularCube.orderedChain c (ModuleCat.of k k)).hom 1)

theorem orderedChainOfCube_def {m : ℕ} (c : SingularCube P.fst m) :
    orderedChainOfCube k c =
      (singularRelπ k P).f m ((SingularCube.orderedChain c (ModuleCat.of k k)).hom 1) :=
  (rfl)

variable {k}

/-- The triangulation of a cube with values in the subspace vanishes in relative chains. -/
theorem orderedChain_comp_singularRelπ_f_eq_zero {m : ℕ} {c : SingularCube P.fst m}
    (hc : range c ⊆ range P.map) :
    SingularCube.orderedChain c (ModuleCat.of k k) ≫ (singularRelπ k P).f m = 0 := by
  rw [singularRelπ_eq, SingularCube.orderedChain_eq_sum]
  refine (Preadditive.sum_comp _ _ _).trans (Finset.sum_eq_zero fun π _ ↦ ?_)
  rw [Units.smul_def]
  refine (Preadditive.zsmul_comp _ _ _).trans ((congrArg _ ?_).trans (zsmul_zero _))
  refine ιChainComplex_comp_singularChainComplexπ_eq_zero P _ _ ?_
  rw [Equiv.apply_symm_apply]
  rintro _ ⟨y, rfl⟩
  exact hc ⟨_, rfl⟩

/-- The triangulation of a cube with values in the subspace vanishes in relative chains. -/
theorem orderedChainOfCube_eq_zero {m : ℕ} {c : SingularCube P.fst m}
    (hc : range c ⊆ range P.map) : orderedChainOfCube k c = 0 :=
  ConcreteCategory.congr_hom (orderedChain_comp_singularRelπ_f_eq_zero hc) (1 : k)

/-- A face of a cube sending the boundary of the cube into the subspace has values in the
subspace. -/
private theorem range_face_subset {m : ℕ} {c : SingularCube P.fst (m + 1)}
    (hc : MapsTo c (Cube.boundary (Fin (m + 1))) (range P.map)) (i : Fin (m + 1)) {t : I}
    (ht : t = 0 ∨ t = 1) : range (SingularCube.face i t c) ⊆ range P.map := by
  rintro _ ⟨y, rfl⟩
  rw [SingularCube.face_apply]
  exact hc ⟨i, by simpa using ht⟩

/-- The triangulation of a cube sending the boundary of the cube into the subspace is a relative
cycle. -/
theorem d_orderedChainOfCube {m : ℕ} {c : SingularCube P.fst (m + 1)}
    (hc : MapsTo c (Cube.boundary (Fin (m + 1))) (range P.map)) :
    (P.singularChainComplex (ModuleCat.of k k)).d (m + 1) m (orderedChainOfCube k c) = 0 := by
  have h : SingularCube.orderedChain c (ModuleCat.of k k) ≫ (singularRelπ k P).f (m + 1) ≫
      (P.singularChainComplex (ModuleCat.of k k)).d (m + 1) m = 0 := calc
    _ = (SingularCube.orderedChain c (ModuleCat.of k k) ≫
          ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of k k)).d (m + 1) m) ≫
            (singularRelπ k P).f m :=
      (congrArg (_ ≫ ·) ((singularRelπ k P).comm (m + 1) m)).trans (Category.assoc _ _ _).symm
    _ = 0 := by
      rw [SingularCube.orderedChain_boundary]
      refine (Preadditive.sum_comp _ _ _).trans (Finset.sum_eq_zero fun i _ ↦ ?_)
      refine (Preadditive.zsmul_comp _ _ _).trans ((congrArg _
        ((Preadditive.sub_comp _ _ _).trans ?_)).trans (zsmul_zero _))
      rw [orderedChain_comp_singularRelπ_f_eq_zero (range_face_subset hc i (Or.inr rfl)),
        orderedChain_comp_singularRelπ_f_eq_zero (range_face_subset hc i (Or.inl rfl)), sub_zero]
  exact ConcreteCategory.congr_hom h (1 : k)

variable (k) in
/-- The positive ordered triangulation of a cube sending the boundary of the cube into the
subspace, as a relative singular cycle of `P`. -/
def orderedCycleOfCube {m : ℕ} (c : SingularCube P.fst (m + 1))
    (hc : MapsTo c (Cube.boundary (Fin (m + 1))) (range P.map)) :
    (P.singularChainComplex (ModuleCat.of k k)).cycles (m + 1) :=
  HomologicalComplex.moduleCatCyclesMk _ (orderedChainOfCube k c) m (by simp)
    (d_orderedChainOfCube hc)

@[simp]
theorem iCycles_orderedCycleOfCube {m : ℕ} (c : SingularCube P.fst (m + 1))
    (hc : MapsTo c (Cube.boundary (Fin (m + 1))) (range P.map)) :
    (P.singularChainComplex (ModuleCat.of k k)).iCycles (m + 1) (orderedCycleOfCube k c hc) =
      orderedChainOfCube k c :=
  HomologicalComplex.iCycles_moduleCatCyclesMk ..

/-- The natural homotopy `TauCeti.orderedTriangulationHomotopy` carries a cube with values in the
subspace to a chain vanishing in relative chains. -/
private theorem singularRelπ_orderedTriangulationHomotopy_eq_zero {m : ℕ}
    {c : SingularCube P.fst m} (hc : range c ⊆ range P.map) :
    (singularRelπ k P).f (m + 1)
      ((orderedTriangulationHomotopy k P.fst).hom m (m + 1) (rawCubicalChainOfCube c)) = 0 := by
  have hc' : ∀ x, c x ∈ range P.map := fun x ↦ hc ⟨x, rfl⟩
  -- The cube is the push-forward of its lift to the subspace.
  have hlift : rawCubicalChainOfCube (k := k) c =
      ((rawCubicalChainComplex k).map P.map).f m (rawCubicalChainOfCube (P.liftSnd c hc')) := by
    rw [rawCubicalChainComplex_map_f_rawCubicalChainOfCube]
    congr 1
    ext x
    exact (P.map_liftSnd c hc' x).symm
  have hnat := ConcreteCategory.congr_hom
    (orderedTriangulationHomotopy_hom_naturality (k := k) P.map m (m + 1))
    (rawCubicalChainOfCube (P.liftSnd c hc'))
  simp only [ModuleCat.comp_apply] at hnat
  have h0 : ((singularChains k).map P.map ≫ singularRelπ k P).f (m + 1) = 0 := by
    rw [singularRelπ_eq]
    exact congrArg (fun φ ↦ HomologicalComplex.Hom.f φ (m + 1))
      (chainComplexMap_comp_singularChainComplexπ P (ModuleCat.of k k))
  rw [hlift, hnat]
  exact ConcreteCategory.congr_hom h0 _

/-- **The relative triangulation cycle represents the cubical class**: for a cube `c` of the
ambient space of `P` sending the boundary of `Iᵐ⁺¹` into the subspace, the class of `c` in relative
cubical homology, read in relative singular homology, is `(-1) ^ (m + 1)` times the class of its
positive ordered triangulation. -/
theorem singularCubicalHomologyIso_inv_homologyπ_cubicalCycleOfCube {m : ℕ}
    (c : SingularCube P.fst (m + 1))
    (hc : MapsTo c (Cube.boundary (Fin (m + 1))) (range P.map)) :
    (singularCubicalHomologyIso k P (m + 1)).inv
        ((P.cubicalChainComplex k).homologyπ (m + 1) (cubicalCycleOfCube k c hc)) =
      (-1 : k) ^ (m + 1) •
        (P.singularChainComplex (ModuleCat.of k k)).homologyπ (m + 1)
          (orderedCycleOfCube k c hc) := by
  set H := orderedTriangulationHomotopy k P.fst
  set x := rawCubicalChainOfCube (k := k) c
  set π := singularRelπ k P
  -- The homotopy formula `T = d H + H d + G` in degree `m + 1`, followed by the quotient map.
  have hcomm : ((orderedTriangulationNatTrans k).app P.fst).f (m + 1) ≫ π.f (m + 1) =
      (((rawCubicalChainComplex k).obj P.fst).d (m + 1) m ≫ H.hom m (m + 1)) ≫ π.f (m + 1) +
        (H.hom (m + 1) (m + 2) ≫ π.f (m + 2)) ≫
          (P.singularChainComplex (ModuleCat.of k k)).d (m + 2) (m + 1) +
        ((rawCubicalChainComplexπ k ≫ cubicalToSingular k).app P.fst).f (m + 1) ≫ π.f (m + 1) := by
    rw [H.comm (m + 1), dNext_eq H.hom (show (ComplexShape.down ℕ).Rel (m + 1) m from rfl),
      prevD_eq H.hom (show (ComplexShape.down ℕ).Rel (m + 2) (m + 1) from rfl),
      Preadditive.add_comp, Preadditive.add_comp, Category.assoc (H.hom (m + 1) (m + 2)),
      Category.assoc (H.hom (m + 1) (m + 2)), π.comm]
  have hx := ConcreteCategory.congr_hom hcomm x
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply] at hx
  -- The term `H (d x)` is a combination of the homotopy on faces, which lie in the subspace.
  have hface : π.f (m + 1)
      (H.hom m (m + 1) (((rawCubicalChainComplex k).obj P.fst).d (m + 1) m x)) = 0 := by
    simp only [x, rawCubicalChainComplex_d_rawCubicalChainOfCube, map_sum, map_smul, map_sub]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [singularRelπ_orderedTriangulationHomotopy_eq_zero (range_face_subset hc i (Or.inl rfl)),
      singularRelπ_orderedTriangulationHomotopy_eq_zero (range_face_subset hc i (Or.inr rfl)),
      sub_zero, smul_zero]
  rw [hface, zero_add] at hx
  -- `(-1) ^ (m + 1)` times the triangulation is `T x`, and the cubical class is `G x`.
  have hT : (-1 : k) ^ (m + 1) • orderedChainOfCube k c =
      π.f (m + 1) (((orderedTriangulationNatTrans k).app P.fst).f (m + 1) x) := by
    rw [orderedTriangulationNatTrans_app_f_rawCubicalChainOfCube]
    exact (map_smul (π.f (m + 1)).hom _ _).symm
  have hG : (cubicalToSingularRel k P).f (m + 1) (cubicalChainOfCube k c) =
      π.f (m + 1) (((rawCubicalChainComplexπ k ≫ cubicalToSingular k).app P.fst).f (m + 1) x) := by
    rw [NatTrans.comp_app, HomologicalComplex.comp_f, ModuleCat.comp_apply,
      rawCubicalChainComplexπ_app_f_rawCubicalChainOfCube, cubicalChainOfCube_def,
      ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, π_cubicalToSingularRel,
      HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [singularCubicalHomologyIso_inv, ← ModuleCat.comp_apply,
    HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply, ← map_smul]
  refine HomologicalComplex.moduleCat_homologyπ_eq_of_iCycles_sub_eq_d _
    (-π.f (m + 2) (H.hom (m + 1) (m + 2) x)) ?_
  rw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, iCycles_cubicalCycleOfCube, map_smul,
    iCycles_orderedCycleOfCube, map_neg, hG, hT, hx]
  abel

end TopPair

namespace TauCeti

variable (k : Type u) [Ring k]

/-! ### The coordinate cube class -/

/-- The **coordinate cube class** `[Iᵐ⁺¹, ∂Iᵐ⁺¹]` in `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; k)`: the class of the
positive ordered triangulation of the identity cube, the signed sum over the coordinate orderings
of the simplices from the origin to the far vertex. With integer coefficients its chain is the
iterated shuffle product of the interval chain `t ↦ t` in coordinate order
(`TauCeti.iteratedIntegralShuffle_eq_orderedChain`). -/
def coordinateCubeClass (m : ℕ) :
    (cubeBoundaryPair.{u} (m + 1)).singularHomology (C := ModuleCat.{u} k) (ModuleCat.of k k)
      (m + 1) :=
  ((cubeBoundaryPair.{u} (m + 1)).singularChainComplex (ModuleCat.of k k)).homologyπ (m + 1)
    (TopPair.orderedCycleOfCube k
      (upCube.{u} (m + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1)).fst (m + 1))
      (mapsTo_upCube_boundary (m + 1)))

/-- The coordinate cube class is `(-1) ^ (m + 1)` times the cubical class of the identity cube. -/
theorem coordinateCubeClass_eq_neg_one_pow_smul (m : ℕ) :
    coordinateCubeClass k m =
      (-1 : k) ^ (m + 1) • (TopPair.singularCubicalHomologyIso k (cubeBoundaryPair.{u} (m + 1))
        (m + 1)).inv (((cubeBoundaryPair.{u} (m + 1)).cubicalChainComplex k).homologyπ (m + 1)
          (cubeBoundaryPairCycle k m)) := by
  have hz : cubeBoundaryPairCycle k m = TopPair.cubicalCycleOfCube k
      (upCube.{u} (m + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1)).fst (m + 1))
      (mapsTo_upCube_boundary (m + 1)) :=
    HomologicalComplex.moduleCat_iCycles_injective _ (m + 1)
      ((iCycles_cubeBoundaryPairCycle k m).trans (TopPair.iCycles_cubicalCycleOfCube ..).symm)
  have h := congrArg ((-1 : k) ^ (m + 1) • ·)
    (TopPair.singularCubicalHomologyIso_inv_homologyπ_cubicalCycleOfCube (k := k)
      (P := cubeBoundaryPair.{u} (m + 1)) _ (mapsTo_upCube_boundary (m + 1)))
  have hε : (-1 : k) ^ (m + 1) * (-1) ^ (m + 1) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨m + 1, rfl⟩
  rw [hz]
  -- The ambient space of the cube pair is the cube model only up to unfolding `Arrow.mk`, so the
  -- relative formula is combined with equations rather than rewritten.
  exact (h.trans ((smul_smul _ _ _).trans
    ((congrArg (fun a : k ↦ a • coordinateCubeClass k m) hε).trans (one_smul k _)))).symm

/-- **The coordinate of the cube class**: under `TauCeti.singularHomologyCubeBoundaryPairIso`, the
coordinate cube class of `Iⁿ`, `n = m + 1`, is `(-1) ^ (n (n + 1) / 2)`. -/
theorem singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass (m : ℕ) :
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (m + 1)).hom (coordinateCubeClass k m) =
      (-1 : k) ^ ((m + 1) * (m + 2) / 2) := by
  rw [coordinateCubeClass_eq_neg_one_pow_smul, map_smul,
    singularHomologyCubeBoundaryPairIso_hom_cubeBoundaryPairCycle, smul_eq_mul, ← pow_add]
  congr 1
  have h : (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1) := by ring
  rw [h, Nat.add_mul_div_left _ _ two_pos, add_comm]

/-- The selected generator of `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; k)` is `(-1) ^ ((m + 1) (m + 2) / 2)` times the
coordinate cube class. -/
theorem singularHomologyCubeBoundaryPairIso_inv_apply_one (m : ℕ) :
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (m + 1)).inv (1 : k) =
      (-1 : k) ^ ((m + 1) * (m + 2) / 2) • coordinateCubeClass k m := by
  apply (ModuleCat.mono_iff_injective
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (m + 1)).hom).1 inferInstance
  rw [ModuleCat.hom_inv_apply, map_smul,
    singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass, smul_eq_mul, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow]

/-- **The coordinate cube class generates**: `a ↦ a • [Iᵐ⁺¹, ∂Iᵐ⁺¹]` is a bijection from `k` onto
`Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; k)`. -/
theorem bijective_smul_coordinateCubeClass (m : ℕ) :
    Function.Bijective fun a : k ↦ a • coordinateCubeClass k m := by
  set e := singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (m + 1)
  set ε : k := (-1) ^ ((m + 1) * (m + 2) / 2)
  have hε : ε * ε = 1 := by rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have he : ∀ a : k, e.hom (a • coordinateCubeClass k m) = a * ε := fun a ↦ by
    rw [map_smul, singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass, smul_eq_mul]
  refine ⟨fun a b hab ↦ ?_, fun z ↦ ⟨e.hom z * ε, ?_⟩⟩
  · have h := congrArg (· * ε) ((he a).symm.trans ((congrArg e.hom hab).trans (he b)))
    simpa only [mul_assoc, hε, mul_one] using h
  · apply (ModuleCat.mono_iff_injective e.hom).1 inferInstance
    rw [he, mul_assoc, hε, mul_one]

/-- In dimension one the coordinate cube class is the class of the singular simplex `t ↦ t`, whose
boundary is `[1] - [0]` (`TauCeti.cubeRelClass_singularHomologyδ`). -/
theorem coordinateCubeClass_zero :
    coordinateCubeClass k 0 = (cubeRelClass.{u} (ModuleCat.of k k)).hom (1 : k) := by
  apply (ModuleCat.mono_iff_injective
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) 1).hom).1 inferInstance
  have h := congrArg (fun φ ↦ ((singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) 1).hom)
    (φ.hom (1 : k))) (singularHomologyCubeBoundaryPairIso_one_inv (ModuleCat.of k k))
  simp only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg] at h
  rw [singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass, ← neg_eq_iff_eq_neg.2 h]
  norm_num

end TauCeti
