/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Triangulation.Chains
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic

/-!
# The ordered triangulation and the cubical–simplicial comparison

The sign-corrected ordered triangulation of raw cubical chains,
`CubicalChain.orderedTriangulationChainMap`, and the normalization followed by the acyclic-models
comparison `TauCeti.cubicalToSingular` are two natural chain maps from the raw cubical chains
`TauCeti.rawCubicalChainComplex k` to the singular chains, agreeing on points. The raw cubical
chains are free on the cubes (`TauCeti.rawCubicalModelPresentation`), so the method of acyclic
models makes the two maps naturally homotopic (`TauCeti.orderedTriangulationHomotopy`), and they
agree on homology. By naturality the homotopy carries cubes of a subspace to chains of the subspace,
so for a pair `P` and a cube `c` sending the boundary of the cube into the subspace, the relative
triangulation cycle `TopPair.orderedCycleOfCube k c hc` represents `(-1) ^ (m + 1)` times the image
of the cubical class of `c` (`TopPair.singularCubicalHomologyIso_inv_homologyπ_cubicalCycleOfCube`).

## Main definitions

* `TauCeti.orderedTriangulationNatTrans k`: the ordered triangulation as a natural chain map.
* `TauCeti.orderedTriangulationHomotopy k X`: the natural homotopy from the triangulation to the
  normalization followed by `TauCeti.cubicalToSingular`.
* `TopPair.orderedCycleOfCube k c hc`: the triangulation of a cube sending the boundary of the cube
  into the subspace, as a relative singular cycle.

## Main results

* `TauCeti.homologyMap_orderedTriangulationNatTrans_app`: on homology the triangulation is the
  normalization followed by the inverse of `TauCeti.singularCubicalHomologyIso`.
* `TopPair.singularCubicalHomologyIso_inv_homologyπ_cubicalCycleOfCube`: the relative form.

## References

* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
* S. Eilenberg and S. Mac Lane, *Acyclic models*, Amer. J. Math. 75 (1953).
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open CategoryTheory Limits Set Finsupp
open scoped unitInterval

universe u

namespace TauCeti

variable (k : Type u) [Ring k]

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
  rw [rawCubicalChainOfCube_def]
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
      rw [orderedChain_comp_singularRelπ_f_eq_zero
          (range_subset_iff.2 (face_mem_range_map hc i (.inr rfl))),
        orderedChain_comp_singularRelπ_f_eq_zero
          (range_subset_iff.2 (face_mem_range_map hc i (.inl rfl))), sub_zero]
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
    rw [singularRelπ_orderedTriangulationHomotopy_eq_zero
        (range_subset_iff.2 (face_mem_range_map hc i (.inl rfl))),
      singularRelπ_orderedTriangulationHomotopy_eq_zero
        (range_subset_iff.2 (face_mem_range_map hc i (.inr rfl))),
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
