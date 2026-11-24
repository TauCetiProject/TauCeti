/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.ExteriorPowerCoords
public import TauCeti.Topology.VectorBundle.FiniteRank.CoordinateFunctor
public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Exterior powers of finite-rank bundle cores

The `j`th exterior power of a finite-rank core `A` of rank `r` is the core of rank `r.choose j`
with the same charts, whose transitions are the `j`th compound matrices of the transitions of `A`
(`ContinuousLinearMap.exteriorPowerCoords`): its fibre is `⋀^j` of the fibre of `A`, read in the
basis of wedges of standard basis vectors. This arises from the
continuous coordinate functor `TauCeti.CoordinateFunctor.exteriorPower 𝕜 j`, so it is a functor

* `FiniteRankBundleCore.exteriorPower B j : FiniteRankBundleCore 𝕜 B ⥤ FiniteRankBundleCore 𝕜 B`,

acting on bundle maps by taking compound matrices of their fibre maps. It sends trivial cores to
trivial cores (`TauCeti.CoordinateFunctor.mapCoreTrivialIso`) and commutes strictly with
pullback (`TauCeti.CoordinateFunctor.functor_comp_pullbackFunctor`).

In low degrees the exterior powers are identified explicitly:

* `FiniteRankBundleCore.exteriorPowerZeroIso`: `⋀^0 A` is the trivial line bundle, and every
  bundle map acts on it as the identity (`exteriorPowerZeroIso_hom_naturality`);
* `FiniteRankBundleCore.exteriorPowerOneNatIso`: `⋀^1` is naturally isomorphic to the identity
  functor;
* `FiniteRankBundleCore.isZero_exteriorPower_obj`: `⋀^j A` is a zero object when `j` exceeds the
  rank of `A`.

In the top degree, the rank `r` of `A`, the exterior power is the determinant line
`FiniteRankBundleCore.det A = ⋀^r A`. It has rank one (`FiniteRankBundleCore.rank_det`), its
transitions are multiplication by the determinants of the transitions of `A`
(`FiniteRankBundleCore.coordChange_det`), morphisms between cores of equal rank induce morphisms of
their determinant lines functorially (`FiniteRankBundleCore.detMap`,
`FiniteRankBundleCore.detIso`), `j`-tuples and `r`-tuples of sections assemble into exterior-power
and determinant sections (`FiniteRankBundleCore.wedgeSection`, `FiniteRankBundleCore.detSection`),
and objects, morphisms, and sections commute with pullback (`FiniteRankBundleCore.pullback_det`,
`FiniteRankBundleCore.pullbackMap_detMap`, `FiniteRankBundleCore.pullback_wedgeSection`,
`FiniteRankBundleCore.pullback_detSection`).

Twisting by a line bundle `L`, a core of rank one, multiplies the `j`th exterior power by the
`j`th tensor power of `L`: `FiniteRankBundleCore.exteriorPowerLineTensorIso` identifies
`⋀^j (L ⊗ E)` with `L^⊗j ⊗ ⋀^j E`, naturally in `E`
(`FiniteRankBundleCore.exteriorPowerLineTensorNatIso`). In the charts the transitions of `L` are
multiplication by scalars, and the `j`th compound matrix is homogeneous of degree `j`
(`ContinuousLinearMap.exteriorPowerCoords_smul`), so the isomorphism is a fixed reindexing of
coordinates on every fibre.

These are the bundle operations whose classes form the coefficients of `λ_t(E) = Σ [⋀^j E] tʲ`
in topological K-theory.

## References

* M. F. Atiyah, *K-Theory*, §1.2 and §3.1.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits

namespace TauCeti

namespace CoordinateFunctor

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

/-- The `j`th exterior power of coordinate spaces: `Fin n → 𝕜` is sent to the coordinates
`Fin (n.choose j) → 𝕜` of its `j`th exterior power, and operators to their compound matrices. -/
-- Expose the dimension function so that coordinate spaces of exterior powers reduce.
@[expose]
noncomputable def exteriorPower (j : ℕ) : CoordinateFunctor 𝕜 𝕜 where
  rank n := n.choose j
  map g := g.exteriorPowerCoords j
  continuous_map m n := ContinuousLinearMap.continuous_exteriorPowerCoords j m n
  map_id n := ContinuousLinearMap.exteriorPowerCoords_id j n
  map_comp g f := ContinuousLinearMap.exteriorPowerCoords_comp j g f

@[simp] theorem rank_exteriorPower (j n : ℕ) : (exteriorPower 𝕜 j).rank n = n.choose j := (rfl)

@[simp] theorem map_exteriorPower (j : ℕ) {m n : ℕ} (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    (exteriorPower 𝕜 j).map g = g.exteriorPowerCoords j := (rfl)

end CoordinateFunctor

namespace FiniteRankBundleCore

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable (B : Type u) [TopologicalSpace B]

variable (𝕜) in
/-- The `j`th exterior power of finite-rank bundle cores: a bundle of rank `r` is sent to the
bundle of rank `r.choose j` whose fibres are the `j`th exterior powers of the original fibres. -/
-- Expose the object map so that coordinate spaces of exterior powers reduce.
@[expose]
noncomputable def exteriorPower (j : ℕ) : FiniteRankBundleCore 𝕜 B ⥤ FiniteRankBundleCore 𝕜 B :=
  (CoordinateFunctor.exteriorPower 𝕜 j).functor B

variable {B}

theorem exteriorPower_obj (j : ℕ) (A : FiniteRankBundleCore 𝕜 B) :
    (exteriorPower 𝕜 B j).obj A = (CoordinateFunctor.exteriorPower 𝕜 j).mapCore A := (rfl)

@[simp] theorem rank_exteriorPower_obj (j : ℕ) (A : FiniteRankBundleCore 𝕜 B) :
    ((exteriorPower 𝕜 B j).obj A).rank = A.rank.choose j := (rfl)

@[simp] theorem localTriv_baseSet_exteriorPower_obj (j : ℕ) (A : FiniteRankBundleCore 𝕜 B)
    (i : B) : (((exteriorPower 𝕜 B j).obj A).core.localTriv i).baseSet = A.core.baseSet i := (rfl)

/-- The transitions of an exterior power are the compound matrices of the transitions. -/
@[simp] theorem coordChange_exteriorPower_obj (j : ℕ) (A : FiniteRankBundleCore 𝕜 B)
    (i i' x : B) :
    ((exteriorPower 𝕜 B j).obj A).core.coordChange i i' x =
      (A.core.coordChange i i' x).exteriorPowerCoords j := (rfl)

/-- On every fibre, the exterior power of a bundle map is the compound matrix of its fibre map. -/
@[simp] theorem fiberMap_exteriorPower_map (j : ℕ) {A D : FiniteRankBundleCore 𝕜 B} (f : A ⟶ D)
    (x : B) :
    ((exteriorPower 𝕜 B j).map f).fiberMap x = (f.fiberMap x).exteriorPowerCoords j :=
  CoordinateFunctor.fiberMap_mapHom _ f x

/-! ### Vanishing above the rank -/

/-- An exterior power of degree larger than the rank is a zero object. -/
theorem isZero_exteriorPower_obj {j : ℕ} {A : FiniteRankBundleCore 𝕜 B} (h : A.rank < j) :
    IsZero ((exteriorPower 𝕜 B j).obj A) :=
  isZero_of_rank_eq_zero _ (Nat.choose_eq_zero_of_lt h)

/-! ### Degree zero -/

/-- The bundle map from the degree-zero exterior power to the trivial line bundle, given by
`exteriorPower.piZeroContinuousEquiv` on every fibre. -/
private noncomputable def exteriorPowerZeroHom (A : FiniteRankBundleCore 𝕜 B) :
    (exteriorPower 𝕜 B 0).obj A ⟶ trivial 𝕜 B 1 :=
  constHom (fun _ => Set.subset_univ _)
    (exteriorPower.piZeroContinuousEquiv 𝕜 A.rank :
      (Fin (A.rank.choose 0) → 𝕜) →L[𝕜] (Fin 1 → 𝕜))
    -- The transitions of the trivial core are identities, stated on `Fin 1 → 𝕜`.
    fun _ _ _ _ _ => (exteriorPower.piZeroContinuousEquiv_comp_exteriorPowerCoords _).trans
      (ContinuousLinearMap.id_comp _).symm

private theorem fiberMap_exteriorPowerZeroHom (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (exteriorPowerZeroHom A).fiberMap x =
      (exteriorPower.piZeroContinuousEquiv 𝕜 A.rank :
        (Fin (A.rank.choose 0) → 𝕜) →L[𝕜] (Fin 1 → 𝕜)) :=
  fiberMap_constHom _ _ _ x

/-- The bundle map from the trivial line bundle to the degree-zero exterior power, given by the
inverse of `exteriorPower.piZeroContinuousEquiv` on every fibre. -/
private noncomputable def exteriorPowerZeroInv (A : FiniteRankBundleCore 𝕜 B) :
    trivial 𝕜 B 1 ⟶ (exteriorPower 𝕜 B 0).obj A where
  operator _ _ := ContinuousMap.const _
    ((exteriorPower.piZeroContinuousEquiv 𝕜 A.rank).symm :
      (Fin 1 → 𝕜) →L[𝕜] (Fin (A.rank.choose 0) → 𝕜))
  compatible _ _ j j' x _ _ _ _ v := by
    -- Every compound matrix of degree zero fixes the image of the inverse equivalence.
    apply (exteriorPower.piZeroContinuousEquiv 𝕜 A.rank).injective
    have h := congrArg (fun T => T ((exteriorPower.piZeroContinuousEquiv 𝕜 A.rank).symm v))
      (exteriorPower.piZeroContinuousEquiv_comp_exteriorPowerCoords (A.core.coordChange j j' x))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at h
    exact h

private theorem fiberMap_exteriorPowerZeroInv (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (exteriorPowerZeroInv A).fiberMap x =
      ((exteriorPower.piZeroContinuousEquiv 𝕜 A.rank).symm :
        (Fin 1 → 𝕜) →L[𝕜] (Fin (A.rank.choose 0) → 𝕜)) := by
  rw [VectorBundleCore.CoordinateHom.fiberMap_def]
  rfl

/-- The degree-zero exterior power of a bundle is the trivial line bundle. -/
noncomputable def exteriorPowerZeroIso (A : FiniteRankBundleCore 𝕜 B) :
    (exteriorPower 𝕜 B 0).obj A ≅ trivial 𝕜 B 1 where
  hom := exteriorPowerZeroHom A
  inv := exteriorPowerZeroInv A
  hom_inv_id := hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_exteriorPowerZeroHom, fiberMap_exteriorPowerZeroInv, fiberMap_id]
    exact (exteriorPower.piZeroContinuousEquiv 𝕜 A.rank).coe_symm_comp_coe
  inv_hom_id := hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_exteriorPowerZeroHom, fiberMap_exteriorPowerZeroInv, fiberMap_id]
    exact (exteriorPower.piZeroContinuousEquiv 𝕜 A.rank).coe_comp_coe_symm

@[simp] theorem fiberMap_exteriorPowerZeroIso_hom (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (exteriorPowerZeroIso A).hom.fiberMap x =
      (exteriorPower.piZeroContinuousEquiv 𝕜 A.rank :
        (Fin (A.rank.choose 0) → 𝕜) →L[𝕜] (Fin 1 → 𝕜)) :=
  fiberMap_exteriorPowerZeroHom A x

@[simp] theorem fiberMap_exteriorPowerZeroIso_inv (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (exteriorPowerZeroIso A).inv.fiberMap x =
      ((exteriorPower.piZeroContinuousEquiv 𝕜 A.rank).symm :
        (Fin 1 → 𝕜) →L[𝕜] (Fin (A.rank.choose 0) → 𝕜)) :=
  fiberMap_exteriorPowerZeroInv A x

/-- Every bundle map acts as the identity on degree-zero exterior powers. -/
@[reassoc (attr := simp)]
theorem exteriorPowerZeroIso_hom_naturality {A D : FiniteRankBundleCore 𝕜 B} (f : A ⟶ D) :
    (exteriorPower 𝕜 B 0).map f ≫ (exteriorPowerZeroIso D).hom = (exteriorPowerZeroIso A).hom :=
  hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_exteriorPower_map, fiberMap_exteriorPowerZeroIso_hom,
      fiberMap_exteriorPowerZeroIso_hom]
    -- The coordinate models of the exterior powers reduce to `Fin (_.choose 0) → 𝕜`.
    exact exteriorPower.piZeroContinuousEquiv_comp_exteriorPowerCoords _

/-! ### Degree one -/

/-- The degree-one exterior power of a bundle is the bundle itself. -/
noncomputable def exteriorPowerOneIso (A : FiniteRankBundleCore 𝕜 B) :
    (exteriorPower 𝕜 B 1).obj A ≅ A :=
  constIso (fun _ => subset_rfl) (exteriorPower.piOneContinuousEquiv 𝕜 A.rank)
    -- The transitions of the exterior power are compound matrices on `Fin (A.rank.choose 1) → 𝕜`.
    fun _ _ _ _ _ => exteriorPower.piOneContinuousEquiv_comp_exteriorPowerCoords _

@[simp] theorem fiberMap_exteriorPowerOneIso_hom (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (exteriorPowerOneIso A).hom.fiberMap x =
      (exteriorPower.piOneContinuousEquiv 𝕜 A.rank :
        (Fin (A.rank.choose 1) → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)) :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_exteriorPowerOneIso_inv (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (exteriorPowerOneIso A).inv.fiberMap x =
      ((exteriorPower.piOneContinuousEquiv 𝕜 A.rank).symm :
        (Fin A.rank → 𝕜) →L[𝕜] (Fin (A.rank.choose 1) → 𝕜)) :=
  fiberMap_constIso_inv _ _ _ x

/-- The identification of degree-one exterior powers is natural in bundle maps. -/
@[reassoc]
theorem exteriorPowerOneIso_hom_naturality {A D : FiniteRankBundleCore 𝕜 B} (f : A ⟶ D) :
    (exteriorPower 𝕜 B 1).map f ≫ (exteriorPowerOneIso D).hom =
      (exteriorPowerOneIso A).hom ≫ f :=
  hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_comp, fiberMap_exteriorPower_map,
      fiberMap_exteriorPowerOneIso_hom, fiberMap_exteriorPowerOneIso_hom]
    -- The coordinate models of the exterior powers reduce to `Fin (_.choose 1) → 𝕜`.
    exact exteriorPower.piOneContinuousEquiv_comp_exteriorPowerCoords _

variable (𝕜 B) in
/-- The degree-one exterior power functor is naturally isomorphic to the identity functor. -/
noncomputable def exteriorPowerOneNatIso :
    exteriorPower 𝕜 B 1 ≅ 𝟭 (FiniteRankBundleCore 𝕜 B) :=
  NatIso.ofComponents exteriorPowerOneIso exteriorPowerOneIso_hom_naturality

@[simp] theorem exteriorPowerOneNatIso_app (A : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerOneNatIso 𝕜 B).app A = exteriorPowerOneIso A := (rfl)

/-! ### The top degree -/

section TopDegree

variable {B : Type*} [TopologicalSpace B]

/-- The determinant line of a finite-rank core of rank `r`: its exterior power `⋀^r A` in the top
degree, with fibres the top exterior powers of the fibres of `A`. -/
-- Expose so the coordinate model and Hom types reduce to `(exteriorPower 𝕜 B A.rank).obj A`.
@[expose]
noncomputable def det (A : FiniteRankBundleCore 𝕜 B) : FiniteRankBundleCore 𝕜 B :=
  (exteriorPower 𝕜 B A.rank).obj A

/-- The determinant line is the exterior power in the degree of the rank. -/
theorem det_def (A : FiniteRankBundleCore 𝕜 B) : A.det = (exteriorPower 𝕜 B A.rank).obj A := (rfl)

/-- The determinant line has rank one. -/
@[simp] theorem rank_det (A : FiniteRankBundleCore 𝕜 B) : A.det.rank = 1 := by
  rw [det_def, rank_exteriorPower_obj, Nat.choose_self]

@[simp] theorem localTriv_baseSet_det (A : FiniteRankBundleCore 𝕜 B) (i : B) :
    (A.det.core.localTriv i).baseSet = A.core.baseSet i := (rfl)

/-- The transitions of the determinant line are multiplication by the determinants of the
transitions of the core. -/
@[simp] theorem coordChange_det (A : FiniteRankBundleCore 𝕜 B) (i i' x : B) :
    A.det.core.coordChange i i' x =
      (A.core.coordChange i i' x).det • ContinuousLinearMap.id 𝕜 (Fin A.det.rank → 𝕜) := by
  rw [det_def, coordChange_exteriorPower_obj]
  exact ContinuousLinearMap.exteriorPowerCoords_self _

/-- The determinant core of a bundle has transition scalar equal to the determinant of the
bundle transition in the preferred charts. -/
theorem coordChange_det_ofBundle (n : ℕ) (E : B → Type*)
    [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (Bundle.TotalSpace (Fin n → 𝕜) E)]
    [FiberBundle (Fin n → 𝕜) E] [VectorBundle 𝕜 (Fin n → 𝕜) E] (i i' x : B) :
    (ofBundle 𝕜 n E).det.core.coordChange i i' x =
      ((trivializationAt (Fin n → 𝕜) E i).coordChangeL 𝕜
        (trivializationAt (Fin n → 𝕜) E i') x : (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜)).det •
        ContinuousLinearMap.id 𝕜 _ := by
  rw [coordChange_det, core_ofBundle, pointIndexedCore_coordChange]

/-- Induced morphism between determinant line bundles of two finite-rank cores of equal rank:
the top exterior power `(exteriorPower 𝕜 B A.rank).map a` followed by transport along `hr`. -/
noncomputable def detMap {A D : FiniteRankBundleCore 𝕜 B} (a : A ⟶ D) (hr : A.rank = D.rank) :
    A.det ⟶ D.det :=
  (exteriorPower 𝕜 B A.rank).map a ≫ eqToHom (congrArg (fun r ↦ (exteriorPower 𝕜 B r).obj D) hr)

/-- On an endomorphism `a : A ⟶ A`, `detMap a rfl` is `(exteriorPower 𝕜 B A.rank).map a`. -/
@[simp] theorem detMap_self {A : FiniteRankBundleCore 𝕜 B} (a : A ⟶ A) :
    detMap a rfl = (exteriorPower 𝕜 B A.rank).map a :=
  Category.comp_id _

/-- On every fibre, `detMap a rfl` acts on `A.det` as scalar multiplication by
`(a.fiberMap x).det`. -/
theorem fiberMap_detMap_self {A : FiniteRankBundleCore 𝕜 B} (a : A ⟶ A) (x : B) :
    (detMap a rfl).fiberMap x =
      (a.fiberMap x).det • ContinuousLinearMap.id 𝕜 (Fin A.det.rank → 𝕜) :=
  (congrArg (fun m ↦ m.fiberMap x) (detMap_self a)).trans
    ((fiberMap_exteriorPower_map A.rank a x).trans
      (ContinuousLinearMap.exteriorPowerCoords_self (a.fiberMap x)))

/-- `detMap` preserves identity bundle morphisms. -/
theorem detMap_id (A : FiniteRankBundleCore 𝕜 B) :
    detMap (𝟙 A) rfl = 𝟙 A.det :=
  (detMap_self (𝟙 A)).trans ((exteriorPower 𝕜 B A.rank).map_id A)

/-- `detMap` preserves composition of bundle morphisms between cores of equal rank. -/
@[simp] theorem detMap_comp {A D C : FiniteRankBundleCore 𝕜 B}
    (a : A ⟶ D) (b : D ⟶ C) (hr₁ : A.rank = D.rank) (hr₂ : D.rank = C.rank) :
    detMap (a ≫ b) (hr₁.trans hr₂) = detMap a hr₁ ≫ detMap b hr₂ := by
  have hnat : ∀ (r : ℕ) (h : r = D.rank),
      (exteriorPower 𝕜 B r).map b ≫
          eqToHom (congrArg (fun k ↦ (exteriorPower 𝕜 B k).obj C) (h.trans hr₂)) =
        eqToHom (congrArg (fun k ↦ (exteriorPower 𝕜 B k).obj D) h) ≫
          (exteriorPower 𝕜 B D.rank).map b ≫
          eqToHom (congrArg (fun k ↦ (exteriorPower 𝕜 B k).obj C) hr₂) := by
    rintro _ rfl
    simp only [eqToHom_refl, Category.id_comp]
  dsimp only [det, detMap]
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hnat A.rank hr₁, Category.assoc]

/-- On total spaces, `detMap a hr` factors as `(exteriorPower 𝕜 B A.rank).map a` followed by
`eqToHom` along `hr`. -/
theorem totalSpaceMap_detMap {A D : FiniteRankBundleCore 𝕜 B}
    (a : A ⟶ D) (hr : A.rank = D.rank) :
    (detMap a hr).totalSpaceMap =
      (eqToHom (congrArg (fun r ↦ (exteriorPower 𝕜 B r).obj D) hr)).totalSpaceMap ∘
        ((exteriorPower 𝕜 B A.rank).map a).totalSpaceMap := by
  dsimp +instances only [det, detMap]
  exact VectorBundleCore.CoordinateHom.totalSpaceMap_comp _ _

/-- If two bundle morphisms between cores of equal rank agree as coordinate operators on the fibres
over `x` and `y` respectively, their induced determinant morphisms agree there as well. -/
theorem fiberMap_detMap_eq_of_fiberMap_eq {A D : FiniteRankBundleCore 𝕜 B}
    {a b : A ⟶ D} (hr : A.rank = D.rank) {x y : B}
    (hxy : a.fiberMap x = b.fiberMap y) :
    (detMap a hr).fiberMap x = (detMap b hr).fiberMap y := by
  have heq : ∀ {C₁ C₂ : FiniteRankBundleCore 𝕜 B} (h : C₁ = C₂) (x y : B),
      (eqToHom h).fiberMap x = (eqToHom h).fiberMap y := by
    rintro _ _ rfl _ _
    rw [eqToHom_refl, fiberMap_id, fiberMap_id]
  dsimp +instances only [det, detMap]
  rw [fiberMap_comp, fiberMap_comp, heq _ x y,
    fiberMap_exteriorPower_map, fiberMap_exteriorPower_map, hxy]

/-- An isomorphism between finite-rank cores of equal rank induces an isomorphism of their
determinant line bundles. -/
noncomputable def detIso {A D : FiniteRankBundleCore 𝕜 B} (e : A ≅ D) (hr : A.rank = D.rank) :
      A.det ≅ D.det where
  hom := detMap e.hom hr
  inv := detMap e.inv hr.symm
  hom_inv_id := by rw [← detMap_comp, e.hom_inv_id, detMap_id]
  inv_hom_id := by rw [← detMap_comp, e.inv_hom_id, detMap_id]

@[simp] theorem detIso_hom {A D : FiniteRankBundleCore 𝕜 B} (e : A ≅ D) (hr : A.rank = D.rank) :
    (detIso e hr).hom = detMap e.hom hr := (rfl)

@[simp] theorem detIso_inv {A D : FiniteRankBundleCore 𝕜 B} (e : A ≅ D) (hr : A.rank = D.rank) :
    (detIso e hr).inv = detMap e.inv hr.symm := (rfl)

end TopDegree

/-! ### Twisting by a line bundle -/

section LineTensor

open MonoidalCategory ContinuousLinearMap ContinuousLinearEquiv

/-- For a line bundle `L`, the fibres of `⋀^j (L ⊗ E)` and `L^⊗j ⊗ ⋀^j E` have the same
dimension. -/
theorem choose_rank_mul_rank_of_rank_eq_one {L : FiniteRankBundleCore 𝕜 B} (hL : L.rank = 1)
    (E : FiniteRankBundleCore 𝕜 B) (j : ℕ) :
    (L.rank * E.rank).choose j = (tensorPow L j).rank * E.rank.choose j := by
  rw [rank_tensorPow_of_rank_eq_one hL, hL, one_mul, one_mul]

variable (j : ℕ) (L : FiniteRankBundleCore 𝕜 B)

/-- For a line bundle `L`, the `j`th exterior power of `L ⊗ E` is `L^⊗j ⊗ ⋀^j E`. On every fibre
the isomorphism reindexes the coordinates of the two spaces, both of dimension
`E.rank.choose j`: in the charts the transition maps of `L` are multiplication by scalars `c`, and
the `j`th compound matrix of `c • g` is `c ^ j` times the compound matrix of `g`. -/
noncomputable def exteriorPowerLineTensorIso (hL : L.rank = 1) (E : FiniteRankBundleCore 𝕜 B) :
    (exteriorPower 𝕜 B j).obj (L ⊗ E) ≅ tensorPow L j ⊗ (exteriorPower 𝕜 B j).obj E :=
  constIso (fun i ↦ Set.inter_subset_inter_left _ (baseSet_subset_baseSet_tensorPow L i j))
    (piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr (choose_rank_mul_rank_of_rank_eq_one hL E j)))
    fun i i' x _ _ ↦ by
      let : Unique (Fin L.rank) := ⟨⟨⟨0, by omega⟩⟩, fun k ↦ Fin.ext (by omega)⟩
      obtain ⟨c, hc⟩ : ∃ c : 𝕜, L.core.coordChange i i' x =
          c • ContinuousLinearMap.id 𝕜 (Fin L.rank → 𝕜) :=
        ⟨_, (L.core.coordChange i i' x).eq_smul_id_of_unique⟩
      simp only [coordChange_exteriorPower_obj, coordChange_tensorObj,
        coordChange_tensorPow_of_eq_smul_id L hc j, hc]
      exact piCongrLeft_comp_exteriorPowerCoords_kronecker j hL
        (rank_tensorPow_of_rank_eq_one hL j) _ _ _ _

@[simp] theorem fiberMap_exteriorPowerLineTensorIso_hom (hL : L.rank = 1)
    (E : FiniteRankBundleCore 𝕜 B) (x : B) :
    (exteriorPowerLineTensorIso j L hL E).hom.fiberMap x =
      ContinuousLinearEquiv.toContinuousLinearMap (piCongrLeft 𝕜 (fun _ ↦ 𝕜)
        (finCongr (choose_rank_mul_rank_of_rank_eq_one hL E j))) :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_exteriorPowerLineTensorIso_inv (hL : L.rank = 1)
    (E : FiniteRankBundleCore 𝕜 B) (x : B) :
    (exteriorPowerLineTensorIso j L hL E).inv.fiberMap x =
      ContinuousLinearEquiv.toContinuousLinearMap (piCongrLeft 𝕜 (fun _ ↦ 𝕜)
        (finCongr (choose_rank_mul_rank_of_rank_eq_one hL E j).symm)) :=
  (fiberMap_constIso_inv _ _ _ x).trans (congrArg _ (piCongrLeft_finCongr_symm _))

/-- The identification `⋀^j (L ⊗ E) ≅ L^⊗j ⊗ ⋀^j E` is natural in `E`. -/
@[reassoc]
theorem exteriorPowerLineTensorIso_hom_naturality (hL : L.rank = 1)
    {E E' : FiniteRankBundleCore 𝕜 B} (f : E ⟶ E') :
    (exteriorPower 𝕜 B j).map (L ◁ f) ≫ (exteriorPowerLineTensorIso j L hL E').hom =
      (exteriorPowerLineTensorIso j L hL E).hom ≫ tensorPow L j ◁ (exteriorPower 𝕜 B j).map f :=
  hom_ext fun x ↦ by
    have h := piCongrLeft_comp_exteriorPowerCoords_kronecker j hL
      (rank_tensorPow_of_rank_eq_one hL j) 1 (f.fiberMap x)
      (choose_rank_mul_rank_of_rank_eq_one hL E j) (choose_rank_mul_rank_of_rank_eq_one hL E' j)
    simp only [one_smul, one_pow] at h
    simp only [fiberMap_comp, fiberMap_exteriorPower_map, fiberMap_whiskerLeft,
      fiberMap_exteriorPowerLineTensorIso_hom]
    exact h

/-- For a line bundle `L`, the functors `E ↦ ⋀^j (L ⊗ E)` and `E ↦ L^⊗j ⊗ ⋀^j E` are naturally
isomorphic. -/
noncomputable def exteriorPowerLineTensorNatIso (hL : L.rank = 1) :
    tensorLeft L ⋙ exteriorPower 𝕜 B j ≅ exteriorPower 𝕜 B j ⋙ tensorLeft (tensorPow L j) :=
  NatIso.ofComponents (exteriorPowerLineTensorIso j L hL)
    (exteriorPowerLineTensorIso_hom_naturality j L hL)

@[simp] theorem exteriorPowerLineTensorNatIso_app (hL : L.rank = 1)
    (E : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerLineTensorNatIso j L hL).app E = exteriorPowerLineTensorIso j L hL E := (rfl)

end LineTensor

/-! ### Pullback -/

section Pullback

variable {X : Type*} [TopologicalSpace X]

/-- Pulling back commutes strictly with exterior powers of finite-rank cores. -/
@[simp] theorem pullback_exteriorPower_obj (j : ℕ) (A : FiniteRankBundleCore 𝕜 B) (f : C(X, B)) :
    ((exteriorPower 𝕜 B j).obj A).pullback f = (exteriorPower 𝕜 X j).obj (A.pullback f) := (rfl)

/-- Pulling back commutes with the action of exterior powers on bundle maps. -/
@[simp] theorem pullbackMap_exteriorPower_map (j : ℕ) {A D : FiniteRankBundleCore 𝕜 B}
    (a : A ⟶ D) (f : C(X, B)) :
    pullbackMap ((exteriorPower 𝕜 B j).map a) f =
      (exteriorPower 𝕜 X j).map (pullbackMap a f) :=
  ((CoordinateFunctor.exteriorPower 𝕜 j).mapHom_pullbackMap a f).symm

/-- Exterior powers commute strictly with pullback as functors. -/
theorem exteriorPower_comp_pullbackFunctor (j : ℕ) (f : C(X, B)) :
    exteriorPower 𝕜 B j ⋙ pullbackFunctor f = pullbackFunctor f ⋙ exteriorPower 𝕜 X j :=
  (CoordinateFunctor.exteriorPower 𝕜 j).functor_comp_pullbackFunctor f

@[simp] theorem pullbackMap_exteriorPowerZeroIso_hom (A : FiniteRankBundleCore 𝕜 B)
    (f : C(X, B)) :
    pullbackMap (exteriorPowerZeroIso A).hom f = (exteriorPowerZeroIso (A.pullback f)).hom :=
  hom_ext fun x => by
    simp only [fiberMap_pullbackMap, fiberMap_exteriorPowerZeroIso_hom]
    -- `((exteriorPower 𝕜 B 0).obj A).pullback f` and `(trivial 𝕜 B 1).pullback f` coincide with
    -- `(exteriorPower 𝕜 X 0).obj (A.pullback f)` and `trivial 𝕜 X 1` at default transparency.
    exact (fiberMap_exteriorPowerZeroIso_hom (A.pullback f) x).symm

@[simp] theorem pullbackMap_exteriorPowerZeroIso_inv (A : FiniteRankBundleCore 𝕜 B)
    (f : C(X, B)) :
    pullbackMap (exteriorPowerZeroIso A).inv f = (exteriorPowerZeroIso (A.pullback f)).inv :=
  hom_ext fun x => by
    simp only [fiberMap_pullbackMap, fiberMap_exteriorPowerZeroIso_inv]
    exact (fiberMap_exteriorPowerZeroIso_inv (A.pullback f) x).symm

@[simp] theorem pullbackMap_exteriorPowerOneIso_hom (A : FiniteRankBundleCore 𝕜 B)
    (f : C(X, B)) :
    pullbackMap (exteriorPowerOneIso A).hom f = (exteriorPowerOneIso (A.pullback f)).hom :=
  pullbackMap_constIso_hom _ _ _ f

@[simp] theorem pullbackMap_exteriorPowerOneIso_inv (A : FiniteRankBundleCore 𝕜 B)
    (f : C(X, B)) :
    pullbackMap (exteriorPowerOneIso A).inv f = (exteriorPowerOneIso (A.pullback f)).inv :=
  pullbackMap_constIso_inv _ _ _ f

/-- Pulling back commutes strictly with forming the determinant line of a finite-rank core. -/
@[simp] theorem pullback_det (A : FiniteRankBundleCore 𝕜 B) (f : C(X, B)) :
    A.det.pullback f = (A.pullback f).det := (rfl)

/-- Pulling back commutes with the induced morphism on determinant line bundles. -/
@[simp] theorem pullbackMap_detMap {A D : FiniteRankBundleCore 𝕜 B}
    (a : A ⟶ D) (hr : A.rank = D.rank) (f : C(X, B)) :
    pullbackMap (detMap a hr) f = detMap (pullbackMap a f) hr := by
  have hmap : pullbackMap ((exteriorPower 𝕜 B A.rank).map a) f =
      (exteriorPower 𝕜 X (A.pullback f).rank).map (pullbackMap a f) :=
    ((CoordinateFunctor.exteriorPower 𝕜 A.rank).mapHom_pullbackMap a f).symm
  have heq : pullbackMap
      (eqToHom (congrArg (fun r ↦ (exteriorPower 𝕜 B r).obj D) hr)) f =
      eqToHom (congrArg (fun r ↦ (exteriorPower 𝕜 X r).obj (D.pullback f)) hr) :=
    eqToHom_map (pullbackFunctor f) _
  dsimp only [det, detMap]
  rw [pullbackMap_comp, hmap, heq]
  rfl

end Pullback

section Sections

/-- The exterior product `s 0 ∧ ⋯ ∧ s (j - 1)` of `j` sections of `A`, as a section of
`(exteriorPower 𝕜 B j).obj A` in the standard coordinates `exteriorPower.piEquiv`. -/
noncomputable def wedgeSection (j : ℕ) (A : FiniteRankBundleCore 𝕜 B)
    (s : Fin j → ∀ x, A.core.Fiber x) (x : B) :
    ((exteriorPower 𝕜 B j).obj A).core.Fiber x :=
  exteriorPower.piEquiv 𝕜 A.rank j (exteriorPower.ιMulti 𝕜 j fun k ↦ s k x)

/-- The determinant wedge `s 0 ∧ ⋯ ∧ s (A.rank - 1)` of `A.rank` sections of `A`, as a section of
the determinant line bundle `A.det`. -/
@[expose]
noncomputable def detSection (A : FiniteRankBundleCore 𝕜 B)
    (s : Fin A.rank → ∀ x, A.core.Fiber x) (x : B) : A.det.core.Fiber x :=
  wedgeSection A.rank A s x

theorem detSection_def (A : FiniteRankBundleCore 𝕜 B) (s : Fin A.rank → ∀ x, A.core.Fiber x) :
    detSection A s = wedgeSection A.rank A s := (rfl)

/-- `(exteriorPower 𝕜 B j).map f` acts on `wedgeSection` by applying `f.fiberMap` to each factor. -/
theorem fiberMap_exteriorPower_map_wedgeSection (j : ℕ) {A D : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ D) (s : Fin j → ∀ x, A.core.Fiber x) (x : B) :
    ((exteriorPower 𝕜 B j).map f).fiberMap x (wedgeSection j A s x) =
      wedgeSection j D (fun k y ↦ f.fiberMap y (s k y)) x := by
  rw [fiberMap_exteriorPower_map]
  exact ContinuousLinearMap.exteriorPowerCoords_piEquiv_ιMulti j (f.fiberMap x) (fun k ↦ s k x)

/-- `detMap f hr` acts on `detSection` by applying `f.fiberMap` to each factor across `hr`. -/
@[simp] theorem fiberMap_detMap_detSection {A D : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ D) (hr : A.rank = D.rank) (s : Fin A.rank → ∀ x, A.core.Fiber x) (x : B) :
    (detMap f hr).fiberMap x (detSection A s x) =
      detSection D (fun k y ↦ f.fiberMap y (s (Fin.cast hr.symm k) y)) x := by
  have key : ∀ (r : ℕ) (h : r = D.rank) (t : Fin r → ∀ y, D.core.Fiber y),
      (eqToHom (congrArg (fun l ↦ (exteriorPower 𝕜 B l).obj D) h)).fiberMap x
          (wedgeSection r D t x) =
        wedgeSection D.rank D (fun k y ↦ t (Fin.cast h.symm k) y) x := by
    rintro _ rfl t
    rw [eqToHom_refl, fiberMap_id]
    rfl
  dsimp +instances only [det, detMap, detSection]
  rw [fiberMap_comp]
  change (eqToHom (congrArg (fun l ↦ (exteriorPower 𝕜 B l).obj D) hr)).fiberMap x
      (((exteriorPower 𝕜 B A.rank).map f).fiberMap x (wedgeSection A.rank A s x)) = _
  rw [fiberMap_exteriorPower_map_wedgeSection]
  exact key A.rank hr (fun k y ↦ f.fiberMap y (s k y))

/-- In chart `i` of `(exteriorPower 𝕜 B j).obj A`, the fibre coordinate of `wedgeSection` is the
exterior product in coordinates of the chart coordinates of the factor sections. -/
theorem localTriv_wedgeSection_snd (j : ℕ) (A : FiniteRankBundleCore 𝕜 B)
    (s : Fin j → ∀ x, A.core.Fiber x) (i x : B) :
    (((exteriorPower 𝕜 B j).obj A).core.localTriv i ⟨x, wedgeSection j A s x⟩).2 =
      exteriorPower.piEquiv 𝕜 A.rank j
        (exteriorPower.ιMulti 𝕜 j fun k ↦ (A.core.localTriv i ⟨x, s k x⟩).2) := by
  simp only [VectorBundleCore.localTriv_apply, indexAt_eq, coordChange_exteriorPower_obj]
  exact ContinuousLinearMap.exteriorPowerCoords_piEquiv_ιMulti j (A.core.coordChange x i x)
    (fun k ↦ s k x)

/-- The exterior product of `j` continuous sections of `A` is a continuous section of
`(exteriorPower 𝕜 B j).obj A`. -/
theorem continuous_wedgeSection (j : ℕ) (A : FiniteRankBundleCore 𝕜 B)
    {s : Fin j → ∀ x, A.core.Fiber x}
    (hs : ∀ k, Continuous fun x ↦ TotalSpace.mk' (Fin A.rank → 𝕜) x (s k x)) :
    Continuous fun x ↦
      TotalSpace.mk' (Fin ((exteriorPower 𝕜 B j).obj A).rank → 𝕜) x (wedgeSection j A s x) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  have hc (k : Fin j) :
      ContinuousAt (fun x ↦ (A.core.localTriv x₀ ⟨x, s k x⟩).2) x₀ := by
    have h := ((FiberBundle.continuousAt_totalSpace _ _).1 ((hs k).continuousAt (x := x₀))).2
    rwa [show (TotalSpace.mk' (Fin A.rank → 𝕜) x₀ (s k x₀)).proj = x₀ from rfl,
      A.trivializationAt_core x₀] at h
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  rw [show (TotalSpace.mk' (Fin ((exteriorPower 𝕜 B j).obj A).rank → 𝕜) x₀
    (wedgeSection j A s x₀)).proj = x₀ from rfl,
    ((exteriorPower 𝕜 B j).obj A).trivializationAt_core x₀]
  exact (((exteriorPower.contDiff_piEquiv_ιMulti 𝕜 j A.rank (k := 0)).continuous.continuousAt).comp
    (continuousAt_pi.2 hc)).congr
    (Filter.Eventually.of_forall fun x ↦ (localTriv_wedgeSection_snd j A s x₀ x).symm)

/-- The determinant wedge of `A.rank` continuous sections of `A` is a continuous section of
`A.det`. -/
theorem continuous_detSection (A : FiniteRankBundleCore 𝕜 B)
    {s : Fin A.rank → ∀ x, A.core.Fiber x}
    (hs : ∀ k, Continuous fun x ↦ TotalSpace.mk' (Fin A.rank → 𝕜) x (s k x)) :
    Continuous fun x ↦ TotalSpace.mk' (Fin A.det.rank → 𝕜) x (detSection A s x) :=
  continuous_wedgeSection A.rank A hs

/-- `wedgeSection j A s x` depends only on the values `s k x` of the factor sections over `x`. -/
theorem wedgeSection_congr {j : ℕ} {A : FiniteRankBundleCore 𝕜 B}
    {s₁ s₂ : Fin j → ∀ x, A.core.Fiber x} {x : B} (h : ∀ k, s₁ k x = s₂ k x) :
    wedgeSection j A s₁ x = wedgeSection j A s₂ x := by
  dsimp only [wedgeSection]
  congr 2
  exact funext h

/-- Evaluating `wedgeSection` on `A.pullback f` at `x` depends only on the fibre vectors `s k x`,
read in the fibre of `A` over `f x`. -/
theorem wedgeSection_pullback_apply {X : Type*} [TopologicalSpace X]
    (j : ℕ) (A : FiniteRankBundleCore 𝕜 B) (f : C(X, B))
    (s : Fin j → ∀ x, (A.pullback f).core.Fiber x) (x : X) :
    wedgeSection j (A.pullback f) s x = wedgeSection j A (fun k _ ↦ s k x) (f x) := (rfl)

/-- Pulling back sections commutes strictly with forming `wedgeSection`. -/
@[simp] theorem pullback_wedgeSection {X : Type*} [TopologicalSpace X]
    (j : ℕ) (A : FiniteRankBundleCore 𝕜 B) (f : C(X, B))
    (s : Fin j → ∀ y, A.core.Fiber y) :
    wedgeSection j (A.pullback f) (fun k x ↦ s k (f x)) =
      fun x ↦ wedgeSection j A s (f x) := (rfl)

/-- Pulling back sections commutes strictly with forming `detSection`. -/
@[simp] theorem pullback_detSection {X : Type*} [TopologicalSpace X]
    (A : FiniteRankBundleCore 𝕜 B) (f : C(X, B))
    (s : Fin A.rank → ∀ y, A.core.Fiber y) :
    detSection (A.pullback f) (fun k x ↦ s k (f x)) =
      fun x ↦ detSection A s (f x) := (rfl)

end Sections
end FiniteRankBundleCore
end TauCeti
