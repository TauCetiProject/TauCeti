/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.ExteriorPowerCoords
public import TauCeti.Topology.VectorBundle.FiniteRank.CoordinateFunctor
public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal

/-!
# Exterior powers of finite-rank bundle cores

The `j`th exterior power of a finite-rank core `A` of rank `r` is the core of rank `r.choose j`
with the same charts, whose transitions are the `j`th compound matrices of the transitions of `A`
(`ContinuousLinearMap.exteriorPowerCoords`): its fibre is `⋀^j` of the fibre of `A`, read in the
basis of wedges of standard basis vectors. This arises from the
continuous coordinate functor `TauCeti.CoordinateFunctor.exteriorPower 𝕜 j`, so it is a functor

* `FiniteRankBundleCore.exteriorPower 𝕜 B j : FiniteRankBundleCore 𝕜 B ⥤ FiniteRankBundleCore 𝕜 B`,

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
`FiniteRankBundleCore.det A = ⋀^r A`. It has rank one (`FiniteRankBundleCore.rank_det`), and its
transitions are multiplication by the determinants of the transitions of `A`
(`FiniteRankBundleCore.coordChange_det`).

For a Whitney sum `whitneySum A D`, the continuous coordinate Künneth inclusions and projections
`TauCeti.exteriorPower.piProdInlL` and `TauCeti.exteriorPower.piProdProjL` intertwine the compound
matrices of block-diagonal transitions with Kronecker products of compound matrices over the shared
intersected chart domains `A.core.baseSet c ∩ D.core.baseSet c`, yielding actual bundle morphisms
over an arbitrary topological base `B` and nontrivially normed field `𝕜` (with no completeness,
compactness or separation assumptions):

* `FiniteRankBundleCore.exteriorPowerWhitneyInl` and
  `FiniteRankBundleCore.exteriorPowerWhitneyProj`: the bidegree-`(p, q)` Künneth bundle inclusion
  and projection, natural in bundle morphisms on `A` and `D` and strictly compatible with pullback;
* `FiniteRankBundleCore.exteriorPowerWhitneyBicone`,
  `FiniteRankBundleCore.exteriorPowerWhitneyBiconeIsBilimit` and
  `FiniteRankBundleCore.exteriorPowerWhitneySumIso`: the bilimit bicone and categorical biproduct
  isomorphism `⋀^n (A ⊕ D) ≅ ⨁_{i : Fin (n + 1)} (⋀^i A ⊗ ⋀^(n - i) D)`;
* `FiniteRankBundleCore.exteriorPowerTopWhitneySumIso` and
  `FiniteRankBundleCore.detWhitneySumIso`: the top-degree and determinant-line isomorphisms
  `det (A ⊕ D) ≅ det A ⊗ det D`, together with strict pullback compatibility `pullback_det` and
  `pullbackFunctor_mapIso_exteriorPowerTopWhitneySumIso`;
* `FiniteRankBundleCore.exteriorPowerTwoWhitneySumIso` and
  `FiniteRankBundleCore.exteriorPowerTwoWhitneySumOfRankLeOneIso`: the concrete degree-two
  Whitney-sum decomposition `⋀^2 (A ⊕ D) ≅ ⋀^2 A ⊕ ((A ⊗ D) ⊕ ⋀^2 D)` and its specialization
  `⋀^2 (A ⊕ D) ≅ A ⊗ D` when `A` and `D` have rank at most `1` (in particular for line bundles).

These are the bundle operations and sum laws whose classes form `λ_t(E) = Σ [⋀^j E] tʲ` in
topological K-theory.

## References

* M. F. Atiyah, *K-Theory*, §1.2 and §3.1.
* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3.
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory VectorBundleCore

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
  constIso (fun _ => rfl) (exteriorPower.piOneContinuousEquiv 𝕜 A.rank)
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

/-- The determinant line of a finite-rank core of rank `r`: its exterior power `⋀^r A` in the top
degree, with fibres the top exterior powers of the fibres of `A`. -/
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

/-! ### Whitney-sum Künneth decomposition -/

private theorem fiberMap_sum {ι : Type*} {A D : FiniteRankBundleCore 𝕜 B}
    (s : Finset ι) (f : ι → (A ⟶ D)) (x : B) :
    (∑ i ∈ s, f i).fiberMap x = ∑ i ∈ s, (f i).fiberMap x :=
  map_sum
    ({ toFun := fun g : A ⟶ D ↦ g.fiberMap x
       map_zero' := CoordinateHom.fiberMap_zero x
       map_add' := fun g h ↦ fiberMap_add g h x } : (A ⟶ D) →+ _)
    f s

/-- The bidegree-`(p, q)` Künneth inclusion `(⋀^p A) ⊗ (⋀^q D) ⟶ ⋀^n (A ⊕ D)` of finite-rank
bundle cores for `p + q = n`, given on every fibre by `TauCeti.exteriorPower.piProdInlL`. -/
noncomputable def exteriorPowerWhitneyInl (A D : FiniteRankBundleCore 𝕜 B)
    (p q n : ℕ) (h : p + q = n) :
    (exteriorPower 𝕜 B p).obj A ⊗ (exteriorPower 𝕜 B q).obj D ⟶
      (exteriorPower 𝕜 B n).obj (whitneySum A D) :=
  constHom (fun _ ↦ le_rfl)
    (TauCeti.exteriorPower.piProdInlL 𝕜 A.rank D.rank p q n h)
    fun i j x _ _ ↦
      (TauCeti.exteriorPower.exteriorPowerCoords_splitCoords_comp_piProdInlL
        (A.core.coordChange i j x) (D.core.coordChange i j x) p q n h).symm

/-- The bidegree-`(p, q)` Künneth projection `⋀^n (A ⊕ D) ⟶ (⋀^p A) ⊗ (⋀^q D)` of finite-rank
bundle cores, given on every fibre by `TauCeti.exteriorPower.piProdProjL`. It vanishes outside
total degree `p + q = n`. -/
noncomputable def exteriorPowerWhitneyProj (A D : FiniteRankBundleCore 𝕜 B) (p q n : ℕ) :
    (exteriorPower 𝕜 B n).obj (whitneySum A D) ⟶
      (exteriorPower 𝕜 B p).obj A ⊗ (exteriorPower 𝕜 B q).obj D :=
  constHom (fun _ ↦ le_rfl)
    (TauCeti.exteriorPower.piProdProjL 𝕜 A.rank D.rank p q n)
    fun i j x _ _ ↦
      TauCeti.exteriorPower.piProdProjL_comp_exteriorPowerCoords_splitCoords
        (A.core.coordChange i j x) (D.core.coordChange i j x) p q n

@[simp]
theorem fiberMap_exteriorPowerWhitneyInl (A D : FiniteRankBundleCore 𝕜 B)
    (p q n : ℕ) (h : p + q = n) (x : B) :
    (exteriorPowerWhitneyInl A D p q n h).fiberMap x =
      TauCeti.exteriorPower.piProdInlL 𝕜 A.rank D.rank p q n h :=
  fiberMap_constHom _ _ _ x

@[simp]
theorem fiberMap_exteriorPowerWhitneyProj (A D : FiniteRankBundleCore 𝕜 B)
    (p q n : ℕ) (x : B) :
    (exteriorPowerWhitneyProj A D p q n).fiberMap x =
      TauCeti.exteriorPower.piProdProjL 𝕜 A.rank D.rank p q n :=
  fiberMap_constHom _ _ _ x

/-- The Künneth projection is right inverse to the Künneth inclusion in matching bidegree. -/
@[reassoc (attr := simp)]
theorem exteriorPowerWhitneyInl_proj_self (A D : FiniteRankBundleCore 𝕜 B)
    (p q n : ℕ) (h : p + q = n) :
    exteriorPowerWhitneyInl A D p q n h ≫ exteriorPowerWhitneyProj A D p q n = 𝟙 _ :=
  hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_exteriorPowerWhitneyInl, fiberMap_exteriorPowerWhitneyProj,
      fiberMap_id]
    exact TauCeti.exteriorPower.piProdProjL_comp_piProdInlL_self A.rank D.rank p q n h

/-- The Künneth inclusion followed by the Künneth projection in a distinct bidegree vanishes. -/
@[reassoc]
theorem exteriorPowerWhitneyInl_proj_of_ne (A D : FiniteRankBundleCore 𝕜 B)
    {p' q' p q n : ℕ} (h : p + q = n) (hne : p ≠ p' ∨ q ≠ q') :
    exteriorPowerWhitneyInl A D p q n h ≫ exteriorPowerWhitneyProj A D p' q' n = 0 :=
  hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_exteriorPowerWhitneyInl, fiberMap_exteriorPowerWhitneyProj,
      CoordinateHom.fiberMap_zero]
    exact TauCeti.exteriorPower.piProdProjL_comp_piProdInlL_of_ne h hne

/-- The Künneth projection vanishes whenever `p + q ≠ n`. -/
theorem exteriorPowerWhitneyProj_eq_zero_of_add_ne (A D : FiniteRankBundleCore 𝕜 B)
    {p q n : ℕ} (h : p + q ≠ n) :
    exteriorPowerWhitneyProj A D p q n = 0 :=
  hom_ext fun x ↦ by
    rw [fiberMap_exteriorPowerWhitneyProj, CoordinateHom.fiberMap_zero]
    apply ContinuousLinearMap.coe_injective
    rw [TauCeti.exteriorPower.coe_piProdProjL, ContinuousLinearMap.toLinearMap_zero]
    exact TauCeti.exteriorPower.piProdProj_eq_zero_of_add_ne h

/-- Over `p + q = n`, the Künneth projections followed by the Künneth inclusions sum to the
identity of `⋀^n (A ⊕ D)`. -/
theorem sum_exteriorPowerWhitneyProj_comp_inl (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ) :
    ∑ i : Fin (n + 1),
      exteriorPowerWhitneyProj A D i (n - i) n ≫
        exteriorPowerWhitneyInl A D i (n - i) n (by omega) =
      𝟙 ((exteriorPower 𝕜 B n).obj (whitneySum A D)) :=
  hom_ext fun x ↦ by
    rw [fiberMap_sum, fiberMap_id]
    simp_rw [fiberMap_comp, fiberMap_exteriorPowerWhitneyProj, fiberMap_exteriorPowerWhitneyInl]
    exact TauCeti.exteriorPower.sum_piProdInlL_comp_piProdProjL A.rank D.rank n

/-- Naturality of the Künneth inclusion with respect to bundle morphisms on each summand. -/
@[reassoc]
theorem tensorHom_exteriorPowerWhitneyInl {A A' D D' : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ A') (g : D ⟶ D') (p q n : ℕ) (h : p + q = n) :
    ((exteriorPower 𝕜 B p).map f ⊗ₘ (exteriorPower 𝕜 B q).map g) ≫
        exteriorPowerWhitneyInl A' D' p q n h =
      exteriorPowerWhitneyInl A D p q n h ≫ (exteriorPower 𝕜 B n).map (whitneyMap f g) :=
  hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_comp, fiberMap_tensorHom_monoidal, fiberMap_exteriorPower_map,
      fiberMap_exteriorPower_map, fiberMap_exteriorPower_map, fiberMap_whitneyMap,
      fiberMap_exteriorPowerWhitneyInl, fiberMap_exteriorPowerWhitneyInl]
    exact (TauCeti.exteriorPower.exteriorPowerCoords_splitCoords_comp_piProdInlL
      (f.fiberMap x) (g.fiberMap x) p q n h).symm

/-- Naturality of the Künneth projection with respect to bundle morphisms on each summand. -/
@[reassoc]
theorem exteriorPower_map_whitneyMap_proj {A A' D D' : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ A') (g : D ⟶ D') (p q n : ℕ) :
    (exteriorPower 𝕜 B n).map (whitneyMap f g) ≫ exteriorPowerWhitneyProj A' D' p q n =
      exteriorPowerWhitneyProj A D p q n ≫
        ((exteriorPower 𝕜 B p).map f ⊗ₘ (exteriorPower 𝕜 B q).map g) :=
  hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_comp, fiberMap_exteriorPower_map, fiberMap_whitneyMap,
      fiberMap_tensorHom_monoidal, fiberMap_exteriorPower_map, fiberMap_exteriorPower_map,
      fiberMap_exteriorPowerWhitneyProj, fiberMap_exteriorPowerWhitneyProj]
    exact TauCeti.exteriorPower.piProdProjL_comp_exteriorPowerCoords_splitCoords
      (f.fiberMap x) (g.fiberMap x) p q n

/-- The `i`th Künneth summand `(⋀^i A) ⊗ (⋀^(n - i) D)` of `⋀^n (A ⊕ D)`. -/
noncomputable abbrev exteriorPowerWhitneySummand (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ)
    (i : Fin (n + 1)) : FiniteRankBundleCore 𝕜 B :=
  (exteriorPower 𝕜 B i).obj A ⊗ (exteriorPower 𝕜 B (n - i)).obj D

/-- The Künneth bicone exhibiting `⋀^n (A ⊕ D)` as a candidate biproduct of
`exteriorPowerWhitneySummand A D n`. -/
-- Expose the point projection so the types of the legs reduce to `⋀^n (whitneySum A D)`.
@[expose]
noncomputable def exteriorPowerWhitneyBicone (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ) :
    Bicone (exteriorPowerWhitneySummand A D n) where
  pt := (exteriorPower 𝕜 B n).obj (whitneySum A D)
  π i := exteriorPowerWhitneyProj A D i (n - i) n
  ι i := exteriorPowerWhitneyInl A D i (n - i) n (by omega)
  ι_π i j := by
    split_ifs with h
    · subst h
      simpa only [eqToHom_refl] using exteriorPowerWhitneyInl_proj_self A D i (n - i) n (by omega)
    · exact exteriorPowerWhitneyInl_proj_of_ne A D (by omega)
        (Or.inl fun hv ↦ h (Fin.ext hv))

@[simp]
theorem exteriorPowerWhitneyBicone_pt (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ) :
    (exteriorPowerWhitneyBicone A D n).pt = (exteriorPower 𝕜 B n).obj (whitneySum A D) :=
  (rfl)

@[simp]
theorem exteriorPowerWhitneyBicone_π (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ) (i : Fin (n + 1)) :
    (exteriorPowerWhitneyBicone A D n).π i = exteriorPowerWhitneyProj A D i (n - i) n :=
  (rfl)

@[simp]
theorem exteriorPowerWhitneyBicone_ι (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ) (i : Fin (n + 1)) :
    (exteriorPowerWhitneyBicone A D n).ι i =
      exteriorPowerWhitneyInl A D i (n - i) n (by omega) :=
  (rfl)

/-- The Künneth bicone is a bilimit: `⋀^n (A ⊕ D)` is both the product and the coproduct of the
summands `(⋀^i A) ⊗ (⋀^(n - i) D)` for `i : Fin (n + 1)`. -/
noncomputable def exteriorPowerWhitneyBiconeIsBilimit (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ) :
    (exteriorPowerWhitneyBicone A D n).IsBilimit :=
  isBilimitOfTotal _ (sum_exteriorPowerWhitneyProj_comp_inl A D n)

/-- The family `exteriorPowerWhitneySummand A D n` admits a categorical biproduct. Like
`TauCeti.hasFiniteBiproducts_of_hasBinaryBiproducts`, this is stated as a theorem rather than an
instance so that downstream constructions may use any chosen `HasFiniteBiproducts` structure. -/
theorem hasBiproduct_exteriorPowerWhitneySummand (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ) :
    HasBiproduct (exteriorPowerWhitneySummand A D n) :=
  hasBiproduct_of_total (exteriorPowerWhitneyBicone A D n)
    (sum_exteriorPowerWhitneyProj_comp_inl A D n)

/-- The Künneth isomorphism `⋀^n (A ⊕ D) ≅ ⨁_{i : Fin (n + 1)} (⋀^i A ⊗ ⋀^(n - i) D)` with any
categorical biproduct of `exteriorPowerWhitneySummand A D n`. -/
noncomputable def exteriorPowerWhitneySumIso (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ)
    [HasBiproduct (exteriorPowerWhitneySummand A D n)] :
    (exteriorPower 𝕜 B n).obj (whitneySum A D) ≅ ⨁ exteriorPowerWhitneySummand A D n :=
  biproduct.uniqueUpToIso _ (exteriorPowerWhitneyBiconeIsBilimit A D n)

@[reassoc (attr := simp)]
theorem exteriorPowerWhitneySumIso_hom_π (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ)
    [HasBiproduct (exteriorPowerWhitneySummand A D n)] (i : Fin (n + 1)) :
    (exteriorPowerWhitneySumIso A D n).hom ≫ biproduct.π (exteriorPowerWhitneySummand A D n) i =
      exteriorPowerWhitneyProj A D i (n - i) n :=
  biproduct.lift_π (exteriorPowerWhitneyBicone A D n).π i

@[reassoc (attr := simp)]
theorem ι_exteriorPowerWhitneySumIso_inv (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ)
    [HasBiproduct (exteriorPowerWhitneySummand A D n)] (i : Fin (n + 1)) :
    biproduct.ι (exteriorPowerWhitneySummand A D n) i ≫ (exteriorPowerWhitneySumIso A D n).inv =
      exteriorPowerWhitneyInl A D i (n - i) n (by omega) :=
  biproduct.ι_desc (exteriorPowerWhitneyBicone A D n).ι i

/-- Naturality of `exteriorPowerWhitneySumIso` with respect to `whitneyMap f g`. -/
@[reassoc]
theorem exteriorPower_map_whitneyMap_exteriorPowerWhitneySumIso_hom
    {A A' D D' : FiniteRankBundleCore 𝕜 B} (f : A ⟶ A') (g : D ⟶ D') (n : ℕ)
    [HasBiproduct (exteriorPowerWhitneySummand A D n)]
    [HasBiproduct (exteriorPowerWhitneySummand A' D' n)] :
    (exteriorPower 𝕜 B n).map (whitneyMap f g) ≫ (exteriorPowerWhitneySumIso A' D' n).hom =
      (exteriorPowerWhitneySumIso A D n).hom ≫
        biproduct.map fun i ↦ (exteriorPower 𝕜 B i).map f ⊗ₘ (exteriorPower 𝕜 B (n - i)).map g :=
  biproduct.hom_ext _ _ fun i ↦ by simp [exteriorPower_map_whitneyMap_proj]

/-! ### Top degree and determinant of a Whitney sum -/

private theorem exteriorPowerTop_hom_inv_id (A D : FiniteRankBundleCore 𝕜 B) :
    exteriorPowerWhitneyProj A D A.rank D.rank (A.rank + D.rank) ≫
        exteriorPowerWhitneyInl A D A.rank D.rank (A.rank + D.rank) rfl = 𝟙 _ :=
  hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_exteriorPowerWhitneyProj, fiberMap_exteriorPowerWhitneyInl,
      fiberMap_id]
    exact TauCeti.exteriorPower.piProdInlL_comp_piProdProjL_top A.rank D.rank

/-- In the top degree `A.rank + D.rank`, the single Künneth summand in bidegree `(A.rank, D.rank)`
gives an isomorphism `⋀^(A.rank + D.rank) (A ⊕ D) ≅ ⋀^A.rank A ⊗ ⋀^D.rank D`. -/
noncomputable def exteriorPowerTopWhitneySumIso (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPower 𝕜 B (A.rank + D.rank)).obj (whitneySum A D) ≅
      (exteriorPower 𝕜 B A.rank).obj A ⊗ (exteriorPower 𝕜 B D.rank).obj D where
  hom := exteriorPowerWhitneyProj A D A.rank D.rank (A.rank + D.rank)
  inv := exteriorPowerWhitneyInl A D A.rank D.rank (A.rank + D.rank) rfl
  hom_inv_id := exteriorPowerTop_hom_inv_id A D
  inv_hom_id := exteriorPowerWhitneyInl_proj_self A D A.rank D.rank (A.rank + D.rank) rfl

@[simp]
theorem exteriorPowerTopWhitneySumIso_hom (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerTopWhitneySumIso A D).hom =
      exteriorPowerWhitneyProj A D A.rank D.rank (A.rank + D.rank) :=
  (rfl)

@[simp]
theorem exteriorPowerTopWhitneySumIso_inv (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerTopWhitneySumIso A D).inv =
      exteriorPowerWhitneyInl A D A.rank D.rank (A.rank + D.rank) rfl :=
  (rfl)

/-- Naturality of `exteriorPowerTopWhitneySumIso` for endomorphisms of `A` and `D`. -/
@[reassoc]
theorem exteriorPower_map_whitneyMap_topWhitneySumIso_hom
    {A D : FiniteRankBundleCore 𝕜 B} (f : A ⟶ A) (g : D ⟶ D) :
    (exteriorPower 𝕜 B (A.rank + D.rank)).map (whitneyMap f g) ≫
        (exteriorPowerTopWhitneySumIso A D).hom =
      (exteriorPowerTopWhitneySumIso A D).hom ≫
        ((exteriorPower 𝕜 B A.rank).map f ⊗ₘ (exteriorPower 𝕜 B D.rank).map g) :=
  exteriorPower_map_whitneyMap_proj f g A.rank D.rank (A.rank + D.rank)

/-- The determinant line of a Whitney sum is canonically isomorphic to the tensor product of the
determinant lines of the summands. -/
@[expose]
noncomputable def detWhitneySumIso (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneySum A D).det ≅ A.det ⊗ D.det :=
  eqToIso (det_def (whitneySum A D)) ≪≫
    exteriorPowerTopWhitneySumIso A D ≪≫
    (eqToIso (det_def A).symm ⊗ᵢ eqToIso (det_def D).symm)

/-! ### Degree two and the line-bundle cross term -/

/-- `(⋀^n A) ⊗ (⋀^0 D)` is canonically isomorphic to `⋀^n A` via `exteriorPowerZeroIso D` and the
right unitor. -/
@[expose]
noncomputable def exteriorPowerRightZeroTensorIso (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ) :
    (exteriorPower 𝕜 B n).obj A ⊗ (exteriorPower 𝕜 B 0).obj D ≅ (exteriorPower 𝕜 B n).obj A :=
  (exteriorPower 𝕜 B n).obj A ◁ᵢ exteriorPowerZeroIso D ≪≫ ρ_ ((exteriorPower 𝕜 B n).obj A)

/-- `(⋀^0 A) ⊗ (⋀^n D)` is canonically isomorphic to `⋀^n D` via `exteriorPowerZeroIso A` and the
left unitor. -/
@[expose]
noncomputable def exteriorPowerLeftZeroTensorIso (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ) :
    (exteriorPower 𝕜 B 0).obj A ⊗ (exteriorPower 𝕜 B n).obj D ≅ (exteriorPower 𝕜 B n).obj D :=
  exteriorPowerZeroIso A ▷ᵢ (exteriorPower 𝕜 B n).obj D ≪≫ λ_ ((exteriorPower 𝕜 B n).obj D)

/-- `(⋀^1 A) ⊗ (⋀^1 D)` is canonically isomorphic to `A ⊗ D` via `exteriorPowerOneIso`. -/
@[expose]
noncomputable def exteriorPowerOneOneTensorIso (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPower 𝕜 B 1).obj A ⊗ (exteriorPower 𝕜 B 1).obj D ≅ A ⊗ D :=
  exteriorPowerOneIso A ⊗ᵢ exteriorPowerOneIso D

@[reassoc]
theorem exteriorPowerRightZeroTensorIso_hom_naturality
    {A A' D D' : FiniteRankBundleCore 𝕜 B} (f : A ⟶ A') (g : D ⟶ D') (n : ℕ) :
    ((exteriorPower 𝕜 B n).map f ⊗ₘ (exteriorPower 𝕜 B 0).map g) ≫
        (exteriorPowerRightZeroTensorIso A' D' n).hom =
      (exteriorPowerRightZeroTensorIso A D n).hom ≫ (exteriorPower 𝕜 B n).map f := by
  simp only [exteriorPowerRightZeroTensorIso, Iso.trans_hom, whiskerLeftIso_hom]
  rw [tensorHom_comp_whiskerLeft_assoc, exteriorPowerZeroIso_hom_naturality, tensorHom_def'_assoc]
  exact (congrArg (_ ≫ ·)
    (MonoidalCategory.rightUnitor_naturality ((exteriorPower 𝕜 B n).map f))).trans
    (Category.assoc _ _ _).symm

@[reassoc]
theorem exteriorPowerLeftZeroTensorIso_hom_naturality
    {A A' D D' : FiniteRankBundleCore 𝕜 B} (f : A ⟶ A') (g : D ⟶ D') (n : ℕ) :
    ((exteriorPower 𝕜 B 0).map f ⊗ₘ (exteriorPower 𝕜 B n).map g) ≫
        (exteriorPowerLeftZeroTensorIso A' D' n).hom =
      (exteriorPowerLeftZeroTensorIso A D n).hom ≫ (exteriorPower 𝕜 B n).map g := by
  simp only [exteriorPowerLeftZeroTensorIso, Iso.trans_hom, whiskerRightIso_hom]
  rw [tensorHom_comp_whiskerRight_assoc, exteriorPowerZeroIso_hom_naturality, tensorHom_def_assoc]
  exact (congrArg (_ ≫ ·)
    (MonoidalCategory.leftUnitor_naturality ((exteriorPower 𝕜 B n).map g))).trans
    (Category.assoc _ _ _).symm

@[reassoc]
theorem exteriorPowerOneOneTensorIso_hom_naturality
    {A A' D D' : FiniteRankBundleCore 𝕜 B} (f : A ⟶ A') (g : D ⟶ D') :
    ((exteriorPower 𝕜 B 1).map f ⊗ₘ (exteriorPower 𝕜 B 1).map g) ≫
        (exteriorPowerOneOneTensorIso A' D').hom =
      (exteriorPowerOneOneTensorIso A D).hom ≫ (f ⊗ₘ g) := by
  simp only [exteriorPowerOneOneTensorIso, tensorIso_hom, MonoidalCategory.tensorHom_comp_tensorHom,
    exteriorPowerOneIso_hom_naturality]

private theorem exteriorPowerTwo_total (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerWhitneyProj A D 2 0 2 ≫ (exteriorPowerRightZeroTensorIso A D 2).hom) ≫
        ((exteriorPowerRightZeroTensorIso A D 2).inv ≫ exteriorPowerWhitneyInl A D 2 0 2 rfl) +
      ((exteriorPowerWhitneyProj A D 1 1 2 ≫ (exteriorPowerOneOneTensorIso A D).hom) ≫
        ((exteriorPowerOneOneTensorIso A D).inv ≫ exteriorPowerWhitneyInl A D 1 1 2 rfl) +
      (exteriorPowerWhitneyProj A D 0 2 2 ≫ (exteriorPowerLeftZeroTensorIso A D 2).hom) ≫
        ((exteriorPowerLeftZeroTensorIso A D 2).inv ≫ exteriorPowerWhitneyInl A D 0 2 2 rfl)) =
      𝟙 ((exteriorPower 𝕜 B 2).obj (whitneySum A D)) := by
  have hsum := sum_exteriorPowerWhitneyProj_comp_inl A D 2
  rw [Fin.sum_univ_three] at hsum
  dsimp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at hsum
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← hsum]
  abel

private theorem exteriorPowerTwo_hom_inv_id (A D : FiniteRankBundleCore 𝕜 B) :
    whitneyLift
        (exteriorPowerWhitneyProj A D 2 0 2 ≫ (exteriorPowerRightZeroTensorIso A D 2).hom)
        (whitneyLift
          (exteriorPowerWhitneyProj A D 1 1 2 ≫ (exteriorPowerOneOneTensorIso A D).hom)
          (exteriorPowerWhitneyProj A D 0 2 2 ≫ (exteriorPowerLeftZeroTensorIso A D 2).hom)) ≫
      whitneyDesc
        ((exteriorPowerRightZeroTensorIso A D 2).inv ≫ exteriorPowerWhitneyInl A D 2 0 2 rfl)
        (whitneyDesc
          ((exteriorPowerOneOneTensorIso A D).inv ≫ exteriorPowerWhitneyInl A D 1 1 2 rfl)
          ((exteriorPowerLeftZeroTensorIso A D 2).inv ≫ exteriorPowerWhitneyInl A D 0 2 2 rfl)) =
      𝟙 ((exteriorPower 𝕜 B 2).obj (whitneySum A D)) := by
  rw [whitneyLift_desc, whitneyLift_desc]
  exact exteriorPowerTwo_total A D

private theorem exteriorPowerTwo_inv_hom_id (A D : FiniteRankBundleCore 𝕜 B) :
    whitneyDesc
        ((exteriorPowerRightZeroTensorIso A D 2).inv ≫ exteriorPowerWhitneyInl A D 2 0 2 rfl)
        (whitneyDesc
          ((exteriorPowerOneOneTensorIso A D).inv ≫ exteriorPowerWhitneyInl A D 1 1 2 rfl)
          ((exteriorPowerLeftZeroTensorIso A D 2).inv ≫ exteriorPowerWhitneyInl A D 0 2 2 rfl)) ≫
      whitneyLift
        (exteriorPowerWhitneyProj A D 2 0 2 ≫ (exteriorPowerRightZeroTensorIso A D 2).hom)
        (whitneyLift
          (exteriorPowerWhitneyProj A D 1 1 2 ≫ (exteriorPowerOneOneTensorIso A D).hom)
          (exteriorPowerWhitneyProj A D 0 2 2 ≫ (exteriorPowerLeftZeroTensorIso A D 2).hom)) =
      𝟙 _ := by
  refine whitneySum_hom_ext' ?_ (whitneySum_hom_ext' ?_ ?_) <;>
    refine whitneySum_hom_ext ?_ (whitneySum_hom_ext ?_ ?_)
  · simp
  · simp [exteriorPowerWhitneyInl_proj_of_ne_assoc A D (p := 2) (q := 0) (p' := 1) (q' := 1) rfl
      (Or.inl (by decide))]
  · simp [exteriorPowerWhitneyInl_proj_of_ne_assoc A D (p := 2) (q := 0) (p' := 0) (q' := 2) rfl
      (Or.inl (by decide))]
  · simp [exteriorPowerWhitneyInl_proj_of_ne_assoc A D (p := 1) (q := 1) (p' := 2) (q' := 0) rfl
      (Or.inl (by decide))]
  · simp
  · simp [exteriorPowerWhitneyInl_proj_of_ne_assoc A D (p := 1) (q := 1) (p' := 0) (q' := 2) rfl
      (Or.inl (by decide))]
  · simp [exteriorPowerWhitneyInl_proj_of_ne_assoc A D (p := 0) (q := 2) (p' := 2) (q' := 0) rfl
      (Or.inl (by decide))]
  · simp [exteriorPowerWhitneyInl_proj_of_ne_assoc A D (p := 0) (q := 2) (p' := 1) (q' := 1) rfl
      (Or.inl (by decide))]
  · simp

/-- Concrete Whitney-sum decomposition of the second exterior power:
`⋀^2 (A ⊕ D) ≅ ⋀^2 A ⊕ ((A ⊗ D) ⊕ ⋀^2 D)`, retaining the mixed cross term `A ⊗ D`. -/
noncomputable def exteriorPowerTwoWhitneySumIso (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPower 𝕜 B 2).obj (whitneySum A D) ≅
      whitneySum ((exteriorPower 𝕜 B 2).obj A)
        (whitneySum (A ⊗ D) ((exteriorPower 𝕜 B 2).obj D)) where
  hom := whitneyLift
    (exteriorPowerWhitneyProj A D 2 0 2 ≫ (exteriorPowerRightZeroTensorIso A D 2).hom)
    (whitneyLift
      (exteriorPowerWhitneyProj A D 1 1 2 ≫ (exteriorPowerOneOneTensorIso A D).hom)
      (exteriorPowerWhitneyProj A D 0 2 2 ≫ (exteriorPowerLeftZeroTensorIso A D 2).hom))
  inv := whitneyDesc
    ((exteriorPowerRightZeroTensorIso A D 2).inv ≫ exteriorPowerWhitneyInl A D 2 0 2 rfl)
    (whitneyDesc
      ((exteriorPowerOneOneTensorIso A D).inv ≫ exteriorPowerWhitneyInl A D 1 1 2 rfl)
      ((exteriorPowerLeftZeroTensorIso A D 2).inv ≫ exteriorPowerWhitneyInl A D 0 2 2 rfl))
  hom_inv_id := exteriorPowerTwo_hom_inv_id A D
  inv_hom_id := exteriorPowerTwo_inv_hom_id A D

@[simp]
theorem exteriorPowerTwoWhitneySumIso_hom (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerTwoWhitneySumIso A D).hom =
      whitneyLift
        (exteriorPowerWhitneyProj A D 2 0 2 ≫ (exteriorPowerRightZeroTensorIso A D 2).hom)
        (whitneyLift
          (exteriorPowerWhitneyProj A D 1 1 2 ≫ (exteriorPowerOneOneTensorIso A D).hom)
          (exteriorPowerWhitneyProj A D 0 2 2 ≫ (exteriorPowerLeftZeroTensorIso A D 2).hom)) :=
  (rfl)

@[simp]
theorem exteriorPowerTwoWhitneySumIso_inv (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerTwoWhitneySumIso A D).inv =
      whitneyDesc
        ((exteriorPowerRightZeroTensorIso A D 2).inv ≫ exteriorPowerWhitneyInl A D 2 0 2 rfl)
        (whitneyDesc
          ((exteriorPowerOneOneTensorIso A D).inv ≫ exteriorPowerWhitneyInl A D 1 1 2 rfl)
          ((exteriorPowerLeftZeroTensorIso A D 2).inv ≫ exteriorPowerWhitneyInl A D 0 2 2 rfl)) :=
  (rfl)

/-- Naturality of `exteriorPowerTwoWhitneySumIso` with respect to bundle morphisms on `A` and
`D`. -/
@[reassoc]
theorem exteriorPower_map_whitneyMap_twoWhitneySumIso_hom
    {A A' D D' : FiniteRankBundleCore 𝕜 B} (f : A ⟶ A') (g : D ⟶ D') :
    (exteriorPower 𝕜 B 2).map (whitneyMap f g) ≫ (exteriorPowerTwoWhitneySumIso A' D').hom =
      (exteriorPowerTwoWhitneySumIso A D).hom ≫
        whitneyMap ((exteriorPower 𝕜 B 2).map f)
          (whitneyMap (f ⊗ₘ g) ((exteriorPower 𝕜 B 2).map g)) := by
  rw [exteriorPowerTwoWhitneySumIso_hom, exteriorPowerTwoWhitneySumIso_hom]
  refine whitneySum_hom_ext ?_ (whitneySum_hom_ext ?_ ?_)
  · simp only [Category.assoc, whitneyLift_fst, whitneyMap_fst, whitneyLift_fst_assoc,
      exteriorPower_map_whitneyMap_proj_assoc, exteriorPowerRightZeroTensorIso_hom_naturality]
  · simp only [Category.assoc, whitneyLift_snd, whitneyLift_fst, whitneyMap_snd,
      whitneyLift_snd_assoc, whitneyMap_fst, whitneyLift_fst_assoc,
      exteriorPower_map_whitneyMap_proj_assoc, exteriorPowerOneOneTensorIso_hom_naturality]
  · simp only [Category.assoc, whitneyLift_snd, whitneyMap_snd, whitneyLift_snd_assoc,
      exteriorPower_map_whitneyMap_proj_assoc, exteriorPowerLeftZeroTensorIso_hom_naturality]

private theorem exteriorPowerTwoOfRankLeOne_hom_inv_id
    {A D : FiniteRankBundleCore 𝕜 B} (hA : A.rank ≤ 1) (hD : D.rank ≤ 1) :
    (exteriorPowerWhitneyProj A D 1 1 2 ≫ (exteriorPowerOneOneTensorIso A D).hom) ≫
        ((exteriorPowerOneOneTensorIso A D).inv ≫ exteriorPowerWhitneyInl A D 1 1 2 rfl) =
      𝟙 ((exteriorPower 𝕜 B 2).obj (whitneySum A D)) := by
  have htotal := exteriorPowerTwo_total A D
  have hA0 : IsZero ((exteriorPower 𝕜 B 2).obj A) :=
    isZero_exteriorPower_obj (Nat.lt_succ_of_le hA)
  have hD0 : IsZero ((exteriorPower 𝕜 B 2).obj D) :=
    isZero_exteriorPower_obj (Nat.lt_succ_of_le hD)
  rw [hA0.eq_zero_of_tgt (exteriorPowerWhitneyProj A D 2 0 2 ≫ _), zero_comp, zero_add,
    hD0.eq_zero_of_tgt (exteriorPowerWhitneyProj A D 0 2 2 ≫ _), zero_comp, add_zero] at htotal
  exact htotal

/-- When `A` and `D` have rank at most `1` (in particular for line bundles), `⋀^2 A` and `⋀^2 D`
are zero objects and the second exterior power `⋀^2 (A ⊕ D)` is canonically isomorphic to the
cross term `A ⊗ D`. -/
noncomputable def exteriorPowerTwoWhitneySumOfRankLeOneIso
    {A D : FiniteRankBundleCore 𝕜 B} (hA : A.rank ≤ 1) (hD : D.rank ≤ 1) :
    (exteriorPower 𝕜 B 2).obj (whitneySum A D) ≅ A ⊗ D where
  hom := exteriorPowerWhitneyProj A D 1 1 2 ≫ (exteriorPowerOneOneTensorIso A D).hom
  inv := (exteriorPowerOneOneTensorIso A D).inv ≫ exteriorPowerWhitneyInl A D 1 1 2 rfl
  hom_inv_id := exteriorPowerTwoOfRankLeOne_hom_inv_id hA hD
  inv_hom_id := by simp

@[simp]
theorem exteriorPowerTwoWhitneySumOfRankLeOneIso_hom
    {A D : FiniteRankBundleCore 𝕜 B} (hA : A.rank ≤ 1) (hD : D.rank ≤ 1) :
    (exteriorPowerTwoWhitneySumOfRankLeOneIso hA hD).hom =
      exteriorPowerWhitneyProj A D 1 1 2 ≫ (exteriorPowerOneOneTensorIso A D).hom :=
  (rfl)

@[simp]
theorem exteriorPowerTwoWhitneySumOfRankLeOneIso_inv
    {A D : FiniteRankBundleCore 𝕜 B} (hA : A.rank ≤ 1) (hD : D.rank ≤ 1) :
    (exteriorPowerTwoWhitneySumOfRankLeOneIso hA hD).inv =
      (exteriorPowerOneOneTensorIso A D).inv ≫ exteriorPowerWhitneyInl A D 1 1 2 rfl :=
  (rfl)

/-- Naturality of the cross-term isomorphism `⋀^2 (A ⊕ D) ≅ A ⊗ D` for bundles of rank at most
`1`. -/
@[reassoc]
theorem exteriorPower_map_whitneyMap_twoWhitneySumOfRankLeOneIso_hom
    {A A' D D' : FiniteRankBundleCore 𝕜 B} (hA : A.rank ≤ 1) (hD : D.rank ≤ 1)
    (hA' : A'.rank ≤ 1) (hD' : D'.rank ≤ 1) (f : A ⟶ A') (g : D ⟶ D') :
    (exteriorPower 𝕜 B 2).map (whitneyMap f g) ≫
        (exteriorPowerTwoWhitneySumOfRankLeOneIso hA' hD').hom =
      (exteriorPowerTwoWhitneySumOfRankLeOneIso hA hD).hom ≫ (f ⊗ₘ g) := by
  rw [exteriorPowerTwoWhitneySumOfRankLeOneIso_hom, exteriorPowerTwoWhitneySumOfRankLeOneIso_hom,
    exteriorPower_map_whitneyMap_proj_assoc, exteriorPowerOneOneTensorIso_hom_naturality,
    Category.assoc]

/-! ### Pullback compatibility -/

section Pullback

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pulling back a determinant line bundle core gives the determinant of the pulled-back core. -/
@[simp]
theorem pullback_det (A : FiniteRankBundleCore 𝕜 Y) (φ : C(X, Y)) :
    A.det.pullback φ = (A.pullback φ).det := by
  rw [det_def, det_def, rank_pullback]
  rfl

/-- Pulling back commutes strictly with the Künneth bundle inclusions. -/
@[simp]
theorem pullbackMap_exteriorPowerWhitneyInl (A D : FiniteRankBundleCore 𝕜 Y)
    (p q n : ℕ) (h : p + q = n) (φ : C(X, Y)) :
    pullbackMap (exteriorPowerWhitneyInl A D p q n h) φ =
      exteriorPowerWhitneyInl (A.pullback φ) (D.pullback φ) p q n h :=
  hom_ext fun x ↦
    (fiberMap_pullbackMap _ φ x).trans
      ((fiberMap_exteriorPowerWhitneyInl A D p q n h (φ x)).trans
        (fiberMap_exteriorPowerWhitneyInl (A.pullback φ) (D.pullback φ) p q n h x).symm)

/-- Pulling back commutes strictly with the Künneth bundle projections. -/
@[simp]
theorem pullbackMap_exteriorPowerWhitneyProj (A D : FiniteRankBundleCore 𝕜 Y)
    (p q n : ℕ) (φ : C(X, Y)) :
    pullbackMap (exteriorPowerWhitneyProj A D p q n) φ =
      exteriorPowerWhitneyProj (A.pullback φ) (D.pullback φ) p q n :=
  hom_ext fun x ↦
    (fiberMap_pullbackMap _ φ x).trans
      ((fiberMap_exteriorPowerWhitneyProj A D p q n (φ x)).trans
        (fiberMap_exteriorPowerWhitneyProj (A.pullback φ) (D.pullback φ) p q n x).symm)

/-- Pulling back commutes strictly with `exteriorPowerTopWhitneySumIso`. -/
@[simp]
theorem pullbackFunctor_mapIso_exteriorPowerTopWhitneySumIso
    (A D : FiniteRankBundleCore 𝕜 Y) (φ : C(X, Y)) :
    (pullbackFunctor φ).mapIso (exteriorPowerTopWhitneySumIso A D) =
      exteriorPowerTopWhitneySumIso (A.pullback φ) (D.pullback φ) :=
  Iso.ext (pullbackMap_exteriorPowerWhitneyProj A D A.rank D.rank (A.rank + D.rank) φ)

end Pullback

end FiniteRankBundleCore
end TauCeti
