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
`TauCeti.exteriorPower.piProdInclL` and `TauCeti.exteriorPower.piProdProjL` intertwine the compound
matrices of block-diagonal transitions with Kronecker products of compound matrices over the shared
intersected chart domains `A.core.baseSet c ∩ D.core.baseSet c`, yielding actual bundle morphisms
over an arbitrary topological base `B` and nontrivially normed field `𝕜` (with no completeness,
compactness or separation assumptions):

* `FiniteRankBundleCore.exteriorPowerWhitneyIncl` and
  `FiniteRankBundleCore.exteriorPowerWhitneyProj`: the bidegree-`(p, q)` Künneth bundle inclusion
  and projection, natural in bundle morphisms on `A` and `D` and strictly compatible with pullback;
* `FiniteRankBundleCore.exteriorPowerWhitneyBicone`,
  `FiniteRankBundleCore.exteriorPowerWhitneyBiconeIsBilimit` and
  `FiniteRankBundleCore.exteriorPowerWhitneySumIso`: the bilimit bicone and categorical biproduct
  isomorphism `⋀^n (A ⊕ D) ≅ ⨁_{i : Fin (n + 1)} (⋀^i A ⊗ ⋀^(n - i) D)`;
* `FiniteRankBundleCore.exteriorPowerWhitneySumOfRankLeIso`,
  `FiniteRankBundleCore.exteriorPowerTopWhitneySumIso` and
  `FiniteRankBundleCore.detWhitneySumIso`: the rank-bounded Künneth isomorphism
  `⋀^n (A ⊕ D) ≅ ⋀^p A ⊗ ⋀^q D` when `A.rank ≤ p`, `D.rank ≤ q`, `p + q = n`, and its top-degree
  and determinant-line specializations `det (A ⊕ D) ≅ det A ⊗ det D`, together with pullback
  compatibility (strict on exterior powers, and via `pullback_det` on determinant lines);
* `FiniteRankBundleCore.exteriorPowerTwoWhitneySumIso` and
  `FiniteRankBundleCore.exteriorPowerTwoWhitneySumOfRankLeOneIso`: the concrete degree-two
  Whitney-sum decomposition `⋀^2 (A ⊕ D) ≅ ⋀^2 A ⊕ ((A ⊗ D) ⊕ ⋀^2 D)` and its specialization
  `⋀^2 (A ⊕ D) ≅ A ⊗ D` when `A` and `D` have rank at most `1` (in particular for line bundles),
  together with strict pullback compatibility.

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

/-- The bidegree-`(p, q)` Künneth inclusion `(⋀^p A) ⊗ (⋀^q D) ⟶ ⋀^n (A ⊕ D)` of finite-rank
bundle cores for `p + q = n`, given on every fibre by `TauCeti.exteriorPower.piProdInclL`. -/
noncomputable def exteriorPowerWhitneyIncl (A D : FiniteRankBundleCore 𝕜 B)
    (p q n : ℕ) (h : p + q = n) :
    (exteriorPower 𝕜 B p).obj A ⊗ (exteriorPower 𝕜 B q).obj D ⟶
      (exteriorPower 𝕜 B n).obj (whitneySum A D) :=
  constHom (fun _ ↦ le_rfl)
    (TauCeti.exteriorPower.piProdInclL 𝕜 A.rank D.rank p q n h)
    fun i j x _ _ ↦
      (TauCeti.exteriorPower.exteriorPowerCoords_splitCoords_comp_piProdInclL
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
theorem fiberMap_exteriorPowerWhitneyIncl (A D : FiniteRankBundleCore 𝕜 B)
    (p q n : ℕ) (h : p + q = n) (x : B) :
    (exteriorPowerWhitneyIncl A D p q n h).fiberMap x =
      TauCeti.exteriorPower.piProdInclL 𝕜 A.rank D.rank p q n h :=
  fiberMap_constHom _ _ _ x

@[simp]
theorem fiberMap_exteriorPowerWhitneyProj (A D : FiniteRankBundleCore 𝕜 B)
    (p q n : ℕ) (x : B) :
    (exteriorPowerWhitneyProj A D p q n).fiberMap x =
      TauCeti.exteriorPower.piProdProjL 𝕜 A.rank D.rank p q n :=
  fiberMap_constHom _ _ _ x

/-- The Künneth projection is left inverse to the Künneth inclusion in matching bidegree. -/
@[reassoc (attr := simp)]
theorem exteriorPowerWhitneyIncl_proj_self (A D : FiniteRankBundleCore 𝕜 B)
    (p q n : ℕ) (h : p + q = n) :
    exteriorPowerWhitneyIncl A D p q n h ≫ exteriorPowerWhitneyProj A D p q n = 𝟙 _ :=
  hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_exteriorPowerWhitneyIncl, fiberMap_exteriorPowerWhitneyProj,
      fiberMap_id]
    exact TauCeti.exteriorPower.piProdProjL_comp_piProdInclL_self A.rank D.rank p q n h

/-- The Künneth inclusion followed by the Künneth projection in a distinct bidegree vanishes. -/
@[reassoc]
theorem exteriorPowerWhitneyIncl_proj_of_ne (A D : FiniteRankBundleCore 𝕜 B)
    {p' q' p q n : ℕ} (h : p + q = n) (hne : p ≠ p' ∨ q ≠ q') :
    exteriorPowerWhitneyIncl A D p q n h ≫ exteriorPowerWhitneyProj A D p' q' n = 0 :=
  hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_exteriorPowerWhitneyIncl, fiberMap_exteriorPowerWhitneyProj,
      CoordinateHom.fiberMap_zero]
    exact TauCeti.exteriorPower.piProdProjL_comp_piProdInclL_of_ne h hne

/-- The Künneth projection vanishes whenever `p + q ≠ n`. -/
theorem exteriorPowerWhitneyProj_eq_zero_of_add_ne (A D : FiniteRankBundleCore 𝕜 B)
    {p q n : ℕ} (h : p + q ≠ n) :
    exteriorPowerWhitneyProj A D p q n = 0 :=
  hom_ext fun x ↦ by
    rw [fiberMap_exteriorPowerWhitneyProj, CoordinateHom.fiberMap_zero]
    exact TauCeti.exteriorPower.piProdProjL_eq_zero_of_add_ne h

/-- Over `p + q = n`, the Künneth projections followed by the Künneth inclusions sum to the
identity of `⋀^n (A ⊕ D)`. -/
theorem sum_exteriorPowerWhitneyProj_comp_incl (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ) :
    ∑ i : Fin (n + 1),
      exteriorPowerWhitneyProj A D i (n - i) n ≫
        exteriorPowerWhitneyIncl A D i (n - i) n (by omega) =
      𝟙 ((exteriorPower 𝕜 B n).obj (whitneySum A D)) :=
  hom_ext fun x ↦ by
    rw [fiberMap_sum, fiberMap_id]
    simp_rw [fiberMap_comp, fiberMap_exteriorPowerWhitneyProj, fiberMap_exteriorPowerWhitneyIncl]
    exact TauCeti.exteriorPower.sum_piProdInclL_comp_piProdProjL A.rank D.rank n

/-- Naturality of the Künneth inclusion with respect to bundle morphisms on each summand. -/
@[reassoc]
theorem tensorHom_exteriorPowerWhitneyIncl {A A' D D' : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ A') (g : D ⟶ D') (p q n : ℕ) (h : p + q = n) :
    ((exteriorPower 𝕜 B p).map f ⊗ₘ (exteriorPower 𝕜 B q).map g) ≫
        exteriorPowerWhitneyIncl A' D' p q n h =
      exteriorPowerWhitneyIncl A D p q n h ≫ (exteriorPower 𝕜 B n).map (whitneyMap f g) :=
  hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_comp, fiberMap_tensorHom_monoidal, fiberMap_exteriorPower_map,
      fiberMap_exteriorPower_map, fiberMap_exteriorPower_map, fiberMap_whitneyMap,
      fiberMap_exteriorPowerWhitneyIncl, fiberMap_exteriorPowerWhitneyIncl]
    exact (TauCeti.exteriorPower.exteriorPowerCoords_splitCoords_comp_piProdInclL
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
  ι i := exteriorPowerWhitneyIncl A D i (n - i) n (by omega)
  ι_π i j := by
    split_ifs with h
    · subst h
      simpa only [eqToHom_refl] using exteriorPowerWhitneyIncl_proj_self A D i (n - i) n (by omega)
    · exact exteriorPowerWhitneyIncl_proj_of_ne A D (by omega)
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
      exteriorPowerWhitneyIncl A D i (n - i) n (by omega) :=
  (rfl)

/-- The Künneth bicone is a bilimit: `⋀^n (A ⊕ D)` is both the product and the coproduct of the
summands `(⋀^i A) ⊗ (⋀^(n - i) D)` for `i : Fin (n + 1)`. -/
noncomputable def exteriorPowerWhitneyBiconeIsBilimit (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ) :
    (exteriorPowerWhitneyBicone A D n).IsBilimit :=
  isBilimitOfTotal _ (sum_exteriorPowerWhitneyProj_comp_incl A D n)

/-- The family `exteriorPowerWhitneySummand A D n` admits a categorical biproduct. Like
`TauCeti.hasFiniteBiproducts_of_hasBinaryBiproducts`, this is stated as a theorem rather than an
instance so that downstream constructions may use any chosen `HasFiniteBiproducts` structure. -/
theorem hasBiproduct_exteriorPowerWhitneySummand (A D : FiniteRankBundleCore 𝕜 B) (n : ℕ) :
    HasBiproduct (exteriorPowerWhitneySummand A D n) :=
  hasBiproduct_of_total (exteriorPowerWhitneyBicone A D n)
    (sum_exteriorPowerWhitneyProj_comp_incl A D n)

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
      exteriorPowerWhitneyIncl A D i (n - i) n (by omega) :=
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

/-! ### Rank-bounded collapse, top degree, and determinant of a Whitney sum -/

/-- When `A.rank ≤ p`, `D.rank ≤ q` and `p + q = n`, the Künneth inclusion is left inverse to
the Künneth projection in bidegree `(p, q)`. -/
@[reassoc]
theorem exteriorPowerWhitneyProj_incl_of_rank_le
    {A D : FiniteRankBundleCore 𝕜 B} {p q n : ℕ}
    (hA : A.rank ≤ p) (hD : D.rank ≤ q) (h : p + q = n) :
    exteriorPowerWhitneyProj A D p q n ≫ exteriorPowerWhitneyIncl A D p q n h = 𝟙 _ :=
  hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_exteriorPowerWhitneyProj, fiberMap_exteriorPowerWhitneyIncl,
      fiberMap_id]
    exact TauCeti.exteriorPower.piProdInclL_comp_piProdProjL_of_le hA hD h

/-- In the top degree `A.rank + D.rank`, the Künneth inclusion is left inverse to the Künneth
projection in bidegree `(A.rank, D.rank)`. -/
@[reassoc (attr := simp)]
theorem exteriorPowerWhitneyProj_incl_top (A D : FiniteRankBundleCore 𝕜 B) :
    exteriorPowerWhitneyProj A D A.rank D.rank (A.rank + D.rank) ≫
        exteriorPowerWhitneyIncl A D A.rank D.rank (A.rank + D.rank) rfl = 𝟙 _ :=
  exteriorPowerWhitneyProj_incl_of_rank_le le_rfl le_rfl rfl

/-- When `A.rank ≤ p`, `D.rank ≤ q` and `p + q = n`, the single Künneth summand in bidegree
`(p, q)` gives an isomorphism `⋀^n (A ⊕ D) ≅ ⋀^p A ⊗ ⋀^q D`. -/
noncomputable def exteriorPowerWhitneySumOfRankLeIso
    {A D : FiniteRankBundleCore 𝕜 B} {p q n : ℕ}
    (hA : A.rank ≤ p) (hD : D.rank ≤ q) (h : p + q = n) :
    (exteriorPower 𝕜 B n).obj (whitneySum A D) ≅
      (exteriorPower 𝕜 B p).obj A ⊗ (exteriorPower 𝕜 B q).obj D where
  hom := exteriorPowerWhitneyProj A D p q n
  inv := exteriorPowerWhitneyIncl A D p q n h
  hom_inv_id := exteriorPowerWhitneyProj_incl_of_rank_le hA hD h
  inv_hom_id := exteriorPowerWhitneyIncl_proj_self A D p q n h

theorem exteriorPowerWhitneySumOfRankLeIso_hom
    {A D : FiniteRankBundleCore 𝕜 B} {p q n : ℕ}
    (hA : A.rank ≤ p) (hD : D.rank ≤ q) (h : p + q = n) :
    (exteriorPowerWhitneySumOfRankLeIso hA hD h).hom =
      exteriorPowerWhitneyProj A D p q n :=
  (rfl)

theorem exteriorPowerWhitneySumOfRankLeIso_inv
    {A D : FiniteRankBundleCore 𝕜 B} {p q n : ℕ}
    (hA : A.rank ≤ p) (hD : D.rank ≤ q) (h : p + q = n) :
    (exteriorPowerWhitneySumOfRankLeIso hA hD h).inv =
      exteriorPowerWhitneyIncl A D p q n h :=
  (rfl)

/-- Naturality of `exteriorPowerWhitneySumOfRankLeIso` with respect to bundle morphisms on each
summand. -/
@[reassoc]
theorem exteriorPower_map_whitneyMap_whitneySumOfRankLeIso_hom
    {A A' D D' : FiniteRankBundleCore 𝕜 B} {p q n : ℕ}
    (hA : A.rank ≤ p) (hD : D.rank ≤ q) (hA' : A'.rank ≤ p) (hD' : D'.rank ≤ q)
    (h : p + q = n) (f : A ⟶ A') (g : D ⟶ D') :
    (exteriorPower 𝕜 B n).map (whitneyMap f g) ≫
        (exteriorPowerWhitneySumOfRankLeIso hA' hD' h).hom =
      (exteriorPowerWhitneySumOfRankLeIso hA hD h).hom ≫
        ((exteriorPower 𝕜 B p).map f ⊗ₘ (exteriorPower 𝕜 B q).map g) :=
  exteriorPower_map_whitneyMap_proj f g p q n

/-- In the top degree `A.rank + D.rank`, the single Künneth summand in bidegree `(A.rank, D.rank)`
gives an isomorphism `⋀^(A.rank + D.rank) (A ⊕ D) ≅ ⋀^A.rank A ⊗ ⋀^D.rank D`. -/
noncomputable def exteriorPowerTopWhitneySumIso (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPower 𝕜 B (A.rank + D.rank)).obj (whitneySum A D) ≅
      (exteriorPower 𝕜 B A.rank).obj A ⊗ (exteriorPower 𝕜 B D.rank).obj D :=
  exteriorPowerWhitneySumOfRankLeIso le_rfl le_rfl rfl

@[simp]
theorem exteriorPowerTopWhitneySumIso_hom (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerTopWhitneySumIso A D).hom =
      exteriorPowerWhitneyProj A D A.rank D.rank (A.rank + D.rank) :=
  (rfl)

@[simp]
theorem exteriorPowerTopWhitneySumIso_inv (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerTopWhitneySumIso A D).inv =
      exteriorPowerWhitneyIncl A D A.rank D.rank (A.rank + D.rank) rfl :=
  (rfl)

/-- Naturality of `exteriorPowerTopWhitneySumIso` for endomorphisms of `A` and `D`. -/
@[reassoc]
theorem exteriorPower_map_whitneyMap_topWhitneySumIso_hom
    {A D : FiniteRankBundleCore 𝕜 B} (f : A ⟶ A) (g : D ⟶ D) :
    (exteriorPower 𝕜 B (A.rank + D.rank)).map (whitneyMap f g) ≫
        (exteriorPowerTopWhitneySumIso A D).hom =
      (exteriorPowerTopWhitneySumIso A D).hom ≫
        ((exteriorPower 𝕜 B A.rank).map f ⊗ₘ (exteriorPower 𝕜 B D.rank).map g) :=
  exteriorPower_map_whitneyMap_whitneySumOfRankLeIso_hom le_rfl le_rfl le_rfl le_rfl rfl f g

/-- The determinant line of a Whitney sum `A ⊕ D` is the exterior power in degree
`A.rank + D.rank`. -/
theorem det_whitneySum (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneySum A D).det = (exteriorPower 𝕜 B (A.rank + D.rank)).obj (whitneySum A D) :=
  (rfl)

/-- The determinant line of a Whitney sum is canonically isomorphic to the tensor product of the
determinant lines of the summands. -/
noncomputable def detWhitneySumIso (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneySum A D).det ≅ A.det ⊗ D.det :=
  eqToIso (det_whitneySum A D) ≪≫
    exteriorPowerTopWhitneySumIso A D ≪≫
    (eqToIso (det_def A).symm ⊗ᵢ eqToIso (det_def D).symm)

theorem detWhitneySumIso_hom (A D : FiniteRankBundleCore 𝕜 B) :
    (detWhitneySumIso A D).hom =
      eqToHom (det_whitneySum A D) ≫
        exteriorPowerWhitneyProj A D A.rank D.rank (A.rank + D.rank) ≫
        (eqToHom (det_def A).symm ⊗ₘ eqToHom (det_def D).symm) := by
  simp [detWhitneySumIso]

theorem detWhitneySumIso_inv (A D : FiniteRankBundleCore 𝕜 B) :
    (detWhitneySumIso A D).inv =
      (eqToHom (det_def A) ⊗ₘ eqToHom (det_def D)) ≫
        exteriorPowerWhitneyIncl A D A.rank D.rank (A.rank + D.rank) rfl ≫
        eqToHom (det_whitneySum A D).symm := by
  simp [detWhitneySumIso]

/-! ### Degree two and the line-bundle cross term -/

/-- `A ⊗ (⋀^0 D)` is canonically isomorphic to `A` via `exteriorPowerZeroIso D` and the right
unitor. -/
noncomputable def exteriorPowerRightZeroTensorIso (A D : FiniteRankBundleCore 𝕜 B) :
    A ⊗ (exteriorPower 𝕜 B 0).obj D ≅ A :=
  A ◁ᵢ exteriorPowerZeroIso D ≪≫ ρ_ A

@[simp]
theorem exteriorPowerRightZeroTensorIso_hom (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerRightZeroTensorIso A D).hom =
      A ◁ (exteriorPowerZeroIso D).hom ≫ (ρ_ A).hom :=
  (rfl)

@[simp]
theorem exteriorPowerRightZeroTensorIso_inv (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerRightZeroTensorIso A D).inv =
      (ρ_ A).inv ≫ A ◁ (exteriorPowerZeroIso D).inv :=
  (rfl)

/-- `(⋀^0 A) ⊗ D` is canonically isomorphic to `D` via `exteriorPowerZeroIso A` and the left
unitor. -/
noncomputable def exteriorPowerLeftZeroTensorIso (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPower 𝕜 B 0).obj A ⊗ D ≅ D :=
  exteriorPowerZeroIso A ▷ᵢ D ≪≫ λ_ D

@[simp]
theorem exteriorPowerLeftZeroTensorIso_hom (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerLeftZeroTensorIso A D).hom =
      (exteriorPowerZeroIso A).hom ▷ D ≫ (λ_ D).hom :=
  (rfl)

@[simp]
theorem exteriorPowerLeftZeroTensorIso_inv (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerLeftZeroTensorIso A D).inv =
      (λ_ D).inv ≫ (exteriorPowerZeroIso A).inv ▷ D :=
  (rfl)

/-- `(⋀^1 A) ⊗ (⋀^1 D)` is canonically isomorphic to `A ⊗ D` via `exteriorPowerOneIso`. -/
noncomputable def exteriorPowerOneOneTensorIso (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPower 𝕜 B 1).obj A ⊗ (exteriorPower 𝕜 B 1).obj D ≅ A ⊗ D :=
  exteriorPowerOneIso A ⊗ᵢ exteriorPowerOneIso D

@[simp]
theorem exteriorPowerOneOneTensorIso_hom (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerOneOneTensorIso A D).hom =
      (exteriorPowerOneIso A).hom ⊗ₘ (exteriorPowerOneIso D).hom :=
  (rfl)

@[simp]
theorem exteriorPowerOneOneTensorIso_inv (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerOneOneTensorIso A D).inv =
      (exteriorPowerOneIso A).inv ⊗ₘ (exteriorPowerOneIso D).inv :=
  (rfl)

@[reassoc]
theorem exteriorPowerRightZeroTensorIso_hom_naturality
    {A A' D D' : FiniteRankBundleCore 𝕜 B} (f : A ⟶ A') (g : D ⟶ D') :
    (f ⊗ₘ (exteriorPower 𝕜 B 0).map g) ≫
        (exteriorPowerRightZeroTensorIso A' D').hom =
      (exteriorPowerRightZeroTensorIso A D).hom ≫ f := by
  rw [exteriorPowerRightZeroTensorIso_hom, exteriorPowerRightZeroTensorIso_hom,
    tensorHom_comp_whiskerLeft_assoc, exteriorPowerZeroIso_hom_naturality, tensorHom_def'_assoc]
  exact (congrArg (_ ≫ ·) (MonoidalCategory.rightUnitor_naturality f)).trans
    (Category.assoc _ _ _).symm

@[reassoc]
theorem exteriorPowerLeftZeroTensorIso_hom_naturality
    {A A' D D' : FiniteRankBundleCore 𝕜 B} (f : A ⟶ A') (g : D ⟶ D') :
    ((exteriorPower 𝕜 B 0).map f ⊗ₘ g) ≫
        (exteriorPowerLeftZeroTensorIso A' D').hom =
      (exteriorPowerLeftZeroTensorIso A D).hom ≫ g := by
  rw [exteriorPowerLeftZeroTensorIso_hom, exteriorPowerLeftZeroTensorIso_hom,
    tensorHom_comp_whiskerRight_assoc, exteriorPowerZeroIso_hom_naturality, tensorHom_def_assoc]
  exact (congrArg (_ ≫ ·) (MonoidalCategory.leftUnitor_naturality g)).trans
    (Category.assoc _ _ _).symm

@[reassoc]
theorem exteriorPowerOneOneTensorIso_hom_naturality
    {A A' D D' : FiniteRankBundleCore 𝕜 B} (f : A ⟶ A') (g : D ⟶ D') :
    ((exteriorPower 𝕜 B 1).map f ⊗ₘ (exteriorPower 𝕜 B 1).map g) ≫
        (exteriorPowerOneOneTensorIso A' D').hom =
      (exteriorPowerOneOneTensorIso A D).hom ≫ (f ⊗ₘ g) := by
  simp only [exteriorPowerOneOneTensorIso_hom, MonoidalCategory.tensorHom_comp_tensorHom,
    exteriorPowerOneIso_hom_naturality]

private theorem exteriorPowerTwo_total (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerWhitneyProj A D 2 0 2 ≫
        (exteriorPowerRightZeroTensorIso ((exteriorPower 𝕜 B 2).obj A) D).hom) ≫
        ((exteriorPowerRightZeroTensorIso ((exteriorPower 𝕜 B 2).obj A) D).inv ≫
          exteriorPowerWhitneyIncl A D 2 0 2 rfl) +
      ((exteriorPowerWhitneyProj A D 1 1 2 ≫ (exteriorPowerOneOneTensorIso A D).hom) ≫
        ((exteriorPowerOneOneTensorIso A D).inv ≫ exteriorPowerWhitneyIncl A D 1 1 2 rfl) +
      (exteriorPowerWhitneyProj A D 0 2 2 ≫
        (exteriorPowerLeftZeroTensorIso A ((exteriorPower 𝕜 B 2).obj D)).hom) ≫
        ((exteriorPowerLeftZeroTensorIso A ((exteriorPower 𝕜 B 2).obj D)).inv ≫
          exteriorPowerWhitneyIncl A D 0 2 2 rfl)) =
      𝟙 ((exteriorPower 𝕜 B 2).obj (whitneySum A D)) := by
  have hsum := sum_exteriorPowerWhitneyProj_comp_incl A D 2
  rw [Fin.sum_univ_three] at hsum
  dsimp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at hsum
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← hsum]
  abel

private theorem exteriorPowerTwo_hom_inv_id (A D : FiniteRankBundleCore 𝕜 B) :
    whitneyLift
        (exteriorPowerWhitneyProj A D 2 0 2 ≫
          (exteriorPowerRightZeroTensorIso ((exteriorPower 𝕜 B 2).obj A) D).hom)
        (whitneyLift
          (exteriorPowerWhitneyProj A D 1 1 2 ≫ (exteriorPowerOneOneTensorIso A D).hom)
          (exteriorPowerWhitneyProj A D 0 2 2 ≫
            (exteriorPowerLeftZeroTensorIso A ((exteriorPower 𝕜 B 2).obj D)).hom)) ≫
      whitneyDesc
        ((exteriorPowerRightZeroTensorIso ((exteriorPower 𝕜 B 2).obj A) D).inv ≫
          exteriorPowerWhitneyIncl A D 2 0 2 rfl)
        (whitneyDesc
          ((exteriorPowerOneOneTensorIso A D).inv ≫ exteriorPowerWhitneyIncl A D 1 1 2 rfl)
          ((exteriorPowerLeftZeroTensorIso A ((exteriorPower 𝕜 B 2).obj D)).inv ≫
            exteriorPowerWhitneyIncl A D 0 2 2 rfl)) =
      𝟙 ((exteriorPower 𝕜 B 2).obj (whitneySum A D)) := by
  rw [whitneyLift_desc, whitneyLift_desc]
  exact exteriorPowerTwo_total A D

private theorem exteriorPowerTwo_inv_hom_id (A D : FiniteRankBundleCore 𝕜 B) :
    whitneyDesc
        ((exteriorPowerRightZeroTensorIso ((exteriorPower 𝕜 B 2).obj A) D).inv ≫
          exteriorPowerWhitneyIncl A D 2 0 2 rfl)
        (whitneyDesc
          ((exteriorPowerOneOneTensorIso A D).inv ≫ exteriorPowerWhitneyIncl A D 1 1 2 rfl)
          ((exteriorPowerLeftZeroTensorIso A ((exteriorPower 𝕜 B 2).obj D)).inv ≫
            exteriorPowerWhitneyIncl A D 0 2 2 rfl)) ≫
      whitneyLift
        (exteriorPowerWhitneyProj A D 2 0 2 ≫
          (exteriorPowerRightZeroTensorIso ((exteriorPower 𝕜 B 2).obj A) D).hom)
        (whitneyLift
          (exteriorPowerWhitneyProj A D 1 1 2 ≫ (exteriorPowerOneOneTensorIso A D).hom)
          (exteriorPowerWhitneyProj A D 0 2 2 ≫
            (exteriorPowerLeftZeroTensorIso A ((exteriorPower 𝕜 B 2).obj D)).hom)) =
      𝟙 _ := by
  refine whitneySum_hom_ext' ?_ (whitneySum_hom_ext' ?_ ?_) <;>
    refine whitneySum_hom_ext ?_ (whitneySum_hom_ext ?_ ?_)
  · simp
  · simp [exteriorPowerWhitneyIncl_proj_of_ne_assoc A D (p := 2) (q := 0) (p' := 1) (q' := 1) rfl
      (Or.inl (by decide))]
  · simp [exteriorPowerWhitneyIncl_proj_of_ne_assoc A D (p := 2) (q := 0) (p' := 0) (q' := 2) rfl
      (Or.inl (by decide))]
  · simp [exteriorPowerWhitneyIncl_proj_of_ne_assoc A D (p := 1) (q := 1) (p' := 2) (q' := 0) rfl
      (Or.inl (by decide))]
  · simp
  · simp [exteriorPowerWhitneyIncl_proj_of_ne_assoc A D (p := 1) (q := 1) (p' := 0) (q' := 2) rfl
      (Or.inl (by decide))]
  · simp [exteriorPowerWhitneyIncl_proj_of_ne_assoc A D (p := 0) (q := 2) (p' := 2) (q' := 0) rfl
      (Or.inl (by decide))]
  · simp [exteriorPowerWhitneyIncl_proj_of_ne_assoc A D (p := 0) (q := 2) (p' := 1) (q' := 1) rfl
      (Or.inl (by decide))]
  · simp

/-- Concrete Whitney-sum decomposition of the second exterior power:
`⋀^2 (A ⊕ D) ≅ ⋀^2 A ⊕ ((A ⊗ D) ⊕ ⋀^2 D)`, retaining the mixed cross term `A ⊗ D`. -/
noncomputable def exteriorPowerTwoWhitneySumIso (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPower 𝕜 B 2).obj (whitneySum A D) ≅
      whitneySum ((exteriorPower 𝕜 B 2).obj A)
        (whitneySum (A ⊗ D) ((exteriorPower 𝕜 B 2).obj D)) where
  hom := whitneyLift
    (exteriorPowerWhitneyProj A D 2 0 2 ≫
      (exteriorPowerRightZeroTensorIso ((exteriorPower 𝕜 B 2).obj A) D).hom)
    (whitneyLift
      (exteriorPowerWhitneyProj A D 1 1 2 ≫ (exteriorPowerOneOneTensorIso A D).hom)
      (exteriorPowerWhitneyProj A D 0 2 2 ≫
        (exteriorPowerLeftZeroTensorIso A ((exteriorPower 𝕜 B 2).obj D)).hom))
  inv := whitneyDesc
    ((exteriorPowerRightZeroTensorIso ((exteriorPower 𝕜 B 2).obj A) D).inv ≫
      exteriorPowerWhitneyIncl A D 2 0 2 rfl)
    (whitneyDesc
      ((exteriorPowerOneOneTensorIso A D).inv ≫ exteriorPowerWhitneyIncl A D 1 1 2 rfl)
      ((exteriorPowerLeftZeroTensorIso A ((exteriorPower 𝕜 B 2).obj D)).inv ≫
        exteriorPowerWhitneyIncl A D 0 2 2 rfl))
  hom_inv_id := exteriorPowerTwo_hom_inv_id A D
  inv_hom_id := exteriorPowerTwo_inv_hom_id A D

theorem exteriorPowerTwoWhitneySumIso_hom (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerTwoWhitneySumIso A D).hom =
      whitneyLift
        (exteriorPowerWhitneyProj A D 2 0 2 ≫
          (exteriorPowerRightZeroTensorIso ((exteriorPower 𝕜 B 2).obj A) D).hom)
        (whitneyLift
          (exteriorPowerWhitneyProj A D 1 1 2 ≫ (exteriorPowerOneOneTensorIso A D).hom)
          (exteriorPowerWhitneyProj A D 0 2 2 ≫
            (exteriorPowerLeftZeroTensorIso A ((exteriorPower 𝕜 B 2).obj D)).hom)) :=
  (rfl)

theorem exteriorPowerTwoWhitneySumIso_inv (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerTwoWhitneySumIso A D).inv =
      whitneyDesc
        ((exteriorPowerRightZeroTensorIso ((exteriorPower 𝕜 B 2).obj A) D).inv ≫
          exteriorPowerWhitneyIncl A D 2 0 2 rfl)
        (whitneyDesc
          ((exteriorPowerOneOneTensorIso A D).inv ≫ exteriorPowerWhitneyIncl A D 1 1 2 rfl)
          ((exteriorPowerLeftZeroTensorIso A ((exteriorPower 𝕜 B 2).obj D)).inv ≫
            exteriorPowerWhitneyIncl A D 0 2 2 rfl)) :=
  (rfl)

@[reassoc (attr := simp)]
theorem exteriorPowerTwoWhitneySumIso_hom_whitneyFst (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerTwoWhitneySumIso A D).hom ≫
        whitneyFst ((exteriorPower 𝕜 B 2).obj A)
          (whitneySum (A ⊗ D) ((exteriorPower 𝕜 B 2).obj D)) =
      exteriorPowerWhitneyProj A D 2 0 2 ≫
        (exteriorPowerRightZeroTensorIso ((exteriorPower 𝕜 B 2).obj A) D).hom :=
  whitneyLift_fst _ _

@[reassoc (attr := simp)]
theorem exteriorPowerTwoWhitneySumIso_hom_whitneySnd (A D : FiniteRankBundleCore 𝕜 B) :
    (exteriorPowerTwoWhitneySumIso A D).hom ≫
        whitneySnd ((exteriorPower 𝕜 B 2).obj A)
          (whitneySum (A ⊗ D) ((exteriorPower 𝕜 B 2).obj D)) =
      whitneyLift
        (exteriorPowerWhitneyProj A D 1 1 2 ≫ (exteriorPowerOneOneTensorIso A D).hom)
        (exteriorPowerWhitneyProj A D 0 2 2 ≫
          (exteriorPowerLeftZeroTensorIso A ((exteriorPower 𝕜 B 2).obj D)).hom) :=
  whitneyLift_snd _ _

@[reassoc (attr := simp)]
theorem whitneyInl_exteriorPowerTwoWhitneySumIso_inv (A D : FiniteRankBundleCore 𝕜 B) :
    whitneyInl ((exteriorPower 𝕜 B 2).obj A)
        (whitneySum (A ⊗ D) ((exteriorPower 𝕜 B 2).obj D)) ≫
        (exteriorPowerTwoWhitneySumIso A D).inv =
      (exteriorPowerRightZeroTensorIso ((exteriorPower 𝕜 B 2).obj A) D).inv ≫
        exteriorPowerWhitneyIncl A D 2 0 2 rfl :=
  whitneyInl_desc _ _

@[reassoc (attr := simp)]
theorem whitneyInr_exteriorPowerTwoWhitneySumIso_inv (A D : FiniteRankBundleCore 𝕜 B) :
    whitneyInr ((exteriorPower 𝕜 B 2).obj A)
        (whitneySum (A ⊗ D) ((exteriorPower 𝕜 B 2).obj D)) ≫
        (exteriorPowerTwoWhitneySumIso A D).inv =
      whitneyDesc
        ((exteriorPowerOneOneTensorIso A D).inv ≫ exteriorPowerWhitneyIncl A D 1 1 2 rfl)
        ((exteriorPowerLeftZeroTensorIso A ((exteriorPower 𝕜 B 2).obj D)).inv ≫
          exteriorPowerWhitneyIncl A D 0 2 2 rfl) :=
  whitneyInr_desc _ _

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

/-- When `A` and `D` have rank at most `1` (in particular for line bundles), `⋀^2 A` and `⋀^2 D`
are zero objects and the second exterior power `⋀^2 (A ⊕ D)` is canonically isomorphic to the
cross term `A ⊗ D`. -/
noncomputable def exteriorPowerTwoWhitneySumOfRankLeOneIso
    {A D : FiniteRankBundleCore 𝕜 B} (hA : A.rank ≤ 1) (hD : D.rank ≤ 1) :
    (exteriorPower 𝕜 B 2).obj (whitneySum A D) ≅ A ⊗ D :=
  exteriorPowerWhitneySumOfRankLeIso hA hD rfl ≪≫ exteriorPowerOneOneTensorIso A D

theorem exteriorPowerTwoWhitneySumOfRankLeOneIso_hom
    {A D : FiniteRankBundleCore 𝕜 B} (hA : A.rank ≤ 1) (hD : D.rank ≤ 1) :
    (exteriorPowerTwoWhitneySumOfRankLeOneIso hA hD).hom =
      exteriorPowerWhitneyProj A D 1 1 2 ≫ (exteriorPowerOneOneTensorIso A D).hom :=
  (rfl)

theorem exteriorPowerTwoWhitneySumOfRankLeOneIso_inv
    {A D : FiniteRankBundleCore 𝕜 B} (hA : A.rank ≤ 1) (hD : D.rank ≤ 1) :
    (exteriorPowerTwoWhitneySumOfRankLeOneIso hA hD).inv =
      (exteriorPowerOneOneTensorIso A D).inv ≫ exteriorPowerWhitneyIncl A D 1 1 2 rfl :=
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
    ← exteriorPowerWhitneySumOfRankLeIso_hom hA hD rfl,
    ← exteriorPowerWhitneySumOfRankLeIso_hom hA' hD' rfl,
    exteriorPower_map_whitneyMap_whitneySumOfRankLeIso_hom_assoc,
    exteriorPowerOneOneTensorIso_hom_naturality, Category.assoc]

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
theorem pullbackMap_exteriorPowerWhitneyIncl (A D : FiniteRankBundleCore 𝕜 Y)
    (p q n : ℕ) (h : p + q = n) (φ : C(X, Y)) :
    pullbackMap (exteriorPowerWhitneyIncl A D p q n h) φ =
      exteriorPowerWhitneyIncl (A.pullback φ) (D.pullback φ) p q n h :=
  hom_ext fun x ↦
    (fiberMap_pullbackMap _ φ x).trans
      ((fiberMap_exteriorPowerWhitneyIncl A D p q n h (φ x)).trans
        (fiberMap_exteriorPowerWhitneyIncl (A.pullback φ) (D.pullback φ) p q n h x).symm)

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

/-- Pulling back commutes strictly with `exteriorPowerWhitneySumOfRankLeIso`. -/
@[simp]
theorem pullbackFunctor_mapIso_exteriorPowerWhitneySumOfRankLeIso
    {A D : FiniteRankBundleCore 𝕜 Y} {p q n : ℕ}
    (hA : A.rank ≤ p) (hD : D.rank ≤ q) (h : p + q = n) (φ : C(X, Y)) :
    (pullbackFunctor φ).mapIso (exteriorPowerWhitneySumOfRankLeIso hA hD h) =
      exteriorPowerWhitneySumOfRankLeIso
        ((rank_pullback A φ).le.trans hA) ((rank_pullback D φ).le.trans hD) h :=
  Iso.ext (pullbackMap_exteriorPowerWhitneyProj A D p q n φ)

/-- Pulling back commutes strictly with `exteriorPowerTopWhitneySumIso`. -/
@[simp]
theorem pullbackFunctor_mapIso_exteriorPowerTopWhitneySumIso
    (A D : FiniteRankBundleCore 𝕜 Y) (φ : C(X, Y)) :
    (pullbackFunctor φ).mapIso (exteriorPowerTopWhitneySumIso A D) =
      exteriorPowerTopWhitneySumIso (A.pullback φ) (D.pullback φ) :=
  pullbackFunctor_mapIso_exteriorPowerWhitneySumOfRankLeIso le_rfl le_rfl rfl φ

private theorem fiberMap_exteriorPowerRightZeroTensorIso_hom
    (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (exteriorPowerRightZeroTensorIso A D).hom.fiberMap x =
      (ContinuousLinearEquiv.kroneckerRid 𝕜 A.rank).toContinuousLinearMap.comp
        ((ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)).kronecker
          (exteriorPower.piZeroContinuousEquiv 𝕜 D.rank :
            (Fin (D.rank.choose 0) → 𝕜) →L[𝕜] (Fin 1 → 𝕜))) :=
  (fiberMap_comp _ _ x).trans <|
    congrArg₂ ContinuousLinearMap.comp (fiberMap_rightUnitor_hom A x)
      ((fiberMap_whiskerLeft A _ x).trans (congrArg _ (fiberMap_exteriorPowerZeroIso_hom D x)))

private theorem fiberMap_exteriorPowerLeftZeroTensorIso_hom
    (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (exteriorPowerLeftZeroTensorIso A D).hom.fiberMap x =
      (ContinuousLinearEquiv.kroneckerLid 𝕜 D.rank).toContinuousLinearMap.comp
        ((exteriorPower.piZeroContinuousEquiv 𝕜 A.rank :
            (Fin (A.rank.choose 0) → 𝕜) →L[𝕜] (Fin 1 → 𝕜)).kronecker
          (ContinuousLinearMap.id 𝕜 (Fin D.rank → 𝕜))) :=
  (fiberMap_comp _ _ x).trans <|
    congrArg₂ ContinuousLinearMap.comp (fiberMap_leftUnitor_hom D x)
      ((fiberMap_whiskerRight _ D x).trans
        (congrArg (ContinuousLinearMap.kronecker · (ContinuousLinearMap.id 𝕜 (Fin D.rank → 𝕜)))
          (fiberMap_exteriorPowerZeroIso_hom A x)))

private theorem fiberMap_exteriorPowerOneOneTensorIso_hom
    (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (exteriorPowerOneOneTensorIso A D).hom.fiberMap x =
      (exteriorPower.piOneContinuousEquiv 𝕜 A.rank :
          (Fin (A.rank.choose 1) → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)).kronecker
        (exteriorPower.piOneContinuousEquiv 𝕜 D.rank :
          (Fin (D.rank.choose 1) → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) :=
  (fiberMap_tensorHom_monoidal _ _ x).trans <|
    congrArg₂ ContinuousLinearMap.kronecker
      (fiberMap_exteriorPowerOneIso_hom A x) (fiberMap_exteriorPowerOneIso_hom D x)

private theorem fiberMap_exteriorPowerTwoWhitneySumIso_hom
    (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (exteriorPowerTwoWhitneySumIso A D).hom.fiberMap x =
      (splitCoords (𝕜 := 𝕜)
          (A.rank.choose 2) (A.rank * D.rank + D.rank.choose 2)).symm.toContinuousLinearMap.comp
        ((((ContinuousLinearEquiv.kroneckerRid 𝕜 (A.rank.choose 2)).toContinuousLinearMap.comp
              ((ContinuousLinearMap.id 𝕜 (Fin (A.rank.choose 2) → 𝕜)).kronecker
                (exteriorPower.piZeroContinuousEquiv 𝕜 D.rank :
                  (Fin (D.rank.choose 0) → 𝕜) →L[𝕜] (Fin 1 → 𝕜)))).comp
            (TauCeti.exteriorPower.piProdProjL 𝕜 A.rank D.rank 2 0 2)).prod
          ((splitCoords (𝕜 := 𝕜)
              (A.rank * D.rank) (D.rank.choose 2)).symm.toContinuousLinearMap.comp
            ((((exteriorPower.piOneContinuousEquiv 𝕜 A.rank :
                    (Fin (A.rank.choose 1) → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)).kronecker
                  (exteriorPower.piOneContinuousEquiv 𝕜 D.rank :
                    (Fin (D.rank.choose 1) → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))).comp
                (TauCeti.exteriorPower.piProdProjL 𝕜 A.rank D.rank 1 1 2)).prod
              (((ContinuousLinearEquiv.kroneckerLid 𝕜 (D.rank.choose 2)).toContinuousLinearMap.comp
                  ((exteriorPower.piZeroContinuousEquiv 𝕜 A.rank :
                      (Fin (A.rank.choose 0) → 𝕜) →L[𝕜] (Fin 1 → 𝕜)).kronecker
                    (ContinuousLinearMap.id 𝕜 (Fin (D.rank.choose 2) → 𝕜)))).comp
                (TauCeti.exteriorPower.piProdProjL 𝕜 A.rank D.rank 0 2 2))))) :=
  (fiberMap_whitneyLift _ _ x).trans <|
    congrArg _ <| congrArg₂ ContinuousLinearMap.prod
      ((fiberMap_comp _ _ x).trans <|
        congrArg₂ ContinuousLinearMap.comp
          (fiberMap_exteriorPowerRightZeroTensorIso_hom _ D x)
          (fiberMap_exteriorPowerWhitneyProj A D 2 0 2 x))
      ((fiberMap_whitneyLift _ _ x).trans <|
        congrArg _ <| congrArg₂ ContinuousLinearMap.prod
          ((fiberMap_comp _ _ x).trans <|
            congrArg₂ ContinuousLinearMap.comp
              (fiberMap_exteriorPowerOneOneTensorIso_hom A D x)
              (fiberMap_exteriorPowerWhitneyProj A D 1 1 2 x))
          ((fiberMap_comp _ _ x).trans <|
            congrArg₂ ContinuousLinearMap.comp
              (fiberMap_exteriorPowerLeftZeroTensorIso_hom A _ x)
              (fiberMap_exteriorPowerWhitneyProj A D 0 2 2 x)))

private theorem tensorIso_eqToIso {C : Type*} [Category* C] [MonoidalCategory C]
    {X₁ X₂ Y₁ Y₂ : C} (hX : X₁ = X₂) (hY : Y₁ = Y₂) :
    eqToIso hX ⊗ᵢ eqToIso hY = eqToIso congr($hX ⊗ $hY) := by
  subst hX hY
  ext
  simp

private theorem eqToIso_conj_trans {C : Type*} [Category* C] {W X Y Z V U : C}
    (h₁ : W = X) (h₂ : X = Y) (e : Y ≅ Z) (h₃ : Z = V) (h₄ : V = U) :
    eqToIso (h₁.trans h₂) ≪≫ e ≪≫ eqToIso (h₃.trans h₄) =
      eqToIso h₁ ≪≫ (eqToIso h₂ ≪≫ e ≪≫ eqToIso h₃) ≪≫ eqToIso h₄ := by
  subst h₁ h₂ h₃ h₄
  simp

/-- Pulling back `detWhitneySumIso` identifies with `detWhitneySumIso` of the pullbacks across
`pullback_det`. -/
theorem pullbackFunctor_mapIso_detWhitneySumIso
    (A D : FiniteRankBundleCore 𝕜 Y) (φ : C(X, Y)) :
    (pullbackFunctor φ).mapIso (detWhitneySumIso A D) =
      eqToIso (pullback_det (whitneySum A D) φ) ≪≫
        detWhitneySumIso (A.pullback φ) (D.pullback φ) ≪≫
        (eqToIso (pullback_det A φ).symm ⊗ᵢ eqToIso (pullback_det D φ).symm) :=
  ((Functor.mapIso_trans (pullbackFunctor φ) (eqToIso (det_whitneySum A D)) _).trans
    (congrArg₂ Iso.trans (eqToIso_map (pullbackFunctor φ) (det_whitneySum A D))
      ((Functor.mapIso_trans (pullbackFunctor φ) (exteriorPowerTopWhitneySumIso A D) _).trans
        (congrArg₂ Iso.trans (pullbackFunctor_mapIso_exteriorPowerTopWhitneySumIso A D φ)
          ((congrArg (pullbackFunctor φ).mapIso
              (tensorIso_eqToIso (det_def A).symm (det_def D).symm)).trans
            (eqToIso_map (pullbackFunctor φ) _)))))).trans <|
    (eqToIso_conj_trans (pullback_det (whitneySum A D) φ)
      (det_whitneySum (A.pullback φ) (D.pullback φ))
      (exteriorPowerTopWhitneySumIso (A.pullback φ) (D.pullback φ))
      congr($((det_def (A.pullback φ)).symm) ⊗ $((det_def (D.pullback φ)).symm))
      congr($((pullback_det A φ).symm) ⊗ $((pullback_det D φ).symm))).trans <|
      congrArg (_ ≪≫ ·) <| congrArg₂ Iso.trans
        (congrArg (_ ≪≫ ·) <| congrArg (_ ≪≫ ·)
          (tensorIso_eqToIso (det_def (A.pullback φ)).symm (det_def (D.pullback φ)).symm).symm)
        (tensorIso_eqToIso (pullback_det A φ).symm (pullback_det D φ).symm).symm

/-- Pulling back commutes strictly with `exteriorPowerTwoWhitneySumIso`. -/
@[simp]
theorem pullbackFunctor_mapIso_exteriorPowerTwoWhitneySumIso
    (A D : FiniteRankBundleCore 𝕜 Y) (φ : C(X, Y)) :
    (pullbackFunctor φ).mapIso (exteriorPowerTwoWhitneySumIso A D) =
      exteriorPowerTwoWhitneySumIso (A.pullback φ) (D.pullback φ) :=
  Iso.ext <| hom_ext fun x ↦
    (fiberMap_pullbackMap _ φ x).trans
      ((fiberMap_exteriorPowerTwoWhitneySumIso_hom A D (φ x)).trans
        (fiberMap_exteriorPowerTwoWhitneySumIso_hom (A.pullback φ) (D.pullback φ) x).symm)

/-- Pulling back commutes strictly with `exteriorPowerTwoWhitneySumOfRankLeOneIso`. -/
@[simp]
theorem pullbackFunctor_mapIso_exteriorPowerTwoWhitneySumOfRankLeOneIso
    {A D : FiniteRankBundleCore 𝕜 Y} (hA : A.rank ≤ 1) (hD : D.rank ≤ 1) (φ : C(X, Y)) :
    (pullbackFunctor φ).mapIso (exteriorPowerTwoWhitneySumOfRankLeOneIso hA hD) =
      exteriorPowerTwoWhitneySumOfRankLeOneIso
        ((rank_pullback A φ).le.trans hA) ((rank_pullback D φ).le.trans hD) :=
  Iso.ext <| hom_ext fun x ↦
    (fiberMap_pullbackMap _ φ x).trans <|
      ((fiberMap_comp _ _ (φ x)).trans
        (congrArg₂ ContinuousLinearMap.comp
          (fiberMap_exteriorPowerOneOneTensorIso_hom A D (φ x))
          (fiberMap_exteriorPowerWhitneyProj A D 1 1 2 (φ x)))).trans
      ((fiberMap_comp _ _ x).trans
        (congrArg₂ ContinuousLinearMap.comp
          (fiberMap_exteriorPowerOneOneTensorIso_hom (A.pullback φ) (D.pullback φ) x)
          (fiberMap_exteriorPowerWhitneyProj (A.pullback φ) (D.pullback φ) 1 1 2 x))).symm

end Pullback

end FiniteRankBundleCore
end TauCeti
