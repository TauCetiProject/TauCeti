/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.ExteriorPowerCoords
public import TauCeti.Topology.VectorBundle.FiniteRank.CoordinateFunctor

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

These are the bundle operations whose classes form the coefficients of `λ_t(E) = Σ [⋀^j E] tʲ`
in topological K-theory.

## References

* M. F. Atiyah, *K-Theory*, §1.2 and §3.1.
-/

public section

open CategoryTheory CategoryTheory.Limits

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

end FiniteRankBundleCore
end TauCeti
