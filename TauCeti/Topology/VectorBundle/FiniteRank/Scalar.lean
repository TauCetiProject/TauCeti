/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Basic

/-!
# Point-indexed rank-one presentation of scalar line-bundle cores

A Mathlib `VectorBundleCore 𝕜 B 𝕜 ι` with model fibre `𝕜` presents a line bundle by scalar
transition functions (`VectorBundleCore.isContMDiff_iff_contMDiffOn_coordChange_one`), while
monoidal and dual operations on coordinate bundles live on `FiniteRankBundleCore 𝕜 B` with model
fibres `Fin r → 𝕜` and base-point-indexed charts.

For any `Z : VectorBundleCore 𝕜 B 𝕜 ι`, `FiniteRankBundleCore.ofScalarCore Z` restricts the chart
family along `Z.indexAt : B → ι` and transports the fibre `𝕜` to `Fin 1 → 𝕜` via
`ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜`. The mutually inverse cocycle morphisms
`toScalarCore Z` and `fromScalarCore Z` identify `(ofScalarCore Z).core` with `Z` over the identity
of `B` (`ofScalarCoreHomeomorph`), without completeness or separation assumptions.

We also construct `isoTrivialOfCoordChangeEqId`, the canonical isomorphism `A ≅ trivial 𝕜 B A.rank`
for any point-indexed core whose transition maps are identities on chart overlaps, without
requiring chart domains to be `Set.univ`.

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §§2–3.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public section

open Bundle CategoryTheory Set VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B ι : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

-- Expose the rank projection so the dependent fibre model reduces to `Fin 1 → 𝕜`.
/-- Present a scalar line-bundle core `Z : VectorBundleCore 𝕜 B 𝕜 ι` as a point-indexed core of
rank one, using the preferred chart `Z.indexAt x` at each base point `x` and identifying
`Fin 1 → 𝕜` with `𝕜` by evaluation at `0`. -/
@[expose]
noncomputable def ofScalarCore (Z : VectorBundleCore 𝕜 B 𝕜 ι) : FiniteRankBundleCore 𝕜 B where
  rank := 1
  core :=
    let e := ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜
    { baseSet x := Z.baseSet (Z.indexAt x)
      isOpen_baseSet x := Z.isOpen_baseSet (Z.indexAt x)
      indexAt := id
      mem_baseSet_at x := Z.mem_baseSet_at x
      coordChange x y z :=
        e.symm.toContinuousLinearMap.comp
          ((Z.coordChange (Z.indexAt x) (Z.indexAt y) z).comp e.toContinuousLinearMap)
      coordChange_self x z hz v := by
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          Z.coordChange_self (Z.indexAt x) z hz, ContinuousLinearEquiv.symm_apply_apply]
      continuousOn_coordChange x y :=
        continuousOn_const.clm_comp
          ((Z.continuousOn_coordChange (Z.indexAt x) (Z.indexAt y)).clm_comp continuousOn_const)
      coordChange_comp x y w z hz v := by
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.apply_symm_apply,
          Z.coordChange_comp (Z.indexAt x) (Z.indexAt y) (Z.indexAt w) z hz] }
  indexAt_eq _ := rfl

@[simp]
theorem rank_ofScalarCore (Z : VectorBundleCore 𝕜 B 𝕜 ι) : (ofScalarCore Z).rank = 1 := (rfl)

/-- Chart domain of `ofScalarCore Z` at `x` equals the preferred chart domain of `Z` at `x`. -/
theorem baseSet_ofScalarCore (Z : VectorBundleCore 𝕜 B 𝕜 ι) (x : B) :
    (ofScalarCore Z).core.baseSet x = Z.baseSet (Z.indexAt x) := (rfl)

@[simp]
theorem localTriv_baseSet_ofScalarCore (Z : VectorBundleCore 𝕜 B 𝕜 ι) (x : B) :
    ((ofScalarCore Z).core.localTriv x).baseSet = Z.baseSet (Z.indexAt x) := (rfl)

@[simp]
theorem coordChange_ofScalarCore_apply (Z : VectorBundleCore 𝕜 B 𝕜 ι) (x y z : B)
    (v : Fin (ofScalarCore Z).rank → 𝕜) (k : Fin (ofScalarCore Z).rank) :
    (ofScalarCore Z).core.coordChange x y z v k =
      Z.coordChange (Z.indexAt x) (Z.indexAt y) z (v (0 : Fin 1)) := by
  dsimp [ofScalarCore] at k ⊢
  rw [Subsingleton.elim k 0]
  rfl

/-- Each transition of `ofScalarCore Z` is scalar multiplication by the scalar transition
`Z.coordChange (Z.indexAt x) (Z.indexAt y) z 1`. -/
theorem coordChange_ofScalarCore_eq_smul (Z : VectorBundleCore 𝕜 B 𝕜 ι) (x y z : B) :
    (ofScalarCore Z).core.coordChange x y z =
      Z.coordChange (Z.indexAt x) (Z.indexAt y) z 1 •
        ContinuousLinearMap.id 𝕜 (Fin (ofScalarCore Z).rank → 𝕜) := by
  dsimp +instances only [ofScalarCore]
  ext v k
  rw [Subsingleton.elim k 0]
  change Z.coordChange (Z.indexAt x) (Z.indexAt y) z (v 0) =
    Z.coordChange (Z.indexAt x) (Z.indexAt y) z 1 * v 0
  rw [mul_comm, ← smul_eq_mul, ← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]

/-- The cocycle morphism from `(ofScalarCore Z).core` to `Z` acting on every fibre by
`ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜`. -/
noncomputable def toScalarCore (Z : VectorBundleCore 𝕜 B 𝕜 ι) :
    CoordinateHom (ofScalarCore Z).core Z where
  operator x j :=
    let e : (Fin (ofScalarCore Z).rank → 𝕜) →L[𝕜] 𝕜 :=
      (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).toContinuousLinearMap
    ⟨fun z ↦ (Z.coordChange (Z.indexAt x) j z.1).comp e,
      (continuousOn_iff_continuous_domRestrict.1
        (Z.continuousOn_coordChange (Z.indexAt x) j)).clm_comp_const e⟩
  compatible x x' j j' z hx hx' hj hj' v := by
    dsimp +instances only [ofScalarCore] at v ⊢
    change Z.coordChange j j' z (Z.coordChange (Z.indexAt x) j z (v 0)) =
      Z.coordChange (Z.indexAt x') j' z (Z.coordChange (Z.indexAt x) (Z.indexAt x') z (v 0))
    rw [Z.coordChange_comp (Z.indexAt x) j j' z ⟨⟨hx, hj⟩, hj'⟩,
      Z.coordChange_comp (Z.indexAt x) (Z.indexAt x') j' z ⟨⟨hx, hx'⟩, hj'⟩]

@[simp]
theorem fiberMap_toScalarCore (Z : VectorBundleCore 𝕜 B 𝕜 ι) (x : B) :
    (toScalarCore Z).fiberMap x =
      (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).toContinuousLinearMap := by
  ext v
  rw [CoordinateHom.fiberMap_def]
  exact Z.coordChange_self (Z.indexAt x) x (Z.mem_baseSet_at x) _

/-- Chart operator of `toScalarCore Z` on the overlap of charts `x` and `j`. -/
theorem inChartCoordinates_toScalarCore (Z : VectorBundleCore 𝕜 B 𝕜 ι) (x : B) (j : ι) {z : B}
    (hx : z ∈ (ofScalarCore Z).core.baseSet x) (hj : z ∈ Z.baseSet j) :
    (ofScalarCore Z).core.inChartCoordinates Z x j z ((toScalarCore Z).fiberMap z) =
      (Z.coordChange (Z.indexAt x) j z).comp
        (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).toContinuousLinearMap :=
  ((toScalarCore Z).operator_eq x j ⟨z, hx, hj⟩).symm

/-- The inverse cocycle morphism from `Z` to `(ofScalarCore Z).core`. -/
noncomputable def fromScalarCore (Z : VectorBundleCore 𝕜 B 𝕜 ι) :
    CoordinateHom Z (ofScalarCore Z).core where
  operator i y :=
    let e : 𝕜 →L[𝕜] (Fin (ofScalarCore Z).rank → 𝕜) :=
      (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm.toContinuousLinearMap
    ⟨fun z ↦ e.comp (Z.coordChange i (Z.indexAt y) z.1),
      continuous_const.clm_comp <| continuousOn_iff_continuous_domRestrict.1
        (Z.continuousOn_coordChange i (Z.indexAt y))⟩
  compatible i i' y y' z hi hi' hy hy' v := by
    ext k
    rw [coordChange_ofScalarCore_apply]
    change Z.coordChange (Z.indexAt y) (Z.indexAt y') z (Z.coordChange i (Z.indexAt y) z v) =
      Z.coordChange i' (Z.indexAt y') z (Z.coordChange i i' z v)
    rw [Z.coordChange_comp i (Z.indexAt y) (Z.indexAt y') z ⟨⟨hi, hy⟩, hy'⟩,
      Z.coordChange_comp i i' (Z.indexAt y') z ⟨⟨hi, hi'⟩, hy'⟩]

@[simp]
theorem fiberMap_fromScalarCore (Z : VectorBundleCore 𝕜 B 𝕜 ι) (x : B) :
    (fromScalarCore Z).fiberMap x =
      (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm.toContinuousLinearMap := by
  ext k
  rw [CoordinateHom.fiberMap_def]
  exact Z.coordChange_self (Z.indexAt x) x (Z.mem_baseSet_at x) 1

/-- Chart operator of `fromScalarCore Z` on the overlap of charts `i` and `y`. -/
theorem inChartCoordinates_fromScalarCore (Z : VectorBundleCore 𝕜 B 𝕜 ι) (i : ι) (y : B) {z : B}
    (hi : z ∈ Z.baseSet i) (hy : z ∈ (ofScalarCore Z).core.baseSet y) :
    Z.inChartCoordinates (ofScalarCore Z).core i y z ((fromScalarCore Z).fiberMap z) =
      (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm.toContinuousLinearMap.comp
        (Z.coordChange i (Z.indexAt y) z) :=
  ((fromScalarCore Z).operator_eq i y ⟨z, hi, hy⟩).symm

@[simp]
theorem fromScalarCore_comp_toScalarCore (Z : VectorBundleCore 𝕜 B 𝕜 ι) :
    (fromScalarCore Z).comp (toScalarCore Z) = CoordinateHom.id (ofScalarCore Z).core := by
  apply CoordinateHom.fiberMap_injective
  funext x
  rw [CoordinateHom.fiberMap_comp, fiberMap_fromScalarCore, fiberMap_toScalarCore,
    CoordinateHom.fiberMap_id]
  exact (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).coe_symm_comp_coe

@[simp]
theorem toScalarCore_comp_fromScalarCore (Z : VectorBundleCore 𝕜 B 𝕜 ι) :
    (toScalarCore Z).comp (fromScalarCore Z) = CoordinateHom.id Z := by
  apply CoordinateHom.fiberMap_injective
  funext x
  rw [CoordinateHom.fiberMap_comp, fiberMap_toScalarCore, fiberMap_fromScalarCore,
    CoordinateHom.fiberMap_id]
  exact (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).coe_comp_coe_symm

/-- The homeomorphism of total spaces identifying `(ofScalarCore Z).core` with `Z` over the
identity of `B`, acting on each fibre by evaluation at `0 : Fin 1`. -/
noncomputable def ofScalarCoreHomeomorph (Z : VectorBundleCore 𝕜 B 𝕜 ι) :
    (ofScalarCore Z).core.TotalSpace ≃ₜ Z.TotalSpace where
  toFun := (toScalarCore Z).totalSpaceMap
  invFun := (fromScalarCore Z).totalSpaceMap
  left_inv p := by
    have h := congrFun (congrArg CoordinateHom.totalSpaceMap (fromScalarCore_comp_toScalarCore Z)) p
    rwa [CoordinateHom.totalSpaceMap_comp, Function.comp_apply, CoordinateHom.totalSpaceMap_id,
      id_eq] at h
  right_inv p := by
    have h := congrFun (congrArg CoordinateHom.totalSpaceMap (toScalarCore_comp_fromScalarCore Z)) p
    rwa [CoordinateHom.totalSpaceMap_comp, Function.comp_apply, CoordinateHom.totalSpaceMap_id,
      id_eq] at h
  continuous_toFun := (toScalarCore Z).continuous_totalSpaceMap
  continuous_invFun := (fromScalarCore Z).continuous_totalSpaceMap

@[simp]
theorem coe_ofScalarCoreHomeomorph (Z : VectorBundleCore 𝕜 B 𝕜 ι) :
    ⇑(ofScalarCoreHomeomorph Z) = (toScalarCore Z).totalSpaceMap := (rfl)

@[simp]
theorem coe_ofScalarCoreHomeomorph_symm (Z : VectorBundleCore 𝕜 B 𝕜 ι) :
    ⇑(ofScalarCoreHomeomorph Z).symm = (fromScalarCore Z).totalSpaceMap := (rfl)

/-! ### Cores with identity transition maps -/

/-- The forward cocycle morphism from a core with identity transition maps to `trivial 𝕜 B A.rank`.
-/
private def toTrivialOfCoordChangeEqId (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    A ⟶ trivial 𝕜 B A.rank where
  operator _ _ := ContinuousMap.const _ (ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜))
  compatible i i' _ _ x hi hi' _ _ v := by
    rw [h i i' x hi hi']
    rfl

/-- The inverse cocycle morphism from `trivial 𝕜 B A.rank` to a core with identity transition maps.
-/
private def fromTrivialOfCoordChangeEqId (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    trivial 𝕜 B A.rank ⟶ A where
  operator _ _ := ContinuousMap.const _ (ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜))
  compatible _ _ j j' x _ _ hj hj' v := by
    rw [h j j' x hj hj']
    rfl

/-- Any point-indexed finite-rank core whose transition maps are identities on chart overlaps is
canonically isomorphic to `trivial 𝕜 B A.rank`, with identity fibre maps. Unlike `constIso`, the
chart domains of `A` need not be `Set.univ`. -/
def isoTrivialOfCoordChangeEqId (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    A ≅ trivial 𝕜 B A.rank where
  hom := toTrivialOfCoordChangeEqId A h
  inv := fromTrivialOfCoordChangeEqId A h
  hom_inv_id := hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_id]
    ext v
    rw [CoordinateHom.fiberMap_def, CoordinateHom.fiberMap_def]
    rfl
  inv_hom_id := hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_id]
    ext v
    rw [CoordinateHom.fiberMap_def, CoordinateHom.fiberMap_def]
    rfl

@[simp]
theorem fiberMap_isoTrivialOfCoordChangeEqId_hom (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) (x : B) :
    (isoTrivialOfCoordChangeEqId A h).hom.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
  rw [CoordinateHom.fiberMap_def]
  rfl

@[simp]
theorem fiberMap_isoTrivialOfCoordChangeEqId_inv (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) (x : B) :
    (isoTrivialOfCoordChangeEqId A h).inv.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
  rw [CoordinateHom.fiberMap_def]
  rfl

/-- Chart operator of the forward comparison `(isoTrivialOfCoordChangeEqId A h).hom`. -/
theorem inChartCoordinates_isoTrivialOfCoordChangeEqId_hom (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜))
    (i j : B) {x : B} (hi : x ∈ A.core.baseSet i) :
    A.core.inChartCoordinates (trivial 𝕜 B A.rank).core i j x
        ((isoTrivialOfCoordChangeEqId A h).hom.fiberMap x) =
      ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) :=
  ((isoTrivialOfCoordChangeEqId A h).hom.operator_eq i j ⟨x, hi, Set.mem_univ _⟩).symm

/-- Chart operator of the inverse comparison `(isoTrivialOfCoordChangeEqId A h).inv`. -/
theorem inChartCoordinates_isoTrivialOfCoordChangeEqId_inv (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜))
    (i j : B) {x : B} (hj : x ∈ A.core.baseSet j) :
    (trivial 𝕜 B A.rank).core.inChartCoordinates A.core i j x
        ((isoTrivialOfCoordChangeEqId A h).inv.fiberMap x) =
      ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) :=
  ((isoTrivialOfCoordChangeEqId A h).inv.operator_eq i j ⟨x, Set.mem_univ _, hj⟩).symm

end TauCeti.FiniteRankBundleCore
