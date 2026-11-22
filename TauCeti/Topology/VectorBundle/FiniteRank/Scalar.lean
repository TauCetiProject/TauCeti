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

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §§2–3.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public section

open Bundle Set VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B ι : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

section ScalarCore

variable (Z : VectorBundleCore 𝕜 B 𝕜 ι)

/-- Unexposed underlying `VectorBundleCore` for `ofScalarCore Z` with model fibre `Fin 1 → 𝕜`. -/
noncomputable def ofScalarCoreAux : VectorBundleCore 𝕜 B (Fin 1 → 𝕜) B :=
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

/-- Every base point `x : B` is its own preferred chart index in `ofScalarCoreAux Z`. -/
theorem indexAt_ofScalarCoreAux (x : B) : (ofScalarCoreAux Z).indexAt x = x := (rfl)

-- Expose only the wrapper so `(ofScalarCore Z).rank` reduces definitionally to `1` in
-- dependent fibre statements while keeping the cocycle body in `ofScalarCoreAux` unexposed;
-- Lean's `module` system requires declarations referenced in `@[expose]` bodies to be `public`.
/-- Present a scalar line-bundle core `Z : VectorBundleCore 𝕜 B 𝕜 ι` as a point-indexed core of
rank one, using the preferred chart `Z.indexAt x` at each base point `x` and identifying
`Fin 1 → 𝕜` with `𝕜` by evaluation at `0`. -/
@[expose]
noncomputable def ofScalarCore : FiniteRankBundleCore 𝕜 B where
  rank := 1
  core := ofScalarCoreAux Z
  indexAt_eq := indexAt_ofScalarCoreAux Z

@[simp] theorem rank_ofScalarCore : (ofScalarCore Z).rank = 1 := (rfl)

/-- Chart domain of `ofScalarCore Z` at `x` equals the preferred chart domain of `Z` at `x`. -/
theorem baseSet_ofScalarCore (x : B) : (ofScalarCore Z).core.baseSet x = Z.baseSet (Z.indexAt x) :=
  (rfl)

@[simp] theorem localTriv_baseSet_ofScalarCore (x : B) :
    ((ofScalarCore Z).core.localTriv x).baseSet = Z.baseSet (Z.indexAt x) := (rfl)

/-- Each transition of `ofScalarCore Z` is the preferred transition of `Z` conjugated by the
canonical identification `ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜`. -/
theorem coordChange_ofScalarCore (x y z : B) :
    (ofScalarCore Z).core.coordChange x y z =
      (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm.toContinuousLinearMap.comp
        ((Z.coordChange (Z.indexAt x) (Z.indexAt y) z).comp
          (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).toContinuousLinearMap) :=
  (rfl)

@[simp] theorem coordChange_ofScalarCore_apply (x y z : B) (v : Fin (ofScalarCore Z).rank → 𝕜)
    (k : Fin (ofScalarCore Z).rank) :
    (ofScalarCore Z).core.coordChange x y z v k =
      Z.coordChange (Z.indexAt x) (Z.indexAt y) z (v (0 : Fin 1)) := by
  dsimp +instances only [ofScalarCore, ofScalarCoreAux] at v k ⊢
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_funUnique, ContinuousLinearEquiv.coe_funUnique_symm,
    Function.const_apply, Function.eval, Fin.default_eq_zero]

/-- Each transition of `ofScalarCore Z` is scalar multiplication by the scalar transition
`Z.coordChange (Z.indexAt x) (Z.indexAt y) z 1`. -/
theorem coordChange_ofScalarCore_eq_smul (x y z : B) :
    (ofScalarCore Z).core.coordChange x y z =
      Z.coordChange (Z.indexAt x) (Z.indexAt y) z 1 •
        ContinuousLinearMap.id 𝕜 (Fin (ofScalarCore Z).rank → 𝕜) := by
  ext v k
  rw [coordChange_ofScalarCore_apply, _root_.smul_apply, ContinuousLinearMap.id_apply,
    Pi.smul_apply, smul_eq_mul]
  have hk : k = (0 : Fin 1) :=
    Fin.ext (Nat.lt_one_iff.mp (by simpa [rank_ofScalarCore] using k.isLt))
  rw [hk, mul_comm, ← smul_eq_mul, ← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]

/-- The cocycle morphism from `(ofScalarCore Z).core` to `Z` acting on every fibre by
`ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜`. -/
noncomputable def toScalarCore : CoordinateHom (ofScalarCore Z).core Z where
  operator x j :=
    let e : (Fin (ofScalarCore Z).rank → 𝕜) →L[𝕜] 𝕜 :=
      (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).toContinuousLinearMap
    ⟨fun z ↦ (Z.coordChange (Z.indexAt x) j z.val).comp e,
      (continuousOn_iff_continuous_domRestrict.1
        (Z.continuousOn_coordChange (Z.indexAt x) j)).clm_comp_const e⟩
  compatible x x' j j' z hx hx' hj hj' v := by
    -- `ContinuousMap.coe_mk` cannot fire at implicit transparency because `funUnique (Fin 1) 𝕜 𝕜`
    -- has domain `Fin 1 → 𝕜` while the core fibre is `Fin (ofScalarCore Z).rank → 𝕜`
    -- (definitionally equal via `ofScalarCore`); `calc` reduces both sides directly to the
    -- underlying transitions of `Z`.
    rw [baseSet_ofScalarCore] at hx hx'
    calc Z.coordChange j j' z (Z.coordChange (Z.indexAt x) j z (v (0 : Fin 1)))
        = Z.coordChange (Z.indexAt x) j' z (v (0 : Fin 1)) :=
          Z.coordChange_comp (Z.indexAt x) j j' z ⟨⟨hx, hj⟩, hj'⟩ _
      _ = Z.coordChange (Z.indexAt x') j' z
            (Z.coordChange (Z.indexAt x) (Z.indexAt x') z (v (0 : Fin 1))) :=
          (Z.coordChange_comp (Z.indexAt x) (Z.indexAt x') j' z ⟨⟨hx, hx'⟩, hj'⟩ _).symm

@[simp] theorem fiberMap_toScalarCore (x : B) :
    (toScalarCore Z).fiberMap x =
      (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).toContinuousLinearMap := by
  ext v; rw [CoordinateHom.fiberMap_def]
  exact Z.coordChange_self (Z.indexAt x) x (Z.mem_baseSet_at x) _

/-- Chart operator of `toScalarCore Z` on the overlap of charts `x` and `j`. -/
theorem inChartCoordinates_toScalarCore (x : B) (j : ι) {z : B}
    (hx : z ∈ (ofScalarCore Z).core.baseSet x) (hj : z ∈ Z.baseSet j) :
    (ofScalarCore Z).core.inChartCoordinates Z x j z ((toScalarCore Z).fiberMap z) =
      (Z.coordChange (Z.indexAt x) j z).comp
        (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).toContinuousLinearMap :=
  ((toScalarCore Z).operator_eq x j ⟨z, hx, hj⟩).symm

/-- The inverse cocycle morphism from `Z` to `(ofScalarCore Z).core`. -/
noncomputable def fromScalarCore : CoordinateHom Z (ofScalarCore Z).core where
  operator i y :=
    let e : 𝕜 →L[𝕜] (Fin (ofScalarCore Z).rank → 𝕜) :=
      (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm.toContinuousLinearMap
    ⟨fun z ↦ e.comp (Z.coordChange i (Z.indexAt y) z.val),
      continuous_const.clm_comp <| continuousOn_iff_continuous_domRestrict.1
        (Z.continuousOn_coordChange i (Z.indexAt y))⟩
  compatible i i' y y' z hi hi' hy hy' v := by
    -- As in `toScalarCore`, `funUnique.symm` has codomain `Fin 1 → 𝕜` rather than
    -- `Fin (ofScalarCore Z).rank → 𝕜` (definitionally equal via `ofScalarCore`), so `simp` cannot
    -- reduce the composition with `funUnique.symm` at implicit transparency; `calc` reduces both
    -- sides directly to the underlying transitions of `Z`.
    rw [baseSet_ofScalarCore] at hy hy'
    ext k
    rw [coordChange_ofScalarCore_apply]
    calc Z.coordChange (Z.indexAt y) (Z.indexAt y') z (Z.coordChange i (Z.indexAt y) z v)
        = Z.coordChange i (Z.indexAt y') z v :=
          Z.coordChange_comp i (Z.indexAt y) (Z.indexAt y') z ⟨⟨hi, hy⟩, hy'⟩ v
      _ = Z.coordChange i' (Z.indexAt y') z (Z.coordChange i i' z v) :=
          (Z.coordChange_comp i i' (Z.indexAt y') z ⟨⟨hi, hi'⟩, hy'⟩ v).symm

@[simp] theorem fiberMap_fromScalarCore (x : B) :
    (fromScalarCore Z).fiberMap x =
      (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm.toContinuousLinearMap := by
  ext k; rw [CoordinateHom.fiberMap_def]
  exact Z.coordChange_self (Z.indexAt x) x (Z.mem_baseSet_at x) 1

/-- Chart operator of `fromScalarCore Z` on the overlap of charts `i` and `y`. -/
theorem inChartCoordinates_fromScalarCore (i : ι) (y : B) {z : B}
    (hi : z ∈ Z.baseSet i) (hy : z ∈ (ofScalarCore Z).core.baseSet y) :
    Z.inChartCoordinates (ofScalarCore Z).core i y z ((fromScalarCore Z).fiberMap z) =
      (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm.toContinuousLinearMap.comp
        (Z.coordChange i (Z.indexAt y) z) :=
  ((fromScalarCore Z).operator_eq i y ⟨z, hi, hy⟩).symm

@[simp] theorem fromScalarCore_comp_toScalarCore :
    (fromScalarCore Z).comp (toScalarCore Z) = CoordinateHom.id (ofScalarCore Z).core :=
  CoordinateHom.fiberMap_injective <| funext fun _ ↦ by
    rw [CoordinateHom.fiberMap_comp, fiberMap_fromScalarCore, fiberMap_toScalarCore,
      CoordinateHom.fiberMap_id]
    exact (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).coe_symm_comp_coe

@[simp] theorem toScalarCore_comp_fromScalarCore :
    (toScalarCore Z).comp (fromScalarCore Z) = CoordinateHom.id Z :=
  CoordinateHom.fiberMap_injective <| funext fun _ ↦ by
    rw [CoordinateHom.fiberMap_comp, fiberMap_toScalarCore, fiberMap_fromScalarCore,
      CoordinateHom.fiberMap_id]
    exact (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).coe_comp_coe_symm

/-- The homeomorphism of total spaces identifying `(ofScalarCore Z).core` with `Z` over the
identity of `B`, acting on each fibre by evaluation at `0 : Fin 1`. -/
noncomputable def ofScalarCoreHomeomorph : (ofScalarCore Z).core.TotalSpace ≃ₜ Z.TotalSpace where
  toFun := (toScalarCore Z).totalSpaceMap
  invFun := (fromScalarCore Z).totalSpaceMap
  left_inv p := by
    simpa only [CoordinateHom.totalSpaceMap_comp, CoordinateHom.totalSpaceMap_id,
      Function.comp_apply, id_eq] using
      congrFun (congrArg CoordinateHom.totalSpaceMap (fromScalarCore_comp_toScalarCore Z)) p
  right_inv p := by
    simpa only [CoordinateHom.totalSpaceMap_comp, CoordinateHom.totalSpaceMap_id,
      Function.comp_apply, id_eq] using
      congrFun (congrArg CoordinateHom.totalSpaceMap (toScalarCore_comp_fromScalarCore Z)) p
  continuous_toFun := (toScalarCore Z).continuous_totalSpaceMap
  continuous_invFun := (fromScalarCore Z).continuous_totalSpaceMap

@[simp] theorem coe_ofScalarCoreHomeomorph :
    ⇑(ofScalarCoreHomeomorph Z) = (toScalarCore Z).totalSpaceMap := (rfl)

@[simp] theorem coe_ofScalarCoreHomeomorph_symm :
    ⇑(ofScalarCoreHomeomorph Z).symm = (fromScalarCore Z).totalSpaceMap := (rfl)

end ScalarCore

end TauCeti.FiniteRankBundleCore
