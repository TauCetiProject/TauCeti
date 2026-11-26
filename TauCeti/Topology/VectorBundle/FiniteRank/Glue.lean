/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
import TauCeti.Analysis.Normed.Module.ContinuousInverse

/-!
# Gluing two finite-rank cores along a morphism invertible near a closed set

Let `Φ : P ⟶ Q` be a morphism of point-indexed finite-rank cores of the same rank over `B`, whose
fibre maps are invertible at every point of an open set `V`, and let `K ⊆ V` be closed. The glued
core `GluingData.glue` uses, at a point `i ∈ V`, the chart of `P` labelled `i` restricted to `V`,
and at a point `i ∉ V` the chart of `Q` labelled `i` restricted to the complement of `K`. Its
transitions are those of `P` between charts of `P`, those of `Q` between charts of `Q`, and the
chart operators of `Φ` or their inverses between charts of different kinds. Coordinates of `P`
are carried to those of `Q` by reindexing along the rank equality (`GluingData.rankEquiv`).

The glued core is isomorphic to `Q` (`GluingData.glueIso`): its chart operators are those of `Φ`
from charts of `P`, and transitions of `Q` from charts of `Q`. Over `K` only charts of `P` occur
(`GluingData.mem_V_of_mem_baseSet_glue`), and there the transitions of the glued core are those
of `P` (`GluingData.coordChange_of_mem_of_mem`). The bundle is therefore unchanged up to
isomorphism, while near `K` it is presented by the atlas of `P`.

All cocycle identities reduce to one statement: reading a chart of the glued core in a chart of
`Q` (`GluingData.chartToQ`) is compatible with the transitions on both sides
(`GluingData.coordChange_comp_chartToQ`, `GluingData.chartToQ_comp_coordChange`), and is
invertible (`GluingData.isInvertible_chartToQ`).

The construction uses `VectorBundleCore.CoordinateHom` and its inversion
`VectorBundleCore.CoordinateHom.invOfIsInvertible`.
-/

public section

noncomputable section

open Bundle CategoryTheory Set VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {P Q : FiniteRankBundleCore 𝕜 B}

/-- Data for gluing `P` near a closed set `K` to `Q` away from `K` along a morphism `Φ : P ⟶ Q`:
equal ranks, and an open set `V` containing `K` at whose points `Φ` is invertible. -/
structure GluingData (Φ : P ⟶ Q) where
  /-- The two cores have the same rank. -/
  rank_eq : P.rank = Q.rank
  /-- The open set at whose points `Φ` is invertible; its points label charts of `P`. -/
  V : Set B
  /-- The closed set over which only charts of `P` are used. -/
  K : Set B
  /-- The charts of `P` are restricted to the open set `V`. -/
  isOpen_V : IsOpen V
  /-- The charts of `Q` are restricted to the open complement of `K`. -/
  isClosed_K : IsClosed K
  /-- `K` lies in `V`, so every point lies in the chart of the glued core labelled by itself. -/
  K_subset_V : K ⊆ V
  /-- `Φ` is invertible at every point of `V`. -/
  isInvertible_fiberMap : ∀ x ∈ V, (Φ.fiberMap x).IsInvertible

namespace GluingData

variable {Φ : P ⟶ Q} (D : GluingData Φ) {i j k k' x : B}

/-- Coordinates of `P` read as coordinates of `Q` by reindexing along the rank equality. -/
def rankEquiv : (Fin P.rank → 𝕜) ≃L[𝕜] (Fin Q.rank → 𝕜) :=
  ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr D.rank_eq)

@[simp] theorem rankEquiv_apply (v : Fin P.rank → 𝕜) (l : Fin Q.rank) :
    D.rankEquiv v l = v (Fin.cast D.rank_eq.symm l) := by
  simp [rankEquiv, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

/-- Reindexing back and then forward is the identity, in the form composed with a further map. -/
@[simp] theorem rankEquiv_symm_comp_rankEquiv_comp {m : ℕ}
    (f : (Fin m → 𝕜) →L[𝕜] (Fin P.rank → 𝕜)) :
    D.rankEquiv.symm.toContinuousLinearMap.comp (D.rankEquiv.toContinuousLinearMap.comp f) = f := by
  ext v : 1
  exact D.rankEquiv.symm_apply_apply (f v)

open Classical in
/-- The chart domain of the glued core labelled by `i`: the chart of `P` inside `V` when `i ∈ V`,
and the chart of `Q` outside `K` otherwise. -/
def baseSet (i : B) : Set B :=
  if i ∈ D.V then P.core.baseSet i ∩ D.V else Q.core.baseSet i ∩ D.Kᶜ

theorem baseSet_of_mem (hi : i ∈ D.V) : D.baseSet i = P.core.baseSet i ∩ D.V := ite_eq_left hi

theorem baseSet_of_notMem (hi : i ∉ D.V) : D.baseSet i = Q.core.baseSet i ∩ D.Kᶜ := ite_eq_right hi

theorem baseSet_subset_of_mem (hi : i ∈ D.V) : D.baseSet i ⊆ P.core.baseSet i :=
  D.baseSet_of_mem hi ▸ inter_subset_left

theorem baseSet_subset_of_notMem (hi : i ∉ D.V) : D.baseSet i ⊆ Q.core.baseSet i :=
  D.baseSet_of_notMem hi ▸ inter_subset_left

/-- The overlap of two charts of the glued core coming from `P` lies in the overlap of the charts of
`P`. -/
theorem baseSet_inter_subset_of_mem_of_mem (hi : i ∈ D.V) (hj : j ∈ D.V) :
    D.baseSet i ∩ D.baseSet j ⊆ P.core.baseSet i ∩ P.core.baseSet j :=
  inter_subset_inter (D.baseSet_subset_of_mem hi) (D.baseSet_subset_of_mem hj)

/-- The overlap of a chart of the glued core coming from `Q` with one coming from `P` lies in the
overlap of the chart of `P` with the chart of `Q`. -/
theorem baseSet_inter_subset_of_notMem_of_mem (hi : i ∉ D.V) (hj : j ∈ D.V) :
    D.baseSet i ∩ D.baseSet j ⊆ P.core.baseSet j ∩ Q.core.baseSet i :=
  fun _ hx ↦ ⟨D.baseSet_subset_of_mem hj hx.2, D.baseSet_subset_of_notMem hi hx.1⟩

/-- The overlap of a chart of the glued core with one coming from `Q` lies in the overlap of the
first with the chart of `Q`. -/
theorem baseSet_inter_subset_of_notMem (hj : j ∉ D.V) :
    D.baseSet i ∩ D.baseSet j ⊆ D.baseSet i ∩ Q.core.baseSet j :=
  inter_subset_inter_right _ (D.baseSet_subset_of_notMem hj)

theorem isOpen_baseSet (i : B) : IsOpen (D.baseSet i) := by
  by_cases hi : i ∈ D.V
  · rw [D.baseSet_of_mem hi]; exact (P.core.isOpen_baseSet i).inter D.isOpen_V
  · rw [D.baseSet_of_notMem hi]; exact (Q.core.isOpen_baseSet i).inter D.isClosed_K.isOpen_compl

theorem mem_baseSet_self (x : B) : x ∈ D.baseSet x := by
  by_cases hx : x ∈ D.V
  · rw [D.baseSet_of_mem hx]; exact ⟨P.mem_baseSet_self x, hx⟩
  · rw [D.baseSet_of_notMem hx]; exact ⟨Q.mem_baseSet_self x, fun hK ↦ hx (D.K_subset_V hK)⟩

open Classical in
/-- The chart of the glued core labelled `i`, read in the chart of `Q` labelled `k` at `x`: through
`Φ` from a chart of `P`, and by the transition of `Q` from a chart of `Q`. -/
def chartToQ (i k x : B) : (Fin Q.rank → 𝕜) →L[𝕜] (Fin Q.rank → 𝕜) :=
  if i ∈ D.V then
    (P.core.inChartCoordinates Q.core i k x (Φ.fiberMap x)).comp
      D.rankEquiv.symm.toContinuousLinearMap
  else Q.core.coordChange i k x

theorem chartToQ_of_mem (hi : i ∈ D.V) :
    D.chartToQ i k x = (P.core.inChartCoordinates Q.core i k x (Φ.fiberMap x)).comp
      D.rankEquiv.symm.toContinuousLinearMap := by
  rw [chartToQ, ite_eq_left hi]

/-- From a chart of `P`, reading in a chart of `Q` is the chart operator of `Φ`. -/
theorem chartToQ_eq_operator (hi : i ∈ D.V) (hx : x ∈ P.core.baseSet i)
    (hk : x ∈ Q.core.baseSet k) :
    D.chartToQ i k x =
      (Φ.operator i k ⟨x, hx, hk⟩).comp D.rankEquiv.symm.toContinuousLinearMap := by
  rw [D.chartToQ_of_mem hi, Φ.operator_eq]

theorem chartToQ_of_notMem (hi : i ∉ D.V) : D.chartToQ i k x = Q.core.coordChange i k x := by
  rw [chartToQ, ite_eq_right hi]

/-- Reading a chart of the glued core in two charts of `Q` differs by the transition of `Q`. -/
theorem coordChange_comp_chartToQ (hx : x ∈ D.baseSet i) (hk : x ∈ Q.core.baseSet k)
    (hk' : x ∈ Q.core.baseSet k') :
    (Q.core.coordChange k k' x).comp (D.chartToQ i k x) = D.chartToQ i k' x := by
  by_cases hi : i ∈ D.V
  · have hP := D.baseSet_subset_of_mem hi hx
    have h := Φ.coordChange_comp_operator i i k k' x hP hP hk hk'
    rw [P.core.coordChange_self_eq_id hP, ContinuousLinearMap.comp_id] at h
    rw [D.chartToQ_eq_operator hi hP hk, D.chartToQ_eq_operator hi hP hk',
      ← ContinuousLinearMap.comp_assoc, h]
  · rw [D.chartToQ_of_notMem hi, D.chartToQ_of_notMem hi]
    exact Q.core.coordChange_linear_comp i k k' x ⟨⟨D.baseSet_subset_of_notMem hi hx, hk⟩, hk'⟩

/-- From a chart of `P` in the glued core, the chart operator of `Φ` is invertible. -/
theorem isInvertible_inChartCoordinates (hj : j ∈ D.V) (hx : x ∈ D.baseSet j)
    (hk : x ∈ Q.core.baseSet k) :
    (P.core.inChartCoordinates Q.core j k x (Φ.fiberMap x)).IsInvertible := by
  rw [D.baseSet_of_mem hj] at hx
  rw [← Φ.operator_eq j k ⟨x, hx.1, hk⟩]
  exact (Φ.operator_isInvertible_iff hx.1 hk).2 (D.isInvertible_fiberMap x hx.2)

/-- A chart of the glued core read in a chart of `Q` is invertible. -/
theorem isInvertible_chartToQ (hx : x ∈ D.baseSet i) (hk : x ∈ Q.core.baseSet k) :
    (D.chartToQ i k x).IsInvertible := by
  by_cases hi : i ∈ D.V
  · rw [D.chartToQ_of_mem hi]
    exact (D.isInvertible_inChartCoordinates hi hx hk).comp
      ContinuousLinearMap.isInvertible_equiv
  · rw [D.chartToQ_of_notMem hi]
    exact Q.core.isInvertible_coordChange (D.baseSet_subset_of_notMem hi hx) hk

theorem continuousOn_chartToQ (i k : B) :
    ContinuousOn (D.chartToQ i k) (D.baseSet i ∩ Q.core.baseSet k) := by
  by_cases hi : i ∈ D.V
  · exact ((continuousOn_inChartCoordinates Φ.continuous_fiberMap.continuousOn).mono
      (inter_subset_inter_left _ (D.baseSet_subset_of_mem hi))).clm_comp
      continuousOn_const |>.congr fun x _ ↦ D.chartToQ_of_mem hi
  · exact ((Q.core.continuousOn_coordChange i k).mono
      (inter_subset_inter_left _ (D.baseSet_subset_of_notMem hi))).congr
      fun x _ ↦ D.chartToQ_of_notMem hi

open Classical in
/-- The transitions of the glued core: those of `P` between charts of `P`, those of `Q` between
charts of `Q`, the chart operators of `Φ` from a chart of `P` to one of `Q`, and their inverses
from a chart of `Q` to one of `P`. -/
def coordChange (i j x : B) : (Fin Q.rank → 𝕜) →L[𝕜] (Fin Q.rank → 𝕜) :=
  if j ∈ D.V then
    if i ∈ D.V then
      D.rankEquiv.toContinuousLinearMap.comp
        ((P.core.coordChange i j x).comp D.rankEquiv.symm.toContinuousLinearMap)
    else D.rankEquiv.toContinuousLinearMap.comp
      (P.core.inChartCoordinates Q.core j i x (Φ.fiberMap x)).inverse
  else D.chartToQ i j x

theorem coordChange_of_mem_of_mem (hi : i ∈ D.V) (hj : j ∈ D.V) :
    D.coordChange i j x = D.rankEquiv.toContinuousLinearMap.comp
      ((P.core.coordChange i j x).comp D.rankEquiv.symm.toContinuousLinearMap) := by
  rw [coordChange, ite_eq_left hj, ite_eq_left hi]

theorem coordChange_of_notMem_of_mem (hi : i ∉ D.V) (hj : j ∈ D.V) :
    D.coordChange i j x = D.rankEquiv.toContinuousLinearMap.comp
      (P.core.inChartCoordinates Q.core j i x (Φ.fiberMap x)).inverse := by
  rw [coordChange, ite_eq_left hj, ite_eq_right hi]

theorem coordChange_of_notMem (hj : j ∉ D.V) : D.coordChange i j x = D.chartToQ i j x := by
  rw [coordChange, ite_eq_right hj]

/-- Changing charts of the glued core is compatible with reading them in any chart of `Q`. This
single identity yields every cocycle condition. -/
theorem chartToQ_comp_coordChange (hi : x ∈ D.baseSet i) (hj : x ∈ D.baseSet j)
    (hk : x ∈ Q.core.baseSet k) :
    (D.chartToQ j k x).comp (D.coordChange i j x) = D.chartToQ i k x := by
  by_cases hjV : j ∈ D.V
  · have hPj := D.baseSet_subset_of_mem hjV hj
    by_cases hiV : i ∈ D.V
    · -- Both are charts of `P`: `Φ` intertwines the transition of `P` with that of `Q` from `k`.
      have h := Φ.coordChange_comp_operator i j k k x (D.baseSet_subset_of_mem hiV hi) hPj hk hk
      rw [Q.core.coordChange_self_eq_id hk, ContinuousLinearMap.id_comp] at h
      simp only [D.coordChange_of_mem_of_mem hiV hjV, D.chartToQ_eq_operator hjV hPj hk,
        D.chartToQ_eq_operator hiV (D.baseSet_subset_of_mem hiV hi) hk,
        ContinuousLinearMap.comp_assoc, rankEquiv_symm_comp_rankEquiv_comp, h]
    · -- From a chart of `Q` to one of `P`: the transition inverts the chart operator of `Φ`.
      have hQi := D.baseSet_subset_of_notMem hiV hi
      have h := Φ.coordChange_comp_operator j j i k x hPj hPj hQi hk
      rw [P.core.coordChange_self_eq_id hPj, ContinuousLinearMap.comp_id] at h
      simp only [D.coordChange_of_notMem_of_mem hiV hjV, D.chartToQ_eq_operator hjV hPj hk,
        D.chartToQ_of_notMem hiV, ← Φ.operator_eq j i ⟨x, hPj, hQi⟩, ← h,
        ContinuousLinearMap.comp_assoc, rankEquiv_symm_comp_rankEquiv_comp,
        ((Φ.operator_isInvertible_iff hPj hQi).2 (D.isInvertible_fiberMap x
          (D.baseSet_of_mem hjV ▸ hj).2)).self_comp_inverse, ContinuousLinearMap.comp_id]
  · rw [D.coordChange_of_notMem hjV, D.chartToQ_of_notMem hjV]
    exact D.coordChange_comp_chartToQ hi (D.baseSet_subset_of_notMem hjV hj) hk

theorem coordChange_self (hx : x ∈ D.baseSet i) (v : Fin Q.rank → 𝕜) :
    D.coordChange i i x v = v := by
  have h := D.chartToQ_comp_coordChange hx hx (Q.mem_baseSet_self x)
  exact (D.isInvertible_chartToQ hx (Q.mem_baseSet_self x)).injective (congrArg (· v) h)

theorem coordChange_comp (hx : x ∈ D.baseSet i ∩ D.baseSet j ∩ D.baseSet k)
    (v : Fin Q.rank → 𝕜) :
    D.coordChange j k x (D.coordChange i j x v) = D.coordChange i k x v := by
  obtain ⟨⟨hi, hj⟩, hk⟩ := hx
  have hq := Q.mem_baseSet_self x
  apply (D.isInvertible_chartToQ hk hq).injective
  have h₁ := congrArg (· (D.coordChange i j x v)) (D.chartToQ_comp_coordChange hj hk hq)
  have h₂ := congrArg (· v) (D.chartToQ_comp_coordChange hi hj hq)
  have h₃ := congrArg (· v) (D.chartToQ_comp_coordChange hi hk hq)
  simp only [ContinuousLinearMap.comp_apply] at h₁ h₂ h₃
  rw [h₁, h₂, h₃]

theorem continuousOn_coordChange (i j : B) :
    ContinuousOn (D.coordChange i j) (D.baseSet i ∩ D.baseSet j) := by
  by_cases hjV : j ∈ D.V
  · by_cases hiV : i ∈ D.V
    · exact (continuousOn_const.clm_comp (((P.core.continuousOn_coordChange i j).mono
        (D.baseSet_inter_subset_of_mem_of_mem hiV hjV)).clm_comp
        continuousOn_const)).congr fun x _ ↦ D.coordChange_of_mem_of_mem hiV hjV
    · have hs := D.baseSet_inter_subset_of_notMem_of_mem hiV hjV
      have hc := (continuousOn_inChartCoordinates (Φ.continuous_fiberMap.continuousOn) (i := j)
        (j := i)).mono hs
      have hinv : ∀ x ∈ D.baseSet i ∩ D.baseSet j,
          (P.core.inChartCoordinates Q.core j i x (Φ.fiberMap x)).IsInvertible :=
        fun x hx ↦ D.isInvertible_inChartCoordinates hjV hx.2 (hs hx).2
      exact (continuousOn_const.clm_comp fun x hx ↦ (hc x hx).clm_inverse_of_eventually_isInvertible
        (hinv x hx) (eventually_nhdsWithin_of_forall hinv)).congr
        fun x _ ↦ D.coordChange_of_notMem_of_mem hiV hjV
  · exact ((D.continuousOn_chartToQ i j).mono (D.baseSet_inter_subset_of_notMem hjV)).congr
      fun x _ ↦ D.coordChange_of_notMem hjV

/-- The glued core: at a point of `V` the chart of `P` labelled by it, restricted to `V`, and at
any other point the chart of `Q` labelled by it, restricted to the complement of `K`. -/
-- Expose the rank projection so the dependent fibre model reduces to `Fin Q.rank → 𝕜`, also during
-- implicit-argument matching of coordinate-map lemmas.
@[expose, implicit_reducible]
def glue : FiniteRankBundleCore 𝕜 B where
  rank := Q.rank
  core :=
    { baseSet := D.baseSet
      isOpen_baseSet := D.isOpen_baseSet
      indexAt := id
      mem_baseSet_at := D.mem_baseSet_self
      coordChange := D.coordChange
      coordChange_self := fun _ _ hx v ↦ D.coordChange_self hx v
      continuousOn_coordChange := D.continuousOn_coordChange
      coordChange_comp := fun _ _ _ _ hx v ↦ D.coordChange_comp hx v }
  indexAt_eq _ := rfl

@[simp] theorem rank_glue : D.glue.rank = Q.rank := (rfl)

/-- Stated for the whole family of chart domains, so that the left-hand side is simp-normal: the
applied form `D.glue.core.baseSet i` is rewritten by `VectorBundleCore.baseSet_at` first. -/
@[simp] theorem baseSet_glue : D.glue.core.baseSet = D.baseSet := (rfl)

@[simp] theorem localTriv_baseSet_glue (i : B) : (D.glue.core.localTriv i).baseSet = D.baseSet i :=
  (rfl)

@[simp] theorem coordChange_glue (i j x : B) :
    D.glue.core.coordChange i j x = D.coordChange i j x := (rfl)

/-- Over `K`, every chart of the glued core containing the point is a chart of `P`. -/
theorem mem_V_of_mem_baseSet_glue (hx : x ∈ D.K) (hi : x ∈ D.glue.core.baseSet i) : i ∈ D.V := by
  by_contra hiV
  rw [baseSet_glue, D.baseSet_of_notMem hiV] at hi
  exact hi.2 hx

/-- The comparison of the glued core with `Q`: from a chart of `P` the chart operators of `Φ`, and
from a chart of `Q` the transitions of `Q`. -/
def glueHom : D.glue ⟶ Q where
  operator i k := ⟨fun y ↦ D.chartToQ i k y, (D.continuousOn_chartToQ i k).domRestrict⟩
  compatible i i' k k' x hi hi' hk hk' v := by
    have h₁ := congrArg (· v) (D.coordChange_comp_chartToQ hi hk hk')
    have h₂ := congrArg (· v) (D.chartToQ_comp_coordChange hi hi' hk')
    simp only [ContinuousLinearMap.comp_apply] at h₁ h₂
    exact h₁.trans h₂.symm

/-- Stated for the whole chart operator, so that the left-hand side is simp-normal: applied to a
point, the type of the point is rewritten by `VectorBundleCore.baseSet_at` first. -/
@[simp] theorem operator_glueHom (i k : B) :
    D.glueHom.operator i k =
      ⟨fun y ↦ D.chartToQ i k y, (D.continuousOn_chartToQ i k).domRestrict⟩ := (rfl)

/-- In charts, the comparison with `Q` reads each chart of the glued core in the chart of `Q`. -/
theorem inChartCoordinates_glueHom (hi : x ∈ D.glue.core.baseSet i)
    (hk : x ∈ Q.core.baseSet k) :
    D.glue.core.inChartCoordinates Q.core i k x (D.glueHom.fiberMap x) = D.chartToQ i k x :=
  (D.glueHom.operator_eq i k ⟨x, hi, hk⟩).symm

/-- On the fibre at `x`, the comparison with `Q` reads the chart of the glued core at `x` in the
chart of `Q` at `x`. -/
theorem fiberMap_glueHom (x : B) : D.glueHom.fiberMap x = D.chartToQ x x x :=
  -- `operator_self` at `x`, whose left-hand side is `chartToQ x x x` by `operator_glueHom`.
  (operator_self D.glueHom x).symm

/-- At a point of `V`, the comparison with `Q` is `Φ` after reindexing coordinates. -/
theorem fiberMap_glueHom_of_mem (hx : x ∈ D.V) :
    D.glueHom.fiberMap x = (Φ.fiberMap x).comp D.rankEquiv.symm.toContinuousLinearMap := by
  rw [D.fiberMap_glueHom, D.chartToQ_eq_operator hx (P.mem_baseSet_self x) (Q.mem_baseSet_self x),
    operator_self]

/-- Away from `V`, the comparison with `Q` is the identity. -/
theorem fiberMap_glueHom_of_notMem (hx : x ∉ D.V) :
    D.glueHom.fiberMap x = ContinuousLinearMap.id 𝕜 (Fin Q.rank → 𝕜) := by
  rw [D.fiberMap_glueHom, D.chartToQ_of_notMem hx]
  exact Q.coordChange_self x

theorem isInvertible_fiberMap_glueHom (x : B) : (D.glueHom.fiberMap x).IsInvertible := by
  by_cases hx : x ∈ D.V
  · rw [D.fiberMap_glueHom_of_mem hx]
    exact (D.isInvertible_fiberMap x hx).comp ContinuousLinearMap.isInvertible_equiv
  · rw [D.fiberMap_glueHom_of_notMem hx]
    exact ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl 𝕜 _)

/-- The glued core is isomorphic to `Q`, by `Φ` at points of `V` and the identity elsewhere. -/
def glueIso : D.glue ≅ Q where
  hom := D.glueHom
  inv := D.glueHom.invOfIsInvertible D.isInvertible_fiberMap_glueHom
  hom_inv_id := D.glueHom.invOfIsInvertible_comp D.isInvertible_fiberMap_glueHom
  inv_hom_id := D.glueHom.comp_invOfIsInvertible D.isInvertible_fiberMap_glueHom

@[simp] theorem glueIso_hom : D.glueIso.hom = D.glueHom := (rfl)

@[simp] theorem glueIso_inv :
    D.glueIso.inv = D.glueHom.invOfIsInvertible D.isInvertible_fiberMap_glueHom := (rfl)

/-- In charts, the inverse comparison inverts the reading of a chart of the glued core in a chart
of `Q`. -/
theorem inChartCoordinates_glueIso_inv (hk : x ∈ Q.core.baseSet k)
    (hi : x ∈ D.glue.core.baseSet i) :
    Q.core.inChartCoordinates D.glue.core k i x (D.glueIso.inv.fiberMap x) =
      (D.chartToQ i k x).inverse := by
  rw [← D.glueIso.inv.operator_eq k i ⟨x, hk, hi⟩]
  exact CoordinateHom.operator_invOfIsInvertible_apply _ _ k i ⟨x, hk, hi⟩

end GluingData

end TauCeti.FiniteRankBundleCore

end
