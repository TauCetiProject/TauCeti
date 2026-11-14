/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Basic
public import TauCeti.Topology.Algebra.Module.Equiv.Fin
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.LocallyConstant.Algebra

import TauCeti.Topology.LocallyConstant.Fiber
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Whitney sums of variable-rank bundle atlases

`TauCeti.FiniteRankAtlas.whitneySum A D` forms the Whitney sum of two variable-rank atlases, with
rank `A.rank + D.rank : LocallyConstant X ℕ`. Because a single total-rank stratum
`{x : X | (A.rank + D.rank) x = n}` may decompose into clopen pieces with distinct summand-rank
pairs `(A.rank x, D.rank x)`, each chart centred at `i` is supported on the clopen-intersected
domain where both summands lie in their preferred charts at `i` (`chartBaseSet_whitneySum`, built
from `FiniteRankAtlas.chartBaseSet`), with block-diagonal coordinate changes conjugated along
`TauCeti.splitCoords` (`splitCoords_whitneyCharts_coordChange`,
`whitneyCharts_coordChange_splitCoords_symm`, `whitneyCharts_coordChange_of_not_rank_eq`).

`whitneySumTotalSpaceHomeomorph` identifies `TotalSpace Unit (whitneySum A D).Fiber` with
Mathlib's native direct-sum bundle `TotalSpace (Unit × Unit) (A.Fiber ×ᵇ D.Fiber)`, over the
identity of `X` and by `whitneySumFiberEquiv` (`TauCeti.splitCoords`) on every fibre. This yields
the two-component continuity characterizations `continuous_mk_whitneySum_iff` and
`continuous_whitneySum_iff`. No compactness, separation, nonemptiness, bounded-rank, or
scalar-completeness hypothesis is required.

The block-coordinate construction and `Bundle.Prod` comparison parallel the constant-rank
development for `TauCeti.FiniteRankBundleCore` in
`TauCeti.Topology.VectorBundle.FiniteRank.Biproduct`, lifting coordinate splitting along
`TauCeti.splitCoords` and Mathlib's `FiberBundle.Prod` topology to variable-rank atlases.
Categorical biproducts, universal-property pairing/copairing, and coherence isomorphisms are
developed in `TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Biproduct`.

## References

* M. F. Atiyah, *K-Theory*, §1.1–1.2.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, §3.
-/

public section

open Bundle Set

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

private def blockCoordChange (A D : FiniteRankAtlas 𝕜 X) {n : ℕ} (a d : ℕ) (had : a + d = n)
    (i j x : {x : X // (A.rank + D.rank) x = n})
    (hi : A.rank i.1 = a ∧ D.rank i.1 = d)
    (hj : A.rank j.1 = a ∧ D.rank j.1 = d)
    (hx : A.rank x.1 = a ∧ D.rank x.1 = d) :
    (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜) :=
  let e : (Fin n → 𝕜) ≃L[𝕜] (Fin a → 𝕜) × (Fin d → 𝕜) :=
    (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜) (finCongr had)).symm.trans
      (splitCoords (𝕜 := 𝕜) a d)
  e.symm.toContinuousLinearMap.comp
    ((((A.charts a).coordChange ⟨i.1, hi.1⟩ ⟨j.1, hj.1⟩ ⟨x.1, hx.1⟩).prodMap
      ((D.charts d).coordChange ⟨i.1, hi.2⟩ ⟨j.1, hj.2⟩ ⟨x.1, hx.2⟩)).comp
      e.toContinuousLinearMap)

private theorem blockCoordChange_congr (A D : FiniteRankAtlas 𝕜 X) {n a d a' d' : ℕ}
    (had : a + d = n) (had' : a' + d' = n)
    (i j x : {x : X // (A.rank + D.rank) x = n})
    (hi : A.rank i.1 = a ∧ D.rank i.1 = d) (hi' : A.rank i.1 = a' ∧ D.rank i.1 = d')
    (hj : A.rank j.1 = a ∧ D.rank j.1 = d) (hj' : A.rank j.1 = a' ∧ D.rank j.1 = d')
    (hx : A.rank x.1 = a ∧ D.rank x.1 = d) (hx' : A.rank x.1 = a' ∧ D.rank x.1 = d') :
    blockCoordChange A D a d had i j x hi hj hx =
      blockCoordChange A D a' d' had' i j x hi' hj' hx' := by
  have ha : a = a' := hi.1.symm.trans hi'.1
  have hd : d = d' := hi.2.symm.trans hi'.2
  subst ha; subst hd; rfl

private def whitneyCoordChange (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (i j x : {x : X // (A.rank + D.rank) x = n}) :
    (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜) :=
  if h : (A.rank i.1 = A.rank j.1 ∧ D.rank i.1 = D.rank j.1) ∧
      (A.rank x.1 = A.rank j.1 ∧ D.rank x.1 = D.rank j.1) then
    blockCoordChange A D (A.rank j.1) (D.rank j.1) j.2 i j x h.1 ⟨rfl, rfl⟩ h.2
  else
    ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)

private theorem whitneyCoordChange_eq_blockCoordChange (A D : FiniteRankAtlas 𝕜 X) {n a d : ℕ}
    (had : a + d = n) (i j x : {x : X // (A.rank + D.rank) x = n})
    (hi : A.rank i.1 = a ∧ D.rank i.1 = d)
    (hj : A.rank j.1 = a ∧ D.rank j.1 = d)
    (hx : A.rank x.1 = a ∧ D.rank x.1 = d) :
    whitneyCoordChange A D n i j x = blockCoordChange A D a d had i j x hi hj hx := by
  have hcond : (A.rank i.1 = A.rank j.1 ∧ D.rank i.1 = D.rank j.1) ∧
      (A.rank x.1 = A.rank j.1 ∧ D.rank x.1 = D.rank j.1) :=
    ⟨⟨hi.1.trans hj.1.symm, hi.2.trans hj.2.symm⟩,
      ⟨hx.1.trans hj.1.symm, hx.2.trans hj.2.symm⟩⟩
  simp only [whitneyCoordChange, hcond]
  exact blockCoordChange_congr A D j.2 had i j x hcond.1 hi ⟨rfl, rfl⟩ hj hcond.2 hx

private theorem whitneyCoordChange_self (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (i x : {x : X // (A.rank + D.rank) x = n})
    (hx : x ∈ Subtype.val ⁻¹' (A.chartBaseSet i.1 ∩ D.chartBaseSet i.1))
    (v : Fin n → 𝕜) :
    whitneyCoordChange A D n i i x v = v := by
  have hxi : A.rank x.1 = A.rank i.1 ∧ D.rank x.1 = D.rank i.1 :=
    ⟨A.rank_eq_of_mem_chartBaseSet hx.1, D.rank_eq_of_mem_chartBaseSet hx.2⟩
  rw [whitneyCoordChange_eq_blockCoordChange A D i.2 i i x ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ hxi]
  simp only [blockCoordChange, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply',
    (A.charts (A.rank i.1)).coordChange_self ⟨i.1, rfl⟩ ⟨x.1, hxi.1⟩
      (mem_baseSet_charts_iff.2 hx.1),
    (D.charts (D.rank i.1)).coordChange_self ⟨i.1, rfl⟩ ⟨x.1, hxi.2⟩
      (mem_baseSet_charts_iff.2 hx.2),
    Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]

private theorem continuousOn_whitneyCoordChange (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (i j : {x : X // (A.rank + D.rank) x = n}) :
    ContinuousOn (whitneyCoordChange A D n i j)
      (Subtype.val ⁻¹' (A.chartBaseSet i.1 ∩ D.chartBaseSet i.1) ∩
        Subtype.val ⁻¹' (A.chartBaseSet j.1 ∩ D.chartBaseSet j.1)) := by
  let S : Set {x : X // (A.rank + D.rank) x = n} :=
    Subtype.val ⁻¹' (A.chartBaseSet i.1 ∩ D.chartBaseSet i.1) ∩
      Subtype.val ⁻¹' (A.chartBaseSet j.1 ∩ D.chartBaseSet j.1)
  by_cases hij : A.rank i.1 = A.rank j.1 ∧ D.rank i.1 = D.rank j.1
  · rw [continuousOn_iff_continuous_domRestrict]
    let φA : S → ↑((A.charts (A.rank j.1)).baseSet ⟨i.1, hij.1⟩ ∩
        (A.charts (A.rank j.1)).baseSet ⟨j.1, rfl⟩) := fun x =>
      ⟨⟨x.1.1, A.rank_eq_of_mem_chartBaseSet x.2.2.1⟩,
        mem_baseSet_charts_iff.2 x.2.1.1,
        mem_baseSet_charts_iff.2 x.2.2.1⟩
    let φD : S → ↑((D.charts (D.rank j.1)).baseSet ⟨i.1, hij.2⟩ ∩
        (D.charts (D.rank j.1)).baseSet ⟨j.1, rfl⟩) := fun x =>
      ⟨⟨x.1.1, D.rank_eq_of_mem_chartBaseSet x.2.2.2⟩,
        mem_baseSet_charts_iff.2 x.2.1.2,
        mem_baseSet_charts_iff.2 x.2.2.2⟩
    have hφA : Continuous φA :=
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
    have hφD : Continuous φD :=
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
    have hcA := ((A.charts (A.rank j.1)).continuousOn_coordChange
      ⟨i.1, hij.1⟩ ⟨j.1, rfl⟩).domRestrict.comp hφA
    have hcD := ((D.charts (D.rank j.1)).continuousOn_coordChange
      ⟨i.1, hij.2⟩ ⟨j.1, rfl⟩).domRestrict.comp hφD
    let e : (Fin n → 𝕜) ≃L[𝕜] (Fin (A.rank j.1) → 𝕜) × (Fin (D.rank j.1) → 𝕜) :=
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜) (finCongr j.2)).symm.trans
        (splitCoords (𝕜 := 𝕜) (A.rank j.1) (D.rank j.1))
    refine (((hcA.prod_mapL 𝕜 hcD).clm_comp_const
      e.toContinuousLinearMap).const_clm_comp
      e.symm.toContinuousLinearMap).congr fun x => ?_
    exact (whitneyCoordChange_eq_blockCoordChange A D j.2 i j x.1 hij ⟨rfl, rfl⟩
      ⟨A.rank_eq_of_mem_chartBaseSet x.2.2.1, D.rank_eq_of_mem_chartBaseSet x.2.2.2⟩).symm
  · have hEmpty : S = ∅ := eq_empty_iff_forall_notMem.2 fun x hx => hij
      ⟨(A.rank_eq_of_mem_chartBaseSet hx.1.1).symm.trans (A.rank_eq_of_mem_chartBaseSet hx.2.1),
        (D.rank_eq_of_mem_chartBaseSet hx.1.2).symm.trans (D.rank_eq_of_mem_chartBaseSet hx.2.2)⟩
    dsimp only [S] at hEmpty
    rw [hEmpty]
    exact continuousOn_empty _

private theorem whitneyCoordChange_comp (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (i j k x : {x : X // (A.rank + D.rank) x = n})
    (hx : x ∈ Subtype.val ⁻¹' (A.chartBaseSet i.1 ∩ D.chartBaseSet i.1) ∩
      Subtype.val ⁻¹' (A.chartBaseSet j.1 ∩ D.chartBaseSet j.1) ∩
      Subtype.val ⁻¹' (A.chartBaseSet k.1 ∩ D.chartBaseSet k.1))
    (v : Fin n → 𝕜) :
    whitneyCoordChange A D n j k x (whitneyCoordChange A D n i j x v) =
      whitneyCoordChange A D n i k x v := by
  have hxA_k := A.rank_eq_of_mem_chartBaseSet hx.2.1
  have hxD_k := D.rank_eq_of_mem_chartBaseSet hx.2.2
  have hi : A.rank i.1 = A.rank k.1 ∧ D.rank i.1 = D.rank k.1 :=
    ⟨(A.rank_eq_of_mem_chartBaseSet hx.1.1.1).symm.trans hxA_k,
      (D.rank_eq_of_mem_chartBaseSet hx.1.1.2).symm.trans hxD_k⟩
  have hj : A.rank j.1 = A.rank k.1 ∧ D.rank j.1 = D.rank k.1 :=
    ⟨(A.rank_eq_of_mem_chartBaseSet hx.1.2.1).symm.trans hxA_k,
      (D.rank_eq_of_mem_chartBaseSet hx.1.2.2).symm.trans hxD_k⟩
  rw [whitneyCoordChange_eq_blockCoordChange A D k.2 i j x hi hj ⟨hxA_k, hxD_k⟩,
    whitneyCoordChange_eq_blockCoordChange A D k.2 j k x hj ⟨rfl, rfl⟩ ⟨hxA_k, hxD_k⟩,
    whitneyCoordChange_eq_blockCoordChange A D k.2 i k x hi ⟨rfl, rfl⟩ ⟨hxA_k, hxD_k⟩]
  simp only [blockCoordChange, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_prodMap', Prod.map_apply']
  rw [(A.charts (A.rank k.1)).coordChange_comp ⟨i.1, hi.1⟩ ⟨j.1, hj.1⟩ ⟨k.1, rfl⟩ ⟨x.1, hxA_k⟩
      ⟨⟨mem_baseSet_charts_iff.2 hx.1.1.1, mem_baseSet_charts_iff.2 hx.1.2.1⟩,
        mem_baseSet_charts_iff.2 hx.2.1⟩,
    (D.charts (D.rank k.1)).coordChange_comp ⟨i.1, hi.2⟩ ⟨j.1, hj.2⟩ ⟨k.1, rfl⟩ ⟨x.1, hxD_k⟩
      ⟨⟨mem_baseSet_charts_iff.2 hx.1.1.2, mem_baseSet_charts_iff.2 hx.1.2.2⟩,
        mem_baseSet_charts_iff.2 hx.2.2⟩]

/-- The point-indexed coordinate bundle core on the total-rank-`n` stratum of the Whitney sum of
`A` and `D`, with clopen-intersected chart domains and block-diagonal transitions. -/
def whitneyCharts (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    VectorBundleCore 𝕜 {x : X // (A.rank + D.rank) x = n} (Fin n → 𝕜)
      {x : X // (A.rank + D.rank) x = n} where
  baseSet i := Subtype.val ⁻¹' (A.chartBaseSet i.1 ∩ D.chartBaseSet i.1)
  isOpen_baseSet i :=
    ((A.isOpen_chartBaseSet i.1).inter (D.isOpen_chartBaseSet i.1)).preimage
      continuous_subtype_val
  indexAt := id
  mem_baseSet_at x := ⟨A.mem_chartBaseSet_self x.1, D.mem_chartBaseSet_self x.1⟩
  coordChange := whitneyCoordChange A D n
  coordChange_self := whitneyCoordChange_self A D n
  continuousOn_coordChange := continuousOn_whitneyCoordChange A D n
  coordChange_comp := whitneyCoordChange_comp A D n

@[simp] theorem whitneyCharts_localTriv_baseSet (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (i : {x : X // (A.rank + D.rank) x = n}) :
    ((whitneyCharts A D n).localTriv i).baseSet =
      Subtype.val ⁻¹' (A.chartBaseSet i.1 ∩ D.chartBaseSet i.1) := (rfl)

@[simp] theorem whitneyCharts_indexAt (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (x : {x : X // (A.rank + D.rank) x = n}) :
    (whitneyCharts A D n).indexAt x = x := (rfl)

/-- On any summand-rank decomposition `a + d = n`, splitting `(whitneyCharts A D n).coordChange`
along `splitCoords` applies the two summand coordinate transitions to the two coordinate blocks. -/
theorem splitCoords_whitneyCharts_coordChange (A D : FiniteRankAtlas 𝕜 X) {n a d : ℕ}
    (had : a + d = n) (i j x : {x : X // (A.rank + D.rank) x = n})
    (hi : A.rank i.1 = a ∧ D.rank i.1 = d)
    (hj : A.rank j.1 = a ∧ D.rank j.1 = d)
    (hx : A.rank x.1 = a ∧ D.rank x.1 = d)
    (v : Fin n → 𝕜) :
    splitCoords (𝕜 := 𝕜) a d (((whitneyCharts A D n).coordChange i j x v) ∘ Fin.cast had) =
      ((A.charts a).coordChange ⟨i.1, hi.1⟩ ⟨j.1, hj.1⟩ ⟨x.1, hx.1⟩
        (splitCoords (𝕜 := 𝕜) a d (v ∘ Fin.cast had)).1,
       (D.charts d).coordChange ⟨i.1, hi.2⟩ ⟨j.1, hj.2⟩ ⟨x.1, hx.2⟩
        (splitCoords (𝕜 := 𝕜) a d (v ∘ Fin.cast had)).2) := by
  subst had
  unfold whitneyCharts
  dsimp only
  rw [whitneyCoordChange_eq_blockCoordChange A D rfl i j x hi hj hx]
  have he : ((ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin (a + d) => 𝕜)
      (finCongr (rfl : a + d = a + d))).symm.trans (splitCoords (𝕜 := 𝕜) (M := 𝕜) a d)) =
      splitCoords (𝕜 := 𝕜) (M := 𝕜) a d := by
    apply DFunLike.ext
    intro y
    rw [ContinuousLinearEquiv.trans_apply]
    -- `(ContinuousLinearEquiv.piCongrLeft 𝕜 _ (finCongr rfl)).symm` reduces definitionally to the
    -- identity on coordinates.
    rfl
  simp only [Fin.cast_refl, Function.comp_id, blockCoordChange, he,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_prodMap', Prod.map_apply']

/-- On any summand-rank decomposition `a + d = n`, the coordinate transition of `whitneyCharts`
applies the two summand coordinate transitions blockwise along `splitCoords.symm`. -/
theorem whitneyCharts_coordChange_splitCoords_symm (A D : FiniteRankAtlas 𝕜 X) {n a d : ℕ}
    (had : a + d = n) (i j x : {x : X // (A.rank + D.rank) x = n})
    (hi : A.rank i.1 = a ∧ D.rank i.1 = d)
    (hj : A.rank j.1 = a ∧ D.rank j.1 = d)
    (hx : A.rank x.1 = a ∧ D.rank x.1 = d)
    (u : Fin a → 𝕜) (w : Fin d → 𝕜) :
    (whitneyCharts A D n).coordChange i j x
        ((splitCoords (𝕜 := 𝕜) a d).symm (u, w) ∘ Fin.cast had.symm) =
      (splitCoords (𝕜 := 𝕜) a d).symm
        ((A.charts a).coordChange ⟨i.1, hi.1⟩ ⟨j.1, hj.1⟩ ⟨x.1, hx.1⟩ u,
         (D.charts d).coordChange ⟨i.1, hi.2⟩ ⟨j.1, hj.2⟩ ⟨x.1, hx.2⟩ w) ∘
        Fin.cast had.symm := by
  subst had
  funext k
  simpa only [Fin.cast_refl, Function.comp_id, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply] using
    congrArg (fun p => (splitCoords (𝕜 := 𝕜) a d).symm p k)
      (splitCoords_whitneyCharts_coordChange A D rfl i j x hi hj hx
        ((splitCoords (𝕜 := 𝕜) a d).symm (u, w)))

/-- Outside the clopen locus where `i`, `j`, and `x` share the same summand ranks,
`(whitneyCharts A D n).coordChange i j x` defaults to the identity continuous linear map. -/
theorem whitneyCharts_coordChange_of_not_rank_eq (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (i j x : {x : X // (A.rank + D.rank) x = n})
    (h : ¬((A.rank i.1 = A.rank j.1 ∧ D.rank i.1 = D.rank j.1) ∧
      (A.rank x.1 = A.rank j.1 ∧ D.rank x.1 = D.rank j.1))) :
    (whitneyCharts A D n).coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin n → 𝕜) := by
  simp only [whitneyCharts, whitneyCoordChange, h, ↓reduceDIte]

/-- The Whitney sum of two variable-rank bundle atlases, with rank `A.rank + D.rank` and
clopen-intersected block-diagonal charts on each total-rank stratum. -/
-- Expose the rank projection so `(whitneySum A D).Fiber x` reduces to
-- `Fin (A.rank x + D.rank x) → 𝕜`.
@[expose] def whitneySum (A D : FiniteRankAtlas 𝕜 X) : FiniteRankAtlas 𝕜 X where
  rank := A.rank + D.rank
  charts := whitneyCharts A D
  indexAt_eq _ := whitneyCharts_indexAt A D _

@[simp] theorem rank_whitneySum (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySum A D).rank = A.rank + D.rank := (rfl)

@[simp] theorem charts_whitneySum (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (whitneySum A D).charts n = whitneyCharts A D n := (rfl)

/-- The preferred chart domain of `whitneySum A D` at `z` is the intersection of the preferred
chart domains of `A` and `D` at `z`. -/
@[simp] theorem chartBaseSet_whitneySum (A D : FiniteRankAtlas 𝕜 X) (z : X) :
    (whitneySum A D).chartBaseSet z = A.chartBaseSet z ∩ D.chartBaseSet z := by
  rw [chartBaseSet_def]
  ext x
  constructor
  · rintro ⟨⟨y, _⟩, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, by simp [A.rank_eq_of_mem_chartBaseSet hx.1,
      D.rank_eq_of_mem_chartBaseSet hx.2]⟩, hx, rfl⟩

/-- The continuous linear equivalence splitting each coordinate fibre of `whitneySum A D` into the
product of the fibres of `A` and `D`. -/
def whitneySumFiberEquiv (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneySum A D).Fiber x ≃L[𝕜] (A.Fiber ×ᵇ D.Fiber) x :=
  splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)

@[simp] theorem whitneySumFiberEquiv_apply (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    whitneySumFiberEquiv A D x v = splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v := (rfl)

@[simp] theorem whitneySumFiberEquiv_symm_apply (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (w : (A.Fiber ×ᵇ D.Fiber) x) :
    (whitneySumFiberEquiv A D x).symm w =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm w := (rfl)

private theorem continuous_whitneyStratum_iff {Z : Type*} [TopologicalSpace Z]
    {A D : FiniteRankAtlas 𝕜 X} {a d : ℕ} {b : Z → X}
    (hA : ∀ z, A.rank (b z) = a) (hD : ∀ z, D.rank (b z) = d)
    (u' : Z → Fin a → 𝕜) (w' : Z → Fin d → 𝕜) :
    Continuous (fun z =>
      (⟨⟨b z, by simp [hA z, hD z]⟩,
        (splitCoords (𝕜 := 𝕜) a d).symm (u' z, w' z)⟩ :
          ((whitneySum A D).charts (a + d)).TotalSpace)) ↔
      Continuous (fun z => (⟨⟨b z, hA z⟩, u' z⟩ : (A.charts a).TotalSpace)) ∧
        Continuous (fun z => (⟨⟨b z, hD z⟩, w' z⟩ : (D.charts d).TotalSpace)) := by
  by_cases hb : Continuous b
  · have hAD : ∀ z, (whitneySum A D).rank (b z) = a + d := fun z => by simp [hA z, hD z]
    have htriv (z₀ z : Z) :
        (trivializationAt (Fin (a + d) → 𝕜) ((whitneySum A D).charts (a + d)).Fiber
          ⟨b z₀, hAD z₀⟩ ⟨⟨b z, hAD z⟩, (splitCoords (𝕜 := 𝕜) a d).symm (u' z, w' z)⟩).2 =
          (splitCoords (𝕜 := 𝕜) a d).symm
            ((trivializationAt (Fin a → 𝕜) (A.charts a).Fiber ⟨b z₀, hA z₀⟩ ⟨⟨b z, hA z⟩, u' z⟩).2,
             (trivializationAt (Fin d → 𝕜) (D.charts d).Fiber
               ⟨b z₀, hD z₀⟩ ⟨⟨b z, hD z⟩, w' z⟩).2) := by
      rw [((whitneySum A D).charts (a + d)).trivializationAt, (A.charts a).trivializationAt,
        (D.charts d).trivializationAt, ← VectorBundleCore.localTrivAt_def,
        ← VectorBundleCore.localTrivAt_def, ← VectorBundleCore.localTrivAt_def,
        (whitneySum A D).indexAt_eq, A.indexAt_eq, D.indexAt_eq]
      simp only [VectorBundleCore.localTriv_apply, (whitneySum A D).indexAt_eq, A.indexAt_eq,
        D.indexAt_eq]
      have hcoord := whitneyCharts_coordChange_splitCoords_symm A D rfl ⟨b z, hAD z⟩ ⟨b z₀, hAD z₀⟩
        ⟨b z, hAD z⟩ ⟨hA z, hD z⟩ ⟨hA z₀, hD z₀⟩ ⟨hA z, hD z⟩ (u' z) (w' z)
      simp only [Fin.cast_refl, Function.comp_id] at hcoord
      exact hcoord
    simp only [continuous_iff_continuousAt, FiberBundle.continuousAt_totalSpace]
    refine ⟨fun h => ⟨fun z₀ => ⟨(hb.subtype_mk hA).continuousAt, ?_⟩,
        fun z₀ => ⟨(hb.subtype_mk hD).continuousAt, ?_⟩⟩, fun ⟨hcA, hcD⟩ z₀ =>
        ⟨(hb.subtype_mk hAD).continuousAt, ?_⟩⟩
    · have hW := ((splitCoords (𝕜 := 𝕜) a d).continuous.continuousAt.comp (h z₀).2).fst
      refine hW.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
      dsimp only [Function.comp_apply]
      rw [htriv z₀ z, ContinuousLinearEquiv.apply_symm_apply]
    · have hW := ((splitCoords (𝕜 := 𝕜) a d).continuous.continuousAt.comp (h z₀).2).snd
      refine hW.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
      dsimp only [Function.comp_apply]
      rw [htriv z₀ z, ContinuousLinearEquiv.apply_symm_apply]
    · have hAD' := (splitCoords (𝕜 := 𝕜) a d).symm.continuous.continuousAt.comp
        ((hcA z₀).2.prodMk (hcD z₀).2)
      refine hAD'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
      dsimp only [Function.comp_apply]
      exact htriv z₀ z
  · exact ⟨fun h => absurd (continuous_subtype_val.comp
        ((FiberBundle.continuous_proj _ _).comp h)) hb,
      fun h => absurd (continuous_subtype_val.comp
        ((FiberBundle.continuous_proj _ _).comp h.1)) hb⟩

/-- Assembling a pair of fibre vectors into `TotalSpace Unit (whitneySum A D).Fiber` over `b` is
continuous if and only if both component maps into `TotalSpace Unit A.Fiber` and
`TotalSpace Unit D.Fiber` are continuous. -/
theorem continuous_mk_whitneySum_iff {Y : Type*} [TopologicalSpace Y] {A D : FiniteRankAtlas 𝕜 X}
    {b : Y → X} (u : ∀ y, A.Fiber (b y)) (w : ∀ y, D.Fiber (b y)) :
    Continuous (fun y =>
      (⟨b y, (whitneySumFiberEquiv A D (b y)).symm (u y, w y)⟩ :
        TotalSpace Unit (whitneySum A D).Fiber)) ↔
      Continuous (fun y => (⟨b y, u y⟩ : TotalSpace Unit A.Fiber)) ∧
        Continuous (fun y => (⟨b y, w y⟩ : TotalSpace Unit D.Fiber)) := by
  have hb_iff : (Continuous fun y =>
        (⟨b y, (whitneySumFiberEquiv A D (b y)).symm (u y, w y)⟩ :
          TotalSpace Unit (whitneySum A D).Fiber)) → Continuous b :=
    fun h => (whitneySum A D).continuous_proj.comp h
  by_cases hb : Continuous b
  · have hlcA : IsLocallyConstant fun y => A.rank (b y) :=
      A.rank.isLocallyConstant.comp_continuous hb
    have hlcD : IsLocallyConstant fun y => D.rank (b y) :=
      D.rank.isLocallyConstant.comp_continuous hb
    rw [hlcA.continuous_iff₂ hlcD, hlcA.continuous_iff₂ hlcD, hlcA.continuous_iff₂ hlcD]
    simp only [← forall_and]
    refine forall₂_congr fun a d => ?_
    let u' : {y : Y // A.rank (b y) = a ∧ D.rank (b y) = d} → Fin a → 𝕜 :=
      fun z i => u z.1 (Fin.cast z.2.1.symm i)
    let w' : {y : Y // A.rank (b y) = a ∧ D.rank (b y) = d} → Fin d → 𝕜 :=
      fun z i => w z.1 (Fin.cast z.2.2.symm i)
    have hA_eq : (fun z : {y : Y // A.rank (b y) = a ∧ D.rank (b y) = d} =>
        (⟨b z.1, u z.1⟩ : TotalSpace Unit A.Fiber)) =
        fun z => A.totalSpaceHomeomorph
          ⟨a, (⟨⟨b z.1, z.2.1⟩, u' z⟩ : (A.charts a).TotalSpace)⟩ := by
      funext ⟨y, hAy, hDy⟩; cases hAy
      simp only [totalSpaceHomeomorph_apply, Fin.cast_refl, id_eq, u']
    have hD_eq : (fun z : {y : Y // A.rank (b y) = a ∧ D.rank (b y) = d} =>
        (⟨b z.1, w z.1⟩ : TotalSpace Unit D.Fiber)) =
        fun z => D.totalSpaceHomeomorph
          ⟨d, (⟨⟨b z.1, z.2.2⟩, w' z⟩ : (D.charts d).TotalSpace)⟩ := by
      funext ⟨y, hAy, hDy⟩; cases hDy
      simp only [totalSpaceHomeomorph_apply, Fin.cast_refl, id_eq, w']
    have hW_eq : (fun z : {y : Y // A.rank (b y) = a ∧ D.rank (b y) = d} =>
        (⟨b z.1, (whitneySumFiberEquiv A D (b z.1)).symm (u z.1, w z.1)⟩ :
          TotalSpace Unit (whitneySum A D).Fiber)) =
        fun z => (whitneySum A D).totalSpaceHomeomorph
          ⟨a + d, (⟨⟨b z.1, by simp [z.2.1, z.2.2]⟩,
            (splitCoords (𝕜 := 𝕜) (M := 𝕜) a d).symm (u' z, w' z)⟩ :
              ((whitneySum A D).charts (a + d)).TotalSpace)⟩ := by
      funext ⟨y, hAy, hDy⟩; cases hAy; cases hDy
      rw [totalSpaceHomeomorph_apply]
      refine congrArg (TotalSpace.mk' Unit (b y)) (funext fun i => ?_)
      rw [whitneySumFiberEquiv_symm_apply]
      dsimp only [Function.comp_apply, u', w']
      simp only [Fin.cast_refl, id_eq]
      exact congrArg
        ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank (b y)) (D.rank (b y))).symm (u y, w y))
        (Fin.ext rfl)
    rw [hW_eq, hA_eq, hD_eq]
    exact (((whitneySum A D).isOpenEmbedding_stratum (a + d)).isInducing.continuous_iff.symm.trans
      (continuous_whitneyStratum_iff (fun z => z.2.1) (fun z => z.2.2) u' w')).trans
      (and_congr (A.isOpenEmbedding_stratum a).isInducing.continuous_iff
        (D.isOpenEmbedding_stratum d).isInducing.continuous_iff)
  · exact ⟨fun h => absurd (hb_iff h) hb, fun h => absurd (A.continuous_proj.comp h.1) hb⟩

/-- The reconstructed total space of `whitneySum A D` is homeomorphic to Mathlib's native
direct-sum bundle `A.Fiber ×ᵇ D.Fiber`, over the identity of `X` and by `whitneySumFiberEquiv`
on each fibre. -/
def whitneySumTotalSpaceHomeomorph (A D : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit (whitneySum A D).Fiber ≃ₜ
      TotalSpace (Unit × Unit) (A.Fiber ×ᵇ D.Fiber) where
  toFun p := ⟨p.proj, whitneySumFiberEquiv A D p.proj p.2⟩
  invFun p := ⟨p.proj, (whitneySumFiberEquiv A D p.proj).symm p.2⟩
  left_inv p := by
    rcases p with ⟨x, v⟩
    exact congrArg (TotalSpace.mk' Unit x) ((whitneySumFiberEquiv A D x).symm_apply_apply v)
  right_inv p := by
    rcases p with ⟨x, w⟩
    exact congrArg (TotalSpace.mk' (Unit × Unit) x)
      ((whitneySumFiberEquiv A D x).apply_symm_apply w)
  continuous_toFun := by
    rw [(FiberBundle.Prod.isInducing_diag Unit A.Fiber Unit D.Fiber).continuous_iff]
    have h := (continuous_mk_whitneySum_iff (A := A) (D := D) (b := TotalSpace.proj)
      (fun p : TotalSpace Unit (whitneySum A D).Fiber =>
        (whitneySumFiberEquiv A D p.proj p.2).1)
      (fun p => (whitneySumFiberEquiv A D p.proj p.2).2)).1
      (continuous_id.congr fun ⟨x, v⟩ =>
        (congrArg (TotalSpace.mk' Unit x) ((whitneySumFiberEquiv A D x).symm_apply_apply v)).symm)
    exact h.1.prodMk h.2
  continuous_invFun := by
    have hdiag := (FiberBundle.Prod.isInducing_diag Unit A.Fiber Unit D.Fiber).continuous
    exact (continuous_mk_whitneySum_iff (A := A) (D := D) (b := TotalSpace.proj)
      (fun p : TotalSpace (Unit × Unit) (A.Fiber ×ᵇ D.Fiber) => p.2.1)
      (fun p => p.2.2)).2 ⟨hdiag.fst, hdiag.snd⟩

@[simp] theorem whitneySumTotalSpaceHomeomorph_apply (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    whitneySumTotalSpaceHomeomorph A D p = ⟨p.proj, whitneySumFiberEquiv A D p.proj p.2⟩ := (rfl)

@[simp] theorem whitneySumTotalSpaceHomeomorph_symm_apply (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace (Unit × Unit) (A.Fiber ×ᵇ D.Fiber)) :
    (whitneySumTotalSpaceHomeomorph A D).symm p =
      ⟨p.proj, (whitneySumFiberEquiv A D p.proj).symm p.2⟩ := (rfl)

/-- A map into `TotalSpace Unit (whitneySum A D).Fiber` is continuous if and only if its two
coordinate-block projections into `TotalSpace Unit A.Fiber` and `TotalSpace Unit D.Fiber` are
continuous. -/
theorem continuous_whitneySum_iff {Y : Type*} [TopologicalSpace Y] {A D : FiniteRankAtlas 𝕜 X}
    {f : Y → TotalSpace Unit (whitneySum A D).Fiber} :
    Continuous f ↔
      Continuous (fun y => (⟨(f y).proj, (whitneySumFiberEquiv A D (f y).proj (f y).2).1⟩ :
        TotalSpace Unit A.Fiber)) ∧
      Continuous (fun y => (⟨(f y).proj, (whitneySumFiberEquiv A D (f y).proj (f y).2).2⟩ :
        TotalSpace Unit D.Fiber)) := by
  rw [← (whitneySumTotalSpaceHomeomorph A D).comp_continuous_iff,
    (FiberBundle.Prod.isInducing_diag Unit A.Fiber Unit D.Fiber).continuous_iff]
  exact continuous_prodMk

end TauCeti.FiniteRankAtlas
