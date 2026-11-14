/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Basic
public import TauCeti.Topology.Algebra.Module.Equiv.Fin
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.LocallyConstant.Algebra

import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Trivial atlases, zero object, and Whitney sums of variable-rank bundle atlases

`TauCeti.FiniteRankAtlas.trivial 𝕜 r` constructs the variable-rank trivial atlas with locally
constant fibre dimension `r : LocallyConstant X ℕ`, using `TauCeti.FiniteRankBundleCore.trivial`
on each clopen rank stratum. A map into its reconstructed total space is continuous precisely when
its base projection is continuous and its coordinate vectors are continuous on each rank stratum
(`continuous_trivial_iff`); for constant rank `LocallyConstant.const X n`, the reconstructed total
space is homeomorphic to `X × (Fin n → 𝕜)` (`trivialConstHomeomorph`).

An object of `FiniteRankAtlas 𝕜 X` is a categorical zero object if and only if its locally
constant rank vanishes identically (`isZero_iff_rank_eq_zero`). In particular,
`trivial 𝕜 (0 : LocallyConstant X ℕ)` supplies `HasZeroObject (FiniteRankAtlas 𝕜 X)`, and over an
empty base every atlas is a zero object (`isZero_of_isEmpty`).

`TauCeti.FiniteRankAtlas.whitneySum A D` forms the Whitney sum of two variable-rank atlases, with
rank `A.rank + D.rank : LocallyConstant X ℕ`. Because a single total-rank stratum
`{x : X | A.rank x + D.rank x = n}` may decompose into clopen pieces with distinct summand-rank
pairs `(A.rank x, D.rank x)`, each chart centred at `i` is supported on the clopen-intersected
domain where both summands lie in their preferred charts at `i` (`chartBaseSet_whitneySum`), with
block-diagonal coordinate changes conjugated along `TauCeti.splitCoords`.

`whitneySumTotalSpaceHomeomorph` identifies `TotalSpace Unit (whitneySum A D).Fiber` with
Mathlib's native direct-sum bundle `TotalSpace (Unit × Unit) (A.Fiber ×ᵇ D.Fiber)`, over the
identity of `X` and by `whitneySumFiberEquiv` (`TauCeti.splitCoords`) on every fibre. This gives
the two-projection continuity criterion `continuous_whitneySum_iff`, from which the canonical
projections and inclusions (`whitneyFst`, `whitneySnd`, `whitneyInl`, `whitneyInr`), the binary
bicone (`whitneyBicone`, `whitneyBiconeIsBilimit`), and `HasBinaryBiproducts (FiniteRankAtlas 𝕜 X)`
follow, together with concrete pairing (`whitneyLift`), copairing (`whitneyDesc`), functorial
direct sums (`whitneyMap`, `whitneyMapIso`), symmetry, associativity, and unit coherence
isomorphisms (`whitneyCommIso`, `whitneyAssocIso`, `whitneyZeroLeftIso`, `whitneyZeroRightIso`),
and the trivial-atlas sum isomorphism `trivialAddIso`. No compactness, separation, nonemptiness,
bounded-rank, or scalar-completeness hypothesis is required.

The universal-property, coherence, and `Bundle.Prod` comparison API parallels the constant-rank
development for `TauCeti.FiniteRankBundleCore` in
`TauCeti.Topology.VectorBundle.FiniteRank.Biproduct`, lifting coordinate splitting along
`TauCeti.splitCoords`, Mathlib's `FiberBundle.Prod` topology, and
`CategoryTheory.Limits.isBinaryBilimitOfTotal` to variable-rank atlases.

## References

* M. F. Atiyah, *K-Theory*, §1.1–1.2.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, §3.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits ZeroObject Set Topology

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

section ChartBaseSet

/-- The open domain in `X` of the preferred chart of `A` centred at `z`, lying inside the clopen
stratum `{x : X | A.rank x = A.rank z}`. -/
def chartBaseSet (A : FiniteRankAtlas 𝕜 X) (z : X) : Set X :=
  Subtype.val '' (A.charts (A.rank z)).baseSet ⟨z, rfl⟩

/-- Membership in `A.chartBaseSet z` means matching rank with `z` and membership in the stratum
chart at `z`. -/
theorem mem_chartBaseSet_iff {A : FiniteRankAtlas 𝕜 X} {z x : X} :
    x ∈ A.chartBaseSet z ↔
      ∃ hx : A.rank x = A.rank z, ⟨x, hx⟩ ∈ (A.charts (A.rank z)).baseSet ⟨z, rfl⟩ := by
  constructor
  · rintro ⟨⟨y, hy⟩, hmem, rfl⟩
    exact ⟨hy, hmem⟩
  · rintro ⟨hx, hmem⟩
    exact ⟨⟨x, hx⟩, hmem, rfl⟩

/-- Every point in the preferred chart centred at `z` has the same rank as `z`. -/
theorem rank_eq_of_mem_chartBaseSet {A : FiniteRankAtlas 𝕜 X} {z x : X}
    (hx : x ∈ A.chartBaseSet z) : A.rank x = A.rank z :=
  (mem_chartBaseSet_iff.1 hx).1

/-- Each preferred chart domain `A.chartBaseSet z` is open in the base `X`. -/
theorem isOpen_chartBaseSet (A : FiniteRankAtlas 𝕜 X) (z : X) : IsOpen (A.chartBaseSet z) :=
  (A.rank.isLocallyConstant.isOpen_fiber (A.rank z)).isOpenEmbedding_subtypeVal.isOpenMap _
    ((A.charts (A.rank z)).isOpen_baseSet ⟨z, rfl⟩)

/-- Every base point belongs to the domain of its own preferred chart. -/
theorem self_mem_chartBaseSet (A : FiniteRankAtlas 𝕜 X) (z : X) : z ∈ A.chartBaseSet z :=
  mem_chartBaseSet_iff.2
    ⟨rfl, by simpa only [A.indexAt_eq] using (A.charts (A.rank z)).mem_baseSet_at ⟨z, rfl⟩⟩

private theorem mem_charts_baseSet_of_mem_chartBaseSet {A : FiniteRankAtlas 𝕜 X} {z x : X}
    (hx : x ∈ A.chartBaseSet z) {m : ℕ} (hm : A.rank z = m) :
    ⟨x, (A.rank_eq_of_mem_chartBaseSet hx).trans hm⟩ ∈ (A.charts m).baseSet ⟨z, hm⟩ := by
  subst hm
  exact (mem_chartBaseSet_iff.1 hx).2

end ChartBaseSet

section TrivialAndZero

variable (𝕜) in
/-- The variable-rank trivial atlas with locally constant fibre dimension `r`. -/
-- Expose the rank projection so `(trivial 𝕜 r).Fiber x` reduces to `Fin (r x) → 𝕜`.
@[expose] def trivial (r : LocallyConstant X ℕ) : FiniteRankAtlas 𝕜 X where
  rank := r
  charts n := (FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n).core
  indexAt_eq n := (FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n).indexAt_eq

@[simp] theorem rank_trivial (r : LocallyConstant X ℕ) : (trivial 𝕜 r).rank = r := (rfl)

@[simp] theorem charts_trivial (r : LocallyConstant X ℕ) (n : ℕ) :
    (trivial 𝕜 r).charts n = (FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n).core := (rfl)

@[simp] theorem localTriv_baseSet_trivial (r : LocallyConstant X ℕ) (n : ℕ)
    (x : {x : X // r x = n}) :
    (((trivial 𝕜 r).charts n).localTriv x).baseSet = Set.univ := (rfl)

theorem coordChange_trivial (r : LocallyConstant X ℕ) (n : ℕ)
    (i j x : {x : X // r x = n}) :
    ((trivial 𝕜 r).charts n).coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin n → 𝕜) := (rfl)

/-- The preferred chart domain at `z` of a trivial variable-rank atlas is the entire rank fiber of
`z`. -/
@[simp] theorem chartBaseSet_trivial (r : LocallyConstant X ℕ) (z : X) :
    (trivial 𝕜 r).chartBaseSet z = {x : X | r x = r z} := by
  ext x
  simp [mem_chartBaseSet_iff, trivial]

/-- A map into the reconstructed total space of `trivial 𝕜 r` is continuous if and only if its
base projection is continuous and its coordinate vectors are continuous on each rank stratum. -/
theorem continuous_trivial_iff {Y : Type*} [TopologicalSpace Y] {r : LocallyConstant X ℕ}
    {f : Y → TotalSpace Unit (trivial 𝕜 r).Fiber} :
    Continuous f ↔
      Continuous (fun y => (f y).proj) ∧
        ∀ n : ℕ, Continuous (fun y : {y : Y // r (f y).proj = n} =>
          (fun i => (f y.1).2 (Fin.cast y.2.symm i) : Fin n → 𝕜)) := by
  constructor
  · intro hf
    have hb : Continuous fun y => (f y).proj := (trivial 𝕜 r).continuous_proj.comp hf
    refine ⟨hb, fun n => ?_⟩
    have hn := ((trivial 𝕜 r).continuous_mk_iff_rankStrata hb (fun y => (f y).2)).1 hf n
    exact (FiniteRankBundleCore.continuous_trivial_iff.1 hn).2
  · rintro ⟨hb, hs⟩
    exact ((trivial 𝕜 r).continuous_mk_iff_rankStrata hb (fun y => (f y).2)).2 fun n =>
      FiniteRankBundleCore.continuous_trivial_iff.2
        ⟨(hb.comp continuous_subtype_val).subtype_mk _, hs n⟩

/-- Assembling a map into `TotalSpace Unit (trivial 𝕜 r).Fiber` whose base points all have rank `n`
is continuous if and only if both the base map and the `Fin n → 𝕜` coordinate map are continuous. -/
theorem continuous_mk_trivial_of_rank_eq_iff {Y : Type*} [TopologicalSpace Y]
    {r : LocallyConstant X ℕ} {n : ℕ} {b : Y → X} {v : Y → Fin n → 𝕜}
    (hr : ∀ y, r (b y) = n) :
    Continuous (fun y =>
      (⟨b y, fun i => v y (Fin.cast (hr y) i)⟩ : TotalSpace Unit (trivial 𝕜 r).Fiber)) ↔
      Continuous b ∧ Continuous v := by
  rw [continuous_trivial_iff]
  refine and_congr_right fun _ => ⟨fun hs => ?_, fun hv m => ?_⟩
  · exact ((hs n).comp (continuous_id.subtype_mk hr)).congr fun y =>
      funext fun _ => congrArg (v y) (Fin.ext rfl)
  · by_cases hnm : n = m
    · subst hnm
      exact (hv.comp continuous_subtype_val).congr fun y =>
        funext fun _ => congrArg (v y.1) (Fin.ext rfl)
    · exact continuous_iff_continuousAt.2 fun y => False.elim (hnm ((hr y.1).symm.trans y.2))

/-- A map into the reconstructed total space of a constant-rank trivial atlas is continuous if and
only if both its base point and its coordinate vector in `Fin n → 𝕜` are continuous. -/
theorem continuous_trivial_const_iff {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    {f : Y → TotalSpace Unit (trivial 𝕜 (.const X n)).Fiber} :
    Continuous f ↔
      Continuous (fun y => (f y).proj) ∧
        Continuous (fun y (i : Fin n) =>
          (f y).2 (Fin.cast (congrFun (LocallyConstant.coe_const n) (f y).proj).symm i)) := by
  have hf : f = fun y => ⟨(f y).proj, fun i =>
      (fun y (j : Fin n) => (f y).2
        (Fin.cast (congrFun (LocallyConstant.coe_const n) (f y).proj).symm j)) y
        (Fin.cast (congrFun (LocallyConstant.coe_const n) (f y).proj) i)⟩ :=
    funext fun y =>
      congrArg (TotalSpace.mk' Unit (f y).proj) (funext fun _ => congrArg (f y).2 (Fin.ext rfl))
  exact (congrArg Continuous hf).to_iff.trans
    (continuous_mk_trivial_of_rank_eq_iff (b := fun y => (f y).proj)
      (v := fun y (i : Fin n) =>
        (f y).2 (Fin.cast (congrFun (LocallyConstant.coe_const n) (f y).proj).symm i))
      fun y => congrFun (LocallyConstant.coe_const n) (f y).proj)

/-- For constant rank `n`, the reconstructed total space of `trivial 𝕜 (.const X n)` is
homeomorphic to `X × (Fin n → 𝕜)`. -/
def trivialConstHomeomorph (n : ℕ) :
    TotalSpace Unit (trivial 𝕜 (.const X n)).Fiber ≃ₜ X × (Fin n → 𝕜) where
  toFun p :=
    (p.proj, fun (i : Fin n) =>
      p.2 (Fin.cast (congrFun (LocallyConstant.coe_const n) p.proj).symm i))
  invFun q := ⟨q.1, fun i => q.2 (Fin.cast (congrFun (LocallyConstant.coe_const n) q.1) i)⟩
  left_inv p := by
    rcases p with ⟨x, v⟩
    exact congrArg (TotalSpace.mk' Unit x) (funext fun _ => congrArg v (Fin.ext rfl))
  right_inv q := by
    rcases q with ⟨x, v⟩
    exact Prod.ext rfl (funext fun _ => congrArg v (Fin.ext rfl))
  continuous_toFun :=
    (continuous_trivial_const_iff.1 continuous_id).1.prodMk
      (continuous_trivial_const_iff.1 continuous_id).2
  continuous_invFun :=
    continuous_trivial_const_iff.2
      ⟨continuous_fst, continuous_snd.congr fun q => funext fun _ => congrArg q.2 (Fin.ext rfl)⟩

@[simp] theorem trivialConstHomeomorph_apply (n : ℕ)
    (p : TotalSpace Unit (trivial 𝕜 (.const X n)).Fiber) :
    trivialConstHomeomorph (𝕜 := 𝕜) n p =
      (p.proj, fun (i : Fin n) =>
        p.2 (Fin.cast (congrFun (LocallyConstant.coe_const n) p.proj).symm i)) := (rfl)

@[simp] theorem trivialConstHomeomorph_symm_apply (n : ℕ) (q : X × (Fin n → 𝕜)) :
    (trivialConstHomeomorph (𝕜 := 𝕜) (X := X) n).symm q =
      ⟨q.1, fun i => q.2 (Fin.cast (congrFun (LocallyConstant.coe_const n) q.1) i)⟩ := (rfl)

/-- Any atlas whose locally constant rank is identically zero is a zero object. -/
theorem isZero_of_rank_eq_zero {A : FiniteRankAtlas 𝕜 X} (h : A.rank = 0) : IsZero A where
  unique_to D := ⟨⟨⟨0⟩, fun f => hom_ext fun x => LinearMap.ext fun v => by
    have hx : A.rank x = 0 := DFunLike.congr_fun h x
    have : Subsingleton (A.Fiber x) := by unfold Fiber; rw [hx]; infer_instance
    simp [Subsingleton.elim v 0]⟩⟩
  unique_from D := ⟨⟨⟨0⟩, fun f => hom_ext fun x => LinearMap.ext fun v =>
    funext fun i => (Fin.cast (DFunLike.congr_fun h x) i).elim0⟩⟩

/-- Every zero object in `FiniteRankAtlas 𝕜 X` has identically zero locally constant rank. -/
theorem rank_eq_zero_of_isZero {A : FiniteRankAtlas 𝕜 X} (hA : IsZero A) : A.rank = 0 := by
  ext x
  by_contra hx
  have hid : (𝟙 A : A ⟶ A) = 0 := hA.eq_of_src _ _
  have hval := congrFun (LinearMap.congr_fun (congrArg (fun f => f.fiberMap x) hid)
    (fun _ => (1 : 𝕜))) ⟨0, Nat.pos_of_ne_zero hx⟩
  exact one_ne_zero hval

/-- An atlas in `FiniteRankAtlas 𝕜 X` is a categorical zero object if and only if its locally
constant rank is `0`. -/
theorem isZero_iff_rank_eq_zero (A : FiniteRankAtlas 𝕜 X) : IsZero A ↔ A.rank = 0 :=
  ⟨rank_eq_zero_of_isZero, isZero_of_rank_eq_zero⟩

/-- The trivial rank-zero atlas is a zero object. -/
theorem isZero_trivial_zero : IsZero (trivial 𝕜 (0 : LocallyConstant X ℕ)) :=
  isZero_of_rank_eq_zero (rank_trivial 0)

/-- `trivial 𝕜 (0 : LocallyConstant X ℕ)` provides a zero object for `FiniteRankAtlas 𝕜 X`. -/
instance : HasZeroObject (FiniteRankAtlas 𝕜 X) :=
  ⟨⟨trivial 𝕜 (0 : LocallyConstant X ℕ), isZero_trivial_zero⟩⟩

/-- The categorical zero object of `FiniteRankAtlas 𝕜 X` has rank `0`. -/
@[simp] theorem rank_zero : (0 : FiniteRankAtlas 𝕜 X).rank = 0 :=
  rank_eq_zero_of_isZero (Limits.isZero_zero _)

/-- Over an empty base space, every variable-rank atlas is a zero object. -/
theorem isZero_of_isEmpty [IsEmpty X] (A : FiniteRankAtlas 𝕜 X) : IsZero A :=
  isZero_of_rank_eq_zero (LocallyConstant.ext isEmptyElim)

end TrivialAndZero

section WhitneySum

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
      (mem_charts_baseSet_of_mem_chartBaseSet hx.1 rfl),
    (D.charts (D.rank i.1)).coordChange_self ⟨i.1, rfl⟩ ⟨x.1, hxi.2⟩
      (mem_charts_baseSet_of_mem_chartBaseSet hx.2 rfl),
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
        mem_charts_baseSet_of_mem_chartBaseSet x.2.1.1 hij.1,
        mem_charts_baseSet_of_mem_chartBaseSet x.2.2.1 rfl⟩
    let φD : S → ↑((D.charts (D.rank j.1)).baseSet ⟨i.1, hij.2⟩ ∩
        (D.charts (D.rank j.1)).baseSet ⟨j.1, rfl⟩) := fun x =>
      ⟨⟨x.1.1, D.rank_eq_of_mem_chartBaseSet x.2.2.2⟩,
        mem_charts_baseSet_of_mem_chartBaseSet x.2.1.2 hij.2,
        mem_charts_baseSet_of_mem_chartBaseSet x.2.2.2 rfl⟩
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
      ⟨⟨mem_charts_baseSet_of_mem_chartBaseSet hx.1.1.1 hi.1,
        mem_charts_baseSet_of_mem_chartBaseSet hx.1.2.1 hj.1⟩,
        mem_charts_baseSet_of_mem_chartBaseSet hx.2.1 rfl⟩,
    (D.charts (D.rank k.1)).coordChange_comp ⟨i.1, hi.2⟩ ⟨j.1, hj.2⟩ ⟨k.1, rfl⟩ ⟨x.1, hxD_k⟩
      ⟨⟨mem_charts_baseSet_of_mem_chartBaseSet hx.1.1.2 hi.2,
        mem_charts_baseSet_of_mem_chartBaseSet hx.1.2.2 hj.2⟩,
        mem_charts_baseSet_of_mem_chartBaseSet hx.2.2 rfl⟩]

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
  mem_baseSet_at x := ⟨A.self_mem_chartBaseSet x.1, D.self_mem_chartBaseSet x.1⟩
  coordChange := whitneyCoordChange A D n
  coordChange_self := whitneyCoordChange_self A D n
  continuousOn_coordChange := continuousOn_whitneyCoordChange A D n
  coordChange_comp := whitneyCoordChange_comp A D n

theorem whitneyCharts_baseSet (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (i : {x : X // (A.rank + D.rank) x = n}) :
    (whitneyCharts A D n).baseSet i =
      Subtype.val ⁻¹' (A.chartBaseSet i.1 ∩ D.chartBaseSet i.1) := (rfl)

@[simp] theorem whitneyCharts_localTriv_baseSet (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (i : {x : X // (A.rank + D.rank) x = n}) :
    ((whitneyCharts A D n).localTriv i).baseSet =
      Subtype.val ⁻¹' (A.chartBaseSet i.1 ∩ D.chartBaseSet i.1) := (rfl)

@[simp] theorem whitneyCharts_indexAt (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (x : {x : X // (A.rank + D.rank) x = n}) :
    (whitneyCharts A D n).indexAt x = x := (rfl)

/-- On any summand-rank decomposition `a + d`, the coordinate transition of `whitneyCharts`
applies the two summand coordinate transitions blockwise along `splitCoords`. -/
theorem whitneyCharts_coordChange_splitCoords_symm (A D : FiniteRankAtlas 𝕜 X) {a d : ℕ}
    (i j x : {x : X // (A.rank + D.rank) x = a + d})
    (hi : A.rank i.1 = a ∧ D.rank i.1 = d)
    (hj : A.rank j.1 = a ∧ D.rank j.1 = d)
    (hx : A.rank x.1 = a ∧ D.rank x.1 = d)
    (u : Fin a → 𝕜) (w : Fin d → 𝕜) :
    (whitneyCharts A D (a + d)).coordChange i j x ((splitCoords (𝕜 := 𝕜) a d).symm (u, w)) =
      (splitCoords (𝕜 := 𝕜) a d).symm
        ((A.charts a).coordChange ⟨i.1, hi.1⟩ ⟨j.1, hj.1⟩ ⟨x.1, hx.1⟩ u,
         (D.charts d).coordChange ⟨i.1, hi.2⟩ ⟨j.1, hj.2⟩ ⟨x.1, hx.2⟩ w) := by
  unfold whitneyCharts
  dsimp only
  rw [whitneyCoordChange_eq_blockCoordChange A D rfl i j x hi hj hx]
  have he : ((ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin (a + d) => 𝕜)
      (finCongr (rfl : a + d = a + d))).symm.trans (splitCoords (𝕜 := 𝕜) (M := 𝕜) a d)) =
      splitCoords (𝕜 := 𝕜) (M := 𝕜) a d := DFunLike.ext _ _ fun _ => rfl
  simp only [blockCoordChange, he, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply']

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

private theorem continuous_pairStrata_iff {Y T : Type*} [TopologicalSpace Y] [TopologicalSpace T]
    {A D : FiniteRankAtlas 𝕜 X} {b : Y → X} (hb : Continuous b) {g : Y → T} :
    Continuous g ↔
      ∀ a d : ℕ, Continuous (fun y : {y : Y // A.rank (b y) = a ∧ D.rank (b y) = d} => g y.1) := by
  refine ⟨fun hg _ _ => hg.comp continuous_subtype_val, fun hg => ?_⟩
  apply continuous_of_cover_nhds (s := fun p : ℕ × ℕ =>
    {y : Y | A.rank (b y) = p.1 ∧ D.rank (b y) = p.2})
  · intro y
    exact ⟨(A.rank (b y), D.rank (b y)),
      (((A.rank.isLocallyConstant.isOpen_fiber _).inter
        (D.rank.isLocallyConstant.isOpen_fiber _)).preimage hb).mem_nhds ⟨rfl, rfl⟩⟩
  · rintro ⟨a, d⟩
    exact continuousOn_iff_continuous_domRestrict.2 (hg a d)

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
  · have hAD : ∀ z, (A.rank + D.rank) (b z) = a + d := fun z => by simp [hA z, hD z]
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
      simp only [VectorBundleCore.localTriv_apply, A.indexAt_eq, D.indexAt_eq, charts_whitneySum]
      exact whitneyCharts_coordChange_splitCoords_symm A D ⟨b z, hAD z⟩ ⟨b z₀, hAD z₀⟩
        ⟨b z, hAD z⟩ ⟨hA z, hD z⟩ ⟨hA z₀, hD z₀⟩ ⟨hA z, hD z⟩ (u' z) (w' z)
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
  · rw [continuous_pairStrata_iff (A := A) (D := D) hb,
      continuous_pairStrata_iff (A := A) (D := D) hb,
      continuous_pairStrata_iff (A := A) (D := D) hb]
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
      simp only [totalSpaceHomeomorph_apply, whitneySumFiberEquiv_symm_apply, Fin.cast_refl,
        id_eq, u', w']
      rfl
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

/-- Projection of the Whitney sum onto its first summand. -/
def whitneyFst (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ A where
  fiberMap x := ((ContinuousLinearMap.fst 𝕜 (A.Fiber x) (D.Fiber x)).comp
    (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toContinuousLinearMap).toLinearMap
  continuous_totalSpaceMap := (continuous_whitneySum_iff.1 continuous_id).1

/-- Projection of the Whitney sum onto its second summand. -/
def whitneySnd (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ D where
  fiberMap x := ((ContinuousLinearMap.snd 𝕜 (A.Fiber x) (D.Fiber x)).comp
    (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toContinuousLinearMap).toLinearMap
  continuous_totalSpaceMap := (continuous_whitneySum_iff.1 continuous_id).2

/-- Inclusion of the first summand into the Whitney sum. -/
def whitneyInl (A D : FiniteRankAtlas 𝕜 X) : A ⟶ whitneySum A D where
  fiberMap x := ((splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl 𝕜 (A.Fiber x) (D.Fiber x))).toLinearMap
  continuous_totalSpaceMap := (continuous_mk_whitneySum_iff (b := TotalSpace.proj)
    (fun p : TotalSpace Unit A.Fiber => p.2) (fun _ => 0)).2
    ⟨continuous_id, D.continuous_zeroSection.comp A.continuous_proj⟩

/-- Inclusion of the second summand into the Whitney sum. -/
def whitneyInr (A D : FiniteRankAtlas 𝕜 X) : D ⟶ whitneySum A D where
  fiberMap x := ((splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr 𝕜 (A.Fiber x) (D.Fiber x))).toLinearMap
  continuous_totalSpaceMap := (continuous_mk_whitneySum_iff (b := TotalSpace.proj)
    (fun _ : TotalSpace Unit D.Fiber => 0) (fun p => p.2)).2
    ⟨A.continuous_zeroSection.comp D.continuous_proj, continuous_id⟩

/-- On each fibre, `whitneyFst` extracts the first coordinate block. -/
@[simp] theorem fiberMap_whitneyFst (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyFst A D).fiberMap x =
      ((ContinuousLinearMap.fst 𝕜 (A.Fiber x) (D.Fiber x)).comp
        (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toContinuousLinearMap).toLinearMap := (rfl)

/-- On each fibre, `whitneySnd` extracts the second coordinate block. -/
@[simp] theorem fiberMap_whitneySnd (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneySnd A D).fiberMap x =
      ((ContinuousLinearMap.snd 𝕜 (A.Fiber x) (D.Fiber x)).comp
        (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toContinuousLinearMap).toLinearMap := (rfl)

/-- On each fibre, `whitneyInl` appends a zero block. -/
@[simp] theorem fiberMap_whitneyInl (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyInl A D).fiberMap x =
      ((splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl 𝕜 (A.Fiber x) (D.Fiber x))).toLinearMap := (rfl)

/-- On each fibre, `whitneyInr` prepends a zero block. -/
@[simp] theorem fiberMap_whitneyInr (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyInr A D).fiberMap x =
      ((splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inr 𝕜 (A.Fiber x) (D.Fiber x))).toLinearMap := (rfl)

theorem fst_whitneySumFiberEquiv (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneySumFiberEquiv A D x v).1 = (whitneyFst A D).fiberMap x v := (rfl)

theorem snd_whitneySumFiberEquiv (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneySumFiberEquiv A D x v).2 = (whitneySnd A D).fiberMap x v := (rfl)

theorem whitneySumFiberEquiv_whitneyInl (A D : FiniteRankAtlas 𝕜 X) (x : X) (u : A.Fiber x) :
    whitneySumFiberEquiv A D x ((whitneyInl A D).fiberMap x u) = (u, 0) :=
  (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (u, 0)

theorem whitneySumFiberEquiv_whitneyInr (A D : FiniteRankAtlas 𝕜 X) (x : X) (w : D.Fiber x) :
    whitneySumFiberEquiv A D x ((whitneyInr A D).fiberMap x w) = (0, w) :=
  (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (0, w)

@[reassoc (attr := simp)] theorem whitneyInl_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneyFst A D = 𝟙 A :=
  hom_ext fun x => LinearMap.ext fun u =>
    congrArg Prod.fst (whitneySumFiberEquiv_whitneyInl A D x u)

@[reassoc (attr := simp)] theorem whitneyInl_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneySnd A D = 0 :=
  hom_ext fun x => LinearMap.ext fun u =>
    congrArg Prod.snd (whitneySumFiberEquiv_whitneyInl A D x u)

@[reassoc (attr := simp)] theorem whitneyInr_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneyFst A D = 0 :=
  hom_ext fun x => LinearMap.ext fun w =>
    congrArg Prod.fst (whitneySumFiberEquiv_whitneyInr A D x w)

@[reassoc (attr := simp)] theorem whitneyInr_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneySnd A D = 𝟙 D :=
  hom_ext fun x => LinearMap.ext fun w =>
    congrArg Prod.snd (whitneySumFiberEquiv_whitneyInr A D x w)

/-- The concrete binary bicone exhibiting `whitneySum A D` with its four canonical bundle maps. -/
-- Expose the point projection so the legs reduce to morphisms on `whitneySum A D`.
@[expose] def whitneyBicone (A D : FiniteRankAtlas 𝕜 X) : BinaryBicone A D where
  pt := whitneySum A D
  fst := whitneyFst A D
  snd := whitneySnd A D
  inl := whitneyInl A D
  inr := whitneyInr A D
  inl_fst := whitneyInl_fst A D
  inl_snd := whitneyInl_snd A D
  inr_fst := whitneyInr_fst A D
  inr_snd := whitneyInr_snd A D

@[simp] theorem whitneyBicone_pt (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).pt = whitneySum A D := (rfl)

@[simp] theorem whitneyBicone_fst (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).fst = whitneyFst A D := (rfl)

@[simp] theorem whitneyBicone_snd (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).snd = whitneySnd A D := (rfl)

@[simp] theorem whitneyBicone_inl (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).inl = whitneyInl A D := (rfl)

@[simp] theorem whitneyBicone_inr (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).inr = whitneyInr A D := (rfl)

/-- The coordinate-block projections and inclusions of `whitneySum A D` resolve the identity. -/
@[simp] theorem whitney_total (A D : FiniteRankAtlas 𝕜 X) :
    whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D =
      𝟙 (whitneySum A D) := by
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro v
  apply (whitneySumFiberEquiv A D x).injective
  simp only [fiberMap_add, fiberMap_comp, fiberMap_id, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_add, whitneySumFiberEquiv_whitneyInl, whitneySumFiberEquiv_whitneyInr,
    ← fst_whitneySumFiberEquiv, ← snd_whitneySumFiberEquiv, Prod.mk_add_mk, add_zero, zero_add,
    Prod.mk.eta]

/-- The Whitney sum bicone is a categorical binary biproduct in `FiniteRankAtlas 𝕜 X`. -/
def whitneyBiconeIsBilimit (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).IsBilimit :=
  isBinaryBilimitOfTotal _ (whitney_total A D)

/-- Whitney sums provide binary biproducts of variable-rank bundle atlases. -/
instance : HasBinaryBiproducts (FiniteRankAtlas 𝕜 X) where
  has_binary_biproduct A D := ⟨⟨whitneyBicone A D, whitneyBiconeIsBilimit A D⟩⟩

/-- The locally constant rank of a categorical binary biproduct is the sum of the summand ranks. -/
@[simp] theorem rank_biprod (A D : FiniteRankAtlas 𝕜 X) :
    (A ⊞ D).rank = A.rank + D.rank :=
  (biprod.uniqueUpToIso A D (whitneyBiconeIsBilimit A D)).symm.finiteRankAtlas_rank_eq

end WhitneySum

section UniversalProperty

variable {A A' A'' D D' D'' C E : FiniteRankAtlas 𝕜 X}

/-- Pair two bundle morphisms with common source into the concrete Whitney sum. -/
def whitneyLift (f : E ⟶ A) (g : E ⟶ D) : E ⟶ whitneySum A D :=
  f ≫ whitneyInl A D + g ≫ whitneyInr A D

theorem whitneyLift_def (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g = f ≫ whitneyInl A D + g ≫ whitneyInr A D := (rfl)

@[reassoc (attr := simp)]
theorem whitneyLift_fst (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g ≫ whitneyFst A D = f := by
  simp [whitneyLift, Preadditive.add_comp]

@[reassoc (attr := simp)]
theorem whitneyLift_snd (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g ≫ whitneySnd A D = g := by
  simp [whitneyLift, Preadditive.add_comp]

/-- Every morphism into a Whitney sum is the pairing of its two projections. -/
theorem eq_whitneyLift (h : E ⟶ whitneySum A D) :
    h = whitneyLift (h ≫ whitneyFst A D) (h ≫ whitneySnd A D) := by
  calc
    h = h ≫ 𝟙 (whitneySum A D) := (Category.comp_id h).symm
    _ = h ≫ (whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D) := by
      rw [whitney_total]
    _ = whitneyLift (h ≫ whitneyFst A D) (h ≫ whitneySnd A D) := by
      simp only [whitneyLift, Preadditive.comp_add, Category.assoc]

/-- Morphisms into a Whitney sum are determined by their compositions with the two projections. -/
theorem whitneySum_hom_ext {h₁ h₂ : E ⟶ whitneySum A D}
    (hfst : h₁ ≫ whitneyFst A D = h₂ ≫ whitneyFst A D)
    (hsnd : h₁ ≫ whitneySnd A D = h₂ ≫ whitneySnd A D) : h₁ = h₂ := by
  rw [eq_whitneyLift h₁, eq_whitneyLift h₂, hfst, hsnd]

@[reassoc]
theorem comp_whitneyLift (h : C ⟶ E) (f : E ⟶ A) (g : E ⟶ D) :
    h ≫ whitneyLift f g = whitneyLift (h ≫ f) (h ≫ g) := by
  simp only [whitneyLift, Preadditive.comp_add, Category.assoc]

@[simp]
theorem whitneyLift_fst_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyLift (whitneyFst A D) (whitneySnd A D) = 𝟙 (whitneySum A D) :=
  whitney_total A D

/-- On each fibre, `whitneyLift f g` pairs `f.fiberMap x` and `g.fiberMap x` via `splitCoords`. -/
@[simp]
theorem fiberMap_whitneyLift (f : E ⟶ A) (g : E ⟶ D) (x : X) :
    (whitneyLift f g).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toLinearEquiv.toLinearMap.comp
        ((f.fiberMap x).prod (g.fiberMap x)) := by
  apply LinearMap.ext
  intro v
  apply (whitneySumFiberEquiv A D x).injective
  have lhs : whitneySumFiberEquiv A D x ((whitneyLift f g).fiberMap x v) =
      (f.fiberMap x v, g.fiberMap x v) := by
    simp only [whitneyLift, fiberMap_add, fiberMap_comp, LinearMap.add_apply, LinearMap.comp_apply,
      map_add, whitneySumFiberEquiv_whitneyInl, whitneySumFiberEquiv_whitneyInr, Prod.mk_add_mk,
      add_zero, zero_add]
  exact lhs.trans
    ((whitneySumFiberEquiv A D x).apply_symm_apply (f.fiberMap x v, g.fiberMap x v)).symm

theorem splitCoords_fiberMap_whitneyLift (f : E ⟶ A) (g : E ⟶ D) (x : X) (v : E.Fiber x) :
    splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) ((whitneyLift f g).fiberMap x v) =
      (f.fiberMap x v, g.fiberMap x v) := by
  rw [fiberMap_whitneyLift]
  exact (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply
    (f.fiberMap x v, g.fiberMap x v)

/-- Copair two bundle morphisms with common target out of the concrete Whitney sum. -/
def whitneyDesc (f : A ⟶ E) (g : D ⟶ E) : whitneySum A D ⟶ E :=
  whitneyFst A D ≫ f + whitneySnd A D ≫ g

theorem whitneyDesc_def (f : A ⟶ E) (g : D ⟶ E) :
    whitneyDesc f g = whitneyFst A D ≫ f + whitneySnd A D ≫ g := (rfl)

@[reassoc (attr := simp)]
theorem whitneyInl_desc (f : A ⟶ E) (g : D ⟶ E) :
    whitneyInl A D ≫ whitneyDesc f g = f := by
  simp [whitneyDesc, Preadditive.comp_add]

@[reassoc (attr := simp)]
theorem whitneyInr_desc (f : A ⟶ E) (g : D ⟶ E) :
    whitneyInr A D ≫ whitneyDesc f g = g := by
  simp [whitneyDesc, Preadditive.comp_add]

@[reassoc (attr := simp)]
theorem whitneyLift_desc (f : E ⟶ A) (g : E ⟶ D) (h : A ⟶ C) (k : D ⟶ C) :
    whitneyLift f g ≫ whitneyDesc h k = f ≫ h + g ≫ k := by
  simp [whitneyLift, whitneyDesc, Preadditive.add_comp, Preadditive.comp_add]

/-- Every morphism out of a Whitney sum is the copairing of its two summand restrictions. -/
theorem eq_whitneyDesc (h : whitneySum A D ⟶ E) :
    h = whitneyDesc (whitneyInl A D ≫ h) (whitneyInr A D ≫ h) := by
  calc
    h = 𝟙 (whitneySum A D) ≫ h := (Category.id_comp h).symm
    _ = (whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D) ≫ h := by
      rw [whitney_total]
    _ = whitneyDesc (whitneyInl A D ≫ h) (whitneyInr A D ≫ h) := by
      simp only [whitneyDesc, Preadditive.add_comp, Category.assoc]

/-- Morphisms out of a Whitney sum are determined by their restrictions to the two summands. -/
theorem whitneySum_hom_ext' {h₁ h₂ : whitneySum A D ⟶ E}
    (hinl : whitneyInl A D ≫ h₁ = whitneyInl A D ≫ h₂)
    (hinr : whitneyInr A D ≫ h₁ = whitneyInr A D ≫ h₂) : h₁ = h₂ := by
  rw [eq_whitneyDesc h₁, eq_whitneyDesc h₂, hinl, hinr]

@[reassoc]
theorem whitneyDesc_comp (f : A ⟶ E) (g : D ⟶ E) (h : E ⟶ C) :
    whitneyDesc f g ≫ h = whitneyDesc (f ≫ h) (g ≫ h) := by
  simp only [whitneyDesc, Preadditive.add_comp, Category.assoc]

@[simp]
theorem whitneyDesc_inl_inr (A D : FiniteRankAtlas 𝕜 X) :
    whitneyDesc (whitneyInl A D) (whitneyInr A D) = 𝟙 (whitneySum A D) :=
  whitney_total A D

/-- On each fibre, `whitneyDesc f g` copairs `f.fiberMap x` and `g.fiberMap x` after
`splitCoords`. -/
@[simp]
theorem fiberMap_whitneyDesc (f : A ⟶ E) (g : D ⟶ E) (x : X) :
    (whitneyDesc f g).fiberMap x =
      ((f.fiberMap x).coprod (g.fiberMap x)).comp
        (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearEquiv.toLinearMap := by
  ext v
  rfl

theorem fiberMap_whitneyDesc_apply (f : A ⟶ E) (g : D ⟶ E) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneyDesc f g).fiberMap x v =
      f.fiberMap x (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).1 +
        g.fiberMap x (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).2 := (rfl)

/-- Direct sum of two bundle morphisms on Whitney sums. -/
def whitneyMap (f : A ⟶ A') (g : D ⟶ D') : whitneySum A D ⟶ whitneySum A' D' :=
  whitneyLift (whitneyFst A D ≫ f) (whitneySnd A D ≫ g)

theorem whitneyMap_def (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g = whitneyLift (whitneyFst A D ≫ f) (whitneySnd A D ≫ g) := (rfl)

@[reassoc (attr := simp)]
theorem whitneyMap_fst (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ whitneyFst A' D' = whitneyFst A D ≫ f :=
  whitneyLift_fst _ _

@[reassoc (attr := simp)]
theorem whitneyMap_snd (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ whitneySnd A' D' = whitneySnd A D ≫ g :=
  whitneyLift_snd _ _

@[reassoc (attr := simp)]
theorem whitneyInl_map (f : A ⟶ A') (g : D ⟶ D') :
    whitneyInl A D ≫ whitneyMap f g = f ≫ whitneyInl A' D' :=
  whitneySum_hom_ext (by simp) (by simp)

@[reassoc (attr := simp)]
theorem whitneyInr_map (f : A ⟶ A') (g : D ⟶ D') :
    whitneyInr A D ≫ whitneyMap f g = g ≫ whitneyInr A' D' :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyMap_id (A D : FiniteRankAtlas 𝕜 X) :
    whitneyMap (𝟙 A) (𝟙 D) = 𝟙 (whitneySum A D) := by
  simp [whitneyMap_def]

@[simp]
theorem whitneyMap_zero (A A' D D' : FiniteRankAtlas 𝕜 X) :
    whitneyMap (0 : A ⟶ A') (0 : D ⟶ D') = 0 :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyMap_comp (f₁ : A ⟶ A') (f₂ : A' ⟶ A'') (g₁ : D ⟶ D') (g₂ : D' ⟶ D'') :
    whitneyMap (f₁ ≫ f₂) (g₁ ≫ g₂) = whitneyMap f₁ g₁ ≫ whitneyMap f₂ g₂ :=
  whitneySum_hom_ext (by simp) (by simp)

/-- On each fibre, `whitneyMap f g` acts as `Prod.map` conjugated by `splitCoords`. -/
@[simp]
theorem fiberMap_whitneyMap (f : A ⟶ A') (g : D ⟶ D') (x : X) :
    (whitneyMap f g).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A'.rank x) (D'.rank x)).symm.toLinearEquiv.toLinearMap.comp
        (((f.fiberMap x).prodMap (g.fiberMap x)).comp
          (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearEquiv.toLinearMap) := by
  rw [whitneyMap, fiberMap_whitneyLift]
  ext v
  rfl

theorem whitneySumFiberEquiv_fiberMap_whitneyMap (f : A ⟶ A') (g : D ⟶ D') (x : X)
    (v : (whitneySum A D).Fiber x) :
    whitneySumFiberEquiv A' D' x ((whitneyMap f g).fiberMap x v) =
      (f.fiberMap x (whitneySumFiberEquiv A D x v).1,
        g.fiberMap x (whitneySumFiberEquiv A D x v).2) := by
  rw [whitneySumFiberEquiv_apply, whitneySumFiberEquiv_apply, fiberMap_whitneyMap]
  exact (splitCoords (𝕜 := 𝕜) (A'.rank x) (D'.rank x)).apply_symm_apply _

/-- `whitneySumTotalSpaceHomeomorph` intertwines `whitneyMap f g` with the componentwise action of
`f` and `g` on Mathlib's direct-sum bundle. -/
theorem whitneySumTotalSpaceHomeomorph_naturality (f : A ⟶ A') (g : D ⟶ D')
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    whitneySumTotalSpaceHomeomorph A' D' ((whitneyMap f g).totalSpaceMap p) =
      ⟨(whitneySumTotalSpaceHomeomorph A D p).proj,
        (f.fiberMap (whitneySumTotalSpaceHomeomorph A D p).proj
          (whitneySumTotalSpaceHomeomorph A D p).2.1,
         g.fiberMap (whitneySumTotalSpaceHomeomorph A D p).proj
          (whitneySumTotalSpaceHomeomorph A D p).2.2)⟩ := by
  rcases p with ⟨x, v⟩
  let F : TotalSpace (Unit × Unit) (A.Fiber ×ᵇ D.Fiber) →
      TotalSpace (Unit × Unit) (A'.Fiber ×ᵇ D'.Fiber) :=
    fun q => ⟨q.proj, (f.fiberMap q.proj q.2.1, g.fiberMap q.proj q.2.2)⟩
  refine (congrArg (whitneySumTotalSpaceHomeomorph A' D')
    (Hom.totalSpaceMap_mk (whitneyMap f g) x v)).trans ?_
  refine (whitneySumTotalSpaceHomeomorph_apply A' D' _).trans ?_
  refine (congrArg (TotalSpace.mk' (Unit × Unit) x (E := A'.Fiber ×ᵇ D'.Fiber))
    (whitneySumFiberEquiv_fiberMap_whitneyMap f g x v)).trans ?_
  exact (congrArg F (whitneySumTotalSpaceHomeomorph_apply A D ⟨x, v⟩)).symm

/-- Direct sum of two bundle atlas isomorphisms. -/
def whitneyMapIso (e₁ : A ≅ A') (e₂ : D ≅ D') : whitneySum A D ≅ whitneySum A' D' where
  hom := whitneyMap e₁.hom e₂.hom
  inv := whitneyMap e₁.inv e₂.inv
  hom_inv_id := by rw [← whitneyMap_comp, e₁.hom_inv_id, e₂.hom_inv_id, whitneyMap_id]
  inv_hom_id := by rw [← whitneyMap_comp, e₁.inv_hom_id, e₂.inv_hom_id, whitneyMap_id]

@[simp]
theorem whitneyMapIso_hom (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).hom = whitneyMap e₁.hom e₂.hom := (rfl)

@[simp]
theorem whitneyMapIso_inv (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).inv = whitneyMap e₁.inv e₂.inv := (rfl)

end UniversalProperty

section Coherence

/-- Symmetry isomorphism exchanging the two summands of a Whitney sum. -/
def whitneyCommIso (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ≅ whitneySum D A where
  hom := whitneyLift (whitneySnd A D) (whitneyFst A D)
  inv := whitneyLift (whitneySnd D A) (whitneyFst D A)
  hom_inv_id := whitneySum_hom_ext (by simp) (by simp)
  inv_hom_id := whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyCommIso_hom (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyCommIso A D).hom = whitneyLift (whitneySnd A D) (whitneyFst A D) := (rfl)

@[simp]
theorem whitneyCommIso_inv (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyCommIso A D).inv = whitneyLift (whitneySnd D A) (whitneyFst D A) := (rfl)

@[reassoc]
theorem whitneyMap_commIso_hom {A A' D D' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ (whitneyCommIso A' D').hom =
      (whitneyCommIso A D).hom ≫ whitneyMap g f :=
  whitneySum_hom_ext (by simp) (by simp)

/-- Associativity isomorphism regrouping a threefold Whitney sum. -/
def whitneyAssocIso (A D C : FiniteRankAtlas 𝕜 X) :
    whitneySum (whitneySum A D) C ≅ whitneySum A (whitneySum D C) where
  hom := whitneyLift (whitneyFst _ _ ≫ whitneyFst A D)
    (whitneyLift (whitneyFst _ _ ≫ whitneySnd A D) (whitneySnd _ _))
  inv := whitneyLift (whitneyLift (whitneyFst _ _) (whitneySnd _ _ ≫ whitneyFst D C))
    (whitneySnd _ _ ≫ whitneySnd D C)
  hom_inv_id := whitneySum_hom_ext (whitneySum_hom_ext (by simp) (by simp)) (by simp)
  inv_hom_id := whitneySum_hom_ext (by simp) (whitneySum_hom_ext (by simp) (by simp))

@[simp]
theorem whitneyAssocIso_hom (A D C : FiniteRankAtlas 𝕜 X) :
    (whitneyAssocIso A D C).hom =
      whitneyLift (whitneyFst _ _ ≫ whitneyFst A D)
        (whitneyLift (whitneyFst _ _ ≫ whitneySnd A D) (whitneySnd _ _)) := (rfl)

@[simp]
theorem whitneyAssocIso_inv (A D C : FiniteRankAtlas 𝕜 X) :
    (whitneyAssocIso A D C).inv =
      whitneyLift (whitneyLift (whitneyFst _ _) (whitneySnd _ _ ≫ whitneyFst D C))
        (whitneySnd _ _ ≫ whitneySnd D C) := (rfl)

@[reassoc]
theorem whitneyMap_assocIso_hom {A A' D D' C C' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') (h : C ⟶ C') :
    whitneyMap (whitneyMap f g) h ≫ (whitneyAssocIso A' D' C').hom =
      (whitneyAssocIso A D C).hom ≫ whitneyMap f (whitneyMap g h) :=
  whitneySum_hom_ext (by simp) (whitneySum_hom_ext (by simp) (by simp))

/-- Left unit isomorphism for Whitney sum with the trivial rank-zero atlas. -/
def whitneyZeroLeftIso (A : FiniteRankAtlas 𝕜 X) :
    whitneySum (trivial 𝕜 (0 : LocallyConstant X ℕ)) A ≅ A where
  hom := whitneySnd (trivial 𝕜 0) A
  inv := whitneyInr (trivial 𝕜 0) A
  hom_inv_id := whitneySum_hom_ext' (isZero_trivial_zero.eq_of_src _ _) (by simp)
  inv_hom_id := whitneyInr_snd (trivial 𝕜 0) A

@[simp]
theorem whitneyZeroLeftIso_hom (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroLeftIso A).hom = whitneySnd (trivial 𝕜 0) A := (rfl)

@[simp]
theorem whitneyZeroLeftIso_inv (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroLeftIso A).inv = whitneyInr (trivial 𝕜 0) A := (rfl)

@[reassoc]
theorem whitneyMap_zeroLeftIso_hom {A A' : FiniteRankAtlas 𝕜 X}
    (g : trivial 𝕜 (0 : LocallyConstant X ℕ) ⟶ trivial 𝕜 0) (f : A ⟶ A') :
    whitneyMap g f ≫ (whitneyZeroLeftIso A').hom = (whitneyZeroLeftIso A).hom ≫ f := by
  simp only [whitneyZeroLeftIso_hom, whitneyMap_snd]

/-- Right unit isomorphism for Whitney sum with the trivial rank-zero atlas. -/
def whitneyZeroRightIso (A : FiniteRankAtlas 𝕜 X) :
    whitneySum A (trivial 𝕜 (0 : LocallyConstant X ℕ)) ≅ A where
  hom := whitneyFst A (trivial 𝕜 0)
  inv := whitneyInl A (trivial 𝕜 0)
  hom_inv_id := whitneySum_hom_ext' (by simp) (isZero_trivial_zero.eq_of_src _ _)
  inv_hom_id := whitneyInl_fst A (trivial 𝕜 0)

@[simp]
theorem whitneyZeroRightIso_hom (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroRightIso A).hom = whitneyFst A (trivial 𝕜 0) := (rfl)

@[simp]
theorem whitneyZeroRightIso_inv (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroRightIso A).inv = whitneyInl A (trivial 𝕜 0) := (rfl)

@[reassoc]
theorem whitneyMap_zeroRightIso_hom {A A' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : trivial 𝕜 (0 : LocallyConstant X ℕ) ⟶ trivial 𝕜 0) :
    whitneyMap f g ≫ (whitneyZeroRightIso A').hom = (whitneyZeroRightIso A).hom ≫ f := by
  simp only [whitneyZeroRightIso_hom, whitneyMap_fst]

private theorem continuous_trivialAdd_toFun (r s : LocallyConstant X ℕ) :
    Continuous (fun p : TotalSpace Unit (trivial 𝕜 (r + s)).Fiber =>
      (⟨p.proj, p.2⟩ : TotalSpace Unit (whitneySum (trivial 𝕜 r) (trivial 𝕜 s)).Fiber)) := by
  have hrs := continuous_trivial_iff.1
    (continuous_id (X := TotalSpace Unit (trivial 𝕜 (r + s)).Fiber))
  apply (continuous_pairStrata_iff (A := trivial 𝕜 r) (D := trivial 𝕜 s) hrs.1).2
  intro a d
  let Z := {p : TotalSpace Unit (trivial 𝕜 (r + s)).Fiber // r p.proj = a ∧ s p.proj = d}
  let φ : Z → {p : TotalSpace Unit (trivial 𝕜 (r + s)).Fiber // (r + s) p.proj = a + d} :=
    fun z => ⟨z.1, by simp [z.2.1, z.2.2]⟩
  let uv : Z → (Fin a → 𝕜) × (Fin d → 𝕜) :=
    fun z => splitCoords (𝕜 := 𝕜) a d (fun i => (φ z).1.2 (Fin.cast (φ z).2.symm i))
  have hb : Continuous (fun z : Z => z.1.proj) := hrs.1.comp continuous_subtype_val
  have huv : Continuous uv := (splitCoords (𝕜 := 𝕜) a d).continuous.comp
    ((hrs.2 (a + d)).comp (continuous_subtype_val.subtype_mk _))
  refine ((continuous_mk_whitneySum_iff (A := trivial 𝕜 r) (D := trivial 𝕜 s)
    (b := fun z : Z => z.1.proj)
    (fun z i => (uv z).1 (Fin.cast z.2.1 i))
    (fun z i => (uv z).2 (Fin.cast z.2.2 i))).2
      ⟨(continuous_mk_trivial_of_rank_eq_iff fun z => z.2.1).2 ⟨hb, huv.fst⟩,
       (continuous_mk_trivial_of_rank_eq_iff fun z => z.2.2).2 ⟨hb, huv.snd⟩⟩).congr fun z => ?_
  rcases z with ⟨⟨x, v⟩, ha, hd⟩
  dsimp only [Z, uv, φ] at ha hd ⊢
  subst ha; subst hd
  exact congrArg (TotalSpace.mk' Unit x)
    ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (r x) (s x)).symm_apply_apply v)

private theorem continuous_trivialAdd_invFun (r s : LocallyConstant X ℕ) :
    Continuous (fun p : TotalSpace Unit (whitneySum (trivial 𝕜 r) (trivial 𝕜 s)).Fiber =>
      (⟨p.proj, p.2⟩ : TotalSpace Unit (trivial 𝕜 (r + s)).Fiber)) := by
  have hw := continuous_whitneySum_iff.1
    (continuous_id (X := TotalSpace Unit (whitneySum (trivial 𝕜 r) (trivial 𝕜 s)).Fiber))
  have hr := continuous_trivial_iff.1 hw.1
  have hs := continuous_trivial_iff.1 hw.2
  apply (continuous_pairStrata_iff (A := trivial 𝕜 r) (D := trivial 𝕜 s)
    (whitneySum (trivial 𝕜 r) (trivial 𝕜 s)).continuous_proj).2
  intro a d
  let Z := {p : TotalSpace Unit (whitneySum (trivial 𝕜 r) (trivial 𝕜 s)).Fiber //
    r p.proj = a ∧ s p.proj = d}
  have hrs : ∀ z : Z, (r + s) z.1.proj = a + d := fun z => by simp [z.2.1, z.2.2]
  have hc := (splitCoords (𝕜 := 𝕜) a d).symm.continuous.comp
    (((hr.2 a).comp (continuous_subtype_val.subtype_mk fun z : Z => z.2.1)).prodMk
      ((hs.2 d).comp (continuous_subtype_val.subtype_mk fun z : Z => z.2.2)))
  refine ((continuous_mk_trivial_of_rank_eq_iff hrs).2
    ⟨(whitneySum (trivial 𝕜 r) (trivial 𝕜 s)).continuous_proj.comp continuous_subtype_val,
      hc⟩).congr fun z => ?_
  rcases z with ⟨⟨x, v⟩, ha, hd⟩
  dsimp only [Z] at ha hd ⊢
  subst ha; subst hd
  exact congrArg (TotalSpace.mk' Unit x)
    ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (r x) (s x)).symm_apply_apply v)

/-- The trivial atlas of rank `r + s` is isomorphic, by the identity on every coordinate fibre, to
the Whitney sum of the trivial atlases of ranks `r` and `s`. -/
def trivialAddIso (r s : LocallyConstant X ℕ) :
    trivial 𝕜 (r + s) ≅ whitneySum (trivial 𝕜 r) (trivial 𝕜 s) :=
  isoMk (fun x => LinearEquiv.refl 𝕜 (Fin (r x + s x) → 𝕜))
    (continuous_trivialAdd_toFun r s)
    (continuous_trivialAdd_invFun r s)

@[simp]
theorem fiberMap_trivialAddIso_hom (r s : LocallyConstant X ℕ) (x : X) :
    (trivialAddIso (𝕜 := 𝕜) r s).hom.fiberMap x = LinearMap.id :=
  fiberMap_isoMk_hom _ _ _ x

@[simp]
theorem fiberMap_trivialAddIso_inv (r s : LocallyConstant X ℕ) (x : X) :
    (trivialAddIso (𝕜 := 𝕜) r s).inv.fiberMap x = LinearMap.id :=
  fiberMap_isoMk_inv _ _ _ x

end Coherence

end TauCeti.FiniteRankAtlas
