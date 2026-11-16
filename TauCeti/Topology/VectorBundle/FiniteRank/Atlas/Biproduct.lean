/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.Algebra.Module.Equiv.Fin
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Topology.LocallyConstant.Algebra

import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Zero objects and Whitney sums of variable-rank bundle atlases

Variable-rank bundle atlases `TauCeti.FiniteRankAtlas 𝕜 X` admit zero objects and binary
(hence finite) biproducts over an arbitrary topological base `X` and nontrivially normed
field `𝕜`, without bounded-rank, compactness, separation, or completeness assumptions.

An atlas is a zero object precisely when its locally constant rank vanishes identically
(`isZero_iff_rank_eq_zero`), with `FiniteRankAtlas.trivial 𝕜 0` supplying a canonical
zero object (`HasZeroObject`).

The Whitney sum `whitneySum A D` has locally constant rank `A.rank + D.rank`. On each
total-rank stratum `n`, its chart domains intersect the summand charts on the open
joint-rank strata, and its transition maps conjugate block-diagonal summand transitions
by `TauCeti.splitCoords`. Its reconstructed total-space topology is characterized by
`continuous_mk_whitneySum_iff` and identified with the fibre product of the summand total
spaces over `X` by `whitneySumTotalSpaceHomeomorph`.

The coordinate-block projections and inclusions (`whitneyFst`, `whitneySnd`, `whitneyInl`,
`whitneyInr`) assemble into a binary bicone (`whitneyBicone`) whose bilimit property
(`whitneyBiconeIsBilimit`, via Mathlib's `CategoryTheory.Limits.isBinaryBilimitOfTotal`)
yields `HasBinaryBiproducts`, `HasFiniteBiproducts`, the canonical comparison isomorphism
`whitneySumIsoBiprod : whitneySum A D ≅ A ⊞ D`, and rank additivity (`rank_zero`,
`rank_biprod`). Concrete pairing (`whitneyLift`), copairing (`whitneyDesc`), direct sums
of morphisms and isomorphisms (`whitneyMap`, `whitneyMapIso`), structural coherence
isomorphisms (`whitneyCommIso`, `whitneyAssocIso`, `whitneyZeroLeftIso`,
`whitneyZeroRightIso`), and the trivial-atlas sum isomorphism (`whitneyTrivialIso`) are
provided directly on `whitneySum`.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits ZeroObject Topology Set

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

section ZeroObject

/-- A variable-rank atlas whose rank vanishes everywhere is a zero object. -/
theorem isZero_of_rank_eq_zero (A : FiniteRankAtlas 𝕜 X) (h : A.rank = 0) : IsZero A where
  unique_to D := ⟨⟨⟨0⟩, fun f => hom_ext fun x => LinearMap.ext fun v => by
    have hv : v = 0 := funext fun i => (Fin.cast (DFunLike.congr_fun h x) i).elim0
    rw [hv, map_zero, map_zero]⟩⟩
  unique_from D := ⟨⟨⟨0⟩, fun f => hom_ext fun x => LinearMap.ext fun v =>
    funext fun i => (Fin.cast (DFunLike.congr_fun h x) i).elim0⟩⟩

/-- The trivial atlas of zero rank is a zero object. -/
theorem isZero_trivial_zero : IsZero (trivial 𝕜 (0 : LocallyConstant X ℕ)) :=
  isZero_of_rank_eq_zero _ (rank_trivial 𝕜 0)

/-- The trivial rank-zero atlas supplies the category's zero object. -/
instance : HasZeroObject (FiniteRankAtlas 𝕜 X) :=
  ⟨⟨trivial 𝕜 0, isZero_trivial_zero⟩⟩

/-- A variable-rank atlas is a zero object precisely when its rank is identically zero. -/
theorem isZero_iff_rank_eq_zero (A : FiniteRankAtlas 𝕜 X) : IsZero A ↔ A.rank = 0 :=
  ⟨fun h => (h.iso isZero_trivial_zero).finiteRankAtlas_rank_eq, isZero_of_rank_eq_zero A⟩

/-- The zero atlas has identically zero rank. -/
@[simp] theorem rank_zero : (0 : FiniteRankAtlas 𝕜 X).rank = 0 :=
  (isZero_iff_rank_eq_zero _).1 (Limits.isZero_zero _)

end ZeroObject

section WhitneySum

private def splitCoordsCongr {a b n : ℕ} (h : a + b = n) :
    (Fin n → 𝕜) ≃L[𝕜] (Fin a → 𝕜) × (Fin b → 𝕜) :=
  (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n ↦ 𝕜) (finCongr h)).symm.trans
    (splitCoords (𝕜 := 𝕜) a b)

private theorem splitCoordsCongr_rfl {a b : ℕ} (v : Fin (a + b) → 𝕜) :
    splitCoordsCongr (𝕜 := 𝕜) (rfl : a + b = a + b) v = splitCoords (𝕜 := 𝕜) a b v :=
  rfl

private theorem splitCoordsCongr_symm_rfl {a b : ℕ} (w : (Fin a → 𝕜) × (Fin b → 𝕜)) :
    (splitCoordsCongr (𝕜 := 𝕜) (rfl : a + b = a + b)).symm w =
      (splitCoords (𝕜 := 𝕜) a b).symm w :=
  rfl

private theorem splitCoords_cast {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b)
    (v : Fin (a' + b') → 𝕜) :
    splitCoords (𝕜 := 𝕜) a b (fun i => v (Fin.cast (congrArg₂ (· + ·) ha hb).symm i)) =
      (fun i => (splitCoords (𝕜 := 𝕜) a' b' v).1 (Fin.cast ha.symm i),
       fun i => (splitCoords (𝕜 := 𝕜) a' b' v).2 (Fin.cast hb.symm i)) := by
  cases ha
  cases hb
  rfl

private theorem mem_baseSet_cast (A : FiniteRankAtlas 𝕜 X) {m n : ℕ} (h : m = n)
    {i x : X} {hi : A.rank i = m} {hx : A.rank x = m}
    (hmem : (⟨x, hx⟩ : {z : X // A.rank z = m}) ∈ (A.charts m).baseSet ⟨i, hi⟩) :
    (⟨x, hx.trans h⟩ : {z : X // A.rank z = n}) ∈ (A.charts n).baseSet ⟨i, hi.trans h⟩ := by
  cases h
  exact hmem

private theorem totalSpaceHomeomorph_cast (A : FiniteRankAtlas 𝕜 X) {n : ℕ} (x : X)
    (hx : A.rank x = n) (v : A.Fiber x) :
    A.totalSpaceHomeomorph ⟨n, ⟨⟨x, hx⟩, fun i => v (Fin.cast hx.symm i)⟩⟩ = ⟨x, v⟩ := by
  cases hx
  simp only [totalSpaceHomeomorph_apply, Fin.cast_refl, id_eq]

private def whitneyBaseSet (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (i : {x : X // (A.rank + D.rank) x = n}) :
    Set {x : X // (A.rank + D.rank) x = n} :=
  {x | ∃ (hA : A.rank x.1 = A.rank i.1) (hD : D.rank x.1 = D.rank i.1),
    ⟨x.1, hA⟩ ∈ (A.charts (A.rank i.1)).baseSet ⟨i.1, rfl⟩ ∧
    ⟨x.1, hD⟩ ∈ (D.charts (D.rank i.1)).baseSet ⟨i.1, rfl⟩}

private theorem isOpen_whitneyBaseSet (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (i : {x : X // (A.rank + D.rank) x = n}) :
    IsOpen (whitneyBaseSet A D n i) := by
  have hA : IsOpen (Subtype.val '' (A.charts (A.rank i.1)).baseSet ⟨i.1, rfl⟩) :=
    (A.rank.isLocallyConstant.isOpen_fiber _).isOpenEmbedding_subtypeVal.isOpenMap _
      ((A.charts _).isOpen_baseSet _)
  have hD : IsOpen (Subtype.val '' (D.charts (D.rank i.1)).baseSet ⟨i.1, rfl⟩) :=
    (D.rank.isLocallyConstant.isOpen_fiber _).isOpenEmbedding_subtypeVal.isOpenMap _
      ((D.charts _).isOpen_baseSet _)
  have heq : whitneyBaseSet A D n i =
      Subtype.val ⁻¹' ((Subtype.val '' (A.charts (A.rank i.1)).baseSet ⟨i.1, rfl⟩) ∩
        (Subtype.val '' (D.charts (D.rank i.1)).baseSet ⟨i.1, rfl⟩)) := by
    ext x
    simp only [whitneyBaseSet, mem_ofPred_eq, mem_preimage, mem_inter_iff, mem_image,
      Subtype.exists]
    constructor
    · rintro ⟨hA, hD, hxA, hxD⟩
      exact ⟨⟨x.1, hA, hxA, rfl⟩, ⟨x.1, hD, hxD, rfl⟩⟩
    · rintro ⟨⟨_, hA, hxA, rfl⟩, ⟨_, hD, hxD, rfl⟩⟩
      exact ⟨hA, hD, hxA, hxD⟩
  rw [heq]
  exact (hA.inter hD).preimage continuous_subtype_val

private def whitneyCoordChangeAux (A D : FiniteRankAtlas 𝕜 X) {a b n : ℕ} (hab : a + b = n)
    (i j x : X) (hiA : A.rank i = a) (hjA : A.rank j = a) (hxA : A.rank x = a)
    (hiD : D.rank i = b) (hjD : D.rank j = b) (hxD : D.rank x = b) :
    (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜) :=
  let e := splitCoordsCongr (𝕜 := 𝕜) hab
  e.symm.toContinuousLinearMap.comp
    ((((A.charts a).coordChange ⟨i, hiA⟩ ⟨j, hjA⟩ ⟨x, hxA⟩).prodMap
      ((D.charts b).coordChange ⟨i, hiD⟩ ⟨j, hjD⟩ ⟨x, hxD⟩)).comp e.toContinuousLinearMap)

private def whitneyCoordChange (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (i j x : {x : X // (A.rank + D.rank) x = n}) :
    (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜) :=
  if h : A.rank x.1 = A.rank i.1 ∧ D.rank x.1 = D.rank i.1 ∧
      A.rank j.1 = A.rank i.1 ∧ D.rank j.1 = D.rank i.1 then
    whitneyCoordChangeAux A D i.2 i.1 j.1 x.1 rfl h.2.2.1 h.1 rfl h.2.2.2 h.2.1
  else
    0

private theorem whitneyCoordChange_eq (A D : FiniteRankAtlas 𝕜 X) {n : ℕ}
    (i j x : {x : X // (A.rank + D.rank) x = n})
    {a b : ℕ} (hab : a + b = n)
    (hiA : A.rank i.1 = a) (hjA : A.rank j.1 = a) (hxA : A.rank x.1 = a)
    (hiD : D.rank i.1 = b) (hjD : D.rank j.1 = b) (hxD : D.rank x.1 = b) :
    whitneyCoordChange A D n i j x =
      whitneyCoordChangeAux A D hab i.1 j.1 x.1 hiA hjA hxA hiD hjD hxD := by
  subst hiA
  subst hiD
  exact dite_eq_left ⟨hxA, hxD, hjA, hjD⟩

private theorem continuousOn_whitneyCoordChange (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (i j : {x : X // (A.rank + D.rank) x = n}) :
    ContinuousOn (whitneyCoordChange A D n i j)
      (whitneyBaseSet A D n i ∩ whitneyBaseSet A D n j) := by
  by_cases hj : A.rank j.1 = A.rank i.1 ∧ D.rank j.1 = D.rank i.1
  · let U := whitneyBaseSet A D n i ∩ whitneyBaseSet A D n j
    have hAx (x : U) : A.rank x.1.1 = A.rank i.1 := let ⟨hA, _⟩ := x.2.1; hA
    have hDx (x : U) : D.rank x.1.1 = D.rank i.1 := let ⟨_, hD, _⟩ := x.2.1; hD
    have hcA := ((A.charts (A.rank i.1)).continuousOn_coordChange
      ⟨i.1, rfl⟩ ⟨j.1, hj.1⟩).comp_continuous
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk hAx) fun x =>
        ⟨let ⟨_, _, h, _⟩ := x.2.1; h, let ⟨_, _, h, _⟩ := x.2.2; mem_baseSet_cast A hj.1 h⟩
    have hcD := ((D.charts (D.rank i.1)).continuousOn_coordChange
      ⟨i.1, rfl⟩ ⟨j.1, hj.2⟩).comp_continuous
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk hDx) fun x =>
        ⟨let ⟨_, _, _, h⟩ := x.2.1; h, let ⟨_, _, _, h⟩ := x.2.2; mem_baseSet_cast D hj.2 h⟩
    rw [continuousOn_iff_continuous_domRestrict]
    refine (((hcA.prod_mapL 𝕜 hcD).clm_comp_const
      (splitCoordsCongr (𝕜 := 𝕜) i.2).toContinuousLinearMap).const_clm_comp
      (splitCoordsCongr (𝕜 := 𝕜) i.2).symm.toContinuousLinearMap).congr fun x => ?_
    exact (whitneyCoordChange_eq A D i j x.1 i.2 rfl hj.1 (hAx x) rfl hj.2 (hDx x)).symm
  · have hempty : whitneyBaseSet A D n i ∩ whitneyBaseSet A D n j = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
      rintro ⟨⟨hAi, hDi, _⟩, ⟨hAj, hDj, _⟩⟩
      exact hj ⟨hAj.symm.trans hAi, hDj.symm.trans hDi⟩
    rw [hempty]
    exact continuousOn_empty _

private theorem whitneyCoordChange_self (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (i x : {x : X // (A.rank + D.rank) x = n}) (hx : x ∈ whitneyBaseSet A D n i)
    (v : Fin n → 𝕜) :
    whitneyCoordChange A D n i i x v = v := by
  rcases hx with ⟨hA, hD, hxA, hxD⟩
  rw [whitneyCoordChange_eq A D i i x i.2 rfl rfl hA rfl rfl hD]
  simp only [whitneyCoordChangeAux, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.coe_prodMap', Prod.map_apply',
    (A.charts (A.rank i.1)).coordChange_self _ _ hxA,
    (D.charts (D.rank i.1)).coordChange_self _ _ hxD, Prod.mk.eta,
    ContinuousLinearEquiv.symm_apply_apply]

private theorem whitneyCoordChange_comp (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (i j k x : {x : X // (A.rank + D.rank) x = n})
    (hx : x ∈ (whitneyBaseSet A D n i ∩ whitneyBaseSet A D n j) ∩ whitneyBaseSet A D n k)
    (v : Fin n → 𝕜) :
    whitneyCoordChange A D n j k x (whitneyCoordChange A D n i j x v) =
      whitneyCoordChange A D n i k x v := by
  rcases hx with ⟨⟨⟨hAi, hDi, hxAi, hxDi⟩, ⟨hAj, hDj, hxAj, hxDj⟩⟩, ⟨hAk, hDk, hxAk, hxDk⟩⟩
  rw [whitneyCoordChange_eq A D j k x x.2 hAj.symm hAk.symm rfl hDj.symm hDk.symm rfl,
    whitneyCoordChange_eq A D i j x x.2 hAi.symm hAj.symm rfl hDi.symm hDj.symm rfl,
    whitneyCoordChange_eq A D i k x x.2 hAi.symm hAk.symm rfl hDi.symm hDk.symm rfl]
  simp only [whitneyCoordChangeAux, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply']
  have hxAi' := mem_baseSet_cast A hAi.symm hxAi
  have hxAj' := mem_baseSet_cast A hAj.symm hxAj
  have hxAk' := mem_baseSet_cast A hAk.symm hxAk
  have hxDi' := mem_baseSet_cast D hDi.symm hxDi
  have hxDj' := mem_baseSet_cast D hDj.symm hxDj
  have hxDk' := mem_baseSet_cast D hDk.symm hxDk
  rw [(A.charts (A.rank x.1)).coordChange_comp ⟨i.1, hAi.symm⟩ ⟨j.1, hAj.symm⟩ ⟨k.1, hAk.symm⟩
      ⟨x.1, rfl⟩ ⟨⟨hxAi', hxAj'⟩, hxAk'⟩,
    (D.charts (D.rank x.1)).coordChange_comp ⟨i.1, hDi.symm⟩ ⟨j.1, hDj.symm⟩ ⟨k.1, hDk.symm⟩
      ⟨x.1, rfl⟩ ⟨⟨hxDi', hxDj'⟩, hxDk'⟩]

/-- The Whitney sum of two variable-rank bundle atlases, with locally constant rank
`A.rank + D.rank` and block-diagonal transitions on each joint-rank stratum. -/
-- Expose the rank projection so the dependent fibres reduce to `Fin (A.rank x + D.rank x) → 𝕜`.
@[expose] def whitneySum (A D : FiniteRankAtlas 𝕜 X) : FiniteRankAtlas 𝕜 X where
  rank := A.rank + D.rank
  charts n :=
    { baseSet := fun i =>
        {x | ∃ (hA : A.rank x.1 = A.rank i.1) (hD : D.rank x.1 = D.rank i.1),
          ⟨x.1, hA⟩ ∈ (A.charts (A.rank i.1)).baseSet ⟨i.1, rfl⟩ ∧
          ⟨x.1, hD⟩ ∈ (D.charts (D.rank i.1)).baseSet ⟨i.1, rfl⟩}
      isOpen_baseSet := fun i => by exact isOpen_whitneyBaseSet A D n i
      indexAt := id
      mem_baseSet_at := fun x =>
        ⟨rfl, rfl, A.mem_baseSet_self _ ⟨x.1, rfl⟩, D.mem_baseSet_self _ ⟨x.1, rfl⟩⟩
      coordChange := fun i j x =>
        if h : A.rank x.1 = A.rank i.1 ∧ D.rank x.1 = D.rank i.1 ∧
            A.rank j.1 = A.rank i.1 ∧ D.rank j.1 = D.rank i.1 then
          let e := (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n ↦ 𝕜)
            (finCongr i.2)).symm.trans (splitCoords (𝕜 := 𝕜) (A.rank i.1) (D.rank i.1))
          e.symm.toContinuousLinearMap.comp
            ((((A.charts (A.rank i.1)).coordChange ⟨i.1, rfl⟩ ⟨j.1, h.2.2.1⟩ ⟨x.1, h.1⟩).prodMap
              ((D.charts (D.rank i.1)).coordChange ⟨i.1, rfl⟩ ⟨j.1, h.2.2.2⟩ ⟨x.1, h.2.1⟩)).comp
              e.toContinuousLinearMap)
        else
          0
      coordChange_self := fun i x hx v => by exact whitneyCoordChange_self A D n i x hx v
      continuousOn_coordChange := fun i j => by exact continuousOn_whitneyCoordChange A D n i j
      coordChange_comp := fun i j k x hx v => by exact whitneyCoordChange_comp A D n i j k x hx v }
  indexAt_eq _ _ := rfl

@[simp] theorem rank_whitneySum (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySum A D).rank = A.rank + D.rank := (rfl)

private theorem whitneySum_coordChange_eq (A D : FiniteRankAtlas 𝕜 X) {n : ℕ}
    (i j x : {x : X // (whitneySum A D).rank x = n})
    {a d : ℕ} (had : a + d = n)
    (hiA : A.rank i.1 = a) (hjA : A.rank j.1 = a) (hxA : A.rank x.1 = a)
    (hiD : D.rank i.1 = d) (hjD : D.rank j.1 = d) (hxD : D.rank x.1 = d) :
    ((whitneySum A D).charts n).coordChange i j x =
      whitneyCoordChangeAux A D had i.1 j.1 x.1 hiA hjA hxA hiD hjD hxD :=
  whitneyCoordChange_eq A D i j x had hiA hjA hxA hiD hjD hxD

/-- On each fibre, the Whitney sum is continuously linearly equivalent to the product of the
two summand fibres via `TauCeti.splitCoords`. -/
def whitneySumFiberEquiv (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneySum A D).Fiber x ≃L[𝕜] A.Fiber x × D.Fiber x :=
  splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)

theorem whitneySumFiberEquiv_apply (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    whitneySumFiberEquiv A D x v = splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v := (rfl)

theorem whitneySumFiberEquiv_symm_apply (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (w : A.Fiber x × D.Fiber x) :
    (whitneySumFiberEquiv A D x).symm w = (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm w :=
  (rfl)

private theorem continuous_iff_jointStrata {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {b : Y → X} (hb : Continuous b) (A D : FiniteRankAtlas 𝕜 X) (f : Y → Z) :
    Continuous f ↔
      ∀ a d : ℕ, Continuous (fun y : {y : Y // A.rank (b y) = a ∧ D.rank (b y) = d} => f y.1) := by
  constructor
  · intro hf a d
    exact hf.comp continuous_subtype_val
  · intro hf
    apply continuous_of_cover_nhds
      (s := fun p : ℕ × ℕ => {y : Y | A.rank (b y) = p.1 ∧ D.rank (b y) = p.2})
    · intro y
      exact ⟨(A.rank (b y), D.rank (b y)),
        (((A.rank.isLocallyConstant.isOpen_fiber _).preimage hb).inter
          ((D.rank.isLocallyConstant.isOpen_fiber _).preimage hb)).mem_nhds ⟨rfl, rfl⟩⟩
    · rintro ⟨a, d⟩
      rw [continuousOn_iff_continuous_domRestrict]
      exact hf a d

private theorem whitneyCoordChangeAux_rfl_apply (A D : FiniteRankAtlas 𝕜 X) {a d : ℕ}
    (i j x : X) (hiA : A.rank i = a) (hjA : A.rank j = a) (hxA : A.rank x = a)
    (hiD : D.rank i = d) (hjD : D.rank j = d) (hxD : D.rank x = d) (v : Fin (a + d) → 𝕜) :
    whitneyCoordChangeAux A D (rfl : a + d = a + d) i j x hiA hjA hxA hiD hjD hxD v =
      (splitCoords (𝕜 := 𝕜) a d).symm
        ((A.charts a).coordChange ⟨i, hiA⟩ ⟨j, hjA⟩ ⟨x, hxA⟩ (splitCoords (𝕜 := 𝕜) a d v).1,
         (D.charts d).coordChange ⟨i, hiD⟩ ⟨j, hjD⟩ ⟨x, hxD⟩ (splitCoords (𝕜 := 𝕜) a d v).2) := by
  simp only [whitneyCoordChangeAux, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, splitCoordsCongr_rfl, splitCoordsCongr_symm_rfl,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply']

private theorem continuous_mk_iff_of_rank_eq {Y : Type*} [TopologicalSpace Y]
    (A : FiniteRankAtlas 𝕜 X) {b : Y → X} {n : ℕ} (hr : ∀ y, A.rank (b y) = n)
    (s : ∀ y, A.Fiber (b y)) :
    Continuous (fun y => (⟨b y, s y⟩ : TotalSpace Unit A.Fiber)) ↔
      Continuous (fun y =>
        (⟨⟨b y, hr y⟩, fun i => s y (Fin.cast (hr y).symm i)⟩ : (A.charts n).TotalSpace)) := by
  rw [(A.isOpenEmbedding_stratum n).isEmbedding.continuous_iff]
  exact continuous_congr fun y => (A.totalSpaceHomeomorph_cast (b y) (hr y) (s y)).symm

private theorem trivializationAt_whitneySum_snd (A D : FiniteRankAtlas 𝕜 X) {a d : ℕ}
    {x₀ x : X} (hx₀A : A.rank x₀ = a) (hx₀D : D.rank x₀ = d)
    (hxA : A.rank x = a) (hxD : D.rank x = d) (v : (whitneySum A D).Fiber x) :
    (trivializationAt (Fin (a + d) → 𝕜) ((whitneySum A D).charts (a + d)).Fiber
      ⟨x₀, congrArg₂ (· + ·) hx₀A hx₀D⟩
      ⟨⟨x, congrArg₂ (· + ·) hxA hxD⟩,
        fun i => v (Fin.cast (congrArg₂ (· + ·) hxA hxD).symm i)⟩).2 =
      (splitCoords (𝕜 := 𝕜) a d).symm
        ((trivializationAt (Fin a → 𝕜) (A.charts a).Fiber ⟨x₀, hx₀A⟩
          ⟨⟨x, hxA⟩, fun i => (whitneySumFiberEquiv A D x v).1 (Fin.cast hxA.symm i)⟩).2,
         (trivializationAt (Fin d → 𝕜) (D.charts d).Fiber ⟨x₀, hx₀D⟩
          ⟨⟨x, hxD⟩, fun i => (whitneySumFiberEquiv A D x v).2 (Fin.cast hxD.symm i)⟩).2) := by
  rw [(whitneySum A D).trivializationAt_charts, A.trivializationAt_charts,
    D.trivializationAt_charts]
  simp only [VectorBundleCore.localTriv_apply, (whitneySum A D).indexAt_eq,
    A.indexAt_eq, D.indexAt_eq]
  rw [whitneySum_coordChange_eq A D ⟨x, congrArg₂ (· + ·) hxA hxD⟩
    ⟨x₀, congrArg₂ (· + ·) hx₀A hx₀D⟩ ⟨x, congrArg₂ (· + ·) hxA hxD⟩ rfl
    hxA hx₀A hxA hxD hx₀D hxD]
  exact (whitneyCoordChangeAux_rfl_apply A D x x₀ x hxA hx₀A hxA hxD hx₀D hxD _).trans
    (congrArg (splitCoords (𝕜 := 𝕜) a d).symm <| Prod.ext
      (congrArg ((A.charts a).coordChange ⟨x, hxA⟩ ⟨x₀, hx₀A⟩ ⟨x, hxA⟩)
        (congrArg Prod.fst (splitCoords_cast hxA hxD v)))
      (congrArg ((D.charts d).coordChange ⟨x, hxD⟩ ⟨x₀, hx₀D⟩ ⟨x, hxD⟩)
        (congrArg Prod.snd (splitCoords_cast hxA hxD v))))

private theorem continuous_mk_whitneySum_jointStratum_iff {Y : Type*} [TopologicalSpace Y]
    (A D : FiniteRankAtlas 𝕜 X) {b : Y → X} (hb : Continuous b)
    (s : ∀ y, (whitneySum A D).Fiber (b y)) (a d : ℕ) :
    Continuous (fun y : {y : Y // A.rank (b y) = a ∧ D.rank (b y) = d} =>
        (⟨b y.1, s y.1⟩ : TotalSpace Unit (whitneySum A D).Fiber)) ↔
      Continuous (fun y : {y : Y // A.rank (b y) = a ∧ D.rank (b y) = d} =>
        (⟨b y.1, (whitneySumFiberEquiv A D (b y.1) (s y.1)).1⟩ : TotalSpace Unit A.Fiber)) ∧
      Continuous (fun y : {y : Y // A.rank (b y) = a ∧ D.rank (b y) = d} =>
        (⟨b y.1, (whitneySumFiberEquiv A D (b y.1) (s y.1)).2⟩ : TotalSpace Unit D.Fiber)) := by
  let Y' := {y : Y // A.rank (b y) = a ∧ D.rank (b y) = d}
  rw [continuous_mk_iff_of_rank_eq (whitneySum A D) (fun y : Y' => congrArg₂ (· + ·) y.2.1 y.2.2),
    continuous_mk_iff_of_rank_eq A (fun y : Y' => y.2.1),
    continuous_mk_iff_of_rank_eq D (fun y : Y' => y.2.2),
    continuous_iff_continuousAt, continuous_iff_continuousAt, continuous_iff_continuousAt,
    ← forall_and]
  refine forall_congr' fun y₀ => ?_
  rw [FiberBundle.continuousAt_totalSpace, FiberBundle.continuousAt_totalSpace,
    FiberBundle.continuousAt_totalSpace]
  have hbA : ContinuousAt (fun y : Y' => (⟨b y.1, y.2.1⟩ : {x : X // A.rank x = a})) y₀ :=
    ((hb.comp continuous_subtype_val).subtype_mk fun y => y.2.1).continuousAt
  have hbD : ContinuousAt (fun y : Y' => (⟨b y.1, y.2.2⟩ : {x : X // D.rank x = d})) y₀ :=
    ((hb.comp continuous_subtype_val).subtype_mk fun y => y.2.2).continuousAt
  have hbAD : ContinuousAt (fun y : Y' =>
      (⟨b y.1, congrArg₂ (· + ·) y.2.1 y.2.2⟩ : {x : X // (whitneySum A D).rank x = a + d})) y₀ :=
    ((hb.comp continuous_subtype_val).subtype_mk fun y =>
      congrArg₂ (· + ·) y.2.1 y.2.2).continuousAt
  simp only [hbA, hbD, hbAD, true_and]
  have hfun : (fun y : Y' => (trivializationAt (Fin (a + d) → 𝕜)
        ((whitneySum A D).charts (a + d)).Fiber ⟨b y₀.1, congrArg₂ (· + ·) y₀.2.1 y₀.2.2⟩
        ⟨⟨b y.1, congrArg₂ (· + ·) y.2.1 y.2.2⟩,
          fun i => s y.1 (Fin.cast (congrArg₂ (· + ·) y.2.1 y.2.2).symm i)⟩).2) =
      (splitCoords (𝕜 := 𝕜) a d).symm.toHomeomorph ∘ (fun y : Y' =>
        ((trivializationAt (Fin a → 𝕜) (A.charts a).Fiber ⟨b y₀.1, y₀.2.1⟩
          ⟨⟨b y.1, y.2.1⟩, fun i => (whitneySumFiberEquiv A D (b y.1) (s y.1)).1
            (Fin.cast y.2.1.symm i)⟩).2,
         (trivializationAt (Fin d → 𝕜) (D.charts d).Fiber ⟨b y₀.1, y₀.2.2⟩
          ⟨⟨b y.1, y.2.2⟩, fun i => (whitneySumFiberEquiv A D (b y.1) (s y.1)).2
            (Fin.cast y.2.2.symm i)⟩).2)) :=
    funext fun y => trivializationAt_whitneySum_snd A D y₀.2.1 y₀.2.2 y.2.1 y.2.2 (s y.1)
  rw [hfun]
  exact (splitCoords (𝕜 := 𝕜) a d).symm.toHomeomorph.isEmbedding.continuousAt_iff.symm.trans
    ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

/-- A map into the total space of a Whitney sum is continuous precisely when its two
coordinate-block projections into the summand total spaces are continuous. -/
theorem continuous_mk_whitneySum_iff {Y : Type*} [TopologicalSpace Y]
    {A D : FiniteRankAtlas 𝕜 X} {b : Y → X} (s : ∀ y, (whitneySum A D).Fiber (b y)) :
    Continuous (fun y => (⟨b y, s y⟩ : TotalSpace Unit (whitneySum A D).Fiber)) ↔
      Continuous (fun y =>
        (⟨b y, (whitneySumFiberEquiv A D (b y) (s y)).1⟩ : TotalSpace Unit A.Fiber)) ∧
      Continuous (fun y =>
        (⟨b y, (whitneySumFiberEquiv A D (b y) (s y)).2⟩ : TotalSpace Unit D.Fiber)) := by
  constructor
  · intro hs
    have hb : Continuous b := (whitneySum A D).continuous_proj.comp hs
    rw [continuous_iff_jointStrata hb A D] at hs
    exact ⟨(continuous_iff_jointStrata hb A D _).2 fun a d =>
        ((continuous_mk_whitneySum_jointStratum_iff A D hb s a d).1 (hs a d)).1,
      (continuous_iff_jointStrata hb A D _).2 fun a d =>
        ((continuous_mk_whitneySum_jointStratum_iff A D hb s a d).1 (hs a d)).2⟩
  · rintro ⟨hsA, hsD⟩
    have hb : Continuous b := A.continuous_proj.comp hsA
    rw [continuous_iff_jointStrata hb A D] at hsA hsD ⊢
    intro a d
    exact (continuous_mk_whitneySum_jointStratum_iff A D hb s a d).2 ⟨hsA a d, hsD a d⟩

/-- The reconstructed total space of a Whitney sum is homeomorphic to the fibre product of
the summand total spaces over `X`, acting by `whitneySumFiberEquiv` on every fibre. -/
def whitneySumTotalSpaceHomeomorph (A D : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit (whitneySum A D).Fiber ≃ₜ
      {p : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // p.1.proj = p.2.proj} where
  toFun p :=
    ⟨(⟨p.proj, (whitneySumFiberEquiv A D p.proj p.2).1⟩,
      ⟨p.proj, (whitneySumFiberEquiv A D p.proj p.2).2⟩), rfl⟩
  invFun p :=
    ⟨p.1.1.proj, (whitneySumFiberEquiv A D p.1.1.proj).symm
      (p.1.1.2, fun i => p.1.2.2 (Fin.cast (congrArg D.rank p.2) i))⟩
  left_inv p := by
    cases p with
    | mk x v =>
      simp only [Fin.cast_refl, id_eq, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  right_inv p := by
    rcases p with ⟨⟨⟨x, u⟩, ⟨y, w⟩⟩, h⟩
    cases h
    simp only [Fin.cast_refl, id_eq, ContinuousLinearEquiv.apply_symm_apply]
  continuous_toFun := by
    have h := (continuous_mk_whitneySum_iff
      (b := TotalSpace.proj) (s := fun p : TotalSpace Unit (whitneySum A D).Fiber => p.2)).1
      continuous_id
    exact (h.1.prodMk h.2).subtype_mk _
  continuous_invFun := by
    apply (continuous_mk_whitneySum_iff (A := A) (D := D)
      (b := fun p : {p : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber //
        p.1.proj = p.2.proj} => p.1.1.proj) _).2
    refine ⟨?_, ?_⟩
    · refine (continuous_fst.comp continuous_subtype_val).congr ?_
      rintro ⟨⟨⟨x, u⟩, ⟨y, w⟩⟩, h⟩
      cases h
      simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    · refine (continuous_snd.comp continuous_subtype_val).congr ?_
      rintro ⟨⟨⟨x, u⟩, ⟨y, w⟩⟩, h⟩
      cases h
      simp only [Function.comp_apply, Fin.cast_refl, id_eq, ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem whitneySumTotalSpaceHomeomorph_apply (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    whitneySumTotalSpaceHomeomorph A D p =
      ⟨(⟨p.proj, (whitneySumFiberEquiv A D p.proj p.2).1⟩,
        ⟨p.proj, (whitneySumFiberEquiv A D p.proj p.2).2⟩), rfl⟩ := (rfl)

@[simp] theorem whitneySumTotalSpaceHomeomorph_symm_apply_mk (A D : FiniteRankAtlas 𝕜 X)
    (x : X) (u : A.Fiber x) (w : D.Fiber x) :
    (whitneySumTotalSpaceHomeomorph A D).symm ⟨(⟨x, u⟩, ⟨x, w⟩), rfl⟩ =
      ⟨x, (whitneySumFiberEquiv A D x).symm (u, w)⟩ := (rfl)

end WhitneySum

section Biproduct

/-- Projection of the Whitney sum onto its first summand. -/
def whitneyFst (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ A where
  fiberMap x := (LinearMap.fst 𝕜 (A.Fiber x) (D.Fiber x)).comp
    (whitneySumFiberEquiv A D x).toLinearEquiv.toLinearMap
  continuous_totalSpaceMap :=
    ((continuous_mk_whitneySum_iff
      (b := TotalSpace.proj) (s := fun p : TotalSpace Unit (whitneySum A D).Fiber => p.2)).1
      continuous_id).1

/-- Projection of the Whitney sum onto its second summand. -/
def whitneySnd (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ D where
  fiberMap x := (LinearMap.snd 𝕜 (A.Fiber x) (D.Fiber x)).comp
    (whitneySumFiberEquiv A D x).toLinearEquiv.toLinearMap
  continuous_totalSpaceMap :=
    ((continuous_mk_whitneySum_iff
      (b := TotalSpace.proj) (s := fun p : TotalSpace Unit (whitneySum A D).Fiber => p.2)).1
      continuous_id).2

/-- Inclusion of the first summand into the Whitney sum. -/
def whitneyInl (A D : FiniteRankAtlas 𝕜 X) : A ⟶ whitneySum A D where
  fiberMap x := (whitneySumFiberEquiv A D x).symm.toLinearEquiv.toLinearMap.comp
    (LinearMap.inl 𝕜 (A.Fiber x) (D.Fiber x))
  continuous_totalSpaceMap := by
    apply (continuous_mk_whitneySum_iff (A := A) (D := D)
      (b := TotalSpace.proj) _).2
    refine ⟨?_, ?_⟩
    · refine continuous_id.congr fun p => ?_
      cases p
      simp only [id_eq, LinearMap.comp_apply, LinearMap.inl_apply,
        LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
        ContinuousLinearEquiv.apply_symm_apply]
    · refine (D.continuous_zeroSection.comp A.continuous_proj).congr fun p => ?_
      cases p
      simp only [Function.comp_apply, LinearMap.comp_apply, LinearMap.inl_apply,
        LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
        ContinuousLinearEquiv.apply_symm_apply]

/-- Inclusion of the second summand into the Whitney sum. -/
def whitneyInr (A D : FiniteRankAtlas 𝕜 X) : D ⟶ whitneySum A D where
  fiberMap x := (whitneySumFiberEquiv A D x).symm.toLinearEquiv.toLinearMap.comp
    (LinearMap.inr 𝕜 (A.Fiber x) (D.Fiber x))
  continuous_totalSpaceMap := by
    apply (continuous_mk_whitneySum_iff (A := A) (D := D)
      (b := TotalSpace.proj) _).2
    refine ⟨?_, ?_⟩
    · refine (A.continuous_zeroSection.comp D.continuous_proj).congr fun p => ?_
      cases p
      simp only [Function.comp_apply, LinearMap.comp_apply, LinearMap.inr_apply,
        LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
        ContinuousLinearEquiv.apply_symm_apply]
    · refine continuous_id.congr fun p => ?_
      cases p
      simp only [id_eq, LinearMap.comp_apply, LinearMap.inr_apply,
        LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
        ContinuousLinearEquiv.apply_symm_apply]

/-- The first projection extracts the first coordinate block on every fibre. -/
@[simp] theorem fiberMap_whitneyFst (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyFst A D).fiberMap x =
      (LinearMap.fst 𝕜 (A.Fiber x) (D.Fiber x)).comp
        (whitneySumFiberEquiv A D x).toLinearEquiv.toLinearMap := (rfl)

/-- The second projection extracts the second coordinate block on every fibre. -/
@[simp] theorem fiberMap_whitneySnd (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneySnd A D).fiberMap x =
      (LinearMap.snd 𝕜 (A.Fiber x) (D.Fiber x)).comp
        (whitneySumFiberEquiv A D x).toLinearEquiv.toLinearMap := (rfl)

/-- The first inclusion appends a zero block on every fibre. -/
@[simp] theorem fiberMap_whitneyInl (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyInl A D).fiberMap x =
      (whitneySumFiberEquiv A D x).symm.toLinearEquiv.toLinearMap.comp
        (LinearMap.inl 𝕜 (A.Fiber x) (D.Fiber x)) := (rfl)

/-- The second inclusion prepends a zero block on every fibre. -/
@[simp] theorem fiberMap_whitneyInr (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyInr A D).fiberMap x =
      (whitneySumFiberEquiv A D x).symm.toLinearEquiv.toLinearMap.comp
        (LinearMap.inr 𝕜 (A.Fiber x) (D.Fiber x)) := (rfl)

@[reassoc (attr := simp)] theorem whitneyInl_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneyFst A D = 𝟙 A := by
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro v
  simp

@[reassoc (attr := simp)] theorem whitneyInl_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneySnd A D = 0 := by
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro v
  simp

@[reassoc (attr := simp)] theorem whitneyInr_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneyFst A D = 0 := by
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro v
  simp

@[reassoc (attr := simp)] theorem whitneyInr_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneySnd A D = 𝟙 D := by
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro v
  simp

/-- The Whitney sum with its four canonical bundle morphisms. -/
-- Expose the point projection so the bicone legs reduce to the Whitney sum.
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

/-- The two coordinate-block projections and inclusions resolve the identity. -/
@[simp] theorem whitney_total (A D : FiniteRankAtlas 𝕜 X) :
    whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D =
      𝟙 (whitneySum A D) := by
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro v
  simp [← map_add]

/-- The geometric Whitney sum is simultaneously a product and a coproduct. -/
def whitneyBiconeIsBilimit (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).IsBilimit :=
  isBinaryBilimitOfTotal _ (whitney_total A D)

/-- Whitney sums provide binary biproducts of variable-rank bundle atlases. -/
instance : HasBinaryBiproducts (FiniteRankAtlas 𝕜 X) where
  has_binary_biproduct A D := ⟨⟨whitneyBicone A D, whitneyBiconeIsBilimit A D⟩⟩

/-- Variable-rank bundle atlases admit all finite biproducts. -/
instance : HasFiniteBiproducts (FiniteRankAtlas 𝕜 X) :=
  hasFiniteBiproducts_of_hasBinaryBiproducts

/-- The canonical isomorphism between the concrete Whitney sum and the categorical binary
biproduct `A ⊞ D`. -/
noncomputable def whitneySumIsoBiprod (A D : FiniteRankAtlas 𝕜 X) :
    whitneySum A D ≅ A ⊞ D :=
  biprod.uniqueUpToIso A D (whitneyBiconeIsBilimit A D)

@[simp] theorem whitneySumIsoBiprod_hom (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySumIsoBiprod A D).hom = biprod.lift (whitneyFst A D) (whitneySnd A D) := by
  simp [whitneySumIsoBiprod]
  rfl

@[simp] theorem whitneySumIsoBiprod_inv (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySumIsoBiprod A D).inv = biprod.desc (whitneyInl A D) (whitneyInr A D) := by
  simp [whitneySumIsoBiprod]
  rfl

/-- The rank of a binary biproduct is the sum of the summand ranks. -/
@[simp] theorem rank_biprod (A D : FiniteRankAtlas 𝕜 X) :
    (A ⊞ D).rank = A.rank + D.rank :=
  (whitneySumIsoBiprod A D).finiteRankAtlas_rank_eq.symm

end Biproduct

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

/-- Morphisms into a Whitney sum are determined by their two projections. -/
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

@[simp]
theorem fiberMap_whitneyLift (f : E ⟶ A) (g : E ⟶ D) (x : X) :
    (whitneyLift f g).fiberMap x =
      (whitneySumFiberEquiv A D x).symm.toLinearEquiv.toLinearMap.comp
        ((f.fiberMap x).prod (g.fiberMap x)) := by
  apply LinearMap.ext
  intro v
  simp [whitneyLift, ← map_add]

theorem whitneySumFiberEquiv_fiberMap_whitneyLift (f : E ⟶ A) (g : E ⟶ D) (x : X)
    (v : E.Fiber x) :
    whitneySumFiberEquiv A D x ((whitneyLift f g).fiberMap x v) =
      (f.fiberMap x v, g.fiberMap x v) := by
  simp

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

/-- Every morphism out of a Whitney sum is the copairing of its two restrictions. -/
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

@[simp]
theorem fiberMap_whitneyDesc (f : A ⟶ E) (g : D ⟶ E) (x : X) :
    (whitneyDesc f g).fiberMap x =
      ((f.fiberMap x).coprod (g.fiberMap x)).comp
        (whitneySumFiberEquiv A D x).toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro v
  rfl

theorem fiberMap_whitneyDesc_apply (f : A ⟶ E) (g : D ⟶ E) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneyDesc f g).fiberMap x v =
      f.fiberMap x (whitneySumFiberEquiv A D x v).1 +
        g.fiberMap x (whitneySumFiberEquiv A D x v).2 := by
  simp [fiberMap_whitneyDesc]

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

@[simp]
theorem fiberMap_whitneyMap (f : A ⟶ A') (g : D ⟶ D') (x : X) :
    (whitneyMap f g).fiberMap x =
      (whitneySumFiberEquiv A' D' x).symm.toLinearEquiv.toLinearMap.comp
        (((f.fiberMap x).prodMap (g.fiberMap x)).comp
          (whitneySumFiberEquiv A D x).toLinearEquiv.toLinearMap) := by
  apply LinearMap.ext
  intro v
  simp [whitneyMap]

theorem whitneySumFiberEquiv_fiberMap_whitneyMap (f : A ⟶ A') (g : D ⟶ D') (x : X)
    (v : (whitneySum A D).Fiber x) :
    whitneySumFiberEquiv A' D' x ((whitneyMap f g).fiberMap x v) =
      (f.fiberMap x (whitneySumFiberEquiv A D x v).1,
        g.fiberMap x (whitneySumFiberEquiv A D x v).2) := by
  simp

/-- `whitneySumTotalSpaceHomeomorph` intertwines `whitneyMap f g` with the componentwise
action of `f` and `g` on the fibre product of the total spaces. -/
theorem whitneySumTotalSpaceHomeomorph_naturality (f : A ⟶ A') (g : D ⟶ D')
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    whitneySumTotalSpaceHomeomorph A' D' ((whitneyMap f g).totalSpaceMap p) =
      ⟨(f.totalSpaceMap (whitneySumTotalSpaceHomeomorph A D p).1.1,
        g.totalSpaceMap (whitneySumTotalSpaceHomeomorph A D p).1.2), by simp⟩ := by
  cases p with
  | mk x v =>
    apply Subtype.ext
    simp

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
    whitneySum (trivial 𝕜 0) A ≅ A where
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
    (g : trivial 𝕜 0 ⟶ trivial 𝕜 0) (f : A ⟶ A') :
    whitneyMap g f ≫ (whitneyZeroLeftIso A').hom = (whitneyZeroLeftIso A).hom ≫ f := by
  simp only [whitneyZeroLeftIso_hom, whitneyMap_snd]

/-- Right unit isomorphism for Whitney sum with the trivial rank-zero atlas. -/
def whitneyZeroRightIso (A : FiniteRankAtlas 𝕜 X) :
    whitneySum A (trivial 𝕜 0) ≅ A where
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
    (f : A ⟶ A') (g : trivial 𝕜 0 ⟶ trivial 𝕜 0) :
    whitneyMap f g ≫ (whitneyZeroRightIso A').hom = (whitneyZeroRightIso A).hom ≫ f := by
  simp only [whitneyZeroRightIso_hom, whitneyMap_fst]

private theorem whitneySum_trivial_coordChange_eq_id (r₁ r₂ : LocallyConstant X ℕ) (n : ℕ)
    (i j x : {x : X // (whitneySum (trivial 𝕜 r₁) (trivial 𝕜 r₂)).rank x = n})
    (hx : x ∈ ((whitneySum (trivial 𝕜 r₁) (trivial 𝕜 r₂)).charts n).baseSet i ∩
      ((whitneySum (trivial 𝕜 r₁) (trivial 𝕜 r₂)).charts n).baseSet j) (v : Fin n → 𝕜) :
    ((whitneySum (trivial 𝕜 r₁) (trivial 𝕜 r₂)).charts n).coordChange i j x v = v := by
  rcases hx with ⟨⟨hAi, hDi, _⟩, ⟨hAj, hDj, _⟩⟩
  rw [whitneySum_coordChange_eq (trivial 𝕜 r₁) (trivial 𝕜 r₂) i j x i.2
    rfl (hAj.symm.trans hAi) hAi rfl (hDj.symm.trans hDi) hDi]
  exact (splitCoordsCongr (𝕜 := 𝕜) i.2).symm_apply_apply v

/-- The Whitney sum of two trivial variable-rank atlases is canonically isomorphic to the
trivial atlas of the sum of their ranks, via the identity on every coordinate fibre. -/
def whitneyTrivialIso (r₁ r₂ : LocallyConstant X ℕ) :
    whitneySum (trivial 𝕜 r₁) (trivial 𝕜 r₂) ≅ trivial 𝕜 (r₁ + r₂) :=
  let eW := (whitneySum (trivial 𝕜 r₁) (trivial 𝕜 r₂)).totalSpaceHomeomorphOfCoordChangeEqId
    (whitneySum_trivial_coordChange_eq_id r₁ r₂)
  let eT := trivialTotalSpaceHomeomorph 𝕜 (r₁ + r₂)
  isoMk (fun _ => LinearEquiv.refl 𝕜 _)
    ((eW.trans eT.symm).continuous.congr fun ⟨x, v⟩ => by
      change eT.symm (eW ⟨x, v⟩) = ⟨x, v⟩
      rw [totalSpaceHomeomorphOfCoordChangeEqId_apply]
      exact trivialTotalSpaceHomeomorph_symm_apply 𝕜 (r₁ + r₂) ((r₁ + r₂) x) ⟨x, rfl⟩ v)
    ((eT.trans eW.symm).continuous.congr fun ⟨x, v⟩ => by
      change eW.symm (eT ⟨x, v⟩) = ⟨x, v⟩
      rw [trivialTotalSpaceHomeomorph_apply]
      exact totalSpaceHomeomorphOfCoordChangeEqId_symm_apply _ _ ((r₁ + r₂) x) ⟨x, rfl⟩ v)

@[simp]
theorem fiberMap_whitneyTrivialIso_hom (r₁ r₂ : LocallyConstant X ℕ) (x : X) :
    (whitneyTrivialIso (𝕜 := 𝕜) r₁ r₂).hom.fiberMap x = LinearMap.id :=
  fiberMap_isoMk_hom _ _ _ x

@[simp]
theorem fiberMap_whitneyTrivialIso_inv (r₁ r₂ : LocallyConstant X ℕ) (x : X) :
    (whitneyTrivialIso (𝕜 := 𝕜) r₁ r₂).inv.fiberMap x = LinearMap.id :=
  fiberMap_isoMk_inv _ _ _ x

end Coherence

end TauCeti.FiniteRankAtlas
