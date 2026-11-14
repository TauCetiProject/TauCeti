/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Trivial
public import TauCeti.Topology.Algebra.Module.Equiv.Fin
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import TauCeti.Topology.VectorBundle.Core.Congr
import TauCeti.Topology.VectorBundle.Core.LocallyConstant
import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Whitney-sum binary and finite biproducts of variable-rank bundle atlases

This file constructs the Whitney sum of variable-rank bundle atlases and equips
`TauCeti.FiniteRankAtlas 𝕜 X` with binary and finite biproducts over an arbitrary topological space
`X` and nontrivially normed scalar field `𝕜`. Neither compactness nor separation of `X`, nor
completeness of `𝕜`, nor boundedness of the locally constant ranks is assumed.

For two variable-rank atlases `A` and `D`, the sum `A.rank + D.rank` is locally constant, while on a
single stratum `B_n := {x : X // (A.rank + D.rank) x = n}` the individual summand ranks
`(A.rank x, D.rank x)` may still vary across clopen components. Because the rank-splitting map
`B_n → {pq : ℕ × ℕ // pq.1 + pq.2 = n}` is locally constant, pulling back the stratum cores of `A`
and `D` to each clopen fibre, forming `FiniteRankBundleCore.whitneySum`, transporting the model
`Fin (p + q) → 𝕜` along `finCongr`, and gluing via
`IsLocallyConstant.pointIndexedVectorBundleCore` yields the point-indexed variable-rank Whitney sum
`FiniteRankAtlas.whitneySum A D`.

`FiniteRankAtlas.continuous_mk_whitneySum_iff` proves that a map into the reconstructed total space
of `whitneySum A D` is continuous if and only if its two coordinate blocks under
`TauCeti.splitCoords` define continuous maps into the reconstructed total spaces of `A` and `D`.
From this criterion we obtain:
* the canonical projections and inclusions `whitneyFst`, `whitneySnd`, `whitneyInl`, `whitneyInr`,
  the bicone `whitneyBicone`, its bilimit witness `whitneyBiconeIsBilimit`, and the instances
  `HasBinaryBiproducts (FiniteRankAtlas 𝕜 X)` and `HasFiniteBiproducts (FiniteRankAtlas 𝕜 X)`,
  together with rank additivity `rank_biprod` and `rank_biproduct`;
* concrete pairing, copairing, functoriality, symmetry, associativity, unit, and trivial-atlas sum
  isomorphisms (`whitneyLift`, `whitneyDesc`, `whitneyMap`, `whitneyMapIso`, `whitneyCommIso`,
  `whitneyAssocIso`, `whitneyZeroLeftIso`, `whitneyZeroRightIso`, `trivialAddIso`);
* the global homeomorphism `whitneySumFiberedProdHomeomorph` identifying the reconstructed total
  space of `whitneySum A D` with the topological fibered product of the total spaces of `A` and `D`
  over `X`.

## References

* M. F. Atiyah, *K-Theory*, W. A. Benjamin (1967), §1.1–1.2.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, 3rd ed., Springer GTM 20 (1994), Chapter 3.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits Set Topology

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

section WhitneySum

/-- On the rank-`n` stratum of `A.rank + D.rank`, record the pair of individual summand ranks. -/
private def rankSplit (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (x : {x : X // (A.rank + D.rank) x = n}) :
    {pq : ℕ × ℕ // pq.1 + pq.2 = n} :=
  ⟨(A.rank x.1, D.rank x.1), x.2⟩

private theorem isLocallyConstant_rankSplit (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    IsLocallyConstant (rankSplit A D n) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  filter_upwards [((A.rank.isLocallyConstant.comp_continuous continuous_subtype_val).prodMk
    (D.rank.isLocallyConstant.comp_continuous continuous_subtype_val)).eventually_eq x] with y hy
  exact Subtype.ext hy

private def rankInclusionLeft (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    C({x : {x : X // (A.rank + D.rank) x = n} // rankSplit A D n x = pq},
      {z : X // A.rank z = pq.1.1}) :=
  ⟨fun x => ⟨x.1.1, congrArg (fun u : {pq : ℕ × ℕ // pq.1 + pq.2 = n} => u.1.1) x.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

private def rankInclusionRight (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    C({x : {x : X // (A.rank + D.rank) x = n} // rankSplit A D n x = pq},
      {z : X // D.rank z = pq.1.2}) :=
  ⟨fun x => ⟨x.1.1, congrArg (fun u : {pq : ℕ × ℕ // pq.1 + pq.2 = n} => u.1.2) x.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

/-- On each clopen `(p, q)`-piece of the rank-`n` stratum, form the constant-rank Whitney sum of
the pulled-back stratum cores of `A` and `D`. -/
private def whitneyPieceCore (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    FiniteRankBundleCore 𝕜
      {x : {x : X // (A.rank + D.rank) x = n} // rankSplit A D n x = pq} :=
  FiniteRankBundleCore.whitneySum
    ((A.stratumCore pq.1.1).pullback (rankInclusionLeft A D n pq))
    ((D.stratumCore pq.1.2).pullback (rankInclusionRight A D n pq))

/-- Glue the model-transported constant-rank Whitney sums across the clopen fibres of `rankSplit`
to obtain a point-indexed `VectorBundleCore` on `{x : X // (A.rank + D.rank) x = n}`. -/
noncomputable def whitneyStratumCore (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    VectorBundleCore 𝕜 {x : X // (A.rank + D.rank) x = n} (Fin n → 𝕜)
      {x : X // (A.rank + D.rank) x = n} :=
  (isLocallyConstant_rankSplit A D n).pointIndexedVectorBundleCore fun pq =>
    (whitneyPieceCore A D n pq).core.congrModel
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜) (finCongr pq.2))

/-- Every point of the rank-`n` stratum of `A.rank + D.rank` is its own preferred chart index in
`whitneyStratumCore`. -/
@[simp]
theorem indexAt_whitneyStratumCore (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (x : {x : X // (A.rank + D.rank) x = n}) :
    (whitneyStratumCore A D n).indexAt x = x :=
  (isLocallyConstant_rankSplit A D n).indexAt_pointIndexedVectorBundleCore _
    (fun pq y =>
      ((whitneyPieceCore A D n pq).core.indexAt_congrModel _ y).trans
        ((whitneyPieceCore A D n pq).indexAt_eq y)) x

/-- The Whitney sum of two variable-rank bundle atlases, with locally constant rank
`A.rank + D.rank` and concatenated coordinate fibres `Fin (A.rank x + D.rank x) → 𝕜`. -/
-- Expose the rank projection so `(whitneySum A D).Fiber x` reduces to
-- `Fin (A.rank x + D.rank x) → 𝕜`, while keeping the glued stratum cores inside
-- `whitneyStratumCore`.
@[expose]
noncomputable def whitneySum (A D : FiniteRankAtlas 𝕜 X) : FiniteRankAtlas 𝕜 X where
  rank := A.rank + D.rank
  charts := whitneyStratumCore A D
  indexAt_eq := indexAt_whitneyStratumCore A D

@[simp]
theorem rank_whitneySum (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySum A D).rank = A.rank + D.rank := (rfl)

@[simp]
theorem charts_whitneySum (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (whitneySum A D).charts n = whitneyStratumCore A D n := (rfl)

private theorem continuous_whitneyPieceCore_iff {Z : Type*} [TopologicalSpace Z]
    (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    {g : Z → {x : {x : X // (A.rank + D.rank) x = n} // rankSplit A D n x = pq}}
    (hg : Continuous g) (t : Z → Fin n → 𝕜) :
    Continuous (fun z =>
        (⟨g z, t z⟩ :
          ((whitneyPieceCore A D n pq).core.congrModel
            (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜)
              (finCongr pq.2))).TotalSpace)) ↔
      Continuous (fun z =>
        (⟨rankInclusionLeft A D n pq (g z),
          (splitCoords (𝕜 := 𝕜) pq.1.1 pq.1.2
            ((ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜)
              (finCongr pq.2)).symm (t z))).1⟩ :
          (A.charts pq.1.1).TotalSpace)) ∧
      Continuous (fun z =>
        (⟨rankInclusionRight A D n pq (g z),
          (splitCoords (𝕜 := 𝕜) pq.1.1 pq.1.2
            ((ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜)
              (finCongr pq.2)).symm (t z))).2⟩ :
          (D.charts pq.1.2).TotalSpace)) := by
  refine (VectorBundleCore.continuous_mk_congrModel_iff _ _).trans ?_
  refine (FiniteRankBundleCore.continuous_mk_whitneySum_iff
    ((A.stratumCore pq.1.1).pullback (rankInclusionLeft A D n pq))
    ((D.stratumCore pq.1.2).pullback (rankInclusionRight A D n pq))).trans ?_
  exact and_congr
    (((A.stratumCore pq.1.1).continuous_mk_pullback_iff
      (rankInclusionLeft A D n pq)).trans (and_iff_right hg))
    (((D.stratumCore pq.1.2).continuous_mk_pullback_iff
      (rankInclusionRight A D n pq)).trans (and_iff_right hg))

private theorem splitCoords_cast_fst {n p q a d : ℕ}
    (hp : a = p) (hq : d = q) (hn : a + d = n) (hpq : p + q = n)
    (v : Fin (a + d) → 𝕜) (i : Fin p) :
    (splitCoords (𝕜 := 𝕜) p q (fun k : Fin (p + q) => v (Fin.cast (hpq.trans hn.symm) k))).1 i =
      (splitCoords (𝕜 := 𝕜) a d v).1 (Fin.cast hp.symm i) := by
  subst hp hq hn
  rfl

private theorem splitCoords_cast_snd {n p q a d : ℕ}
    (hp : a = p) (hq : d = q) (hn : a + d = n) (hpq : p + q = n)
    (v : Fin (a + d) → 𝕜) (j : Fin q) :
    (splitCoords (𝕜 := 𝕜) p q (fun k : Fin (p + q) => v (Fin.cast (hpq.trans hn.symm) k))).2 j =
      (splitCoords (𝕜 := 𝕜) a d v).2 (Fin.cast hq.symm j) := by
  subst hp hq hn
  rfl

private theorem continuous_blocks_of_continuous_whitneySum {Y : Type*} [TopologicalSpace Y]
    {A D : FiniteRankAtlas 𝕜 X} {b : Y → X} {s : ∀ y, (whitneySum A D).Fiber (b y)}
    (hs : Continuous fun y => (⟨b y, s y⟩ : TotalSpace Unit (whitneySum A D).Fiber)) :
    Continuous (fun y =>
      (⟨b y, (splitCoords (𝕜 := 𝕜) (A.rank (b y)) (D.rank (b y)) (s y)).1⟩ :
        TotalSpace Unit A.Fiber)) ∧
    Continuous (fun y =>
      (⟨b y, (splitCoords (𝕜 := 𝕜) (A.rank (b y)) (D.rank (b y)) (s y)).2⟩ :
        TotalSpace Unit D.Fiber)) := by
  have hb : Continuous b := (whitneySum A D).continuous_proj.comp hs
  have hstrata := ((whitneySum A D).continuous_mk_iff_rankStrata hb s).1 hs
  let s₁ (y : Y) : A.Fiber (b y) :=
    (splitCoords (𝕜 := 𝕜) (A.rank (b y)) (D.rank (b y)) (s y)).1
  let s₂ (y : Y) : D.Fiber (b y) :=
    (splitCoords (𝕜 := 𝕜) (A.rank (b y)) (D.rank (b y)) (s y)).2
  have hpiece (p q : ℕ) := (continuous_whitneyPieceCore_iff A D (p + q) ⟨(p, q), rfl⟩
    ((((hb.comp continuous_subtype_val).comp continuous_subtype_val).subtype_mk _).subtype_mk _)
    (fun y => fun i : Fin (p + q) => s y.1.1 (Fin.cast y.1.2.symm i))).1 <|
      ((isLocallyConstant_rankSplit A D (p + q)).continuous_mk_pointIndexedVectorBundleCore_iff
        _ ((hb.comp continuous_subtype_val).subtype_mk _) _).1 (hstrata (p + q)) ⟨(p, q), rfl⟩
  refine ⟨(A.continuous_mk_iff_rankStrata hb s₁).2 fun p => ?_,
    (D.continuous_mk_iff_rankStrata hb s₂).2 fun q => ?_⟩
  · apply continuous_of_cover_nhds
      (s := fun q : ℕ => {z : {y : Y // A.rank (b y) = p} | D.rank (b z.1) = q})
    · exact fun z => ⟨D.rank (b z.1),
        ((D.rank.isLocallyConstant.isOpen_fiber _).preimage
          (hb.comp continuous_subtype_val)).mem_nhds rfl⟩
    · intro q
      rw [continuousOn_iff_continuous_domRestrict]
      let g : {z : {y : Y // A.rank (b y) = p} // D.rank (b z.1) = q} →
          {y : {y : Y // (A.rank + D.rank) (b y) = p + q} //
            rankSplit A D (p + q) ⟨b y.1, y.2⟩ = ⟨(p, q), rfl⟩} :=
        fun z => ⟨⟨z.1.1, congrArg₂ (· + ·) z.1.2 z.2⟩, Subtype.ext (Prod.ext z.1.2 z.2)⟩
      have hg : Continuous g :=
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
      refine ((hpiece p q).1.comp hg).congr fun z => TotalSpace.mk_inj.mpr (funext fun i => ?_)
      exact splitCoords_cast_fst z.1.2 z.2 (g z).1.2 rfl (s z.1.1) i
  · apply continuous_of_cover_nhds
      (s := fun p : ℕ => {z : {y : Y // D.rank (b y) = q} | A.rank (b z.1) = p})
    · exact fun z => ⟨A.rank (b z.1),
        ((A.rank.isLocallyConstant.isOpen_fiber _).preimage
          (hb.comp continuous_subtype_val)).mem_nhds rfl⟩
    · intro p
      rw [continuousOn_iff_continuous_domRestrict]
      let g : {z : {y : Y // D.rank (b y) = q} // A.rank (b z.1) = p} →
          {y : {y : Y // (A.rank + D.rank) (b y) = p + q} //
            rankSplit A D (p + q) ⟨b y.1, y.2⟩ = ⟨(p, q), rfl⟩} :=
        fun z => ⟨⟨z.1.1, congrArg₂ (· + ·) z.2 z.1.2⟩, Subtype.ext (Prod.ext z.2 z.1.2)⟩
      have hg : Continuous g :=
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
      refine ((hpiece p q).2.comp hg).congr fun z => TotalSpace.mk_inj.mpr (funext fun j => ?_)
      exact splitCoords_cast_snd z.2 z.1.2 (g z).1.2 rfl (s z.1.1) j

/-- **Continuity into a variable-rank Whitney sum.** A map into the reconstructed total space of
`whitneySum A D` is continuous if and only if its two coordinate blocks under `splitCoords` define
continuous maps into the reconstructed total spaces of `A` and `D`. -/
theorem continuous_mk_whitneySum_iff {Y : Type*} [TopologicalSpace Y]
    {A D : FiniteRankAtlas 𝕜 X} {b : Y → X} {s : ∀ y, (whitneySum A D).Fiber (b y)} :
    Continuous (fun y => (⟨b y, s y⟩ : TotalSpace Unit (whitneySum A D).Fiber)) ↔
      Continuous (fun y =>
        (⟨b y, (splitCoords (𝕜 := 𝕜) (A.rank (b y)) (D.rank (b y)) (s y)).1⟩ :
          TotalSpace Unit A.Fiber)) ∧
      Continuous (fun y =>
        (⟨b y, (splitCoords (𝕜 := 𝕜) (A.rank (b y)) (D.rank (b y)) (s y)).2⟩ :
          TotalSpace Unit D.Fiber)) := by
  refine ⟨continuous_blocks_of_continuous_whitneySum, ?_⟩
  rintro ⟨hs₁, hs₂⟩
  have hb : Continuous b := A.continuous_proj.comp hs₁
  let s₁ (y : Y) : A.Fiber (b y) :=
    (splitCoords (𝕜 := 𝕜) (A.rank (b y)) (D.rank (b y)) (s y)).1
  let s₂ (y : Y) : D.Fiber (b y) :=
    (splitCoords (𝕜 := 𝕜) (A.rank (b y)) (D.rank (b y)) (s y)).2
  have hs₁_strata := (A.continuous_mk_iff_rankStrata hb s₁).1 hs₁
  have hs₂_strata := (D.continuous_mk_iff_rankStrata hb s₂).1 hs₂
  refine ((whitneySum A D).continuous_mk_iff_rankStrata hb s).2 fun n => ?_
  refine ((isLocallyConstant_rankSplit A D n).continuous_mk_pointIndexedVectorBundleCore_iff
    _ ((hb.comp continuous_subtype_val).subtype_mk _) _).2 fun pq => ?_
  refine (continuous_whitneyPieceCore_iff A D n pq
    ((((hb.comp continuous_subtype_val).comp continuous_subtype_val).subtype_mk _).subtype_mk _)
    _).2 ⟨?_, ?_⟩
  · let g₁ : {y : {y : Y // (A.rank + D.rank) (b y) = n} // rankSplit A D n ⟨b y.1, y.2⟩ = pq} →
        {z : Y // A.rank (b z) = pq.1.1} :=
      fun y => ⟨y.1.1, congrArg (fun u : {pq : ℕ × ℕ // pq.1 + pq.2 = n} => u.1.1) y.2⟩
    have hg₁ : Continuous g₁ :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    refine ((hs₁_strata pq.1.1).comp hg₁).congr fun y => TotalSpace.mk_inj.mpr (funext fun i => ?_)
    exact (splitCoords_cast_fst (g₁ y).2
      (congrArg (fun u : {pq : ℕ × ℕ // pq.1 + pq.2 = n} => u.1.2) y.2) y.1.2 pq.2 (s y.1.1) i).symm
  · let g₂ : {y : {y : Y // (A.rank + D.rank) (b y) = n} // rankSplit A D n ⟨b y.1, y.2⟩ = pq} →
        {z : Y // D.rank (b z) = pq.1.2} :=
      fun y => ⟨y.1.1, congrArg (fun u : {pq : ℕ × ℕ // pq.1 + pq.2 = n} => u.1.2) y.2⟩
    have hg₂ : Continuous g₂ :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    refine ((hs₂_strata pq.1.2).comp hg₂).congr fun y => TotalSpace.mk_inj.mpr (funext fun j => ?_)
    exact (splitCoords_cast_snd
      (congrArg (fun u : {pq : ℕ × ℕ // pq.1 + pq.2 = n} => u.1.1) y.2)
      (g₂ y).2 y.1.2 pq.2 (s y.1.1) j).symm

/-- Projection of the variable-rank Whitney sum onto its first summand. -/
noncomputable def whitneyFst (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ A where
  fiberMap x := (LinearMap.fst 𝕜 (A.Fiber x) (D.Fiber x)).comp
    (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearMap
  continuous_totalSpaceMap :=
    (continuous_mk_whitneySum_iff.1
      (continuous_id (X := TotalSpace Unit (whitneySum A D).Fiber))).1

/-- Projection of the variable-rank Whitney sum onto its second summand. -/
noncomputable def whitneySnd (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ D where
  fiberMap x := (LinearMap.snd 𝕜 (A.Fiber x) (D.Fiber x)).comp
    (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearMap
  continuous_totalSpaceMap :=
    (continuous_mk_whitneySum_iff.1
      (continuous_id (X := TotalSpace Unit (whitneySum A D).Fiber))).2

/-- Inclusion of the first summand into the variable-rank Whitney sum. -/
noncomputable def whitneyInl (A D : FiniteRankAtlas 𝕜 X) : A ⟶ whitneySum A D where
  fiberMap x := (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toLinearMap.comp
    (LinearMap.inl 𝕜 (A.Fiber x) (D.Fiber x))
  continuous_totalSpaceMap := by
    refine continuous_mk_whitneySum_iff.2 ⟨?_, ?_⟩
    · refine continuous_id.congr fun p => ?_
      rcases p with ⟨x, v⟩
      exact TotalSpace.mk_inj.mpr <| congrArg Prod.fst
        ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (v, 0)).symm
    · refine (D.continuous_zeroSection.comp A.continuous_proj).congr fun p => ?_
      rcases p with ⟨x, v⟩
      exact TotalSpace.mk_inj.mpr <| congrArg Prod.snd
        ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (v, 0)).symm

/-- Inclusion of the second summand into the variable-rank Whitney sum. -/
noncomputable def whitneyInr (A D : FiniteRankAtlas 𝕜 X) : D ⟶ whitneySum A D where
  fiberMap x := (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toLinearMap.comp
    (LinearMap.inr 𝕜 (A.Fiber x) (D.Fiber x))
  continuous_totalSpaceMap := by
    refine continuous_mk_whitneySum_iff.2 ⟨?_, ?_⟩
    · refine (A.continuous_zeroSection.comp D.continuous_proj).congr fun p => ?_
      rcases p with ⟨x, w⟩
      exact TotalSpace.mk_inj.mpr <| congrArg Prod.fst
        ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (0, w)).symm
    · refine continuous_id.congr fun p => ?_
      rcases p with ⟨x, w⟩
      exact TotalSpace.mk_inj.mpr <| congrArg Prod.snd
        ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (0, w)).symm

@[simp] theorem fiberMap_whitneyFst (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyFst A D).fiberMap x =
      (LinearMap.fst 𝕜 (A.Fiber x) (D.Fiber x)).comp
        (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearMap := (rfl)

@[simp] theorem fiberMap_whitneySnd (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneySnd A D).fiberMap x =
      (LinearMap.snd 𝕜 (A.Fiber x) (D.Fiber x)).comp
        (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearMap := (rfl)

@[simp] theorem fiberMap_whitneyInl (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyInl A D).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toLinearMap.comp
        (LinearMap.inl 𝕜 (A.Fiber x) (D.Fiber x)) := (rfl)

@[simp] theorem fiberMap_whitneyInr (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyInr A D).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toLinearMap.comp
        (LinearMap.inr 𝕜 (A.Fiber x) (D.Fiber x)) := (rfl)

@[reassoc (attr := simp)] theorem whitneyInl_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneyFst A D = 𝟙 A := by
  apply hom_ext; intro x
  apply LinearMap.ext; intro v
  exact congrArg Prod.fst
    ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (v, 0))

@[reassoc (attr := simp)] theorem whitneyInl_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneySnd A D = 0 := by
  apply hom_ext; intro x
  apply LinearMap.ext; intro v
  exact congrArg Prod.snd
    ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (v, 0))

@[reassoc (attr := simp)] theorem whitneyInr_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneyFst A D = 0 := by
  apply hom_ext; intro x
  apply LinearMap.ext; intro w
  exact congrArg Prod.fst
    ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (0, w))

@[reassoc (attr := simp)] theorem whitneyInr_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneySnd A D = 𝟙 D := by
  apply hom_ext; intro x
  apply LinearMap.ext; intro w
  exact congrArg Prod.snd
    ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (0, w))

/-- The variable-rank Whitney sum equipped with its four canonical projections and inclusions. -/
-- Expose the point projection so the types of the four legs reduce to `whitneySum A D`.
@[expose]
noncomputable def whitneyBicone (A D : FiniteRankAtlas 𝕜 X) : BinaryBicone A D where
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

/-- The two coordinate-block projections and inclusions resolve the identity on `whitneySum A D`. -/
@[simp] theorem whitney_total (A D : FiniteRankAtlas 𝕜 X) :
    whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D =
      𝟙 (whitneySum A D) := by
  apply hom_ext; intro x
  apply LinearMap.ext; intro v
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)
  exact (e.symm.map_add ((e v).1, 0) (0, (e v).2)).symm.trans <|
    (congrArg e.symm (Prod.ext (add_zero _) (zero_add _))).trans (e.symm_apply_apply v)

/-- The variable-rank Whitney sum is simultaneously a categorical product and coproduct. -/
noncomputable def whitneyBiconeIsBilimit (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).IsBilimit :=
  isBinaryBilimitOfTotal _ (whitney_total A D)

/-- Variable-rank bundle atlases have binary biproducts given by the geometric Whitney sum. -/
instance : HasBinaryBiproducts (FiniteRankAtlas 𝕜 X) where
  has_binary_biproduct A D := ⟨⟨whitneyBicone A D, whitneyBiconeIsBilimit A D⟩⟩

/-- Variable-rank bundle atlases have all finite biproducts. -/
instance : HasFiniteBiproducts (FiniteRankAtlas 𝕜 X) :=
  hasFiniteBiproducts_of_hasBinaryBiproducts

@[simp] theorem rank_biprod (A D : FiniteRankAtlas 𝕜 X) :
    (A ⊞ D).rank = A.rank + D.rank :=
  (biprod.uniqueUpToIso A D (whitneyBiconeIsBilimit A D)).symm.finiteRankAtlas_rank_eq

@[simp] theorem rank_biproduct.{w} {J : Type w} [Fintype J] (f : J → FiniteRankAtlas 𝕜 X) :
    (⨁ f).rank = ∑ j, (f j).rank := by
  suffices ∀ (n : ℕ) {K : Type w} [Fintype K] (g : K → FiniteRankAtlas 𝕜 X),
      Fintype.card K = n → (⨁ g).rank = ∑ k, (g k).rank from
    this (Fintype.card J) f rfl
  intro n
  induction n with
  | zero =>
    intro K _ g hK
    have : IsEmpty K := Fintype.card_eq_zero_iff.1 hK
    rw [isZero_iff_rank_eq_zero.1 (isZero_biproduct_of_isEmpty g), Finset.sum_of_isEmpty]
  | succ n ih =>
    intro K _ g hK
    classical
    have : Nonempty K := Fintype.card_pos_iff.1 (by omega)
    let k₀ : K := Classical.arbitrary K
    have hcard : Fintype.card {k : K // k ≠ k₀} = n := by
      have : Unique {k : K // k = k₀} :=
        { default := ⟨k₀, rfl⟩, uniq := fun ⟨_, hk⟩ => Subtype.ext hk }
      have h1 : Fintype.card {k : K // k = k₀} = 1 := Fintype.card_unique
      rw [Fintype.card_subtype_compl (· = k₀), h1, hK]
      omega
    calc
      (⨁ g).rank = (g k₀ ⊞ ⨁ Subtype.restrict (· ≠ k₀) g).rank :=
        (biproductSubtypeNeIso g k₀).finiteRankAtlas_rank_eq
      _ = (g k₀).rank + (⨁ Subtype.restrict (· ≠ k₀) g).rank := rank_biprod _ _
      _ = (g k₀).rank + ∑ k : {k : K // k ≠ k₀}, (g k.1).rank := by
        rw [ih (Subtype.restrict (· ≠ k₀) g) hcard]
        rfl
      _ = ∑ k, (g k).rank := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀)]
        congr 1
        refine Finset.sum_bij (fun k _ => k.1)
          (fun k _ => Finset.mem_erase.2 ⟨k.2, Finset.mem_univ _⟩)
          (fun _ _ _ _ h => Subtype.ext h)
          (fun k hk => ⟨⟨k, (Finset.mem_erase.1 hk).1⟩, Finset.mem_univ _, rfl⟩)
          (fun _ _ => rfl)

end WhitneySum

section UniversalProperty

variable {A A' A'' D D' D'' C E : FiniteRankAtlas 𝕜 X}

/-- Pair two variable-rank bundle morphisms with common source into the concrete Whitney sum. -/
noncomputable def whitneyLift (f : E ⟶ A) (g : E ⟶ D) : E ⟶ whitneySum A D :=
  f ≫ whitneyInl A D + g ≫ whitneyInr A D

theorem whitneyLift_def (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g = f ≫ whitneyInl A D + g ≫ whitneyInr A D := (rfl)

@[reassoc (attr := simp)] theorem whitneyLift_fst (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g ≫ whitneyFst A D = f := by
  simp [whitneyLift, Preadditive.add_comp]

@[reassoc (attr := simp)] theorem whitneyLift_snd (f : E ⟶ A) (g : E ⟶ D) :
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

@[reassoc] theorem comp_whitneyLift (h : C ⟶ E) (f : E ⟶ A) (g : E ⟶ D) :
    h ≫ whitneyLift f g = whitneyLift (h ≫ f) (h ≫ g) := by
  simp only [whitneyLift, Preadditive.comp_add, Category.assoc]

@[simp] theorem whitneyLift_fst_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyLift (whitneyFst A D) (whitneySnd A D) = 𝟙 (whitneySum A D) :=
  whitney_total A D

@[simp] theorem fiberMap_whitneyLift (f : E ⟶ A) (g : E ⟶ D) (x : X) :
    (whitneyLift f g).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toLinearMap.comp
        ((f.fiberMap x).prod (g.fiberMap x)) := by
  apply LinearMap.ext; intro v
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)
  exact (e.symm.map_add (f.fiberMap x v, 0) (0, g.fiberMap x v)).symm.trans
    (congrArg e.symm (Prod.ext (add_zero _) (zero_add _)))

theorem splitCoords_fiberMap_whitneyLift (f : E ⟶ A) (g : E ⟶ D) (x : X) (v : E.Fiber x) :
    splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) ((whitneyLift f g).fiberMap x v) =
      (f.fiberMap x v, g.fiberMap x v) := by
  rw [DFunLike.congr_fun (fiberMap_whitneyLift f g x) v]
  exact (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply
    (f.fiberMap x v, g.fiberMap x v)

/-- Copair two variable-rank bundle morphisms with common target out of the concrete Whitney sum. -/
noncomputable def whitneyDesc (f : A ⟶ E) (g : D ⟶ E) : whitneySum A D ⟶ E :=
  whitneyFst A D ≫ f + whitneySnd A D ≫ g

theorem whitneyDesc_def (f : A ⟶ E) (g : D ⟶ E) :
    whitneyDesc f g = whitneyFst A D ≫ f + whitneySnd A D ≫ g := (rfl)

@[reassoc (attr := simp)] theorem whitneyInl_desc (f : A ⟶ E) (g : D ⟶ E) :
    whitneyInl A D ≫ whitneyDesc f g = f := by
  simp [whitneyDesc, Preadditive.comp_add]

@[reassoc (attr := simp)] theorem whitneyInr_desc (f : A ⟶ E) (g : D ⟶ E) :
    whitneyInr A D ≫ whitneyDesc f g = g := by
  simp [whitneyDesc, Preadditive.comp_add]

@[reassoc (attr := simp)] theorem whitneyLift_desc (f : E ⟶ A) (g : E ⟶ D) (h : A ⟶ C) (k : D ⟶ C) :
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

@[reassoc] theorem whitneyDesc_comp (f : A ⟶ E) (g : D ⟶ E) (h : E ⟶ C) :
    whitneyDesc f g ≫ h = whitneyDesc (f ≫ h) (g ≫ h) := by
  simp only [whitneyDesc, Preadditive.add_comp, Category.assoc]

@[simp] theorem whitneyDesc_inl_inr (A D : FiniteRankAtlas 𝕜 X) :
    whitneyDesc (whitneyInl A D) (whitneyInr A D) = 𝟙 (whitneySum A D) :=
  whitney_total A D

@[simp] theorem fiberMap_whitneyDesc (f : A ⟶ E) (g : D ⟶ E) (x : X) :
    (whitneyDesc f g).fiberMap x =
      ((f.fiberMap x).coprod (g.fiberMap x)).comp
        (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearMap := by
  apply LinearMap.ext; intro _; rfl

theorem fiberMap_whitneyDesc_apply (f : A ⟶ E) (g : D ⟶ E) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneyDesc f g).fiberMap x v =
      f.fiberMap x (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).1 +
        g.fiberMap x (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).2 :=
  (DFunLike.congr_fun (fiberMap_whitneyDesc f g x) v).trans <|
    LinearMap.coprod_apply (f.fiberMap x) (g.fiberMap x)
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v)

/-- Direct sum of two variable-rank bundle morphisms on Whitney sums. -/
noncomputable def whitneyMap (f : A ⟶ A') (g : D ⟶ D') : whitneySum A D ⟶ whitneySum A' D' :=
  whitneyLift (whitneyFst A D ≫ f) (whitneySnd A D ≫ g)

theorem whitneyMap_def (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g = whitneyLift (whitneyFst A D ≫ f) (whitneySnd A D ≫ g) := (rfl)

@[reassoc (attr := simp)] theorem whitneyMap_fst (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ whitneyFst A' D' = whitneyFst A D ≫ f :=
  whitneyLift_fst _ _

@[reassoc (attr := simp)] theorem whitneyMap_snd (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ whitneySnd A' D' = whitneySnd A D ≫ g :=
  whitneyLift_snd _ _

@[reassoc (attr := simp)] theorem whitneyInl_map (f : A ⟶ A') (g : D ⟶ D') :
    whitneyInl A D ≫ whitneyMap f g = f ≫ whitneyInl A' D' :=
  whitneySum_hom_ext (by simp) (by simp)

@[reassoc (attr := simp)] theorem whitneyInr_map (f : A ⟶ A') (g : D ⟶ D') :
    whitneyInr A D ≫ whitneyMap f g = g ≫ whitneyInr A' D' :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp] theorem whitneyMap_id (A D : FiniteRankAtlas 𝕜 X) :
    whitneyMap (𝟙 A) (𝟙 D) = 𝟙 (whitneySum A D) := by
  simp [whitneyMap_def]

@[simp] theorem whitneyMap_zero (A A' D D' : FiniteRankAtlas 𝕜 X) :
    whitneyMap (0 : A ⟶ A') (0 : D ⟶ D') = 0 :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp] theorem whitneyMap_comp (f₁ : A ⟶ A') (f₂ : A' ⟶ A'') (g₁ : D ⟶ D') (g₂ : D' ⟶ D'') :
    whitneyMap (f₁ ≫ f₂) (g₁ ≫ g₂) = whitneyMap f₁ g₁ ≫ whitneyMap f₂ g₂ :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp] theorem fiberMap_whitneyMap (f : A ⟶ A') (g : D ⟶ D') (x : X) :
    (whitneyMap f g).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A'.rank x) (D'.rank x)).symm.toLinearMap.comp
        (((f.fiberMap x).prodMap (g.fiberMap x)).comp
          (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearMap) := by
  simp only [whitneyMap_def, fiberMap_whitneyLift, fiberMap_comp, fiberMap_whitneyFst,
    fiberMap_whitneySnd]
  apply LinearMap.ext; intro _; rfl

theorem splitCoords_fiberMap_whitneyMap (f : A ⟶ A') (g : D ⟶ D') (x : X)
    (v : (whitneySum A D).Fiber x) :
    splitCoords (𝕜 := 𝕜) (A'.rank x) (D'.rank x) ((whitneyMap f g).fiberMap x v) =
      (f.fiberMap x (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).1,
        g.fiberMap x (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).2) := by
  rw [DFunLike.congr_fun (fiberMap_whitneyMap f g x) v]
  exact (splitCoords (𝕜 := 𝕜) (A'.rank x) (D'.rank x)).apply_symm_apply _

/-- Direct sum of two variable-rank bundle atlas isomorphisms. -/
noncomputable def whitneyMapIso (e₁ : A ≅ A') (e₂ : D ≅ D') :
    whitneySum A D ≅ whitneySum A' D' where
  hom := whitneyMap e₁.hom e₂.hom
  inv := whitneyMap e₁.inv e₂.inv
  hom_inv_id := by rw [← whitneyMap_comp, e₁.hom_inv_id, e₂.hom_inv_id, whitneyMap_id]
  inv_hom_id := by rw [← whitneyMap_comp, e₁.inv_hom_id, e₂.inv_hom_id, whitneyMap_id]

@[simp] theorem whitneyMapIso_hom (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).hom = whitneyMap e₁.hom e₂.hom := (rfl)

@[simp] theorem whitneyMapIso_inv (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).inv = whitneyMap e₁.inv e₂.inv := (rfl)

end UniversalProperty

section Coherence

/-- Symmetry isomorphism exchanging the two summands of a variable-rank Whitney sum. -/
noncomputable def whitneyCommIso (A D : FiniteRankAtlas 𝕜 X) :
    whitneySum A D ≅ whitneySum D A where
  hom := whitneyLift (whitneySnd A D) (whitneyFst A D)
  inv := whitneyLift (whitneySnd D A) (whitneyFst D A)
  hom_inv_id := whitneySum_hom_ext (by simp) (by simp)
  inv_hom_id := whitneySum_hom_ext (by simp) (by simp)

@[simp] theorem whitneyCommIso_hom (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyCommIso A D).hom = whitneyLift (whitneySnd A D) (whitneyFst A D) := (rfl)

@[simp] theorem whitneyCommIso_inv (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyCommIso A D).inv = whitneyLift (whitneySnd D A) (whitneyFst D A) := (rfl)

@[reassoc] theorem whitneyMap_commIso_hom {A A' D D' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ (whitneyCommIso A' D').hom =
      (whitneyCommIso A D).hom ≫ whitneyMap g f :=
  whitneySum_hom_ext (by simp) (by simp)

/-- Associativity isomorphism regrouping a threefold variable-rank Whitney sum. -/
noncomputable def whitneyAssocIso (A D C : FiniteRankAtlas 𝕜 X) :
    whitneySum (whitneySum A D) C ≅ whitneySum A (whitneySum D C) where
  hom := whitneyLift (whitneyFst _ _ ≫ whitneyFst A D)
    (whitneyLift (whitneyFst _ _ ≫ whitneySnd A D) (whitneySnd _ _))
  inv := whitneyLift (whitneyLift (whitneyFst _ _) (whitneySnd _ _ ≫ whitneyFst D C))
    (whitneySnd _ _ ≫ whitneySnd D C)
  hom_inv_id := whitneySum_hom_ext (whitneySum_hom_ext (by simp) (by simp)) (by simp)
  inv_hom_id := whitneySum_hom_ext (by simp) (whitneySum_hom_ext (by simp) (by simp))

@[simp] theorem whitneyAssocIso_hom (A D C : FiniteRankAtlas 𝕜 X) :
    (whitneyAssocIso A D C).hom =
      whitneyLift (whitneyFst _ _ ≫ whitneyFst A D)
        (whitneyLift (whitneyFst _ _ ≫ whitneySnd A D) (whitneySnd _ _)) := (rfl)

@[simp] theorem whitneyAssocIso_inv (A D C : FiniteRankAtlas 𝕜 X) :
    (whitneyAssocIso A D C).inv =
      whitneyLift (whitneyLift (whitneyFst _ _) (whitneySnd _ _ ≫ whitneyFst D C))
        (whitneySnd _ _ ≫ whitneySnd D C) := (rfl)

@[reassoc] theorem whitneyMap_assocIso_hom {A A' D D' C C' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') (h : C ⟶ C') :
    whitneyMap (whitneyMap f g) h ≫ (whitneyAssocIso A' D' C').hom =
      (whitneyAssocIso A D C).hom ≫ whitneyMap f (whitneyMap g h) :=
  whitneySum_hom_ext (by simp) (whitneySum_hom_ext (by simp) (by simp))

/-- Left unit isomorphism for Whitney sum with the trivial rank-zero atlas. -/
noncomputable def whitneyZeroLeftIso (A : FiniteRankAtlas 𝕜 X) :
    whitneySum (trivial 𝕜 X 0) A ≅ A where
  hom := whitneySnd (trivial 𝕜 X 0) A
  inv := whitneyInr (trivial 𝕜 X 0) A
  hom_inv_id := whitneySum_hom_ext' (isZero_trivial_zero.eq_of_src _ _) (by simp)
  inv_hom_id := whitneyInr_snd (trivial 𝕜 X 0) A

@[simp] theorem whitneyZeroLeftIso_hom (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroLeftIso A).hom = whitneySnd (trivial 𝕜 X 0) A := (rfl)

@[simp] theorem whitneyZeroLeftIso_inv (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroLeftIso A).inv = whitneyInr (trivial 𝕜 X 0) A := (rfl)

@[reassoc] theorem whitneyMap_zeroLeftIso_hom {A A' : FiniteRankAtlas 𝕜 X}
    (g : trivial 𝕜 X 0 ⟶ trivial 𝕜 X 0) (f : A ⟶ A') :
    whitneyMap g f ≫ (whitneyZeroLeftIso A').hom = (whitneyZeroLeftIso A).hom ≫ f := by
  simp only [whitneyZeroLeftIso_hom, whitneyMap_snd]

/-- Right unit isomorphism for Whitney sum with the trivial rank-zero atlas. -/
noncomputable def whitneyZeroRightIso (A : FiniteRankAtlas 𝕜 X) :
    whitneySum A (trivial 𝕜 X 0) ≅ A where
  hom := whitneyFst A (trivial 𝕜 X 0)
  inv := whitneyInl A (trivial 𝕜 X 0)
  hom_inv_id := whitneySum_hom_ext' (by simp) (isZero_trivial_zero.eq_of_src _ _)
  inv_hom_id := whitneyInl_fst A (trivial 𝕜 X 0)

@[simp] theorem whitneyZeroRightIso_hom (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroRightIso A).hom = whitneyFst A (trivial 𝕜 X 0) := (rfl)

@[simp] theorem whitneyZeroRightIso_inv (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroRightIso A).inv = whitneyInl A (trivial 𝕜 X 0) := (rfl)

@[reassoc] theorem whitneyMap_zeroRightIso_hom {A A' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : trivial 𝕜 X 0 ⟶ trivial 𝕜 X 0) :
    whitneyMap f g ≫ (whitneyZeroRightIso A').hom = (whitneyZeroRightIso A).hom ≫ f := by
  simp only [whitneyZeroRightIso_hom, whitneyMap_fst]

private theorem splitCoords_symm_cast {n p q a d : ℕ}
    (hp : a = p) (hq : d = q) (hn : a + d = n) (hpq : p + q = n)
    (v : Fin (a + d) → 𝕜) (i : Fin n) :
    v (Fin.cast hn.symm i) =
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜) (finCongr hpq))
        ((splitCoords (𝕜 := 𝕜) p q).symm
          (fun k => (splitCoords (𝕜 := 𝕜) a d v).1 (Fin.cast hp.symm k),
            fun k => (splitCoords (𝕜 := 𝕜) a d v).2 (Fin.cast hq.symm k))) i := by
  subst hp hq hn
  have h := (splitCoords (𝕜 := 𝕜) a d).symm_apply_apply v
  exact (congrFun h i).symm

private theorem continuous_trivialAdd_hom (r₁ r₂ : LocallyConstant X ℕ) :
    Continuous (fun p : TotalSpace Unit (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).Fiber =>
      (⟨p.proj, p.2⟩ : TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber)) := by
  have hfst_snd := continuous_mk_whitneySum_iff.1
    (continuous_id
      (X := TotalSpace Unit (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).Fiber))
  have hc₁ := (continuous_mk_trivial_iff (r := r₁)
    (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).continuous_proj _).1 hfst_snd.1
  have hc₂ := (continuous_mk_trivial_iff (r := r₂)
    (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).continuous_proj _).1 hfst_snd.2
  refine (continuous_mk_trivial_iff (r := r₁ + r₂)
    (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).continuous_proj
    (fun p => (p.2 : (trivial 𝕜 X (r₁ + r₂)).Fiber p.proj))).2 fun n => ?_
  let S := {y : TotalSpace Unit (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).Fiber //
    (r₁ + r₂) y.proj = n}
  apply continuous_of_cover_nhds
    (s := fun pq : ℕ × ℕ => {y : S | r₁ y.1.proj = pq.1 ∧ r₂ y.1.proj = pq.2})
  · exact fun y => ⟨(r₁ y.1.proj, r₂ y.1.proj),
      (((r₁.isLocallyConstant.isOpen_fiber _).preimage
          ((whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).continuous_proj.comp
            continuous_subtype_val)).inter
        ((r₂.isLocallyConstant.isOpen_fiber _).preimage
          ((whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).continuous_proj.comp
            continuous_subtype_val))).mem_nhds ⟨rfl, rfl⟩⟩
  · rintro ⟨p, q⟩
    rw [continuousOn_iff_continuous_domRestrict]
    by_cases hpq : p + q = n
    · let g₁ : {y : S // r₁ y.1.proj = p ∧ r₂ y.1.proj = q} →
          {z : TotalSpace Unit (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).Fiber //
            r₁ z.proj = p} := fun y => ⟨y.1.1, y.2.1⟩
      let g₂ : {y : S // r₁ y.1.proj = p ∧ r₂ y.1.proj = q} →
          {z : TotalSpace Unit (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).Fiber //
            r₂ z.proj = q} := fun y => ⟨y.1.1, y.2.2⟩
      have hg₁ : Continuous g₁ :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      have hg₂ : Continuous g₂ :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      have hpair := ((hc₁ p).comp hg₁).prodMk ((hc₂ q).comp hg₂)
      have hjoined :=
        (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜) (finCongr hpq)).continuous.comp
          ((splitCoords (𝕜 := 𝕜) (M := 𝕜) p q).symm.continuous.comp hpair)
      refine hjoined.congr fun y => funext fun i => ?_
      exact (splitCoords_symm_cast y.2.1 y.2.2 y.1.2 hpq y.1.1.2 i).symm
    · have : IsEmpty {y : S // r₁ y.1.proj = p ∧ r₂ y.1.proj = q} :=
        ⟨fun y => hpq ((congrArg₂ (· + ·) y.2.1.symm y.2.2.symm).trans y.1.2)⟩
      exact continuous_of_discreteTopology

private theorem continuous_trivialAdd_inv (r₁ r₂ : LocallyConstant X ℕ) :
    Continuous (fun p : TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber =>
      (⟨p.proj, p.2⟩ :
        TotalSpace Unit (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).Fiber)) := by
  have hc := (continuous_mk_trivial_iff (r := r₁ + r₂)
    (trivial 𝕜 X (r₁ + r₂)).continuous_proj _).1
      (continuous_id (X := TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber))
  refine (continuous_mk_whitneySum_iff
    (A := trivial 𝕜 X r₁) (D := trivial 𝕜 X r₂)
    (b := fun p : TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber => p.proj)
    (s := fun p => (p.2 : (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).Fiber p.proj))).2 ⟨?_, ?_⟩
  · refine (continuous_mk_trivial_iff (r := r₁)
      (trivial 𝕜 X (r₁ + r₂)).continuous_proj _).2 fun p => ?_
    let S := {y : TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber // r₁ y.proj = p}
    apply continuous_of_cover_nhds
      (s := fun q : ℕ => {y : S | r₂ y.1.proj = q})
    · exact fun y => ⟨r₂ y.1.proj,
        ((r₂.isLocallyConstant.isOpen_fiber _).preimage
          ((trivial 𝕜 X (r₁ + r₂)).continuous_proj.comp continuous_subtype_val)).mem_nhds rfl⟩
    · intro q
      rw [continuousOn_iff_continuous_domRestrict]
      let g : {y : S // r₂ y.1.proj = q} →
          {z : TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber // (r₁ + r₂) z.proj = p + q} :=
        fun y => ⟨y.1.1, congrArg₂ (· + ·) y.1.2 y.2⟩
      have hg : Continuous g :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      have hfst := (continuous_fst.comp
        (splitCoords (𝕜 := 𝕜) (M := 𝕜) p q).continuous).comp ((hc (p + q)).comp hg)
      refine hfst.congr fun y => funext fun i => ?_
      exact splitCoords_cast_fst y.1.2 y.2 (g y).2 rfl y.1.1.2 i
  · refine (continuous_mk_trivial_iff (r := r₂)
      (trivial 𝕜 X (r₁ + r₂)).continuous_proj _).2 fun q => ?_
    let S := {y : TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber // r₂ y.proj = q}
    apply continuous_of_cover_nhds
      (s := fun p : ℕ => {y : S | r₁ y.1.proj = p})
    · exact fun y => ⟨r₁ y.1.proj,
        ((r₁.isLocallyConstant.isOpen_fiber _).preimage
          ((trivial 𝕜 X (r₁ + r₂)).continuous_proj.comp continuous_subtype_val)).mem_nhds rfl⟩
    · intro p
      rw [continuousOn_iff_continuous_domRestrict]
      let g : {y : S // r₁ y.1.proj = p} →
          {z : TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber // (r₁ + r₂) z.proj = p + q} :=
        fun y => ⟨y.1.1, congrArg₂ (· + ·) y.2 y.1.2⟩
      have hg : Continuous g :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      have hsnd := (continuous_snd.comp
        (splitCoords (𝕜 := 𝕜) (M := 𝕜) p q).continuous).comp ((hc (p + q)).comp hg)
      refine hsnd.congr fun y => funext fun j => ?_
      exact splitCoords_cast_snd y.2 y.1.2 (g y).2 rfl y.1.1.2 j

/-- Canonical isomorphism identifying the Whitney sum of two trivial variable-rank atlases with the
trivial atlas of the summed rank, acting as the identity on every coordinate fibre. -/
noncomputable def trivialAddIso (r₁ r₂ : LocallyConstant X ℕ) :
    whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂) ≅ trivial 𝕜 X (r₁ + r₂) :=
  isoMk
    (fun x : X => (LinearEquiv.refl 𝕜 (Fin (r₁ x + r₂ x) → 𝕜) :
      (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).Fiber x ≃ₗ[𝕜]
        (trivial 𝕜 X (r₁ + r₂)).Fiber x))
    (continuous_trivialAdd_hom r₁ r₂) (continuous_trivialAdd_inv r₁ r₂)

@[simp]
theorem fiberMap_trivialAddIso_hom (r₁ r₂ : LocallyConstant X ℕ) (x : X) :
    (trivialAddIso (𝕜 := 𝕜) r₁ r₂).hom.fiberMap x = LinearMap.id :=
  fiberMap_isoMk_hom _ _ _ x

@[simp]
theorem fiberMap_trivialAddIso_inv (r₁ r₂ : LocallyConstant X ℕ) (x : X) :
    (trivialAddIso (𝕜 := 𝕜) r₁ r₂).inv.fiberMap x = LinearMap.id :=
  fiberMap_isoMk_inv _ _ _ x

end Coherence

section FiberedProduct

private noncomputable def fiberedProdToFun (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj} :=
  ⟨((whitneyFst A D).totalSpaceMap p, (whitneySnd A D).totalSpaceMap p), by simp⟩

private noncomputable def fiberedProdInvFun (A D : FiniteRankAtlas 𝕜 X)
    (pq : {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj}) :
    TotalSpace Unit (whitneySum A D).Fiber :=
  ⟨pq.1.1.proj,
    (splitCoords (𝕜 := 𝕜) (A.rank pq.1.1.proj) (D.rank pq.1.1.proj)).symm
      (pq.1.1.2, cast (congrArg D.Fiber pq.2.symm) pq.1.2.2)⟩

/-- Global homeomorphism between the reconstructed total space of `whitneySum A D` and the
topological fibered product over `X` of the reconstructed total spaces of `A` and `D`. -/
noncomputable def whitneySumFiberedProdHomeomorph (A D : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit (whitneySum A D).Fiber ≃ₜ
      {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj} where
  toFun := fiberedProdToFun A D
  invFun := fiberedProdInvFun A D
  left_inv p := by
    rcases p with ⟨x, v⟩
    have hpair : fiberedProdToFun A D ⟨x, v⟩ =
        ⟨(⟨x, (whitneyFst A D).fiberMap x v⟩, ⟨x, (whitneySnd A D).fiberMap x v⟩), rfl⟩ :=
      Subtype.ext (Prod.ext ((whitneyFst A D).totalSpaceMap_mk x v)
        ((whitneySnd A D).totalSpaceMap_mk x v))
    exact (congrArg (fiberedProdInvFun A D) hpair).trans
      (TotalSpace.mk_inj.mpr
        ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).symm_apply_apply v))
  right_inv := by
    rintro ⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, h⟩
    cases h
    let v : (whitneySum A D).Fiber x₁ :=
      (splitCoords (𝕜 := 𝕜) (A.rank x₁) (D.rank x₁)).symm (u, w)
    exact Subtype.ext (Prod.ext
      (((whitneyFst A D).totalSpaceMap_mk x₁ v).trans
        (TotalSpace.mk_inj.mpr (congrArg Prod.fst
          ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x₁) (D.rank x₁)).apply_symm_apply (u, w)))))
      (((whitneySnd A D).totalSpaceMap_mk x₁ v).trans
        (TotalSpace.mk_inj.mpr (congrArg Prod.snd
          ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x₁) (D.rank x₁)).apply_symm_apply (u, w))))))
  continuous_toFun :=
    (((whitneyFst A D).totalSpaceMap.continuous).prodMk
      ((whitneySnd A D).totalSpaceMap.continuous)).subtype_mk _
  continuous_invFun := by
    refine continuous_mk_whitneySum_iff.2 ⟨?_, ?_⟩
    · refine (continuous_fst.comp continuous_subtype_val).congr fun pq => ?_
      rcases pq with ⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, h⟩
      cases h
      exact TotalSpace.mk_inj.mpr
        (congrArg Prod.fst
          ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x₁) (D.rank x₁)).apply_symm_apply (u, w))).symm
    · refine (continuous_snd.comp continuous_subtype_val).congr fun pq => ?_
      rcases pq with ⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, h⟩
      cases h
      exact TotalSpace.mk_inj.mpr
        (congrArg Prod.snd
          ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x₁) (D.rank x₁)).apply_symm_apply (u, w))).symm

@[simp]
theorem whitneySumFiberedProdHomeomorph_apply_fst (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    (whitneySumFiberedProdHomeomorph A D p).1.1 = (whitneyFst A D).totalSpaceMap p := (rfl)

@[simp]
theorem whitneySumFiberedProdHomeomorph_apply_snd (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    (whitneySumFiberedProdHomeomorph A D p).1.2 = (whitneySnd A D).totalSpaceMap p := (rfl)

/-- `whitneySumFiberedProdHomeomorph` intertwines `whitneyMap f g` on total spaces with the
componentwise action `(f.totalSpaceMap, g.totalSpaceMap)` on the fibered product over `X`. -/
theorem whitneySumFiberedProdHomeomorph_naturality {A A' D D' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') (p : TotalSpace Unit (whitneySum A D).Fiber) :
    whitneySumFiberedProdHomeomorph A' D' ((whitneyMap f g).totalSpaceMap p) =
      ⟨(f.totalSpaceMap (whitneySumFiberedProdHomeomorph A D p).1.1,
          g.totalSpaceMap (whitneySumFiberedProdHomeomorph A D p).1.2),
        by simp⟩ := by
  rcases p with ⟨x, v⟩
  let w : (whitneySum A' D').Fiber x := (whitneyMap f g).fiberMap x v
  have hw : (whitneyMap f g).totalSpaceMap ⟨x, v⟩ = ⟨x, w⟩ :=
    (whitneyMap f g).totalSpaceMap_mk x v
  rw [hw]
  exact Subtype.ext (Prod.ext
    (((whitneyFst A' D').totalSpaceMap_mk x w).trans <|
      (TotalSpace.mk_inj.mpr (congrArg Prod.fst (splitCoords_fiberMap_whitneyMap f g x v))).trans <|
        (f.totalSpaceMap_mk x _).symm.trans
          (congrArg f.totalSpaceMap ((whitneyFst A D).totalSpaceMap_mk x v).symm))
    (((whitneySnd A' D').totalSpaceMap_mk x w).trans <|
      (TotalSpace.mk_inj.mpr (congrArg Prod.snd (splitCoords_fiberMap_whitneyMap f g x v))).trans <|
        (g.totalSpaceMap_mk x _).symm.trans
          (congrArg g.totalSpaceMap ((whitneySnd A D).totalSpaceMap_mk x v).symm)))

end FiberedProduct

end TauCeti.FiniteRankAtlas
