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
import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct
import TauCeti.Topology.VectorBundle.FiniteRank.Pullback.Basic
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

open Bundle CategoryTheory CategoryTheory.Limits

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

section WhitneySum

/-- On the rank-`n` stratum of `A.rank + D.rank`, record the pair of individual summand ranks. -/
private def rankSplit (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (x : {x : X // (A.rank + D.rank) x = n}) :
    {pq : ℕ × ℕ // pq.1 + pq.2 = n} :=
  ⟨(A.rank x.val, D.rank x.val), x.property⟩

private theorem isLocallyConstant_rankSplit (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    IsLocallyConstant (rankSplit A D n) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  filter_upwards [((A.rank.isLocallyConstant.comp_continuous continuous_subtypeVal).prodMk
    (D.rank.isLocallyConstant.comp_continuous continuous_subtypeVal)).eventually_eq x] with y hy
  exact Subtype.ext hy

private def rankInclusionLeft (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    C({x : {x : X // (A.rank + D.rank) x = n} // rankSplit A D n x = pq},
      {z : X // A.rank z = pq.val.1}) :=
  ⟨fun x => ⟨x.val.val, congrArg (fun u : {pq : ℕ × ℕ // pq.1 + pq.2 = n} => u.val.1) x.property⟩,
    (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _⟩

private def rankInclusionRight (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    C({x : {x : X // (A.rank + D.rank) x = n} // rankSplit A D n x = pq},
      {z : X // D.rank z = pq.val.2}) :=
  ⟨fun x => ⟨x.val.val, congrArg (fun u : {pq : ℕ × ℕ // pq.1 + pq.2 = n} => u.val.2) x.property⟩,
    (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _⟩

/-- On each clopen `(p, q)`-piece of the rank-`n` stratum, form the constant-rank Whitney sum of
the pulled-back stratum cores of `A` and `D`. -/
private def whitneyPieceCore (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    FiniteRankBundleCore 𝕜
      {x : {x : X // (A.rank + D.rank) x = n} // rankSplit A D n x = pq} :=
  FiniteRankBundleCore.whitneySum
    ((A.stratumCore pq.val.1).pullback (rankInclusionLeft A D n pq))
    ((D.stratumCore pq.val.2).pullback (rankInclusionRight A D n pq))

/-- Glue the model-transported constant-rank Whitney sums across the clopen fibres of `rankSplit`
to obtain a point-indexed `VectorBundleCore` on `{x : X // (A.rank + D.rank) x = n}`. -/
noncomputable def whitneyStratumCore (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    VectorBundleCore 𝕜 {x : X // (A.rank + D.rank) x = n} (Fin n → 𝕜)
      {x : X // (A.rank + D.rank) x = n} :=
  (isLocallyConstant_rankSplit A D n).pointIndexedVectorBundleCore fun pq =>
    (whitneyPieceCore A D n pq).core.congrModel
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜) (finCongr pq.property))

/-- Every point of the rank-`n` stratum of `A.rank + D.rank` is its own preferred chart index in
`whitneyStratumCore`. -/
@[simp] theorem indexAt_whitneyStratumCore (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (x : {x : X // (A.rank + D.rank) x = n}) :
    (whitneyStratumCore A D n).indexAt x = x :=
  (isLocallyConstant_rankSplit A D n).indexAt_pointIndexedVectorBundleCore _
    (fun pq y => ((whitneyPieceCore A D n pq).core.indexAt_congrModel _ y).trans
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

/-- The rank function of `whitneySum A D` is the sum `A.rank + D.rank`. -/
@[simp] theorem rank_whitneySum (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySum A D).rank = A.rank + D.rank := (rfl)

/-- Stratum coordinate core of `whitneySum A D` on the rank-`n` clopen stratum. -/
@[simp] theorem charts_whitneySum (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (whitneySum A D).charts n = whitneyStratumCore A D n := (rfl)

private theorem continuous_whitneyPieceCore_iff {Z : Type*} [TopologicalSpace Z]
    (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    {g : Z → {x : {x : X // (A.rank + D.rank) x = n} // rankSplit A D n x = pq}}
    (hg : Continuous g) (t : Z → Fin n → 𝕜) :
    Continuous (fun z =>
        (⟨g z, t z⟩ :
          ((whitneyPieceCore A D n pq).core.congrModel
            (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜)
              (finCongr pq.property))).TotalSpace)) ↔
      Continuous (fun z =>
        (⟨rankInclusionLeft A D n pq (g z),
          (splitCoords (𝕜 := 𝕜) pq.val.1 pq.val.2
            ((ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜)
              (finCongr pq.property)).symm (t z))).1⟩ :
          (A.charts pq.val.1).TotalSpace)) ∧
      Continuous (fun z =>
        (⟨rankInclusionRight A D n pq (g z),
          (splitCoords (𝕜 := 𝕜) pq.val.1 pq.val.2
            ((ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜)
              (finCongr pq.property)).symm (t z))).2⟩ :
          (D.charts pq.val.2).TotalSpace)) := by
  refine (VectorBundleCore.continuous_mk_congrModel_iff _ _).trans ?_
  refine (FiniteRankBundleCore.continuous_mk_whitneySum_iff
    ((A.stratumCore pq.val.1).pullback (rankInclusionLeft A D n pq))
    ((D.stratumCore pq.val.2).pullback (rankInclusionRight A D n pq))).trans ?_
  rw [(A.stratumCore pq.val.1).continuous_core_pullback_iff (rankInclusionLeft A D n pq),
    (D.stratumCore pq.val.2).continuous_core_pullback_iff (rankInclusionRight A D n pq)]
  simp only [and_iff_right hg]
  exact and_congr
    (continuous_congr fun z =>
      (A.stratumCore pq.val.1).pullbackLift_eq_mk (rankInclusionLeft A D n pq) _ rfl rfl)
    (continuous_congr fun z =>
      (D.stratumCore pq.val.2).pullbackLift_eq_mk (rankInclusionRight A D n pq) _ rfl rfl)

private theorem continuous_blocks_of_continuous_whitneySum {Y : Type*} [TopologicalSpace Y]
    {A D : FiniteRankAtlas 𝕜 X} {b : Y → X} {s : ∀ y, (whitneySum A D).Fiber (b y)}
    (hs : Continuous fun y => (⟨b y, s y⟩ : TotalSpace Unit (whitneySum A D).Fiber)) :
    Continuous (fun y =>
      (⟨b y, (splitCoords (𝕜 := 𝕜) (A.rank (b y)) (D.rank (b y)) (s y)).1⟩ :
        TotalSpace Unit A.Fiber)) ∧
    Continuous (fun y =>
      (⟨b y, (splitCoords (𝕜 := 𝕜) (A.rank (b y)) (D.rank (b y)) (s y)).2⟩ :
        TotalSpace Unit D.Fiber)) := by
  have hb : Continuous b := (VariableRankBundle.continuous_proj (whitneySum A D)).comp hs
  have hstrata := (VariableRankBundle.continuous_mk_iff_rankStrata (whitneySum A D) hb s).1 hs
  let s₁ (y : Y) : A.Fiber (b y) := (splitCoords (𝕜 := 𝕜) (A.rank (b y)) (D.rank (b y)) (s y)).1
  let s₂ (y : Y) : D.Fiber (b y) := (splitCoords (𝕜 := 𝕜) (A.rank (b y)) (D.rank (b y)) (s y)).2
  have hpiece (p q : ℕ) := (continuous_whitneyPieceCore_iff A D (p + q) ⟨(p, q), rfl⟩
    ((((hb.comp continuous_subtypeVal).comp continuous_subtypeVal).subtype_mk _).subtype_mk _)
    (fun y => fun i : Fin (p + q) => s y.val.val (Fin.cast y.val.property.symm i))).1 <|
      ((isLocallyConstant_rankSplit A D (p + q)).continuous_mk_pointIndexedVectorBundleCore_iff
        _ ((hb.comp continuous_subtypeVal).subtype_mk _) _).1 (hstrata (p + q)) ⟨(p, q), rfl⟩
  refine ⟨(VariableRankBundle.continuous_mk_iff_rankStrata A hb s₁).2 fun p => ?_,
    (VariableRankBundle.continuous_mk_iff_rankStrata D hb s₂).2 fun q => ?_⟩
  · refine continuous_of_cover_nhds
      (s := fun q : ℕ => {z : {y : Y // A.rank (b y) = p} | D.rank (b z.val) = q})
      (fun z => ⟨D.rank (b z.val), ((D.rank.isLocallyConstant.isOpen_fiber _).preimage
        (hb.comp continuous_subtypeVal)).mem_nhds rfl⟩) fun q => ?_
    rw [continuousOn_iff_continuous_domRestrict]
    let g : {z : {y : Y // A.rank (b y) = p} // D.rank (b z.val) = q} →
        {y : {y : Y // (A.rank + D.rank) (b y) = p + q} //
          rankSplit A D (p + q) ⟨b y.val, y.property⟩ = ⟨(p, q), rfl⟩} :=
      fun z => ⟨⟨z.val.val, congrArg₂ (· + ·) z.val.property z.property⟩, Subtype.ext
          (Prod.ext z.val.property z.property)⟩
    have hg : Continuous g :=
      ((continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _).subtype_mk _
    exact ((hpiece p q).1.comp hg).congr fun z =>
      TotalSpace.mk_inj.mpr (splitCoords_cast_fst z.val.property.symm (g z).val.property.symm
          (s z.val.val))
  · refine continuous_of_cover_nhds
      (s := fun p : ℕ => {z : {y : Y // D.rank (b y) = q} | A.rank (b z.val) = p})
      (fun z => ⟨A.rank (b z.val), ((A.rank.isLocallyConstant.isOpen_fiber _).preimage
        (hb.comp continuous_subtypeVal)).mem_nhds rfl⟩) fun p => ?_
    rw [continuousOn_iff_continuous_domRestrict]
    let g : {z : {y : Y // D.rank (b y) = q} // A.rank (b z.val) = p} →
        {y : {y : Y // (A.rank + D.rank) (b y) = p + q} //
          rankSplit A D (p + q) ⟨b y.val, y.property⟩ = ⟨(p, q), rfl⟩} :=
      fun z => ⟨⟨z.val.val, congrArg₂ (· + ·) z.property z.val.property⟩, Subtype.ext
          (Prod.ext z.property z.val.property)⟩
    have hg : Continuous g :=
      ((continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _).subtype_mk _
    exact ((hpiece p q).2.comp hg).congr fun z =>
      TotalSpace.mk_inj.mpr (splitCoords_cast_snd z.val.property.symm (g z).val.property.symm
          (s z.val.val))

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
  have hb : Continuous b := (VariableRankBundle.continuous_proj A).comp hs₁
  let s₁ (y : Y) : A.Fiber (b y) := (splitCoords (𝕜 := 𝕜) (A.rank (b y)) (D.rank (b y)) (s y)).1
  let s₂ (y : Y) : D.Fiber (b y) := (splitCoords (𝕜 := 𝕜) (A.rank (b y)) (D.rank (b y)) (s y)).2
  have hs₁_strata := (VariableRankBundle.continuous_mk_iff_rankStrata A hb s₁).1 hs₁
  have hs₂_strata := (VariableRankBundle.continuous_mk_iff_rankStrata D hb s₂).1 hs₂
  refine (VariableRankBundle.continuous_mk_iff_rankStrata (whitneySum A D) hb s).2 fun n => ?_
  refine ((isLocallyConstant_rankSplit A D n).continuous_mk_pointIndexedVectorBundleCore_iff
    _ ((hb.comp continuous_subtypeVal).subtype_mk _) _).2 fun pq => ?_
  refine (continuous_whitneyPieceCore_iff A D n pq
    ((((hb.comp continuous_subtypeVal).comp continuous_subtypeVal).subtype_mk _).subtype_mk _)
    _).2 ⟨?_, ?_⟩
  · let g₁ :
      {y : {y : Y // (A.rank + D.rank) (b y) = n} // rankSplit A D n ⟨b y.val, y.property⟩ = pq} →
        {z : Y // A.rank (b z) = pq.val.1} :=
      fun y => ⟨y.val.val, congrArg (fun u : {pq : ℕ × ℕ // pq.1 + pq.2 = n} => u.val.1) y.property⟩
    have hg₁ : Continuous g₁ := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
    exact ((hs₁_strata pq.val.1).comp hg₁).congr fun y =>
      TotalSpace.mk_inj.mpr
        (splitCoords_cast_fst (g₁ y).property.symm (pq.property.trans y.val.property.symm)
            (s y.val.val)).symm
  · let g₂ :
      {y : {y : Y // (A.rank + D.rank) (b y) = n} // rankSplit A D n ⟨b y.val, y.property⟩ = pq} →
        {z : Y // D.rank (b z) = pq.val.2} :=
      fun y => ⟨y.val.val, congrArg (fun u : {pq : ℕ × ℕ // pq.1 + pq.2 = n} => u.val.2) y.property⟩
    have hg₂ : Continuous g₂ := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
    exact ((hs₂_strata pq.val.2).comp hg₂).congr fun y =>
      TotalSpace.mk_inj.mpr
        (splitCoords_cast_snd (g₂ y).property.symm (pq.property.trans y.val.property.symm)
            (s y.val.val)).symm

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
    refine continuous_mk_whitneySum_iff.2 ⟨continuous_id.congr fun ⟨x, v⟩ => ?_,
      ((VariableRankBundle.continuous_zeroSection D).comp
        (VariableRankBundle.continuous_proj A)).congr fun ⟨x, v⟩ => ?_⟩
    · exact TotalSpace.mk_inj.mpr <| congrArg Prod.fst
        ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (v, 0)).symm
    · exact TotalSpace.mk_inj.mpr <| congrArg Prod.snd
        ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (v, 0)).symm

/-- Inclusion of the second summand into the variable-rank Whitney sum. -/
noncomputable def whitneyInr (A D : FiniteRankAtlas 𝕜 X) : D ⟶ whitneySum A D where
  fiberMap x := (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toLinearMap.comp
    (LinearMap.inr 𝕜 (A.Fiber x) (D.Fiber x))
  continuous_totalSpaceMap := by
    refine continuous_mk_whitneySum_iff.2
      ⟨((VariableRankBundle.continuous_zeroSection A).comp
          (VariableRankBundle.continuous_proj D)).congr fun ⟨x, w⟩ => ?_,
        continuous_id.congr fun ⟨x, w⟩ => ?_⟩
    · exact TotalSpace.mk_inj.mpr <| congrArg Prod.fst
        ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (0, w)).symm
    · exact TotalSpace.mk_inj.mpr <| congrArg Prod.snd
        ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (0, w)).symm

/-- Fibrewise linear action of `whitneyFst A D` at `x : X`. -/
@[simp] theorem fiberMap_whitneyFst (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyFst A D).fiberMap x =
      (LinearMap.fst 𝕜 (A.Fiber x) (D.Fiber x)).comp
        (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearMap := (rfl)

/-- Fibrewise linear action of `whitneySnd A D` at `x : X`. -/
@[simp] theorem fiberMap_whitneySnd (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneySnd A D).fiberMap x =
      (LinearMap.snd 𝕜 (A.Fiber x) (D.Fiber x)).comp
        (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearMap := (rfl)

/-- Fibrewise linear action of `whitneyInl A D` at `x : X`. -/
@[simp] theorem fiberMap_whitneyInl (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyInl A D).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toLinearMap.comp
        (LinearMap.inl 𝕜 (A.Fiber x) (D.Fiber x)) := (rfl)

/-- Fibrewise linear action of `whitneyInr A D` at `x : X`. -/
@[simp] theorem fiberMap_whitneyInr (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyInr A D).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toLinearMap.comp
        (LinearMap.inr 𝕜 (A.Fiber x) (D.Fiber x)) := (rfl)

/-- Composing the first inclusion with the first projection is the identity on `A`. -/
@[reassoc (attr := simp)] theorem whitneyInl_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneyFst A D = 𝟙 A := by
  apply VariableRankBundle.hom_ext; intro x; apply LinearMap.ext; intro v
  exact congrArg Prod.fst
    ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (v, 0))

/-- Composing the first inclusion with the second projection is zero. -/
@[reassoc (attr := simp)] theorem whitneyInl_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneySnd A D = 0 := by
  apply VariableRankBundle.hom_ext; intro x; apply LinearMap.ext; intro v
  exact congrArg Prod.snd
    ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (v, 0))

/-- Composing the second inclusion with the first projection is zero. -/
@[reassoc (attr := simp)] theorem whitneyInr_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneyFst A D = 0 := by
  apply VariableRankBundle.hom_ext; intro x; apply LinearMap.ext; intro w
  exact congrArg Prod.fst
    ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (0, w))

/-- Composing the second inclusion with the second projection is the identity on `D`. -/
@[reassoc (attr := simp)] theorem whitneyInr_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneySnd A D = 𝟙 D := by
  apply VariableRankBundle.hom_ext; intro x; apply LinearMap.ext; intro w
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

/-- Underlying object of `whitneyBicone A D`. -/
@[simp] theorem whitneyBicone_pt (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).pt = whitneySum A D := (rfl)

/-- First projection of `whitneyBicone A D`. -/
@[simp] theorem whitneyBicone_fst (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).fst = whitneyFst A D := (rfl)

/-- Second projection of `whitneyBicone A D`. -/
@[simp] theorem whitneyBicone_snd (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).snd = whitneySnd A D := (rfl)

/-- First inclusion of `whitneyBicone A D`. -/
@[simp] theorem whitneyBicone_inl (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).inl = whitneyInl A D := (rfl)

/-- Second inclusion of `whitneyBicone A D`. -/
@[simp] theorem whitneyBicone_inr (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).inr = whitneyInr A D := (rfl)

/-- The two coordinate-block projections and inclusions resolve the identity on `whitneySum A D`. -/
@[simp] theorem whitney_total (A D : FiniteRankAtlas 𝕜 X) :
    whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D =
      𝟙 (whitneySum A D) := by
  apply VariableRankBundle.hom_ext; intro x; apply LinearMap.ext; intro v
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

/-- Rank additivity for the categorical binary biproduct `A ⊞ D`. -/
@[simp] theorem rank_biprod (A D : FiniteRankAtlas 𝕜 X) :
    (A ⊞ D).rank = A.rank + D.rank :=
  (biprod.uniqueUpToIso A D (whitneyBiconeIsBilimit A D)).symm.variableRankBundle_rank_eq

/-- Rank additivity for finite categorical biproducts `⨁ f`. -/
@[simp] theorem rank_biproduct.{w} {J : Type w} [Fintype J] (f : J → FiniteRankAtlas 𝕜 X) :
    (⨁ f).rank = ∑ j, (f j).rank := by
  suffices ∀ (n : ℕ) {K : Type w} [Fintype K] (g : K → FiniteRankAtlas 𝕜 X),
      Fintype.card K = n → (⨁ g).rank = ∑ k, (g k).rank from
    this (Fintype.card J) f rfl
  intro n; induction n with
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
      rw [Fintype.card_subtype_compl (· = k₀), h1, hK]; omega
    calc
      (⨁ g).rank = (g k₀ ⊞ ⨁ Subtype.restrict (· ≠ k₀) g).rank :=
        (biproductSubtypeNeIso g k₀).variableRankBundle_rank_eq
      _ = (g k₀).rank + (⨁ Subtype.restrict (· ≠ k₀) g).rank := rank_biprod _ _
      _ = (g k₀).rank + ∑ k : {k : K // k ≠ k₀}, (g k.val).rank := by
        rw [ih (Subtype.restrict (· ≠ k₀) g) hcard]; rfl
      _ = ∑ k, (g k).rank := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀)]; congr 1
        refine Finset.sum_bij (fun k _ => k.val)
          (fun k _ => Finset.mem_erase.2 ⟨k.property, Finset.mem_univ _⟩)
          (fun _ _ _ _ h => Subtype.ext h)
          (fun k hk => ⟨⟨k, (Finset.mem_erase.1 hk).1⟩, Finset.mem_univ _, rfl⟩)
          (fun _ _ => rfl)

end WhitneySum

section UniversalProperty

variable {A A' A'' D D' D'' C E : FiniteRankAtlas 𝕜 X}

/-- Pair two variable-rank bundle morphisms with common source into the concrete Whitney sum. -/
noncomputable def whitneyLift (f : E ⟶ A) (g : E ⟶ D) : E ⟶ whitneySum A D :=
  f ≫ whitneyInl A D + g ≫ whitneyInr A D

/-- Explicit expansion of `whitneyLift f g` in terms of `whitneyInl` and `whitneyInr`. -/
theorem whitneyLift_def (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g = f ≫ whitneyInl A D + g ≫ whitneyInr A D := (rfl)

/-- Composing `whitneyLift f g` with the first projection recovers `f`. -/
@[reassoc (attr := simp)] theorem whitneyLift_fst (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g ≫ whitneyFst A D = f := by
  simp [whitneyLift, Preadditive.add_comp]

/-- Composing `whitneyLift f g` with the second projection recovers `g`. -/
@[reassoc (attr := simp)] theorem whitneyLift_snd (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g ≫ whitneySnd A D = g := by
  simp [whitneyLift, Preadditive.add_comp]

/-- Every morphism into a Whitney sum is the pairing of its two projections. -/
theorem eq_whitneyLift (h : E ⟶ whitneySum A D) :
    h = whitneyLift (h ≫ whitneyFst A D) (h ≫ whitneySnd A D) := by
  nth_rw 1 [← Category.comp_id h, ← whitney_total]
  simp only [whitneyLift, Preadditive.comp_add, Category.assoc]

/-- Morphisms into a Whitney sum are determined by their two projections. -/
theorem whitneySum_hom_ext {h₁ h₂ : E ⟶ whitneySum A D}
    (hfst : h₁ ≫ whitneyFst A D = h₂ ≫ whitneyFst A D)
    (hsnd : h₁ ≫ whitneySnd A D = h₂ ≫ whitneySnd A D) : h₁ = h₂ := by
  rw [eq_whitneyLift h₁, eq_whitneyLift h₂, hfst, hsnd]

/-- Precomposition distributes into `whitneyLift`. -/
@[reassoc] theorem comp_whitneyLift (h : C ⟶ E) (f : E ⟶ A) (g : E ⟶ D) :
    h ≫ whitneyLift f g = whitneyLift (h ≫ f) (h ≫ g) := by
  simp only [whitneyLift, Preadditive.comp_add, Category.assoc]

/-- Pairing the two canonical projections gives the identity on `whitneySum A D`. -/
@[simp] theorem whitneyLift_fst_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyLift (whitneyFst A D) (whitneySnd A D) = 𝟙 (whitneySum A D) :=
  whitney_total A D

/-- Fibrewise linear action of `whitneyLift f g` at `x : X`. -/
@[simp] theorem fiberMap_whitneyLift (f : E ⟶ A) (g : E ⟶ D) (x : X) :
    (whitneyLift f g).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toLinearMap.comp
        ((f.fiberMap x).prod (g.fiberMap x)) := by
  apply LinearMap.ext; intro v
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)
  exact (e.symm.map_add (f.fiberMap x v, 0) (0, g.fiberMap x v)).symm.trans
    (congrArg e.symm (Prod.ext (add_zero _) (zero_add _)))

/-- Coordinate blocks of `(whitneyLift f g).fiberMap x v` under `splitCoords`. -/
theorem splitCoords_fiberMap_whitneyLift (f : E ⟶ A) (g : E ⟶ D) (x : X) (v : E.Fiber x) :
    splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) ((whitneyLift f g).fiberMap x v) =
      (f.fiberMap x v, g.fiberMap x v) := by
  rw [DFunLike.congr_fun (fiberMap_whitneyLift f g x) v]
  exact (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply
    (f.fiberMap x v, g.fiberMap x v)

/-- Copair two variable-rank bundle morphisms with common target out of the concrete Whitney sum. -/
noncomputable def whitneyDesc (f : A ⟶ E) (g : D ⟶ E) : whitneySum A D ⟶ E :=
  whitneyFst A D ≫ f + whitneySnd A D ≫ g

/-- Explicit expansion of `whitneyDesc f g` in terms of `whitneyFst` and `whitneySnd`. -/
theorem whitneyDesc_def (f : A ⟶ E) (g : D ⟶ E) :
    whitneyDesc f g = whitneyFst A D ≫ f + whitneySnd A D ≫ g := (rfl)

/-- Restricting `whitneyDesc f g` along `whitneyInl` recovers `f`. -/
@[reassoc (attr := simp)] theorem whitneyInl_desc (f : A ⟶ E) (g : D ⟶ E) :
    whitneyInl A D ≫ whitneyDesc f g = f := by simp [whitneyDesc, Preadditive.comp_add]

/-- Restricting `whitneyDesc f g` along `whitneyInr` recovers `g`. -/
@[reassoc (attr := simp)] theorem whitneyInr_desc (f : A ⟶ E) (g : D ⟶ E) :
    whitneyInr A D ≫ whitneyDesc f g = g := by simp [whitneyDesc, Preadditive.comp_add]

/-- Composing a pairing `whitneyLift f g` with a copairing `whitneyDesc h k`. -/
@[reassoc (attr := simp)] theorem whitneyLift_desc (f : E ⟶ A) (g : E ⟶ D) (h : A ⟶ C) (k : D ⟶ C) :
    whitneyLift f g ≫ whitneyDesc h k = f ≫ h + g ≫ k := by
  simp [whitneyLift, whitneyDesc, Preadditive.add_comp, Preadditive.comp_add]

/-- Every morphism out of a Whitney sum is the copairing of its two restrictions. -/
theorem eq_whitneyDesc (h : whitneySum A D ⟶ E) :
    h = whitneyDesc (whitneyInl A D ≫ h) (whitneyInr A D ≫ h) := by
  nth_rw 1 [← Category.id_comp h, ← whitney_total]
  simp only [whitneyDesc, Preadditive.add_comp, Category.assoc]

/-- Morphisms out of a Whitney sum are determined by their restrictions to the two summands. -/
theorem whitneySum_hom_ext' {h₁ h₂ : whitneySum A D ⟶ E}
    (hinl : whitneyInl A D ≫ h₁ = whitneyInl A D ≫ h₂)
    (hinr : whitneyInr A D ≫ h₁ = whitneyInr A D ≫ h₂) : h₁ = h₂ := by
  rw [eq_whitneyDesc h₁, eq_whitneyDesc h₂, hinl, hinr]

/-- Postcomposition distributes into `whitneyDesc`. -/
@[reassoc] theorem whitneyDesc_comp (f : A ⟶ E) (g : D ⟶ E) (h : E ⟶ C) :
    whitneyDesc f g ≫ h = whitneyDesc (f ≫ h) (g ≫ h) := by
  simp only [whitneyDesc, Preadditive.add_comp, Category.assoc]

/-- Copairing the two canonical inclusions gives the identity on `whitneySum A D`. -/
@[simp] theorem whitneyDesc_inl_inr (A D : FiniteRankAtlas 𝕜 X) :
    whitneyDesc (whitneyInl A D) (whitneyInr A D) = 𝟙 (whitneySum A D) :=
  whitney_total A D

/-- Fibrewise linear action of `whitneyDesc f g` at `x : X`. -/
@[simp] theorem fiberMap_whitneyDesc (f : A ⟶ E) (g : D ⟶ E) (x : X) :
    (whitneyDesc f g).fiberMap x =
      ((f.fiberMap x).coprod (g.fiberMap x)).comp
        (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearMap := by
  apply LinearMap.ext; intro _; rfl

/-- Pointwise formula for `(whitneyDesc f g).fiberMap x` in terms of `splitCoords`. -/
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

/-- Explicit expansion of `whitneyMap f g` as a `whitneyLift`. -/
theorem whitneyMap_def (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g = whitneyLift (whitneyFst A D ≫ f) (whitneySnd A D ≫ g) := (rfl)

/-- First projection of `whitneyMap f g`. -/
@[reassoc (attr := simp)] theorem whitneyMap_fst (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ whitneyFst A' D' = whitneyFst A D ≫ f := whitneyLift_fst _ _

/-- Second projection of `whitneyMap f g`. -/
@[reassoc (attr := simp)] theorem whitneyMap_snd (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ whitneySnd A' D' = whitneySnd A D ≫ g := whitneyLift_snd _ _

/-- Naturality of `whitneyInl` with respect to `whitneyMap`. -/
@[reassoc (attr := simp)] theorem whitneyInl_map (f : A ⟶ A') (g : D ⟶ D') :
    whitneyInl A D ≫ whitneyMap f g = f ≫ whitneyInl A' D' :=
  whitneySum_hom_ext (by simp) (by simp)

/-- Naturality of `whitneyInr` with respect to `whitneyMap`. -/
@[reassoc (attr := simp)] theorem whitneyInr_map (f : A ⟶ A') (g : D ⟶ D') :
    whitneyInr A D ≫ whitneyMap f g = g ≫ whitneyInr A' D' :=
  whitneySum_hom_ext (by simp) (by simp)

/-- `whitneyMap` preserves identity morphisms. -/
@[simp] theorem whitneyMap_id (A D : FiniteRankAtlas 𝕜 X) :
    whitneyMap (𝟙 A) (𝟙 D) = 𝟙 (whitneySum A D) := by simp [whitneyMap_def]

/-- `whitneyMap` sends a pair of zero morphisms to zero. -/
@[simp] theorem whitneyMap_zero (A A' D D' : FiniteRankAtlas 𝕜 X) :
    whitneyMap (0 : A ⟶ A') (0 : D ⟶ D') = 0 :=
  whitneySum_hom_ext (by simp) (by simp)

/-- `whitneyMap` preserves composition in both arguments. -/
@[simp] theorem whitneyMap_comp (f₁ : A ⟶ A') (f₂ : A' ⟶ A'') (g₁ : D ⟶ D') (g₂ : D' ⟶ D'') :
    whitneyMap (f₁ ≫ f₂) (g₁ ≫ g₂) = whitneyMap f₁ g₁ ≫ whitneyMap f₂ g₂ :=
  whitneySum_hom_ext (by simp) (by simp)

/-- Fibrewise linear action of `whitneyMap f g` at `x : X`. -/
@[simp] theorem fiberMap_whitneyMap (f : A ⟶ A') (g : D ⟶ D') (x : X) :
    (whitneyMap f g).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A'.rank x) (D'.rank x)).symm.toLinearMap.comp
        (((f.fiberMap x).prodMap (g.fiberMap x)).comp
          (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearMap) := by
  simp only [whitneyMap_def, fiberMap_whitneyLift, VariableRankBundle.fiberMap_comp,
    fiberMap_whitneyFst, fiberMap_whitneySnd]
  apply LinearMap.ext; intro _; rfl

/-- Coordinate blocks of `(whitneyMap f g).fiberMap x v` under `splitCoords`. -/
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

/-- Forward morphism of `whitneyMapIso e₁ e₂`. -/
@[simp] theorem whitneyMapIso_hom (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).hom = whitneyMap e₁.hom e₂.hom := (rfl)

/-- Inverse morphism of `whitneyMapIso e₁ e₂`. -/
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

/-- Forward morphism of `whitneyCommIso A D`. -/
@[simp] theorem whitneyCommIso_hom (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyCommIso A D).hom = whitneyLift (whitneySnd A D) (whitneyFst A D) := (rfl)

/-- Inverse morphism of `whitneyCommIso A D`. -/
@[simp] theorem whitneyCommIso_inv (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyCommIso A D).inv = whitneyLift (whitneySnd D A) (whitneyFst D A) := (rfl)

/-- Naturality of the symmetry isomorphism `whitneyCommIso` with respect to `whitneyMap`. -/
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

/-- Forward morphism of `whitneyAssocIso A D C`. -/
@[simp] theorem whitneyAssocIso_hom (A D C : FiniteRankAtlas 𝕜 X) :
    (whitneyAssocIso A D C).hom =
      whitneyLift (whitneyFst _ _ ≫ whitneyFst A D)
        (whitneyLift (whitneyFst _ _ ≫ whitneySnd A D) (whitneySnd _ _)) := (rfl)

/-- Inverse morphism of `whitneyAssocIso A D C`. -/
@[simp] theorem whitneyAssocIso_inv (A D C : FiniteRankAtlas 𝕜 X) :
    (whitneyAssocIso A D C).inv =
      whitneyLift (whitneyLift (whitneyFst _ _) (whitneySnd _ _ ≫ whitneyFst D C))
        (whitneySnd _ _ ≫ whitneySnd D C) := (rfl)

/-- Naturality of the associativity isomorphism `whitneyAssocIso` with respect to `whitneyMap`. -/
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

/-- Forward morphism of `whitneyZeroLeftIso A`. -/
@[simp] theorem whitneyZeroLeftIso_hom (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroLeftIso A).hom = whitneySnd (trivial 𝕜 X 0) A := (rfl)

/-- Inverse morphism of `whitneyZeroLeftIso A`. -/
@[simp] theorem whitneyZeroLeftIso_inv (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroLeftIso A).inv = whitneyInr (trivial 𝕜 X 0) A := (rfl)

/-- Naturality of `whitneyZeroLeftIso` with respect to `whitneyMap`. -/
@[reassoc] theorem whitneyMap_zeroLeftIso_hom {A A' : FiniteRankAtlas 𝕜 X}
    (g : trivial 𝕜 X 0 ⟶ trivial 𝕜 X 0) (f : A ⟶ A') :
    whitneyMap g f ≫ (whitneyZeroLeftIso A').hom = (whitneyZeroLeftIso A).hom ≫ f :=
  whitneyMap_snd g f

/-- Right unit isomorphism for Whitney sum with the trivial rank-zero atlas. -/
noncomputable def whitneyZeroRightIso (A : FiniteRankAtlas 𝕜 X) :
    whitneySum A (trivial 𝕜 X 0) ≅ A where
  hom := whitneyFst A (trivial 𝕜 X 0)
  inv := whitneyInl A (trivial 𝕜 X 0)
  hom_inv_id := whitneySum_hom_ext' (by simp) (isZero_trivial_zero.eq_of_src _ _)
  inv_hom_id := whitneyInl_fst A (trivial 𝕜 X 0)

/-- Forward morphism of `whitneyZeroRightIso A`. -/
@[simp] theorem whitneyZeroRightIso_hom (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroRightIso A).hom = whitneyFst A (trivial 𝕜 X 0) := (rfl)

/-- Inverse morphism of `whitneyZeroRightIso A`. -/
@[simp] theorem whitneyZeroRightIso_inv (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroRightIso A).inv = whitneyInl A (trivial 𝕜 X 0) := (rfl)

/-- Naturality of `whitneyZeroRightIso` with respect to `whitneyMap`. -/
@[reassoc] theorem whitneyMap_zeroRightIso_hom {A A' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : trivial 𝕜 X 0 ⟶ trivial 𝕜 X 0) :
    whitneyMap f g ≫ (whitneyZeroRightIso A').hom = (whitneyZeroRightIso A).hom ≫ f :=
  whitneyMap_fst f g

private theorem continuous_trivialAdd_hom (r₁ r₂ : LocallyConstant X ℕ) :
    Continuous (fun p : TotalSpace Unit (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).Fiber =>
      (⟨p.proj, p.snd⟩ : TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber)) := by
  let WT := whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)
  have hproj := VariableRankBundle.continuous_proj WT
  have hfst_snd := continuous_mk_whitneySum_iff.1 (continuous_id (X := TotalSpace Unit WT.Fiber))
  have hc₁ := (continuous_mk_trivial_iff (r := r₁) hproj _).1 hfst_snd.1
  have hc₂ := (continuous_mk_trivial_iff (r := r₂) hproj _).1 hfst_snd.2
  refine (continuous_mk_trivial_iff (r := r₁ + r₂) hproj
    (fun p => (p.snd : (trivial 𝕜 X (r₁ + r₂)).Fiber p.proj))).2 fun n => ?_
  let S := {y : TotalSpace Unit WT.Fiber // (r₁ + r₂) y.proj = n}
  apply continuous_of_cover_nhds
    (s := fun pq : ℕ × ℕ => {y : S | r₁ y.val.proj = pq.1 ∧ r₂ y.val.proj = pq.2})
  · exact fun y => ⟨(r₁ y.val.proj, r₂ y.val.proj),
      (((r₁.isLocallyConstant.isOpen_fiber _).preimage
          (hproj.comp continuous_subtypeVal)).inter
        ((r₂.isLocallyConstant.isOpen_fiber _).preimage
          (hproj.comp continuous_subtypeVal))).mem_nhds ⟨rfl, rfl⟩⟩
  · rintro ⟨p, q⟩
    rw [continuousOn_iff_continuous_domRestrict]
    by_cases hpq : p + q = n
    · let g₁ : {y : S // r₁ y.val.proj = p ∧ r₂ y.val.proj = q} →
          {z : TotalSpace Unit WT.Fiber // r₁ z.proj = p} := fun y => ⟨y.val.val, y.property.1⟩
      let g₂ : {y : S // r₁ y.val.proj = p ∧ r₂ y.val.proj = q} →
          {z : TotalSpace Unit WT.Fiber // r₂ z.proj = q} := fun y => ⟨y.val.val, y.property.2⟩
      have hg₁ : Continuous g₁ := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
      have hg₂ : Continuous g₂ := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
      have hjoined :=
        (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜) (finCongr hpq)).continuous.comp
          ((splitCoords (𝕜 := 𝕜) (M := 𝕜) p q).symm.continuous.comp
            (((hc₁ p).comp hg₁).prodMk ((hc₂ q).comp hg₂)))
      exact hjoined.congr fun y =>
        (congrArg (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜) (finCongr hpq))
          (splitCoords_symm_cast (𝕜 := 𝕜) y.property.1.symm y.property.2.symm
            (splitCoords (𝕜 := 𝕜) (r₁ y.val.val.proj) (r₂ y.val.val.proj) y.val.val.snd).1
            (splitCoords (𝕜 := 𝕜) (r₁ y.val.val.proj) (r₂ y.val.val.proj) y.val.val.snd).2)).trans
                <|
          funext fun i =>
            congrFun ((splitCoords (𝕜 := 𝕜) (r₁ y.val.val.proj)
                (r₂ y.val.val.proj)).symm_apply_apply
              y.val.val.snd) (Fin.cast y.val.property.symm i)
    · have : IsEmpty {y : S // r₁ y.val.proj = p ∧ r₂ y.val.proj = q} :=
        ⟨fun y => hpq ((congrArg₂ (· + ·) y.property.1.symm y.property.2.symm).trans
            y.val.property)⟩
      exact continuous_of_discreteTopology

private theorem continuous_trivialAdd_inv (r₁ r₂ : LocallyConstant X ℕ) :
    Continuous (fun p : TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber =>
      (⟨p.proj, p.snd⟩ :
        TotalSpace Unit (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).Fiber)) := by
  have hproj := VariableRankBundle.continuous_proj (trivial 𝕜 X (r₁ + r₂))
  have hc := (continuous_mk_trivial_iff (r := r₁ + r₂) hproj _).1
    (continuous_id (X := TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber))
  refine (continuous_mk_whitneySum_iff
    (A := trivial 𝕜 X r₁) (D := trivial 𝕜 X r₂)
    (b := fun p : TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber => p.proj)
    (s := fun p => (p.snd : (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).Fiber p.proj))).2 ⟨?_,
        ?_⟩
  · refine (continuous_mk_trivial_iff (r := r₁) hproj _).2 fun p => ?_
    let S := {y : TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber // r₁ y.proj = p}
    refine continuous_of_cover_nhds (s := fun q : ℕ => {y : S | r₂ y.val.proj = q})
      (fun y => ⟨r₂ y.val.proj, ((r₂.isLocallyConstant.isOpen_fiber _).preimage
        (hproj.comp continuous_subtypeVal)).mem_nhds rfl⟩)
      fun q => ?_
    rw [continuousOn_iff_continuous_domRestrict]
    let g : {y : S // r₂ y.val.proj = q} →
        {z : TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber // (r₁ + r₂) z.proj = p + q} :=
      fun y => ⟨y.val.val, congrArg₂ (· + ·) y.val.property y.property⟩
    have hg : Continuous g := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
    exact (((continuous_fst.comp (splitCoords (𝕜 := 𝕜) (M := 𝕜) p q).continuous).comp
      ((hc (p + q)).comp hg)).congr
      fun y => splitCoords_cast_fst y.val.property.symm (g y).property.symm y.val.val.snd)
  · refine (continuous_mk_trivial_iff (r := r₂) hproj _).2 fun q => ?_
    let S := {y : TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber // r₂ y.proj = q}
    refine continuous_of_cover_nhds (s := fun p : ℕ => {y : S | r₁ y.val.proj = p})
      (fun y => ⟨r₁ y.val.proj, ((r₁.isLocallyConstant.isOpen_fiber _).preimage
        (hproj.comp continuous_subtypeVal)).mem_nhds rfl⟩)
      fun p => ?_
    rw [continuousOn_iff_continuous_domRestrict]
    let g : {y : S // r₁ y.val.proj = p} →
        {z : TotalSpace Unit (trivial 𝕜 X (r₁ + r₂)).Fiber // (r₁ + r₂) z.proj = p + q} :=
      fun y => ⟨y.val.val, congrArg₂ (· + ·) y.property y.val.property⟩
    have hg : Continuous g := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
    exact (((continuous_snd.comp (splitCoords (𝕜 := 𝕜) (M := 𝕜) p q).continuous).comp
      ((hc (p + q)).comp hg)).congr
      fun y => splitCoords_cast_snd y.val.property.symm (g y).property.symm y.val.val.snd)

/-- Canonical isomorphism identifying the Whitney sum of two trivial variable-rank atlases with the
trivial atlas of the summed rank, acting as the identity on every coordinate fibre. -/
noncomputable def trivialAddIso (r₁ r₂ : LocallyConstant X ℕ) :
    whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂) ≅ trivial 𝕜 X (r₁ + r₂) :=
  VariableRankBundle.isoMk
    (fun x : X => (LinearEquiv.refl 𝕜 (Fin (r₁ x + r₂ x) → 𝕜) :
      (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).Fiber x ≃ₗ[𝕜]
        (trivial 𝕜 X (r₁ + r₂)).Fiber x))
    (continuous_trivialAdd_hom r₁ r₂) (continuous_trivialAdd_inv r₁ r₂)

/-- Forward fibrewise action of `trivialAddIso r₁ r₂` is the identity. -/
@[simp] theorem fiberMap_trivialAddIso_hom (r₁ r₂ : LocallyConstant X ℕ) (x : X) :
    (trivialAddIso (𝕜 := 𝕜) r₁ r₂).hom.fiberMap x = LinearMap.id :=
  VariableRankBundle.fiberMap_isoMk_hom _ _ _ x

/-- Inverse fibrewise action of `trivialAddIso r₁ r₂` is the identity. -/
@[simp] theorem fiberMap_trivialAddIso_inv (r₁ r₂ : LocallyConstant X ℕ) (x : X) :
    (trivialAddIso (𝕜 := 𝕜) r₁ r₂).inv.fiberMap x = LinearMap.id :=
  VariableRankBundle.fiberMap_isoMk_inv _ _ _ x

end Coherence

section FiberedProduct

private noncomputable def fiberedProdToFun (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj} :=
  ⟨((whitneyFst A D).totalSpaceMap p, (whitneySnd A D).totalSpaceMap p), by simp⟩

private noncomputable def fiberedProdInvFun (A D : FiniteRankAtlas 𝕜 X)
    (pq : {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj}) :
    TotalSpace Unit (whitneySum A D).Fiber :=
  ⟨pq.val.1.proj,
    (splitCoords (𝕜 := 𝕜) (A.rank pq.val.1.proj) (D.rank pq.val.1.proj)).symm
      (pq.val.1.snd, cast (congrArg D.Fiber pq.property.symm) pq.val.2.snd)⟩

/-- Global homeomorphism between the reconstructed total space of `whitneySum A D` and the
topological fibered product over `X` of the reconstructed total spaces of `A` and `D`. -/
noncomputable def whitneySumFiberedProdHomeomorph (A D : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit (whitneySum A D).Fiber ≃ₜ
      {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj} where
  toFun := fiberedProdToFun A D
  invFun := fiberedProdInvFun A D
  left_inv := fun ⟨x, v⟩ => by
    have hpair : fiberedProdToFun A D ⟨x, v⟩ =
        ⟨(⟨x, (whitneyFst A D).fiberMap x v⟩, ⟨x, (whitneySnd A D).fiberMap x v⟩), rfl⟩ :=
      Subtype.ext (Prod.ext ((whitneyFst A D).totalSpaceMap_mk x v)
        ((whitneySnd A D).totalSpaceMap_mk x v))
    exact (congrArg (fiberedProdInvFun A D) hpair).trans
      (TotalSpace.mk_inj.mpr
        ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).symm_apply_apply v))
  right_inv := by
    rintro ⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, h⟩; cases h
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
    refine continuous_mk_whitneySum_iff.2
      ⟨(continuous_fst.comp continuous_subtypeVal).congr fun pq => ?_,
        (continuous_snd.comp continuous_subtypeVal).congr fun pq => ?_⟩
    · rcases pq with ⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, h⟩; cases h
      exact TotalSpace.mk_inj.mpr (congrArg Prod.fst
        ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x₁) (D.rank x₁)).apply_symm_apply (u, w))).symm
    · rcases pq with ⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, h⟩; cases h
      exact TotalSpace.mk_inj.mpr (congrArg Prod.snd
        ((splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x₁) (D.rank x₁)).apply_symm_apply (u, w))).symm

/-- First component of `whitneySumFiberedProdHomeomorph A D` is `(whitneyFst A D).totalSpaceMap`. -/
@[simp] theorem whitneySumFiberedProdHomeomorph_apply_fst (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    (whitneySumFiberedProdHomeomorph A D p).val.1 = (whitneyFst A D).totalSpaceMap p := (rfl)

/-- Second component of `whitneySumFiberedProdHomeomorph A D` is
`(whitneySnd A D).totalSpaceMap`. -/
@[simp] theorem whitneySumFiberedProdHomeomorph_apply_snd (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    (whitneySumFiberedProdHomeomorph A D p).val.2 = (whitneySnd A D).totalSpaceMap p := (rfl)

/-- `whitneySumFiberedProdHomeomorph` intertwines `whitneyMap f g` on total spaces with the
componentwise action `(f.totalSpaceMap, g.totalSpaceMap)` on the fibered product over `X`. -/
theorem whitneySumFiberedProdHomeomorph_naturality {A A' D D' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') (p : TotalSpace Unit (whitneySum A D).Fiber) :
    whitneySumFiberedProdHomeomorph A' D' ((whitneyMap f g).totalSpaceMap p) =
      ⟨(f.totalSpaceMap (whitneySumFiberedProdHomeomorph A D p).val.1,
          g.totalSpaceMap (whitneySumFiberedProdHomeomorph A D p).val.2),
        by simp⟩ := by
  rcases p with ⟨x, v⟩
  let w : (whitneySum A' D').Fiber x := (whitneyMap f g).fiberMap x v
  rw [(whitneyMap f g).totalSpaceMap_mk x v]
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
