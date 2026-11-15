/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Trivial
public import TauCeti.Topology.VectorBundle.FiniteRank.LocallyConstant
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct

/-!
# Whitney sums and binary biproducts of variable-rank bundle atlases

Given two variable-rank bundle atlases `A D : FiniteRankAtlas 𝕜 X`, their Whitney sum
`whitneySum A D` has locally constant rank `A.rank + D.rank`. On a total-rank stratum
`{x : X // (A.rank + D.rank) x = n}`, the summand ranks `(A.rank x, D.rank x)` need not be
constant, so `whitneyStratumCore` partitions the stratum along the locally constant rank-splitting
map `whitneyRankSplit` into clopen pieces `{p : ℕ × ℕ // p.1 + p.2 = n}`, forms the constant-rank
`FiniteRankBundleCore.whitneySum` of the pulled-back summand cores on each piece, and glues them
into a single point-indexed core of rank `n` via `FiniteRankBundleCore.ofLocallyConstant`.

Because `(A.rank + D.rank) x` is definitionally `A.rank x + D.rank x`, the fibre at `x` is
`Fin (A.rank x + D.rank x) → 𝕜`, and the four canonical morphisms (`whitneyFst`, `whitneySnd`,
`whitneyInl`, `whitneyInr`) act on each fibre through `TauCeti.splitCoords` with no rank casts.
`whitneyBiconeIsBilimit` establishes the bilimit property via `isBinaryBilimitOfTotal`, providing
`HasBinaryBiproducts (FiniteRankAtlas 𝕜 X)` and, via
`TauCeti.hasFiniteBiproducts_of_hasBinaryBiproducts`, `HasFiniteBiproducts (FiniteRankAtlas 𝕜 X)`.
This covers unbounded ranks, disconnected or noncompact bases, empty bases, and arbitrary
nontrivially normed scalar fields (completeness is not needed).

Following the constant-rank interface of `TauCeti.FiniteRankBundleCore`, the universal property is
accompanied by concrete pairing (`whitneyLift`), copairing (`whitneyDesc`), functoriality
(`whitneyMap`, `whitneyMapIso`), symmetry, associativity, and unit coherence isomorphisms
(`whitneyCommIso`, `whitneyAssocIso`, `whitneyZeroLeftIso`, `whitneyZeroRightIso`), an isomorphism
`whitneyTrivialIso` identifying the Whitney sum of two trivial variable-rank atlases with
`trivial 𝕜 (r₁ + r₂)`, and the total-space comparison `whitneySumTotalSpaceHomeomorph` identifying
`TotalSpace Unit (whitneySum A D).Fiber` over `X` with the fibre product
`{q : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // q.1.proj = q.2.proj}`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* M. F. Atiyah, *K-Theory*, §1.1–1.2.
* M. Karoubi, *K-Theory: An Introduction*, Chapter I, §§1–2.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits Set Topology

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

section Construction

/-- On the rank-`n` stratum of `A.rank + D.rank`, record the locally constant pair of summand ranks
`(A.rank x, D.rank x)` summing to `n`. -/
def whitneyRankSplit (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    LocallyConstant {x : X // (A.rank + D.rank) x = n} {p : ℕ × ℕ // p.1 + p.2 = n} where
  toFun x := ⟨(A.rank x.1, D.rank x.1), x.2⟩
  isLocallyConstant := (IsLocallyConstant.iff_eventually_eq _).2 fun x => by
    have hA : ∀ᶠ y : {x : X // (A.rank + D.rank) x = n} in 𝓝 x, A.rank y.1 = A.rank x.1 :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        ((A.rank.isLocallyConstant.isOpen_fiber (A.rank x.1)).mem_nhds rfl)
    have hD : ∀ᶠ y : {x : X // (A.rank + D.rank) x = n} in 𝓝 x, D.rank y.1 = D.rank x.1 :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        ((D.rank.isLocallyConstant.isOpen_fiber (D.rank x.1)).mem_nhds rfl)
    exact (hA.and hD).mono fun _ ⟨hyA, hyD⟩ => Subtype.ext (Prod.ext hyA hyD)

@[simp]
theorem whitneyRankSplit_apply (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (x : {x : X // (A.rank + D.rank) x = n}) :
    whitneyRankSplit A D n x = ⟨(A.rank x.1, D.rank x.1), x.2⟩ := (rfl)

private theorem whitneyFstInclusion_mem (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (p : {p : ℕ × ℕ // p.1 + p.2 = n})
    (z : {x : {x : X // (A.rank + D.rank) x = n} // whitneyRankSplit A D n x = p}) :
    A.rank z.1.1 = p.1.1 :=
  congrArg (fun q => q.1.1) ((whitneyRankSplit_apply A D n z.1).symm.trans z.2)

/-- Continuous inclusion from the `p`-piece of the rank-`n` stratum of `A.rank + D.rank` into the
rank-`p.1.1` stratum of `A`. -/
def whitneyFstInclusion (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (p : {p : ℕ × ℕ // p.1 + p.2 = n}) :
    C({x : {x : X // (A.rank + D.rank) x = n} // whitneyRankSplit A D n x = p},
      {x : X // A.rank x = p.1.1}) where
  toFun z := ⟨z.1.1, whitneyFstInclusion_mem A D n p z⟩
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (whitneyFstInclusion_mem A D n p)

@[simp]
theorem coe_whitneyFstInclusion_apply (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (p : {p : ℕ × ℕ // p.1 + p.2 = n})
    (z : {x : {x : X // (A.rank + D.rank) x = n} // whitneyRankSplit A D n x = p}) :
    (whitneyFstInclusion A D n p z).1 = z.1.1 := (rfl)

private theorem whitneySndInclusion_mem (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (p : {p : ℕ × ℕ // p.1 + p.2 = n})
    (z : {x : {x : X // (A.rank + D.rank) x = n} // whitneyRankSplit A D n x = p}) :
    D.rank z.1.1 = p.1.2 :=
  congrArg (fun q => q.1.2) ((whitneyRankSplit_apply A D n z.1).symm.trans z.2)

/-- Continuous inclusion from the `p`-piece of the rank-`n` stratum of `A.rank + D.rank` into the
rank-`p.1.2` stratum of `D`. -/
def whitneySndInclusion (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (p : {p : ℕ × ℕ // p.1 + p.2 = n}) :
    C({x : {x : X // (A.rank + D.rank) x = n} // whitneyRankSplit A D n x = p},
      {x : X // D.rank x = p.1.2}) where
  toFun z := ⟨z.1.1, whitneySndInclusion_mem A D n p z⟩
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (whitneySndInclusion_mem A D n p)

@[simp]
theorem coe_whitneySndInclusion_apply (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (p : {p : ℕ × ℕ // p.1 + p.2 = n})
    (z : {x : {x : X // (A.rank + D.rank) x = n} // whitneyRankSplit A D n x = p}) :
    (whitneySndInclusion A D n p z).1 = z.1.1 := (rfl)

/-- On the clopen piece of the rank-`n` stratum where `(A.rank x, D.rank x) = p.1`, pull back
`A.stratumCore p.1.1` and `D.stratumCore p.1.2` and form their constant-rank Whitney sum. -/
-- Reduce the rank projection so `p.2` directly witnesses `(whitneyPieceCore A D n p).rank = n`.
@[expose, implicit_reducible]
def whitneyPieceCore (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (p : {p : ℕ × ℕ // p.1 + p.2 = n}) :
    FiniteRankBundleCore 𝕜
      {x : {x : X // (A.rank + D.rank) x = n} // whitneyRankSplit A D n x = p} :=
  FiniteRankBundleCore.whitneySum
    ((A.stratumCore p.1.1).pullback (whitneyFstInclusion A D n p))
    ((D.stratumCore p.1.2).pullback (whitneySndInclusion A D n p))

@[simp]
theorem rank_whitneyPieceCore (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (p : {p : ℕ × ℕ // p.1 + p.2 = n}) :
    (whitneyPieceCore A D n p).rank = p.1.1 + p.1.2 := (rfl)

/-- Glue the summand-rank Whitney-sum pieces across the clopen partition `whitneyRankSplit A D n`
into a single point-indexed core of rank `n` on `{x : X // (A.rank + D.rank) x = n}`. -/
-- Reduce the rank projection so the stratum core has rank definitionally equal to `n`.
@[expose, implicit_reducible]
def whitneyStratumCore (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    FiniteRankBundleCore 𝕜 {x : X // (A.rank + D.rank) x = n} :=
  FiniteRankBundleCore.ofLocallyConstant n (whitneyRankSplit A D n)
    (whitneyPieceCore A D n) Subtype.prop

@[simp]
theorem rank_whitneyStratumCore (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (whitneyStratumCore A D n).rank = n := (rfl)

/-- The Whitney sum of two variable-rank bundle atlases, with locally constant rank
`A.rank + D.rank` and strata glued from the constant-rank Whitney sums on all summand-rank pieces.
-/
-- Expose the rank projection so `(whitneySum A D).Fiber x` reduces to
-- `Fin (A.rank x + D.rank x) → 𝕜`.
@[expose, implicit_reducible]
def whitneySum (A D : FiniteRankAtlas 𝕜 X) : FiniteRankAtlas 𝕜 X where
  rank := A.rank + D.rank
  charts n := (whitneyStratumCore A D n).core
  indexAt_eq n := (whitneyStratumCore A D n).indexAt_eq

@[simp]
theorem rank_whitneySum (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySum A D).rank = A.rank + D.rank := (rfl)

@[simp]
theorem charts_whitneySum (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (whitneySum A D).charts n = (whitneyStratumCore A D n).core := (rfl)

@[simp]
theorem stratumCore_whitneySum (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (whitneySum A D).stratumCore n = whitneyStratumCore A D n := (rfl)

end Construction

section Bicone

private theorem whitneySum_totalSpaceHomeomorph_piece (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : Fin (A.rank x + D.rank x) → 𝕜) :
    (whitneySum A D).totalSpaceHomeomorph
      ⟨A.rank x + D.rank x,
        FiniteRankBundleCore.ofLocallyConstantTotalSpaceHomeomorph
          (A.rank x + D.rank x) (whitneyRankSplit A D (A.rank x + D.rank x))
          (whitneyPieceCore A D (A.rank x + D.rank x)) Subtype.prop
          ⟨⟨(A.rank x, D.rank x), rfl⟩,
            (⟨⟨⟨x, rfl⟩, rfl⟩, v⟩ :
              (whitneyPieceCore A D (A.rank x + D.rank x)
                ⟨(A.rank x, D.rank x), rfl⟩).core.TotalSpace)⟩⟩ = ⟨x, v⟩ :=
  (congrArg (fun q => (whitneySum A D).totalSpaceHomeomorph ⟨A.rank x + D.rank x, q⟩)
    ((FiniteRankBundleCore.ofLocallyConstantTotalSpaceHomeomorph_apply
      (A.rank x + D.rank x) (whitneyRankSplit A D (A.rank x + D.rank x))
      (whitneyPieceCore A D (A.rank x + D.rank x)) Subtype.prop
      ⟨(A.rank x, D.rank x), rfl⟩
      (⟨⟨⟨x, rfl⟩, rfl⟩, v⟩ :
        (whitneyPieceCore A D (A.rank x + D.rank x)
          ⟨(A.rank x, D.rank x), rfl⟩).core.TotalSpace)).trans
      (congrArg (TotalSpace.mk' (Fin (A.rank x + D.rank x) → 𝕜)
        (⟨x, rfl⟩ : {x' : X // (A.rank + D.rank) x' = A.rank x + D.rank x}))
        (DFunLike.congr_fun
          (FiniteRankBundleCore.castRankEquiv_rfl (𝕜 := 𝕜) (A.rank x + D.rank x)) v)))).trans
    ((whitneySum A D).totalSpaceHomeomorph_apply ⟨A.rank x + D.rank x, ⟨⟨x, rfl⟩, v⟩⟩)

private theorem whitneyFst_piece_eq (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneyPieceCore A D (A.rank x + D.rank x) ⟨(A.rank x, D.rank x), rfl⟩).core.Fiber
      ⟨⟨x, rfl⟩, whitneyRankSplit_apply A D _ ⟨x, rfl⟩⟩) :
    let p0 : {p : ℕ × ℕ // p.1 + p.2 = A.rank x + D.rank x} := ⟨(A.rank x, D.rank x), rfl⟩
    let z0 : {x' : {x' : X // (A.rank + D.rank) x' = A.rank x + D.rank x} //
        whitneyRankSplit A D (A.rank x + D.rank x) x' = p0} :=
      ⟨⟨x, rfl⟩, whitneyRankSplit_apply A D _ ⟨x, rfl⟩⟩
    let ιA0 := whitneyFstInclusion A D (A.rank x + D.rank x) p0
    let ιD0 := whitneySndInclusion A D (A.rank x + D.rank x) p0
    A.totalSpaceHomeomorph ⟨A.rank x,
      Pullback.lift (F := Fin (A.rank x) → 𝕜) (E := (A.charts (A.rank x)).Fiber) ιA0
        (((A.stratumCore (A.rank x)).pullbackHomeomorph ιA0)
          ((FiniteRankBundleCore.whitneyFst
            ((A.stratumCore (A.rank x)).pullback ιA0)
            ((D.stratumCore (D.rank x)).pullback ιD0)).totalSpaceMap ⟨z0, v⟩))⟩ =
      ⟨x, (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).1⟩ := by
  intro p0 z0 ιA0 ιD0
  let u₁ : Fin (A.rank x) → 𝕜 := (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).1
  have h1 : (FiniteRankBundleCore.whitneyFst
      ((A.stratumCore (A.rank x)).pullback ιA0)
      ((D.stratumCore (D.rank x)).pullback ιD0)).totalSpaceMap ⟨z0, v⟩ = ⟨z0, u₁⟩ :=
    ((FiniteRankBundleCore.whitneyFst _ _).totalSpaceMap_mk z0 v).trans
      (congrArg (TotalSpace.mk' _ z0)
        (DFunLike.congr_fun (FiniteRankBundleCore.fiberMap_whitneyFst _ _ z0) v))
  have h2 : ((A.stratumCore (A.rank x)).pullbackHomeomorph ιA0) ⟨z0, u₁⟩ = ⟨z0, u₁⟩ :=
    FiniteRankBundleCore.pullbackHomeomorph_apply (A.stratumCore (A.rank x)) ιA0 ⟨z0, u₁⟩
  have h3 : Pullback.lift (F := Fin (A.rank x) → 𝕜) (E := (A.charts (A.rank x)).Fiber)
      ιA0 ⟨z0, u₁⟩ = ⟨⟨x, rfl⟩, u₁⟩ :=
    (Pullback.lift_mk (E := (A.charts (A.rank x)).Fiber) (F := Fin (A.rank x) → 𝕜)
      ιA0 z0 u₁).trans
      (congrArg (fun b => (⟨b, u₁⟩ : (A.charts (A.rank x)).TotalSpace))
        (Subtype.ext (coe_whitneyFstInclusion_apply A D _ p0 z0)))
  exact (congrArg (fun t => A.totalSpaceHomeomorph ⟨A.rank x,
    Pullback.lift (F := Fin (A.rank x) → 𝕜) (E := (A.charts (A.rank x)).Fiber) ιA0
      (((A.stratumCore (A.rank x)).pullbackHomeomorph ιA0) t)⟩) h1).trans
    ((congrArg (fun t => A.totalSpaceHomeomorph ⟨A.rank x,
      Pullback.lift (F := Fin (A.rank x) → 𝕜) (E := (A.charts (A.rank x)).Fiber) ιA0 t⟩) h2).trans
      ((congrArg (fun t => A.totalSpaceHomeomorph ⟨A.rank x, t⟩) h3).trans
        (A.totalSpaceHomeomorph_apply ⟨A.rank x, ⟨⟨x, rfl⟩, u₁⟩⟩)))

private theorem continuous_whitneyFst (A D : FiniteRankAtlas 𝕜 X) :
    Continuous (fun q : TotalSpace Unit (whitneySum A D).Fiber =>
      (⟨q.proj, (splitCoords (𝕜 := 𝕜) (A.rank q.proj) (D.rank q.proj) q.2).1⟩ :
        TotalSpace Unit A.Fiber)) := by
  refine ((whitneySum A D).continuous_totalSpace_iff_rankStrata).2 fun n => ?_
  rw [← (FiniteRankBundleCore.ofLocallyConstantTotalSpaceHomeomorph n
    (whitneyRankSplit A D n) (whitneyPieceCore A D n) Subtype.prop).comp_continuous_iff',
    continuous_sigma_iff]
  rintro ⟨⟨r, s⟩, rfl⟩
  refine Continuous.congr
    (f := fun u : (whitneyPieceCore A D (r + s) ⟨(r, s), rfl⟩).core.TotalSpace =>
      A.totalSpaceHomeomorph ⟨r,
        Pullback.lift (F := Fin r → 𝕜) (E := (A.charts r).Fiber)
          (whitneyFstInclusion A D (r + s) ⟨(r, s), rfl⟩)
          (((A.stratumCore r).pullbackHomeomorph
            (whitneyFstInclusion A D (r + s) ⟨(r, s), rfl⟩))
            ((FiniteRankBundleCore.whitneyFst
              ((A.stratumCore r).pullback (whitneyFstInclusion A D (r + s) ⟨(r, s), rfl⟩))
              ((D.stratumCore s).pullback
                (whitneySndInclusion A D (r + s) ⟨(r, s), rfl⟩))).totalSpaceMap u))⟩)
    (A.totalSpaceHomeomorph.continuous.comp
      (continuous_sigmaMk.comp
        ((Pullback.continuous_lift _ _ _).comp
          (((A.stratumCore r).pullbackHomeomorph _).continuous.comp
            (FiniteRankBundleCore.whitneyFst _ _).continuous_totalSpaceMap))))
    fun u => ?_
  rcases u with ⟨⟨⟨x, hx⟩, hsplit⟩, v⟩
  have hr : A.rank x = r :=
    congrArg (fun q => q.1.1) ((whitneyRankSplit_apply A D _ ⟨x, hx⟩).symm.trans hsplit)
  have hs : D.rank x = s :=
    congrArg (fun q => q.1.2) ((whitneyRankSplit_apply A D _ ⟨x, hx⟩).symm.trans hsplit)
  subst hr; subst hs
  have hx_rfl : hx = rfl := Subsingleton.elim _ _
  cases hx_rfl
  have hsplit_rfl : hsplit = whitneyRankSplit_apply A D (A.rank x + D.rank x) ⟨x, rfl⟩ :=
    Subsingleton.elim _ _
  cases hsplit_rfl
  exact (whitneyFst_piece_eq A D x v).trans
    (congrArg (fun q : TotalSpace Unit (whitneySum A D).Fiber =>
      (⟨q.proj, (splitCoords (𝕜 := 𝕜) (A.rank q.proj) (D.rank q.proj) q.2).1⟩ :
        TotalSpace Unit A.Fiber)) (whitneySum_totalSpaceHomeomorph_piece A D x v)).symm

private theorem whitneySnd_piece_eq (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneyPieceCore A D (A.rank x + D.rank x) ⟨(A.rank x, D.rank x), rfl⟩).core.Fiber
      ⟨⟨x, rfl⟩, whitneyRankSplit_apply A D _ ⟨x, rfl⟩⟩) :
    let p0 : {p : ℕ × ℕ // p.1 + p.2 = A.rank x + D.rank x} := ⟨(A.rank x, D.rank x), rfl⟩
    let z0 : {x' : {x' : X // (A.rank + D.rank) x' = A.rank x + D.rank x} //
        whitneyRankSplit A D (A.rank x + D.rank x) x' = p0} :=
      ⟨⟨x, rfl⟩, whitneyRankSplit_apply A D _ ⟨x, rfl⟩⟩
    let ιA0 := whitneyFstInclusion A D (A.rank x + D.rank x) p0
    let ιD0 := whitneySndInclusion A D (A.rank x + D.rank x) p0
    D.totalSpaceHomeomorph ⟨D.rank x,
      Pullback.lift (F := Fin (D.rank x) → 𝕜) (E := (D.charts (D.rank x)).Fiber) ιD0
        (((D.stratumCore (D.rank x)).pullbackHomeomorph ιD0)
          ((FiniteRankBundleCore.whitneySnd
            ((A.stratumCore (A.rank x)).pullback ιA0)
            ((D.stratumCore (D.rank x)).pullback ιD0)).totalSpaceMap ⟨z0, v⟩))⟩ =
      ⟨x, (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).2⟩ := by
  intro p0 z0 ιA0 ιD0
  let u₂ : Fin (D.rank x) → 𝕜 := (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).2
  have h1 : (FiniteRankBundleCore.whitneySnd
      ((A.stratumCore (A.rank x)).pullback ιA0)
      ((D.stratumCore (D.rank x)).pullback ιD0)).totalSpaceMap ⟨z0, v⟩ = ⟨z0, u₂⟩ :=
    ((FiniteRankBundleCore.whitneySnd _ _).totalSpaceMap_mk z0 v).trans
      (congrArg (TotalSpace.mk' _ z0)
        (DFunLike.congr_fun (FiniteRankBundleCore.fiberMap_whitneySnd _ _ z0) v))
  have h2 : ((D.stratumCore (D.rank x)).pullbackHomeomorph ιD0) ⟨z0, u₂⟩ = ⟨z0, u₂⟩ :=
    FiniteRankBundleCore.pullbackHomeomorph_apply (D.stratumCore (D.rank x)) ιD0 ⟨z0, u₂⟩
  have h3 : Pullback.lift (F := Fin (D.rank x) → 𝕜) (E := (D.charts (D.rank x)).Fiber)
      ιD0 ⟨z0, u₂⟩ = ⟨⟨x, rfl⟩, u₂⟩ :=
    (Pullback.lift_mk (E := (D.charts (D.rank x)).Fiber) (F := Fin (D.rank x) → 𝕜)
      ιD0 z0 u₂).trans
      (congrArg (fun b => (⟨b, u₂⟩ : (D.charts (D.rank x)).TotalSpace))
        (Subtype.ext (coe_whitneySndInclusion_apply A D _ p0 z0)))
  exact (congrArg (fun t => D.totalSpaceHomeomorph ⟨D.rank x,
    Pullback.lift (F := Fin (D.rank x) → 𝕜) (E := (D.charts (D.rank x)).Fiber) ιD0
      (((D.stratumCore (D.rank x)).pullbackHomeomorph ιD0) t)⟩) h1).trans
    ((congrArg (fun t => D.totalSpaceHomeomorph ⟨D.rank x,
      Pullback.lift (F := Fin (D.rank x) → 𝕜) (E := (D.charts (D.rank x)).Fiber) ιD0 t⟩) h2).trans
      ((congrArg (fun t => D.totalSpaceHomeomorph ⟨D.rank x, t⟩) h3).trans
        (D.totalSpaceHomeomorph_apply ⟨D.rank x, ⟨⟨x, rfl⟩, u₂⟩⟩)))

private theorem continuous_whitneySnd (A D : FiniteRankAtlas 𝕜 X) :
    Continuous (fun q : TotalSpace Unit (whitneySum A D).Fiber =>
      (⟨q.proj, (splitCoords (𝕜 := 𝕜) (A.rank q.proj) (D.rank q.proj) q.2).2⟩ :
        TotalSpace Unit D.Fiber)) := by
  refine ((whitneySum A D).continuous_totalSpace_iff_rankStrata).2 fun n => ?_
  rw [← (FiniteRankBundleCore.ofLocallyConstantTotalSpaceHomeomorph n
    (whitneyRankSplit A D n) (whitneyPieceCore A D n) Subtype.prop).comp_continuous_iff',
    continuous_sigma_iff]
  rintro ⟨⟨r, s⟩, rfl⟩
  refine Continuous.congr
    (f := fun u : (whitneyPieceCore A D (r + s) ⟨(r, s), rfl⟩).core.TotalSpace =>
      D.totalSpaceHomeomorph ⟨s,
        Pullback.lift (F := Fin s → 𝕜) (E := (D.charts s).Fiber)
          (whitneySndInclusion A D (r + s) ⟨(r, s), rfl⟩)
          (((D.stratumCore s).pullbackHomeomorph
            (whitneySndInclusion A D (r + s) ⟨(r, s), rfl⟩))
            ((FiniteRankBundleCore.whitneySnd
              ((A.stratumCore r).pullback (whitneyFstInclusion A D (r + s) ⟨(r, s), rfl⟩))
              ((D.stratumCore s).pullback
                (whitneySndInclusion A D (r + s) ⟨(r, s), rfl⟩))).totalSpaceMap u))⟩)
    (D.totalSpaceHomeomorph.continuous.comp
      (continuous_sigmaMk.comp
        ((Pullback.continuous_lift _ _ _).comp
          (((D.stratumCore s).pullbackHomeomorph _).continuous.comp
            (FiniteRankBundleCore.whitneySnd _ _).continuous_totalSpaceMap))))
    fun u => ?_
  rcases u with ⟨⟨⟨x, hx⟩, hsplit⟩, v⟩
  have hr : A.rank x = r :=
    congrArg (fun q => q.1.1) ((whitneyRankSplit_apply A D _ ⟨x, hx⟩).symm.trans hsplit)
  have hs : D.rank x = s :=
    congrArg (fun q => q.1.2) ((whitneyRankSplit_apply A D _ ⟨x, hx⟩).symm.trans hsplit)
  subst hr; subst hs
  have hx_rfl : hx = rfl := Subsingleton.elim _ _
  cases hx_rfl
  have hsplit_rfl : hsplit = whitneyRankSplit_apply A D (A.rank x + D.rank x) ⟨x, rfl⟩ :=
    Subsingleton.elim _ _
  cases hsplit_rfl
  exact (whitneySnd_piece_eq A D x v).trans
    (congrArg (fun q : TotalSpace Unit (whitneySum A D).Fiber =>
      (⟨q.proj, (splitCoords (𝕜 := 𝕜) (A.rank q.proj) (D.rank q.proj) q.2).2⟩ :
        TotalSpace Unit D.Fiber)) (whitneySum_totalSpaceHomeomorph_piece A D x v)).symm

private theorem continuous_whitneyInl (A D : FiniteRankAtlas 𝕜 X) :
    Continuous (fun q : TotalSpace Unit A.Fiber =>
      (⟨q.proj, (splitCoords (𝕜 := 𝕜) (A.rank q.proj) (D.rank q.proj)).symm (q.2, 0)⟩ :
        TotalSpace Unit (whitneySum A D).Fiber)) := by
  -- Restrict each `A`-stratum along the clopen fibres of `D.rank` and lift through `whitneyInl`.
  refine (A.continuous_totalSpace_iff_rankStrata).2 fun r => ?_
  refine continuous_of_cover_nhds
    (s := fun s : ℕ => {t : (A.charts r).TotalSpace | D.rank t.proj.1 = s})
    (fun t => ⟨D.rank t.proj.1,
      ((D.rank.isLocallyConstant.isOpen_fiber _).preimage
        (continuous_subtype_val.comp (A.charts r).continuous_proj)).mem_nhds rfl⟩)
    fun s => ?_
  rw [continuousOn_iff_continuous_domRestrict]
  let zFn : {t : (A.charts r).TotalSpace // D.rank t.proj.1 = s} →
      {x : {x : X // (A.rank + D.rank) x = r + s} //
        whitneyRankSplit A D (r + s) x = ⟨(r, s), rfl⟩} :=
    fun y => ⟨⟨y.1.proj.1, congrArg₂ (· + ·) y.1.proj.2 y.2⟩,
      (whitneyRankSplit_apply A D (r + s) _).trans (Subtype.ext (Prod.ext y.1.proj.2 y.2))⟩
  have hz : Continuous zFn :=
    ((continuous_subtype_val.comp ((A.charts r).continuous_proj.comp
      continuous_subtype_val)).subtype_mk _).subtype_mk _
  let toPb : {t : (A.charts r).TotalSpace // D.rank t.proj.1 = s} →
      TotalSpace (Fin r → 𝕜)
        (⇑(whitneyFstInclusion A D (r + s) ⟨(r, s), rfl⟩) *ᵖ (A.charts r).Fiber) :=
    fun y => ⟨zFn y, y.1.2⟩
  have htoPb : Continuous toPb :=
    (inducing_pullbackTotalSpaceEmbedding (Fin r → 𝕜) (A.charts r).Fiber
      (whitneyFstInclusion A D (r + s) ⟨(r, s), rfl⟩)).continuous_iff.2
      (hz.prodMk (continuous_subtype_val.congr fun y => by
        rcases y with ⟨⟨⟨x, hx⟩, u⟩, hy⟩
        exact ((Pullback.lift_mk (E := (A.charts r).Fiber) (F := Fin r → 𝕜)
          (whitneyFstInclusion A D (r + s) ⟨(r, s), rfl⟩) (zFn ⟨⟨⟨x, hx⟩, u⟩, hy⟩) u).trans
          (congrArg (fun b => (⟨b, u⟩ : (A.charts r).TotalSpace))
            (Subtype.ext (coe_whitneyFstInclusion_apply A D (r + s) ⟨(r, s), rfl⟩ _)))).symm))
  refine Continuous.congr
    (f := fun y : {t : (A.charts r).TotalSpace // D.rank t.proj.1 = s} =>
      (whitneySum A D).totalSpaceHomeomorph
        ⟨r + s,
          FiniteRankBundleCore.ofLocallyConstantTotalSpaceHomeomorph (r + s)
            (whitneyRankSplit A D (r + s)) (whitneyPieceCore A D (r + s)) Subtype.prop
            ⟨⟨(r, s), rfl⟩,
              (FiniteRankBundleCore.whitneyInl
                ((A.stratumCore r).pullback (whitneyFstInclusion A D (r + s) ⟨(r, s), rfl⟩))
                ((D.stratumCore s).pullback
                  (whitneySndInclusion A D (r + s) ⟨(r, s), rfl⟩))).totalSpaceMap
                (((A.stratumCore r).pullbackHomeomorph
                  (whitneyFstInclusion A D (r + s) ⟨(r, s), rfl⟩)).symm (toPb y))⟩⟩)
    ((whitneySum A D).totalSpaceHomeomorph.continuous.comp
      (continuous_sigmaMk.comp
        ((FiniteRankBundleCore.ofLocallyConstantTotalSpaceHomeomorph _ _ _ _).continuous.comp
          (continuous_sigmaMk.comp
            ((FiniteRankBundleCore.whitneyInl _ _).continuous_totalSpaceMap.comp
              (((A.stratumCore r).pullbackHomeomorph _).symm.continuous.comp htoPb))))))
    fun y => ?_
  -- Identify the glued piece-level inclusion pointwise with the target coordinate embedding.
  dsimp only [toPb, zFn, Set.domRestrict_apply]
  clear htoPb toPb hz zFn
  rcases y with ⟨⟨⟨x, hr⟩, u⟩, hs⟩
  dsimp only at hs
  subst hr; subst hs
  let p0 : {p : ℕ × ℕ // p.1 + p.2 = A.rank x + D.rank x} := ⟨(A.rank x, D.rank x), rfl⟩
  let z0 : {x' : {x' : X // (A.rank + D.rank) x' = A.rank x + D.rank x} //
      whitneyRankSplit A D (A.rank x + D.rank x) x' = p0} :=
    ⟨⟨x, rfl⟩, (whitneyRankSplit_apply A D _ ⟨x, rfl⟩).trans rfl⟩
  let ιA0 := whitneyFstInclusion A D (A.rank x + D.rank x) p0
  let ιD0 := whitneySndInclusion A D (A.rank x + D.rank x) p0
  let pb0 : TotalSpace (Fin (A.rank x) → 𝕜) (⇑ιA0 *ᵖ (A.charts (A.rank x)).Fiber) := ⟨z0, u⟩
  let w₀ : Fin (A.rank x + D.rank x) → 𝕜 :=
    (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm (u, 0)
  have h1 : ((A.stratumCore (A.rank x)).pullbackHomeomorph ιA0).symm pb0 = ⟨z0, u⟩ :=
    FiniteRankBundleCore.pullbackHomeomorph_symm_apply (A.stratumCore (A.rank x)) ιA0 pb0
  have h2 : (FiniteRankBundleCore.whitneyInl
      ((A.stratumCore (A.rank x)).pullback ιA0)
      ((D.stratumCore (D.rank x)).pullback ιD0)).totalSpaceMap ⟨z0, u⟩ = ⟨z0, w₀⟩ :=
    ((FiniteRankBundleCore.whitneyInl
      ((A.stratumCore (A.rank x)).pullback ιA0)
      ((D.stratumCore (D.rank x)).pullback ιD0)).totalSpaceMap_mk z0 u).trans
      (congrArg (TotalSpace.mk' _ z0)
        (DFunLike.congr_fun (FiniteRankBundleCore.fiberMap_whitneyInl
          ((A.stratumCore (A.rank x)).pullback ιA0)
          ((D.stratumCore (D.rank x)).pullback ιD0) z0) u))
  have hz0 : (⟨z0, w₀⟩ : (whitneyPieceCore A D (A.rank x + D.rank x) p0).core.TotalSpace) =
      ⟨⟨⟨x, rfl⟩, rfl⟩, w₀⟩ := by
    have : z0 = ⟨⟨x, rfl⟩, rfl⟩ := Subtype.ext rfl
    rw [this]
  have hlhs : (whitneySum A D).totalSpaceHomeomorph
      ⟨A.rank x + D.rank x,
        FiniteRankBundleCore.ofLocallyConstantTotalSpaceHomeomorph (A.rank x + D.rank x)
          (whitneyRankSplit A D _) (whitneyPieceCore A D _) Subtype.prop
          ⟨p0, (FiniteRankBundleCore.whitneyInl
            ((A.stratumCore (A.rank x)).pullback ιA0)
            ((D.stratumCore (D.rank x)).pullback ιD0)).totalSpaceMap
              (((A.stratumCore (A.rank x)).pullbackHomeomorph ιA0).symm pb0)⟩⟩ = ⟨x, w₀⟩ :=
    (congrArg (fun t => (whitneySum A D).totalSpaceHomeomorph ⟨A.rank x + D.rank x,
      FiniteRankBundleCore.ofLocallyConstantTotalSpaceHomeomorph _ _ _ _
        ⟨p0, (FiniteRankBundleCore.whitneyInl _ _).totalSpaceMap t⟩⟩) h1).trans
      ((congrArg (fun t => (whitneySum A D).totalSpaceHomeomorph ⟨A.rank x + D.rank x,
        FiniteRankBundleCore.ofLocallyConstantTotalSpaceHomeomorph _ _ _ _ ⟨p0, t⟩⟩)
        (h2.trans hz0)).trans
        (whitneySum_totalSpaceHomeomorph_piece A D x w₀))
  exact hlhs.trans (congrArg (fun q : TotalSpace Unit A.Fiber =>
    (⟨q.proj, (splitCoords (𝕜 := 𝕜) (A.rank q.proj) (D.rank q.proj)).symm (q.2, 0)⟩ :
      TotalSpace Unit (whitneySum A D).Fiber))
    (A.totalSpaceHomeomorph_apply ⟨A.rank x, ⟨⟨x, rfl⟩, u⟩⟩)).symm

private theorem continuous_whitneyInr (A D : FiniteRankAtlas 𝕜 X) :
    Continuous (fun q : TotalSpace Unit D.Fiber =>
      (⟨q.proj, (splitCoords (𝕜 := 𝕜) (A.rank q.proj) (D.rank q.proj)).symm (0, q.2)⟩ :
        TotalSpace Unit (whitneySum A D).Fiber)) := by
  -- Restrict each `D`-stratum along the clopen fibres of `A.rank` and lift through `whitneyInr`.
  refine (D.continuous_totalSpace_iff_rankStrata).2 fun s => ?_
  refine continuous_of_cover_nhds
    (s := fun r : ℕ => {t : (D.charts s).TotalSpace | A.rank t.proj.1 = r})
    (fun t => ⟨A.rank t.proj.1,
      ((A.rank.isLocallyConstant.isOpen_fiber _).preimage
        (continuous_subtype_val.comp (D.charts s).continuous_proj)).mem_nhds rfl⟩)
    fun r => ?_
  rw [continuousOn_iff_continuous_domRestrict]
  let zFn : {t : (D.charts s).TotalSpace // A.rank t.proj.1 = r} →
      {x : {x : X // (A.rank + D.rank) x = r + s} //
        whitneyRankSplit A D (r + s) x = ⟨(r, s), rfl⟩} :=
    fun y => ⟨⟨y.1.proj.1, congrArg₂ (· + ·) y.2 y.1.proj.2⟩,
      (whitneyRankSplit_apply A D (r + s) _).trans (Subtype.ext (Prod.ext y.2 y.1.proj.2))⟩
  have hz : Continuous zFn :=
    ((continuous_subtype_val.comp ((D.charts s).continuous_proj.comp
      continuous_subtype_val)).subtype_mk _).subtype_mk _
  let toPb : {t : (D.charts s).TotalSpace // A.rank t.proj.1 = r} →
      TotalSpace (Fin s → 𝕜)
        (⇑(whitneySndInclusion A D (r + s) ⟨(r, s), rfl⟩) *ᵖ (D.charts s).Fiber) :=
    fun y => ⟨zFn y, y.1.2⟩
  have htoPb : Continuous toPb :=
    (inducing_pullbackTotalSpaceEmbedding (Fin s → 𝕜) (D.charts s).Fiber
      (whitneySndInclusion A D (r + s) ⟨(r, s), rfl⟩)).continuous_iff.2
      (hz.prodMk (continuous_subtype_val.congr fun y => by
        rcases y with ⟨⟨⟨x, hx⟩, w⟩, hy⟩
        exact ((Pullback.lift_mk (E := (D.charts s).Fiber) (F := Fin s → 𝕜)
          (whitneySndInclusion A D (r + s) ⟨(r, s), rfl⟩) (zFn ⟨⟨⟨x, hx⟩, w⟩, hy⟩) w).trans
          (congrArg (fun b => (⟨b, w⟩ : (D.charts s).TotalSpace))
            (Subtype.ext (coe_whitneySndInclusion_apply A D (r + s) ⟨(r, s), rfl⟩ _)))).symm))
  refine Continuous.congr
    (f := fun y : {t : (D.charts s).TotalSpace // A.rank t.proj.1 = r} =>
      (whitneySum A D).totalSpaceHomeomorph
        ⟨r + s,
          FiniteRankBundleCore.ofLocallyConstantTotalSpaceHomeomorph (r + s)
            (whitneyRankSplit A D (r + s)) (whitneyPieceCore A D (r + s)) Subtype.prop
            ⟨⟨(r, s), rfl⟩,
              (FiniteRankBundleCore.whitneyInr
                ((A.stratumCore r).pullback (whitneyFstInclusion A D (r + s) ⟨(r, s), rfl⟩))
                ((D.stratumCore s).pullback
                  (whitneySndInclusion A D (r + s) ⟨(r, s), rfl⟩))).totalSpaceMap
                (((D.stratumCore s).pullbackHomeomorph
                  (whitneySndInclusion A D (r + s) ⟨(r, s), rfl⟩)).symm (toPb y))⟩⟩)
    ((whitneySum A D).totalSpaceHomeomorph.continuous.comp
      (continuous_sigmaMk.comp
        ((FiniteRankBundleCore.ofLocallyConstantTotalSpaceHomeomorph _ _ _ _).continuous.comp
          (continuous_sigmaMk.comp
            ((FiniteRankBundleCore.whitneyInr _ _).continuous_totalSpaceMap.comp
              (((D.stratumCore s).pullbackHomeomorph _).symm.continuous.comp htoPb))))))
    fun y => ?_
  -- Identify the glued piece-level inclusion pointwise with the target coordinate embedding.
  dsimp only [toPb, zFn, Set.domRestrict_apply]
  clear htoPb toPb hz zFn
  rcases y with ⟨⟨⟨x, hs⟩, w⟩, hr⟩
  dsimp only at hr
  subst hr; subst hs
  let p0 : {p : ℕ × ℕ // p.1 + p.2 = A.rank x + D.rank x} := ⟨(A.rank x, D.rank x), rfl⟩
  let z0 : {x' : {x' : X // (A.rank + D.rank) x' = A.rank x + D.rank x} //
      whitneyRankSplit A D (A.rank x + D.rank x) x' = p0} :=
    ⟨⟨x, rfl⟩, (whitneyRankSplit_apply A D _ ⟨x, rfl⟩).trans rfl⟩
  let ιA0 := whitneyFstInclusion A D (A.rank x + D.rank x) p0
  let ιD0 := whitneySndInclusion A D (A.rank x + D.rank x) p0
  let pb0 : TotalSpace (Fin (D.rank x) → 𝕜) (⇑ιD0 *ᵖ (D.charts (D.rank x)).Fiber) := ⟨z0, w⟩
  let w₀ : Fin (A.rank x + D.rank x) → 𝕜 :=
    (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm (0, w)
  have h1 : ((D.stratumCore (D.rank x)).pullbackHomeomorph ιD0).symm pb0 = ⟨z0, w⟩ :=
    FiniteRankBundleCore.pullbackHomeomorph_symm_apply (D.stratumCore (D.rank x)) ιD0 pb0
  have h2 : (FiniteRankBundleCore.whitneyInr
      ((A.stratumCore (A.rank x)).pullback ιA0)
      ((D.stratumCore (D.rank x)).pullback ιD0)).totalSpaceMap ⟨z0, w⟩ = ⟨z0, w₀⟩ :=
    ((FiniteRankBundleCore.whitneyInr
      ((A.stratumCore (A.rank x)).pullback ιA0)
      ((D.stratumCore (D.rank x)).pullback ιD0)).totalSpaceMap_mk z0 w).trans
      (congrArg (TotalSpace.mk' _ z0)
        (DFunLike.congr_fun (FiniteRankBundleCore.fiberMap_whitneyInr
          ((A.stratumCore (A.rank x)).pullback ιA0)
          ((D.stratumCore (D.rank x)).pullback ιD0) z0) w))
  have hz0 : (⟨z0, w₀⟩ : (whitneyPieceCore A D (A.rank x + D.rank x) p0).core.TotalSpace) =
      ⟨⟨⟨x, rfl⟩, rfl⟩, w₀⟩ := by
    have : z0 = ⟨⟨x, rfl⟩, rfl⟩ := Subtype.ext rfl
    rw [this]
  have hlhs : (whitneySum A D).totalSpaceHomeomorph
      ⟨A.rank x + D.rank x,
        FiniteRankBundleCore.ofLocallyConstantTotalSpaceHomeomorph (A.rank x + D.rank x)
          (whitneyRankSplit A D _) (whitneyPieceCore A D _) Subtype.prop
          ⟨p0, (FiniteRankBundleCore.whitneyInr
            ((A.stratumCore (A.rank x)).pullback ιA0)
            ((D.stratumCore (D.rank x)).pullback ιD0)).totalSpaceMap
              (((D.stratumCore (D.rank x)).pullbackHomeomorph ιD0).symm pb0)⟩⟩ = ⟨x, w₀⟩ :=
    (congrArg (fun t => (whitneySum A D).totalSpaceHomeomorph ⟨A.rank x + D.rank x,
      FiniteRankBundleCore.ofLocallyConstantTotalSpaceHomeomorph _ _ _ _
        ⟨p0, (FiniteRankBundleCore.whitneyInr _ _).totalSpaceMap t⟩⟩) h1).trans
      ((congrArg (fun t => (whitneySum A D).totalSpaceHomeomorph ⟨A.rank x + D.rank x,
        FiniteRankBundleCore.ofLocallyConstantTotalSpaceHomeomorph _ _ _ _ ⟨p0, t⟩⟩)
        (h2.trans hz0)).trans
        (whitneySum_totalSpaceHomeomorph_piece A D x w₀))
  exact hlhs.trans (congrArg (fun q : TotalSpace Unit D.Fiber =>
    (⟨q.proj, (splitCoords (𝕜 := 𝕜) (A.rank q.proj) (D.rank q.proj)).symm (0, q.2)⟩ :
      TotalSpace Unit (whitneySum A D).Fiber))
    (D.totalSpaceHomeomorph_apply ⟨D.rank x, ⟨⟨x, rfl⟩, w⟩⟩)).symm

/-- Projection of the variable-rank Whitney sum onto its first summand. -/
def whitneyFst (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ A where
  fiberMap x := ((ContinuousLinearMap.fst 𝕜 (A.Fiber x) (D.Fiber x)).comp
    (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toContinuousLinearMap).toLinearMap
  continuous_totalSpaceMap := continuous_whitneyFst A D

/-- Projection of the variable-rank Whitney sum onto its second summand. -/
def whitneySnd (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ D where
  fiberMap x := ((ContinuousLinearMap.snd 𝕜 (A.Fiber x) (D.Fiber x)).comp
    (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toContinuousLinearMap).toLinearMap
  continuous_totalSpaceMap := continuous_whitneySnd A D

/-- Inclusion of the first summand into the variable-rank Whitney sum. -/
def whitneyInl (A D : FiniteRankAtlas 𝕜 X) : A ⟶ whitneySum A D where
  fiberMap x := ((splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl 𝕜 (A.Fiber x) (D.Fiber x))).toLinearMap
  continuous_totalSpaceMap := continuous_whitneyInl A D

/-- Inclusion of the second summand into the variable-rank Whitney sum. -/
def whitneyInr (A D : FiniteRankAtlas 𝕜 X) : D ⟶ whitneySum A D where
  fiberMap x := ((splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr 𝕜 (A.Fiber x) (D.Fiber x))).toLinearMap
  continuous_totalSpaceMap := continuous_whitneyInr A D

@[simp]
theorem fiberMap_whitneyFst_apply (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneyFst A D).fiberMap x v = (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).1 := (rfl)

@[simp]
theorem fiberMap_whitneySnd_apply (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneySnd A D).fiberMap x v = (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).2 := (rfl)

@[simp]
theorem fiberMap_whitneyInl_apply (A D : FiniteRankAtlas 𝕜 X) (x : X) (u : A.Fiber x) :
    (whitneyInl A D).fiberMap x u =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm (u, 0) := (rfl)

@[simp]
theorem fiberMap_whitneyInr_apply (A D : FiniteRankAtlas 𝕜 X) (x : X) (w : D.Fiber x) :
    (whitneyInr A D).fiberMap x w =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm (0, w) := (rfl)

@[reassoc (attr := simp)]
theorem whitneyInl_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneyFst A D = 𝟙 A := by
  ext x u
  simp

@[reassoc (attr := simp)]
theorem whitneyInl_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneySnd A D = 0 := by
  ext x u
  simp

@[reassoc (attr := simp)]
theorem whitneyInr_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneyFst A D = 0 := by
  ext x w
  simp

@[reassoc (attr := simp)]
theorem whitneyInr_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneySnd A D = 𝟙 D := by
  ext x w
  simp

/-- The variable-rank Whitney sum packaged with its four canonical morphisms. -/
-- Expose the point projection so the four leg types reduce to `whitneySum A D`.
@[expose, implicit_reducible]
def whitneyBicone (A D : FiniteRankAtlas 𝕜 X) : BinaryBicone A D where
  pt := whitneySum A D
  fst := whitneyFst A D
  snd := whitneySnd A D
  inl := whitneyInl A D
  inr := whitneyInr A D
  inl_fst := whitneyInl_fst A D
  inl_snd := whitneyInl_snd A D
  inr_fst := whitneyInr_fst A D
  inr_snd := whitneyInr_snd A D

@[simp]
theorem whitneyBicone_pt (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).pt = whitneySum A D := (rfl)

@[simp]
theorem whitneyBicone_fst (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).fst = whitneyFst A D := (rfl)

@[simp]
theorem whitneyBicone_snd (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).snd = whitneySnd A D := (rfl)

@[simp]
theorem whitneyBicone_inl (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).inl = whitneyInl A D := (rfl)

@[simp]
theorem whitneyBicone_inr (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).inr = whitneyInr A D := (rfl)

/-- The two block projections and inclusions resolve the identity on `whitneySum A D`. -/
@[simp]
theorem whitney_total (A D : FiniteRankAtlas 𝕜 X) :
    whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D =
      𝟙 (whitneySum A D) := by
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro v
  apply (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).injective
  simp

/-- The geometric Whitney sum of two variable-rank bundle atlases is a binary bilimit. -/
def whitneyBiconeIsBilimit (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).IsBilimit :=
  isBinaryBilimitOfTotal _ (whitney_total A D)

/-- Variable-rank bundle atlases admit binary biproducts given by Whitney sums. -/
instance : HasBinaryBiproducts (FiniteRankAtlas 𝕜 X) where
  has_binary_biproduct A D := ⟨⟨whitneyBicone A D, whitneyBiconeIsBilimit A D⟩⟩

/-- Variable-rank bundle atlases admit all finite biproducts. -/
instance : HasFiniteBiproducts (FiniteRankAtlas 𝕜 X) :=
  TauCeti.hasFiniteBiproducts_of_hasBinaryBiproducts

end Bicone

section UniversalProperty

variable {A A' A'' D D' D'' C E : FiniteRankAtlas 𝕜 X}

/-- Pair two atlas morphisms with common source into the concrete Whitney sum. -/
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
theorem fiberMap_whitneyLift_apply (f : E ⟶ A) (g : E ⟶ D) (x : X) (v : E.Fiber x) :
    (whitneyLift f g).fiberMap x v =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm (f.fiberMap x v, g.fiberMap x v) := by
  apply (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).injective
  simp [whitneyLift]

theorem splitCoords_fiberMap_whitneyLift (f : E ⟶ A) (g : E ⟶ D) (x : X) (v : E.Fiber x) :
    splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) ((whitneyLift f g).fiberMap x v) =
      (f.fiberMap x v, g.fiberMap x v) := by
  simp

/-- Copair two atlas morphisms with common target out of the concrete Whitney sum. -/
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
theorem fiberMap_whitneyDesc_apply (f : A ⟶ E) (g : D ⟶ E) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneyDesc f g).fiberMap x v =
      f.fiberMap x (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).1 +
        g.fiberMap x (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).2 := (rfl)

/-- Direct sum of two variable-rank atlas morphisms on Whitney sums. -/
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
theorem fiberMap_whitneyMap_apply (f : A ⟶ A') (g : D ⟶ D') (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneyMap f g).fiberMap x v =
      (splitCoords (𝕜 := 𝕜) (A'.rank x) (D'.rank x)).symm
        (f.fiberMap x (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).1,
          g.fiberMap x (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).2) := by
  simp [whitneyMap]

theorem splitCoords_fiberMap_whitneyMap (f : A ⟶ A') (g : D ⟶ D') (x : X)
    (v : (whitneySum A D).Fiber x) :
    splitCoords (𝕜 := 𝕜) (A'.rank x) (D'.rank x) ((whitneyMap f g).fiberMap x v) =
      (f.fiberMap x (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).1,
        g.fiberMap x (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).2) := by
  simp

/-- Direct sum of two variable-rank atlas isomorphisms. -/
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

/-- Symmetry isomorphism exchanging the two summands of a variable-rank Whitney sum. -/
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

/-- Associativity isomorphism regrouping a threefold variable-rank Whitney sum. -/
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
  hom := whitneySnd (trivial 𝕜 (0 : LocallyConstant X ℕ)) A
  inv := whitneyInr (trivial 𝕜 (0 : LocallyConstant X ℕ)) A
  hom_inv_id := whitneySum_hom_ext' (isZero_trivial_zero.eq_of_src _ _) (by simp)
  inv_hom_id := whitneyInr_snd (trivial 𝕜 (0 : LocallyConstant X ℕ)) A

@[simp]
theorem whitneyZeroLeftIso_hom (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroLeftIso A).hom = whitneySnd (trivial 𝕜 (0 : LocallyConstant X ℕ)) A := (rfl)

@[simp]
theorem whitneyZeroLeftIso_inv (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroLeftIso A).inv = whitneyInr (trivial 𝕜 (0 : LocallyConstant X ℕ)) A := (rfl)

@[reassoc]
theorem whitneyMap_zeroLeftIso_hom {A A' : FiniteRankAtlas 𝕜 X}
    (g : trivial 𝕜 (0 : LocallyConstant X ℕ) ⟶ trivial 𝕜 (0 : LocallyConstant X ℕ))
    (f : A ⟶ A') :
    whitneyMap g f ≫ (whitneyZeroLeftIso A').hom = (whitneyZeroLeftIso A).hom ≫ f := by
  simp only [whitneyZeroLeftIso_hom, whitneyMap_snd]

/-- Right unit isomorphism for Whitney sum with the trivial rank-zero atlas. -/
def whitneyZeroRightIso (A : FiniteRankAtlas 𝕜 X) :
    whitneySum A (trivial 𝕜 (0 : LocallyConstant X ℕ)) ≅ A where
  hom := whitneyFst A (trivial 𝕜 (0 : LocallyConstant X ℕ))
  inv := whitneyInl A (trivial 𝕜 (0 : LocallyConstant X ℕ))
  hom_inv_id := whitneySum_hom_ext' (by simp) (isZero_trivial_zero.eq_of_src _ _)
  inv_hom_id := whitneyInl_fst A (trivial 𝕜 (0 : LocallyConstant X ℕ))

@[simp]
theorem whitneyZeroRightIso_hom (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroRightIso A).hom = whitneyFst A (trivial 𝕜 (0 : LocallyConstant X ℕ)) := (rfl)

@[simp]
theorem whitneyZeroRightIso_inv (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroRightIso A).inv = whitneyInl A (trivial 𝕜 (0 : LocallyConstant X ℕ)) := (rfl)

@[reassoc]
theorem whitneyMap_zeroRightIso_hom {A A' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A')
    (g : trivial 𝕜 (0 : LocallyConstant X ℕ) ⟶ trivial 𝕜 (0 : LocallyConstant X ℕ)) :
    whitneyMap f g ≫ (whitneyZeroRightIso A').hom = (whitneyZeroRightIso A).hom ≫ f := by
  simp only [whitneyZeroRightIso_hom, whitneyMap_fst]

private def trivialHomOfBlockMap {R₁ R₂ : LocallyConstant X ℕ}
    (r₁ r₂ : LocallyConstant X ℕ)
    (F₁ F₂ : ℕ → ℕ → ℕ)
    (hR₁ : ∀ x, R₁ x = F₁ (r₁ x) (r₂ x))
    (hR₂ : ∀ x, R₂ x = F₂ (r₁ x) (r₂ x))
    (L : ∀ a b : ℕ, (Fin (F₁ a b) → 𝕜) →L[𝕜] (Fin (F₂ a b) → 𝕜)) :
    trivial 𝕜 R₁ ⟶ trivial 𝕜 R₂ where
  fiberMap x :=
    ((FiniteRankBundleCore.castRankEquiv (𝕜 := 𝕜) (hR₂ x).symm).toLinearMap).comp
      ((L (r₁ x) (r₂ x)).toLinearMap.comp
        (FiniteRankBundleCore.castRankEquiv (𝕜 := 𝕜) (hR₁ x)).toLinearMap)
  continuous_totalSpaceMap := by
    -- Cover each source rank stratum by the clopen joint fibres of `(r₁, r₂)`.
    refine ((trivial 𝕜 R₁).continuous_totalSpace_iff_rankStrata).2 fun m => ?_
    refine continuous_of_cover_nhds
      (s := fun ab : ℕ × ℕ =>
        {p : ((trivial 𝕜 R₁).charts m).TotalSpace | r₁ p.proj.1 = ab.1 ∧ r₂ p.proj.1 = ab.2})
      (fun p => ⟨(r₁ p.proj.1, r₂ p.proj.1),
        (((r₁.isLocallyConstant.isOpen_fiber _).preimage
          (continuous_subtype_val.comp ((trivial 𝕜 R₁).charts m).continuous_proj)).inter
          ((r₂.isLocallyConstant.isOpen_fiber _).preimage
            (continuous_subtype_val.comp ((trivial 𝕜 R₁).charts m).continuous_proj))).mem_nhds
          ⟨rfl, rfl⟩⟩)
      fun ⟨a, b⟩ => ?_
    rw [continuousOn_iff_continuous_domRestrict]
    by_cases hm : m = F₁ a b
    · subst hm
      have hbase : Continuous (fun y : {p : ((trivial 𝕜 R₁).charts (F₁ a b)).TotalSpace //
          r₁ p.proj.1 = a ∧ r₂ p.proj.1 = b} =>
          (⟨y.1.proj.1, (hR₂ y.1.proj.1).trans (congrArg₂ F₂ y.2.1 y.2.2)⟩ :
            {x : X // R₂ x = F₂ a b})) :=
        Continuous.subtype_mk
          (continuous_subtype_val.comp
            (((trivial 𝕜 R₁).charts (F₁ a b)).continuous_proj.comp continuous_subtype_val)) _
      have hcoord : Continuous (fun y : {p : ((trivial 𝕜 R₁).charts (F₁ a b)).TotalSpace //
          r₁ p.proj.1 = a ∧ r₂ p.proj.1 = b} => L a b y.1.2) :=
        (L a b).continuous.comp
          ((FiniteRankBundleCore.continuous_trivial_snd
            (𝕜 := 𝕜) (B := {x : X // R₁ x = F₁ a b}) (n := F₁ a b)).comp continuous_subtype_val)
      have hstratum : Continuous (fun y : {p : ((trivial 𝕜 R₁).charts (F₁ a b)).TotalSpace //
          r₁ p.proj.1 = a ∧ r₂ p.proj.1 = b} =>
          (⟨⟨y.1.proj.1, (hR₂ y.1.proj.1).trans (congrArg₂ F₂ y.2.1 y.2.2)⟩, L a b y.1.2⟩ :
            ((trivial 𝕜 R₂).charts (F₂ a b)).TotalSpace)) :=
        (FiniteRankBundleCore.continuous_trivial_iff
          (𝕜 := 𝕜) (B := {x : X // R₂ x = F₂ a b}) (n := F₂ a b)).2 ⟨hbase, hcoord⟩
      refine ((trivial 𝕜 R₂).totalSpaceHomeomorph.continuous.comp
        (continuous_sigmaMk.comp hstratum)).congr fun y => ?_
      -- Match the stratum coordinate map with the reindexed fibrewise operator.
      dsimp only [Set.domRestrict_apply, Function.comp_apply]
      clear hstratum hcoord hbase
      rcases y with ⟨⟨⟨x, hx₁⟩, v⟩, ha, hb⟩
      dsimp only at ha hb
      subst ha; subst hb
      have hx₁_rfl : hx₁ = hR₁ x := Subsingleton.elim _ _
      cases hx₁_rfl
      have hlhs : (trivial 𝕜 R₂).totalSpaceHomeomorph
          ⟨F₂ (r₁ x) (r₂ x), ⟨⟨x, hR₂ x⟩, L (r₁ x) (r₂ x) v⟩⟩ =
          ⟨x, FiniteRankBundleCore.castRankEquiv (𝕜 := 𝕜) (hR₂ x).symm (L (r₁ x) (r₂ x) v)⟩ :=
        ((trivial 𝕜 R₂).totalSpaceHomeomorph_apply _).trans
          (congrArg (TotalSpace.mk' Unit x) (by ext i; simp))
      have hrhs : (trivial 𝕜 R₁).totalSpaceHomeomorph ⟨F₁ (r₁ x) (r₂ x), ⟨⟨x, hR₁ x⟩, v⟩⟩ =
          ⟨x, FiniteRankBundleCore.castRankEquiv (𝕜 := 𝕜) (hR₁ x).symm v⟩ :=
        ((trivial 𝕜 R₁).totalSpaceHomeomorph_apply _).trans
          (congrArg (TotalSpace.mk' Unit x) (funext fun i =>
            (FiniteRankBundleCore.castRankEquiv_apply (𝕜 := 𝕜) (hR₁ x).symm v i).symm))
      have hmid : (⟨x,
          FiniteRankBundleCore.castRankEquiv (𝕜 := 𝕜) (hR₂ x).symm (L (r₁ x) (r₂ x) v)⟩ :
          TotalSpace Unit (trivial 𝕜 R₂).Fiber) =
          ⟨x, (((FiniteRankBundleCore.castRankEquiv (𝕜 := 𝕜) (hR₂ x).symm).toLinearMap).comp
            ((L (r₁ x) (r₂ x)).toLinearMap.comp
              (FiniteRankBundleCore.castRankEquiv (𝕜 := 𝕜) (hR₁ x)).toLinearMap))
            (FiniteRankBundleCore.castRankEquiv (𝕜 := 𝕜) (hR₁ x).symm v)⟩ := by
        refine congrArg (TotalSpace.mk' Unit x) ?_
        dsimp only [LinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearMap.coe_coe]
        refine congrArg (FiniteRankBundleCore.castRankEquiv (𝕜 := 𝕜) (hR₂ x).symm)
          (congrArg (L (r₁ x) (r₂ x)) ?_)
        ext k
        exact ((FiniteRankBundleCore.castRankEquiv_apply (𝕜 := 𝕜) (hR₁ x) _ k).trans
          (FiniteRankBundleCore.castRankEquiv_apply (𝕜 := 𝕜) (hR₁ x).symm v _)).symm
      exact hlhs.trans (hmid.trans
        (congrArg (fun q : TotalSpace Unit (trivial 𝕜 R₁).Fiber =>
          (⟨q.proj,
            (((FiniteRankBundleCore.castRankEquiv (𝕜 := 𝕜) (hR₂ q.proj).symm).toLinearMap).comp
              ((L (r₁ q.proj) (r₂ q.proj)).toLinearMap.comp
                (FiniteRankBundleCore.castRankEquiv (𝕜 := 𝕜) (hR₁ q.proj)).toLinearMap))
              q.2⟩ :
            TotalSpace Unit (trivial 𝕜 R₂).Fiber)) hrhs).symm)
    · have : IsEmpty {p : ((trivial 𝕜 R₁).charts m).TotalSpace //
          r₁ p.proj.1 = a ∧ r₂ p.proj.1 = b} :=
        ⟨fun y => hm (y.1.proj.2.symm.trans ((hR₁ y.1.proj.1).trans (congrArg₂ F₁ y.2.1 y.2.2)))⟩
      exact continuous_of_discreteTopology

/-- The Whitney sum of two trivial variable-rank atlases of locally constant ranks `r₁` and `r₂`
is canonically isomorphic, via the identity on every coordinate fibre `Fin (r₁ x + r₂ x) → 𝕜`, to
the trivial variable-rank atlas of rank `r₁ + r₂`. -/
def whitneyTrivialIso (r₁ r₂ : LocallyConstant X ℕ) :
    whitneySum (trivial 𝕜 r₁) (trivial 𝕜 r₂) ≅ trivial 𝕜 (r₁ + r₂) :=
  isoMk (fun x => LinearEquiv.refl 𝕜 (Fin (r₁ x + r₂ x) → 𝕜))
    ((whitneyDesc
      (trivialHomOfBlockMap r₁ r₂ (fun a _ => a) (· + ·) (fun _ => rfl) (fun _ => rfl)
        fun a b => (splitCoords (𝕜 := 𝕜) a b).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.inl 𝕜 (Fin a → 𝕜) (Fin b → 𝕜)))
      (trivialHomOfBlockMap r₁ r₂ (fun _ b => b) (· + ·) (fun _ => rfl) (fun _ => rfl)
        fun a b => (splitCoords (𝕜 := 𝕜) a b).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.inr 𝕜 (Fin a → 𝕜) (Fin b → 𝕜)))).continuous_totalSpaceMap.congr
      fun p => by
        rcases p with ⟨x, v⟩
        refine congrArg (TotalSpace.mk' Unit x) ?_
        apply (splitCoords (𝕜 := 𝕜) (r₁ x) (r₂ x)).injective
        ext i <;> simp [trivialHomOfBlockMap] <;> rfl)
    ((whitneyLift
      (trivialHomOfBlockMap r₁ r₂ (· + ·) (fun a _ => a) (fun _ => rfl) (fun _ => rfl)
        fun a b => (ContinuousLinearMap.fst 𝕜 (Fin a → 𝕜) (Fin b → 𝕜)).comp
          (splitCoords (𝕜 := 𝕜) a b).toContinuousLinearMap)
      (trivialHomOfBlockMap r₁ r₂ (· + ·) (fun _ b => b) (fun _ => rfl) (fun _ => rfl)
        fun a b => (ContinuousLinearMap.snd 𝕜 (Fin a → 𝕜) (Fin b → 𝕜)).comp
          (splitCoords (𝕜 := 𝕜) a b).toContinuousLinearMap)).continuous_totalSpaceMap.congr
      fun p => by
        rcases p with ⟨x, v⟩
        refine congrArg (TotalSpace.mk' Unit x) ?_
        apply (splitCoords (𝕜 := 𝕜) (r₁ x) (r₂ x)).injective
        ext i <;> simp [trivialHomOfBlockMap] <;> rfl)

@[simp]
theorem fiberMap_whitneyTrivialIso_hom (r₁ r₂ : LocallyConstant X ℕ) (x : X) :
    (whitneyTrivialIso (𝕜 := 𝕜) r₁ r₂).hom.fiberMap x = LinearMap.id := by
  simp [whitneyTrivialIso]

@[simp]
theorem fiberMap_whitneyTrivialIso_inv (r₁ r₂ : LocallyConstant X ℕ) (x : X) :
    (whitneyTrivialIso (𝕜 := 𝕜) r₁ r₂).inv.fiberMap x = LinearMap.id := by
  apply LinearMap.ext
  intro v
  simp [whitneyTrivialIso]
  rfl

end Coherence

section TotalSpace

/-- Split a coordinate vector in the fibre of `whitneySum A D` at `x` into its pair of vectors in
`A.Fiber x × D.Fiber x`. -/
def whitneySumFiberEquiv (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneySum A D).Fiber x ≃L[𝕜] A.Fiber x × D.Fiber x :=
  splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)

theorem whitneySumFiberEquiv_apply (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    whitneySumFiberEquiv A D x v = splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v := (rfl)

theorem whitneySumFiberEquiv_symm_apply (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (w : A.Fiber x × D.Fiber x) :
    (whitneySumFiberEquiv A D x).symm w =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm w := (rfl)

@[simp]
theorem fst_whitneySumFiberEquiv (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneySumFiberEquiv A D x v).1 = (whitneyFst A D).fiberMap x v := (rfl)

@[simp]
theorem snd_whitneySumFiberEquiv (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneySumFiberEquiv A D x v).2 = (whitneySnd A D).fiberMap x v := (rfl)

@[simp]
theorem whitneySumFiberEquiv_finAppend (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (u : A.Fiber x) (w : D.Fiber x) :
    whitneySumFiberEquiv A D x (Fin.append u w) = (u, w) := by
  have h := (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (u, w)
  rwa [splitCoords_symm_apply] at h

theorem whitneySumFiberEquiv_whitneyInl (A D : FiniteRankAtlas 𝕜 X) (x : X) (u : A.Fiber x) :
    whitneySumFiberEquiv A D x ((whitneyInl A D).fiberMap x u) = (u, 0) :=
  (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (u, 0)

theorem whitneySumFiberEquiv_whitneyInr (A D : FiniteRankAtlas 𝕜 X) (x : X) (w : D.Fiber x) :
    whitneySumFiberEquiv A D x ((whitneyInr A D).fiberMap x w) = (0, w) :=
  (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).apply_symm_apply (0, w)

theorem whitneySumFiberEquiv_fiberMap_whitneyMap {A A' D D' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') (x : X) (v : (whitneySum A D).Fiber x) :
    whitneySumFiberEquiv A' D' x ((whitneyMap f g).fiberMap x v) =
      (f.fiberMap x (whitneySumFiberEquiv A D x v).1,
        g.fiberMap x (whitneySumFiberEquiv A D x v).2) :=
  splitCoords_fiberMap_whitneyMap f g x v

private def whitneySumTotalInrFiber (A D : FiniteRankAtlas 𝕜 X)
    (q : {q : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // q.1.proj = q.2.proj}) :
    (whitneySum A D).Fiber q.1.1.proj :=
  fun i => (whitneyInr A D).fiberMap q.1.2.proj q.1.2.2
    (Fin.cast (congrArg (whitneySum A D).rank q.2) i)

/-- The reconstructed total space of `whitneySum A D` is homeomorphic over `X` to the topological
fibre product of the reconstructed total spaces of `A` and `D`, acting on each fibre by
`whitneySumFiberEquiv`. -/
def whitneySumTotalSpaceHomeomorph (A D : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit (whitneySum A D).Fiber ≃ₜ
      {q : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // q.1.proj = q.2.proj} where
  toFun p := ⟨(⟨p.proj, (whitneyFst A D).fiberMap p.proj p.2⟩,
    ⟨p.proj, (whitneySnd A D).fiberMap p.proj p.2⟩), rfl⟩
  invFun q := ⟨q.1.1.proj,
    (whitneyInl A D).fiberMap q.1.1.proj q.1.1.2 + whitneySumTotalInrFiber A D q⟩
  left_inv := by
    rintro ⟨x, v⟩
    refine congrArg (TotalSpace.mk' Unit x) ?_
    apply (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).injective
    simp [whitneySumTotalInrFiber]
  right_inv := by
    rintro ⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, h⟩
    cases h
    apply Subtype.ext
    refine Prod.ext (congrArg (TotalSpace.mk' Unit x₁) ?_)
      (congrArg (TotalSpace.mk' Unit x₁) ?_)
    · simp [whitneySumTotalInrFiber]
    · simp [whitneySumTotalInrFiber]
  continuous_toFun :=
    ((whitneyFst A D).continuous_totalSpaceMap.prodMk
      (whitneySnd A D).continuous_totalSpaceMap).subtype_mk _
  continuous_invFun := by
    have hinl : Continuous (fun q :
        {q : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // q.1.proj = q.2.proj} =>
        (⟨q.1.1.proj, (whitneyInl A D).fiberMap q.1.1.proj q.1.1.2⟩ :
          TotalSpace Unit (whitneySum A D).Fiber)) :=
      (whitneyInl A D).continuous_totalSpaceMap.comp (continuous_fst.comp continuous_subtype_val)
    have hinr : Continuous (fun q :
        {q : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // q.1.proj = q.2.proj} =>
        (⟨q.1.1.proj, whitneySumTotalInrFiber A D q⟩ :
          TotalSpace Unit (whitneySum A D).Fiber)) :=
      ((whitneyInr A D).continuous_totalSpaceMap.comp
        (continuous_snd.comp continuous_subtype_val)).congr fun q => by
          rcases q with ⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, h⟩
          cases h
          rfl
    exact (whitneySum A D).continuous_add hinl hinr

@[simp]
theorem whitneySumTotalSpaceHomeomorph_apply (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    whitneySumTotalSpaceHomeomorph A D p =
      ⟨(⟨p.proj, (whitneySumFiberEquiv A D p.proj p.2).1⟩,
        ⟨p.proj, (whitneySumFiberEquiv A D p.proj p.2).2⟩), rfl⟩ := (rfl)

@[simp]
theorem whitneySumTotalSpaceHomeomorph_symm_mk (A D : FiniteRankAtlas 𝕜 X)
    (x : X) (u : A.Fiber x) (w : D.Fiber x) :
    (whitneySumTotalSpaceHomeomorph A D).symm ⟨(⟨x, u⟩, ⟨x, w⟩), rfl⟩ =
      ⟨x, (whitneySumFiberEquiv A D x).symm (u, w)⟩ := by
  refine congrArg (TotalSpace.mk' Unit x) ?_
  apply (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).injective
  simp [whitneySumTotalInrFiber, whitneySumFiberEquiv_symm_apply]

/-- `whitneySumTotalSpaceHomeomorph` intertwines `whitneyMap f g` on the Whitney sum with the
componentwise action of `f` and `g` on the fibre product of total spaces. -/
theorem whitneySumTotalSpaceHomeomorph_naturality {A A' D D' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') (p : TotalSpace Unit (whitneySum A D).Fiber) :
    whitneySumTotalSpaceHomeomorph A' D' ((whitneyMap f g).totalSpaceMap p) =
      ⟨(f.totalSpaceMap (whitneySumTotalSpaceHomeomorph A D p).1.1,
        g.totalSpaceMap (whitneySumTotalSpaceHomeomorph A D p).1.2),
        (f.proj_totalSpaceMap _).trans
          ((whitneySumTotalSpaceHomeomorph A D p).2.trans (g.proj_totalSpaceMap _).symm)⟩ := by
  rcases p with ⟨x, v⟩
  rw [(whitneyMap f g).totalSpaceMap_mk, whitneySumTotalSpaceHomeomorph_apply,
    whitneySumTotalSpaceHomeomorph_apply]
  refine Subtype.ext (Prod.ext ?_ ?_)
  · dsimp only
    rw [f.totalSpaceMap_mk]
    exact congrArg (TotalSpace.mk' Unit x)
      (congrArg Prod.fst (whitneySumFiberEquiv_fiberMap_whitneyMap f g x v))
  · dsimp only
    rw [g.totalSpaceMap_mk]
    exact congrArg (TotalSpace.mk' Unit x)
      (congrArg Prod.snd (whitneySumFiberEquiv_fiberMap_whitneyMap f g x v))

end TotalSpace

end TauCeti.FiniteRankAtlas
