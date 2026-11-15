/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Chart-operator encoding, isomorphism criterion, and fixed-rank comparison for bundle atlases

Between `A, D : FiniteRankAtlas 𝕜 X`, the base decomposes into clopen pairwise-rank strata
`RankPairStratum A D m n = {x : X // A.rank x = m ∧ D.rank x = n}` carrying pulled-back
constant-rank cores `sourcePairCore` and `targetPairCore`. Compatible chart-operator families
assemble into morphisms `A ⟶ D` (`ofCoordinateHom`) without completeness on `𝕜`. Over a complete
field, `toCoordinateHom` provides a two-sided inverse (`ofCoordinateHom_toCoordinateHom`,
`toCoordinateHom_ofCoordinateHom`, packaged as `coordinateHomAddEquiv`), `toCoordinateHom_id`
computes the image of `𝟙 A` on each diagonal stratum, and `isIso_iff_bijective` characterizes
isomorphisms by fibrewise bijectivity. Constant-rank cores embed via `ofCoreFunctor` with essential
image the globally constant-rank atlases (`mem_essImage_ofCoreFunctor_iff`).

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory Topology VectorBundleCore TauCeti.VariableRankBundle

namespace TauCeti.FiniteRankAtlas
universe u v
variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

/-- View the `n`th rank-stratum core of an atlas as a `FiniteRankBundleCore`. -/
-- Expose the rank projection so dependent coordinate fibres reduce during simp matching.
@[expose, implicit_reducible]
def stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    FiniteRankBundleCore 𝕜 {x : X // A.rank x = n} :=
  { rank := n, core := A.charts n, indexAt_eq := A.indexAt_eq n }
@[simp] theorem rank_stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (A.stratumCore n).rank = n := by rfl
@[simp] theorem core_stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (A.stratumCore n).core = A.charts n := by rfl

private def pullbackCoreToTotalSpace (A : FiniteRankAtlas 𝕜 X) {Y : Type*} [TopologicalSpace Y]
    (n : ℕ) (g : C(Y, {x : X // A.rank x = n})) :
    C(((A.stratumCore n).pullback g).core.TotalSpace, TotalSpace Unit A.Fiber) where
  toFun p := ⟨(g p.proj).1, fun i ↦ p.2 (Fin.cast (g p.proj).2 i)⟩
  continuous_toFun := ((totalSpaceHomeomorph A).continuous.comp
    (continuous_sigmaMk.comp ((A.stratumCore n).continuous_pullbackLift g))).congr fun ⟨_, _⟩ ↦ by
      dsimp only [Function.comp_apply]; rw [totalSpaceHomeomorph_apply]; rfl
@[simp] private theorem pullbackCoreToTotalSpace_apply (A : FiniteRankAtlas 𝕜 X) {Y : Type*}
    [TopologicalSpace Y] (n : ℕ) (g : C(Y, {x : X // A.rank x = n}))
    (p : ((A.stratumCore n).pullback g).core.TotalSpace) :
    pullbackCoreToTotalSpace A n g p = ⟨(g p.proj).1, fun i ↦ p.2 (Fin.cast (g p.proj).2 i)⟩ := by
  rfl

/-- The clopen stratum on which `A` has rank `m` and `D` has rank `n`. -/
abbrev RankPairStratum (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) : Type u :=
  {x : X // A.rank x = m ∧ D.rank x = n}
/-- Inclusion of the `(m, n)` pairwise stratum into the `m`th stratum of `A`. -/
-- Expose the subtype projection so `rankPairFst A A n n` and `rankPairSnd A A n n` coincide.
@[expose]
def rankPairFst (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :
    C(RankPairStratum A D m n, {x : X // A.rank x = m}) :=
  ⟨fun x ↦ ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk fun x ↦ x.2.1⟩
/-- Inclusion of the `(m, n)` pairwise stratum into the `n`th stratum of `D`. -/
-- Expose the subtype projection so `rankPairFst A A n n` and `rankPairSnd A A n n` coincide.
@[expose]
def rankPairSnd (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :
    C(RankPairStratum A D m n, {x : X // D.rank x = n}) :=
  ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk fun x ↦ x.2.2⟩
/-- The source core restricted to the `(m, n)` pairwise stratum. -/
-- Expose the rank projection so dependent coordinate fibres reduce to `Fin m → 𝕜`.
@[expose, implicit_reducible]
def sourcePairCore (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :
    FiniteRankBundleCore 𝕜 (RankPairStratum A D m n) :=
  (A.stratumCore m).pullback (rankPairFst A D m n)
/-- The target core restricted to the `(m, n)` pairwise stratum. -/
-- Expose the rank projection so dependent coordinate fibres reduce to `Fin n → 𝕜`.
@[expose, implicit_reducible]
def targetPairCore (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :
    FiniteRankBundleCore 𝕜 (RankPairStratum A D m n) :=
  (D.stratumCore n).pullback (rankPairSnd A D m n)
@[simp] theorem rank_sourcePairCore (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :
    (sourcePairCore A D m n).rank = m := by rfl
@[simp] theorem rank_targetPairCore (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :
    (targetPairCore A D m n).rank = n := by rfl

section Assemble
variable {A D : FiniteRankAtlas 𝕜 X}

/-- Glue compatible chart-operator morphisms on all pairwise rank strata into a morphism of
variable-rank bundle atlases. -/
def ofCoordinateHom (c : ∀ m n : ℕ, sourcePairCore A D m n ⟶ targetPairCore A D m n) : A ⟶ D where
  fiberMap x := ((c (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩).toLinearMap
  continuous_totalSpaceMap := by
    rw [← (totalSpaceHomeomorph A).comp_continuous_iff']
    refine continuous_sigma fun m ↦ continuous_of_cover_nhds
      (s := fun n : ℕ ↦ {q : (A.charts m).TotalSpace | D.rank q.proj.1 = n})
      (fun q ↦ ⟨D.rank q.proj.1, ((D.rank.isLocallyConstant.isOpen_fiber _).preimage
        (continuous_subtype_val.comp (A.charts m).continuous_proj)).mem_nhds rfl⟩) fun n ↦ ?_
    rw [continuousOn_iff_continuous_domRestrict]
    let srcMap : {q : (A.charts m).TotalSpace // D.rank q.proj.1 = n} →
        (sourcePairCore A D m n).core.TotalSpace := fun q ↦ ⟨⟨q.1.proj.1, q.1.proj.2, q.2⟩, q.1.2⟩
    have hsrc : Continuous srcMap :=
      ((A.stratumCore m).continuous_mk_pullback_iff (rankPairFst A D m n)).2
        ⟨(continuous_subtype_val.comp ((A.charts m).continuous_proj.comp
          continuous_subtype_val)).subtype_mk _, continuous_subtype_val⟩
    let tgtMap := pullbackCoreToTotalSpace D n (rankPairSnd A D m n)
    let totalMap : TotalSpace Unit A.Fiber → TotalSpace Unit D.Fiber := fun p ↦
      ⟨p.proj, ((c (A.rank p.proj) (D.rank p.proj)).fiberMap ⟨p.proj, rfl, rfl⟩).toLinearMap p.2⟩
    refine (tgtMap.continuous.comp ((c m n).continuous_totalSpaceMap.comp hsrc)).congr ?_
    rintro ⟨⟨⟨x, hm⟩, v⟩, hn⟩
    dsimp only [Set.domRestrict_apply, Function.comp_apply, srcMap, tgtMap] at hm hn ⊢
    subst hm; subst hn
    let k : CoordinateHom (sourcePairCore A D (A.rank x) (D.rank x)).core
        (targetPairCore A D (A.rank x) (D.rank x)).core := c (A.rank x) (D.rank x)
    have hA : totalSpaceHomeomorph A ⟨A.rank x, ⟨⟨x, rfl⟩, v⟩⟩ = ⟨x, v⟩ := by
      rw [totalSpaceHomeomorph_apply]; rfl
    have hk : pullbackCoreToTotalSpace D (D.rank x) (rankPairSnd A D (A.rank x) (D.rank x))
        (k.totalSpaceMap ⟨⟨x, rfl, rfl⟩, v⟩) = totalMap ⟨x, v⟩ := by
      rw [k.totalSpaceMap_mk ⟨x, rfl, rfl⟩ v, pullbackCoreToTotalSpace_apply]; rfl
    exact hk.trans (congrArg totalMap hA.symm)
@[simp] theorem fiberMap_ofCoordinateHom
    (c : ∀ m n : ℕ, sourcePairCore A D m n ⟶ targetPairCore A D m n) (x : X) :
    (ofCoordinateHom c).fiberMap x =
      ((c (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩).toLinearMap := by rfl
end Assemble

section Extract
variable [CompleteSpace 𝕜] {A D : FiniteRankAtlas 𝕜 X}

private def pairwiseFiberSection (f : A ⟶ D) (m n : ℕ) (z : RankPairStratum A D m n) :
    (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜) :=
  (LinearEquiv.funCongrLeft 𝕜 𝕜 (finCongr z.2.2.symm)).toContinuousLinearEquiv.toContinuousLinearMap
    ∘L (f.fiberMap z.1).toContinuousLinearMap
    ∘L (LinearEquiv.funCongrLeft 𝕜 𝕜 (finCongr z.2.1)).toContinuousLinearEquiv.toContinuousLinearMap
private theorem continuous_pairwiseFiberSection (f : A ⟶ D) (m n : ℕ) :
    Continuous fun z ↦ TotalSpace.mk' ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜))
      (E := fun y ↦ (sourcePairCore A D m n).core.Fiber y →L[𝕜]
        (targetPairCore A D m n).core.Fiber y) z (pairwiseFiberSection f m n z) := by
  refine (continuous_hom_bundle_iff (E₁ := (sourcePairCore A D m n).core.Fiber)
    (E₂ := (targetPairCore A D m n).core.Fiber) (pairwiseFiberSection f m n)).2 ?_
  have hcomp : Continuous (fun p : (sourcePairCore A D m n).core.TotalSpace ↦
      (⟨p.proj.1, f.fiberMap p.proj.1 (fun i ↦ p.2 (Fin.cast p.proj.2.1 i))⟩ :
        TotalSpace Unit D.Fiber)) :=
    (f.continuous_totalSpaceMap.comp
      (pullbackCoreToTotalSpace A m (rankPairFst A D m n)).continuous).congr fun _ ↦ rfl
  have hbase : Continuous (fun p : (sourcePairCore A D m n).core.TotalSpace ↦ p.proj.1) :=
    continuous_subtype_val.comp (sourcePairCore A D m n).core.continuous_proj
  have hstratum := ((continuous_mk_iff_rankStrata D hbase _).1 hcomp n).comp
    (Continuous.subtype_mk continuous_id fun p : (sourcePairCore A D m n).core.TotalSpace ↦
      p.proj.2.2)
  exact ((D.stratumCore n).continuous_mk_pullback_iff (rankPairSnd A D m n)).2
    ⟨(sourcePairCore A D m n).core.continuous_proj, hstratum.congr fun ⟨⟨_, _, _⟩, _⟩ ↦ rfl⟩

/-- Restrict a bundle-atlas morphism to a chart-operator morphism on the `(m, n)` pairwise
stratum. -/
def toCoordinateHom (f : A ⟶ D) (m n : ℕ) : sourcePairCore A D m n ⟶ targetPairCore A D m n :=
  CoordinateHom.ofContinuous (pairwiseFiberSection f m n) (continuous_pairwiseFiberSection f m n)
@[simp] theorem fiberMap_toCoordinateHom_apply (f : A ⟶ D) (m n : ℕ) (z : RankPairStratum A D m n)
    (v : Fin m → 𝕜) (j : Fin n) : (toCoordinateHom f m n).fiberMap z v j =
      f.fiberMap z.1 (fun i ↦ v (Fin.cast z.2.1 i)) (Fin.cast z.2.2.symm j) := by
  have h := congrFun (CoordinateHom.fiberMap_ofContinuous
    (Z := (sourcePairCore A D m n).core) (W := (targetPairCore A D m n).core)
    (pairwiseFiberSection f m n) (continuous_pairwiseFiberSection f m n)) z
  exact congrFun (congrArg (fun T : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜) ↦ T v) h) j
@[simp] theorem fiberMap_toCoordinateHom_self (f : A ⟶ D) (x : X) :
    (toCoordinateHom f (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩ =
      (f.fiberMap x).toContinuousLinearMap := by
  ext v j; exact fiberMap_toCoordinateHom_apply f (A.rank x) (D.rank x) ⟨x, rfl, rfl⟩ v j
@[simp] theorem ofCoordinateHom_toCoordinateHom (f : A ⟶ D) :
    ofCoordinateHom (toCoordinateHom f) = f :=
  hom_ext fun x ↦ LinearMap.ext fun v ↦ funext fun j ↦
    fiberMap_toCoordinateHom_apply f (A.rank x) (D.rank x) ⟨x, rfl, rfl⟩ v j
@[simp] theorem toCoordinateHom_ofCoordinateHom
    (c : ∀ m n : ℕ, sourcePairCore A D m n ⟶ targetPairCore A D m n) (m n : ℕ) :
    toCoordinateHom (ofCoordinateHom c) m n = c m n := by
  refine FiniteRankBundleCore.hom_ext fun ⟨x, hm, hn⟩ ↦ ?_; subst hm; subst hn; ext v j; simp

/-- Morphisms of variable-rank bundle atlases correspond additively to families of chart-operator
morphisms on the clopen pairwise rank strata. -/
def coordinateHomAddEquiv (A D : FiniteRankAtlas 𝕜 X) :
    (A ⟶ D) ≃+ ∀ m n : ℕ, sourcePairCore A D m n ⟶ targetPairCore A D m n where
  toFun := toCoordinateHom
  invFun := ofCoordinateHom
  left_inv := ofCoordinateHom_toCoordinateHom
  right_inv c := funext fun m ↦ funext fun n ↦ toCoordinateHom_ofCoordinateHom c m n
  map_add' f g := by
    ext m n : 2; refine FiniteRankBundleCore.hom_ext fun z ↦ ?_; ext v j
    simp only [Pi.add_apply, FiniteRankBundleCore.fiberMap_add, add_apply,
      fiberMap_toCoordinateHom_apply, fiberMap_add, LinearMap.add_apply]

@[simp] theorem toCoordinateHom_id (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    toCoordinateHom (𝟙 A) n n =
      (A.stratumCore n).pullbackMap (𝟙 (A.stratumCore n)) (rankPairFst A A n n) := by
  apply FiniteRankBundleCore.hom_ext; rintro ⟨x, rfl, h₂⟩; cases Subsingleton.elim h₂ rfl; ext v j
  have h₁ := fiberMap_toCoordinateHom_apply (𝟙 A) (A.rank x) (A.rank x) ⟨x, rfl, rfl⟩ v j
  have h₂ := congrFun (congrArg (fun T : (Fin (A.rank x) → 𝕜) →L[𝕜] (Fin (A.rank x) → 𝕜) ↦ T v)
    (FiniteRankBundleCore.fiberMap_pullbackMap (𝟙 (A.stratumCore (A.rank x)))
      (rankPairFst A A (A.rank x) (A.rank x)) ⟨x, rfl, rfl⟩)) j
  simp only [fiberMap_id, LinearMap.id_apply, Fin.cast_refl] at h₁
  simp only [FiniteRankBundleCore.fiberMap_id] at h₂
  exact h₁.trans h₂.symm

private def rankPairSwap (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :
    C(RankPairStratum D A n m, RankPairStratum A D m n) :=
  ⟨fun z ↦ ⟨z.1, z.2.2, z.2.1⟩, continuous_subtype_val.subtype_mk fun z ↦ ⟨z.2.2, z.2.1⟩⟩
private theorem isIso_toCoordinateHom_of_bijective {f : A ⟶ D}
    (hf : ∀ x : X, Function.Bijective (f.fiberMap x)) (m n : ℕ) :
    IsIso (toCoordinateHom f m n) :=
  (FiniteRankBundleCore.isIso_iff_bijective (toCoordinateHom f m n)).2 fun ⟨x, hm, hn⟩ ↦ by
    subst hm; subst hn; rw [fiberMap_toCoordinateHom_self]; exact hf x
private noncomputable def invCoordFamily (f : A ⟶ D)
    (hf : ∀ x : X, Function.Bijective (f.fiberMap x)) (n m : ℕ) :
    sourcePairCore D A n m ⟶ targetPairCore D A n m :=
  letI := isIso_toCoordinateHom_of_bijective hf m n
  FiniteRankBundleCore.pullbackMap (inv (toCoordinateHom f m n)) (rankPairSwap A D m n)
private theorem fiberMap_ofCoordinateHom_invCoordFamily (f : A ⟶ D)
    (hf : ∀ x : X, Function.Bijective (f.fiberMap x)) (x : X) :
    (ofCoordinateHom (invCoordFamily f hf)).fiberMap x =
      (LinearEquiv.ofBijective (f.fiberMap x) (hf x)).symm.toLinearMap := by
  have := isIso_toCoordinateHom_of_bijective hf (A.rank x) (D.rank x)
  let e := LinearEquiv.ofBijective (f.fiberMap x) (hf x)
  refine LinearMap.ext fun w ↦ e.injective ?_
  have hid := congrArg
    (fun k : targetPairCore A D (A.rank x) (D.rank x) ⟶ targetPairCore A D (A.rank x) (D.rank x) ↦
      k.fiberMap ⟨x, rfl, rfl⟩ w)
    (IsIso.inv_hom_id (toCoordinateHom f (A.rank x) (D.rank x)))
  have hpb := congrArg
    (fun T : (Fin (D.rank x) → 𝕜) →L[𝕜] (Fin (A.rank x) → 𝕜) ↦ f.fiberMap x (T w))
    (FiniteRankBundleCore.fiberMap_pullbackMap
      (inv (toCoordinateHom f (A.rank x) (D.rank x)))
      (rankPairSwap A D (A.rank x) (D.rank x)) ⟨x, rfl, rfl⟩)
  simp only [FiniteRankBundleCore.fiberMap_comp, FiniteRankBundleCore.fiberMap_id,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    fiberMap_toCoordinateHom_self, LinearMap.coe_toContinuousLinearMap'] at hid
  simp only [e, LinearEquiv.ofBijective_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, fiberMap_ofCoordinateHom, invCoordFamily,
    ContinuousLinearMap.coe_coe]
  exact hpb.trans hid

/-- A morphism of variable-rank bundle atlases is an isomorphism if and only if it is bijective on
every fibre. -/
theorem isIso_iff_bijective (f : A ⟶ D) : IsIso f ↔ ∀ x : X, Function.Bijective (f.fiberMap x) := by
  refine ⟨fun _ x ↦
    ((fiberFunctor (FiniteRankAtlas 𝕜 X) x).mapIso (asIso f)).toLinearEquiv.bijective,
    fun hf ↦ ⟨⟨ofCoordinateHom (invCoordFamily f hf), ?_, ?_⟩⟩⟩
  · refine hom_ext fun x ↦ LinearMap.ext fun v ↦ ?_
    rw [fiberMap_comp, fiberMap_id, LinearMap.comp_apply, LinearMap.id_apply,
      fiberMap_ofCoordinateHom_invCoordFamily f hf x]
    exact (LinearEquiv.ofBijective (f.fiberMap x) (hf x)).symm_apply_apply v
  · refine hom_ext fun x ↦ LinearMap.ext fun w ↦ ?_
    rw [fiberMap_comp, fiberMap_id, LinearMap.comp_apply, LinearMap.id_apply,
      fiberMap_ofCoordinateHom_invCoordFamily f hf x]
    exact (LinearEquiv.ofBijective (f.fiberMap x) (hf x)).apply_symm_apply w
end Extract

section FixedRank

/-- Inclusion of the `m`-stratum of `LocallyConstant.const X C.rank` into `X`. -/
def constStratumInclusion (C : FiniteRankBundleCore 𝕜 X) (m : ℕ) :
    C({x : X // LocallyConstant.const X C.rank x = m}, X) := ⟨Subtype.val, continuous_subtype_val⟩
/-- Coordinate core on the `m`-stratum of `LocallyConstant.const X C.rank`: the pullback of `C`
when `C.rank = m`, and the trivial core on the empty stratum otherwise. -/
def constStratumCharts (C : FiniteRankBundleCore 𝕜 X) (m : ℕ) :
    VectorBundleCore 𝕜 {x : X // LocallyConstant.const X C.rank x = m} (Fin m → 𝕜)
      {x : X // LocallyConstant.const X C.rank x = m} :=
  if h : C.rank = m then
    h.rec (motive := fun k _ ↦ VectorBundleCore 𝕜
      {x : X // LocallyConstant.const X C.rank x = m} (Fin k → 𝕜)
      {x : X // LocallyConstant.const X C.rank x = m}) (C.pullback (constStratumInclusion C m)).core
  else (FiniteRankBundleCore.trivial 𝕜 {x : X // LocallyConstant.const X C.rank x = m} m).core

/-- Embed a constant-rank point-indexed core as a variable-rank bundle atlas of constant rank. -/
-- Expose the rank projection so `(ofCore C).Fiber` reduces to `C`'s coordinate fibre.
@[expose, implicit_reducible]
def ofCore (C : FiniteRankBundleCore 𝕜 X) : FiniteRankAtlas 𝕜 X where
  rank := LocallyConstant.const X C.rank
  charts := constStratumCharts C
  indexAt_eq m x := by
    by_cases h : C.rank = m
    · subst h
      rw [show constStratumCharts C C.rank = (C.pullback (constStratumInclusion C C.rank)).core from
        dite_eq_left_of_eq_true (eq_true rfl)]; rfl
    · exact False.elim (h x.2)
@[simp] theorem rank_ofCore (C : FiniteRankBundleCore 𝕜 X) :
    (ofCore C).rank = LocallyConstant.const X C.rank := by rfl
theorem rank_ofCore_apply (C : FiniteRankBundleCore 𝕜 X) (x : X) : (ofCore C).rank x = C.rank := by
  rfl
@[simp] theorem charts_ofCore_self (C : FiniteRankBundleCore 𝕜 X) :
    (ofCore C).charts C.rank = (C.pullback (constStratumInclusion C C.rank)).core :=
  dite_eq_left_of_eq_true (eq_true rfl)

private def chartsOfCoreSelfPkg (C : FiniteRankBundleCore 𝕜 X) :
    { e : ((ofCore C).charts C.rank).TotalSpace ≃ₜ C.core.TotalSpace //
      (∀ q, e q = ⟨q.proj.1, q.2⟩) ∧ (∀ r, e.symm r = ⟨⟨r.proj, rfl⟩, r.2⟩) } :=
  let aux : ∀ (Z : VectorBundleCore 𝕜 {x : X // (ofCore C).rank x = C.rank} (Fin C.rank → 𝕜)
      {x : X // (ofCore C).rank x = C.rank}),
      Z = (C.pullback (constStratumInclusion C C.rank)).core →
      { e : Z.TotalSpace ≃ₜ C.core.TotalSpace //
        (∀ q, e q = ⟨q.proj.1, q.2⟩) ∧ (∀ r, e.symm r = ⟨⟨r.proj, rfl⟩, r.2⟩) } := by
    rintro _ rfl
    exact ⟨{
      toFun q := ⟨q.proj.1, q.2⟩, invFun r := ⟨⟨r.proj, rfl⟩, r.2⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl, right_inv := fun ⟨_, _⟩ ↦ rfl
      continuous_toFun := C.continuous_pullbackLift (constStratumInclusion C C.rank)
      continuous_invFun := (C.continuous_mk_pullback_iff (constStratumInclusion C C.rank)).2
        ⟨C.core.continuous_proj.subtype_mk fun _ ↦ rfl, continuous_id⟩ },
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  aux ((ofCore C).charts C.rank) (charts_ofCore_self C)

/-- The reconstructed total space of `ofCore C` is homeomorphic over `X` to `C.core.TotalSpace`. -/
def ofCoreTotalSpaceHomeomorph (C : FiniteRankBundleCore 𝕜 X) :
    TotalSpace Unit (ofCore C).Fiber ≃ₜ C.core.TotalSpace :=
  let pkg := chartsOfCoreSelfPkg C
  totalSpaceHomeomorphOfConstStratum (ofCore C) (fun _ ↦ rfl) pkg.1
    (fun _ ↦ Equiv.refl _) (fun x v ↦ pkg.2.1 ⟨⟨x, rfl⟩, v⟩) (fun x v ↦ pkg.2.2 ⟨x, v⟩)
@[simp] theorem ofCoreTotalSpaceHomeomorph_apply (C : FiniteRankBundleCore 𝕜 X)
    (p : TotalSpace Unit (ofCore C).Fiber) : ofCoreTotalSpaceHomeomorph C p = ⟨p.proj, p.2⟩ :=
  totalSpaceHomeomorphOfConstStratum_apply _ _ _ _ _ _ p
@[simp] theorem ofCoreTotalSpaceHomeomorph_symm_apply (C : FiniteRankBundleCore 𝕜 X)
    (p : C.core.TotalSpace) : (ofCoreTotalSpaceHomeomorph C).symm p = ⟨p.proj, p.2⟩ :=
  totalSpaceHomeomorphOfConstStratum_symm_apply _ _ _ _ _ _ p

variable (𝕜 X) in
/-- The additive embedding of constant-rank point-indexed cores into variable-rank bundle
atlases. -/
-- Expose the object map so `(ofCoreFunctor 𝕜 X).obj C` reduces to `ofCore C` in morphism types.
@[expose, implicit_reducible]
def ofCoreFunctor : FiniteRankBundleCore 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj := ofCore
  map {C₁ C₂} f :=
    { fiberMap x := (f.fiberMap x).toLinearMap
      continuous_totalSpaceMap := ((ofCoreTotalSpaceHomeomorph C₂).symm.continuous.comp
        (f.continuous_totalSpaceMap.comp (ofCoreTotalSpaceHomeomorph C₁).continuous)).congr
        fun ⟨x, v⟩ ↦ by
          dsimp only [Function.comp_apply]
          rw [ofCoreTotalSpaceHomeomorph_apply, f.totalSpaceMap_mk x v,
            ofCoreTotalSpaceHomeomorph_symm_apply]; rfl }
  -- `LocallyConstant.const` is semireducible, so `rfl` unifies `(ofCore _).Fiber x` with
  -- `Fin _.rank → 𝕜` after `simp` normalizes the fibrewise linear maps.
  map_id _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp; rfl
  map_comp _ _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp; rfl
@[simp] theorem ofCoreFunctor_obj (C : FiniteRankBundleCore 𝕜 X) :
    (ofCoreFunctor 𝕜 X).obj C = ofCore C := by rfl
@[simp] theorem fiberMap_ofCoreFunctor_map {C₁ C₂ : FiniteRankBundleCore 𝕜 X}
    (f : C₁ ⟶ C₂) (x : X) :
    ((ofCoreFunctor 𝕜 X).map f).fiberMap x = (f.fiberMap x).toLinearMap := by rfl
instance : (ofCoreFunctor 𝕜 X).Additive where
  -- Unify `((ofCoreFunctor 𝕜 X).obj _).Fiber x` with `Fin _.rank → 𝕜` via `LocallyConstant.const`.
  map_add {_ _ _ _} := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp; rfl
instance : (ofCoreFunctor 𝕜 X).Faithful where
  map_injective {C₁ C₂} _ _ h := FiniteRankBundleCore.hom_ext fun x ↦ ContinuousLinearMap.ext
    fun v ↦ congrArg (fun k : ofCore C₁ ⟶ ofCore C₂ ↦ k.fiberMap x v) h

private theorem continuous_ofCorePreimageSection [CompleteSpace 𝕜]
    {C₁ C₂ : FiniteRankBundleCore 𝕜 X} (g : ofCore C₁ ⟶ ofCore C₂) :
    Continuous fun x ↦ TotalSpace.mk' ((Fin C₁.rank → 𝕜) →L[𝕜] (Fin C₂.rank → 𝕜))
      (E := fun y ↦ C₁.core.Fiber y →L[𝕜] C₂.core.Fiber y) x
      (g.fiberMap x).toContinuousLinearMap :=
  (continuous_hom_bundle_iff (E₁ := C₁.core.Fiber) (E₂ := C₂.core.Fiber)
    (fun x ↦ (g.fiberMap x).toContinuousLinearMap)).2 <|
    ((ofCoreTotalSpaceHomeomorph C₂).continuous.comp (g.continuous_totalSpaceMap.comp
      (ofCoreTotalSpaceHomeomorph C₁).symm.continuous)).congr fun ⟨x, v⟩ ↦ by
        dsimp only [Function.comp_apply]
        rw [ofCoreTotalSpaceHomeomorph_symm_apply, ofCoreTotalSpaceHomeomorph_apply]; rfl
/-- Over a complete scalar field, `ofCoreFunctor` is fully faithful. -/
def fullyFaithfulOfCoreFunctor [CompleteSpace 𝕜] : (ofCoreFunctor 𝕜 X).FullyFaithful where
  preimage g := CoordinateHom.ofContinuous _ (continuous_ofCorePreimageSection g)
  map_preimage {C₁ C₂} g := hom_ext fun x ↦ LinearMap.ext fun v ↦
    congrArg (fun T : (Fin C₁.rank → 𝕜) →L[𝕜] (Fin C₂.rank → 𝕜) ↦ T v)
      (congrFun (CoordinateHom.fiberMap_ofContinuous (Z := C₁.core) (W := C₂.core) _
        (continuous_ofCorePreimageSection g)) x)
  preimage_map {C₁ C₂} f := FiniteRankBundleCore.hom_ext fun x ↦
    congrFun (CoordinateHom.fiberMap_ofContinuous (Z := C₁.core) (W := C₂.core) _
      (continuous_ofCorePreimageSection ((ofCoreFunctor 𝕜 X).map f))) x
instance [CompleteSpace 𝕜] : (ofCoreFunctor 𝕜 X).Full :=
  (fullyFaithfulOfCoreFunctor (𝕜 := 𝕜) (X := X)).full

/-- A variable-rank bundle atlas lies in the essential image of `ofCoreFunctor` if and only if its
locally constant rank function is globally constant. -/
theorem mem_essImage_ofCoreFunctor_iff (A : FiniteRankAtlas 𝕜 X) :
    (ofCoreFunctor 𝕜 X).essImage A ↔ ∃ n : ℕ, A.rank = LocallyConstant.const X n := by
  refine ⟨fun ⟨C, ⟨e⟩⟩ ↦ ⟨C.rank, e.symm.variableRankBundle_rank_eq.trans (rank_ofCore C)⟩, ?_⟩
  rintro ⟨n, hn⟩
  have hnx (x : X) : rank A x = n := congrFun (congrArg DFunLike.coe hn) x
  let inc := constRankInclusion (V := A) hnx
  let C : FiniteRankBundleCore 𝕜 X := (A.stratumCore n).pullback inc
  refine ⟨C, ⟨isoOfTotalSpaceHomeomorph (fun x ↦ LinearEquiv.funCongrLeft 𝕜 𝕜 (finCongr (hnx x)))
    ((ofCoreTotalSpaceHomeomorph C).trans
      (((A.stratumCore n).pullbackHomeomorph inc).trans (constRankTotalSpaceHomeomorph A hnx).symm))
    fun x v ↦ by
      rw [Homeomorph.trans_apply, ofCoreTotalSpaceHomeomorph_apply, Homeomorph.trans_apply,
        FiniteRankBundleCore.pullbackHomeomorph_apply, constRankTotalSpaceHomeomorph_symm_apply]
      exact TotalSpace.ext rfl (heq_of_eq (funext fun i ↦ congrArg v (Fin.ext rfl)))⟩⟩

end FixedRank
end TauCeti.FiniteRankAtlas
