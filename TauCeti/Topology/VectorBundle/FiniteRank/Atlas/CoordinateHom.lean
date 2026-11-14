/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback

/-!
# Chart-operator encoding, isomorphism criterion, and fixed-rank comparison for bundle atlases

Between two variable-rank bundle atlases `A, D : FiniteRankAtlas 𝕜 X`, the base space decomposes
into clopen pairwise-rank strata `RankPairStratum A D m n = {x : X // A.rank x = m ∧ D.rank x = n}`
on which `A` has constant rank `m` and `D` has constant rank `n`. Restricting `A.charts m` and
`D.charts n` to each pairwise stratum yields constant-rank point-indexed cores `sourcePairCore` and
`targetPairCore`.

Compatible families of chart operators across these pairwise strata assemble into morphisms
`A ⟶ D` (`ofCoordinateHom`) with no completeness assumption on `𝕜`. Over a complete scalar field,
every morphism `A ⟶ D` comes from a unique such family (`toCoordinateHom`), yielding an additive
equivalence `coordinateHomAddEquiv` between `A ⟶ D` and `∏_{m, n} (sourcePairCore ⟶ targetPairCore)`
compatible with the identity (`toCoordinateHom_id`). As a consequence, `isIso_iff_bijective`
characterizes categorical isomorphisms in `FiniteRankAtlas 𝕜 X` by fibrewise bijectivity.

Constant-rank point-indexed cores embed into variable-rank atlases via the additive functor
`ofCoreFunctor : FiniteRankBundleCore 𝕜 X ⥤ FiniteRankAtlas 𝕜 X`, which is faithful unconditionally,
fully faithful over a complete scalar field, and has essential image the atlases of globally
constant rank (`mem_essImage_ofCoreFunctor_iff`).

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory Topology VectorBundleCore

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

/-- View the `n`th rank-stratum core of an atlas as a `FiniteRankBundleCore`. -/
-- Expose the rank projection so dependent coordinate fibres reduce during simp matching.
@[expose, implicit_reducible]
def stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    FiniteRankBundleCore 𝕜 {x : X // A.rank x = n} where
  rank := n
  core := A.charts n
  indexAt_eq := A.indexAt_eq n

@[simp]
theorem rank_stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (A.stratumCore n).rank = n := (rfl)

@[simp]
theorem core_stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (A.stratumCore n).core = A.charts n := (rfl)

/-- The clopen stratum on which `A` has rank `m` and `D` has rank `n`. -/
abbrev RankPairStratum (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) : Type u :=
  {x : X // A.rank x = m ∧ D.rank x = n}

/-- Inclusion of the `(m, n)` pairwise stratum into the `m`th stratum of `A`. -/
-- Expose the subtype projection so `rankPairFst A A n n` and `rankPairSnd A A n n` coincide.
@[expose]
def rankPairFst (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :
    C(RankPairStratum A D m n, {x : X // A.rank x = m}) where
  toFun x := ⟨x.1, x.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk fun x ↦ x.2.1

/-- Inclusion of the `(m, n)` pairwise stratum into the `n`th stratum of `D`. -/
-- Expose the subtype projection so `rankPairFst A A n n` and `rankPairSnd A A n n` coincide.
@[expose]
def rankPairSnd (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :
    C(RankPairStratum A D m n, {x : X // D.rank x = n}) where
  toFun x := ⟨x.1, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk fun x ↦ x.2.2

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

@[simp]
theorem rank_sourcePairCore (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :
    (sourcePairCore A D m n).rank = m := (rfl)

@[simp]
theorem rank_targetPairCore (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :
    (targetPairCore A D m n).rank = n := (rfl)

section Assemble

variable {A D : FiniteRankAtlas 𝕜 X}

/-- Glue compatible chart-operator morphisms on all pairwise rank strata into a morphism of
variable-rank bundle atlases. -/
def ofCoordinateHom
    (c : ∀ m n : ℕ, sourcePairCore A D m n ⟶ targetPairCore A D m n) : A ⟶ D where
  fiberMap x := ((c (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩).toLinearMap
  continuous_totalSpaceMap := by
    rw [← A.totalSpaceHomeomorph.comp_continuous_iff']
    refine continuous_sigma fun m ↦ ?_
    refine continuous_of_cover_nhds (s := fun n : ℕ ↦
      {q : (A.charts m).TotalSpace | D.rank q.proj.1 = n}) ?_ ?_
    · intro q
      exact ⟨D.rank q.proj.1, ((D.rank.isLocallyConstant.isOpen_fiber _).preimage
        (continuous_subtype_val.comp (A.charts m).continuous_proj)).mem_nhds rfl⟩
    · intro n
      rw [continuousOn_iff_continuous_domRestrict]
      let toPull : {q : (A.charts m).TotalSpace // D.rank q.proj.1 = n} →
          TotalSpace (Fin m → 𝕜) ((⇑(rankPairFst A D m n)) *ᵖ (A.charts m).Fiber) :=
        fun q ↦ ⟨⟨q.1.proj.1, q.1.proj.2, q.2⟩, q.1.2⟩
      have htoPull : Continuous toPull := by
        rw [(inducing_pullbackTotalSpaceEmbedding (Fin m → 𝕜) (A.charts m).Fiber
          (rankPairFst A D m n)).continuous_iff]
        refine Continuous.prodMk ?_ continuous_subtype_val
        exact (continuous_subtype_val.comp
          ((A.charts m).continuous_proj.comp continuous_subtype_val)).subtype_mk _
      let srcMap : {q : (A.charts m).TotalSpace // D.rank q.proj.1 = n} →
          (sourcePairCore A D m n).core.TotalSpace :=
        ((A.stratumCore m).pullbackHomeomorph (rankPairFst A D m n)).symm ∘ toPull
      have hsrc : Continuous srcMap :=
        ((A.stratumCore m).pullbackHomeomorph (rankPairFst A D m n)).symm.continuous.comp htoPull
      let tgtMap : (targetPairCore A D m n).core.TotalSpace → TotalSpace Unit D.Fiber :=
        fun r ↦ D.totalSpaceHomeomorph ⟨n,
          Pullback.lift (rankPairSnd A D m n)
            ((D.stratumCore n).pullbackHomeomorph (rankPairSnd A D m n) r)⟩
      have htgt : Continuous tgtMap :=
        D.totalSpaceHomeomorph.continuous.comp <| continuous_sigmaMk.comp <|
          (Pullback.continuous_lift (Fin n → 𝕜) (D.charts n).Fiber (rankPairSnd A D m n)).comp
            ((D.stratumCore n).pullbackHomeomorph (rankPairSnd A D m n)).continuous
      let totalMap : TotalSpace Unit A.Fiber → TotalSpace Unit D.Fiber := fun p ↦
        ⟨p.proj, ((c (A.rank p.proj) (D.rank p.proj)).fiberMap ⟨p.proj, rfl, rfl⟩).toLinearMap p.2⟩
      refine (htgt.comp ((c m n).continuous_totalSpaceMap.comp hsrc)).congr ?_
      rintro ⟨⟨⟨x, hm⟩, v⟩, hn⟩
      dsimp only [Set.domRestrict_apply, Function.comp_apply, srcMap, toPull, tgtMap] at hm hn ⊢
      subst hm; subst hn
      rw [FiniteRankBundleCore.pullbackHomeomorph_symm_apply]
      let k : CoordinateHom (sourcePairCore A D (A.rank x) (D.rank x)).core
          (targetPairCore A D (A.rank x) (D.rank x)).core := c (A.rank x) (D.rank x)
      -- Express the RHS via the non-dependent map `totalMap` so `hA` rewrites without motive casts.
      change D.totalSpaceHomeomorph ⟨D.rank x, Pullback.lift (rankPairSnd A D (A.rank x) (D.rank x))
        ((D.stratumCore (D.rank x)).pullbackHomeomorph (rankPairSnd A D (A.rank x) (D.rank x))
          (k.totalSpaceMap ⟨⟨x, rfl, rfl⟩, v⟩))⟩ =
        totalMap (A.totalSpaceHomeomorph ⟨A.rank x, ⟨⟨x, rfl⟩, v⟩⟩)
      rw [k.totalSpaceMap_mk ⟨x, rfl, rfl⟩ v, FiniteRankBundleCore.pullbackHomeomorph_apply]
      dsimp only [Pullback.lift]
      have hA : A.totalSpaceHomeomorph ⟨A.rank x, ⟨⟨x, rfl⟩, v⟩⟩ = ⟨x, v⟩ := by
        rw [totalSpaceHomeomorph_apply]
        rfl
      rw [hA, totalSpaceHomeomorph_apply]
      rfl

@[simp]
theorem fiberMap_ofCoordinateHom
    (c : ∀ m n : ℕ, sourcePairCore A D m n ⟶ targetPairCore A D m n) (x : X) :
    (ofCoordinateHom c).fiberMap x =
      ((c (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩).toLinearMap := (rfl)

end Assemble

section Extract

variable [CompleteSpace 𝕜] {A D : FiniteRankAtlas 𝕜 X}

private def castSourceEquiv {m n : ℕ} (z : RankPairStratum A D m n) :
    (Fin m → 𝕜) ≃L[𝕜] A.Fiber z.1 :=
  (LinearEquiv.funCongrLeft 𝕜 𝕜 (finCongr z.2.1)).toContinuousLinearEquiv

private def castTargetEquiv {m n : ℕ} (z : RankPairStratum A D m n) :
    D.Fiber z.1 ≃L[𝕜] (Fin n → 𝕜) :=
  (LinearEquiv.funCongrLeft 𝕜 𝕜 (finCongr z.2.2.symm)).toContinuousLinearEquiv

private def pairwiseFiberSection (f : A ⟶ D) (m n : ℕ)
    (z : RankPairStratum A D m n) : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜) :=
  (castTargetEquiv z).toContinuousLinearMap.comp
    ((f.fiberMap z.1).toContinuousLinearMap.comp (castSourceEquiv z).toContinuousLinearMap)

private theorem continuous_pairwiseFiberSection (f : A ⟶ D) (m n : ℕ) :
    Continuous fun z ↦ TotalSpace.mk' ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜))
      (E := fun y ↦ (sourcePairCore A D m n).core.Fiber y →L[𝕜]
        (targetPairCore A D m n).core.Fiber y) z (pairwiseFiberSection f m n z) := by
  refine (continuous_hom_bundle_iff
    (E₁ := (sourcePairCore A D m n).core.Fiber)
    (E₂ := (targetPairCore A D m n).core.Fiber) (pairwiseFiberSection f m n)).2 ?_
  let toA : (sourcePairCore A D m n).core.TotalSpace → TotalSpace Unit A.Fiber := fun p ↦
    A.totalSpaceHomeomorph ⟨m,
      Pullback.lift (rankPairFst A D m n)
        ((A.stratumCore m).pullbackHomeomorph (rankPairFst A D m n) p)⟩
  have htoA : Continuous toA :=
    A.totalSpaceHomeomorph.continuous.comp <| continuous_sigmaMk.comp <|
      (Pullback.continuous_lift (Fin m → 𝕜) (A.charts m).Fiber (rankPairFst A D m n)).comp
        ((A.stratumCore m).pullbackHomeomorph (rankPairFst A D m n)).continuous
  have hcomp : Continuous (fun p : (sourcePairCore A D m n).core.TotalSpace ↦
      (⟨p.proj.1, f.fiberMap p.proj.1 (fun i ↦ p.2 (Fin.cast p.proj.2.1 i))⟩ :
        TotalSpace Unit D.Fiber)) := by
    refine (f.totalSpaceMap.continuous.comp htoA).congr ?_
    rintro ⟨⟨x, hm, hn⟩, v⟩
    dsimp only [Function.comp_apply]
    have htoA_eq : toA ⟨⟨x, hm, hn⟩, v⟩ = ⟨x, fun i ↦ v (Fin.cast hm i)⟩ := by
      dsimp only [toA]
      rw [FiniteRankBundleCore.pullbackHomeomorph_apply]
      dsimp only [Pullback.lift]
      rw [totalSpaceHomeomorph_apply]
      rfl
    rw [htoA_eq, f.totalSpaceMap_mk]
  have hbase : Continuous (fun p : (sourcePairCore A D m n).core.TotalSpace ↦ p.proj.1) :=
    continuous_subtype_val.comp (sourcePairCore A D m n).core.continuous_proj
  have hstratum := ((D.continuous_mk_iff_rankStrata hbase _).1 hcomp n).comp
    (Continuous.subtype_mk continuous_id fun p : (sourcePairCore A D m n).core.TotalSpace ↦
      p.proj.2.2)
  let toPullD : (sourcePairCore A D m n).core.TotalSpace →
      TotalSpace (Fin n → 𝕜) ((⇑(rankPairSnd A D m n)) *ᵖ (D.charts n).Fiber) :=
    fun p ↦ ⟨p.proj, pairwiseFiberSection f m n p.proj p.2⟩
  have htoPullD : Continuous toPullD := by
    rw [(inducing_pullbackTotalSpaceEmbedding (Fin n → 𝕜) (D.charts n).Fiber
      (rankPairSnd A D m n)).continuous_iff]
    refine (sourcePairCore A D m n).core.continuous_proj.prodMk ?_
    refine hstratum.congr ?_
    rintro ⟨⟨x, hm, hn⟩, v⟩
    rfl
  refine (((D.stratumCore n).pullbackHomeomorph (rankPairSnd A D m n)).symm.continuous.comp
    htoPullD).congr ?_
  rintro ⟨z, v⟩
  dsimp only [Function.comp_apply, toPullD]
  exact FiniteRankBundleCore.pullbackHomeomorph_symm_apply (D.stratumCore n)
    (rankPairSnd A D m n) ⟨z, pairwiseFiberSection f m n z v⟩

/-- Restrict a bundle-atlas morphism to a chart-operator morphism on the `(m, n)` pairwise
stratum. -/
def toCoordinateHom (f : A ⟶ D) (m n : ℕ) :
    sourcePairCore A D m n ⟶ targetPairCore A D m n :=
  CoordinateHom.ofContinuous (pairwiseFiberSection f m n) (continuous_pairwiseFiberSection f m n)

@[simp]
theorem fiberMap_toCoordinateHom_apply (f : A ⟶ D) (m n : ℕ)
    (z : RankPairStratum A D m n) (v : Fin m → 𝕜) (j : Fin n) :
    (toCoordinateHom f m n).fiberMap z v j =
      f.fiberMap z.1 (fun i ↦ v (Fin.cast z.2.1 i)) (Fin.cast z.2.2.symm j) := by
  have h := congrFun (CoordinateHom.fiberMap_ofContinuous
    (Z := (sourcePairCore A D m n).core) (W := (targetPairCore A D m n).core)
    (pairwiseFiberSection f m n) (continuous_pairwiseFiberSection f m n)) z
  exact congrFun (congrArg (fun T : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜) ↦ T v) h) j

@[simp]
theorem ofCoordinateHom_toCoordinateHom (f : A ⟶ D) :
    ofCoordinateHom (toCoordinateHom f) = f := by
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro v
  funext j
  exact fiberMap_toCoordinateHom_apply f (A.rank x) (D.rank x) ⟨x, rfl, rfl⟩ v j

@[simp]
theorem toCoordinateHom_ofCoordinateHom
    (c : ∀ m n : ℕ, sourcePairCore A D m n ⟶ targetPairCore A D m n) (m n : ℕ) :
    toCoordinateHom (ofCoordinateHom c) m n = c m n := by
  apply FiniteRankBundleCore.hom_ext
  rintro ⟨x, hm, hn⟩
  ext v j
  rw [fiberMap_toCoordinateHom_apply]
  subst hm; subst hn
  rfl

/-- Morphisms of variable-rank bundle atlases correspond additively to families of chart-operator
morphisms on the clopen pairwise rank strata. -/
def coordinateHomAddEquiv (A D : FiniteRankAtlas 𝕜 X) :
    (A ⟶ D) ≃+ ∀ m n : ℕ, sourcePairCore A D m n ⟶ targetPairCore A D m n where
  toFun := toCoordinateHom
  invFun := ofCoordinateHom
  left_inv := ofCoordinateHom_toCoordinateHom
  right_inv c := funext fun m ↦ funext fun n ↦ toCoordinateHom_ofCoordinateHom c m n
  map_add' f g := by
    ext m n : 2
    apply FiniteRankBundleCore.hom_ext
    intro z
    ext v j
    simp only [Pi.add_apply, FiniteRankBundleCore.fiberMap_add, add_apply,
      fiberMap_toCoordinateHom_apply, fiberMap_add, LinearMap.add_apply]

@[simp]
theorem toCoordinateHom_id (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    toCoordinateHom (𝟙 A) n n =
      (A.stratumCore n).pullbackMap (𝟙 (A.stratumCore n)) (rankPairFst A A n n) := by
  apply FiniteRankBundleCore.hom_ext
  rintro ⟨x, rfl, h₂⟩
  have : h₂ = rfl := Subsingleton.elim _ _
  subst this
  ext v j
  have h₁ := fiberMap_toCoordinateHom_apply (𝟙 A) (A.rank x) (A.rank x) ⟨x, rfl, rfl⟩ v j
  have h₂ := congrFun (congrArg (fun T : (Fin (A.rank x) → 𝕜) →L[𝕜] (Fin (A.rank x) → 𝕜) ↦ T v)
    (FiniteRankBundleCore.fiberMap_pullbackMap (𝟙 (A.stratumCore (A.rank x)))
      (rankPairFst A A (A.rank x) (A.rank x)) ⟨x, rfl, rfl⟩)) j
  simp only [fiberMap_id, LinearMap.id_apply, Fin.cast_refl] at h₁
  simp only [FiniteRankBundleCore.fiberMap_id] at h₂
  exact h₁.trans h₂.symm

/-- Swap the pairwise rank-stratum conditions. -/
private def rankPairSwap (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :
    C(RankPairStratum D A n m, RankPairStratum A D m n) where
  toFun z := ⟨z.1, z.2.2, z.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk fun z ↦ ⟨z.2.2, z.2.1⟩

/-- A morphism of variable-rank bundle atlases is an isomorphism if and only if it is bijective on
every fibre. -/
theorem isIso_iff_bijective (f : A ⟶ D) :
    IsIso f ↔ ∀ x : X, Function.Bijective (f.fiberMap x) := by
  constructor
  · intro hf x
    exact ((fiberFunctor x).mapIso (asIso f)).toLinearEquiv.bijective
  · intro hf
    have hbij : ∀ (m n : ℕ) (z : RankPairStratum A D m n),
        Function.Bijective ((toCoordinateHom f m n).fiberMap z) := by
      rintro m n ⟨x, hm, hn⟩
      subst hm; subst hn
      have hfm : (toCoordinateHom f (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩ =
          (f.fiberMap x).toContinuousLinearMap := by
        ext v j
        exact fiberMap_toCoordinateHom_apply f (A.rank x) (D.rank x) ⟨x, rfl, rfl⟩ v j
      rw [hfm]
      exact hf x
    have hiso : ∀ m n : ℕ, IsIso (toCoordinateHom f m n) := fun m n ↦
      (FiniteRankBundleCore.isIso_iff_bijective (toCoordinateHom f m n)).2 (hbij m n)
    let invFamily : ∀ n m : ℕ, sourcePairCore D A n m ⟶ targetPairCore D A n m := fun n m ↦
      have := hiso m n
      FiniteRankBundleCore.pullbackMap (inv (toCoordinateHom f m n)) (rankPairSwap A D m n)
    let g : D ⟶ A := ofCoordinateHom invFamily
    refine ⟨⟨g, ?_, ?_⟩⟩
    · apply hom_ext
      intro x
      apply LinearMap.ext
      intro v
      funext j
      have := hiso (A.rank x) (D.rank x)
      have hid := congrArg
        (fun k : sourcePairCore A D (A.rank x) (D.rank x) ⟶
            sourcePairCore A D (A.rank x) (D.rank x) ↦
          k.fiberMap ⟨x, rfl, rfl⟩ v j)
        (IsIso.hom_inv_id (toCoordinateHom f (A.rank x) (D.rank x)))
      have hfx : (toCoordinateHom f (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩ v =
          f.fiberMap x v := by
        funext i
        exact fiberMap_toCoordinateHom_apply f (A.rank x) (D.rank x) ⟨x, rfl, rfl⟩ v i
      simp only [FiniteRankBundleCore.fiberMap_comp, FiniteRankBundleCore.fiberMap_id,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hfx] at hid
      have hpb := congrFun
        (congrArg (fun T : (Fin (D.rank x) → 𝕜) →L[𝕜] (Fin (A.rank x) → 𝕜) ↦ T (f.fiberMap x v))
          (FiniteRankBundleCore.fiberMap_pullbackMap
            (inv (toCoordinateHom f (A.rank x) (D.rank x)))
            (rankPairSwap A D (A.rank x) (D.rank x)) ⟨x, rfl, rfl⟩)) j
      exact hpb.trans hid
    · apply hom_ext
      intro x
      apply LinearMap.ext
      intro v
      funext j
      have := hiso (A.rank x) (D.rank x)
      have hid := congrArg
        (fun k : targetPairCore A D (A.rank x) (D.rank x) ⟶
            targetPairCore A D (A.rank x) (D.rank x) ↦
          k.fiberMap ⟨x, rfl, rfl⟩ v j)
        (IsIso.inv_hom_id (toCoordinateHom f (A.rank x) (D.rank x)))
      have hfx : ∀ w : Fin (A.rank x) → 𝕜,
          (toCoordinateHom f (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩ w =
            f.fiberMap x w := fun w ↦ by
        funext i
        exact fiberMap_toCoordinateHom_apply f (A.rank x) (D.rank x) ⟨x, rfl, rfl⟩ w i
      simp only [FiniteRankBundleCore.fiberMap_comp, FiniteRankBundleCore.fiberMap_id,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hfx] at hid
      have hpb : (invFamily (D.rank x) (A.rank x)).fiberMap ⟨x, rfl, rfl⟩ v =
          (inv (toCoordinateHom f (A.rank x) (D.rank x))).fiberMap ⟨x, rfl, rfl⟩ v :=
        congrArg (fun T : (Fin (D.rank x) → 𝕜) →L[𝕜] (Fin (A.rank x) → 𝕜) ↦ T v)
          (FiniteRankBundleCore.fiberMap_pullbackMap
            (inv (toCoordinateHom f (A.rank x) (D.rank x)))
            (rankPairSwap A D (A.rank x) (D.rank x)) ⟨x, rfl, rfl⟩)
      exact (congrFun (congrArg (f.fiberMap x) hpb) j).trans hid

end Extract

section FixedRank

/-- Inclusion of the `m`-stratum of `LocallyConstant.const X C.rank` into `X`. -/
def constStratumInclusion (C : FiniteRankBundleCore 𝕜 X) (m : ℕ) :
    C({x : X // LocallyConstant.const X C.rank x = m}, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Coordinate core on the `m`-stratum of `LocallyConstant.const X C.rank`: the pullback of `C`
when `C.rank = m`, and the trivial core on the empty stratum otherwise. -/
def constStratumCharts (C : FiniteRankBundleCore 𝕜 X) (m : ℕ) :
    VectorBundleCore 𝕜 {x : X // LocallyConstant.const X C.rank x = m} (Fin m → 𝕜)
      {x : X // LocallyConstant.const X C.rank x = m} :=
  if h : C.rank = m then
    h.rec (motive := fun k _ ↦ VectorBundleCore 𝕜
      {x : X // LocallyConstant.const X C.rank x = m} (Fin k → 𝕜)
      {x : X // LocallyConstant.const X C.rank x = m})
      (C.pullback (constStratumInclusion C m)).core
  else
    (FiniteRankBundleCore.trivial 𝕜 {x : X // LocallyConstant.const X C.rank x = m} m).core

/-- Embed a constant-rank point-indexed core as a variable-rank bundle atlas of constant rank. -/
-- Expose the rank projection so `(ofCore C).Fiber` reduces to `C`'s coordinate fibre.
@[expose, implicit_reducible]
def ofCore (C : FiniteRankBundleCore 𝕜 X) : FiniteRankAtlas 𝕜 X where
  rank := LocallyConstant.const X C.rank
  charts := constStratumCharts C
  indexAt_eq m x := by
    by_cases h : C.rank = m
    · subst h
      have hcharts : constStratumCharts C C.rank =
          (C.pullback (constStratumInclusion C C.rank)).core :=
        dite_eq_left_of_eq_true (eq_true rfl)
      rw [hcharts]
      rfl
    · exact False.elim (h x.2)

@[simp]
theorem rank_ofCore (C : FiniteRankBundleCore 𝕜 X) :
    (ofCore C).rank = LocallyConstant.const X C.rank := (rfl)

theorem rank_ofCore_apply (C : FiniteRankBundleCore 𝕜 X) (x : X) :
    (ofCore C).rank x = C.rank := (rfl)

@[simp]
theorem charts_ofCore_self (C : FiniteRankBundleCore 𝕜 X) :
    (ofCore C).charts C.rank = (C.pullback (constStratumInclusion C C.rank)).core :=
  dite_eq_left_of_eq_true (eq_true rfl)

/-- The reconstructed total space of `ofCore C` is homeomorphic over `X` to `C.core.TotalSpace`. -/
def ofCoreTotalSpaceHomeomorph (C : FiniteRankBundleCore 𝕜 X) :
    TotalSpace Unit (ofCore C).Fiber ≃ₜ C.core.TotalSpace where
  toFun p := ⟨p.proj, p.2⟩
  invFun p := ⟨p.proj, p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  continuous_toFun := by
    rw [← (ofCore C).totalSpaceHomeomorph.comp_continuous_iff']
    refine continuous_sigma fun m ↦ ?_
    by_cases h : C.rank = m
    · subst h
      have hcharts := charts_ofCore_self C
      -- Rewrite along `charts_ofCore_self` so `pullbackHomeomorph` acts directly on the domain.
      have hcont : ∀ (Z : VectorBundleCore 𝕜
          {x : X // (ofCore C).rank x = C.rank} (Fin C.rank → 𝕜)
          {x : X // (ofCore C).rank x = C.rank}),
          Z = (C.pullback (constStratumInclusion C C.rank)).core →
          Continuous (fun q : Z.TotalSpace ↦
            (⟨q.proj.1, q.2⟩ : C.core.TotalSpace)) := by
        rintro _ rfl
        refine ((Pullback.continuous_lift (Fin C.rank → 𝕜) C.core.Fiber
          (constStratumInclusion C C.rank)).comp
          (C.pullbackHomeomorph (constStratumInclusion C C.rank)).continuous).congr ?_
        rintro ⟨⟨x, _⟩, v⟩
        dsimp only [Function.comp_apply]
        rw [FiniteRankBundleCore.pullbackHomeomorph_apply]
        rfl
      exact (hcont _ hcharts).congr fun ⟨⟨x, hx⟩, v⟩ ↦ by
        dsimp only [Function.comp_apply]
        rw [(ofCore C).totalSpaceHomeomorph_apply ⟨C.rank, ⟨⟨x, hx⟩, v⟩⟩]
        have : hx = rfl := Subsingleton.elim _ _
        subst this
        rfl
    · have : Subsingleton (((ofCore C).charts m).TotalSpace) :=
        ⟨fun p _ ↦ False.elim (h p.proj.2)⟩
      have : DiscreteTopology (((ofCore C).charts m).TotalSpace) := Subsingleton.discreteTopology
      exact continuous_of_discreteTopology
  continuous_invFun := by
    refine ((ofCore C).continuous_mk_iff_rankStrata C.core.continuous_proj _).2 fun m ↦ ?_
    by_cases h : C.rank = m
    · subst h
      have hcharts := charts_ofCore_self C
      have hcont : ∀ (Z : VectorBundleCore 𝕜
          {x : X // (ofCore C).rank x = C.rank} (Fin C.rank → 𝕜)
          {x : X // (ofCore C).rank x = C.rank}),
          Z = (C.pullback (constStratumInclusion C C.rank)).core →
          Continuous (fun p : {p : C.core.TotalSpace // (ofCore C).rank p.proj = C.rank} ↦
            (⟨⟨p.1.proj, p.2⟩, p.1.2⟩ : Z.TotalSpace)) := by
        rintro _ rfl
        let toPull : {p : C.core.TotalSpace // (ofCore C).rank p.proj = C.rank} →
            TotalSpace (Fin C.rank → 𝕜)
              ((⇑(constStratumInclusion C C.rank)) *ᵖ C.core.Fiber) :=
          fun p ↦ ⟨⟨p.1.proj, rfl⟩, p.1.2⟩
        have htoPull : Continuous toPull := by
          rw [(inducing_pullbackTotalSpaceEmbedding (Fin C.rank → 𝕜) C.core.Fiber
            (constStratumInclusion C C.rank)).continuous_iff]
          refine Continuous.prodMk ?_ continuous_subtype_val
          exact (C.core.continuous_proj.comp continuous_subtype_val).subtype_mk _
        refine ((C.pullbackHomeomorph (constStratumInclusion C C.rank)).symm.continuous.comp
          htoPull).congr ?_
        rintro ⟨⟨x, v⟩, _⟩
        dsimp only [Function.comp_apply, toPull]
        exact C.pullbackHomeomorph_symm_apply (constStratumInclusion C C.rank) ⟨⟨x, rfl⟩, v⟩
      exact (hcont _ hcharts).congr fun _ ↦ rfl
    · have : Subsingleton {p : C.core.TotalSpace // (ofCore C).rank p.proj = m} :=
        ⟨fun p _ ↦ False.elim (h p.2)⟩
      have : DiscreteTopology {p : C.core.TotalSpace // (ofCore C).rank p.proj = m} :=
        Subsingleton.discreteTopology
      exact continuous_of_discreteTopology

@[simp]
theorem ofCoreTotalSpaceHomeomorph_apply (C : FiniteRankBundleCore 𝕜 X)
    (p : TotalSpace Unit (ofCore C).Fiber) :
    ofCoreTotalSpaceHomeomorph C p = ⟨p.proj, p.2⟩ := (rfl)

@[simp]
theorem ofCoreTotalSpaceHomeomorph_symm_apply (C : FiniteRankBundleCore 𝕜 X)
    (p : C.core.TotalSpace) :
    (ofCoreTotalSpaceHomeomorph C).symm p = ⟨p.proj, p.2⟩ := (rfl)

variable (𝕜 X) in
/-- The additive embedding of constant-rank point-indexed cores into variable-rank bundle
atlases. -/
-- Expose the object map so dependent fibre-map types reduce during simp matching.
@[expose, reducible]
def ofCoreFunctor : FiniteRankBundleCore 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj := ofCore
  map {C₁ C₂} f :=
    { fiberMap := fun x ↦ (f.fiberMap x).toLinearMap
      continuous_totalSpaceMap := by
        refine ((ofCoreTotalSpaceHomeomorph C₂).symm.continuous.comp
          (f.continuous_totalSpaceMap.comp (ofCoreTotalSpaceHomeomorph C₁).continuous)).congr ?_
        rintro ⟨x, v⟩
        dsimp only [Function.comp_apply]
        rw [ofCoreTotalSpaceHomeomorph_apply]
        have hmap : f.totalSpaceMap ⟨x, v⟩ = ⟨x, f.fiberMap x v⟩ := f.totalSpaceMap_mk x v
        rw [hmap, ofCoreTotalSpaceHomeomorph_symm_apply]
        rfl }
  map_id C := by
    apply hom_ext
    intro x
    apply LinearMap.ext
    intro v
    rw [fiberMap_id]
    simp only [FiniteRankBundleCore.fiberMap_id]
    rfl
  map_comp f g := by
    apply hom_ext
    intro x
    apply LinearMap.ext
    intro v
    rw [fiberMap_comp]
    simp only [FiniteRankBundleCore.fiberMap_comp]
    rfl

@[simp]
theorem ofCoreFunctor_obj (C : FiniteRankBundleCore 𝕜 X) :
    (ofCoreFunctor 𝕜 X).obj C = ofCore C := (rfl)

@[simp]
theorem fiberMap_ofCoreFunctor_map {C₁ C₂ : FiniteRankBundleCore 𝕜 X} (f : C₁ ⟶ C₂) (x : X) :
    ((ofCoreFunctor 𝕜 X).map f).fiberMap x = (f.fiberMap x).toLinearMap := (rfl)

instance : (ofCoreFunctor 𝕜 X).Additive where
  map_add {_ _ f g} := by
    apply hom_ext
    intro x
    apply LinearMap.ext
    intro v
    rw [fiberMap_add]
    simp only [FiniteRankBundleCore.fiberMap_add, ContinuousLinearMap.toLinearMap_add]
    rfl

instance : (ofCoreFunctor 𝕜 X).Faithful where
  map_injective {C₁ C₂} f g h := by
    apply FiniteRankBundleCore.hom_ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun k : ofCore C₁ ⟶ ofCore C₂ ↦ k.fiberMap x v) h

private def ofCorePreimageSection [CompleteSpace 𝕜] {C₁ C₂ : FiniteRankBundleCore 𝕜 X}
    (g : ofCore C₁ ⟶ ofCore C₂) (x : X) : (Fin C₁.rank → 𝕜) →L[𝕜] (Fin C₂.rank → 𝕜) :=
  (g.fiberMap x).toContinuousLinearMap

private theorem continuous_ofCorePreimageSection [CompleteSpace 𝕜]
    {C₁ C₂ : FiniteRankBundleCore 𝕜 X} (g : ofCore C₁ ⟶ ofCore C₂) :
    Continuous fun x ↦ TotalSpace.mk' ((Fin C₁.rank → 𝕜) →L[𝕜] (Fin C₂.rank → 𝕜))
      (E := fun y ↦ C₁.core.Fiber y →L[𝕜] C₂.core.Fiber y) x (ofCorePreimageSection g x) :=
  (continuous_hom_bundle_iff (E₁ := C₁.core.Fiber) (E₂ := C₂.core.Fiber)
    (ofCorePreimageSection g)).2 <| by
    refine ((ofCoreTotalSpaceHomeomorph C₂).continuous.comp
      (g.continuous_totalSpaceMap.comp
        (ofCoreTotalSpaceHomeomorph C₁).symm.continuous)).congr ?_
    rintro ⟨x, v⟩
    rfl

/-- Over a complete scalar field, `ofCoreFunctor` is fully faithful. -/
def fullyFaithfulOfCoreFunctor [CompleteSpace 𝕜] : (ofCoreFunctor 𝕜 X).FullyFaithful where
  preimage {C₁ C₂} g :=
    CoordinateHom.ofContinuous (ofCorePreimageSection g) (continuous_ofCorePreimageSection g)
  map_preimage {C₁ C₂} g := by
    apply hom_ext
    intro x
    apply LinearMap.ext
    intro v
    have h := congrFun (CoordinateHom.fiberMap_ofContinuous
      (Z := C₁.core) (W := C₂.core) (ofCorePreimageSection g)
      (continuous_ofCorePreimageSection g)) x
    exact congrArg (fun T : (Fin C₁.rank → 𝕜) →L[𝕜] (Fin C₂.rank → 𝕜) ↦ T v) h
  preimage_map {C₁ C₂} f := by
    apply FiniteRankBundleCore.hom_ext
    intro x
    exact congrFun (CoordinateHom.fiberMap_ofContinuous
      (Z := C₁.core) (W := C₂.core) (ofCorePreimageSection ((ofCoreFunctor 𝕜 X).map f))
      (continuous_ofCorePreimageSection ((ofCoreFunctor 𝕜 X).map f))) x

instance [CompleteSpace 𝕜] : (ofCoreFunctor 𝕜 X).Full :=
  (fullyFaithfulOfCoreFunctor (𝕜 := 𝕜) (X := X)).full

/-- A variable-rank bundle atlas lies in the essential image of `ofCoreFunctor` if and only if its
locally constant rank function is globally constant. -/
theorem mem_essImage_ofCoreFunctor_iff (A : FiniteRankAtlas 𝕜 X) :
    (ofCoreFunctor 𝕜 X).essImage A ↔ ∃ n : ℕ, A.rank = LocallyConstant.const X n := by
  constructor
  · rintro ⟨C, ⟨e⟩⟩
    exact ⟨C.rank, e.symm.finiteRankAtlas_rank_eq.trans (rank_ofCore C)⟩
  · rintro ⟨n, hn⟩
    have hnx : ∀ x : X, A.rank x = n := fun x ↦ by
      rw [hn]
      rfl
    let inc : C(X, {x : X // A.rank x = n}) :=
      ⟨fun x ↦ ⟨x, hnx x⟩, continuous_id.subtype_mk _⟩
    let C : FiniteRankBundleCore 𝕜 X := (A.stratumCore n).pullback inc
    refine ⟨C, ⟨?_⟩⟩
    have hrank : ∀ x : X, (ofCore C).rank x = A.rank x := fun x ↦ (hnx x).symm
    let eFib : ∀ x : X, (ofCore C).Fiber x ≃ₗ[𝕜] A.Fiber x := fun x ↦
      LinearEquiv.funCongrLeft 𝕜 𝕜 (finCongr (hrank x).symm)
    refine isoMk eFib ?_ ?_
    · refine ((A.continuous_mk_iff_rankStrata (ofCore C).continuous_proj _).2 fun m ↦ ?_)
      by_cases hm : n = m
      · subst hm
        let toC : {p : TotalSpace Unit (ofCore C).Fiber // A.rank p.proj = n} →
            C.core.TotalSpace :=
          fun p ↦ ofCoreTotalSpaceHomeomorph C p.1
        have htoC : Continuous toC :=
          (ofCoreTotalSpaceHomeomorph C).continuous.comp continuous_subtype_val
        have htoA : Continuous (fun p : C.core.TotalSpace ↦
            Pullback.lift inc ((A.stratumCore n).pullbackHomeomorph inc p)) :=
          (Pullback.continuous_lift (Fin n → 𝕜) (A.charts n).Fiber inc).comp
            ((A.stratumCore n).pullbackHomeomorph inc).continuous
        refine (htoA.comp htoC).congr ?_
        rintro ⟨⟨x, v⟩, hx⟩
        dsimp only [Function.comp_apply, toC]
        rw [ofCoreTotalSpaceHomeomorph_apply, FiniteRankBundleCore.pullbackHomeomorph_apply]
        simp only [Pullback.lift]
        ext
        · rfl
        · refine heq_of_eq (funext fun i ↦ congrArg v ?_)
          exact Fin.ext rfl
      · have : Subsingleton {p : TotalSpace Unit (ofCore C).Fiber // A.rank p.proj = m} :=
          ⟨fun p _ ↦ False.elim (hm ((hnx p.1.proj).symm.trans p.2))⟩
        have : DiscreteTopology {p : TotalSpace Unit (ofCore C).Fiber // A.rank p.proj = m} :=
          Subsingleton.discreteTopology
        exact continuous_of_discreteTopology
    · have htoPull : Continuous (fun p : TotalSpace Unit A.Fiber ↦
          (⟨p.proj, fun i ↦ p.2 (Fin.cast (hnx p.proj).symm i)⟩ :
            TotalSpace (Fin n → 𝕜) ((⇑inc) *ᵖ (A.charts n).Fiber))) := by
        rw [(inducing_pullbackTotalSpaceEmbedding (Fin n → 𝕜) (A.charts n).Fiber
          inc).continuous_iff]
        refine A.continuous_proj.prodMk ?_
        have hstr := (A.continuous_mk_iff_rankStrata A.continuous_proj (fun p ↦ p.2)).1
          continuous_id n
        refine (hstr.comp (Continuous.subtype_mk continuous_id fun p : TotalSpace Unit A.Fiber ↦
          hnx p.proj)).congr ?_
        rintro ⟨x, v⟩
        rfl
      refine ((ofCoreTotalSpaceHomeomorph C).symm.continuous.comp
        (((A.stratumCore n).pullbackHomeomorph inc).symm.continuous.comp htoPull)).congr ?_
      rintro ⟨x, v⟩
      dsimp only [Function.comp_apply]
      rw [FiniteRankBundleCore.pullbackHomeomorph_symm_apply, ofCoreTotalSpaceHomeomorph_symm_apply]
      ext
      · rfl
      · refine heq_of_eq (funext fun i ↦ congrArg v ?_)
        exact Fin.ext rfl

end FixedRank

end TauCeti.FiniteRankAtlas
