/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback

/-!
# Chart-operator encoding and isomorphism criterion for bundle atlases

Between `A, D : FiniteRankAtlas 𝕜 X`, the base decomposes into clopen pairwise-rank strata
`RankPairStratum A D m n = {x : X // A.rank x = m ∧ D.rank x = n}` carrying pulled-back
constant-rank cores `sourcePairCore` and `targetPairCore`. Compatible chart-operator families
assemble into morphisms `A ⟶ D` (`ofCoordinateHom`) without completeness on `𝕜`. Over a complete
field, `toCoordinateHom` provides a two-sided inverse (`ofCoordinateHom_toCoordinateHom`,
`toCoordinateHom_ofCoordinateHom`, packaged as `coordinateHomAddEquiv`), `toCoordinateHom_id`
computes the image of `𝟙 A` on each diagonal stratum, and `isIso_iff_bijective` characterizes
isomorphisms by fibrewise bijectivity.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section
open Bundle CategoryTheory Topology VectorBundleCore TauCeti.VariableRankBundle
namespace TauCeti.FiniteRankAtlas
universe u v
variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

section Stratum
variable (A : FiniteRankAtlas 𝕜 X) (n : ℕ)

variable {Y : Type*} [TopologicalSpace Y] (g : C(Y, {x : X // A.rank x = n}))
private def pullbackCoreToTotalSpace :
    C(((A.stratumCore n).pullback g).core.TotalSpace, TotalSpace Unit A.Fiber) where
  toFun p := ⟨(g p.proj).val, fun i ↦ p.snd (Fin.cast (g p.proj).property i)⟩
  continuous_toFun := ((totalSpaceHomeomorph A).continuous.comp
    (continuous_sigmaMk.comp ((A.stratumCore n).continuous_pullbackLift g))).congr fun ⟨_, _⟩ ↦ by
      dsimp only [Function.comp_apply]
      rw [FiniteRankBundleCore.pullbackLift_mk, totalSpaceHomeomorph_apply]
@[simp] private theorem pullbackCoreToTotalSpace_apply
    (p : ((A.stratumCore n).pullback g).core.TotalSpace) : pullbackCoreToTotalSpace A n g p =
      ⟨(g p.proj).val, fun i ↦ p.snd (Fin.cast (g p.proj).property i)⟩ := by rfl
end Stratum

section Pairwise
variable (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ)
/-- The clopen stratum on which `A` has rank `m` and `D` has rank `n`. -/
abbrev RankPairStratum : Type u := {x : X // A.rank x = m ∧ D.rank x = n}
/-- Inclusion of the `(m, n)` pairwise stratum into the `m`th stratum of `A`. -/
-- Expose the subtype projection so `rankPairFst A A n n` and `rankPairSnd A A n n` coincide.
@[expose] def rankPairFst : C(RankPairStratum A D m n, {x : X // A.rank x = m}) :=
  ⟨fun x ↦ ⟨x.val, x.property.1⟩, continuous_subtypeVal.subtype_mk fun x ↦ x.property.1⟩
/-- Inclusion of the `(m, n)` pairwise stratum into the `n`th stratum of `D`. -/
-- Expose the subtype projection so `rankPairFst A A n n` and `rankPairSnd A A n n` coincide.
@[expose] def rankPairSnd : C(RankPairStratum A D m n, {x : X // D.rank x = n}) :=
  ⟨fun x ↦ ⟨x.val, x.property.2⟩, continuous_subtypeVal.subtype_mk fun x ↦ x.property.2⟩
/-- The source core restricted to the `(m, n)` pairwise stratum. -/
-- Expose the rank projection so dependent coordinate fibres reduce to `Fin m → 𝕜`.
@[expose, implicit_reducible]
def sourcePairCore : FiniteRankBundleCore 𝕜 (RankPairStratum A D m n) :=
  (A.stratumCore m).pullback (rankPairFst A D m n)
/-- The target core restricted to the `(m, n)` pairwise stratum. -/
-- Expose the rank projection so dependent coordinate fibres reduce to `Fin n → 𝕜`.
@[expose, implicit_reducible]
def targetPairCore : FiniteRankBundleCore 𝕜 (RankPairStratum A D m n) :=
  (D.stratumCore n).pullback (rankPairSnd A D m n)
@[simp] theorem rank_sourcePairCore : (sourcePairCore A D m n).rank = m := by rfl
@[simp] theorem rank_targetPairCore : (targetPairCore A D m n).rank = n := by rfl
end Pairwise

section Assemble
variable {A D : FiniteRankAtlas 𝕜 X}
/-- Glue compatible chart-operator morphisms on all pairwise rank strata into a morphism of
variable-rank bundle atlases. -/
def ofCoordinateHom (c : ∀ m n : ℕ, sourcePairCore A D m n ⟶ targetPairCore A D m n) : A ⟶ D where
  fiberMap x := ((c (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩).toLinearMap
  continuous_totalSpaceMap := by
    rw [← (totalSpaceHomeomorph A).comp_continuous_iff']
    refine continuous_sigma fun m ↦ continuous_of_cover_nhds
      (s := fun n : ℕ ↦ {q : (A.charts m).TotalSpace | D.rank q.proj.val = n})
      (fun q ↦ ⟨D.rank q.proj.val, ((D.rank.isLocallyConstant.isOpen_fiber _).preimage
        (continuous_subtypeVal.comp (A.charts m).continuous_proj)).mem_nhds rfl⟩) fun n ↦ ?_
    rw [continuousOn_iff_continuous_domRestrict]
    let srcMap : {q : (A.charts m).TotalSpace // D.rank q.proj.val = n} →
        (sourcePairCore A D m n).core.TotalSpace :=
      fun q ↦ ⟨⟨q.val.proj.val, q.val.proj.property, q.property⟩, q.val.snd⟩
    have hsrc : Continuous srcMap :=
      ((A.stratumCore m).continuous_core_pullback_iff (rankPairFst A D m n)).2
        ⟨(continuous_subtypeVal.comp ((A.charts m).continuous_proj.comp
          continuous_subtypeVal)).subtype_mk _,
          continuous_subtypeVal.congr fun ⟨⟨⟨x, hm⟩, v⟩, hn⟩ ↦
            ((A.stratumCore m).pullbackLift_mk (rankPairFst A D m n) ⟨x, hm, hn⟩ v).symm⟩
    let tgtMap := pullbackCoreToTotalSpace D n (rankPairSnd A D m n)
    refine (tgtMap.continuous.comp ((c m n).continuous_totalSpaceMap.comp hsrc)).congr ?_
    rintro ⟨⟨⟨x, hm⟩, v⟩, hn⟩
    dsimp only [Set.domRestrict_apply, Function.comp_apply, srcMap, tgtMap] at hm hn ⊢
    subst hm; subst hn
    have hA : totalSpaceHomeomorph A ⟨A.rank x, ⟨⟨x, rfl⟩, v⟩⟩ = ⟨x, v⟩ := by
      rw [totalSpaceHomeomorph_apply]; rfl
    rw [hA, (c (A.rank x) (D.rank x)).totalSpaceMap_mk ⟨x, rfl, rfl⟩ v,
      pullbackCoreToTotalSpace_apply]; rfl
@[simp] theorem fiberMap_ofCoordinateHom
    (c : ∀ m n : ℕ, sourcePairCore A D m n ⟶ targetPairCore A D m n) (x : X) :
    (ofCoordinateHom c).fiberMap x =
      ((c (A.rank x) (D.rank x)).fiberMap ⟨x, rfl, rfl⟩).toLinearMap := by rfl
end Assemble

section Extract
variable [CompleteSpace 𝕜] {A D : FiniteRankAtlas 𝕜 X}

private def pairwiseFiberSection (f : A ⟶ D) (m n : ℕ) (z : RankPairStratum A D m n) :
    (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜) :=
  (LinearEquiv.funCongrLeft 𝕜 𝕜
      (finCongr z.property.2.symm)).toContinuousLinearEquiv.toContinuousLinearMap
    ∘L (f.fiberMap z.val).toContinuousLinearMap
    ∘L (LinearEquiv.funCongrLeft 𝕜 𝕜
      (finCongr z.property.1)).toContinuousLinearEquiv.toContinuousLinearMap
private theorem continuous_pairwiseFiberSection (f : A ⟶ D) (m n : ℕ) :
    Continuous fun z ↦ TotalSpace.mk' ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜))
      (E := fun y ↦ (sourcePairCore A D m n).core.Fiber y →L[𝕜]
        (targetPairCore A D m n).core.Fiber y) z (pairwiseFiberSection f m n z) := by
  let sC := (sourcePairCore A D m n).core
  refine (continuous_hom_bundle_iff (E₁ := sC.Fiber) (E₂ := (targetPairCore A D m n).core.Fiber)
    (pairwiseFiberSection f m n)).2 ?_
  have hcomp : Continuous (fun p : sC.TotalSpace ↦
      (⟨p.proj.val, f.fiberMap p.proj.val (fun i ↦ p.snd (Fin.cast p.proj.property.1 i))⟩ :
        TotalSpace Unit D.Fiber)) := (f.continuous_totalSpaceMap.comp
    (pullbackCoreToTotalSpace A m (rankPairFst A D m n)).continuous).congr fun _ ↦ rfl
  have hstratum := ((continuous_mk_iff_rankStrata D (continuous_subtypeVal.comp sC.continuous_proj)
    _).1 hcomp n).comp
      (Continuous.subtype_mk continuous_id fun p : sC.TotalSpace ↦ p.proj.property.2)
  exact ((D.stratumCore n).continuous_core_pullback_iff (rankPairSnd A D m n)).2
    ⟨sC.continuous_proj, hstratum.congr fun ⟨⟨_, _, _⟩, _⟩ ↦
      ((D.stratumCore n).pullbackLift_mk (rankPairSnd A D m n) _ _).symm⟩

/-- Restrict a bundle-atlas morphism to a chart-operator morphism on the `(m, n)` pairwise
stratum. -/
def toCoordinateHom (f : A ⟶ D) (m n : ℕ) : sourcePairCore A D m n ⟶ targetPairCore A D m n :=
  CoordinateHom.ofContinuous (pairwiseFiberSection f m n) (continuous_pairwiseFiberSection f m n)
@[simp] theorem fiberMap_toCoordinateHom_apply (f : A ⟶ D) (m n : ℕ) (z : RankPairStratum A D m n)
    (v : Fin m → 𝕜) (j : Fin n) : (toCoordinateHom f m n).fiberMap z v j =
      f.fiberMap z.val (fun i ↦ v (Fin.cast z.property.1 i)) (Fin.cast z.property.2.symm j) :=
  congrFun (congrArg (fun T : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜) ↦ T v) (congrFun
    (CoordinateHom.fiberMap_ofContinuous (Z := (sourcePairCore A D m n).core)
      (W := (targetPairCore A D m n).core) _ (continuous_pairwiseFiberSection f m n)) z)) j
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
@[simp] theorem coordinateHomAddEquiv_apply (A D : FiniteRankAtlas 𝕜 X) (f : A ⟶ D) :
    coordinateHomAddEquiv A D f = toCoordinateHom f := by rfl
@[simp] theorem coordinateHomAddEquiv_symm_apply (A D : FiniteRankAtlas 𝕜 X)
    (c : ∀ m n : ℕ, sourcePairCore A D m n ⟶ targetPairCore A D m n) :
    (coordinateHomAddEquiv A D).symm c = ofCoordinateHom c := by rfl

@[simp] theorem toCoordinateHom_id (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    toCoordinateHom (𝟙 A) n n =
      (A.stratumCore n).pullbackMap (𝟙 (A.stratumCore n)) (rankPairFst A A n n) := by
  apply FiniteRankBundleCore.hom_ext; rintro ⟨x, rfl, h₂⟩; cases Subsingleton.elim h₂ rfl
  rw [fiberMap_toCoordinateHom_self, fiberMap_id]; ext v j
  rw [LinearMap.coe_toContinuousLinearMap', LinearMap.id_apply]
  exact (congrArg (fun T : (Fin (A.rank x) → 𝕜) →L[𝕜] (Fin (A.rank x) → 𝕜) ↦ T v j)
    ((FiniteRankBundleCore.fiberMap_pullbackMap (𝟙 (A.stratumCore (A.rank x)))
      (rankPairFst A A (A.rank x) (A.rank x)) ⟨x, rfl, rfl⟩).trans
      (FiniteRankBundleCore.fiberMap_id _ _))).symm

private def rankPairSwap (A D : FiniteRankAtlas 𝕜 X) (m n : ℕ) :
    C(RankPairStratum D A n m, RankPairStratum A D m n) :=
  ⟨fun z ↦ ⟨z.val, z.property.2, z.property.1⟩,
    continuous_subtypeVal.subtype_mk fun z ↦ ⟨z.property.2, z.property.1⟩⟩
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
  let m := A.rank x; let n := D.rank x
  have := isIso_toCoordinateHom_of_bijective hf m n
  let e := LinearEquiv.ofBijective (f.fiberMap x) (hf x)
  refine LinearMap.ext fun w ↦ e.injective ?_
  have hid := congrArg (fun k : targetPairCore A D m n ⟶ targetPairCore A D m n ↦
      k.fiberMap ⟨x, rfl, rfl⟩ w) (IsIso.inv_hom_id (toCoordinateHom f m n))
  have hpb := congrArg (fun T : (Fin n → 𝕜) →L[𝕜] _ ↦ f.fiberMap x (T w))
    (FiniteRankBundleCore.fiberMap_pullbackMap (inv (toCoordinateHom f m n))
      (rankPairSwap A D m n) ⟨x, rfl, rfl⟩)
  simp only [m, n, FiniteRankBundleCore.fiberMap_comp, FiniteRankBundleCore.fiberMap_id,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    fiberMap_toCoordinateHom_self, LinearMap.coe_toContinuousLinearMap'] at hid
  simp only [e, LinearEquiv.ofBijective_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    fiberMap_ofCoordinateHom, invCoordFamily, ContinuousLinearMap.coe_coe]
  exact hpb.trans hid

/-- A morphism of variable-rank bundle atlases is an isomorphism if and only if it is bijective on
every fibre. -/
theorem isIso_iff_bijective (f : A ⟶ D) : IsIso f ↔ ∀ x : X, Function.Bijective (f.fiberMap x) := by
  refine ⟨fun _ x ↦
    ((VariableRankBundle.fiberFunctor (FiniteRankAtlas 𝕜 X) x).mapIso
      (asIso f)).toLinearEquiv.bijective,
    fun hf ↦ ⟨⟨ofCoordinateHom (invCoordFamily f hf), ?_, ?_⟩⟩⟩ <;>
  · refine hom_ext fun x ↦ LinearMap.ext fun v ↦ ?_
    rw [fiberMap_comp, fiberMap_id, LinearMap.comp_apply, LinearMap.id_apply,
      fiberMap_ofCoordinateHom_invCoordFamily f hf x]
    first | exact (LinearEquiv.ofBijective (f.fiberMap x) (hf x)).symm_apply_apply v
          | exact (LinearEquiv.ofBijective (f.fiberMap x) (hf x)).apply_symm_apply v
end Extract
end TauCeti.FiniteRankAtlas
