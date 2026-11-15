/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Pi

/-!
# Gluing point-indexed finite-rank cores over locally constant partitions

Given a locally constant map `c : LocallyConstant B α` and a family of point-indexed cores
`C a : FiniteRankBundleCore 𝕜 {b : B // c b = a}` whose ranks all equal `n`,
`FiniteRankBundleCore.ofLocallyConstant` assembles them into a single point-indexed core of rank
`n` over `B`. Each chart at `i : B` is taken inside the clopen fibre `{b : B | c b = c i}`, so
charts from distinct fibres never meet and transitions reduce to those of `C (c i)`.

First, `castRank` reindexes the coordinate model `Fin A.rank → 𝕜` along a rank equality
`A.rank = n`, and `castRankIso` records its categorical isomorphism with `A` via `constIso`.

Pulling `ofLocallyConstant` back along the open inclusion of `{b : B // c b = a}` recovers `C a` up
to `ofLocallyConstantPullbackIso`. Passing to total spaces yields the homeomorphism
`ofLocallyConstantTotalSpaceHomeomorph` from the disjoint union `Σ a : α, (C a).core.TotalSpace` to
`(ofLocallyConstant n c C hrank).core.TotalSpace`, open stratum embeddings, and a stratumwise
continuity criterion for maps into the glued total space. This provides the clopen sub-stratum
gluing needed when a bundle operation on variable-rank atlases combines multiple summand or factor
ranks into a single output rank.

The construction builds on `TauCeti.FiniteRankBundleCore`, `FiniteRankBundleCore.constIso`, and
`FiniteRankBundleCore.pullbackHomeomorph`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* M. F. Atiyah, *K-Theory*, §1.1–1.2.
-/

public section

open Bundle CategoryTheory Set Topology VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

section CastRank

/-- Reindex finite coordinate vectors along an equality of dimensions. -/
def castRankEquiv {m n : ℕ} (h : m = n) : (Fin m → 𝕜) ≃L[𝕜] (Fin n → 𝕜) :=
  (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin m => 𝕜) (finCongr h.symm)).symm

@[simp]
theorem castRankEquiv_apply {m n : ℕ} (h : m = n) (v : Fin m → 𝕜) (i : Fin n) :
    castRankEquiv (𝕜 := 𝕜) h v i = v (Fin.cast h.symm i) := (rfl)

@[simp]
theorem castRankEquiv_symm_apply {m n : ℕ} (h : m = n) (w : Fin n → 𝕜) (j : Fin m) :
    (castRankEquiv (𝕜 := 𝕜) h).symm w j = w (Fin.cast h j) := by
  cases h
  rfl

@[simp]
theorem castRankEquiv_rfl (n : ℕ) :
    castRankEquiv (𝕜 := 𝕜) (rfl : n = n) = ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜) := by
  ext v i
  rfl

/-- Transport a point-indexed finite-rank core along an equality `A.rank = n`, conjugating its
coordinate transitions by `castRankEquiv`. -/
-- Reduce the rank also during implicit-argument matching of coordinate-map simp lemmas.
@[expose, implicit_reducible]
def castRank (A : FiniteRankBundleCore 𝕜 B) {n : ℕ} (h : A.rank = n) :
    FiniteRankBundleCore 𝕜 B where
  rank := n
  core :=
    { baseSet := A.core.baseSet
      isOpen_baseSet := A.core.isOpen_baseSet
      indexAt := id
      mem_baseSet_at := fun x => by
        simpa only [id_eq, A.indexAt_eq] using A.core.mem_baseSet_at x
      coordChange := fun i j x =>
        (castRankEquiv (𝕜 := 𝕜) h).toContinuousLinearMap.comp
          ((A.core.coordChange i j x).comp
            (castRankEquiv (𝕜 := 𝕜) h).symm.toContinuousLinearMap)
      coordChange_self := fun i x hx v => by
        ext k
        simp [A.core.coordChange_self i x hx]
      continuousOn_coordChange := fun i j =>
        continuousOn_iff_continuous_domRestrict.2
          ((((A.core.continuousOn_coordChange i j).domRestrict).clm_comp_const
            (castRankEquiv (𝕜 := 𝕜) h).symm.toContinuousLinearMap).const_clm_comp
              (castRankEquiv (𝕜 := 𝕜) h).toContinuousLinearMap)
      coordChange_comp := fun i j k x hx v => by
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.symm_apply_apply]
        rw [A.core.coordChange_comp i j k x hx] }
  indexAt_eq := fun _ => rfl

@[simp]
theorem rank_castRank (A : FiniteRankBundleCore 𝕜 B) {n : ℕ} (h : A.rank = n) :
    (A.castRank h).rank = n := (rfl)

theorem baseSet_castRank (A : FiniteRankBundleCore 𝕜 B) {n : ℕ} (h : A.rank = n) (i : B) :
    (A.castRank h).core.baseSet i = A.core.baseSet i := (rfl)

@[simp]
theorem localTriv_baseSet_castRank (A : FiniteRankBundleCore 𝕜 B) {n : ℕ} (h : A.rank = n)
    (i : B) :
    ((A.castRank h).core.localTriv i).baseSet = (A.core.localTriv i).baseSet := (rfl)

@[simp]
theorem coordChange_castRank (A : FiniteRankBundleCore 𝕜 B) {n : ℕ} (h : A.rank = n)
    (i j x : B) :
    (A.castRank h).core.coordChange i j x =
      (castRankEquiv (𝕜 := 𝕜) h).toContinuousLinearMap.comp
        ((A.core.coordChange i j x).comp
          (castRankEquiv (𝕜 := 𝕜) h).symm.toContinuousLinearMap) := (rfl)

@[simp]
theorem castRank_rfl (A : FiniteRankBundleCore 𝕜 B) : A.castRank rfl = A := by
  induction A using induction_on
  simp only [castRank, castRankEquiv_rfl, ContinuousLinearEquiv.refl_symm,
    ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

/-- Reindexing the coordinate model along `h : A.rank = n` yields an isomorphic core, with
`castRankEquiv h` on every fibre. -/
def castRankIso (A : FiniteRankBundleCore 𝕜 B) {n : ℕ} (h : A.rank = n) :
    A ≅ A.castRank h :=
  constIso (fun _ => rfl) (castRankEquiv (𝕜 := 𝕜) h) fun i j x _ _ => by
    rw [coordChange_castRank]
    ext v k
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]

@[simp]
theorem fiberMap_castRankIso_hom (A : FiniteRankBundleCore 𝕜 B) {n : ℕ} (h : A.rank = n) (x : B) :
    (castRankIso A h).hom.fiberMap x = (castRankEquiv (𝕜 := 𝕜) h).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

@[simp]
theorem fiberMap_castRankIso_inv (A : FiniteRankBundleCore 𝕜 B) {n : ℕ} (h : A.rank = n) (x : B) :
    (castRankIso A h).inv.fiberMap x = (castRankEquiv (𝕜 := 𝕜) h).symm.toContinuousLinearMap :=
  fiberMap_constIso_inv _ _ _ x

end CastRank

section OfLocallyConstant

variable {α : Type*} (n : ℕ) (c : LocallyConstant B α)
  (C : ∀ a : α, FiniteRankBundleCore 𝕜 {b : B // c b = a})
  (hrank : ∀ a : α, (C a).rank = n)

private theorem mem_stratum_baseSet_iff_of_eq {a a' : α} (haa' : a = a')
    {i x : B} (hi : c i = a) (hx : c x = a) (hi' : c i = a') (hx' : c x = a') :
    (⟨x, hx⟩ : {b : B // c b = a}) ∈ (C a).core.baseSet ⟨i, hi⟩ ↔
      (⟨x, hx'⟩ : {b : B // c b = a'}) ∈ (C a').core.baseSet ⟨i, hi'⟩ := by
  cases haa'
  rfl

private theorem castRank_coordChange_eq_of_eq {a a' : α} (haa' : a = a')
    {i j x : B} (hi : c i = a) (hj : c j = a) (hx : c x = a)
    (hi' : c i = a') (hj' : c j = a') (hx' : c x = a') :
    ((C a).castRank (hrank a)).core.coordChange ⟨i, hi⟩ ⟨j, hj⟩ ⟨x, hx⟩ =
      ((C a').castRank (hrank a')).core.coordChange ⟨i, hi'⟩ ⟨j, hj'⟩ ⟨x, hx'⟩ := by
  cases haa'
  rfl

/-- The canonical continuous inclusion of the `a`-fibre of `c` into the base `B`. -/
abbrev stratumInclusion (a : α) : C({b : B // c b = a}, B) :=
  ⟨Subtype.val, continuous_subtype_val⟩

variable [DecidableEq α]

/-- Assemble point-indexed cores of common rank `n` on the clopen fibres of a locally constant
function `c : LocallyConstant B α` into a single point-indexed core over `B`. -/
-- Reduce the rank also during implicit-argument matching of coordinate-map simp lemmas.
@[expose, implicit_reducible]
def ofLocallyConstant : FiniteRankBundleCore 𝕜 B where
  rank := n
  core :=
    { baseSet := fun i =>
        {x : B | ∃ hx : c x = c i,
          (⟨x, hx⟩ : {b : B // c b = c i}) ∈ (C (c i)).core.baseSet ⟨i, rfl⟩}
      isOpen_baseSet := fun i => by
        have himg : {x : B | ∃ hx : c x = c i,
            (⟨x, hx⟩ : {b : B // c b = c i}) ∈ (C (c i)).core.baseSet ⟨i, rfl⟩} =
            Subtype.val '' ((C (c i)).core.baseSet ⟨i, rfl⟩) := by
          ext x
          exact ⟨fun ⟨hx, hmem⟩ => ⟨⟨x, hx⟩, hmem, rfl⟩,
            fun ⟨⟨y, hy⟩, hmem, hyx⟩ => hyx ▸ ⟨hy, hmem⟩⟩
        rw [himg]
        exact (c.isLocallyConstant.isOpen_fiber (c i)).isOpenEmbedding_subtypeVal.isOpenMap _
          ((C (c i)).core.isOpen_baseSet ⟨i, rfl⟩)
      indexAt := id
      mem_baseSet_at := fun x => ⟨rfl, (C (c x)).mem_baseSet_self ⟨x, rfl⟩⟩
      coordChange := fun i j x =>
        if h : c i = c j ∧ c x = c i then
          ((C (c i)).castRank (hrank (c i))).core.coordChange ⟨i, rfl⟩ ⟨j, h.1.symm⟩ ⟨x, h.2⟩
        else
          ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)
      coordChange_self := fun i x hx v => by
        rw [dite_eq_left ⟨rfl, hx.1⟩]
        exact ((C (c i)).castRank (hrank (c i))).core.coordChange_self ⟨i, rfl⟩ ⟨x, hx.1⟩ hx.2 v
      continuousOn_coordChange := fun i j => by
        by_cases hij : c i = c j
        · rw [continuousOn_iff_continuous_domRestrict]
          let S := ((C (c i)).castRank (hrank (c i))).core.baseSet ⟨i, rfl⟩ ∩
            ((C (c i)).castRank (hrank (c i))).core.baseSet ⟨j, hij.symm⟩
          let g : ↥({x : B | ∃ hx : c x = c i,
                (⟨x, hx⟩ : {b : B // c b = c i}) ∈ (C (c i)).core.baseSet ⟨i, rfl⟩} ∩
              {x : B | ∃ hx : c x = c j,
                (⟨x, hx⟩ : {b : B // c b = c j}) ∈ (C (c j)).core.baseSet ⟨j, rfl⟩}) → S :=
            fun x => ⟨⟨x.1, x.2.1.1⟩, x.2.1.2,
              (mem_stratum_baseSet_iff_of_eq c C hij.symm rfl x.2.2.1 hij.symm x.2.1.1).1 x.2.2.2⟩
          have hg : Continuous g :=
            (continuous_subtype_val.subtype_mk _).subtype_mk _
          refine ((((C (c i)).castRank (hrank (c i))).core.continuousOn_coordChange
            ⟨i, rfl⟩ ⟨j, hij.symm⟩).domRestrict.comp hg).congr fun x => ?_
          dsimp only [Set.domRestrict_apply, Function.comp_apply, g]
          rw [dite_eq_left ⟨hij, x.2.1.1⟩]
        · have hempty : {x : B | ∃ hx : c x = c i,
                (⟨x, hx⟩ : {b : B // c b = c i}) ∈ (C (c i)).core.baseSet ⟨i, rfl⟩} ∩
              {x : B | ∃ hx : c x = c j,
                (⟨x, hx⟩ : {b : B // c b = c j}) ∈ (C (c j)).core.baseSet ⟨j, rfl⟩} = ∅ :=
            eq_empty_iff_forall_notMem.2 fun x hx => hij (hx.1.1.symm.trans hx.2.1)
          rw [hempty]
          exact continuousOn_empty _
      coordChange_comp := fun i j k x hx v => by
        rcases hx with ⟨⟨⟨hxi, hmem_i⟩, ⟨hxj, hmem_j⟩⟩, ⟨hxk, hmem_k⟩⟩
        have hij : c i = c j := hxi.symm.trans hxj
        have hjk : c j = c k := hxj.symm.trans hxk
        have hik : c i = c k := hxi.symm.trans hxk
        rw [dite_eq_left ⟨hjk, hxj⟩, dite_eq_left ⟨hij, hxi⟩, dite_eq_left ⟨hik, hxi⟩,
          castRank_coordChange_eq_of_eq n c C hrank hij.symm rfl hjk.symm hxj hij.symm hik.symm hxi]
        have hmem_j' : (⟨x, hxi⟩ : {b : B // c b = c i}) ∈
            ((C (c i)).castRank (hrank (c i))).core.baseSet ⟨j, hij.symm⟩ :=
          (mem_stratum_baseSet_iff_of_eq c C hij.symm rfl hxj hij.symm hxi).1 hmem_j
        have hmem_k' : (⟨x, hxi⟩ : {b : B // c b = c i}) ∈
            ((C (c i)).castRank (hrank (c i))).core.baseSet ⟨k, hik.symm⟩ :=
          (mem_stratum_baseSet_iff_of_eq c C hik.symm rfl hxk hik.symm hxi).1 hmem_k
        exact ((C (c i)).castRank (hrank (c i))).core.coordChange_comp
          ⟨i, rfl⟩ ⟨j, hij.symm⟩ ⟨k, hik.symm⟩ ⟨x, hxi⟩ ⟨⟨hmem_i, hmem_j'⟩, hmem_k'⟩ v }
  indexAt_eq := fun _ => rfl

@[simp]
theorem rank_ofLocallyConstant : (ofLocallyConstant n c C hrank).rank = n := (rfl)

/-- Pulling `ofLocallyConstant n c C hrank` back to the clopen fibre `{b : B // c b = a}` recovers
`C a` up to the coordinate reindexing `(castRankEquiv (hrank a)).symm`. -/
def ofLocallyConstantPullbackIso (a : α) :
    (ofLocallyConstant n c C hrank).pullback (stratumInclusion c a) ≅ C a :=
  (constIso (D := (C a).castRank (hrank a))
    (fun i => by
      ext x
      exact ⟨fun ⟨_, hmem⟩ =>
          (mem_stratum_baseSet_iff_of_eq c C i.2 rfl _ i.2 x.2).1 hmem,
        fun hmem => ⟨x.2.trans i.2.symm,
          (mem_stratum_baseSet_iff_of_eq c C i.2 rfl (x.2.trans i.2.symm) i.2 x.2).2 hmem⟩⟩)
    (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (fun i j x _ _ => by
      have hij : c i.1 = c j.1 := i.2.trans j.2.symm
      have hxi : c x.1 = c i.1 := x.2.trans i.2.symm
      ext v k
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        coordChange_pullback, ContinuousMap.coe_mk, ofLocallyConstant]
      rw [dite_eq_left ⟨hij, hxi⟩,
        castRank_coordChange_eq_of_eq n c C hrank i.2 rfl hij.symm hxi i.2 j.2 x.2]
      rfl)).trans
    (castRankIso (C a) (hrank a)).symm

@[simp]
theorem fiberMap_ofLocallyConstantPullbackIso_hom (a : α) (x : {b : B // c b = a}) :
    (ofLocallyConstantPullbackIso n c C hrank a).hom.fiberMap x =
      (castRankEquiv (𝕜 := 𝕜) (hrank a)).symm.toContinuousLinearMap := by
  ext v k
  simp only [ofLocallyConstantPullbackIso, Iso.trans_hom, Iso.symm_hom, fiberMap_comp,
    fiberMap_constIso_hom, fiberMap_castRankIso_inv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, castRankEquiv_symm_apply]
  rfl

@[simp]
theorem fiberMap_ofLocallyConstantPullbackIso_inv (a : α) (x : {b : B // c b = a}) :
    (ofLocallyConstantPullbackIso n c C hrank a).inv.fiberMap x =
      (castRankEquiv (𝕜 := 𝕜) (hrank a)).toContinuousLinearMap := by
  ext v k
  simp only [ofLocallyConstantPullbackIso, Iso.trans_inv, Iso.symm_inv, fiberMap_comp,
    fiberMap_constIso_inv, fiberMap_castRankIso_hom, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, castRankEquiv_apply]
  rfl

private def ofLocallyConstantTotalEquiv :
    (Σ a : α, (C a).core.TotalSpace) ≃ (ofLocallyConstant n c C hrank).core.TotalSpace where
  toFun p := ⟨p.2.proj.1, castRankEquiv (𝕜 := 𝕜) (hrank p.1) p.2.2⟩
  invFun q := ⟨c q.proj, ⟨⟨q.proj, rfl⟩, (castRankEquiv (𝕜 := 𝕜) (hrank (c q.proj))).symm q.2⟩⟩
  left_inv := by
    rintro ⟨a, ⟨⟨b, hb⟩, v⟩⟩
    cases hb
    exact congrArg (Sigma.mk (c b))
      (congrArg (TotalSpace.mk' _ _) ((castRankEquiv (hrank (c b))).symm_apply_apply v))
  right_inv := by
    rintro ⟨b, w⟩
    exact congrArg (TotalSpace.mk' _ b) ((castRankEquiv (hrank (c b))).apply_symm_apply w)

/-- The total space of `ofLocallyConstant n c C hrank` is homeomorphic over `B` to the disjoint
union of the constituent core total spaces. -/
def ofLocallyConstantTotalSpaceHomeomorph :
    (Σ a : α, (C a).core.TotalSpace) ≃ₜ (ofLocallyConstant n c C hrank).core.TotalSpace where
  toEquiv := ofLocallyConstantTotalEquiv n c C hrank
  continuous_toFun := by
    refine continuous_sigma fun a => ?_
    let e := ofLocallyConstantPullbackIso n c C hrank a
    have hcont : Continuous fun p : (C a).core.TotalSpace =>
        Pullback.lift (F := Fin n → 𝕜) (E := (ofLocallyConstant n c C hrank).core.Fiber)
          (stratumInclusion c a)
          (((ofLocallyConstant n c C hrank).pullbackHomeomorph (stratumInclusion c a))
            (e.inv.totalSpaceMap p)) :=
      (Pullback.continuous_lift _ _ _).comp
        (((ofLocallyConstant n c C hrank).pullbackHomeomorph _).continuous.comp
          e.inv.continuous_totalSpaceMap)
    refine hcont.congr fun p => ?_
    rcases p with ⟨x, v⟩
    simp only [e, ofLocallyConstantTotalEquiv, CoordinateHom.totalSpaceMap_mk,
      fiberMap_ofLocallyConstantPullbackIso_inv, pullbackHomeomorph_apply]
    exact Pullback.lift_mk (stratumInclusion c a) x _
  continuous_invFun := by
    refine continuous_of_cover_nhds
      (s := fun a : α => {q : (ofLocallyConstant n c C hrank).core.TotalSpace | c q.proj = a})
      (fun q => ⟨c q.proj,
        ((c.isLocallyConstant.isOpen_fiber (c q.proj)).preimage
          (ofLocallyConstant n c C hrank).core.continuous_proj).mem_nhds rfl⟩)
      fun a => ?_
    rw [continuousOn_iff_continuous_domRestrict]
    let e := ofLocallyConstantPullbackIso n c C hrank a
    let toPb : {q : (ofLocallyConstant n c C hrank).core.TotalSpace // c q.proj = a} →
        TotalSpace (Fin n → 𝕜)
          ((stratumInclusion c a) *ᵖ (ofLocallyConstant n c C hrank).core.Fiber) :=
      fun q => ⟨⟨q.1.proj, q.2⟩, q.1.2⟩
    have htoPb : Continuous toPb :=
      (inducing_pullbackTotalSpaceEmbedding (Fin n → 𝕜)
        (ofLocallyConstant n c C hrank).core.Fiber (stratumInclusion c a)).continuous_iff.2
        (((((ofLocallyConstant n c C hrank).core.continuous_proj.comp
          continuous_subtype_val).subtype_mk _)).prodMk continuous_subtype_val)
    have hcont : Continuous fun q :
        {q : (ofLocallyConstant n c C hrank).core.TotalSpace // c q.proj = a} =>
        (⟨a, e.hom.totalSpaceMap
          (((ofLocallyConstant n c C hrank).pullbackHomeomorph (stratumInclusion c a)).symm
            (toPb q))⟩ : Σ a : α, (C a).core.TotalSpace) :=
      continuous_sigmaMk.comp (e.hom.continuous_totalSpaceMap.comp
        (((ofLocallyConstant n c C hrank).pullbackHomeomorph _).symm.continuous.comp htoPb))
    refine hcont.congr fun q => ?_
    rcases q with ⟨⟨b, w⟩, hb⟩
    cases hb
    refine congrArg (Sigma.mk (c b)) ?_
    let b' : {x : B // c x = c b} := ⟨b, rfl⟩
    have hpb : ((ofLocallyConstant n c C hrank).pullbackHomeomorph
        (stratumInclusion c (c b))).symm (toPb ⟨⟨b, w⟩, rfl⟩) = ⟨b', w⟩ :=
      pullbackHomeomorph_symm_apply (ofLocallyConstant n c C hrank)
        (stratumInclusion c (c b)) (toPb ⟨⟨b, w⟩, rfl⟩)
    exact (congrArg e.hom.totalSpaceMap hpb).trans
      ((e.hom.totalSpaceMap_mk b' w).trans
        (congrArg (TotalSpace.mk' _ b')
          (DFunLike.congr_fun
            (fiberMap_ofLocallyConstantPullbackIso_hom n c C hrank (c b) b') w)))

@[simp]
theorem ofLocallyConstantTotalSpaceHomeomorph_apply (a : α) (p : (C a).core.TotalSpace) :
    ofLocallyConstantTotalSpaceHomeomorph n c C hrank ⟨a, p⟩ =
      ⟨p.proj.1, castRankEquiv (𝕜 := 𝕜) (hrank a) p.2⟩ := (rfl)

@[simp]
theorem ofLocallyConstantTotalSpaceHomeomorph_symm_apply
    (q : (ofLocallyConstant n c C hrank).core.TotalSpace) :
    (ofLocallyConstantTotalSpaceHomeomorph n c C hrank).symm q =
      ⟨c q.proj, ⟨⟨q.proj, rfl⟩,
        (castRankEquiv (𝕜 := 𝕜) (hrank (c q.proj))).symm q.2⟩⟩ := (rfl)

@[simp]
theorem proj_ofLocallyConstantTotalSpaceHomeomorph (p : Σ a : α, (C a).core.TotalSpace) :
    (ofLocallyConstantTotalSpaceHomeomorph n c C hrank p).proj = p.2.proj.1 := (rfl)

/-- Each constituent core total space embeds openly into the glued core total space. -/
theorem isOpenEmbedding_ofLocallyConstant_stratum (a : α) :
    IsOpenEmbedding (fun p : (C a).core.TotalSpace =>
      ofLocallyConstantTotalSpaceHomeomorph n c C hrank ⟨a, p⟩) :=
  (ofLocallyConstantTotalSpaceHomeomorph n c C hrank).isOpenEmbedding.comp IsOpenEmbedding.sigmaMk

/-- The image of the `a`th core total space is the clopen part where `c` takes the value `a`. -/
theorem range_ofLocallyConstant_stratum (a : α) :
    Set.range (fun p : (C a).core.TotalSpace =>
      ofLocallyConstantTotalSpaceHomeomorph n c C hrank ⟨a, p⟩) =
      {q : (ofLocallyConstant n c C hrank).core.TotalSpace | c q.proj = a} := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact p.proj.2
  · intro hq
    rcases q with ⟨b, w⟩
    cases hq
    refine ⟨⟨⟨b, rfl⟩, (castRankEquiv (𝕜 := 𝕜) (hrank (c b))).symm w⟩, ?_⟩
    dsimp only [ofLocallyConstantTotalSpaceHomeomorph_apply]
    exact congrArg (TotalSpace.mk' _ b) ((castRankEquiv (hrank (c b))).apply_symm_apply w)

/-- A map into `ofLocallyConstant n c C hrank` is continuous if and only if its restriction to each
clopen fibre of `c ∘ b` is continuous into the corresponding constituent core. -/
theorem continuous_ofLocallyConstant_mk_iff {Y : Type*} [TopologicalSpace Y] {b : Y → B}
    (hb : Continuous b) (s : Y → Fin n → 𝕜) :
    Continuous (fun y => (⟨b y, s y⟩ : (ofLocallyConstant n c C hrank).core.TotalSpace)) ↔
      ∀ a : α, Continuous (fun y : {y : Y // c (b y) = a} =>
        (⟨⟨b y.1, y.2⟩, (castRankEquiv (𝕜 := 𝕜) (hrank a)).symm (s y.1)⟩ :
          (C a).core.TotalSpace)) := by
  constructor
  · intro hs a
    apply (IsEmbedding.sigmaMk (σ := fun a => (C a).core.TotalSpace)).continuous_iff.2
    refine ((ofLocallyConstantTotalSpaceHomeomorph n c C hrank).symm.continuous.comp
      (hs.comp continuous_subtype_val)).congr fun y => ?_
    rcases y with ⟨y, hy⟩
    cases hy
    rfl
  · intro hs
    refine continuous_of_cover_nhds (s := fun a : α => {y : Y | c (b y) = a})
      (fun y => ⟨c (b y), ((c.isLocallyConstant.isOpen_fiber _).preimage hb).mem_nhds rfl⟩)
      fun a => ?_
    rw [continuousOn_iff_continuous_domRestrict]
    refine ((ofLocallyConstantTotalSpaceHomeomorph n c C hrank).continuous.comp
      (continuous_sigmaMk.comp (hs a))).congr fun y => ?_
    rcases y with ⟨y, hy⟩
    cases hy
    dsimp only [Set.domRestrict_apply, Function.comp_apply,
      ofLocallyConstantTotalSpaceHomeomorph_apply]
    exact congrArg (TotalSpace.mk' _ (b y)) ((castRankEquiv (hrank (c (b y)))).apply_symm_apply _)

end OfLocallyConstant

end TauCeti.FiniteRankBundleCore
