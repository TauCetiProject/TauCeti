/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.LocallyConstant.Prod
public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback

import TauCeti.Topology.FiberBundle.Pullback

/-!
# Clopen-stratum gluing and constant-rank comparisons for bundle atlases

Each rank stratum of a variable-rank `TauCeti.FiniteRankAtlas` is a constant-rank
`TauCeti.FiniteRankBundleCore` (`FiniteRankAtlas.stratumCore`). Conversely, given any locally
constant partition `c : LocallyConstant X α` and constant-rank cores
`C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}` on its clopen fibres,
`FiniteRankAtlas.ofClopenCores` assembles them into a single `FiniteRankAtlas 𝕜 X` whose rank at
`x` is `(C (c x)).rank`.

This clopen-gluing construction handles operations whose output rank strata merge several input
rank strata—such as Whitney sums `(A.rank x, D.rank x) ↦ A.rank x + D.rank x` and tensor products
`(A.rank x, D.rank x) ↦ A.rank x * D.rank x`—as well as constant-rank comparisons:

* `FiniteRankAtlas.ofClopenCores_stratumCore` shows that re-gluing the rank-stratum cores of an
  atlas `A` along `A.rank` recovers `A`.
* `FiniteRankAtlas.clopenTotalSpaceHomeomorph` identifies the reconstructed total space of
  `ofClopenCores c C` with the disjoint union `Σ a : α, (C a).core.TotalSpace`, and
  `FiniteRankAtlas.mapClopenCores` glues families of coordinate morphisms functorially and
  additively without completeness assumptions on `𝕜`.
* `FiniteRankAtlas.clopenPullIso` identifies an atlas with the re-gluing of its restrictions to
  any finer clopen partition `c` on whose fibres its rank is constant.
* `FiniteRankAtlas.ofCore` embeds `FiniteRankBundleCore 𝕜 X` faithfully and additively into
  `FiniteRankAtlas 𝕜 X`, with essential image the atlases of constant rank
  (`FiniteRankAtlas.ofCoreToCoreIso`).
* Over a complete scalar field, `FiniteRankAtlas.clopenHomAddEquiv` identifies morphisms between
  clopen-glued atlases with families of `VectorBundleCore.CoordinateHom` chart-matrix morphisms,
  making `ofCore` full, encoding arbitrary variable-rank morphisms on joint rank bi-strata
  (`FiniteRankAtlas.bistratumHomAddEquiv`), and characterizing categorical isomorphisms by
  fibrewise bijectivity (`FiniteRankAtlas.isIso_iff_bijective`).

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* M. F. Atiyah, *K-Theory*, §1.1–1.2.
-/

public section

open Bundle CategoryTheory Topology VectorBundleCore

namespace TauCeti.FiniteRankAtlas

universe u v w

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

/-- Coordinate reindexing equivalence along an equality of finite dimensions. -/
private def finCongrCLE {m n : ℕ} (h : m = n) : (Fin m → 𝕜) ≃L[𝕜] (Fin n → 𝕜) :=
  ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n ↦ 𝕜) (finCongr h)

private theorem finCongrCLE_apply {m n : ℕ} (h : m = n) (v : Fin m → 𝕜) (i : Fin n) :
    finCongrCLE (𝕜 := 𝕜) h v i = v (Fin.cast h.symm i) :=
  (rfl)

private theorem finCongrCLE_symm_apply {m n : ℕ} (h : m = n) (v : Fin n → 𝕜) (i : Fin m) :
    (finCongrCLE (𝕜 := 𝕜) h).symm v i = v (Fin.cast h i) :=
  (rfl)

private theorem finCongrCLE_rfl (n : ℕ) :
    finCongrCLE (𝕜 := 𝕜) (rfl : n = n) = ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜) := by
  ext v i
  rfl

private def finCongrLE {m n : ℕ} (h : m = n) : (Fin m → 𝕜) ≃ₗ[𝕜] (Fin n → 𝕜) where
  toFun v i := v (Fin.cast h.symm i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v i := v (Fin.cast h i)
  left_inv v := funext fun _ ↦ congrArg v (Fin.ext rfl)
  right_inv v := funext fun _ ↦ congrArg v (Fin.ext rfl)

private theorem vectorBundleCore_eq {B F ι : Type*} [TopologicalSpace B]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {Z₁ Z₂ : VectorBundleCore 𝕜 B F ι}
    (hb : Z₁.baseSet = Z₂.baseSet) (hi : Z₁.indexAt = Z₂.indexAt)
    (hc : Z₁.coordChange = Z₂.coordChange) : Z₁ = Z₂ := by
  cases Z₁; cases Z₂
  dsimp only at hb hi hc
  subst hb hi hc
  rfl

private theorem core_mk_eq_mk {B : Type*} [TopologicalSpace B] {n : ℕ}
    {c₁ c₂ : VectorBundleCore 𝕜 B (Fin n → 𝕜) B} {h₁ h₂}
    (hc : c₁ = c₂) :
    (⟨n, c₁, h₁⟩ : FiniteRankBundleCore 𝕜 B) = ⟨n, c₂, h₂⟩ := by
  subst hc
  rfl

private theorem atlas_mk_eq_mk {r : LocallyConstant X ℕ}
    {c₁ c₂ : ∀ n, VectorBundleCore 𝕜 {x : X // r x = n} (Fin n → 𝕜) {x : X // r x = n}}
    {h₁ h₂} (hc : c₁ = c₂) :
    (⟨r, c₁, h₁⟩ : FiniteRankAtlas 𝕜 X) = ⟨r, c₂, h₂⟩ := by
  subst hc
  rfl

/-! ### Restriction to strata and constant-rank pieces -/

/-- The constant-rank point-indexed bundle core on the `n`th clopen rank stratum of an atlas. -/
-- Expose the rank projection so fibre types over the stratum reduce to `Fin n → 𝕜`.
@[expose, implicit_reducible]
def stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    FiniteRankBundleCore 𝕜 {x : X // A.rank x = n} where
  rank := n
  core := A.charts n
  indexAt_eq := A.indexAt_eq n

@[simp]
theorem rank_stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (A.stratumCore n).rank = n :=
  (rfl)

@[simp]
theorem core_stratumCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    (A.stratumCore n).core = A.charts n :=
  (rfl)

/-- Pull back an atlas along a continuous map `g : C(Y, X)` on which `A.rank` takes a constant
value `n`, producing a constant-rank `FiniteRankBundleCore` over `Y`. -/
-- Expose the rank projection so fibre types reduce to `Fin n → 𝕜`.
@[expose, implicit_reducible]
def pullCore {Y : Type*} [TopologicalSpace Y] (A : FiniteRankAtlas 𝕜 X)
    (g : C(Y, X)) (n : ℕ) (hg : ∀ y, A.rank (g y) = n) :
    FiniteRankBundleCore 𝕜 Y :=
  (A.stratumCore n).pullback ⟨fun y ↦ ⟨g y, hg y⟩, g.continuous.subtype_mk hg⟩

@[simp]
theorem rank_pullCore {Y : Type*} [TopologicalSpace Y] (A : FiniteRankAtlas 𝕜 X)
    (g : C(Y, X)) (n : ℕ) (hg : ∀ y, A.rank (g y) = n) :
    (A.pullCore g n hg).rank = n :=
  (rfl)

/-- The canonical lift from the total space of `A.pullCore g n hg` into the reconstructed total
space of `A` is continuous. -/
theorem continuous_pullCoreLift {Y : Type*} [TopologicalSpace Y] (A : FiniteRankAtlas 𝕜 X)
    (g : C(Y, X)) (n : ℕ) (hg : ∀ y, A.rank (g y) = n) :
    Continuous (fun p : (A.pullCore g n hg).core.TotalSpace ↦
      (⟨g p.proj, fun i ↦ p.2 (Fin.cast (hg p.proj) i)⟩ : TotalSpace Unit A.Fiber)) := by
  let g' : C(Y, {x : X // A.rank x = n}) := ⟨fun y ↦ ⟨g y, hg y⟩, g.continuous.subtype_mk hg⟩
  have hlift : Continuous (fun p : (A.pullCore g n hg).core.TotalSpace ↦
      Pullback.lift (F := Fin n → 𝕜) (E := (A.charts n).Fiber) g'
        ((A.stratumCore n).pullbackHomeomorph g' p)) :=
    (Pullback.continuous_lift (Fin n → 𝕜) (A.charts n).Fiber g').comp
      ((A.stratumCore n).pullbackHomeomorph g').continuous
  refine (A.totalSpaceHomeomorph.continuous.comp (continuous_sigmaMk.comp hlift)).congr fun p ↦ ?_
  rcases p with ⟨y, v⟩
  dsimp only [Function.comp_apply]
  rw [FiniteRankBundleCore.pullbackHomeomorph_apply,
    Pullback.lift_mk (E := (A.charts n).Fiber) (F := Fin n → 𝕜) (⇑g') y v,
    A.totalSpaceHomeomorph_apply]
  rfl

/-- A map into the total space of `A.pullCore g n hg` is continuous whenever its base projection
and its lift into the reconstructed total space of `A` are continuous. -/
theorem continuous_into_pullCore {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y]
    (A : FiniteRankAtlas 𝕜 X) (g : C(Y, X)) (n : ℕ) (hg : ∀ y, A.rank (g y) = n)
    {b : Z → Y} (hb : Continuous b) {s : Z → Fin n → 𝕜}
    (hs : Continuous (fun z ↦
      (⟨g (b z), fun i ↦ s z (Fin.cast (hg (b z)) i)⟩ : TotalSpace Unit A.Fiber))) :
    Continuous (fun z ↦ (⟨b z, s z⟩ : (A.pullCore g n hg).core.TotalSpace)) := by
  let g' : C(Y, {x : X // A.rank x = n}) := ⟨fun y ↦ ⟨g y, hg y⟩, g.continuous.subtype_mk hg⟩
  apply ((A.stratumCore n).pullbackHomeomorph g').isInducing.continuous_iff.2
  dsimp only [Function.comp_def]
  simp only [FiniteRankBundleCore.pullbackHomeomorph_apply]
  rw [Bundle.Pullback.continuous_iff]
  refine ⟨hb, ?_⟩
  have hstrata := (A.continuous_mk_iff_rankStrata (g.continuous.comp hb)
    (fun z ↦ fun i ↦ s z (Fin.cast (hg (b z)) i))).1 hs n
  let zToSub : Z → {z : Z // A.rank (g (b z)) = n} := fun z ↦ ⟨z, hg (b z)⟩
  have hz : Continuous zToSub := continuous_id.subtype_mk _
  refine (hstrata.comp hz).congr fun z ↦ ?_
  dsimp only [Function.comp_apply, zToSub]
  exact congrArg (TotalSpace.mk' (E := (A.charts n).Fiber) (Fin n → 𝕜) ⟨g (b z), hg (b z)⟩)
    (funext fun i ↦ congrArg (s z) (Fin.ext rfl))

/-- Extract a constant-rank `FiniteRankBundleCore` over `X` from an atlas of constant rank `n`. -/
-- Expose the rank projection so fibre types reduce to `Fin n → 𝕜`.
@[expose, implicit_reducible]
def toCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) (h : ∀ x, A.rank x = n) :
    FiniteRankBundleCore 𝕜 X :=
  A.pullCore (ContinuousMap.id X) n h

@[simp]
theorem rank_toCore (A : FiniteRankAtlas 𝕜 X) (n : ℕ) (h : ∀ x, A.rank x = n) :
    (A.toCore n h).rank = n :=
  (rfl)

/-! ### Gluing constant-rank cores over a clopen partition -/

section ClopenGluing

variable {α : Type w} (c : LocallyConstant X α)

private def clopenChartBaseSet (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a})
    (n : ℕ) (i : {x : X // (C (c x)).rank = n}) : Set {x : X // (C (c x)).rank = n} :=
  {y | ∃ hy : c y.1 = c i.1, ⟨y.1, hy⟩ ∈ (C (c i.1)).core.baseSet ⟨i.1, rfl⟩}

private theorem mem_clopenChartBaseSet_of_eq
    {C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    {n : ℕ} {a : α} {i y : {x : X // (C (c x)).rank = n}}
    (hi : c i.1 = a) (hy : c y.1 = a) :
    y ∈ clopenChartBaseSet c C n i ↔ ⟨y.1, hy⟩ ∈ (C a).core.baseSet ⟨i.1, hi⟩ := by
  rcases i with ⟨xi, hxi⟩
  dsimp only at hi ⊢
  subst hi
  exact ⟨fun ⟨_, hm⟩ ↦ hm, fun hm ↦ ⟨hy, hm⟩⟩

private theorem isOpen_clopenChartBaseSet (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a})
    (n : ℕ) (i : {x : X // (C (c x)).rank = n}) :
    IsOpen (clopenChartBaseSet c C n i) := by
  let S : Set {x : X // (C (c x)).rank = n} := {y | c y.1 = c i.1}
  have hS : IsOpen S := (c.isLocallyConstant.isOpen_fiber (c i.1)).preimage continuous_subtype_val
  let p : S → {x : X // c x = c i.1} := fun y ↦ ⟨y.1.1, y.2⟩
  have hp : Continuous p := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  convert hS.isOpenMap_subtype_val _ (((C (c i.1)).core.isOpen_baseSet ⟨i.1, rfl⟩).preimage hp)
    using 1
  ext y
  exact ⟨fun ⟨hy, hm⟩ ↦ ⟨⟨y, hy⟩, hm, rfl⟩, fun ⟨⟨_, hy⟩, hm, heq⟩ ↦ heq ▸ ⟨hy, hm⟩⟩

private noncomputable def clopenCoordChange
    (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a})
    (n : ℕ) (i j x : {x : X // (C (c x)).rank = n}) :
    (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜) :=
  open scoped Classical in
  if h : c i.1 = c j.1 ∧ c x.1 = c i.1 then
    (finCongrCLE (𝕜 := 𝕜) i.2).toContinuousLinearMap.comp
      (((C (c i.1)).core.coordChange ⟨i.1, rfl⟩ ⟨j.1, h.1.symm⟩ ⟨x.1, h.2⟩).comp
        (finCongrCLE (𝕜 := 𝕜) i.2).symm.toContinuousLinearMap)
  else 0

private theorem clopenCoordChange_eq_of_eq
    (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a})
    {n : ℕ} {a : α} (ha : (C a).rank = n)
    {i j x : {x : X // (C (c x)).rank = n}}
    (hi : c i.1 = a) (hj : c j.1 = a) (hx : c x.1 = a) :
    clopenCoordChange c C n i j x =
      (finCongrCLE (𝕜 := 𝕜) ha).toContinuousLinearMap.comp
        (((C a).core.coordChange ⟨i.1, hi⟩ ⟨j.1, hj⟩ ⟨x.1, hx⟩).comp
          (finCongrCLE (𝕜 := 𝕜) ha).symm.toContinuousLinearMap) := by
  unfold clopenCoordChange
  split_ifs with h
  · rcases i with ⟨xi, hxi⟩
    dsimp only at hi ⊢
    subst hi
    rfl
  · exact False.elim (h ⟨hi.trans hj.symm, hx.trans hi.symm⟩)

/-- The glued coordinate bundle core on the `n`th rank stratum of a clopen-partitioned family of
constant-rank cores. -/
noncomputable def clopenStratumCharts (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a})
    (n : ℕ) :
    VectorBundleCore 𝕜 {x : X // (C (c x)).rank = n} (Fin n → 𝕜)
      {x : X // (C (c x)).rank = n} where
  baseSet := clopenChartBaseSet c C n
  isOpen_baseSet := isOpen_clopenChartBaseSet c C n
  indexAt := id
  mem_baseSet_at x := ⟨rfl, (C (c x.1)).mem_baseSet_self ⟨x.1, rfl⟩⟩
  coordChange := clopenCoordChange c C n
  coordChange_self i x hx v := by
    obtain ⟨hx', hmem⟩ := hx
    rw [clopenCoordChange_eq_of_eq c C i.2 rfl rfl hx']
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [(C (c i.1)).core.coordChange_self ⟨i.1, rfl⟩ ⟨x.1, hx'⟩ hmem]
    exact (finCongrCLE (𝕜 := 𝕜) i.2).apply_symm_apply v
  continuousOn_coordChange i j := by
    by_cases hij : c i.1 = c j.1
    · rw [continuousOn_iff_continuous_domRestrict]
      let q : ↥(clopenChartBaseSet c C n i ∩ clopenChartBaseSet c C n j) →
          ↥((C (c i.1)).core.baseSet ⟨i.1, rfl⟩ ∩
            (C (c i.1)).core.baseSet ⟨j.1, hij.symm⟩) := fun y ↦
        ⟨⟨y.1.1, y.2.1.choose⟩, y.2.1.choose_spec,
          (mem_clopenChartBaseSet_of_eq c hij.symm y.2.1.choose).1 y.2.2⟩
      have hq : Continuous q :=
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
      have hc := ((((C (c i.1)).core.continuousOn_coordChange ⟨i.1, rfl⟩
        ⟨j.1, hij.symm⟩).domRestrict.comp hq).clm_comp_const
          (finCongrCLE (𝕜 := 𝕜) i.2).symm.toContinuousLinearMap).const_clm_comp
            (finCongrCLE (𝕜 := 𝕜) i.2).toContinuousLinearMap
      refine hc.congr fun y ↦ ?_
      exact (clopenCoordChange_eq_of_eq c C i.2 rfl hij.symm y.2.1.choose).symm
    · have hempty : clopenChartBaseSet c C n i ∩ clopenChartBaseSet c C n j = ∅ := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
        rintro ⟨hyi, -⟩ ⟨hyj, -⟩
        exact hij (hyi.symm.trans hyj)
      rw [hempty]
      exact continuousOn_empty _
  coordChange_comp i j k x hx v := by
    obtain ⟨⟨⟨hxi, hmi⟩, ⟨hxj, hmj⟩⟩, ⟨hxk, hmk⟩⟩ := hx
    have hi : c i.1 = c x.1 := hxi.symm
    have hj : c j.1 = c x.1 := hxj.symm
    have hk : c k.1 = c x.1 := hxk.symm
    rw [clopenCoordChange_eq_of_eq c C x.2 hj hk rfl,
      clopenCoordChange_eq_of_eq c C x.2 hi hj rfl,
      clopenCoordChange_eq_of_eq c C x.2 hi hk rfl]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
    have hmi' := (mem_clopenChartBaseSet_of_eq c hi rfl).1 ⟨hxi, hmi⟩
    have hmj' := (mem_clopenChartBaseSet_of_eq c hj rfl).1 ⟨hxj, hmj⟩
    have hmk' := (mem_clopenChartBaseSet_of_eq c hk rfl).1 ⟨hxk, hmk⟩
    rw [(C (c x.1)).core.coordChange_comp ⟨i.1, hi⟩ ⟨j.1, hj⟩ ⟨k.1, hk⟩ ⟨x.1, rfl⟩
      ⟨⟨hmi', hmj'⟩, hmk'⟩]

@[simp]
theorem clopenStratumCharts_indexAt (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a})
    (n : ℕ) (x : {x : X // (C (c x)).rank = n}) :
    (clopenStratumCharts c C n).indexAt x = x :=
  (rfl)

@[simp]
private theorem clopenStratumCharts_coordChange
    (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a})
    (n : ℕ) (i j x : {x : X // (C (c x)).rank = n}) :
    (clopenStratumCharts c C n).coordChange i j x = clopenCoordChange c C n i j x :=
  (rfl)

/-- Assemble constant-rank point-indexed bundle cores on the clopen fibres of a locally constant
function `c : LocallyConstant X α` into a single `FiniteRankAtlas 𝕜 X`. -/
-- Expose the rank projection so fibre types over `x` reduce to `Fin (C (c x)).rank → 𝕜`.
@[expose, implicit_reducible]
noncomputable def ofClopenCores (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}) :
    FiniteRankAtlas 𝕜 X where
  rank := ⟨fun x ↦ (C (c x)).rank, c.isLocallyConstant.comp fun a ↦ (C a).rank⟩
  charts := clopenStratumCharts c C
  indexAt_eq := clopenStratumCharts_indexAt c C

@[simp]
theorem rank_ofClopenCores (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}) :
    (ofClopenCores c C).rank = c.map (fun a ↦ (C a).rank) :=
  LocallyConstant.ext fun _ ↦ rfl

@[simp]
theorem charts_ofClopenCores (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}) (n : ℕ) :
    (ofClopenCores c C).charts n = clopenStratumCharts c C n :=
  (rfl)

/-- Re-gluing the rank-stratum cores of an atlas along its own rank function recovers the original
atlas on the nose. -/
@[simp]
theorem ofClopenCores_stratumCore (A : FiniteRankAtlas 𝕜 X) :
    ofClopenCores A.rank A.stratumCore = A := by
  refine atlas_mk_eq_mk (funext fun n ↦ vectorBundleCore_eq ?_
    (funext fun x ↦ (A.indexAt_eq n x).symm) ?_)
  · funext ⟨xi, hxi⟩
    subst hxi
    ext ⟨y, hy⟩
    exact ⟨fun ⟨_, hm⟩ ↦ hm, fun hm ↦ ⟨hy, hm⟩⟩
  · funext ⟨xi, hxi⟩ j x
    subst hxi
    rw [clopenStratumCharts_coordChange,
      clopenCoordChange_eq_of_eq A.rank A.stratumCore rfl rfl j.2 x.2, finCongrCLE_rfl]
    ext v k
    rfl

/-! ### Total-space comparison and gluing of morphisms -/

private noncomputable def clopenGluedEquiv
    (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}) :
    (Σ a : α, (C a).core.TotalSpace) ≃ (ofClopenCores c C).GluedTotalSpace where
  toFun p := ⟨(C p.1).rank, ⟨⟨p.2.proj.1, congrArg (fun a ↦ (C a).rank) p.2.proj.2⟩,
    fun i ↦ p.2.2 i⟩⟩
  invFun q := ⟨c q.2.proj.1, ⟨⟨q.2.proj.1, rfl⟩, fun i ↦ q.2.2 (Fin.cast q.2.proj.2 i)⟩⟩
  left_inv p := by
    rcases p with ⟨a, ⟨⟨x, hx⟩, v⟩⟩
    cases hx
    rfl
  right_inv q := by
    rcases q with ⟨n, ⟨⟨x, hx⟩, v⟩⟩
    cases hx
    rfl

private theorem continuous_clopenGluedEquiv
    (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}) :
    Continuous (clopenGluedEquiv c C) := by
  refine continuous_sigma fun a ↦
    (continuous_sigmaMk (σ := fun n ↦ ((ofClopenCores c C).charts n).TotalSpace)
      (i := (C a).rank)).comp ?_
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  have hproj : Continuous (fun p : (C a).core.TotalSpace ↦
      (⟨p.proj.1, congrArg (fun b ↦ (C b).rank) p.proj.2⟩ :
        {x : X // (ofClopenCores c C).rank x = (C a).rank})) :=
    (continuous_subtype_val.comp (C a).core.continuous_proj).subtype_mk _
  refine ⟨hproj.continuousAt, ?_⟩
  have hp₀ : p₀ ∈ ((C a).core.localTrivAt p₀.proj).source :=
    (C a).core.mem_source_at p₀.proj p₀.2
  have hc := (((C a).core.localTrivAt p₀.proj).continuousOn.continuousAt
    (((C a).core.localTrivAt p₀.proj).open_source.mem_nhds hp₀)).snd
  refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p ↦ ?_)
  dsimp only [clopenGluedEquiv, VectorBundleCore.trivializationAt, VectorBundleCore.localTrivAt]
  simp only [charts_ofClopenCores, clopenStratumCharts_indexAt, (C a).indexAt_eq,
    localTriv_apply, clopenStratumCharts_coordChange]
  rw [clopenCoordChange_eq_of_eq c C rfl p.proj.2 p₀.proj.2 p.proj.2, finCongrCLE_rfl]
  rfl

private theorem continuous_clopenGluedEquiv_symm
    (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}) :
    Continuous (clopenGluedEquiv c C).symm := by
  refine continuous_sigma fun n ↦ continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  obtain ⟨a, ha_def⟩ : ∃ a, c q₀.proj.1 = a := ⟨_, rfl⟩
  have ha : (C a).rank = n := ha_def ▸ q₀.proj.2
  let U : Set ((ofClopenCores c C).charts n).TotalSpace :=
    {q | c q.proj.1 = a}
  have hU_open : IsOpen U :=
    ((c.isLocallyConstant.isOpen_fiber a).preimage continuous_subtype_val).preimage
      ((ofClopenCores c C).charts n).continuous_proj
  have hq₀U : q₀ ∈ U := ha_def
  let toA : U → (C a).core.TotalSpace := fun q ↦
    ⟨⟨q.1.proj.1, q.2⟩, (finCongrCLE (𝕜 := 𝕜) ha).symm q.1.2⟩
  have htoA : ContinuousAt toA ⟨q₀, hq₀U⟩ := by
    rw [FiberBundle.continuousAt_totalSpace]
    have hproj : Continuous (fun q : U ↦ (⟨q.1.proj.1, q.2⟩ : {x : X // c x = a})) :=
      (continuous_subtype_val.comp
        (((ofClopenCores c C).charts n).continuous_proj.comp continuous_subtype_val)).subtype_mk _
    refine ⟨hproj.continuousAt, ?_⟩
    let e := ((ofClopenCores c C).charts n).localTrivAt q₀.proj
    have hq₀e : q₀ ∈ e.source := ((ofClopenCores c C).charts n).mem_source_at q₀.proj q₀.2
    have hsub : ContinuousAt (Subtype.val : U → ((ofClopenCores c C).charts n).TotalSpace)
        ⟨q₀, hq₀U⟩ := continuous_subtype_val.continuousAt
    have hce := ((finCongrCLE (𝕜 := 𝕜) ha).symm.continuous.continuousAt.comp
      ((e.continuousOn.continuousAt (e.open_source.mem_nhds hq₀e)).snd)).comp hsub
    refine hce.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q ↦ ?_)
    dsimp only [Function.comp_apply, toA, e, VectorBundleCore.trivializationAt,
      VectorBundleCore.localTrivAt]
    simp only [charts_ofClopenCores, clopenStratumCharts_indexAt, (C a).indexAt_eq,
      localTriv_apply, clopenStratumCharts_coordChange]
    rw [clopenCoordChange_eq_of_eq c C ha q.2 ha_def q.2]
    exact ((finCongrCLE (𝕜 := 𝕜) ha).symm_apply_apply _).symm
  have hsigma : ContinuousAt (fun q : U ↦
      (⟨a, toA q⟩ : Σ b : α, (C b).core.TotalSpace)) ⟨q₀, hq₀U⟩ :=
    continuous_sigmaMk.continuousAt.comp htoA
  apply ContinuousWithinAt.continuousAt (s := U) _ (hU_open.mem_nhds hq₀U)
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ hq₀U]
  refine hsigma.congr (Filter.Eventually.of_forall fun q ↦ ?_)
  rcases q with ⟨⟨⟨x, hx_rank⟩, v⟩, hx_a⟩
  have hx_a' : c x = a := hx_a
  subst hx_a'
  rfl

/-- The reconstructed total space of `ofClopenCores c C` is homeomorphic over `X` to the disjoint
union of the constituent core total spaces. -/
noncomputable def clopenTotalSpaceHomeomorph
    (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}) :
    (Σ a : α, (C a).core.TotalSpace) ≃ₜ TotalSpace Unit (ofClopenCores c C).Fiber :=
  (Homeomorph.mk (clopenGluedEquiv c C)
    (continuous_clopenGluedEquiv c C)
    (continuous_clopenGluedEquiv_symm c C)).trans
      (ofClopenCores c C).totalSpaceHomeomorph

@[simp]
theorem clopenTotalSpaceHomeomorph_apply
    (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a})
    (a : α) (p : (C a).core.TotalSpace) :
    clopenTotalSpaceHomeomorph c C ⟨a, p⟩ =
      ⟨p.proj.1, fun i ↦ p.2 (Fin.cast (congrArg (fun b ↦ (C b).rank) p.proj.2) i)⟩ := by
  rcases p with ⟨⟨x, hx⟩, v⟩
  subst hx
  simp [clopenTotalSpaceHomeomorph, clopenGluedEquiv]

@[simp]
theorem clopenTotalSpaceHomeomorph_symm_apply
    (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a})
    (p : TotalSpace Unit (ofClopenCores c C).Fiber) :
    (clopenTotalSpaceHomeomorph c C).symm p = ⟨c p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩ := by
  rcases p with ⟨x, v⟩
  simp [clopenTotalSpaceHomeomorph, clopenGluedEquiv]

/-- A map into `ofClopenCores c C` is continuous if and only if its restriction to each clopen
piece `{y : Y // c (b y) = a}` into `(C a).core.TotalSpace` is continuous. -/
theorem continuous_mk_iff_clopenCores {Y : Type*} [TopologicalSpace Y] {b : Y → X}
    (hb : Continuous b) (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a})
    (s : ∀ y, (ofClopenCores c C).Fiber (b y)) :
    Continuous (fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit (ofClopenCores c C).Fiber)) ↔
      ∀ a : α, Continuous (fun y : {y : Y // c (b y) = a} ↦
        (⟨⟨b y.1, y.2⟩,
          fun i ↦ s y.1 (Fin.cast (congrArg (fun d ↦ (C d).rank) y.2.symm) i)⟩ :
            (C a).core.TotalSpace)) := by
  constructor
  · intro hs a
    apply (IsEmbedding.sigmaMk (σ := fun a ↦ (C a).core.TotalSpace)).continuous_iff.2
    convert (clopenTotalSpaceHomeomorph c C).symm.continuous.comp
      (hs.comp continuous_subtype_val) using 1
    funext ⟨y, hy⟩
    cases hy
    simp only [Function.comp_apply, clopenTotalSpaceHomeomorph_symm_apply, Fin.cast_refl, id_eq]
  · intro hs
    apply continuous_of_cover_nhds (s := fun a : α ↦ {y : Y | c (b y) = a})
    · intro y
      exact ⟨c (b y), ((c.isLocallyConstant.isOpen_fiber _).preimage hb).mem_nhds rfl⟩
    · intro a
      rw [continuousOn_iff_continuous_domRestrict]
      convert (clopenTotalSpaceHomeomorph c C).continuous.comp
        (continuous_sigmaMk.comp (hs a)) using 1
      funext ⟨y, hy⟩
      cases hy
      simp only [Set.domRestrict_apply, Function.comp_apply, clopenTotalSpaceHomeomorph_apply,
        Fin.cast_refl, id_eq]

/-- Glue a family of constant-rank coordinate morphisms over the clopen fibres of `c` into a
morphism of variable-rank bundle atlases. -/
noncomputable def mapClopenCores
    {C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    (f : ∀ a : α, C a ⟶ D a) : ofClopenCores c C ⟶ ofClopenCores c D where
  fiberMap x := ((f (c x)).fiberMap ⟨x, rfl⟩).toLinearMap
  continuous_totalSpaceMap := by
    have hsigma : Continuous (fun p : Σ a : α, (C a).core.TotalSpace ↦
        (⟨p.1, (f p.1).totalSpaceMap p.2⟩ : Σ a : α, (D a).core.TotalSpace)) :=
      continuous_sigma fun a ↦ continuous_sigmaMk.comp (f a).continuous_totalSpaceMap
    exact ((clopenTotalSpaceHomeomorph c D).continuous.comp
      (hsigma.comp (clopenTotalSpaceHomeomorph c C).symm.continuous)).congr fun p ↦ by
      rcases p with ⟨x, v⟩
      dsimp only [Function.comp_apply]
      rw [clopenTotalSpaceHomeomorph_symm_apply]
      dsimp only
      have hmk : (f (c x)).totalSpaceMap ⟨⟨x, rfl⟩, v⟩ =
          ⟨⟨x, rfl⟩, (f (c x)).fiberMap ⟨x, rfl⟩ v⟩ :=
        CoordinateHom.totalSpaceMap_mk (f (c x)) ⟨x, rfl⟩ v
      rw [hmk, clopenTotalSpaceHomeomorph_apply]
      rfl

@[simp]
theorem fiberMap_mapClopenCores
    {C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    (f : ∀ a : α, C a ⟶ D a) (x : X) :
    (mapClopenCores c f).fiberMap x = ((f (c x)).fiberMap ⟨x, rfl⟩).toLinearMap :=
  (rfl)

@[simp]
theorem mapClopenCores_id (C : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}) :
    mapClopenCores c (fun a ↦ 𝟙 (C a)) = 𝟙 (ofClopenCores c C) :=
  hom_ext fun x ↦ LinearMap.ext fun v ↦ by simp [FiniteRankBundleCore.fiberMap_id]

@[simp]
theorem mapClopenCores_comp
    {C D E : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    (f : ∀ a : α, C a ⟶ D a) (g : ∀ a : α, D a ⟶ E a) :
    mapClopenCores c (fun a ↦ f a ≫ g a) = mapClopenCores c f ≫ mapClopenCores c g :=
  hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp

@[simp]
theorem mapClopenCores_zero
    (C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}) :
    mapClopenCores c (fun a ↦ (0 : C a ⟶ D a)) = 0 :=
  hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp

@[simp]
theorem mapClopenCores_add
    {C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    (f g : ∀ a : α, C a ⟶ D a) :
    mapClopenCores c (fun a ↦ f a + g a) = mapClopenCores c f + mapClopenCores c g :=
  hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp

@[simp]
theorem mapClopenCores_neg
    {C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    (f : ∀ a : α, C a ⟶ D a) :
    mapClopenCores c (fun a ↦ -f a) = -mapClopenCores c f :=
  hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp

/-- Gluing constant-rank coordinate morphisms over a clopen partition is faithful. -/
theorem mapClopenCores_injective
    {C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}} :
    Function.Injective (mapClopenCores c (C := C) (D := D)) := by
  intro f g h
  funext a
  apply FiniteRankBundleCore.hom_ext
  rintro ⟨x, hx⟩
  subst hx
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun k : ofClopenCores c C ⟶ ofClopenCores c D ↦ k.fiberMap x v) h

/-- Glue a family of constant-rank core isomorphisms over `c` into an isomorphism of atlases. -/
noncomputable def isoClopenCores
    {C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    (e : ∀ a : α, C a ≅ D a) : ofClopenCores c C ≅ ofClopenCores c D where
  hom := mapClopenCores c fun a ↦ (e a).hom
  inv := mapClopenCores c fun a ↦ (e a).inv
  hom_inv_id := by simp [← mapClopenCores_comp]
  inv_hom_id := by simp [← mapClopenCores_comp]

@[simp]
theorem isoClopenCores_hom
    {C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    (e : ∀ a : α, C a ≅ D a) :
    (isoClopenCores c e).hom = mapClopenCores c (fun a ↦ (e a).hom) :=
  (rfl)

@[simp]
theorem isoClopenCores_inv
    {C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    (e : ∀ a : α, C a ≅ D a) :
    (isoClopenCores c e).inv = mapClopenCores c (fun a ↦ (e a).inv) :=
  (rfl)

section ClopenRefinement

/-- Restrict an atlas `A` to each clopen fibre of `c` when `A.rank` factors through `c` via `r`. -/
-- Expose the rank projection so fibre types reduce to `Fin (r a) → 𝕜`.
@[expose, implicit_reducible]
def clopenPullCore (A : FiniteRankAtlas 𝕜 X) (r : α → ℕ) (hr : ∀ x, A.rank x = r (c x))
    (a : α) : FiniteRankBundleCore 𝕜 {x : X // c x = a} :=
  A.pullCore ⟨Subtype.val, continuous_subtype_val⟩ (r a)
    fun x ↦ (hr x.1).trans (congrArg r x.2)

@[simp]
theorem rank_clopenPullCore (A : FiniteRankAtlas 𝕜 X) (r : α → ℕ)
    (hr : ∀ x, A.rank x = r (c x)) (a : α) :
    (A.clopenPullCore c r hr a).rank = r a :=
  (rfl)

/-- Refining an atlas along a finer clopen partition `c` on whose fibres its rank is constant gives
an isomorphic atlas, by coordinate reindexing along `hr` on every fibre. -/
noncomputable def clopenPullIso (A : FiniteRankAtlas 𝕜 X) (r : α → ℕ)
    (hr : ∀ x, A.rank x = r (c x)) :
    ofClopenCores c (A.clopenPullCore c r hr) ≅ A :=
  isoMk (fun x ↦ finCongrLE (𝕜 := 𝕜) (hr x).symm)
    (by
      have hsigma : Continuous (fun p : Σ a : α, (A.clopenPullCore c r hr a).core.TotalSpace ↦
          (⟨p.2.proj.1, fun i ↦
            p.2.2 (Fin.cast ((hr p.2.proj.1).trans (congrArg r p.2.proj.2)) i)⟩ :
              TotalSpace Unit A.Fiber)) :=
        continuous_sigma fun a ↦ A.continuous_pullCoreLift
          ⟨Subtype.val, continuous_subtype_val⟩ (r a) _
      exact (hsigma.comp (clopenTotalSpaceHomeomorph c _).symm.continuous).congr fun p ↦ by
        rcases p with ⟨x, v⟩
        dsimp only [Function.comp_apply]
        rw [clopenTotalSpaceHomeomorph_symm_apply]
        rfl)
    (by
      rw [continuous_mk_iff_clopenCores c A.continuous_proj]
      intro a
      refine A.continuous_into_pullCore ⟨Subtype.val, continuous_subtype_val⟩ (r a)
        (fun x ↦ (hr x.1).trans (congrArg r x.2))
        ((A.continuous_proj.comp continuous_subtype_val).subtype_mk _) ?_
      refine continuous_subtype_val.congr fun q ↦ ?_
      rcases q with ⟨⟨x, v⟩, hx⟩
      dsimp only [finCongrLE, LinearEquiv.coe_symm_mk] at hx ⊢
      exact congrArg (TotalSpace.mk' (E := A.Fiber) Unit x)
        (funext fun i ↦ congrArg v (Fin.ext rfl)))

@[simp]
theorem fiberMap_clopenPullIso_hom (A : FiniteRankAtlas 𝕜 X) (r : α → ℕ)
    (hr : ∀ x, A.rank x = r (c x)) (x : X)
    (v : (ofClopenCores c (A.clopenPullCore c r hr)).Fiber x) :
    (A.clopenPullIso c r hr).hom.fiberMap x v = fun i ↦ v (Fin.cast (hr x) i) := by
  simp [clopenPullIso, finCongrLE]

@[simp]
theorem fiberMap_clopenPullIso_inv (A : FiniteRankAtlas 𝕜 X) (r : α → ℕ)
    (hr : ∀ x, A.rank x = r (c x)) (x : X) (v : A.Fiber x) :
    (A.clopenPullIso c r hr).inv.fiberMap x v = fun i ↦ v (Fin.cast (hr x).symm i) := by
  simp [clopenPullIso, finCongrLE]
  rfl

end ClopenRefinement

section CompleteField

variable [CompleteSpace 𝕜]

/-- Extract the constituent constant-rank coordinate morphisms on each clopen fibre from a morphism
between clopen-glued atlases. -/
noncomputable def unmapClopenCores
    {C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    (g : ofClopenCores c C ⟶ ofClopenCores c D) (a : α) : C a ⟶ D a :=
  let ϕ (x : {x : X // c x = a}) : (Fin (C a).rank → 𝕜) →L[𝕜] (Fin (D a).rank → 𝕜) :=
    (finCongrCLE (𝕜 := 𝕜) (congrArg (fun b ↦ (D b).rank) x.2)).toContinuousLinearMap.comp
      ((g.fiberMap x.1).toContinuousLinearMap.comp
        (finCongrCLE (𝕜 := 𝕜) (congrArg (fun b ↦ (C b).rank) x.2)).symm.toContinuousLinearMap)
  CoordinateHom.ofContinuous ϕ <|
    (continuous_hom_bundle_iff (E₁ := (C a).core.Fiber) (E₂ := (D a).core.Fiber) ϕ).2 <| by
      have htot : Continuous (fun p : (C a).core.TotalSpace ↦
          (⟨p.proj.1, g.fiberMap p.proj.1
            (fun i ↦ p.2 (Fin.cast (congrArg (fun b ↦ (C b).rank) p.proj.2) i))⟩ :
              TotalSpace Unit (ofClopenCores c D).Fiber)) := by
        refine (g.totalSpaceMap.continuous.comp
          ((clopenTotalSpaceHomeomorph c C).continuous.comp continuous_sigmaMk)).congr fun p ↦ ?_
        rcases p with ⟨⟨x, hx⟩, v⟩
        subst hx
        dsimp only [Function.comp_apply]
        rw [clopenTotalSpaceHomeomorph_apply, Hom.totalSpaceMap_mk]
      have hsub := (continuous_mk_iff_clopenCores c
        (continuous_subtype_val.comp (C a).core.continuous_proj) D
        (fun p : (C a).core.TotalSpace ↦ g.fiberMap p.proj.1
          (fun i ↦ p.2 (Fin.cast (congrArg (fun b ↦ (C b).rank) p.proj.2) i)))).1 htot a
      refine (hsub.comp (continuous_id.subtype_mk fun p ↦ p.proj.2)).congr fun p ↦ ?_
      rcases p with ⟨⟨x, hx⟩, v⟩
      subst hx
      simp only [Function.comp_apply, ϕ, finCongrCLE_rfl]
      rfl

private theorem fiberMap_unmapClopenCores
    {C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    (g : ofClopenCores c C ⟶ ofClopenCores c D) (a : α) (x : {x : X // c x = a}) :
    (unmapClopenCores c g a).fiberMap x =
      (finCongrCLE (𝕜 := 𝕜) (congrArg (fun b ↦ (D b).rank) x.2)).toContinuousLinearMap.comp
        ((g.fiberMap x.1).toContinuousLinearMap.comp
          (finCongrCLE (𝕜 := 𝕜) (congrArg (fun b ↦ (C b).rank) x.2)).symm.toContinuousLinearMap) :=
  congrFun (CoordinateHom.fiberMap_ofContinuous _ _) x

@[simp]
theorem fiberMap_unmapClopenCores_apply
    {C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    (g : ofClopenCores c C ⟶ ofClopenCores c D) (a : α) (x : {x : X // c x = a})
    (v : Fin (C a).rank → 𝕜) (i : Fin (D a).rank) :
    (unmapClopenCores c g a).fiberMap x v i =
      g.fiberMap x.1 (fun j ↦ v (Fin.cast (congrArg (fun b ↦ (C b).rank) x.2) j))
        (Fin.cast (congrArg (fun b ↦ (D b).rank) x.2).symm i) := by
  rw [fiberMap_unmapClopenCores]
  rfl

@[simp]
theorem mapClopenCores_unmapClopenCores
    {C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    (g : ofClopenCores c C ⟶ ofClopenCores c D) :
    mapClopenCores c (unmapClopenCores c g) = g := by
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro v
  rw [fiberMap_mapClopenCores, fiberMap_unmapClopenCores, finCongrCLE_rfl, finCongrCLE_rfl]
  rfl

@[simp]
theorem unmapClopenCores_mapClopenCores
    {C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    (f : ∀ a : α, C a ⟶ D a) :
    unmapClopenCores c (mapClopenCores c f) = f :=
  mapClopenCores_injective c (mapClopenCores_unmapClopenCores c _)

/-- Over a complete scalar field, morphisms between clopen-glued atlases correspond additively to
families of compatible chart-matrix morphisms `CoordinateHom` on each clopen piece. -/
noncomputable def clopenHomAddEquiv
    (C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}) :
    (∀ a : α, C a ⟶ D a) ≃+ (ofClopenCores c C ⟶ ofClopenCores c D) where
  toFun := mapClopenCores c
  invFun := unmapClopenCores c
  left_inv := unmapClopenCores_mapClopenCores c
  right_inv := mapClopenCores_unmapClopenCores c
  map_add' := mapClopenCores_add c

@[simp]
theorem clopenHomAddEquiv_apply
    {C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    (f : ∀ a : α, C a ⟶ D a) :
    clopenHomAddEquiv c C D f = mapClopenCores c f :=
  (rfl)

@[simp]
theorem clopenHomAddEquiv_symm_apply
    {C D : ∀ a : α, FiniteRankBundleCore 𝕜 {x : X // c x = a}}
    (g : ofClopenCores c C ⟶ ofClopenCores c D) :
    (clopenHomAddEquiv c C D).symm g = unmapClopenCores c g :=
  (rfl)

end CompleteField

end ClopenGluing

/-! ### Constant-rank comparison functor -/

/-- Embed constant-rank point-indexed cores into variable-rank bundle atlases. -/
-- Expose the object map so fibre types of `(ofCore.obj B)` reduce to `Fin B.rank → 𝕜`.
@[expose, implicit_reducible]
noncomputable def ofCore : FiniteRankBundleCore 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj B := ofClopenCores (LocallyConstant.const X ())
    fun _ ↦ B.pullback ⟨Subtype.val, continuous_subtype_val⟩
  map f := mapClopenCores (LocallyConstant.const X ())
    fun _ ↦ FiniteRankBundleCore.pullbackMap f ⟨Subtype.val, continuous_subtype_val⟩
  map_id B := by
    simp only [FiniteRankBundleCore.pullbackMap_id, mapClopenCores_id]
  map_comp f g := by
    simp only [FiniteRankBundleCore.pullbackMap_comp, mapClopenCores_comp]

@[simp]
theorem rank_ofCore_obj (B : FiniteRankBundleCore 𝕜 X) :
    (ofCore.obj B).rank = LocallyConstant.const X B.rank :=
  LocallyConstant.ext fun _ ↦ rfl

@[simp]
theorem fiberMap_ofCore_map {B B' : FiniteRankBundleCore 𝕜 X} (f : B ⟶ B') (x : X) :
    (ofCore.map f).fiberMap x = (f.fiberMap x).toLinearMap := by
  dsimp only [ofCore]
  rw [fiberMap_mapClopenCores, FiniteRankBundleCore.fiberMap_pullbackMap]
  rfl

instance : (ofCore (𝕜 := 𝕜) (X := X)).Additive where
  map_add {_ _ f g} := by
    apply hom_ext
    intro x
    apply LinearMap.ext
    intro v
    simp

instance : (ofCore (𝕜 := 𝕜) (X := X)).Faithful where
  map_injective {B B' f g} h := by
    apply FiniteRankBundleCore.hom_ext
    intro x
    ext v i
    have hx := congrArg (fun k : ofCore.obj B ⟶ ofCore.obj B' ↦ k.fiberMap x v i) h
    simpa only [fiberMap_ofCore_map, ContinuousLinearMap.coe_coe] using hx

/-- The reconstructed total space of `ofCore.obj B` is homeomorphic over `X` to the total space of
`B.core`, acting as the identity on both base points and coordinate vectors. -/
noncomputable def ofCoreTotalSpaceHomeomorph (B : FiniteRankBundleCore 𝕜 X) :
    B.core.TotalSpace ≃ₜ TotalSpace Unit (ofCore.obj B).Fiber where
  toFun p := ⟨p.proj, p.2⟩
  invFun q := ⟨q.proj, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    let sub : C({x : X // LocallyConstant.const X () x = ()}, X) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    apply (continuous_mk_iff_clopenCores (LocallyConstant.const X ()) B.core.continuous_proj
      (fun _ : Unit ↦ B.pullback sub) (fun p ↦ p.2)).2
    rintro ⟨⟩
    apply (B.pullbackHomeomorph sub).isInducing.continuous_iff.2
    dsimp only [Function.comp_def]
    simp only [FiniteRankBundleCore.pullbackHomeomorph_apply]
    rw [Bundle.Pullback.continuous_iff]
    refine ⟨(B.core.continuous_proj.comp continuous_subtype_val).subtype_mk _, ?_⟩
    exact continuous_subtype_val.congr fun _ ↦ rfl
  continuous_invFun := by
    let sub : C({x : X // LocallyConstant.const X () x = ()}, X) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    have hsigma : Continuous (fun r : Σ _ : Unit, (B.pullback sub).core.TotalSpace ↦
        (⟨r.2.proj.1, r.2.2⟩ : B.core.TotalSpace)) :=
      continuous_sigma fun _ ↦
        ((Pullback.continuous_lift (Fin B.rank → 𝕜) B.core.Fiber sub).comp
          (B.pullbackHomeomorph sub).continuous).congr fun p ↦ by
            rcases p with ⟨x, v⟩
            rw [Function.comp_apply, FiniteRankBundleCore.pullbackHomeomorph_apply,
              Pullback.lift_mk (E := B.core.Fiber) (F := Fin B.rank → 𝕜) (⇑sub) x v]
            rfl
    exact (hsigma.comp
      (clopenTotalSpaceHomeomorph (LocallyConstant.const X ()) _).symm.continuous).congr
        fun q ↦ by
          rcases q with ⟨x, v⟩
          rw [Function.comp_apply, clopenTotalSpaceHomeomorph_symm_apply]

@[simp]
theorem ofCoreTotalSpaceHomeomorph_apply (B : FiniteRankBundleCore 𝕜 X)
    (p : B.core.TotalSpace) :
    ofCoreTotalSpaceHomeomorph B p = ⟨p.proj, p.2⟩ :=
  (rfl)

@[simp]
theorem ofCoreTotalSpaceHomeomorph_symm_apply (B : FiniteRankBundleCore 𝕜 X)
    (q : TotalSpace Unit (ofCore.obj B).Fiber) :
    (ofCoreTotalSpaceHomeomorph B).symm q = ⟨q.proj, q.2⟩ :=
  (rfl)

/-- Over a complete scalar field, the embedding of constant-rank cores into variable-rank bundle
atlases is full: every continuous fibrewise linear map comes from compatible chart operators. -/
instance [CompleteSpace 𝕜] : (ofCore (𝕜 := 𝕜) (X := X)).Full where
  map_surjective {B B'} g := by
    let ϕ (x : X) : (Fin B.rank → 𝕜) →L[𝕜] (Fin B'.rank → 𝕜) :=
      (g.fiberMap x).toContinuousLinearMap
    have hcont : Continuous (fun p : B.core.TotalSpace ↦
        (⟨p.proj, ϕ p.proj p.2⟩ : B'.core.TotalSpace)) :=
      ((ofCoreTotalSpaceHomeomorph B').symm.continuous.comp
        (g.totalSpaceMap.continuous.comp (ofCoreTotalSpaceHomeomorph B).continuous)).congr
          fun p ↦ by
            rcases p with ⟨x, v⟩
            let v' : (ofCore.obj B).Fiber x := v
            -- Normalize `v` to `(ofCore.obj B).Fiber x` before rewriting `Hom.totalSpaceMap_mk`.
            change (ofCoreTotalSpaceHomeomorph B').symm (g.totalSpaceMap ⟨x, v'⟩) = ⟨x, ϕ x v'⟩
            rw [Hom.totalSpaceMap_mk, ofCoreTotalSpaceHomeomorph_symm_apply]
            rfl
    refine ⟨CoordinateHom.ofContinuous ϕ
      ((continuous_hom_bundle_iff (E₁ := B.core.Fiber) (E₂ := B'.core.Fiber) ϕ).2 hcont), ?_⟩
    apply hom_ext
    intro x
    apply LinearMap.ext
    intro v
    rw [fiberMap_ofCore_map, CoordinateHom.fiberMap_ofContinuous]
    rfl

/-- Extracting the constant-rank core from `ofCore.obj B` recovers `B` strictly. -/
@[simp]
theorem toCore_ofCore_obj (B : FiniteRankBundleCore 𝕜 X) :
    (ofCore.obj B).toCore B.rank (fun _ ↦ rfl) = B := by
  refine core_mk_eq_mk (vectorBundleCore_eq ?_ (funext fun x ↦ (B.indexAt_eq x).symm) ?_)
  · funext i
    ext x
    exact ⟨fun ⟨_, hm⟩ ↦ hm, fun hm ↦ ⟨rfl, hm⟩⟩
  · funext i j x
    -- Unfold `toCore` and `pullCore` to `pullback` without unfolding `ContinuousMap.id`.
    change (((ofCore.obj B).stratumCore B.rank).pullback _).core.coordChange i j x =
      B.core.coordChange i j x
    rw [FiniteRankBundleCore.coordChange_pullback, core_stratumCore]
    dsimp only [ofCore]
    rw [charts_ofClopenCores, clopenStratumCharts_coordChange,
      clopenCoordChange_eq_of_eq (LocallyConstant.const X ()) _ (a := ())
        (B.rank_pullback _) rfl rfl rfl,
      finCongrCLE_rfl]
    ext v k
    rfl

/-- Every atlas of constant rank `n` is canonically isomorphic to the image of `A.toCore n h`
under `ofCore`. -/
noncomputable def ofCoreToCoreIso (A : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (h : ∀ x, A.rank x = n) : ofCore.obj (A.toCore n h) ≅ A :=
  isoMk (fun x ↦ finCongrLE (𝕜 := 𝕜) (h x).symm)
    (((A.continuous_pullCoreLift (ContinuousMap.id X) n h).comp
      (ofCoreTotalSpaceHomeomorph (A.toCore n h)).symm.continuous).congr fun p ↦ by
        rcases p with ⟨x, v⟩
        rw [Function.comp_apply, ofCoreTotalSpaceHomeomorph_symm_apply]
        rfl)
    (by
      have hin : Continuous (fun z : TotalSpace Unit A.Fiber ↦
          (⟨z.proj, fun i ↦ z.2 (Fin.cast (h z.proj).symm i)⟩ :
            (A.toCore n h).core.TotalSpace)) := by
        refine A.continuous_into_pullCore (ContinuousMap.id X) n h A.continuous_proj ?_
        refine continuous_id.congr fun q ↦ ?_
        rcases q with ⟨x, v⟩
        exact congrArg (TotalSpace.mk' (E := A.Fiber) Unit x)
          (funext fun i ↦ congrArg v (Fin.ext rfl))
      refine ((ofCoreTotalSpaceHomeomorph (A.toCore n h)).continuous.comp hin).congr fun q ↦ ?_
      rcases q with ⟨x, v⟩
      rw [Function.comp_apply, ofCoreTotalSpaceHomeomorph_apply]
      rfl)

@[simp]
theorem fiberMap_ofCoreToCoreIso_hom (A : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (h : ∀ x, A.rank x = n) (x : X) (v : (ofCore.obj (A.toCore n h)).Fiber x) :
    (A.ofCoreToCoreIso n h).hom.fiberMap x v = fun i ↦ v (Fin.cast (h x) i) := by
  simp [ofCoreToCoreIso, finCongrLE]

@[simp]
theorem fiberMap_ofCoreToCoreIso_inv (A : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (h : ∀ x, A.rank x = n) (x : X) (v : A.Fiber x) :
    (A.ofCoreToCoreIso n h).inv.fiberMap x v = fun i ↦ v (Fin.cast (h x).symm i) := by
  simp [ofCoreToCoreIso, finCongrLE]
  rfl

/-! ### Compatible matrix morphisms on joint rank bi-strata and isomorphisms -/

/-- Assemble compatible chart-matrix morphisms on each joint rank bi-stratum
`{x : X // (A.rank x, D.rank x) = p}` into a variable-rank morphism `A ⟶ D`. -/
noncomputable def ofBistratumHoms (A D : FiniteRankAtlas 𝕜 X)
    (f : ∀ p : ℕ × ℕ,
      A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p ⟶
        D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p) :
    A ⟶ D :=
  (A.clopenPullIso (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl)).inv ≫
    mapClopenCores (A.rank.prodMk D.rank) f ≫
    (D.clopenPullIso (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl)).hom

@[simp]
theorem fiberMap_ofBistratumHoms (A D : FiniteRankAtlas 𝕜 X)
    (f : ∀ p : ℕ × ℕ,
      A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p ⟶
        D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p)
    (x : X) :
    (ofBistratumHoms A D f).fiberMap x =
      ((f (A.rank x, D.rank x)).fiberMap ⟨x, rfl⟩).toLinearMap := by
  apply LinearMap.ext
  intro v
  dsimp only [ofBistratumHoms, LocallyConstant.prodMk_apply]
  simp
  rfl

/-- Extract the compatible chart-matrix morphisms on each joint rank bi-stratum from a variable-rank
morphism `g : A ⟶ D`. -/
noncomputable def toBistratumHoms [CompleteSpace 𝕜] {A D : FiniteRankAtlas 𝕜 X}
    (g : A ⟶ D) :
    ∀ p : ℕ × ℕ,
      A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p ⟶
        D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p :=
  unmapClopenCores (A.rank.prodMk D.rank)
    ((A.clopenPullIso (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl)).hom ≫ g ≫
      (D.clopenPullIso (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl)).inv)

@[simp]
theorem ofBistratumHoms_toBistratumHoms [CompleteSpace 𝕜] {A D : FiniteRankAtlas 𝕜 X}
    (g : A ⟶ D) :
    ofBistratumHoms A D (toBistratumHoms g) = g := by
  simp [ofBistratumHoms, toBistratumHoms]

@[simp]
theorem toBistratumHoms_ofBistratumHoms [CompleteSpace 𝕜] (A D : FiniteRankAtlas 𝕜 X)
    (f : ∀ p : ℕ × ℕ,
      A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p ⟶
        D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p) :
    toBistratumHoms (ofBistratumHoms A D f) = f := by
  simp [ofBistratumHoms, toBistratumHoms]

/-- Over a complete scalar field, variable-rank bundle morphisms `A ⟶ D` correspond additively to
families of compatible finite-matrix `CoordinateHom`s on the joint clopen rank bi-strata. -/
noncomputable def bistratumHomAddEquiv [CompleteSpace 𝕜] (A D : FiniteRankAtlas 𝕜 X) :
    (∀ p : ℕ × ℕ,
      A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p ⟶
        D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p) ≃+
      (A ⟶ D) where
  toFun := ofBistratumHoms A D
  invFun := toBistratumHoms
  left_inv := toBistratumHoms_ofBistratumHoms A D
  right_inv := ofBistratumHoms_toBistratumHoms
  map_add' f g := by
    rw [Pi.add_def]
    simp only [ofBistratumHoms, mapClopenCores_add, Preadditive.add_comp, Preadditive.comp_add]

@[simp]
theorem bistratumHomAddEquiv_apply [CompleteSpace 𝕜] (A D : FiniteRankAtlas 𝕜 X)
    (f : ∀ p : ℕ × ℕ,
      A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p ⟶
        D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p) :
    bistratumHomAddEquiv A D f = ofBistratumHoms A D f :=
  (rfl)

@[simp]
theorem bistratumHomAddEquiv_symm_apply [CompleteSpace 𝕜] (A D : FiniteRankAtlas 𝕜 X)
    (g : A ⟶ D) :
    (bistratumHomAddEquiv A D).symm g = toBistratumHoms g :=
  (rfl)

/-- Every categorical isomorphism of bundle atlases is bijective on each fibre. -/
theorem bijective_fiberMap_of_isIso {A D : FiniteRankAtlas 𝕜 X} (f : A ⟶ D) [IsIso f]
    (x : X) : Function.Bijective (f.fiberMap x) := by
  refine ⟨Function.HasLeftInverse.injective ⟨(inv f).fiberMap x, fun v ↦ ?_⟩,
    Function.HasRightInverse.surjective ⟨(inv f).fiberMap x, fun v ↦ ?_⟩⟩
  · have h := congrArg (fun k : A ⟶ A ↦ k.fiberMap x v) (IsIso.hom_inv_id f)
    simpa only [fiberMap_comp, fiberMap_id, LinearMap.comp_apply, LinearMap.id_apply] using h
  · have h := congrArg (fun k : D ⟶ D ↦ k.fiberMap x v) (IsIso.inv_hom_id f)
    simpa only [fiberMap_comp, fiberMap_id, LinearMap.comp_apply, LinearMap.id_apply] using h

/-- Over a complete scalar field, a morphism of variable-rank bundle atlases is an isomorphism
if and only if it is bijective on every fibre. -/
theorem isIso_iff_bijective [CompleteSpace 𝕜] {A D : FiniteRankAtlas 𝕜 X} (f : A ⟶ D) :
    IsIso f ↔ ∀ x, Function.Bijective (f.fiberMap x) := by
  refine ⟨fun _ ↦ bijective_fiberMap_of_isIso f, fun hf ↦ ?_⟩
  have hr : ∀ x, D.rank x = A.rank x := fun x ↦ by
    have hlin := LinearEquiv.ofBijective (f.fiberMap x) (hf x)
    simpa only [Module.finrank_fin_fun] using hlin.finrank_eq.symm
  let eA := A.clopenPullIso A.rank id (fun _ ↦ rfl)
  let eD := D.clopenPullIso A.rank id hr
  let f' := eA.hom ≫ f ≫ eD.inv
  have hf' : ∀ n : ℕ, IsIso (unmapClopenCores A.rank f' n) := fun n ↦ by
    rw [FiniteRankBundleCore.isIso_iff_bijective]
    intro x
    rw [fiberMap_unmapClopenCores, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
    refine (finCongrCLE (𝕜 := 𝕜) (congrArg id x.2)).bijective.comp
      (Function.Bijective.comp ?_ (finCongrCLE (𝕜 := 𝕜) (congrArg id x.2)).symm.bijective)
    rw [LinearMap.coe_toContinuousLinearMap']
    dsimp only [f']
    rw [fiberMap_comp, fiberMap_comp, LinearMap.coe_comp, LinearMap.coe_comp]
    exact (bijective_fiberMap_of_isIso eD.inv x.1).comp
      ((hf x.1).comp (bijective_fiberMap_of_isIso eA.hom x.1))
  let gIso : ofClopenCores A.rank (A.clopenPullCore A.rank id (fun _ ↦ rfl)) ≅
      ofClopenCores A.rank (D.clopenPullCore A.rank id hr) :=
    isoClopenCores A.rank fun n ↦ asIso (unmapClopenCores A.rank f' n)
  have hf'_eq : f' = gIso.hom := by
    simp only [gIso, isoClopenCores_hom, asIso_hom, mapClopenCores_unmapClopenCores]
  have hf_eq : f = eA.inv ≫ gIso.hom ≫ eD.hom := by
    simp only [← hf'_eq, f', Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  rw [hf_eq]
  infer_instance

end TauCeti.FiniteRankAtlas
