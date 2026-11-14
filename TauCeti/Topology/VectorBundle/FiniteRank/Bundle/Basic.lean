/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Section
public import TauCeti.Topology.VectorBundle.ULift
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Topology.Algebra.Module.TransferInstance
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.VectorBundle.Constructions

import TauCeti.Topology.VectorBundle.Smul

/-!
# Variable-rank finite-rank topological vector bundles

`TauCeti.FiniteRankVectorBundle 𝕜 X` is the genuine category of variable-rank finite-rank
topological `𝕜`-vector bundles over a topological space `X`, with fibres in an arbitrary universe
`Type w`. An object consists of a locally constant rank `rank : LocallyConstant X ℕ`, a family of
`𝕜`-modules `Fiber : X → Type w` carrying topologies, and on each clopen rank stratum
`{x : X // rank x = n}` a native Mathlib `VectorBundle 𝕜 (Fin n → 𝕜)` structure on the restricted
fibre family. Neither globally bounded rank, finite trivializing covers, compactness, nor
separation assumptions on `X` are required, and rank `0` as well as empty or disconnected bases are
covered uniformly.

From the preferred linear chart at each point we derive `IsTopologicalAddGroup`, `ContinuousSMul`,
and `Module.Finite` instances on every fibre together with `finrank_fiber`. Gluing the stratum
total spaces gives the native bundle topology on `TotalSpace Unit V.Fiber`
(`totalSpaceHomeomorph`), characterized by `continuous_mk_iff_rankStrata`. Continuous fibrewise
`𝕜`-linear maps form a `Preadditive` category with faithful `totalSpaceFunctor` and additive
evaluation functors `fiberFunctor x`. Constant-rank Mathlib vector bundles embed via `ofFixedRank`
(including `trivial 𝕜 X n`), and `exists_iso_ofFixedRank_iff` identifies their essential image as
the bundles of globally constant rank.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory Topology

namespace TauCeti

universe u v w

/-- A variable-rank finite-rank topological `𝕜`-vector bundle over `X` with fibres in `Type w`.
On each clopen stratum where `rank` takes value `n`, the restricted fibre family is a Mathlib
topological vector bundle with model fibre `Fin n → 𝕜`. -/
structure FiniteRankVectorBundle (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    (X : Type u) [TopologicalSpace X] where
  /-- The locally constant, not necessarily bounded, rank function. -/
  rank : LocallyConstant X ℕ
  /-- The fibre over each point of `X`, in an arbitrary universe `Type w`. -/
  Fiber : X → Type w
  [addCommGroupFiber : ∀ x, AddCommGroup (Fiber x)]
  [moduleFiber : ∀ x, Module 𝕜 (Fiber x)]
  [topologicalSpaceFiber : ∀ x, TopologicalSpace (Fiber x)]
  [topologicalSpaceStratumTotalSpace :
    ∀ n : ℕ, TopologicalSpace (TotalSpace (Fin n → 𝕜) (fun x : {x : X // rank x = n} ↦ Fiber x.1))]
  [fiberBundleStratum :
    ∀ n : ℕ, FiberBundle (Fin n → 𝕜) (fun x : {x : X // rank x = n} ↦ Fiber x.1)]
  [vectorBundleStratum :
    ∀ n : ℕ, VectorBundle 𝕜 (Fin n → 𝕜) (fun x : {x : X // rank x = n} ↦ Fiber x.1)]

attribute [instance]
  FiniteRankVectorBundle.addCommGroupFiber
  FiniteRankVectorBundle.moduleFiber
  FiniteRankVectorBundle.topologicalSpaceFiber
  FiniteRankVectorBundle.topologicalSpaceStratumTotalSpace
  FiniteRankVectorBundle.fiberBundleStratum
  FiniteRankVectorBundle.vectorBundleStratum

namespace FiniteRankVectorBundle

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X] (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)

/-- The fibre family restricted to the `n`th clopen rank stratum `{x : X // V.rank x = n}`. -/
abbrev StratumFiber (n : ℕ) : {x : X // V.rank x = n} → Type w :=
  fun x ↦ V.Fiber x.1

/-- The continuous linear equivalence from `V.Fiber x` to `Fin (V.rank x) → 𝕜` read in the
preferred stratum trivialization at `x`. -/
noncomputable def preferredChartEquiv (x : X) : V.Fiber x ≃L[𝕜] (Fin (V.rank x) → 𝕜) :=
  let e := trivializationAt (Fin (V.rank x) → 𝕜) (V.StratumFiber (V.rank x)) ⟨x, rfl⟩
  e.continuousLinearEquivAt 𝕜 ⟨x, rfl⟩ (mem_baseSet_trivializationAt _ _ _)

instance (x : X) : IsTopologicalAddGroup (V.Fiber x) :=
  (V.preferredChartEquiv x).toContinuousAddEquiv.isTopologicalAddGroup

instance (x : X) : ContinuousSMul 𝕜 (V.Fiber x) :=
  (V.preferredChartEquiv x).continuousSMul

instance (x : X) : Module.Finite 𝕜 (V.Fiber x) :=
  Module.Finite.of_surjective (V.preferredChartEquiv x).symm.toLinearMap
    (V.preferredChartEquiv x).symm.surjective

@[simp]
theorem finrank_fiber (x : X) : Module.finrank 𝕜 (V.Fiber x) = V.rank x :=
  (V.preferredChartEquiv x).toLinearEquiv.finrank_eq.trans (Module.finrank_fin_fun 𝕜)

/-- The disjoint union of the native stratum total spaces. -/
abbrev GluedTotalSpace := Σ n : ℕ, TotalSpace (Fin n → 𝕜) (V.StratumFiber n)

/-- Projection of the disjoint union of stratum total spaces to `X`. -/
def gluedProj (p : V.GluedTotalSpace) : X := p.2.proj.1

@[simp]
theorem gluedProj_mk (n : ℕ) (p : TotalSpace (Fin n → 𝕜) (V.StratumFiber n)) :
    V.gluedProj ⟨n, p⟩ = p.proj.1 := (rfl)

@[continuity, fun_prop]
theorem continuous_gluedProj : Continuous V.gluedProj :=
  continuous_sigma fun n ↦
    continuous_subtype_val.comp (FiberBundle.continuous_proj (Fin n → 𝕜) (V.StratumFiber n))

theorem isOpenMap_gluedProj : IsOpenMap V.gluedProj := by
  refine isOpenMap_sigma.2 fun n ↦ ?_
  exact ((V.rank.isLocallyConstant.isOpen_fiber n).isOpenEmbedding_subtypeVal.isOpenMap).comp
    (FiberBundle.isOpenMap_proj (Fin n → 𝕜) (V.StratumFiber n))

private def totalSpaceEquiv : V.GluedTotalSpace ≃ TotalSpace Unit V.Fiber where
  toFun p := ⟨p.2.proj.1, p.2.2⟩
  invFun p := ⟨V.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩
  left_inv p := by
    rcases p with ⟨n, ⟨⟨x, hx⟩, v⟩⟩
    cases hx
    rfl
  right_inv p := by
    cases p
    rfl

/-- Equip `TotalSpace Unit V.Fiber` with the disjoint-union topology of the stratum bundles. -/
instance : TopologicalSpace (TotalSpace Unit V.Fiber) :=
  TopologicalSpace.induced
    (fun p : TotalSpace Unit V.Fiber ↦
      (⟨V.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩ : V.GluedTotalSpace))
    inferInstance

/-- Reindexing the disjoint union of the stratum total spaces gives the total-space topology of `V`
over `X`. -/
def totalSpaceHomeomorph : V.GluedTotalSpace ≃ₜ TotalSpace Unit V.Fiber :=
  (V.totalSpaceEquiv.symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm

@[simp]
theorem totalSpaceHomeomorph_apply (p : V.GluedTotalSpace) :
    V.totalSpaceHomeomorph p = ⟨p.2.proj.1, p.2.2⟩ := (rfl)

@[simp]
theorem totalSpaceHomeomorph_symm_apply (p : TotalSpace Unit V.Fiber) :
    V.totalSpaceHomeomorph.symm p = ⟨V.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩ := (rfl)

@[continuity, fun_prop]
theorem continuous_proj : Continuous (TotalSpace.proj : TotalSpace Unit V.Fiber → X) :=
  V.continuous_gluedProj.comp V.totalSpaceHomeomorph.symm.continuous

theorem isOpenMap_proj : IsOpenMap (TotalSpace.proj : TotalSpace Unit V.Fiber → X) :=
  V.isOpenMap_gluedProj.comp V.totalSpaceHomeomorph.symm.isOpenMap

/-- Each stratum total space embeds openly into `TotalSpace Unit V.Fiber`. -/
theorem isOpenEmbedding_stratum (n : ℕ) :
    IsOpenEmbedding
      (fun p : TotalSpace (Fin n → 𝕜) (V.StratumFiber n) ↦ V.totalSpaceHomeomorph ⟨n, p⟩) :=
  V.totalSpaceHomeomorph.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk

/-- The image of the `n`th stratum total space is the rank-`n` part of `TotalSpace Unit V.Fiber`. -/
theorem range_stratum (n : ℕ) :
    Set.range
        (fun p : TotalSpace (Fin n → 𝕜) (V.StratumFiber n) ↦ V.totalSpaceHomeomorph ⟨n, p⟩) =
      {p : TotalSpace Unit V.Fiber | V.rank p.proj = n} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.proj.2
  · intro hp
    cases p with
    | mk x v =>
      cases hp
      exact ⟨⟨⟨x, rfl⟩, v⟩, rfl⟩

section Continuity

variable {Y : Type*} [TopologicalSpace Y] {b : Y → X}

/-- A map into `TotalSpace Unit V.Fiber` is continuous if and only if its restriction to each rank
stratum is continuous into that stratum's native bundle total space. -/
theorem continuous_mk_iff_rankStrata (hb : Continuous b) (s : ∀ y, V.Fiber (b y)) :
    Continuous (fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit V.Fiber)) ↔
      ∀ n : ℕ, Continuous (fun y : {y : Y // V.rank (b y) = n} ↦
        (⟨⟨b y, y.2⟩, s y⟩ : TotalSpace (Fin n → 𝕜) (V.StratumFiber n))) := by
  constructor
  · intro hs n
    refine (IsEmbedding.sigmaMk
      (σ := fun n ↦ TotalSpace (Fin n → 𝕜) (V.StratumFiber n))).continuous_iff.2 ?_
    exact (V.totalSpaceHomeomorph.symm.continuous.comp (hs.comp continuous_subtype_val)).congr
      fun ⟨y, hy⟩ ↦ by cases hy; rfl
  · intro hs
    refine continuous_of_cover_nhds (s := fun n : ℕ ↦ {y : Y | V.rank (b y) = n}) ?_ ?_
    · intro y
      exact ⟨V.rank (b y), ((V.rank.isLocallyConstant.isOpen_fiber _).preimage hb).mem_nhds rfl⟩
    · intro n
      rw [continuousOn_iff_continuous_domRestrict]
      exact (V.totalSpaceHomeomorph.continuous.comp (continuous_sigmaMk.comp (hs n))).congr
        fun _ ↦ rfl

@[fun_prop]
theorem continuous_zeroSection :
    Continuous (fun x ↦ (⟨x, 0⟩ : TotalSpace Unit V.Fiber)) := by
  refine (V.continuous_mk_iff_rankStrata continuous_id _).2 fun n ↦ ?_
  exact (Bundle.Trivialization.continuous_zeroSection 𝕜
    (F := Fin n → 𝕜) (E := V.StratumFiber n)).congr fun _ ↦ rfl

theorem continuous_add {s t : ∀ y, V.Fiber (b y)}
    (hs : Continuous (fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit V.Fiber)))
    (ht : Continuous (fun y ↦ (⟨b y, t y⟩ : TotalSpace Unit V.Fiber))) :
    Continuous (fun y ↦ (⟨b y, s y + t y⟩ : TotalSpace Unit V.Fiber)) := by
  have hb : Continuous b := V.continuous_proj.comp hs
  rw [V.continuous_mk_iff_rankStrata hb] at hs ht ⊢
  intro n
  exact (hs n).add_totalSpace 𝕜 (ht n)

theorem continuous_smul {s : ∀ y, V.Fiber (b y)} {c : Y → 𝕜}
    (hc : Continuous c)
    (hs : Continuous (fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit V.Fiber))) :
    Continuous (fun y ↦ (⟨b y, c y • s y⟩ : TotalSpace Unit V.Fiber)) := by
  have hb : Continuous b := V.continuous_proj.comp hs
  rw [V.continuous_mk_iff_rankStrata hb] at hs ⊢
  intro n
  exact (hc.comp continuous_subtype_val).smul_totalSpace (hs n)

end Continuity

section FixedRank

/-- View a constant-rank Mathlib `VectorBundle 𝕜 (Fin n → 𝕜) E` as a `FiniteRankVectorBundle 𝕜 X`,
covering `n = 0` and empty or disconnected bases uniformly. -/
-- Expose the rank and fibre projections so `(ofFixedRank 𝕜 n E).Fiber` reduces to `E`.
@[expose]
noncomputable def ofFixedRank (𝕜 : Type v) [NontriviallyNormedField 𝕜] (n : ℕ) (E : X → Type w)
    [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E] :
    FiniteRankVectorBundle.{u, v, w} 𝕜 X :=
  let data (m : ℕ) :
      Σ' (ts : TopologicalSpace (TotalSpace (Fin m → 𝕜)
          (fun y : {x : X // LocallyConstant.const X n x = m} ↦ E y.1))),
        Σ' (fb : @FiberBundle {x : X // LocallyConstant.const X n x = m} (Fin m → 𝕜) _ _
            (fun y ↦ E y.1) ts _),
          @VectorBundle 𝕜 {x : X // LocallyConstant.const X n x = m} (Fin m → 𝕜)
            (fun y ↦ E y.1) _ (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
            inferInstance inferInstance _ ts _ fb :=
    if h : n = m then
      h.rec (motive := fun k _ ↦
        Σ' (ts : TopologicalSpace (TotalSpace (Fin k → 𝕜)
            (fun y : {x : X // LocallyConstant.const X n x = m} ↦ E y.1))),
          Σ' (fb : @FiberBundle {x : X // LocallyConstant.const X n x = m} (Fin k → 𝕜) _ _
              (fun y ↦ E y.1) ts _),
            @VectorBundle 𝕜 {x : X // LocallyConstant.const X n x = m} (Fin k → 𝕜)
              (fun y ↦ E y.1) _ (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
              inferInstance inferInstance _ ts _ fb)
        (let inc : C({x : X // LocallyConstant.const X n x = m}, X) :=
          ⟨Subtype.val, continuous_subtype_val⟩
        ⟨Pullback.TotalSpace.topologicalSpace (Fin n → 𝕜) E ⇑inc,
         FiberBundle.pullback (F := Fin n → 𝕜) (E := E) inc,
         VectorBundle.pullback (𝕜 := 𝕜) (F := Fin n → 𝕜) (E := E) inc⟩)
    else
      let S := {x : X // LocallyConstant.const X n x = m}
      have hEmpty : IsEmpty S := ⟨fun y ↦ h y.2⟩
      ⟨⊥, @fiberBundleOfIsEmpty S _ hEmpty (Fin m → 𝕜) (fun y : S ↦ E y.1) ⊥ _ _,
       @vectorBundleOfIsEmpty S _ hEmpty (Fin m → 𝕜) (fun y : S ↦ E y.1) ⊥ _ 𝕜 _ _ _ _ _⟩
  { rank := LocallyConstant.const X n
    Fiber := E
    topologicalSpaceStratumTotalSpace m := (data m).1
    fiberBundleStratum m := (data m).2.1
    vectorBundleStratum m := (data m).2.2 }

@[simp]
theorem rank_ofFixedRank (𝕜 : Type v) [NontriviallyNormedField 𝕜] (n : ℕ) (E : X → Type w)
    [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E] :
    (ofFixedRank 𝕜 n E).rank = LocallyConstant.const X n := (rfl)

@[simp]
theorem fiber_ofFixedRank (𝕜 : Type v) [NontriviallyNormedField 𝕜] (n : ℕ) (E : X → Type w)
    [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E] :
    (ofFixedRank 𝕜 n E).Fiber = E := (rfl)

/-- The trivial variable-rank vector bundle `X × (Fin n → 𝕜)` of constant rank `n`. -/
noncomputable abbrev trivial (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    (X : Type u) [TopologicalSpace X] (n : ℕ) :
    FiniteRankVectorBundle.{u, v, v} 𝕜 X :=
  ofFixedRank 𝕜 n (Bundle.Trivial X (Fin n → 𝕜))

/-- The glued total space of `ofFixedRank 𝕜 n E` is homeomorphic over `X` to the native Mathlib
`TotalSpace (Fin n → 𝕜) E`. -/
noncomputable def ofFixedRankTotalSpaceHomeomorph (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    (n : ℕ) (E : X → Type w)
    [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E] :
    TotalSpace Unit (ofFixedRank 𝕜 n E).Fiber ≃ₜ TotalSpace (Fin n → 𝕜) E where
  toFun p := ⟨p.proj, p.2⟩
  invFun p := ⟨p.proj, p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  continuous_toFun := by
    rw [← (ofFixedRank 𝕜 n E).totalSpaceHomeomorph.comp_continuous_iff']
    refine continuous_sigma fun m ↦ ?_
    by_cases h : n = m
    · subst h
      have hts : (ofFixedRank 𝕜 n E).topologicalSpaceStratumTotalSpace n =
          Pullback.TotalSpace.topologicalSpace (Fin n → 𝕜) E
            (Subtype.val : {x : X // LocallyConstant.const X n x = n} → X) :=
        congrArg PSigma.fst (dite_eq_left_of_eq_true (eq_true rfl))
      have hpull : @Continuous _ _
          (Pullback.TotalSpace.topologicalSpace (Fin n → 𝕜) E
            (Subtype.val : {x : X // LocallyConstant.const X n x = n} → X)) _
          (fun q : TotalSpace (Fin n → 𝕜) ((ofFixedRank 𝕜 n E).StratumFiber n) ↦
            (⟨q.proj.1, q.2⟩ : TotalSpace (Fin n → 𝕜) E)) :=
        Pullback.continuous_lift (Fin n → 𝕜) E
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C({x : X // LocallyConstant.const X n x = n}, X))
      -- Make the `n`-stratum domain topology explicit before rewriting with `hts`.
      change @Continuous _ _ ((ofFixedRank 𝕜 n E).topologicalSpaceStratumTotalSpace n) _ _
      rw [hts]
      exact hpull
    · have : Subsingleton (TotalSpace (Fin m → 𝕜) ((ofFixedRank 𝕜 n E).StratumFiber m)) :=
        ⟨fun p _ ↦ False.elim (h p.proj.2)⟩
      have : DiscreteTopology (TotalSpace (Fin m → 𝕜) ((ofFixedRank 𝕜 n E).StratumFiber m)) :=
        Subsingleton.discreteTopology
      exact continuous_of_discreteTopology
  continuous_invFun := by
    refine ((ofFixedRank 𝕜 n E).continuous_mk_iff_rankStrata
      (FiberBundle.continuous_proj (Fin n → 𝕜) E) _).2 fun m ↦ ?_
    by_cases h : n = m
    · subst h
      have hts : (ofFixedRank 𝕜 n E).topologicalSpaceStratumTotalSpace n =
          Pullback.TotalSpace.topologicalSpace (Fin n → 𝕜) E
            (Subtype.val : {x : X // LocallyConstant.const X n x = n} → X) :=
        congrArg PSigma.fst (dite_eq_left_of_eq_true (eq_true rfl))
      let inc : C({x : X // LocallyConstant.const X n x = n}, X) :=
        ⟨Subtype.val, continuous_subtype_val⟩
      have hpull : @Continuous _ _ _ (Pullback.TotalSpace.topologicalSpace (Fin n → 𝕜) E ⇑inc)
          (fun p : {p : TotalSpace (Fin n → 𝕜) E // (ofFixedRank 𝕜 n E).rank p.proj = n} ↦
            (⟨⟨p.1.proj, p.2⟩, p.1.2⟩ : TotalSpace (Fin n → 𝕜) ((⇑inc) *ᵖ E))) := by
        rw [(inducing_pullbackTotalSpaceEmbedding (Fin n → 𝕜) E inc).continuous_iff]
        refine Continuous.prodMk ?_ continuous_subtype_val
        exact ((FiberBundle.continuous_proj (Fin n → 𝕜) E).comp
          continuous_subtype_val).subtype_mk _
      -- Make the `n`-stratum codomain topology explicit before rewriting with `hts`.
      change @Continuous _ _ _ ((ofFixedRank 𝕜 n E).topologicalSpaceStratumTotalSpace n) _
      rw [hts]
      exact hpull
    · have : Subsingleton {p : TotalSpace (Fin n → 𝕜) E // (ofFixedRank 𝕜 n E).rank p.proj = m} :=
        ⟨fun p _ ↦ False.elim (h p.2)⟩
      have : DiscreteTopology
          {p : TotalSpace (Fin n → 𝕜) E // (ofFixedRank 𝕜 n E).rank p.proj = m} :=
        Subsingleton.discreteTopology
      exact continuous_of_discreteTopology

@[simp]
theorem ofFixedRankTotalSpaceHomeomorph_apply (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    (n : ℕ) (E : X → Type w)
    [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E]
    (p : TotalSpace Unit (ofFixedRank 𝕜 n E).Fiber) :
    ofFixedRankTotalSpaceHomeomorph 𝕜 n E p = ⟨p.proj, p.2⟩ := (rfl)

@[simp]
theorem ofFixedRankTotalSpaceHomeomorph_symm_apply (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    (n : ℕ) (E : X → Type w)
    [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E]
    (p : TotalSpace (Fin n → 𝕜) E) :
    (ofFixedRankTotalSpaceHomeomorph 𝕜 n E).symm p = ⟨p.proj, p.2⟩ := (rfl)

end FixedRank

section Category

variable {V} {W U : FiniteRankVectorBundle.{u, v, w} 𝕜 X}

/-- A morphism of variable-rank vector bundles is a family of `𝕜`-linear maps on fibres whose
induced map on the glued total spaces is continuous. -/
@[ext]
structure Hom (V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X) where
  /-- The `𝕜`-linear map on the fibre over `x`. -/
  fiberMap (x : X) : V.Fiber x →ₗ[𝕜] W.Fiber x
  /-- Continuity of the induced map on total spaces in the glued bundle topologies. -/
  continuous_totalSpaceMap : Continuous (fun p : TotalSpace Unit V.Fiber ↦
    (⟨p.proj, fiberMap p.proj p.2⟩ : TotalSpace Unit W.Fiber))

namespace Hom

/-- The bundled continuous map of total spaces induced by a bundle morphism. -/
def totalSpaceMap (f : Hom V W) : C(TotalSpace Unit V.Fiber, TotalSpace Unit W.Fiber) :=
  ⟨_, f.continuous_totalSpaceMap⟩

@[simp]
theorem totalSpaceMap_mk (f : Hom V W) (x : X) (v : V.Fiber x) :
    f.totalSpaceMap ⟨x, v⟩ = ⟨x, f.fiberMap x v⟩ := (rfl)

@[simp]
theorem proj_totalSpaceMap (f : Hom V W) (p : TotalSpace Unit V.Fiber) :
    (f.totalSpaceMap p).proj = p.proj := (rfl)

end Hom

instance : Category (FiniteRankVectorBundle.{u, v, w} 𝕜 X) where
  Hom := Hom
  id _ :=
    { fiberMap _ := LinearMap.id
      continuous_totalSpaceMap := continuous_id }
  comp f g :=
    { fiberMap x := (g.fiberMap x).comp (f.fiberMap x)
      continuous_totalSpaceMap := g.continuous_totalSpaceMap.comp f.continuous_totalSpaceMap }
  id_comp _ := Hom.ext (funext fun _ ↦ LinearMap.ext fun _ ↦ rfl)
  comp_id _ := Hom.ext (funext fun _ ↦ LinearMap.ext fun _ ↦ rfl)
  assoc _ _ _ := Hom.ext (funext fun _ ↦ LinearMap.ext fun _ ↦ rfl)

@[ext]
theorem hom_ext {f g : V ⟶ W} (h : ∀ x, f.fiberMap x = g.fiberMap x) : f = g :=
  Hom.ext (funext h)

@[simp]
theorem fiberMap_id (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) (x : X) :
    (𝟙 V : V ⟶ V).fiberMap x = LinearMap.id := (rfl)

@[simp]
theorem fiberMap_comp (f : V ⟶ W) (g : W ⟶ U) (x : X) :
    (f ≫ g).fiberMap x = (g.fiberMap x).comp (f.fiberMap x) := (rfl)

@[simp]
theorem totalSpaceMap_id (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    (𝟙 V : V ⟶ V).totalSpaceMap = ContinuousMap.id _ := (rfl)

@[simp]
theorem totalSpaceMap_comp (f : V ⟶ W) (g : W ⟶ U) :
    (f ≫ g).totalSpaceMap = g.totalSpaceMap.comp f.totalSpaceMap := (rfl)

theorem totalSpaceMap_injective : Function.Injective (Hom.totalSpaceMap (V := V) (W := W)) := by
  intro f g h
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro v
  exact TotalSpace.mk_inj.mp (congrArg (fun k ↦ k ⟨x, v⟩) h)

namespace Hom

instance : Zero (V ⟶ W) where
  zero := ⟨fun _ ↦ 0, W.continuous_zeroSection.comp V.continuous_proj⟩

instance : Add (V ⟶ W) where
  add f g := ⟨fun x ↦ f.fiberMap x + g.fiberMap x,
    W.continuous_add f.continuous_totalSpaceMap g.continuous_totalSpaceMap⟩

instance : Neg (V ⟶ W) where
  neg f := ⟨fun x ↦ -f.fiberMap x, by
    simpa only [neg_one_smul, LinearMap.neg_apply] using
      W.continuous_smul (continuous_const (y := (-1 : 𝕜))) f.continuous_totalSpaceMap⟩

instance : Sub (V ⟶ W) where
  sub f g := f + -g

instance : SMul ℕ (V ⟶ W) where
  smul n f := ⟨fun x ↦ n • f.fiberMap x, by
    simpa only [Nat.cast_smul_eq_nsmul, LinearMap.smul_apply] using
      W.continuous_smul (continuous_const (y := (n : 𝕜))) f.continuous_totalSpaceMap⟩

instance : SMul ℤ (V ⟶ W) where
  smul n f := ⟨fun x ↦ n • f.fiberMap x, by
    simpa only [Int.cast_smul_eq_zsmul, LinearMap.smul_apply] using
      W.continuous_smul (continuous_const (y := (n : 𝕜))) f.continuous_totalSpaceMap⟩

instance : AddCommGroup (V ⟶ W) :=
  Function.Injective.addCommGroup (fun f ↦ f.fiberMap) (fun _ _ h ↦ Hom.ext h)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ funext fun _ ↦ (sub_eq_add_neg _ _).symm)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end Hom

instance : Preadditive (FiniteRankVectorBundle.{u, v, w} 𝕜 X) where
  add_comp _ _ _ _ _ h := hom_ext fun x ↦ LinearMap.ext fun _ ↦ (h.fiberMap x).map_add _ _
  comp_add _ _ _ _ _ _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

@[simp]
theorem fiberMap_zero (x : X) : (0 : V ⟶ W).fiberMap x = 0 := (rfl)

@[simp]
theorem fiberMap_add (f g : V ⟶ W) (x : X) :
    (f + g).fiberMap x = f.fiberMap x + g.fiberMap x := (rfl)

@[simp]
theorem fiberMap_neg (f : V ⟶ W) (x : X) : (-f).fiberMap x = -f.fiberMap x := (rfl)

@[simp]
theorem fiberMap_sub (f g : V ⟶ W) (x : X) :
    (f - g).fiberMap x = f.fiberMap x - g.fiberMap x := by
  simp only [sub_eq_add_neg, fiberMap_add, fiberMap_neg]

@[simp]
theorem fiberMap_nsmul (n : ℕ) (f : V ⟶ W) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := (rfl)

@[simp]
theorem fiberMap_zsmul (n : ℤ) (f : V ⟶ W) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := (rfl)

/-- Realize variable-rank vector bundles and their morphisms as topological spaces and continuous
maps. -/
-- Expose the object assignment so morphism types reduce to the glued total spaces.
@[expose]
def totalSpaceFunctor : FiniteRankVectorBundle.{u, v, w} 𝕜 X ⥤ TopCat.{max u w} where
  obj V := TopCat.of (TotalSpace Unit V.Fiber)
  map f := TopCat.ofHom f.totalSpaceMap

@[simp]
theorem totalSpaceFunctor_obj (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    totalSpaceFunctor.obj V = TopCat.of (TotalSpace Unit V.Fiber) := (rfl)

@[simp]
theorem totalSpaceFunctor_map_apply (f : V ⟶ W) (p : TotalSpace Unit V.Fiber) :
    totalSpaceFunctor.map f p = f.totalSpaceMap p := (rfl)

instance : (totalSpaceFunctor (𝕜 := 𝕜) (X := X)).Faithful where
  map_injective h := totalSpaceMap_injective (congrArg TopCat.Hom.hom h)

/-- Evaluate a variable-rank vector bundle and its morphisms on the fibre at `x`. -/
-- Expose the object assignment so evaluated morphisms act on `V.Fiber x`.
@[expose]
def fiberFunctor (x : X) : FiniteRankVectorBundle.{u, v, w} 𝕜 X ⥤ ModuleCat.{w} 𝕜 where
  obj V := ModuleCat.of 𝕜 (V.Fiber x)
  map f := ModuleCat.ofHom (f.fiberMap x)

@[simp]
theorem fiberFunctor_obj (x : X) (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    (fiberFunctor x).obj V = ModuleCat.of 𝕜 (V.Fiber x) := (rfl)

@[simp]
theorem fiberFunctor_map_apply (x : X) (f : V ⟶ W) (v : V.Fiber x) :
    (fiberFunctor x).map f v = f.fiberMap x v := (rfl)

instance (x : X) : (fiberFunctor (𝕜 := 𝕜) (X := X) x).Additive where
  map_add := by intros; rfl

/-- Construct an isomorphism of variable-rank vector bundles from fibrewise linear equivalences
whose forward and inverse total-space maps are continuous. -/
def isoMk (e : ∀ x, V.Fiber x ≃ₗ[𝕜] W.Fiber x)
    (h : Continuous (fun p : TotalSpace Unit V.Fiber ↦
      (⟨p.proj, e p.proj p.2⟩ : TotalSpace Unit W.Fiber)))
    (h' : Continuous (fun p : TotalSpace Unit W.Fiber ↦
      (⟨p.proj, (e p.proj).symm p.2⟩ : TotalSpace Unit V.Fiber))) : V ≅ W where
  hom := ⟨fun x ↦ (e x).toLinearMap, h⟩
  inv := ⟨fun x ↦ (e x).symm.toLinearMap, h'⟩
  hom_inv_id := hom_ext fun x ↦ LinearMap.ext (e x).symm_apply_apply
  inv_hom_id := hom_ext fun x ↦ LinearMap.ext (e x).apply_symm_apply

@[simp]
theorem fiberMap_isoMk_hom (e : ∀ x, V.Fiber x ≃ₗ[𝕜] W.Fiber x) (h h') (x : X) :
    (isoMk e h h').hom.fiberMap x = (e x).toLinearMap := (rfl)

@[simp]
theorem fiberMap_isoMk_inv (e : ∀ x, V.Fiber x ≃ₗ[𝕜] W.Fiber x) (h h') (x : X) :
    (isoMk e h h').inv.fiberMap x = (e x).symm.toLinearMap := (rfl)

end Category

end FiniteRankVectorBundle

end TauCeti

namespace CategoryTheory.Iso

open TauCeti

universe u v w

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X] {V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X}

/-- Isomorphic variable-rank vector bundles have the same locally constant rank function. -/
theorem finiteRankVectorBundle_rank_eq (e : V ≅ W) : V.rank = W.rank := by
  ext x
  calc
    V.rank x = Module.finrank 𝕜 ((FiniteRankVectorBundle.fiberFunctor x).obj V) :=
      (V.finrank_fiber x).symm
    _ = Module.finrank 𝕜 ((FiniteRankVectorBundle.fiberFunctor x).obj W) :=
      ((FiniteRankVectorBundle.fiberFunctor x).mapIso e).toLinearEquiv.finrank_eq
    _ = W.rank x := W.finrank_fiber x

end CategoryTheory.Iso

namespace TauCeti.FiniteRankVectorBundle

universe u v w

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

/-- Pullback fibres inherit `AddCommGroup` structure from the target bundle. -/
local instance {B B' : Type*} (f : B' → B) (E : B → Type*) [∀ b, AddCommGroup (E b)] (x : B') :
    AddCommGroup ((f *ᵖ E) x) :=
  inferInstanceAs (AddCommGroup (E (f x)))

/-- A variable-rank vector bundle is isomorphic to `ofFixedRank 𝕜 n E` for some constant-rank
Mathlib `VectorBundle 𝕜 (Fin n → 𝕜) E` over `X` if and only if its rank function is constantly
`n`. -/
theorem exists_iso_ofFixedRank_iff (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) (n : ℕ) :
    (∃ (E : X → Type w) (_ : ∀ x, AddCommGroup (E x)) (_ : ∀ x, Module 𝕜 (E x))
        (_ : ∀ x, TopologicalSpace (E x)) (_ : TopologicalSpace (TotalSpace (Fin n → 𝕜) E))
        (_ : FiberBundle (Fin n → 𝕜) E) (_ : VectorBundle 𝕜 (Fin n → 𝕜) E),
      Nonempty (ofFixedRank 𝕜 n E ≅ V)) ↔ V.rank = LocallyConstant.const X n := by
  constructor
  · rintro ⟨E, _, _, _, _, _, _, ⟨e⟩⟩
    exact e.symm.finiteRankVectorBundle_rank_eq
  · intro hn
    have hnx : ∀ x : X, V.rank x = n := fun x ↦ congrFun (congrArg DFunLike.coe hn) x
    let inc : C(X, {x : X // V.rank x = n}) :=
      ⟨fun x ↦ ⟨x, hnx x⟩, continuous_id.subtype_mk _⟩
    refine ⟨(inc : X → {x : X // V.rank x = n}) *ᵖ (V.StratumFiber n),
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨?_⟩⟩
    refine isoMk (fun x ↦ LinearEquiv.refl 𝕜 (V.Fiber x)) ?_ ?_
    · have htoV : Continuous
          (fun q : TotalSpace (Fin n → 𝕜) ((inc : X → _) *ᵖ (V.StratumFiber n)) ↦
            V.totalSpaceHomeomorph ⟨n, Pullback.lift inc q⟩) :=
        V.totalSpaceHomeomorph.continuous.comp <| continuous_sigmaMk.comp <|
          Pullback.continuous_lift (Fin n → 𝕜) (V.StratumFiber n) inc
      exact (htoV.comp (ofFixedRankTotalSpaceHomeomorph 𝕜 n
        ((inc : X → _) *ᵖ (V.StratumFiber n))).continuous).congr fun _ ↦ rfl
    · have htoE : Continuous (fun p : TotalSpace Unit V.Fiber ↦
          (⟨p.proj, p.2⟩ : TotalSpace (Fin n → 𝕜) ((inc : X → _) *ᵖ (V.StratumFiber n)))) := by
        rw [(inducing_pullbackTotalSpaceEmbedding (Fin n → 𝕜) (V.StratumFiber n)
          inc).continuous_iff]
        refine V.continuous_proj.prodMk ?_
        have hstr := (V.continuous_mk_iff_rankStrata V.continuous_proj (fun p ↦ p.2)).1
          continuous_id n
        exact (hstr.comp (Continuous.subtype_mk continuous_id fun p : TotalSpace Unit V.Fiber ↦
          hnx p.proj)).congr fun _ ↦ rfl
      exact ((ofFixedRankTotalSpaceHomeomorph 𝕜 n
        ((inc : X → _) *ᵖ (V.StratumFiber n))).symm.continuous.comp htoE).congr fun _ ↦ rfl

end TauCeti.FiniteRankVectorBundle
