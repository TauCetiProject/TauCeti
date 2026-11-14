/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.TransferInstance
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.Topology.VectorBundle.TransferInstance
import TauCeti.Topology.VectorBundle.Section
import TauCeti.Topology.VectorBundle.Smul

/-!
# Variable-rank finite-rank topological vector bundles

`TauCeti.FiniteRankBundle.{w} 𝕜 X` packages a genuine variable-rank topological `𝕜`-vector bundle
over `X` with fibres in `Type w`: a locally constant rank `rank : LocallyConstant X ℕ`, a family of
fibres `Fiber : X → Type w`, and on each clopen rank stratum `{x : X // rank x = n}` a genuine
Mathlib `FiberBundle` and `VectorBundle` with coordinate model `Fin n → 𝕜`. No boundedness of the
rank across components, compactness, paracompactness, or scalar completeness is assumed.

Topological-vector-space and finite-dimensionality properties of every fibre
(`IsTopologicalAddGroup`, `ContinuousSMul`, `FiniteDimensional`, `T2Space`, and
`Module.finrank 𝕜 (B.Fiber x) = B.rank x`) are derived from the preferred continuous linear chart
equivalence `TauCeti.FiniteRankBundle.continuousLinearEquivCoord` on the `(B.rank x)`-stratum
rather than stored as redundant fields.

`TotalSpace Unit B.Fiber` carries the topology induced from the disjoint union
`B.GluedTotalSpace = Σ n : ℕ, TotalSpace (Fin n → 𝕜) (B.StratumFiber n)` via
`TauCeti.FiniteRankBundle.gluedTotalSpaceHomeomorph`. Each rank-stratum total space embeds openly
(`TauCeti.FiniteRankBundle.isOpenEmbedding_stratum`), each individual fibre embeds
(`TauCeti.FiniteRankBundle.isEmbedding_totalSpaceMk`), and maps into the glued total space are
continuous if and only if their restrictions to all rank strata are continuous
(`TauCeti.FiniteRankBundle.continuous_mk_iff_rankStrata`). Fibrewise zero, addition, and continuous
scalar multiplication are continuous on the glued total space.

`TauCeti.FiniteRankBundle.ofConstantRank` embeds any constant-rank Mathlib vector bundle with model
`Fin n → 𝕜` as a `FiniteRankBundle` whose glued total space is homeomorphic to the original total
space (`TauCeti.FiniteRankBundle.ofConstantRankTotalSpaceHomeomorph`), and
`TauCeti.FiniteRankBundle.trivial` constructs the trivial bundle of rank `n`.
-/

public section

open Bundle Set Topology

namespace TauCeti

universe w u v

/-- A genuine variable-rank finite-rank topological `𝕜`-vector bundle over `X` with fibres in
`Type w`. On each clopen stratum `{x : X // rank x = n}`, the fibres form a Mathlib `FiberBundle`
and `VectorBundle` with model `Fin n → 𝕜`. -/
@[pp_with_univ]
structure FiniteRankBundle (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    (X : Type u) [TopologicalSpace X] : Type max u v (w + 1) where
  /-- The locally constant, not necessarily bounded, fibre dimension. -/
  rank : LocallyConstant X ℕ
  /-- The fibre over each base point. -/
  Fiber : X → Type w
  [addCommGroup (x : X) : AddCommGroup (Fiber x)]
  [module (x : X) : Module 𝕜 (Fiber x)]
  [topologicalSpaceFiber (x : X) : TopologicalSpace (Fiber x)]
  [topologicalSpaceStratum (n : ℕ) :
    TopologicalSpace (TotalSpace (Fin n → 𝕜) (fun x : {x : X // rank x = n} ↦ Fiber x.1))]
  [fiberBundle (n : ℕ) :
    FiberBundle (Fin n → 𝕜) (fun x : {x : X // rank x = n} ↦ Fiber x.1)]
  [vectorBundle (n : ℕ) :
    VectorBundle 𝕜 (Fin n → 𝕜) (fun x : {x : X // rank x = n} ↦ Fiber x.1)]

attribute [instance] FiniteRankBundle.addCommGroup FiniteRankBundle.module
  FiniteRankBundle.topologicalSpaceFiber FiniteRankBundle.topologicalSpaceStratum
  FiniteRankBundle.fiberBundle FiniteRankBundle.vectorBundle

namespace FiniteRankBundle

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]
  (B : FiniteRankBundle.{w} 𝕜 X)

/-- The fibre family of `B` restricted to the `n`th clopen rank stratum `{x : X // B.rank x = n}`.
This is an abbreviation so the stratum `FiberBundle` and `VectorBundle` instances apply directly. -/
abbrev StratumFiber (n : ℕ) (x : {x : X // B.rank x = n}) : Type w :=
  B.Fiber x.1

/-- The preferred continuous linear equivalence from `B.Fiber x` to its coordinate model
`Fin (B.rank x) → 𝕜`, read from the `(B.rank x)`-stratum vector bundle. -/
noncomputable def continuousLinearEquivCoord (x : X) :
    B.Fiber x ≃L[𝕜] (Fin (B.rank x) → 𝕜) :=
  VectorBundle.continuousLinearEquivAt 𝕜 (Fin (B.rank x) → 𝕜) (B.StratumFiber (B.rank x)) ⟨x, rfl⟩

theorem continuousLinearEquivCoord_eq (x : X) :
    B.continuousLinearEquivCoord x =
      VectorBundle.continuousLinearEquivAt 𝕜 (Fin (B.rank x) → 𝕜)
        (B.StratumFiber (B.rank x)) ⟨x, rfl⟩ := (rfl)

instance (x : X) : IsTopologicalAddGroup (B.Fiber x) :=
  (B.continuousLinearEquivCoord x).toContinuousAddEquiv.isTopologicalAddGroup

instance (x : X) : ContinuousSMul 𝕜 (B.Fiber x) :=
  (B.continuousLinearEquivCoord x).continuousSMul

instance (x : X) : FiniteDimensional 𝕜 (B.Fiber x) :=
  Module.Finite.equiv (B.continuousLinearEquivCoord x).symm.toLinearEquiv

@[simp]
theorem finrank_fiber (x : X) : Module.finrank 𝕜 (B.Fiber x) = B.rank x :=
  (B.continuousLinearEquivCoord x).toLinearEquiv.finrank_eq.trans (Module.finrank_fin_fun 𝕜)

instance (x : X) : T2Space (B.Fiber x) :=
  T2Space.of_injective_continuous (B.continuousLinearEquivCoord x).injective
    (B.continuousLinearEquivCoord x).continuous

/-- The disjoint union of the native stratum total spaces. -/
abbrev GluedTotalSpace : Type max u w :=
  Σ n : ℕ, TotalSpace (Fin n → 𝕜) (B.StratumFiber n)

/-- Projection from the disjoint union of stratum total spaces to `X`. -/
def gluedProj (p : B.GluedTotalSpace) : X :=
  p.2.proj.1

@[simp]
theorem gluedProj_mk (n : ℕ) (p : TotalSpace (Fin n → 𝕜) (B.StratumFiber n)) :
    B.gluedProj ⟨n, p⟩ = p.proj.1 := (rfl)

@[continuity, fun_prop]
theorem continuous_gluedProj : Continuous B.gluedProj :=
  continuous_sigma fun n ↦
    continuous_subtype_val.comp (FiberBundle.continuous_proj (Fin n → 𝕜) (B.StratumFiber n))

theorem isOpenMap_gluedProj : IsOpenMap B.gluedProj :=
  isOpenMap_sigma.2 fun n ↦
    (B.rank.isLocallyConstant.isOpen_fiber n).isOpenEmbedding_subtypeVal.isOpenMap.comp
      (FiberBundle.isOpenMap_proj (Fin n → 𝕜) (B.StratumFiber n))

private def gluedTotalSpaceEquiv : B.GluedTotalSpace ≃ TotalSpace Unit B.Fiber where
  toFun p := ⟨p.2.proj.1, p.2.2⟩
  invFun p := ⟨B.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩
  left_inv := by
    rintro ⟨n, ⟨⟨x, hx⟩, v⟩⟩
    cases hx
    rfl
  right_inv := by
    rintro ⟨x, v⟩
    rfl

/-- The total space `TotalSpace Unit B.Fiber` carries the topology induced from the disjoint union
of the native stratum vector bundles. -/
instance : TopologicalSpace (TotalSpace Unit B.Fiber) :=
  TopologicalSpace.induced
    (fun p : TotalSpace Unit B.Fiber ↦ (⟨B.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩ : B.GluedTotalSpace))
    inferInstance

/-- Reindexing the disjoint union of the rank-stratum total spaces gives a homeomorphism onto
`TotalSpace Unit B.Fiber`. -/
def gluedTotalSpaceHomeomorph : B.GluedTotalSpace ≃ₜ TotalSpace Unit B.Fiber :=
  (B.gluedTotalSpaceEquiv.symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm

@[simp]
theorem gluedTotalSpaceHomeomorph_apply (p : B.GluedTotalSpace) :
    B.gluedTotalSpaceHomeomorph p = ⟨p.2.proj.1, p.2.2⟩ := (rfl)

@[simp]
theorem gluedTotalSpaceHomeomorph_symm_apply (p : TotalSpace Unit B.Fiber) :
    B.gluedTotalSpaceHomeomorph.symm p = ⟨B.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩ := (rfl)

@[continuity, fun_prop]
theorem continuous_proj : Continuous (TotalSpace.proj : TotalSpace Unit B.Fiber → X) :=
  B.continuous_gluedProj.comp B.gluedTotalSpaceHomeomorph.symm.continuous

theorem isOpenMap_proj : IsOpenMap (TotalSpace.proj : TotalSpace Unit B.Fiber → X) :=
  B.isOpenMap_gluedProj.comp B.gluedTotalSpaceHomeomorph.symm.isOpenMap

/-- Each rank-stratum total space embeds as an open subspace of `TotalSpace Unit B.Fiber`. -/
theorem isOpenEmbedding_stratum (n : ℕ) :
    IsOpenEmbedding
      (fun p : TotalSpace (Fin n → 𝕜) (B.StratumFiber n) ↦ B.gluedTotalSpaceHomeomorph ⟨n, p⟩) :=
  B.gluedTotalSpaceHomeomorph.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk

/-- The image of the `n`th stratum total space is the rank-`n` part of `TotalSpace Unit B.Fiber`. -/
theorem range_stratum (n : ℕ) :
    range (fun p : TotalSpace (Fin n → 𝕜) (B.StratumFiber n) ↦
      B.gluedTotalSpaceHomeomorph ⟨n, p⟩) =
      {p : TotalSpace Unit B.Fiber | B.rank p.proj = n} := by
  ext ⟨x, v⟩
  constructor
  · rintro ⟨q, hq⟩
    have hproj : q.proj.1 = x := congrArg TotalSpace.proj hq
    exact hproj ▸ q.proj.2
  · intro hx
    exact ⟨⟨⟨x, hx⟩, v⟩, rfl⟩

/-- Inclusion of a single fibre into the glued total space is a topological embedding. -/
theorem isEmbedding_totalSpaceMk (x : X) :
    IsEmbedding (TotalSpace.mk' Unit x : B.Fiber x → TotalSpace Unit B.Fiber) := by
  have h : (TotalSpace.mk' Unit x : B.Fiber x → TotalSpace Unit B.Fiber) =
      fun v ↦ B.gluedTotalSpaceHomeomorph
        ⟨B.rank x, TotalSpace.mk' (Fin (B.rank x) → 𝕜) ⟨x, rfl⟩ v⟩ :=
    funext fun v ↦ (B.gluedTotalSpaceHomeomorph_apply ⟨B.rank x, ⟨⟨x, rfl⟩, v⟩⟩).symm
  rw [h]
  exact B.gluedTotalSpaceHomeomorph.isEmbedding.comp
    (IsEmbedding.sigmaMk.comp
      (FiberBundle.totalSpaceMk_isEmbedding (Fin (B.rank x) → 𝕜)
        (B.StratumFiber (B.rank x)) ⟨x, rfl⟩))

@[continuity, fun_prop]
theorem continuous_totalSpaceMk (x : X) :
    Continuous (TotalSpace.mk' Unit x : B.Fiber x → TotalSpace Unit B.Fiber) :=
  (B.isEmbedding_totalSpaceMk x).continuous

section Continuity

variable {Y : Type*} [TopologicalSpace Y] {b : Y → X}

/-- A map into `TotalSpace Unit B.Fiber` is continuous if and only if its restrictions to all
clopen rank strata are continuous into the native stratum total spaces. -/
theorem continuous_mk_iff_rankStrata (hb : Continuous b) (s : ∀ y, B.Fiber (b y)) :
    Continuous (fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit B.Fiber)) ↔
      ∀ n : ℕ, Continuous (fun y : {y : Y // B.rank (b y) = n} ↦
        (⟨⟨b y.1, y.2⟩, s y.1⟩ : TotalSpace (Fin n → 𝕜) (B.StratumFiber n))) := by
  constructor
  · intro hs n
    apply (IsEmbedding.sigmaMk (σ := fun m ↦ TotalSpace (Fin m → 𝕜) (B.StratumFiber m)))
      |>.continuous_iff.2
    refine (B.gluedTotalSpaceHomeomorph.symm.continuous.comp
      (hs.comp continuous_subtype_val)).congr ?_
    rintro ⟨y, hy⟩
    cases hy
    exact B.gluedTotalSpaceHomeomorph_symm_apply ⟨b y, s y⟩
  · intro hs
    refine continuous_of_cover_nhds (s := fun n : ℕ ↦ {y : Y | B.rank (b y) = n})
      (fun y ↦ ⟨B.rank (b y), ((B.rank.isLocallyConstant.isOpen_fiber _).preimage hb).mem_nhds rfl⟩)
      fun n ↦ ?_
    rw [continuousOn_iff_continuous_domRestrict]
    refine (B.gluedTotalSpaceHomeomorph.continuous.comp
      (continuous_sigmaMk.comp (hs n))).congr ?_
    rintro ⟨y, hy⟩
    exact (B.gluedTotalSpaceHomeomorph_apply ⟨n, ⟨⟨b y, hy⟩, s y⟩⟩).symm

/-- The zero section of a variable-rank vector bundle is continuous. -/
@[fun_prop]
theorem continuous_zeroSection :
    Continuous (fun x ↦ (⟨x, 0⟩ : TotalSpace Unit B.Fiber)) :=
  (B.continuous_mk_iff_rankStrata continuous_id _).2 fun n ↦
    Bundle.Trivialization.continuous_zeroSection 𝕜
      (F := Fin n → 𝕜) (E := B.StratumFiber n)

/-- Pointwise sums of continuous maps into `TotalSpace Unit B.Fiber` over a common base map are
continuous, without any bounded-rank hypothesis. -/
theorem continuous_add {s t : ∀ y, B.Fiber (b y)}
    (hs : Continuous (fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit B.Fiber)))
    (ht : Continuous (fun y ↦ (⟨b y, t y⟩ : TotalSpace Unit B.Fiber))) :
    Continuous (fun y ↦ (⟨b y, s y + t y⟩ : TotalSpace Unit B.Fiber)) := by
  have hb : Continuous b := B.continuous_proj.comp hs
  rw [B.continuous_mk_iff_rankStrata hb] at hs ht ⊢
  intro n
  exact (hs n).add_totalSpace 𝕜 (ht n)

/-- Pointwise scalar multiples of continuous maps into `TotalSpace Unit B.Fiber` by continuous
scalar functions are continuous. -/
theorem continuous_smul {s : ∀ y, B.Fiber (b y)} {c : Y → 𝕜}
    (hc : Continuous c)
    (hs : Continuous (fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit B.Fiber))) :
    Continuous (fun y ↦ (⟨b y, c y • s y⟩ : TotalSpace Unit B.Fiber)) := by
  have hb : Continuous b := B.continuous_proj.comp hs
  rw [B.continuous_mk_iff_rankStrata hb] at hs ⊢
  intro n
  exact (hc.comp continuous_subtype_val).smul_totalSpace (hs n)

end Continuity

section ConstantRank

variable (𝕜) in
/-- View a constant-rank Mathlib vector bundle with model `Fin n → 𝕜` as a `FiniteRankBundle` of
constant rank `n`. Works on empty or disconnected bases and for `n = 0`. -/
noncomputable def ofConstantRank (n : ℕ) (E : X → Type w)
    [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E] :
    FiniteRankBundle.{w} 𝕜 X :=
  let pkg (m : ℕ) :
      Σ' (t : TopologicalSpace
          (TotalSpace (Fin m → 𝕜) (fun x : {x : X // LocallyConstant.const X n x = m} ↦ E x.1)))
        (fb : @FiberBundle _ (Fin m → 𝕜) _ _
          (fun x : {x : X // LocallyConstant.const X n x = m} ↦ E x.1) t _),
        @VectorBundle 𝕜 _ (Fin m → 𝕜)
          (fun x : {x : X // LocallyConstant.const X n x = m} ↦ E x.1) _ _ _ _ _ _ t _ fb :=
    if h : n = m then
      h ▸
        letI : ∀ x, Nonempty (E x) := fun _ ↦ ⟨0⟩
        let f : C({x : X // LocallyConstant.const X n x = n}, X) :=
          ⟨Subtype.val, continuous_subtype_val⟩
        ⟨Pullback.TotalSpace.topologicalSpace (Fin n → 𝕜) E f,
          FiberBundle.pullback (F := Fin n → 𝕜) (E := E) f,
          VectorBundle.pullback 𝕜 (F := Fin n → 𝕜) (E := E) f⟩
    else
      letI : IsEmpty {x : X // LocallyConstant.const X n x = m} := ⟨fun x ↦ h x.2⟩
      ⟨⊥, @FiberBundle.ofIsEmpty _ _ _ (Fin m → 𝕜) _ _ _ ⊥,
        @VectorBundle.ofIsEmpty 𝕜 _ _ _ _ (Fin m → 𝕜) _ _ _ _ _ _ ⊥⟩
  { rank := LocallyConstant.const X n
    Fiber := E
    topologicalSpaceStratum m := (pkg m).1
    fiberBundle m := (pkg m).2.1
    vectorBundle m := (pkg m).2.2 }

@[simp]
theorem rank_ofConstantRank (n : ℕ) (E : X → Type w)
    [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E] :
    (ofConstantRank 𝕜 n E).rank = LocallyConstant.const X n := (rfl)

variable (𝕜) in
/-- Continuous linear identification of the fibre of `ofConstantRank 𝕜 n E` at `x` with `E x`. -/
noncomputable def ofConstantRankFiberEquiv (n : ℕ) (E : X → Type w)
    [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E] (x : X) :
    (ofConstantRank 𝕜 n E).Fiber x ≃L[𝕜] E x :=
  ContinuousLinearEquiv.refl 𝕜 (E x)

private theorem topologicalSpaceStratum_ofConstantRank_self (n : ℕ) (E : X → Type w)
    [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E] :
    (ofConstantRank 𝕜 n E).topologicalSpaceStratum n =
      Pullback.TotalSpace.topologicalSpace (Fin n → 𝕜) E
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C({x : X // LocallyConstant.const X n x = n}, X)) :=
  congrArg PSigma.fst (dite_eq_left_of_eq_true (eq_true rfl))

variable (𝕜) in
/-- For a constant-rank bundle `ofConstantRank 𝕜 n E`, the glued total space is homeomorphic over
the identity of `X` to the original Mathlib total space `TotalSpace (Fin n → 𝕜) E`. -/
noncomputable def ofConstantRankTotalSpaceHomeomorph (n : ℕ) (E : X → Type w)
    [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E] :
    TotalSpace Unit (ofConstantRank 𝕜 n E).Fiber ≃ₜ TotalSpace (Fin n → 𝕜) E where
  toFun p := ⟨p.proj, ofConstantRankFiberEquiv 𝕜 n E p.proj p.2⟩
  invFun p := ⟨p.proj, (ofConstantRankFiberEquiv 𝕜 n E p.proj).symm p.2⟩
  left_inv := fun ⟨_, _⟩ ↦ rfl
  right_inv := fun ⟨_, _⟩ ↦ rfl
  continuous_toFun := by
    let B' := ofConstantRank 𝕜 n E
    let f : C({x : X // LocallyConstant.const X n x = n}, X) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    have hpull : Continuous (fun q : TotalSpace (Fin n → 𝕜) (B'.StratumFiber n) ↦
        (⟨q.proj.1, q.2⟩ : TotalSpace (Fin n → 𝕜) E)) := by
      have hl := Pullback.continuous_lift (Fin n → 𝕜) E f
      rw [continuous_iff_le_induced] at hl ⊢
      rw [topologicalSpaceStratum_ofConstantRank_self (𝕜 := 𝕜) n E]
      exact hl
    have hsec : Continuous (fun p : TotalSpace Unit B'.Fiber ↦
        (⟨⟨p.proj, rfl⟩, p.2⟩ : TotalSpace (Fin n → 𝕜) (B'.StratumFiber n))) :=
      (IsEmbedding.sigmaMk
        (σ := fun m ↦ TotalSpace (Fin m → 𝕜) (B'.StratumFiber m))).continuous_iff.2
        B'.gluedTotalSpaceHomeomorph.symm.continuous
    exact hpull.comp hsec
  continuous_invFun := by
    let B' := ofConstantRank 𝕜 n E
    let f : C({x : X // LocallyConstant.const X n x = n}, X) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    have hstr : Continuous (fun p : TotalSpace (Fin n → 𝕜) E ↦
        (⟨⟨p.proj, rfl⟩, p.2⟩ : TotalSpace (Fin n → 𝕜) (B'.StratumFiber n))) := by
      have hlift_inv : Continuous (fun p : TotalSpace (Fin n → 𝕜) E ↦
          (⟨⟨p.proj, rfl⟩, p.2⟩ : TotalSpace (Fin n → 𝕜) (f *ᵖ E))) := by
        rw [(inducing_pullbackTotalSpaceEmbedding (Fin n → 𝕜) E f).continuous_iff]
        exact ((FiberBundle.continuous_proj (Fin n → 𝕜) E).subtype_mk _).prodMk continuous_id
      rw [continuous_iff_coinduced_le] at hlift_inv ⊢
      rw [topologicalSpaceStratum_ofConstantRank_self (𝕜 := 𝕜) n E]
      exact hlift_inv
    exact B'.gluedTotalSpaceHomeomorph.continuous.comp (continuous_sigmaMk.comp hstr)

@[simp]
theorem ofConstantRankTotalSpaceHomeomorph_apply (n : ℕ) (E : X → Type w)
    [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E]
    (p : TotalSpace Unit (ofConstantRank 𝕜 n E).Fiber) :
    ofConstantRankTotalSpaceHomeomorph 𝕜 n E p =
      ⟨p.proj, ofConstantRankFiberEquiv 𝕜 n E p.proj p.2⟩ := (rfl)

@[simp]
theorem ofConstantRankTotalSpaceHomeomorph_symm_apply (n : ℕ) (E : X → Type w)
    [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
    [VectorBundle 𝕜 (Fin n → 𝕜) E]
    (p : TotalSpace (Fin n → 𝕜) E) :
    (ofConstantRankTotalSpaceHomeomorph 𝕜 n E).symm p =
      ⟨p.proj, (ofConstantRankFiberEquiv 𝕜 n E p.proj).symm p.2⟩ := (rfl)

variable (𝕜 X) in
/-- The trivial `FiniteRankBundle` of constant rank `n`, with fibres `Fin n → 𝕜`. -/
noncomputable def trivial (n : ℕ) : FiniteRankBundle.{v} 𝕜 X :=
  ofConstantRank 𝕜 n (Bundle.Trivial X (Fin n → 𝕜))

@[simp]
theorem rank_trivial (n : ℕ) : (trivial 𝕜 X n).rank = LocallyConstant.const X n := (rfl)

variable (𝕜 X) in
/-- Continuous linear identification of the fibre of `trivial 𝕜 X n` at `x` with `Fin n → 𝕜`. -/
noncomputable def trivialFiberEquiv (n : ℕ) (x : X) : (trivial 𝕜 X n).Fiber x ≃L[𝕜] (Fin n → 𝕜) :=
  ofConstantRankFiberEquiv 𝕜 n (Bundle.Trivial X (Fin n → 𝕜)) x

end ConstantRank

end FiniteRankBundle
end TauCeti
