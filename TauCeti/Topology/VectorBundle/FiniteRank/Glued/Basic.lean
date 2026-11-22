/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.VectorBundle.Basic

import TauCeti.Topology.VectorBundle.Add
import TauCeti.Topology.VectorBundle.Smul

/-!
# Shared glued total spaces for variable-rank bundles

Small coordinate atlases (`TauCeti.FiniteRankAtlas`) and general variable-rank vector bundles
(`TauCeti.FiniteRankVectorBundle`) both decompose `X` into clopen strata `{x : X // rank x = n}`
carrying Mathlib `VectorBundle 𝕜 (Fin n → 𝕜)` structures linearly identified with `Fiber V`.
`TauCeti.VariableRankBundle` packages this shared interface and develops the glued disjoint-union
topology on `TotalSpace Unit (Fiber V)` (`totalSpaceHomeomorph`, `isOpenEmbedding_stratum`,
`range_stratum`, `continuous_mk_iff_rankStrata`), algebraic continuity (`continuous_zeroSection`,
`continuous_add`, `continuous_smul`), and constant-rank total-space comparisons
(`constRankTotalSpaceHomeomorph`, `totalSpaceHomeomorphOfConstStratum`). Morphisms and the
preadditive category structure live in `TauCeti.Topology.VectorBundle.FiniteRank.Glued.Category`.
-/

public section
open Bundle Topology
namespace TauCeti
universe u v w b

/-- Common interface for variable-rank finite-rank `𝕜`-vector bundle representations over `X` whose
clopen rank strata carry Mathlib `VectorBundle 𝕜 (Fin n → 𝕜)` structures linearly identified with
`Fiber V`. -/
class VariableRankBundle (B : Type b) (𝕜 : outParam (Type v)) (X : outParam (Type u))
    (Fiber : outParam (B → X → Type w)) [NontriviallyNormedField 𝕜] [TopologicalSpace X] where
  /-- The locally constant, not necessarily bounded, rank function. -/
  rank (V : B) : LocallyConstant X ℕ
  /-- The fibre family restricted to the `n`th clopen rank stratum `{x : X // rank V x = n}`. -/
  StratumFiber (V : B) (n : ℕ) : {x : X // rank V x = n} → Type w
  /-- The additive group structure on each fibre `Fiber V x`. -/
  [addCommGroupFiber : ∀ (V : B) (x : X), AddCommGroup (Fiber V x)]
  /-- The `𝕜`-module structure on each fibre `Fiber V x`. -/
  [moduleFiber : ∀ (V : B) (x : X), Module 𝕜 (Fiber V x)]
  [addCommGroupStratumFiber : ∀ V n x, AddCommGroup (StratumFiber V n x)]
  [moduleStratumFiber : ∀ V n x, Module 𝕜 (StratumFiber V n x)]
  [topologicalSpaceStratumFiber : ∀ V n x, TopologicalSpace (StratumFiber V n x)]
  [topologicalSpaceStratumTotalSpace :
    ∀ V n, TopologicalSpace (TotalSpace (Fin n → 𝕜) (StratumFiber V n))]
  [fiberBundleStratum : ∀ V n, FiberBundle (Fin n → 𝕜) (StratumFiber V n)]
  [vectorBundleStratum : ∀ V n, VectorBundle 𝕜 (Fin n → 𝕜) (StratumFiber V n)]
  /-- Linear identification between the `n`th stratum fibre over `y` and `Fiber V y.val`. -/
  stratumFiberEquiv (V : B) {n : ℕ} (y : {x : X // rank V x = n}) :
    StratumFiber V n y ≃ₗ[𝕜] Fiber V y.val

namespace VariableRankBundle
attribute [instance_reducible] addCommGroupFiber moduleFiber addCommGroupStratumFiber
  moduleStratumFiber topologicalSpaceStratumFiber topologicalSpaceStratumTotalSpace
  fiberBundleStratum
attribute [instance] addCommGroupStratumFiber moduleStratumFiber topologicalSpaceStratumFiber
  topologicalSpaceStratumTotalSpace fiberBundleStratum vectorBundleStratum
attribute [local instance] addCommGroupFiber moduleFiber

variable {B : Type b} {𝕜 : Type v} {X : Type u} {Fiber : B → X → Type w}
  [NontriviallyNormedField 𝕜] [TopologicalSpace X] [VariableRankBundle B 𝕜 X Fiber]

section Glued
variable (V : B)
/-- Linear equivalence from `Fiber V x` to `Fin (rank V x) → 𝕜` via the preferred stratum chart. -/
noncomputable def preferredStratumLinearEquiv (x : X) : Fiber V x ≃ₗ[𝕜] (Fin (rank V x) → 𝕜) :=
  (stratumFiberEquiv V ⟨x, rfl⟩).symm.trans
    ((trivializationAt (Fin (rank V x) → 𝕜) (StratumFiber V (rank V x))
      ⟨x, rfl⟩).linearEquivAt 𝕜 ⟨x, rfl⟩ (mem_baseSet_trivializationAt _ _ _))
/-- Every fibre of a variable-rank bundle has `finrank` equal to the locally constant rank. -/
@[simp] theorem finrank_fiber (x : X) : Module.finrank 𝕜 (Fiber V x) = rank V x :=
  (preferredStratumLinearEquiv V x).finrank_eq.trans (Module.finrank_fin_fun 𝕜)

/-- The disjoint union of the native stratum total spaces. -/
abbrev GluedTotalSpace := Σ n : ℕ, TotalSpace (Fin n → 𝕜) (StratumFiber V n)
/-- Projection of the disjoint union of stratum total spaces to `X`. -/
def gluedProj (p : GluedTotalSpace V) : X := p.snd.proj.val
@[simp] theorem gluedProj_mk (n : ℕ) (p : TotalSpace (Fin n → 𝕜) (StratumFiber V n)) :
    gluedProj V ⟨n, p⟩ = p.proj.val := by rfl
/-- The glued projection is continuous, since each stratum projection is continuous. -/
@[continuity, fun_prop] theorem continuous_gluedProj : Continuous (gluedProj V) :=
  continuous_sigma fun n ↦
    continuous_subtypeVal.comp (FiberBundle.continuous_proj (Fin n → 𝕜) (StratumFiber V n))
/-- The glued projection is an open map, since each rank stratum is clopen in `X`. -/
theorem isOpenMap_gluedProj : IsOpenMap (gluedProj V) :=
  isOpenMap_sigma.2 fun n ↦
    (((rank V).isLocallyConstant.isOpen_fiber n).isOpenEmbedding_subtypeVal.isOpenMap).comp
      (FiberBundle.isOpenMap_proj (Fin n → 𝕜) (StratumFiber V n))

private def totalSpaceEquiv : GluedTotalSpace V ≃ TotalSpace Unit (Fiber V) where
  toFun p := ⟨p.snd.proj.val, stratumFiberEquiv V p.snd.proj p.snd.snd⟩
  invFun p := ⟨rank V p.proj, ⟨⟨p.proj, rfl⟩, (stratumFiberEquiv V ⟨p.proj, rfl⟩).symm p.snd⟩⟩
  left_inv := fun ⟨_, ⟨⟨_, rfl⟩, _⟩⟩ ↦ by simp only [LinearEquiv.symm_apply_apply]
  right_inv := fun ⟨_, _⟩ ↦ by simp only [LinearEquiv.apply_symm_apply]
/-- Equip `TotalSpace Unit (Fiber V)` with the topology induced from the disjoint union of the
stratum bundle total spaces. -/
@[instance_reducible] def instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace Unit (Fiber V)) :=
  TopologicalSpace.induced (totalSpaceEquiv V).symm inferInstance
attribute [local instance] instTopologicalSpaceTotalSpace
/-- Reindexing the disjoint union of the stratum total spaces gives the total-space topology of `V`
over `X`. -/
def totalSpaceHomeomorph : GluedTotalSpace V ≃ₜ TotalSpace Unit (Fiber V) :=
  ((totalSpaceEquiv V).symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm
@[simp] theorem totalSpaceHomeomorph_apply (p : GluedTotalSpace V) :
    totalSpaceHomeomorph V p = ⟨p.snd.proj.val, stratumFiberEquiv V p.snd.proj p.snd.snd⟩ := by rfl
@[simp] theorem totalSpaceHomeomorph_symm_apply (p : TotalSpace Unit (Fiber V)) :
    (totalSpaceHomeomorph V).symm p =
      ⟨rank V p.proj, ⟨⟨p.proj, rfl⟩, (stratumFiberEquiv V ⟨p.proj, rfl⟩).symm p.snd⟩⟩ := by rfl

/-- The projection of the glued total space to `X` is continuous. -/
@[continuity, fun_prop] theorem continuous_proj :
    Continuous (TotalSpace.proj : TotalSpace Unit (Fiber V) → X) :=
  (continuous_gluedProj V).comp (totalSpaceHomeomorph V).symm.continuous
/-- The projection of the glued total space to `X` is an open map. -/
theorem isOpenMap_proj : IsOpenMap (TotalSpace.proj : TotalSpace Unit (Fiber V) → X) :=
  (isOpenMap_gluedProj V).comp (totalSpaceHomeomorph V).symm.isOpenMap
/-- Each stratum total space embeds openly into `TotalSpace Unit (Fiber V)`. -/
theorem isOpenEmbedding_stratum (n : ℕ) : IsOpenEmbedding
    (fun p : TotalSpace (Fin n → 𝕜) (StratumFiber V n) ↦ totalSpaceHomeomorph V ⟨n, p⟩) :=
  (totalSpaceHomeomorph V).isOpenEmbedding.comp IsOpenEmbedding.sigmaMk
/-- The image of the `n`th stratum total space is the rank-`n` part of
`TotalSpace Unit (Fiber V)`. -/
theorem range_stratum (n : ℕ) :
    Set.range (fun p : TotalSpace (Fin n → 𝕜) (StratumFiber V n) ↦ totalSpaceHomeomorph V ⟨n, p⟩) =
      {p : TotalSpace Unit (Fiber V) | rank V p.proj = n} := by
  ext ⟨x, u⟩
  refine ⟨fun ⟨q, hq⟩ ↦
    (congrArg (fun p ↦ rank V p.proj) hq).symm.trans q.proj.property, fun hp ↦ ?_⟩
  cases hp; exact ⟨⟨⟨x, rfl⟩, (stratumFiberEquiv V ⟨x, rfl⟩).symm u⟩, by
    simp only [totalSpaceHomeomorph_apply, LinearEquiv.apply_symm_apply]⟩

/-- A map into `TotalSpace Unit (Fiber V)` is continuous if and only if its restriction to each
clopen rank stratum is continuous into that stratum's native bundle total space. -/
theorem continuous_mk_iff_rankStrata {Y : Type*} [TopologicalSpace Y] {b : Y → X}
    (hb : Continuous b) (s : ∀ y, Fiber V (b y)) :
    Continuous (fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit (Fiber V))) ↔
      ∀ n : ℕ, Continuous (fun y : {y : Y // rank V (b y) = n} ↦
        (⟨⟨b y, y.property⟩, (stratumFiberEquiv V ⟨b y, y.property⟩).symm (s y)⟩ :
          TotalSpace (Fin n → 𝕜) (StratumFiber V n))) where
  mp hs n := (IsEmbedding.sigmaMk
    (σ := fun n ↦ TotalSpace (Fin n → 𝕜) (StratumFiber V n))).continuous_iff.2 <|
    ((totalSpaceHomeomorph V).symm.continuous.comp (hs.comp continuous_subtypeVal)).congr
      fun ⟨_, hy⟩ ↦ by cases hy; rfl
  mpr hs := continuous_of_cover_nhds (s := fun n : ℕ ↦ {y : Y | rank V (b y) = n})
    (fun y ↦ ⟨rank V (b y), (((rank V).isLocallyConstant.isOpen_fiber _).preimage hb).mem_nhds rfl⟩)
    fun n ↦ continuousOn_iff_continuous_domRestrict.2 <|
      ((totalSpaceHomeomorph V).continuous.comp (continuous_sigmaMk.comp (hs n))).congr
        fun y ↦ congrArg (TotalSpace.mk' Unit (b y.val))
          ((stratumFiberEquiv V ⟨b y.val, y.property⟩).apply_symm_apply (s y.val))

/-- The zero section of a variable-rank bundle is continuous. -/
@[fun_prop] theorem continuous_zeroSection :
    Continuous (fun x ↦ (⟨x, 0⟩ : TotalSpace Unit (Fiber V))) :=
  (continuous_mk_iff_rankStrata V continuous_id _).2 fun n ↦
    (Bundle.Trivialization.continuous_zeroSection 𝕜 (F := Fin n → 𝕜)
      (E := StratumFiber V n)).congr fun y ↦
        congrArg (TotalSpace.mk' (Fin n → 𝕜) y) (map_zero _).symm
/-- Sums of continuous maps over the same base map are continuous, without bounded-rank
hypotheses. -/
theorem continuous_add {Y : Type*} [TopologicalSpace Y] {b : Y → X} {s t : ∀ y, Fiber V (b y)}
    (hs : Continuous (fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit (Fiber V))))
    (ht : Continuous (fun y ↦ (⟨b y, t y⟩ : TotalSpace Unit (Fiber V)))) :
    Continuous (fun y ↦ (⟨b y, s y + t y⟩ : TotalSpace Unit (Fiber V))) := by
  have hb : Continuous b := (continuous_proj V).comp hs
  rw [continuous_mk_iff_rankStrata V hb] at hs ht ⊢
  exact fun n ↦ ((hs n).add_totalSpace 𝕜 (ht n)).congr fun y ↦
    congrArg (TotalSpace.mk' (Fin n → 𝕜) (⟨b y.val, y.property⟩ : {x : X // rank V x = n}))
      (map_add _ _ _).symm
/-- Continuous scalar multiples of maps into a variable-rank total space are continuous. -/
theorem continuous_smul {Y : Type*} [TopologicalSpace Y] {b : Y → X} {s : ∀ y, Fiber V (b y)}
    {c : Y → 𝕜} (hc : Continuous c)
    (hs : Continuous (fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit (Fiber V)))) :
    Continuous (fun y ↦ (⟨b y, c y • s y⟩ : TotalSpace Unit (Fiber V))) := by
  have hb : Continuous b := (continuous_proj V).comp hs
  rw [continuous_mk_iff_rankStrata V hb] at hs ⊢
  exact fun n ↦ ((hc.comp continuous_subtypeVal).smul_totalSpace (hs n)).congr fun y ↦
    congrArg (TotalSpace.mk' (Fin n → 𝕜) (⟨b y.val, y.property⟩ : {x : X // rank V x = n}))
      (map_smul _ _ _).symm
end Glued
attribute [local instance] instTopologicalSpaceTotalSpace

/-- Continuous section `X → {x : X // rank V x = n}` witnessing that `V` has constant rank `n`. -/
-- Expose the subtype constructor so pullback fibres over `constRankInclusion hn` reduce cleanly.
@[expose] def constRankInclusion {V : B} {n : ℕ} (hn : ∀ x, rank V x = n) :
    C(X, {x : X // rank V x = n}) := ⟨fun x ↦ ⟨x, hn x⟩, continuous_id.subtype_mk hn⟩

section ConstRank
variable (V : B) {n : ℕ} (hn : ∀ x, rank V x = n)
/-- When `V` has constant rank `n` on `X`, its glued total space is homeomorphic over `X` to the
pullback of the `n`th stratum bundle along `constRankInclusion hn`. -/
def constRankTotalSpaceHomeomorph : TotalSpace Unit (Fiber V) ≃ₜ
    TotalSpace (Fin n → 𝕜) ((⇑(constRankInclusion hn)) *ᵖ (StratumFiber V n)) where
  toFun p := ⟨p.proj, (stratumFiberEquiv V ⟨p.proj, hn p.proj⟩).symm p.snd⟩
  invFun q := ⟨q.proj, stratumFiberEquiv V ⟨q.proj, hn q.proj⟩ q.snd⟩
  left_inv := fun ⟨_, _⟩ ↦ by simp only [LinearEquiv.apply_symm_apply]
  right_inv := fun ⟨x, v⟩ ↦ TotalSpace.ext rfl
    (heq_of_eq ((stratumFiberEquiv V ⟨x, hn x⟩).symm_apply_apply v))
  continuous_toFun := by
    rw [(inducing_pullbackTotalSpaceEmbedding (Fin n → 𝕜) (StratumFiber V n)
      (constRankInclusion hn)).continuous_iff]
    exact (continuous_proj V).prodMk <|
      ((continuous_mk_iff_rankStrata V (continuous_proj V) (fun p ↦ p.snd)).1 continuous_id n).comp
        (Continuous.subtype_mk continuous_id fun p ↦ hn p.proj)
  continuous_invFun := (totalSpaceHomeomorph V).continuous.comp <| continuous_sigmaMk.comp <|
    Pullback.continuous_lift (Fin n → 𝕜) (StratumFiber V n) (constRankInclusion hn)
@[simp] theorem constRankTotalSpaceHomeomorph_apply (p : TotalSpace Unit (Fiber V)) :
    constRankTotalSpaceHomeomorph V hn p =
      ⟨p.proj, (stratumFiberEquiv V ⟨p.proj, hn p.proj⟩).symm p.snd⟩ := by rfl
@[simp] theorem constRankTotalSpaceHomeomorph_symm_apply
    (q : TotalSpace (Fin n → 𝕜) ((⇑(constRankInclusion hn)) *ᵖ (StratumFiber V n))) :
    (constRankTotalSpaceHomeomorph V hn).symm q =
      ⟨q.proj, stratumFiberEquiv V ⟨q.proj, hn q.proj⟩ q.snd⟩ := by rfl

variable {F : Type*} {E : X → Type*} [TopologicalSpace (TotalSpace F E)]
  (e : TotalSpace (Fin n → 𝕜) (StratumFiber V n) ≃ₜ TotalSpace F E) (φ : ∀ x, Fiber V x ≃ E x)
  (he : ∀ x u, e ⟨⟨x, hn x⟩, (stratumFiberEquiv V ⟨x, hn x⟩).symm u⟩ = ⟨x, φ x u⟩)
  (hesymm : ∀ x v,
    e.symm ⟨x, v⟩ = ⟨⟨x, hn x⟩, (stratumFiberEquiv V ⟨x, hn x⟩).symm ((φ x).symm v)⟩)
/-- Compare the glued total space of a constant-rank `VariableRankBundle` with an external total
space `TotalSpace F E` from a homeomorphism on the `n`th stratum total space over `Subtype.val`. -/
def totalSpaceHomeomorphOfConstStratum : TotalSpace Unit (Fiber V) ≃ₜ TotalSpace F E where
  toFun p := ⟨p.proj, φ p.proj p.snd⟩
  invFun r := ⟨r.proj, (φ r.proj).symm r.snd⟩
  left_inv := fun ⟨_, _⟩ ↦ by simp only [Equiv.symm_apply_apply]
  right_inv := fun ⟨_, _⟩ ↦ by simp only [Equiv.apply_symm_apply]
  continuous_toFun := (e.continuous.comp ((Pullback.continuous_lift (Fin n → 𝕜)
    (StratumFiber V n) ⇑(constRankInclusion hn)).comp
      (constRankTotalSpaceHomeomorph V hn).continuous)).congr fun ⟨x, u⟩ ↦ by
        dsimp only [Function.comp_apply]; rw [constRankTotalSpaceHomeomorph_apply]; exact he x u
  continuous_invFun := ((totalSpaceHomeomorph V).continuous.comp
    (continuous_sigmaMk.comp e.symm.continuous)).congr fun ⟨x, v⟩ ↦ by
      dsimp only [Function.comp_apply]; rw [hesymm x v, totalSpaceHomeomorph_apply]
      simp only [LinearEquiv.apply_symm_apply]
@[simp] theorem totalSpaceHomeomorphOfConstStratum_apply (p : TotalSpace Unit (Fiber V)) :
    totalSpaceHomeomorphOfConstStratum V hn e φ he hesymm p = ⟨p.proj, φ p.proj p.snd⟩ := by rfl
@[simp] theorem totalSpaceHomeomorphOfConstStratum_symm_apply (r : TotalSpace F E) :
    (totalSpaceHomeomorphOfConstStratum V hn e φ he hesymm).symm r =
      ⟨r.proj, (φ r.proj).symm r.snd⟩ := by rfl
end ConstRank
end VariableRankBundle
end TauCeti
