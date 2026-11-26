/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Transfer
public import TauCeti.Topology.VectorBundle.Section
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.FiniteDimensional

import TauCeti.Topology.FiberBundle.Pullback
import TauCeti.Topology.FiberBundle.Sigma
import TauCeti.Topology.LocallyConstant.Fiber
import TauCeti.Topology.VectorBundle.IsEmpty
import TauCeti.Topology.VectorBundle.Smul
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# The category of genuine finite-rank vector bundles of variable rank

Mathlib's `VectorBundle 𝕜 F E` fixes a single model fibre `F` over the whole base, whereas
`TauCeti.FiniteRankAtlas 𝕜 X` allows locally constant (possibly unbounded) rank across clopen
strata at the cost of replacing fibres by coordinate spaces `Fin n → 𝕜` in the scalar universe.
`TauCeti.FiniteRankBundle.{w} 𝕜 X` retains genuine `Type w` `𝕜`-vector-space fibres `E.Fiber x`
together with a locally constant rank `rank : LocallyConstant X ℕ` and native
`VectorBundle 𝕜 (Fin n → 𝕜)` structures on each clopen rank stratum `{x : X // rank x = n}`.

Each fibre inherits `IsTopologicalAddGroup`, `ContinuousSMul 𝕜`, and `FiniteDimensional 𝕜` with
`Module.finrank 𝕜 (E.Fiber x) = E.rank x` (`FiniteRankBundle.finrank_fiber`). Because
`Bundle.TotalSpace` takes a phantom model-fibre parameter that is unused once fibre dimensions vary
across base points, the global total space is written `TotalSpace Unit E.Fiber` with `Unit` as that
placeholder and carries the disjoint-union topology of the stratum total spaces via
`FiniteRankBundle.totalSpaceHomeomorph`.

Adapting the glued `TotalSpace Unit` topology, stratum continuity criterion, preadditive morphism
group, evaluation functors, and rank-invariance argument from `TauCeti.FiniteRankAtlas`
(`TauCeti.Topology.VectorBundle.FiniteRank.Atlas.{Basic,Category,Preadditive}`), we equip
`FiniteRankBundle.{w} 𝕜 X` with its preadditive category structure, `HasZeroObject`
(`FiniteRankBundle.zero`), forgetful/evaluation functors `totalSpaceFunctor` and `fiberFunctor x`,
constant-rank embedding `ofBundle` (`ofBundleHomeomorph`), and stratumwise bundle assembly
`ofBundles` (`ofBundlesHomeomorph`).
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits Topology

namespace TauCeti

universe w w' u v

variable (𝕜 : Type v) [NontriviallyNormedField 𝕜] (X : Type u) [TopologicalSpace X]

/-- A genuine finite-rank topological vector bundle of locally constant (possibly unbounded) rank
over `X`, with fibres in `Type w`. -/
structure FiniteRankBundle : Type (max u v (w + 1)) where
  /-- The locally constant, not necessarily bounded, fibre dimension. -/
  rank : LocallyConstant X ℕ
  /-- The genuine vector-space fibre over each base point. -/
  Fiber : X → Type w
  [addCommGroupFiber : ∀ x, AddCommGroup (Fiber x)]
  [moduleFiber : ∀ x, Module 𝕜 (Fiber x)]
  [topologicalSpaceFiber : ∀ x, TopologicalSpace (Fiber x)]
  [topologicalSpaceStratum :
    ∀ n : ℕ, TopologicalSpace (TotalSpace (Fin n → 𝕜) fun x : {x : X // rank x = n} ↦ Fiber x.val)]
  [fiberBundleStratum :
    ∀ n : ℕ, FiberBundle (Fin n → 𝕜) fun x : {x : X // rank x = n} ↦ Fiber x.val]
  [vectorBundleStratum :
    ∀ n : ℕ, VectorBundle 𝕜 (Fin n → 𝕜) fun x : {x : X // rank x = n} ↦ Fiber x.val]

namespace FiniteRankBundle

attribute [instance] addCommGroupFiber moduleFiber topologicalSpaceFiber
  topologicalSpaceStratum fiberBundleStratum vectorBundleStratum

variable {𝕜 X} (E : FiniteRankBundle.{w} 𝕜 X)

/-- The fibre family of `E` restricted to its `n`th clopen rank stratum. -/
abbrev StratumFiber (n : ℕ) (x : {x : X // E.rank x = n}) : Type w := E.Fiber x.val

/-- Preferred continuous linear equivalence between `E.Fiber x` and `Fin (E.rank x) → 𝕜`. -/
noncomputable def fiberContinuousLinearEquiv (x : X) : E.Fiber x ≃L[𝕜] (Fin (E.rank x) → 𝕜) :=
  VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E.rank x) → 𝕜) (E.StratumFiber (E.rank x)) ⟨x, rfl⟩

/-- The preferred fibre equivalence is the preferred trivialization of the rank stratum. -/
theorem fiberContinuousLinearEquiv_apply (x : X) (v : E.Fiber x) :
    E.fiberContinuousLinearEquiv x v =
      (trivializationAt (Fin (E.rank x) → 𝕜) (E.StratumFiber (E.rank x)) ⟨x, rfl⟩
        ⟨⟨x, rfl⟩, v⟩).2 := (rfl)

/-- The inverse of the preferred fibre equivalence is the inverse of the preferred trivialization
of the rank stratum. -/
theorem fiberContinuousLinearEquiv_symm_apply (x : X) (v : Fin (E.rank x) → 𝕜) :
    (E.fiberContinuousLinearEquiv x).symm v =
      (trivializationAt (Fin (E.rank x) → 𝕜) (E.StratumFiber (E.rank x)) ⟨x, rfl⟩).symm
        ⟨x, rfl⟩ v := (rfl)

/-- Each fibre `E.Fiber x` is a topological additive group via its stratum vector bundle chart. -/
instance (x : X) : IsTopologicalAddGroup (E.Fiber x) :=
  VectorBundle.isTopologicalAddGroup 𝕜 (Fin (E.rank x) → 𝕜) (E.StratumFiber (E.rank x)) ⟨x, rfl⟩

/-- Scalar multiplication on each fibre `E.Fiber x` is continuous. -/
instance (x : X) : ContinuousSMul 𝕜 (E.Fiber x) :=
  VectorBundle.continuousSMul 𝕜 (Fin (E.rank x) → 𝕜) (E.StratumFiber (E.rank x)) ⟨x, rfl⟩

/-- Each fibre `E.Fiber x` is finite-dimensional over `𝕜`. -/
instance (x : X) : FiniteDimensional 𝕜 (E.Fiber x) :=
  VectorBundle.finiteDimensional 𝕜 (Fin (E.rank x) → 𝕜) (E.StratumFiber (E.rank x)) ⟨x, rfl⟩

/-- The `𝕜`-dimension of the fibre `E.Fiber x` equals the bundle rank `E.rank x`. -/
@[simp] theorem finrank_fiber (x : X) : Module.finrank 𝕜 (E.Fiber x) = E.rank x :=
  (VectorBundle.finrank_eq 𝕜 (Fin (E.rank x) → 𝕜) (E.StratumFiber (E.rank x)) ⟨x, rfl⟩).trans
    (Module.finrank_fin_fun 𝕜)

/-! ### Global total-space topology and continuity criterion -/

/-- The disjoint union of the native stratum bundle total spaces. -/
abbrev GluedTotalSpace := Σ n : ℕ, TotalSpace (Fin n → 𝕜) (E.StratumFiber n)

/-- Projection of the disjoint union of stratum total spaces to `X`. -/
def gluedProj (p : E.GluedTotalSpace) : X := p.2.proj.val

@[simp] theorem gluedProj_mk (n : ℕ) (p : TotalSpace (Fin n → 𝕜) (E.StratumFiber n)) :
    E.gluedProj ⟨n, p⟩ = p.proj.val := (rfl)

/-- The projection from the glued disjoint union of stratum total spaces to `X` is continuous. -/
@[continuity, fun_prop] theorem continuous_gluedProj : Continuous E.gluedProj :=
  continuous_sigma fun n ↦
    continuous_subtypeVal.comp (FiberBundle.continuous_proj (Fin n → 𝕜) (E.StratumFiber n))

/-- The projection from the glued disjoint union of stratum total spaces to `X` is an open map. -/
theorem isOpenMap_gluedProj : IsOpenMap E.gluedProj :=
  isOpenMap_sigma.2 fun n ↦
    (E.rank.isLocallyConstant.isOpen_fiber n).isOpenEmbedding_subtypeVal.isOpenMap.comp
      (FiberBundle.isOpenMap_proj (Fin n → 𝕜) (E.StratumFiber n))

private def totalSpaceEquiv : E.GluedTotalSpace ≃ TotalSpace Unit E.Fiber where
  toFun p := ⟨p.2.proj.val, p.2.snd⟩
  invFun p := ⟨E.rank p.proj, ⟨⟨p.proj, rfl⟩, p.snd⟩⟩
  left_inv := fun ⟨_, ⟨⟨_, hx⟩, _⟩⟩ ↦ by cases hx; rfl
  right_inv p := by cases p; rfl

/-- The global total space `TotalSpace Unit E.Fiber` carries the topology induced from the disjoint
union `E.GluedTotalSpace` of the native stratum bundle total spaces. -/
instance : TopologicalSpace (TotalSpace Unit E.Fiber) :=
  TopologicalSpace.induced
    (fun p : TotalSpace Unit E.Fiber ↦
      (⟨E.rank p.proj, ⟨⟨p.proj, rfl⟩, p.snd⟩⟩ : E.GluedTotalSpace))
    inferInstance

/-- Homeomorphism between `E.GluedTotalSpace` and `TotalSpace Unit E.Fiber`. -/
def totalSpaceHomeomorph : E.GluedTotalSpace ≃ₜ TotalSpace Unit E.Fiber :=
  (E.totalSpaceEquiv.symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm

@[simp] theorem totalSpaceHomeomorph_apply (p : E.GluedTotalSpace) :
    E.totalSpaceHomeomorph p = ⟨p.2.proj.val, p.2.snd⟩ := (rfl)

@[simp] theorem totalSpaceHomeomorph_symm_apply (p : TotalSpace Unit E.Fiber) :
    E.totalSpaceHomeomorph.symm p = ⟨E.rank p.proj, ⟨⟨p.proj, rfl⟩, p.snd⟩⟩ := (rfl)

/-- The bundle projection `TotalSpace Unit E.Fiber → X` is continuous. -/
@[continuity, fun_prop] theorem continuous_proj :
    Continuous (TotalSpace.proj : TotalSpace Unit E.Fiber → X) :=
  E.continuous_gluedProj.comp E.totalSpaceHomeomorph.symm.continuous

/-- The bundle projection `TotalSpace Unit E.Fiber → X` is an open map. -/
theorem isOpenMap_proj : IsOpenMap (TotalSpace.proj : TotalSpace Unit E.Fiber → X) :=
  E.isOpenMap_gluedProj.comp E.totalSpaceHomeomorph.symm.isOpenMap

/-- Each stratum vector-bundle total space embeds openly into `TotalSpace Unit E.Fiber`. -/
theorem isOpenEmbedding_stratum (n : ℕ) :
    IsOpenEmbedding (fun p : TotalSpace (Fin n → 𝕜) (E.StratumFiber n) ↦
      E.totalSpaceHomeomorph ⟨n, p⟩) :=
  E.totalSpaceHomeomorph.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk

/-- The image of the `n`th stratum total space in `TotalSpace Unit E.Fiber` is the rank-`n`
locus. -/
theorem range_stratum (n : ℕ) :
    Set.range (fun p : TotalSpace (Fin n → 𝕜) (E.StratumFiber n) ↦ E.totalSpaceHomeomorph ⟨n, p⟩) =
      {p : TotalSpace Unit E.Fiber | E.rank p.proj = n} := by
  ext p; refine ⟨by rintro ⟨q, rfl⟩; exact q.proj.property, fun hp ↦ ?_⟩
  rcases p with ⟨x, v⟩; cases hp; exact ⟨⟨⟨x, rfl⟩, v⟩, rfl⟩

/-- Inclusion of `E.Fiber x` into `TotalSpace Unit E.Fiber` is inducing. -/
theorem isInducing_mk (x : X) :
    IsInducing (fun v : E.Fiber x ↦ (⟨x, v⟩ : TotalSpace Unit E.Fiber)) :=
  FiberBundle.isInducing_of_comp_eq_sigmaMk_totalSpaceMk (E.rank x) ⟨x, rfl⟩
    E.totalSpaceHomeomorph.symm.isInducing fun v ↦ E.totalSpaceHomeomorph_symm_apply ⟨x, v⟩

section Continuity

variable {Y : Type*} [TopologicalSpace Y] {b : Y → X}

/-- A map into `TotalSpace Unit E.Fiber` over `b` is continuous iff its restriction to each clopen
rank stratum is continuous into the corresponding stratum vector-bundle total space. -/
theorem continuous_mk_iff_rankStrata (hb : Continuous b) (s : ∀ y, E.Fiber (b y)) :
    Continuous (fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit E.Fiber)) ↔
      ∀ n : ℕ, Continuous (fun y : {y : Y // E.rank (b y) = n} ↦
        (⟨⟨b y.val, y.property⟩, s y.val⟩ : TotalSpace (Fin n → 𝕜) (E.StratumFiber n))) := by
  rw [E.totalSpaceHomeomorph.symm.isInducing.continuous_iff]
  exact (E.rank.isLocallyConstant.comp_continuous hb).continuous_iff_of_eq_sigmaMk _
    fun n ⟨y, hy⟩ ↦ by cases hy; rfl

/-- The zero section of a variable-rank vector bundle is continuous. -/
@[fun_prop] theorem continuous_zeroSection :
    Continuous (fun x ↦ (⟨x, 0⟩ : TotalSpace Unit E.Fiber)) :=
  (E.continuous_mk_iff_rankStrata continuous_id _).2 fun n ↦
    (Bundle.Trivialization.continuous_zeroSection 𝕜
      (F := Fin n → 𝕜) (E := E.StratumFiber n)).congr fun _ ↦ rfl

/-- Fibrewise addition of two continuous maps into `TotalSpace Unit E.Fiber` over the same base map
is continuous. -/
theorem continuous_add {s t : ∀ y, E.Fiber (b y)}
    (hs : Continuous fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit E.Fiber))
    (ht : Continuous fun y ↦ (⟨b y, t y⟩ : TotalSpace Unit E.Fiber)) :
    Continuous fun y ↦ (⟨b y, s y + t y⟩ : TotalSpace Unit E.Fiber) := by
  have hb : Continuous b := E.continuous_proj.comp hs
  rw [E.continuous_mk_iff_rankStrata hb] at hs ht ⊢
  exact fun n ↦ (hs n).add_totalSpace 𝕜 (ht n)

/-- Fibrewise scalar multiplication of a continuous map into `TotalSpace Unit E.Fiber` by a
continuous scalar function is continuous. -/
theorem continuous_smul {s : ∀ y, E.Fiber (b y)} {c : Y → 𝕜} (hc : Continuous c)
    (hs : Continuous fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit E.Fiber)) :
    Continuous fun y ↦ (⟨b y, c y • s y⟩ : TotalSpace Unit E.Fiber) := by
  have hb : Continuous b := E.continuous_proj.comp hs
  rw [E.continuous_mk_iff_rankStrata hb] at hs ⊢
  exact fun n ↦ (hc.comp continuous_subtypeVal).smul_totalSpace (hs n)

end Continuity

/-! ### Morphisms, preadditive category structure, and evaluation functors -/

/-- A morphism of genuine variable-rank vector bundles is a family of `𝕜`-linear maps on the fibres
whose induced map on global total spaces is continuous. -/
@[ext]
structure Hom (E F : FiniteRankBundle.{w} 𝕜 X) where
  /-- The linear map on each fibre. -/
  fiberMap : ∀ x : X, E.Fiber x →ₗ[𝕜] F.Fiber x
  /-- Continuity on the global total spaces. -/
  continuous_totalSpaceMap : Continuous fun p : TotalSpace Unit E.Fiber ↦
    (⟨p.proj, fiberMap p.proj p.snd⟩ : TotalSpace Unit F.Fiber)

variable {E} {F G : FiniteRankBundle.{w} 𝕜 X}

namespace Hom

/-- The bundled continuous map of global total spaces induced by a bundle morphism. -/
def totalSpaceMap (f : Hom E F) : C(TotalSpace Unit E.Fiber, TotalSpace Unit F.Fiber) :=
  ⟨_, f.continuous_totalSpaceMap⟩

@[simp] theorem totalSpaceMap_mk (f : Hom E F) (x : X) (v : E.Fiber x) :
    f.totalSpaceMap ⟨x, v⟩ = ⟨x, f.fiberMap x v⟩ := (rfl)

@[simp] theorem proj_totalSpaceMap (f : Hom E F) (p : TotalSpace Unit E.Fiber) :
    (f.totalSpaceMap p).proj = p.proj := (rfl)

/-- Every fibre map of a morphism of variable-rank vector bundles is continuous. -/
@[continuity, fun_prop] theorem continuous_fiberMap (f : Hom E F) (x : X) :
    Continuous (f.fiberMap x) :=
  (F.isInducing_mk x).continuous_iff.2 <|
    f.continuous_totalSpaceMap.comp (E.isInducing_mk x).continuous

/-- The continuous linear map on the fibre at `x` induced by a bundle morphism. -/
def fiberCLM (f : Hom E F) (x : X) : E.Fiber x →L[𝕜] F.Fiber x :=
  ⟨f.fiberMap x, f.continuous_fiberMap x⟩

@[simp] theorem coe_fiberCLM (f : Hom E F) (x : X) :
    (f.fiberCLM x : E.Fiber x →ₗ[𝕜] F.Fiber x) = f.fiberMap x := (rfl)

@[simp] theorem fiberCLM_apply (f : Hom E F) (x : X) (v : E.Fiber x) :
    f.fiberCLM x v = f.fiberMap x v := (rfl)

end Hom

/-- Variable-rank vector bundles over `X` with fibres in `Type w` form a category under continuous
fibrewise `𝕜`-linear bundle maps. -/
instance : Category (FiniteRankBundle.{w} 𝕜 X) where
  Hom := Hom
  id _ := ⟨fun _ ↦ LinearMap.id, continuous_id⟩
  comp f g := ⟨fun x ↦ (g.fiberMap x).comp (f.fiberMap x),
    g.continuous_totalSpaceMap.comp f.continuous_totalSpaceMap⟩

/-- Morphisms in `FiniteRankBundle.{w} 𝕜 X` are determined by their linear maps on every fibre. -/
@[ext] theorem hom_ext {f g : E ⟶ F} (h : ∀ x, f.fiberMap x = g.fiberMap x) : f = g :=
  Hom.ext (funext h)

@[simp] theorem fiberMap_id (E : FiniteRankBundle.{w} 𝕜 X) (x : X) :
    (𝟙 E : E ⟶ E).fiberMap x = LinearMap.id := (rfl)

@[simp] theorem fiberMap_comp (f : E ⟶ F) (g : F ⟶ G) (x : X) :
    (f ≫ g).fiberMap x = (g.fiberMap x).comp (f.fiberMap x) := (rfl)

@[simp] theorem fiberCLM_id (E : FiniteRankBundle.{w} 𝕜 X) (x : X) :
    Hom.fiberCLM (𝟙 E) x = ContinuousLinearMap.id 𝕜 (E.Fiber x) := (rfl)

@[simp] theorem fiberCLM_comp (f : E ⟶ F) (g : F ⟶ G) (x : X) :
    Hom.fiberCLM (f ≫ g) x = (g.fiberCLM x).comp (f.fiberCLM x) := (rfl)

@[simp] theorem totalSpaceMap_id (E : FiniteRankBundle.{w} 𝕜 X) :
    (𝟙 E : E ⟶ E).totalSpaceMap = ContinuousMap.id _ := (rfl)

@[simp] theorem totalSpaceMap_comp (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).totalSpaceMap = g.totalSpaceMap.comp f.totalSpaceMap := (rfl)

/-- Passing from a bundle morphism to its induced continuous map on global total spaces is
injective. -/
theorem totalSpaceMap_injective : Function.Injective (Hom.totalSpaceMap (E := E) (F := F)) :=
  fun _ _ h ↦ hom_ext fun x ↦ LinearMap.ext fun v ↦
    TotalSpace.mk_inj.mp (congrArg (fun k ↦ k ⟨x, v⟩) h)

namespace Hom

/-- The zero morphism between variable-rank vector bundles sends every fibre vector to `0`. -/
instance : Zero (E ⟶ F) := ⟨⟨fun _ ↦ 0, F.continuous_zeroSection.comp E.continuous_proj⟩⟩

/-- Pointwise addition of morphisms of variable-rank vector bundles. -/
instance : Add (E ⟶ F) := ⟨fun f g ↦ ⟨fun x ↦ f.fiberMap x + g.fiberMap x,
  F.continuous_add f.continuous_totalSpaceMap g.continuous_totalSpaceMap⟩⟩

/-- Pointwise negation of a morphism of variable-rank vector bundles. -/
instance : Neg (E ⟶ F) := ⟨fun f ↦ ⟨fun x ↦ -f.fiberMap x, by
  simpa only [neg_one_smul, LinearMap.neg_apply] using
    F.continuous_smul (continuous_const (y := (-1 : 𝕜))) f.continuous_totalSpaceMap⟩⟩

/-- Pointwise subtraction of morphisms of variable-rank vector bundles. -/
instance : Sub (E ⟶ F) := ⟨fun f g ↦ f + -g⟩

/-- Pointwise `ℕ`-scalar multiplication on morphisms of variable-rank vector bundles. -/
instance : SMul ℕ (E ⟶ F) := ⟨fun n f ↦ ⟨fun x ↦ n • f.fiberMap x, by
  simpa only [Nat.cast_smul_eq_nsmul, LinearMap.smul_apply] using
    F.continuous_smul (continuous_const (y := (n : 𝕜))) f.continuous_totalSpaceMap⟩⟩

/-- Pointwise `ℤ`-scalar multiplication on morphisms of variable-rank vector bundles. -/
instance : SMul ℤ (E ⟶ F) := ⟨fun n f ↦ ⟨fun x ↦ n • f.fiberMap x, by
  simpa only [Int.cast_smul_eq_zsmul, LinearMap.smul_apply] using
    F.continuous_smul (continuous_const (y := (n : 𝕜))) f.continuous_totalSpaceMap⟩⟩

/-- Morphisms between two variable-rank vector bundles form an additive commutative group under
pointwise operations on fibres. -/
instance : AddCommGroup (E ⟶ F) :=
  Function.Injective.addCommGroup Hom.fiberMap (fun _ _ h ↦ Hom.ext h) rfl (fun _ _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ _ ↦ funext fun _ ↦ (sub_eq_add_neg _ _).symm) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)

end Hom

/-- Pointwise addition of fibre maps makes `FiniteRankBundle.{w} 𝕜 X` a preadditive category. -/
instance : Preadditive (FiniteRankBundle.{w} 𝕜 X) where
  add_comp _ _ _ _ _ h := hom_ext fun x ↦ LinearMap.ext fun _ ↦ (h.fiberMap x).map_add _ _
  comp_add _ _ _ _ _ _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

@[simp] theorem fiberMap_zero (x : X) : (0 : E ⟶ F).fiberMap x = 0 := (rfl)

@[simp] theorem fiberMap_add (f g : E ⟶ F) (x : X) :
    (f + g).fiberMap x = f.fiberMap x + g.fiberMap x := (rfl)

@[simp] theorem fiberMap_neg (f : E ⟶ F) (x : X) : (-f).fiberMap x = -f.fiberMap x := (rfl)

@[simp] theorem fiberMap_sub (f g : E ⟶ F) (x : X) :
    (f - g).fiberMap x = f.fiberMap x - g.fiberMap x := by
  simp only [sub_eq_add_neg, fiberMap_add, fiberMap_neg]

@[simp] theorem fiberMap_nsmul (n : ℕ) (f : E ⟶ F) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := (rfl)

@[simp] theorem fiberMap_zsmul (n : ℤ) (f : E ⟶ F) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := (rfl)

@[simp] theorem fiberCLM_zero (x : X) : Hom.fiberCLM (0 : E ⟶ F) x = 0 := (rfl)

@[simp] theorem fiberCLM_add (f g : E ⟶ F) (x : X) :
    Hom.fiberCLM (f + g) x = f.fiberCLM x + g.fiberCLM x := (rfl)

@[simp] theorem fiberCLM_neg (f : E ⟶ F) (x : X) :
    Hom.fiberCLM (-f) x = -f.fiberCLM x := (rfl)

@[simp] theorem fiberCLM_sub (f g : E ⟶ F) (x : X) :
    Hom.fiberCLM (f - g) x = f.fiberCLM x - g.fiberCLM x := by
  ext; simp

@[simp] theorem fiberCLM_nsmul (n : ℕ) (f : E ⟶ F) (x : X) :
    Hom.fiberCLM (n • f) x = n • f.fiberCLM x := (rfl)

@[simp] theorem fiberCLM_zsmul (n : ℤ) (f : E ⟶ F) (x : X) :
    Hom.fiberCLM (n • f) x = n • f.fiberCLM x := (rfl)

/-- Forgetful functor sending a genuine variable-rank bundle to its global total space. -/
def totalSpaceFunctor : FiniteRankBundle.{w} 𝕜 X ⥤ TopCat.{max u w} where
  obj E := TopCat.of (TotalSpace Unit E.Fiber)
  map f := TopCat.ofHom f.totalSpaceMap

@[simp] theorem totalSpaceFunctor_obj (E : FiniteRankBundle.{w} 𝕜 X) :
    totalSpaceFunctor.obj E = TopCat.of (TotalSpace Unit E.Fiber) := (rfl)

@[simp] theorem totalSpaceFunctor_map (f : E ⟶ F) :
    totalSpaceFunctor.map f =
      eqToHom (totalSpaceFunctor_obj E) ≫ TopCat.ofHom f.totalSpaceMap ≫
        eqToHom (totalSpaceFunctor_obj F).symm :=
  (rfl)

/-- `totalSpaceFunctor` is faithful because bundle morphisms act injectively via total spaces. -/
instance : (totalSpaceFunctor.{w} (𝕜 := 𝕜) (X := X)).Faithful where
  map_injective {E F} f g h := by
    rw [totalSpaceFunctor_map, totalSpaceFunctor_map] at h
    exact totalSpaceMap_injective <| congrArg TopCat.Hom.hom <|
      (cancel_mono (eqToHom (totalSpaceFunctor_obj F).symm)).1 <|
        (cancel_epi (eqToHom (totalSpaceFunctor_obj E))).1 h

/-- Additive evaluation functor sending a genuine variable-rank bundle to its fibre at `x`. -/
def fiberFunctor (x : X) : FiniteRankBundle.{w} 𝕜 X ⥤ ModuleCat.{w} 𝕜 where
  obj E := ModuleCat.of 𝕜 (E.Fiber x)
  map f := ModuleCat.ofHom (f.fiberMap x)

@[simp] theorem fiberFunctor_obj (x : X) (E : FiniteRankBundle.{w} 𝕜 X) :
    (fiberFunctor x).obj E = ModuleCat.of 𝕜 (E.Fiber x) := (rfl)

@[simp] theorem fiberFunctor_map (x : X) (f : E ⟶ F) :
    (fiberFunctor x).map f =
      eqToHom (fiberFunctor_obj x E) ≫ ModuleCat.ofHom (f.fiberMap x) ≫
        eqToHom (fiberFunctor_obj x F).symm :=
  (rfl)

/-- `fiberFunctor x` preserves addition of bundle morphisms. -/
instance (x : X) : (fiberFunctor.{w} (𝕜 := 𝕜) (X := X) x).Additive where
  map_add {E F f g} := by
    simp only [fiberFunctor_map, fiberMap_add, ModuleCat.ofHom_add, Preadditive.comp_add,
      Preadditive.add_comp]

/-- Construct an isomorphism in `FiniteRankBundle.{w} 𝕜 X` from fibrewise linear equivalences with
continuous forward and inverse total-space maps. -/
def isoMk (e : ∀ x, E.Fiber x ≃ₗ[𝕜] F.Fiber x)
    (h : Continuous fun p : TotalSpace Unit E.Fiber ↦
      (⟨p.proj, e p.proj p.snd⟩ : TotalSpace Unit F.Fiber))
    (h' : Continuous fun p : TotalSpace Unit F.Fiber ↦
      (⟨p.proj, (e p.proj).symm p.snd⟩ : TotalSpace Unit E.Fiber)) : E ≅ F where
  hom := ⟨fun x ↦ (e x).toLinearMap, h⟩
  inv := ⟨fun x ↦ (e x).symm.toLinearMap, h'⟩
  hom_inv_id := hom_ext fun x ↦ LinearMap.ext (e x).symm_apply_apply
  inv_hom_id := hom_ext fun x ↦ LinearMap.ext (e x).apply_symm_apply

@[simp] theorem fiberMap_isoMk_hom (e : ∀ x, E.Fiber x ≃ₗ[𝕜] F.Fiber x) (h h') (x : X) :
    (isoMk e h h').hom.fiberMap x = (e x).toLinearMap := (rfl)

@[simp] theorem fiberMap_isoMk_inv (e : ∀ x, E.Fiber x ≃ₗ[𝕜] F.Fiber x) (h h') (x : X) :
    (isoMk e h h').inv.fiberMap x = (e x).symm.toLinearMap := (rfl)

/-! ### Constant-rank genuine vector bundles and zero object -/

section OfBundle

variable (𝕜) (n : ℕ) (V : X → Type w)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace (Fin n → 𝕜) V)]
  [FiberBundle (Fin n → 𝕜) V] [VectorBundle 𝕜 (Fin n → 𝕜) V]

/-- Induced topology on the `m`th rank stratum of a constant-rank bundle `V` of rank `n`. -/
@[instance_reducible]
def constStratumTopology (m : ℕ) :
    TopologicalSpace
      (TotalSpace (Fin m → 𝕜) fun x : {x : X // (LocallyConstant.const X n) x = m} ↦ V x.val) :=
  TopologicalSpace.induced
    (fun p : TotalSpace (Fin m → 𝕜)
      (fun x : {x : X // (LocallyConstant.const X n) x = m} ↦ V x.val) ↦
      (⟨p.proj.val, p.snd⟩ : TotalSpace (Fin n → 𝕜) V)) inferInstance

private abbrev constStratumInclusion :
    C({x : X // (LocallyConstant.const X n) x = n}, X) :=
  ⟨Subtype.val, continuous_subtypeVal⟩

omit [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 (Fin n → 𝕜) V] in
private theorem isInducing_constStratum_pullback :
    letI := constStratumTopology 𝕜 n V n
    IsInducing (fun p : TotalSpace (Fin n → 𝕜)
        (fun x : {x : X // (LocallyConstant.const X n) x = n} ↦ V x.val) ↦
      (⟨p.proj, p.snd⟩ : TotalSpace (Fin n → 𝕜) ((constStratumInclusion n : _ → X) *ᵖ V))) :=
  letI := constStratumTopology 𝕜 n V n
  ((Bundle.Pullback.isInducing_lift (F := Fin n → 𝕜) (E := V)
    (⟨rfl⟩ : IsInducing (constStratumInclusion n : _ → X))).of_comp_iff
    (f := fun p : TotalSpace (Fin n → 𝕜)
        (fun x : {x : X // (LocallyConstant.const X n) x = n} ↦ V x.val) ↦
      (⟨p.proj, p.snd⟩ : TotalSpace (Fin n → 𝕜) ((constStratumInclusion n : _ → X) *ᵖ V)))).mp ⟨rfl⟩

/-- `FiberBundle` structure on the `m`th rank stratum of a constant-rank bundle `V` of rank `n`. -/
@[instance_reducible]
noncomputable def constStratumFiberBundle (m : ℕ) :
    letI := constStratumTopology 𝕜 n V m
    FiberBundle (Fin m → 𝕜) fun x : {x : X // (LocallyConstant.const X n) x = m} ↦ V x.val :=
  if h : n = m then
    h ▸ (letI := constStratumTopology 𝕜 n V n
      FiberBundle.ofContinuousLinearEquiv (Fin n → 𝕜)
        (E := (constStratumInclusion n : _ → X) *ᵖ V)
        (fun x ↦ ContinuousLinearEquiv.refl 𝕜 (V x.val)) (isInducing_constStratum_pullback 𝕜 n V))
  else
    letI := constStratumTopology 𝕜 n V m
    letI : IsEmpty {x : X // (LocallyConstant.const X n) x = m} := ⟨fun x ↦ h x.property⟩
    FiberBundle.ofIsEmpty (Fin m → 𝕜)
      fun x : {x : X // (LocallyConstant.const X n) x = m} ↦ V x.val

omit [VectorBundle 𝕜 (Fin n → 𝕜) V] in
private theorem constStratumFiberBundle_self :
    constStratumFiberBundle 𝕜 n V n =
      (letI := constStratumTopology 𝕜 n V n
       FiberBundle.ofContinuousLinearEquiv (Fin n → 𝕜)
         (E := (constStratumInclusion n : _ → X) *ᵖ V)
         (fun x ↦ ContinuousLinearEquiv.refl 𝕜 (V x.val))
         (isInducing_constStratum_pullback 𝕜 n V)) :=
  dite_eq_left rfl

/-- `VectorBundle` structure on the `m`th rank stratum of a constant-rank bundle `V` of rank `n`. -/
theorem constStratumVectorBundle (m : ℕ) :
    letI := constStratumTopology 𝕜 n V m
    letI := constStratumFiberBundle 𝕜 n V m
    VectorBundle 𝕜 (Fin m → 𝕜) fun x : {x : X // (LocallyConstant.const X n) x = m} ↦ V x.val := by
  let := constStratumTopology 𝕜 n V m
  by_cases h : n = m
  · subst h
    rw [constStratumFiberBundle_self]
    exact VectorBundle.ofContinuousLinearEquiv (Fin n → 𝕜)
      (E := (constStratumInclusion n : _ → X) *ᵖ V)
      (fun x ↦ ContinuousLinearEquiv.refl 𝕜 (V x.val)) (isInducing_constStratum_pullback 𝕜 n V)
  · have : IsEmpty {x : X // (LocallyConstant.const X n) x = m} := ⟨fun x ↦ h x.property⟩
    let := constStratumFiberBundle 𝕜 n V m
    exact VectorBundle.ofIsEmpty 𝕜 (Fin m → 𝕜) _

/-- Package a constant-rank `VectorBundle 𝕜 (Fin n → 𝕜) V` as an object of
`FiniteRankBundle.{w} 𝕜 X`. -/
@[expose]
noncomputable def ofBundle : FiniteRankBundle.{w} 𝕜 X where
  rank := LocallyConstant.const X n
  Fiber := V
  topologicalSpaceStratum := constStratumTopology 𝕜 n V
  fiberBundleStratum := constStratumFiberBundle 𝕜 n V
  vectorBundleStratum := constStratumVectorBundle 𝕜 n V

@[simp] theorem rank_ofBundle : (ofBundle 𝕜 n V).rank = LocallyConstant.const X n := (rfl)

@[simp] theorem fiber_ofBundle (x : X) : (ofBundle 𝕜 n V).Fiber x = V x := (rfl)

private theorem fiberBundleStratum_ofBundle_self :
    (ofBundle 𝕜 n V).fiberBundleStratum n =
      (letI := constStratumTopology 𝕜 n V n
       FiberBundle.ofContinuousLinearEquiv (Fin n → 𝕜)
         (E := (constStratumInclusion n : _ → X) *ᵖ V)
         (fun x ↦ ContinuousLinearEquiv.refl 𝕜 (V x.val))
         (isInducing_constStratum_pullback 𝕜 n V)) :=
  constStratumFiberBundle_self 𝕜 n V

private theorem trivializationAt_ofBundle_self
    (b : {x : X // (ofBundle 𝕜 n V).rank x = n}) :
    trivializationAt (Fin n → 𝕜) ((ofBundle 𝕜 n V).StratumFiber n) b =
      (letI := constStratumTopology 𝕜 n V n
       (trivializationAt (Fin n → 𝕜) ((constStratumInclusion n : _ → X) *ᵖ V) ⟨b.val, b.property⟩)
         |>.compContinuousLinearEquiv (fun x ↦ ContinuousLinearEquiv.refl 𝕜 (V x.val))
           (isInducing_constStratum_pullback 𝕜 n V)) := by
  rw [fiberBundleStratum_ofBundle_self]
  let := constStratumTopology 𝕜 n V n
  exact FiberBundle.trivializationAt_ofContinuousLinearEquiv (Fin n → 𝕜)
    (E := (constStratumInclusion n : _ → X) *ᵖ V)
    (fun x ↦ ContinuousLinearEquiv.refl 𝕜 (V x.val))
    (isInducing_constStratum_pullback 𝕜 n V) ⟨b.val, b.property⟩

/-- On the `n`th rank stratum of `ofBundle 𝕜 n V`, the preferred trivialization's fibrewise inverse
at `b` agrees with that of `V` at `b.1`. -/
@[simp] theorem trivializationAt_ofBundle_symm
    (b : {x : X // (ofBundle 𝕜 n V).rank x = n}) (v : Fin n → 𝕜) :
    (trivializationAt (Fin n → 𝕜) ((ofBundle 𝕜 n V).StratumFiber n) b).symm b v =
      (trivializationAt (Fin n → 𝕜) V b.val).symm b.val v := by
  rw [trivializationAt_ofBundle_self]
  refine (letI := constStratumTopology 𝕜 n V n
    Trivialization.compContinuousLinearEquiv_symm
      (trivializationAt (Fin n → 𝕜) ((constStratumInclusion n : _ → X) *ᵖ V) ⟨b.val, b.property⟩)
      (fun x ↦ ContinuousLinearEquiv.refl 𝕜 (V x.val))
      (isInducing_constStratum_pullback 𝕜 n V)
      (FiberBundle.mem_baseSet_trivializationAt (Fin n → 𝕜)
        ((constStratumInclusion n : _ → X) *ᵖ V) ⟨b.val, b.property⟩) v).trans ?_
  simp only [FiberBundle.pullback_trivializationAt']
  exact Trivialization.symm_apply ((trivializationAt (Fin n → 𝕜) V b.val).pullback
    (constStratumInclusion n)) (FiberBundle.mem_baseSet_trivializationAt (Fin n → 𝕜) V b.val) v

/-- The forgetful map from the `m`th rank stratum of `ofBundle 𝕜 n V` to `TotalSpace (Fin n → 𝕜) V`
is inducing by construction of `constStratumTopology`. -/
theorem isInducing_stratum_ofBundle (m : ℕ) :
    IsInducing (fun p : TotalSpace (Fin m → 𝕜) ((ofBundle 𝕜 n V).StratumFiber m) ↦
      (⟨p.proj.val, p.snd⟩ : TotalSpace (Fin n → 𝕜) V)) :=
  ⟨rfl⟩

/-- The global total space of `ofBundle 𝕜 n V` is canonically homeomorphic to
`TotalSpace (Fin n → 𝕜) V`. -/
noncomputable def ofBundleHomeomorph :
    TotalSpace Unit (ofBundle 𝕜 n V).Fiber ≃ₜ TotalSpace (Fin n → 𝕜) V where
  toFun p := ⟨p.proj, p.snd⟩
  invFun p := ⟨p.proj, p.snd⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  continuous_toFun := by
    have hsigma : Continuous (fun q : (ofBundle 𝕜 n V).GluedTotalSpace ↦
        (⟨q.2.proj.val, q.2.snd⟩ : TotalSpace (Fin n → 𝕜) V)) :=
      continuous_sigma fun m ↦ (isInducing_stratum_ofBundle 𝕜 n V m).continuous
    exact (hsigma.comp (ofBundle 𝕜 n V).totalSpaceHomeomorph.symm.continuous).congr fun p ↦ by
      rw [Function.comp_apply, (ofBundle 𝕜 n V).totalSpaceHomeomorph_symm_apply]
  continuous_invFun := by
    have h_in : Continuous (fun p : TotalSpace (Fin n → 𝕜) V ↦
        (⟨⟨p.proj, rfl⟩, p.snd⟩ : TotalSpace (Fin n → 𝕜) ((ofBundle 𝕜 n V).StratumFiber n))) :=
      (isInducing_stratum_ofBundle 𝕜 n V n).continuous_iff.2 continuous_id
    exact ((ofBundle 𝕜 n V).totalSpaceHomeomorph.continuous.comp
      (continuous_sigmaMk.comp h_in)).congr fun _ ↦ by
      simp only [Function.comp_apply, totalSpaceHomeomorph_apply]

@[simp] theorem ofBundleHomeomorph_apply (p : TotalSpace Unit (ofBundle 𝕜 n V).Fiber) :
    ofBundleHomeomorph 𝕜 n V p = ⟨p.proj, p.snd⟩ := (rfl)

@[simp] theorem ofBundleHomeomorph_symm_apply (p : TotalSpace (Fin n → 𝕜) V) :
    (ofBundleHomeomorph 𝕜 n V).symm p = ⟨p.proj, p.snd⟩ := (rfl)

end OfBundle

/-! ### Stratumwise bundle transfer -/

section OfBundles

variable (𝕜) (r : LocallyConstant X ℕ) (V : X → Type w')
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  (E : ∀ n : ℕ, {x : X // r x = n} → Type w)
  [∀ n x, AddCommMonoid (E n x)] [∀ n x, Module 𝕜 (E n x)]
  [∀ n x, TopologicalSpace (E n x)]
  [∀ n, TopologicalSpace (TotalSpace (Fin n → 𝕜) (E n))]
  [∀ n, FiberBundle (Fin n → 𝕜) (E n)]
  [∀ n, VectorBundle 𝕜 (Fin n → 𝕜) (E n)]
  (e : ∀ (n : ℕ) (x : {x : X // r x = n}), V x.val ≃L[𝕜] E n x)

/-- Assemble a `FiniteRankBundle` with fibres `V` and rank `r` by transporting stratumwise
`VectorBundle`s `E n` along fibrewise continuous linear equivalences `e n`. -/
@[expose] noncomputable def ofBundles : FiniteRankBundle.{w'} 𝕜 X where
  rank := r
  Fiber := V
  topologicalSpaceStratum n := totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x
  fiberBundleStratum n :=
    letI := totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x
    FiberBundle.ofContinuousLinearEquiv (Fin n → 𝕜) (E := E n) (e n)
      (isInducing_totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x)
  vectorBundleStratum n :=
    letI := totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x
    letI := FiberBundle.ofContinuousLinearEquiv (Fin n → 𝕜) (E := E n) (e n)
      (isInducing_totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x)
    VectorBundle.ofContinuousLinearEquiv (Fin n → 𝕜) (E := E n) (e n)
      (isInducing_totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x)

@[simp] theorem rank_ofBundles : (ofBundles 𝕜 r V E e).rank = r := (rfl)

@[simp] theorem fiber_ofBundles (x : X) : (ofBundles 𝕜 r V E e).Fiber x = V x := (rfl)

private noncomputable def gluedOfBundlesHomeomorph :
    (ofBundles 𝕜 r V E e).GluedTotalSpace ≃ₜ Σ n : ℕ, TotalSpace (Fin n → 𝕜) (E n) :=
  letI (n : ℕ) := totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x
  { toEquiv := Equiv.sigmaCongrRight fun n ↦
      (totalSpaceHomeomorphOfContinuousLinearEquiv (Fin n → 𝕜) (e n)
        (isInducing_totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x)).toEquiv
    continuous_toFun := continuous_sigma fun n ↦ continuous_sigmaMk.comp
      (totalSpaceHomeomorphOfContinuousLinearEquiv (Fin n → 𝕜) (e n)
        (isInducing_totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x)).continuous
    continuous_invFun := continuous_sigma fun n ↦ continuous_sigmaMk.comp
      (totalSpaceHomeomorphOfContinuousLinearEquiv (Fin n → 𝕜) (e n)
        (isInducing_totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x)).symm.continuous }

/-- Homeomorphism over `X` between the global total space of `ofBundles 𝕜 r V E e` and the disjoint
union of the stratum total spaces `TotalSpace (Fin n → 𝕜) (E n)`. -/
noncomputable def ofBundlesHomeomorph :
    TotalSpace Unit (ofBundles 𝕜 r V E e).Fiber ≃ₜ Σ n : ℕ, TotalSpace (Fin n → 𝕜) (E n) :=
  (ofBundles 𝕜 r V E e).totalSpaceHomeomorph.symm.trans (gluedOfBundlesHomeomorph 𝕜 r V E e)

@[simp] theorem ofBundlesHomeomorph_apply (p : TotalSpace Unit (ofBundles 𝕜 r V E e).Fiber) :
    ofBundlesHomeomorph 𝕜 r V E e p =
      ⟨r p.proj, ⟨⟨p.proj, rfl⟩, e (r p.proj) ⟨p.proj, rfl⟩ p.snd⟩⟩ :=
  letI := totalSpaceInduced (Fin (r p.proj) → 𝕜) (E := E (r p.proj)) fun x ↦ e (r p.proj) x
  (congrArg (gluedOfBundlesHomeomorph 𝕜 r V E e)
    ((ofBundles 𝕜 r V E e).totalSpaceHomeomorph_symm_apply p)).trans <|
    congrArg (Sigma.mk (r p.proj))
      (totalSpaceHomeomorphOfContinuousLinearEquiv_apply (Fin (r p.proj) → 𝕜) (e (r p.proj)) _ _)

@[simp] theorem ofBundlesHomeomorph_symm_apply (n : ℕ) (p : TotalSpace (Fin n → 𝕜) (E n)) :
    (ofBundlesHomeomorph 𝕜 r V E e).symm ⟨n, p⟩ = ⟨p.proj.val, (e n p.proj).symm p.snd⟩ :=
  letI := totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x
  (congrArg (fun q ↦ (ofBundles 𝕜 r V E e).totalSpaceHomeomorph ⟨n, q⟩)
    (totalSpaceHomeomorphOfContinuousLinearEquiv_symm_apply (Fin n → 𝕜) (e n) _ p)).trans
    ((ofBundles 𝕜 r V E e).totalSpaceHomeomorph_apply _)

end OfBundles

/-- Every bundle of globally zero rank is a zero object in `FiniteRankBundle.{w} 𝕜 X`. -/
theorem isZero_of_rank_eq_zero (E : FiniteRankBundle.{w} 𝕜 X) (h : ∀ x, E.rank x = 0) :
    IsZero E := by
  have (x : X) : Subsingleton (E.Fiber x) := by
    have : Subsingleton (Fin (E.rank x) → 𝕜) := by rw [h x]; infer_instance
    exact (E.fiberContinuousLinearEquiv x).injective.subsingleton
  exact (Limits.IsZero.iff_id_eq_zero _).2
    (hom_ext fun _ ↦ LinearMap.ext fun _ ↦ Subsingleton.elim _ _)

section ZeroBundle

variable (𝕜 X)

/-- The canonical rank-zero bundle in `FiniteRankBundle.{w} 𝕜 X` with fibre `PUnit.{w + 1}`. -/
noncomputable def zero : FiniteRankBundle.{w} 𝕜 X :=
  let e : PUnit.{w + 1} ≃L[𝕜] (Fin 0 → 𝕜) :=
    { LinearEquiv.ofSubsingleton (R := 𝕜) PUnit.{w + 1} (Fin 0 → 𝕜) with
      continuous_toFun := (continuous_const (y := (0 : Fin 0 → 𝕜))).congr
        fun _ ↦ Subsingleton.elim _ _
      continuous_invFun := (continuous_const (y := PUnit.unit)).congr fun _ ↦ rfl }
  letI := totalSpaceInduced (Fin 0 → 𝕜) (E := Bundle.Trivial X (Fin 0 → 𝕜))
    (E' := fun _ : X ↦ PUnit.{w + 1}) fun _ ↦ e
  let hind := isInducing_totalSpaceInduced (Fin 0 → 𝕜) (E := Bundle.Trivial X (Fin 0 → 𝕜))
    (E' := fun _ : X ↦ PUnit.{w + 1}) fun _ ↦ e
  letI := FiberBundle.ofContinuousLinearEquiv (Fin 0 → 𝕜) (E := Bundle.Trivial X (Fin 0 → 𝕜))
    (fun _ : X ↦ e) hind
  haveI := VectorBundle.ofContinuousLinearEquiv (Fin 0 → 𝕜) (E := Bundle.Trivial X (Fin 0 → 𝕜))
    (fun _ : X ↦ e) hind
  ofBundle 𝕜 0 fun _ : X ↦ PUnit.{w + 1}

@[simp] theorem rank_zero : (zero.{w} 𝕜 X).rank = LocallyConstant.const X 0 := (rfl)

@[simp] theorem fiber_zero (x : X) : (zero.{w} 𝕜 X).Fiber x = PUnit.{w + 1} := (rfl)

/-- The canonical rank-zero bundle `zero 𝕜 X` is a zero object in `FiniteRankBundle.{w} 𝕜 X`. -/
theorem isZero_zero : IsZero (zero.{w} 𝕜 X) := isZero_of_rank_eq_zero _ fun _ ↦ by simp

/-- `FiniteRankBundle.{w} 𝕜 X` admits a zero object, given by `zero 𝕜 X`. -/
instance : HasZeroObject (FiniteRankBundle.{w} 𝕜 X) := ⟨⟨zero.{w} 𝕜 X, isZero_zero 𝕜 X⟩⟩

end ZeroBundle

end FiniteRankBundle

end TauCeti

namespace CategoryTheory.Iso

open TauCeti

universe w u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X] {E F : FiniteRankBundle.{w} 𝕜 X}

/-- Isomorphic variable-rank vector bundles have the same locally constant rank function. -/
theorem finiteRankBundle_rank_eq (e : E ≅ F) : E.rank = F.rank := by
  ext x
  have hfin : Module.finrank 𝕜 ((FiniteRankBundle.fiberFunctor x).obj E) =
      Module.finrank 𝕜 ((FiniteRankBundle.fiberFunctor x).obj F) :=
    ((FiniteRankBundle.fiberFunctor x).mapIso e).toLinearEquiv.finrank_eq
  rw [FiniteRankBundle.fiberFunctor_obj, FiniteRankBundle.fiberFunctor_obj] at hfin
  exact (E.finrank_fiber x).symm.trans (hfin.trans (F.finrank_fiber x))

end CategoryTheory.Iso
