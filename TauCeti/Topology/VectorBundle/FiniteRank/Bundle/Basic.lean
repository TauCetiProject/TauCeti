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
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.VectorBundle.Constructions

import TauCeti.Topology.VectorBundle.Smul

/-!
# The category of genuine finite-rank vector bundles of variable rank

`TauCeti.FiniteRankBundle.{w} 𝕜 X` packages genuine `w`-universe `𝕜`-vector-space fibres over a
topological space `X : Type u`, a locally constant (not necessarily bounded) rank function
`rank : LocallyConstant X ℕ`, and genuine `FiberBundle (Fin n → 𝕜)` and
`VectorBundle 𝕜 (Fin n → 𝕜)` structures over each clopen rank stratum `{x : X // rank x = n}`.
Neither completeness of `𝕜` nor compactness or connectedness of `X` is assumed.

From the stratum vector-bundle trivializations alone, each fibre `E.Fiber x` inherits
`IsTopologicalAddGroup`, `ContinuousSMul 𝕜`, and `FiniteDimensional 𝕜` with
`Module.finrank 𝕜 (E.Fiber x) = E.rank x`, so callers do not supply redundant fibre-level
hypotheses.

The global total space `TotalSpace Unit E.Fiber` carries the disjoint-union topology of the native
stratum bundle total spaces via `FiniteRankBundle.totalSpaceHomeomorph`. Morphisms in
`FiniteRankBundle.{w} 𝕜 X` are fibrewise `𝕜`-linear maps whose induced maps on global total spaces
are continuous. Pointwise operations make `FiniteRankBundle.{w} 𝕜 X` a preadditive category with a
zero object (`FiniteRankBundle.zero`, built with `PUnit.{w + 1}` fibres unconditionally in every
fibre universe `w`), a faithful forgetful functor `totalSpaceFunctor` to `TopCat`, additive fibre
evaluation functors `fiberFunctor x` to `ModuleCat.{w} 𝕜`, and a constant-rank constructor
`ofBundle` whose global total space is canonically homeomorphic to the original constant-rank
total space (`ofBundleHomeomorph`).
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits Topology

namespace TauCeti

universe w u v

variable (𝕜 : Type v) [NontriviallyNormedField 𝕜] (X : Type u) [TopologicalSpace X]

/-- A genuine finite-rank topological vector bundle of locally constant (possibly unbounded) rank
over `X`, with fibres in `Type w`. On each clopen rank stratum `{x : X // rank x = n}`, the
restricted family of fibres carries a native Mathlib `VectorBundle 𝕜 (Fin n → 𝕜)` structure. -/
structure FiniteRankBundle : Type (max u v (w + 1)) where
  /-- The locally constant, not necessarily bounded, fibre dimension. -/
  rank : LocallyConstant X ℕ
  /-- The genuine vector-space fibre over each base point. -/
  Fiber : X → Type w
  [addCommGroupFiber : ∀ x, AddCommGroup (Fiber x)]
  [moduleFiber : ∀ x, Module 𝕜 (Fiber x)]
  [topologicalSpaceFiber : ∀ x, TopologicalSpace (Fiber x)]
  [topologicalSpaceStratum :
    ∀ n : ℕ, TopologicalSpace (TotalSpace (Fin n → 𝕜) fun x : {x : X // rank x = n} ↦ Fiber x.1)]
  [fiberBundleStratum :
    ∀ n : ℕ, FiberBundle (Fin n → 𝕜) fun x : {x : X // rank x = n} ↦ Fiber x.1]
  [vectorBundleStratum :
    ∀ n : ℕ, VectorBundle 𝕜 (Fin n → 𝕜) fun x : {x : X // rank x = n} ↦ Fiber x.1]

namespace FiniteRankBundle

attribute [instance] addCommGroupFiber moduleFiber topologicalSpaceFiber
  topologicalSpaceStratum fiberBundleStratum vectorBundleStratum

variable {𝕜 X}
variable (E : FiniteRankBundle.{w} 𝕜 X)

/-- The fibre family of `E` restricted to its `n`th clopen rank stratum. -/
abbrev StratumFiber (n : ℕ) (x : {x : X // E.rank x = n}) : Type w := E.Fiber x.1

/-- Preferred continuous linear equivalence between `E.Fiber x` and the coordinate model
`Fin (E.rank x) → 𝕜`, read from the stratum trivialization at `⟨x, rfl⟩`. -/
noncomputable def fiberContinuousLinearEquiv (x : X) : E.Fiber x ≃L[𝕜] (Fin (E.rank x) → 𝕜) :=
  VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E.rank x) → 𝕜) (E.StratumFiber (E.rank x)) ⟨x, rfl⟩

instance (x : X) : IsTopologicalAddGroup (E.Fiber x) where
  continuous_add := by
    let e := E.fiberContinuousLinearEquiv x
    exact (e.symm.continuous.comp ((e.continuous.comp continuous_fst).add
      (e.continuous.comp continuous_snd))).congr fun p ↦ by simp
  continuous_neg := by
    let e := E.fiberContinuousLinearEquiv x
    exact (e.symm.continuous.comp e.continuous.neg).congr fun v ↦ by simp

instance (x : X) : ContinuousSMul 𝕜 (E.Fiber x) where
  continuous_smul := by
    let e := E.fiberContinuousLinearEquiv x
    exact (e.symm.continuous.comp (continuous_fst.smul
      (e.continuous.comp continuous_snd))).congr fun p ↦ by simp

instance (x : X) : FiniteDimensional 𝕜 (E.Fiber x) :=
  Module.Finite.equiv (E.fiberContinuousLinearEquiv x).symm.toLinearEquiv

@[simp]
theorem finrank_fiber (x : X) : Module.finrank 𝕜 (E.Fiber x) = E.rank x :=
  (E.fiberContinuousLinearEquiv x).toLinearEquiv.finrank_eq.trans (Module.finrank_fin_fun 𝕜)

/-! ### Global total-space topology and continuity criterion -/

/-- The disjoint union of the native stratum bundle total spaces. -/
abbrev GluedTotalSpace := Σ n : ℕ, TotalSpace (Fin n → 𝕜) (E.StratumFiber n)

/-- Projection of the disjoint union of stratum total spaces to `X`. -/
def gluedProj (p : E.GluedTotalSpace) : X := p.2.proj.1

@[simp]
theorem gluedProj_mk (n : ℕ) (p : TotalSpace (Fin n → 𝕜) (E.StratumFiber n)) :
    E.gluedProj ⟨n, p⟩ = p.proj.1 := (rfl)

@[continuity, fun_prop]
theorem continuous_gluedProj : Continuous E.gluedProj :=
  continuous_sigma fun n ↦
    continuous_subtype_val.comp (FiberBundle.continuous_proj (Fin n → 𝕜) (E.StratumFiber n))

theorem isOpenMap_gluedProj : IsOpenMap E.gluedProj := by
  refine isOpenMap_sigma.2 fun n ↦ ?_
  exact (E.rank.isLocallyConstant.isOpen_fiber n).isOpenEmbedding_subtypeVal.isOpenMap.comp
    (FiberBundle.isOpenMap_proj (Fin n → 𝕜) (E.StratumFiber n))

private def totalSpaceEquiv : E.GluedTotalSpace ≃ TotalSpace Unit E.Fiber where
  toFun p := ⟨p.2.proj.1, p.2.2⟩
  invFun p := ⟨E.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩
  left_inv p := by
    rcases p with ⟨n, ⟨⟨x, hx⟩, v⟩⟩
    cases hx
    rfl
  right_inv p := by
    cases p
    rfl

/-- The global total-space topology on `TotalSpace Unit E.Fiber`, induced from the disjoint union
of the native stratum vector bundles. -/
instance : TopologicalSpace (TotalSpace Unit E.Fiber) :=
  TopologicalSpace.induced
    (fun p : TotalSpace Unit E.Fiber ↦
      (⟨E.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩ : E.GluedTotalSpace))
    inferInstance

/-- Homeomorphism between the disjoint union of stratum bundle total spaces and the global total
space `TotalSpace Unit E.Fiber`. -/
def totalSpaceHomeomorph : E.GluedTotalSpace ≃ₜ TotalSpace Unit E.Fiber :=
  (E.totalSpaceEquiv.symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm

@[simp]
theorem totalSpaceHomeomorph_apply (p : E.GluedTotalSpace) :
    E.totalSpaceHomeomorph p = ⟨p.2.proj.1, p.2.2⟩ := (rfl)

@[simp]
theorem totalSpaceHomeomorph_symm_apply (p : TotalSpace Unit E.Fiber) :
    E.totalSpaceHomeomorph.symm p = ⟨E.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩ := (rfl)

@[continuity, fun_prop]
theorem continuous_proj : Continuous (TotalSpace.proj : TotalSpace Unit E.Fiber → X) :=
  E.continuous_gluedProj.comp E.totalSpaceHomeomorph.symm.continuous

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
    Set.range (fun p : TotalSpace (Fin n → 𝕜) (E.StratumFiber n) ↦
      E.totalSpaceHomeomorph ⟨n, p⟩) =
      {p : TotalSpace Unit E.Fiber | E.rank p.proj = n} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.proj.2
  · intro hp
    rcases p with ⟨x, v⟩
    cases hp
    exact ⟨⟨⟨x, rfl⟩, v⟩, rfl⟩

/-- Inclusion of `E.Fiber x` into `TotalSpace Unit E.Fiber` is topological-space inducing. -/
theorem isInducing_mk (x : X) :
    IsInducing (fun v : E.Fiber x ↦ (⟨x, v⟩ : TotalSpace Unit E.Fiber)) := by
  rw [← E.totalSpaceHomeomorph.symm.isInducing.of_comp_iff]
  have hcomp :
      E.totalSpaceHomeomorph.symm ∘ (fun v : E.Fiber x ↦ (⟨x, v⟩ : TotalSpace Unit E.Fiber)) =
        Sigma.mk (E.rank x) ∘
          (fun v : E.Fiber x ↦
            (⟨⟨x, rfl⟩, v⟩ : TotalSpace (Fin (E.rank x) → 𝕜) (E.StratumFiber (E.rank x)))) := by
    funext v
    exact E.totalSpaceHomeomorph_symm_apply ⟨x, v⟩
  rw [hcomp]
  exact IsEmbedding.sigmaMk.isInducing.comp
    (FiberBundle.totalSpaceMk_isInducing (Fin (E.rank x) → 𝕜) (E.StratumFiber (E.rank x)) ⟨x, rfl⟩)

section Continuity

variable {Y : Type*} [TopologicalSpace Y] {b : Y → X}

/-- A map into `TotalSpace Unit E.Fiber` over `b : Y → X` is continuous if and only if its
restriction to each clopen rank stratum `{y : Y // E.rank (b y) = n}` is continuous into the
corresponding stratum vector-bundle total space. -/
theorem continuous_mk_iff_rankStrata (hb : Continuous b) (s : ∀ y, E.Fiber (b y)) :
    Continuous (fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit E.Fiber)) ↔
      ∀ n : ℕ, Continuous (fun y : {y : Y // E.rank (b y) = n} ↦
        (⟨⟨b y.1, y.2⟩, s y.1⟩ : TotalSpace (Fin n → 𝕜) (E.StratumFiber n))) := by
  constructor
  · intro hs n
    refine (IsEmbedding.sigmaMk (σ := fun n ↦
      TotalSpace (Fin n → 𝕜) (E.StratumFiber n))).continuous_iff.2 ?_
    refine (E.totalSpaceHomeomorph.symm.continuous.comp
      (hs.comp continuous_subtype_val)).congr fun ⟨y, hy⟩ ↦ ?_
    cases hy
    rfl
  · intro hs
    refine continuous_of_cover_nhds (s := fun n : ℕ ↦ {y : Y | E.rank (b y) = n})
      (fun y ↦ ⟨E.rank (b y), ((E.rank.isLocallyConstant.isOpen_fiber _).preimage hb).mem_nhds rfl⟩)
      fun n ↦ ?_
    rw [continuousOn_iff_continuous_domRestrict]
    refine (E.totalSpaceHomeomorph.continuous.comp (continuous_sigmaMk.comp (hs n))).congr
      fun ⟨y, hy⟩ ↦ ?_
    cases hy
    rfl

@[fun_prop]
theorem continuous_zeroSection : Continuous (fun x ↦ (⟨x, 0⟩ : TotalSpace Unit E.Fiber)) := by
  refine (E.continuous_mk_iff_rankStrata continuous_id _).2 fun n ↦ ?_
  exact (Bundle.Trivialization.continuous_zeroSection 𝕜
    (F := Fin n → 𝕜) (E := E.StratumFiber n)).congr fun _ ↦ rfl

theorem continuous_add {s t : ∀ y, E.Fiber (b y)}
    (hs : Continuous fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit E.Fiber))
    (ht : Continuous fun y ↦ (⟨b y, t y⟩ : TotalSpace Unit E.Fiber)) :
    Continuous fun y ↦ (⟨b y, s y + t y⟩ : TotalSpace Unit E.Fiber) := by
  have hb : Continuous b := E.continuous_proj.comp hs
  rw [E.continuous_mk_iff_rankStrata hb] at hs ht ⊢
  exact fun n ↦ (hs n).add_totalSpace 𝕜 (ht n)

theorem continuous_smul {s : ∀ y, E.Fiber (b y)} {c : Y → 𝕜}
    (hc : Continuous c)
    (hs : Continuous fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit E.Fiber)) :
    Continuous fun y ↦ (⟨b y, c y • s y⟩ : TotalSpace Unit E.Fiber) := by
  have hb : Continuous b := E.continuous_proj.comp hs
  rw [E.continuous_mk_iff_rankStrata hb] at hs ⊢
  exact fun n ↦ (hc.comp continuous_subtype_val).smul_totalSpace (hs n)

end Continuity

/-! ### Morphisms, preadditive category structure, and evaluation functors -/

/-- A morphism of genuine variable-rank vector bundles is a family of `𝕜`-linear maps on the fibres
whose induced map on global total spaces is continuous. -/
@[ext]
structure Hom (E F : FiniteRankBundle.{w} 𝕜 X) where
  /-- The linear map on each fibre. -/
  fiberMap : ∀ x : X, E.Fiber x →ₗ[𝕜] F.Fiber x
  /-- Continuity on the global total spaces. -/
  continuous_totalSpaceMap :
    Continuous fun p : TotalSpace Unit E.Fiber ↦
      (⟨p.proj, fiberMap p.proj p.2⟩ : TotalSpace Unit F.Fiber)

variable {E}
variable {F G : FiniteRankBundle.{w} 𝕜 X}

namespace Hom

/-- The bundled continuous map of global total spaces induced by a bundle morphism. -/
def totalSpaceMap (f : Hom E F) : C(TotalSpace Unit E.Fiber, TotalSpace Unit F.Fiber) :=
  ⟨_, f.continuous_totalSpaceMap⟩

@[simp]
theorem totalSpaceMap_mk (f : Hom E F) (x : X) (v : E.Fiber x) :
    f.totalSpaceMap ⟨x, v⟩ = ⟨x, f.fiberMap x v⟩ := (rfl)

@[simp]
theorem proj_totalSpaceMap (f : Hom E F) (p : TotalSpace Unit E.Fiber) :
    (f.totalSpaceMap p).proj = p.proj := (rfl)

@[continuity, fun_prop]
theorem continuous_fiberMap (f : Hom E F) (x : X) : Continuous (f.fiberMap x) :=
  (F.isInducing_mk x).continuous_iff.2 <|
    f.continuous_totalSpaceMap.comp (E.isInducing_mk x).continuous

/-- The continuous linear map on the fibre at `x` induced by a bundle morphism. -/
def fiberCLM (f : Hom E F) (x : X) : E.Fiber x →L[𝕜] F.Fiber x :=
  ⟨f.fiberMap x, f.continuous_fiberMap x⟩

@[simp]
theorem coe_fiberCLM (f : Hom E F) (x : X) :
    (f.fiberCLM x : E.Fiber x →ₗ[𝕜] F.Fiber x) = f.fiberMap x := (rfl)

@[simp]
theorem fiberCLM_apply (f : Hom E F) (x : X) (v : E.Fiber x) :
    f.fiberCLM x v = f.fiberMap x v := (rfl)

end Hom

instance : Category (FiniteRankBundle.{w} 𝕜 X) where
  Hom := Hom
  id E :=
    { fiberMap _ := LinearMap.id
      continuous_totalSpaceMap := continuous_id }
  comp f g :=
    { fiberMap x := (g.fiberMap x).comp (f.fiberMap x)
      continuous_totalSpaceMap := g.continuous_totalSpaceMap.comp f.continuous_totalSpaceMap }

@[ext]
theorem hom_ext {f g : E ⟶ F} (h : ∀ x, f.fiberMap x = g.fiberMap x) : f = g :=
  Hom.ext (funext h)

@[simp]
theorem fiberMap_id (E : FiniteRankBundle.{w} 𝕜 X) (x : X) :
    (𝟙 E : E ⟶ E).fiberMap x = LinearMap.id := (rfl)

@[simp]
theorem fiberMap_comp (f : E ⟶ F) (g : F ⟶ G) (x : X) :
    (f ≫ g).fiberMap x = (g.fiberMap x).comp (f.fiberMap x) := (rfl)

@[simp]
theorem totalSpaceMap_id (E : FiniteRankBundle.{w} 𝕜 X) :
    (𝟙 E : E ⟶ E).totalSpaceMap = ContinuousMap.id _ := (rfl)

@[simp]
theorem totalSpaceMap_comp (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).totalSpaceMap = g.totalSpaceMap.comp f.totalSpaceMap := (rfl)

theorem totalSpaceMap_injective : Function.Injective (Hom.totalSpaceMap (E := E) (F := F)) := by
  intro f g h
  refine hom_ext fun x ↦ LinearMap.ext fun v ↦ ?_
  exact TotalSpace.mk_inj.mp (congrArg (fun k ↦ k ⟨x, v⟩) h)

namespace Hom

instance : Zero (E ⟶ F) where
  zero := ⟨fun _ ↦ 0, F.continuous_zeroSection.comp E.continuous_proj⟩

instance : Add (E ⟶ F) where
  add f g := ⟨fun x ↦ f.fiberMap x + g.fiberMap x,
    F.continuous_add f.continuous_totalSpaceMap g.continuous_totalSpaceMap⟩

instance : Neg (E ⟶ F) where
  neg f := ⟨fun x ↦ -f.fiberMap x, by
    simpa only [neg_one_smul, LinearMap.neg_apply] using
      F.continuous_smul (continuous_const (y := (-1 : 𝕜))) f.continuous_totalSpaceMap⟩

instance : Sub (E ⟶ F) where
  sub f g := f + -g

instance : SMul ℕ (E ⟶ F) where
  smul n f := ⟨fun x ↦ n • f.fiberMap x, by
    simpa only [Nat.cast_smul_eq_nsmul, LinearMap.smul_apply] using
      F.continuous_smul (continuous_const (y := (n : 𝕜))) f.continuous_totalSpaceMap⟩

instance : SMul ℤ (E ⟶ F) where
  smul n f := ⟨fun x ↦ n • f.fiberMap x, by
    simpa only [Int.cast_smul_eq_zsmul, LinearMap.smul_apply] using
      F.continuous_smul (continuous_const (y := (n : 𝕜))) f.continuous_totalSpaceMap⟩

instance : AddCommGroup (E ⟶ F) :=
  Function.Injective.addCommGroup Hom.fiberMap (fun _ _ h ↦ Hom.ext h)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ by funext x; exact (sub_eq_add_neg _ _).symm)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end Hom

instance : Preadditive (FiniteRankBundle.{w} 𝕜 X) where
  add_comp _ _ _ _ _ h := hom_ext fun x ↦ LinearMap.ext fun _ ↦ (h.fiberMap x).map_add _ _
  comp_add _ _ _ _ _ _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

@[simp]
theorem fiberMap_zero (x : X) : (0 : E ⟶ F).fiberMap x = 0 := (rfl)

@[simp]
theorem fiberMap_add (f g : E ⟶ F) (x : X) :
    (f + g).fiberMap x = f.fiberMap x + g.fiberMap x := (rfl)

@[simp]
theorem fiberMap_neg (f : E ⟶ F) (x : X) :
    (-f).fiberMap x = -f.fiberMap x := (rfl)

@[simp]
theorem fiberMap_sub (f g : E ⟶ F) (x : X) :
    (f - g).fiberMap x = f.fiberMap x - g.fiberMap x := by
  simp only [sub_eq_add_neg, fiberMap_add, fiberMap_neg]

@[simp]
theorem fiberMap_nsmul (n : ℕ) (f : E ⟶ F) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := (rfl)

@[simp]
theorem fiberMap_zsmul (n : ℤ) (f : E ⟶ F) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := (rfl)

/-- Forgetful functor sending a genuine variable-rank bundle to its global total space. -/
-- Expose the object assignment so morphism types reduce to the global total spaces.
@[expose]
def totalSpaceFunctor : FiniteRankBundle.{w} 𝕜 X ⥤ TopCat.{max u w} where
  obj E := TopCat.of (TotalSpace Unit E.Fiber)
  map f := TopCat.ofHom f.totalSpaceMap

@[simp]
theorem totalSpaceFunctor_obj (E : FiniteRankBundle.{w} 𝕜 X) :
    totalSpaceFunctor.obj E = TopCat.of (TotalSpace Unit E.Fiber) := (rfl)

@[simp]
theorem totalSpaceFunctor_map_apply (f : E ⟶ F) (p : TotalSpace Unit E.Fiber) :
    totalSpaceFunctor.map f p = f.totalSpaceMap p := (rfl)

instance : (totalSpaceFunctor.{w} (𝕜 := 𝕜) (X := X)).Faithful where
  map_injective h := totalSpaceMap_injective (congrArg TopCat.Hom.hom h)

/-- Additive evaluation functor sending a genuine variable-rank bundle to its fibre module at
`x`. -/
-- Expose the object assignment so evaluated morphisms act on the original fibre modules.
@[expose]
def fiberFunctor (x : X) : FiniteRankBundle.{w} 𝕜 X ⥤ ModuleCat.{w} 𝕜 where
  obj E := ModuleCat.of 𝕜 (E.Fiber x)
  map f := ModuleCat.ofHom (f.fiberMap x)

@[simp]
theorem fiberFunctor_obj (x : X) (E : FiniteRankBundle.{w} 𝕜 X) :
    (fiberFunctor x).obj E = ModuleCat.of 𝕜 (E.Fiber x) := (rfl)

@[simp]
theorem fiberFunctor_map_apply (x : X) (f : E ⟶ F) (v : E.Fiber x) :
    (fiberFunctor x).map f v = f.fiberMap x v := (rfl)

instance (x : X) : (fiberFunctor.{w} (𝕜 := 𝕜) (X := X) x).Additive where
  map_add := by intros; rfl

/-- Construct an isomorphism in `FiniteRankBundle.{w} 𝕜 X` from linear equivalences on the fibres
whose forward and inverse total-space maps are continuous. -/
def isoMk (e : ∀ x, E.Fiber x ≃ₗ[𝕜] F.Fiber x)
    (h : Continuous fun p : TotalSpace Unit E.Fiber ↦
      (⟨p.proj, e p.proj p.2⟩ : TotalSpace Unit F.Fiber))
    (h' : Continuous fun p : TotalSpace Unit F.Fiber ↦
      (⟨p.proj, (e p.proj).symm p.2⟩ : TotalSpace Unit E.Fiber)) : E ≅ F where
  hom := ⟨fun x ↦ (e x).toLinearMap, h⟩
  inv := ⟨fun x ↦ (e x).symm.toLinearMap, h'⟩
  hom_inv_id := hom_ext fun x ↦ LinearMap.ext (e x).symm_apply_apply
  inv_hom_id := hom_ext fun x ↦ LinearMap.ext (e x).apply_symm_apply

@[simp]
theorem fiberMap_isoMk_hom (e : ∀ x, E.Fiber x ≃ₗ[𝕜] F.Fiber x) (h h') (x : X) :
    (isoMk e h h').hom.fiberMap x = (e x).toLinearMap := (rfl)

@[simp]
theorem fiberMap_isoMk_inv (e : ∀ x, E.Fiber x ≃ₗ[𝕜] F.Fiber x) (h h') (x : X) :
    (isoMk e h h').inv.fiberMap x = (e x).symm.toLinearMap := (rfl)

/-! ### Constant-rank genuine vector bundles and zero object -/

section OfBundle

variable (𝕜)
variable (n : ℕ) (V : X → Type w)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace (Fin n → 𝕜) V)]
  [FiberBundle (Fin n → 𝕜) V] [VectorBundle 𝕜 (Fin n → 𝕜) V]

/-- Induced topology on the `m`th rank stratum of a constant-rank bundle `V` of rank `n`. -/
@[instance_reducible]
def constStratumTopology (m : ℕ) :
    TopologicalSpace
      (TotalSpace (Fin m → 𝕜) fun x : {x : X // (LocallyConstant.const X n) x = m} ↦ V x.1) :=
  TopologicalSpace.induced
    (fun p : TotalSpace (Fin m → 𝕜)
        (fun x : {x : X // (LocallyConstant.const X n) x = m} ↦ V x.1) ↦
      (⟨p.proj.1, p.2⟩ : TotalSpace (Fin n → 𝕜) V))
    inferInstance

omit [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 (Fin n → 𝕜) V] in
private theorem isInducing_constStratum_pullback :
    letI := constStratumTopology 𝕜 n V n
    let s : C({x : X // (LocallyConstant.const X n) x = n}, X) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    IsInducing
      (fun p : TotalSpace (Fin n → 𝕜)
          (fun x : {x : X // (LocallyConstant.const X n) x = n} ↦ V x.1) ↦
        (⟨p.proj, p.2⟩ : TotalSpace (Fin n → 𝕜) ((s : _ → X) *ᵖ V))) := by
  let := constStratumTopology 𝕜 n V n
  let S := {x : X // (LocallyConstant.const X n) x = n}
  let s : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let T₁ := TotalSpace (Fin n → 𝕜) (fun x : S ↦ V x.1)
  let T₂ := TotalSpace (Fin n → 𝕜) ((s : S → X) *ᵖ V)
  have hf : Continuous (fun p : T₁ ↦ (⟨p.proj, p.2⟩ : T₂)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding (Fin n → 𝕜) V s).continuous_iff]
    have hlift : Continuous (fun p : T₁ ↦ (⟨p.proj.1, p.2⟩ : TotalSpace (Fin n → 𝕜) V)) :=
      continuous_induced_dom
    have hproj : Continuous (fun p : T₁ ↦ p.proj) :=
      ((FiberBundle.continuous_proj (Fin n → 𝕜) V).comp hlift).subtype_mk fun _ ↦ rfl
    exact hproj.prodMk hlift
  have hg : Continuous (fun q : T₂ ↦ (⟨q.proj, q.2⟩ : T₁)) :=
    continuous_induced_rng.2 (Pullback.continuous_lift (Fin n → 𝕜) V s)
  exact ({ toFun := fun p : T₁ ↦ (⟨p.proj, p.2⟩ : T₂)
           invFun := fun q : T₂ ↦ (⟨q.proj, q.2⟩ : T₁)
           left_inv := fun _ ↦ rfl
           right_inv := fun _ ↦ rfl
           continuous_toFun := hf
           continuous_invFun := hg } : T₁ ≃ₜ T₂).isInducing

/-- Combined `FiberBundle` and `VectorBundle` structures on the `m`th rank stratum of a
constant-rank bundle `V` of rank `n`. -/
noncomputable def constStratumBundle (m : ℕ) :
    letI := constStratumTopology 𝕜 n V m
    Σ' (_ : FiberBundle (Fin m → 𝕜)
        fun x : {x : X // (LocallyConstant.const X n) x = m} ↦ V x.1),
      VectorBundle 𝕜 (Fin m → 𝕜)
        fun x : {x : X // (LocallyConstant.const X n) x = m} ↦ V x.1 := by
  let := constStratumTopology 𝕜 n V m
  by_cases hnm : n = m
  · subst hnm
    let s : C({x : X // (LocallyConstant.const X n) x = n}, X) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    exact ⟨FiberBundle.ofContinuousLinearEquiv (Fin n → 𝕜)
        (E := (s : _ → X) *ᵖ V) (fun x ↦ ContinuousLinearEquiv.refl 𝕜 (V x.1))
        (isInducing_constStratum_pullback 𝕜 n V),
      VectorBundle.ofContinuousLinearEquiv (Fin n → 𝕜)
        (E := (s : _ → X) *ᵖ V) (fun x ↦ ContinuousLinearEquiv.refl 𝕜 (V x.1))
        (isInducing_constStratum_pullback 𝕜 n V)⟩
  · have : IsEmpty {x : X // (LocallyConstant.const X n) x = m} := ⟨fun x ↦ hnm x.2⟩
    exact ⟨FiberBundle.ofIsEmpty (Fin m → 𝕜) _, VectorBundle.ofIsEmpty 𝕜 (Fin m → 𝕜) _⟩

/-- Package a genuine constant-rank Mathlib `VectorBundle 𝕜 (Fin n → 𝕜) V` over `X` as an object of
`FiniteRankBundle.{w} 𝕜 X` retaining the exact fibre family `V`. -/
-- Expose the rank and fibre projections so dependent fibre types reduce to `V x`.
@[expose]
noncomputable def ofBundle : FiniteRankBundle.{w} 𝕜 X where
  rank := LocallyConstant.const X n
  Fiber := V
  topologicalSpaceStratum := constStratumTopology 𝕜 n V
  fiberBundleStratum m := (constStratumBundle 𝕜 n V m).1
  vectorBundleStratum m := (constStratumBundle 𝕜 n V m).2

@[simp]
theorem rank_ofBundle : (ofBundle 𝕜 n V).rank = LocallyConstant.const X n := (rfl)

@[simp]
theorem fiber_ofBundle (x : X) : (ofBundle 𝕜 n V).Fiber x = V x := (rfl)

/-- The global total space of `ofBundle 𝕜 n V` is canonically homeomorphic over `X` to the
original constant-rank total space `TotalSpace (Fin n → 𝕜) V` by the identity on fibres. -/
noncomputable def ofBundleHomeomorph :
    TotalSpace Unit (ofBundle 𝕜 n V).Fiber ≃ₜ TotalSpace (Fin n → 𝕜) V where
  toFun p := ⟨p.proj, p.2⟩
  invFun p := ⟨p.proj, p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  continuous_toFun := by
    have hsigma : Continuous (fun q : (ofBundle 𝕜 n V).GluedTotalSpace ↦
        (⟨q.2.proj.1, q.2.2⟩ : TotalSpace (Fin n → 𝕜) V)) :=
      continuous_sigma fun _ ↦ continuous_induced_dom
    exact (hsigma.comp (ofBundle 𝕜 n V).totalSpaceHomeomorph.symm.continuous).congr
      fun p ↦ by
        rw [Function.comp_apply, (ofBundle 𝕜 n V).totalSpaceHomeomorph_symm_apply]
  continuous_invFun := by
    have h_in : Continuous (fun p : TotalSpace (Fin n → 𝕜) V ↦
        (⟨⟨p.proj, rfl⟩, p.2⟩ :
          TotalSpace (Fin n → 𝕜) ((ofBundle 𝕜 n V).StratumFiber n))) :=
      continuous_induced_rng.2 (continuous_id : Continuous (id : TotalSpace (Fin n → 𝕜) V → _))
    exact ((ofBundle 𝕜 n V).totalSpaceHomeomorph.continuous.comp
      (continuous_sigmaMk.comp h_in)).congr fun _ ↦ rfl

@[simp]
theorem ofBundleHomeomorph_apply (p : TotalSpace Unit (ofBundle 𝕜 n V).Fiber) :
    ofBundleHomeomorph 𝕜 n V p = ⟨p.proj, p.2⟩ := (rfl)

@[simp]
theorem ofBundleHomeomorph_symm_apply (p : TotalSpace (Fin n → 𝕜) V) :
    (ofBundleHomeomorph 𝕜 n V).symm p = ⟨p.proj, p.2⟩ := (rfl)

end OfBundle

/-- Every bundle of globally zero rank is a zero object in `FiniteRankBundle.{w} 𝕜 X`. -/
theorem isZero_of_rank_eq_zero (E : FiniteRankBundle.{w} 𝕜 X) (h : ∀ x, E.rank x = 0) :
    IsZero E := by
  have hsub : ∀ x, Subsingleton (E.Fiber x) := fun x ↦ by
    have : Subsingleton (Fin (E.rank x) → 𝕜) := by rw [h x]; infer_instance
    exact (E.fiberContinuousLinearEquiv x).injective.subsingleton
  refine ⟨fun F ↦ ⟨⟨⟨0⟩, fun f ↦ hom_ext fun x ↦ LinearMap.ext fun v ↦ ?_⟩⟩,
    fun F ↦ ⟨⟨⟨0⟩, fun f ↦ hom_ext fun x ↦ LinearMap.ext fun v ↦ ?_⟩⟩⟩
  · rw [Subsingleton.elim v 0, map_zero, map_zero]
  · exact Subsingleton.elim _ _

section ZeroBundle

variable (𝕜 X)

/-- The canonical rank-zero bundle in `FiniteRankBundle.{w} 𝕜 X` with fibre `PUnit.{w + 1}`,
defined unconditionally for every fibre universe `w` without smallness assumptions on `𝕜`. -/
noncomputable def zero : FiniteRankBundle.{w} 𝕜 X :=
  let e : PUnit.{w + 1} ≃L[𝕜] (Fin 0 → 𝕜) :=
    { LinearEquiv.ofSubsingleton (R := 𝕜) PUnit.{w + 1} (Fin 0 → 𝕜) with
      continuous_toFun := (continuous_const (y := (0 : Fin 0 → 𝕜))).congr
        fun _ ↦ Subsingleton.elim _ _
      continuous_invFun := (continuous_const (y := PUnit.unit)).congr
        fun _ ↦ Subsingleton.elim _ _ }
  letI := totalSpaceInduced (Fin 0 → 𝕜) (E := Bundle.Trivial X (Fin 0 → 𝕜)) fun _ : X ↦ e
  letI := FiberBundle.ofContinuousLinearEquiv (Fin 0 → 𝕜) (E := Bundle.Trivial X (Fin 0 → 𝕜))
    (fun _ : X ↦ e) ⟨rfl⟩
  haveI := VectorBundle.ofContinuousLinearEquiv (Fin 0 → 𝕜) (E := Bundle.Trivial X (Fin 0 → 𝕜))
    (fun _ : X ↦ e) ⟨rfl⟩
  ofBundle 𝕜 0 fun _ : X ↦ PUnit.{w + 1}

@[simp]
theorem rank_zero : (zero.{w} 𝕜 X).rank = LocallyConstant.const X 0 := by
  rw [zero, rank_ofBundle]

theorem isZero_zero : IsZero (zero.{w} 𝕜 X) :=
  isZero_of_rank_eq_zero _ fun x ↦ by simp

instance : HasZeroObject (FiniteRankBundle.{w} 𝕜 X) :=
  ⟨⟨zero.{w} 𝕜 X, isZero_zero 𝕜 X⟩⟩

end ZeroBundle

end FiniteRankBundle

end TauCeti

namespace CategoryTheory.Iso

open TauCeti

universe w u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X] {E F : FiniteRankBundle.{w} 𝕜 X}

/-- Isomorphic variable-rank vector bundles have the same locally constant rank function, even on
noncompact or disconnected bases. -/
theorem finiteRankBundle_rank_eq (e : E ≅ F) : E.rank = F.rank := by
  ext x
  calc
    E.rank x = Module.finrank 𝕜 ((FiniteRankBundle.fiberFunctor x).obj E) :=
      (E.finrank_fiber x).symm
    _ = Module.finrank 𝕜 ((FiniteRankBundle.fiberFunctor x).obj F) :=
      ((FiniteRankBundle.fiberFunctor x).mapIso e).toLinearEquiv.finrank_eq
    _ = F.rank x := F.finrank_fiber x

end CategoryTheory.Iso
