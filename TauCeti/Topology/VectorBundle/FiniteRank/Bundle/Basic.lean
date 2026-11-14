/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiberwiseEquiv
public import TauCeti.Topology.VectorBundle.FiniteRank.Basic
public import TauCeti.Topology.VectorBundle.Section
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.VectorBundle.Constructions

import TauCeti.Topology.VectorBundle.Smul

/-!
# The category of variable-rank finite-rank topological vector bundles

`TauCeti.FiniteRankVectorBundle.{w} 𝕜 X` packages a variable-rank vector bundle with locally
constant rank `rank : LocallyConstant X ℕ`, fibres `Fiber : X → Type w`, and genuine Mathlib
`VectorBundle 𝕜 (Fin n → 𝕜)` structures on the clopen rank strata `{x : X // rank x = n}`.
`TotalSpace Unit V.Fiber` carries the disjoint-union topology (`totalSpaceHomeomorph`), in which
each stratum embeds openly (`isOpenEmbedding_stratum`) and fibre inclusions are inducing
(`totalSpaceMk_isInducing`). Morphisms `V ⟶ W` are fibrewise `𝕜`-linear maps with continuous
total-space maps, giving a preadditive category with zero object `zero 𝕜 X`, `totalSpaceFunctor`,
`fiberFunctor`, `ofFixedRank`, `mapFibers`, and `uliftFunctor`.

## References

* M. F. Atiyah, *K-Theory*, W. A. Benjamin (1967), §1.1–1.2.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits Set Topology

namespace TauCeti

universe w w' v u

/-- A variable-rank finite-rank topological vector bundle over `X` with fibres in `Type w`. On each
clopen rank-`n` stratum `{x : X // rank x = n}`, the restricted fibre family is a Mathlib
`VectorBundle 𝕜 (Fin n → 𝕜)`. -/
structure FiniteRankVectorBundle (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    (X : Type u) [TopologicalSpace X] : Type (max u v (w + 1)) where
  /-- The locally constant finite rank of the fibres. -/
  rank : LocallyConstant X ℕ
  /-- The actual fibre over each base point. -/
  Fiber : X → Type w
  /-- Additive group structure on each fibre. -/
  addCommGroupFiber (x : X) : AddCommGroup (Fiber x)
  /-- `𝕜`-module structure on each fibre. -/
  moduleFiber (x : X) : Module 𝕜 (Fiber x)
  /-- Topology on each fibre. -/
  topologicalSpaceFiber (x : X) : TopologicalSpace (Fiber x)
  /-- Total-space topology on each clopen rank-`n` stratum. -/
  topologicalSpaceStratum (n : ℕ) :
    TopologicalSpace (TotalSpace (Fin n → 𝕜) (fun x : {x : X // rank x = n} => Fiber x.1))
  /-- Fibre-bundle structure on each clopen rank-`n` stratum. -/
  fiberBundleStratum (n : ℕ) :
    FiberBundle (Fin n → 𝕜) (fun x : {x : X // rank x = n} => Fiber x.1)
  /-- Linear vector-bundle structure on each clopen rank-`n` stratum. -/
  vectorBundleStratum (n : ℕ) :
    VectorBundle 𝕜 (Fin n → 𝕜) (fun x : {x : X // rank x = n} => Fiber x.1)

attribute [instance] FiniteRankVectorBundle.addCommGroupFiber
  FiniteRankVectorBundle.moduleFiber
  FiniteRankVectorBundle.topologicalSpaceFiber
  FiniteRankVectorBundle.topologicalSpaceStratum
  FiniteRankVectorBundle.fiberBundleStratum
  FiniteRankVectorBundle.vectorBundleStratum

namespace FiniteRankVectorBundle

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

section TotalSpace

variable (V : FiniteRankVectorBundle.{w} 𝕜 X)

/-- The clopen base stratum where `V` has rank `n`. -/
abbrev Stratum (n : ℕ) : Type u := {x : X // V.rank x = n}

/-- The fibre family of `V` restricted to its rank-`n` stratum. -/
abbrev StratumFiber (n : ℕ) (x : V.Stratum n) : Type w := V.Fiber x.1

/-- The disjoint union of the native stratum total spaces of `V`. -/
abbrev GluedTotalSpace : Type (max u w) :=
  Σ n : ℕ, TotalSpace (Fin n → 𝕜) (V.StratumFiber n)

/-- Projection of the glued stratum total spaces to the base `X`. -/
def gluedProj (p : V.GluedTotalSpace) : X := p.2.proj.1

@[simp] theorem gluedProj_mk (n : ℕ) (p : TotalSpace (Fin n → 𝕜) (V.StratumFiber n)) :
    V.gluedProj ⟨n, p⟩ = p.proj.1 := (rfl)

/-- Projection from the glued stratum total spaces is continuous. -/
@[continuity, fun_prop] theorem continuous_gluedProj : Continuous V.gluedProj :=
  continuous_sigma fun n => continuous_subtype_val.comp
    (FiberBundle.continuous_proj (Fin n → 𝕜) (V.StratumFiber n))

/-- Projection from the glued stratum total spaces is an open map. -/
theorem isOpenMap_gluedProj : IsOpenMap V.gluedProj :=
  isOpenMap_sigma.2 fun n =>
    ((V.rank.isLocallyConstant.isOpen_fiber n).isOpenEmbedding_subtypeVal.isOpenMap).comp
      (FiberBundle.isOpenMap_proj (Fin n → 𝕜) (V.StratumFiber n))

private def totalSpaceEquiv : V.GluedTotalSpace ≃ TotalSpace Unit V.Fiber where
  toFun p := ⟨p.2.proj.1, p.2.2⟩
  invFun p := ⟨V.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩
  left_inv := fun ⟨_, ⟨⟨_, rfl⟩, _⟩⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

/-- Disjoint-union topology on `TotalSpace Unit V.Fiber` induced from stratum total spaces. -/
instance : TopologicalSpace (TotalSpace Unit V.Fiber) :=
  TopologicalSpace.induced
    (fun p : TotalSpace Unit V.Fiber =>
      (⟨V.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩ : V.GluedTotalSpace))
    inferInstance

/-- Homeomorphism from the glued stratum total spaces onto `TotalSpace Unit V.Fiber`. -/
def totalSpaceHomeomorph : V.GluedTotalSpace ≃ₜ TotalSpace Unit V.Fiber :=
  (V.totalSpaceEquiv.symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm

@[simp] theorem totalSpaceHomeomorph_apply (p : V.GluedTotalSpace) :
    V.totalSpaceHomeomorph p = ⟨p.2.proj.1, p.2.2⟩ := (rfl)

@[simp] theorem totalSpaceHomeomorph_symm_apply (p : TotalSpace Unit V.Fiber) :
    V.totalSpaceHomeomorph.symm p = ⟨V.rank p.proj, ⟨⟨p.proj, rfl⟩, p.2⟩⟩ := (rfl)

/-- Projection from the variable-rank total space to the base is continuous. -/
@[continuity, fun_prop] theorem continuous_proj :
    Continuous (TotalSpace.proj : TotalSpace Unit V.Fiber → X) :=
  V.continuous_gluedProj.comp V.totalSpaceHomeomorph.symm.continuous

/-- Projection from the variable-rank total space to the base is an open map. -/
theorem isOpenMap_proj : IsOpenMap (TotalSpace.proj : TotalSpace Unit V.Fiber → X) :=
  V.isOpenMap_gluedProj.comp V.totalSpaceHomeomorph.symm.isOpenMap

/-- Each stratum total space embeds openly into `TotalSpace Unit V.Fiber`. -/
theorem isOpenEmbedding_stratum (n : ℕ) :
    IsOpenEmbedding (fun p : TotalSpace (Fin n → 𝕜) (V.StratumFiber n) =>
      V.totalSpaceHomeomorph ⟨n, p⟩) :=
  V.totalSpaceHomeomorph.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk

/-- Image of the `n`th stratum total space: `{p : TotalSpace Unit V.Fiber | V.rank p.proj = n}`. -/
theorem range_stratum (n : ℕ) :
    Set.range (fun p : TotalSpace (Fin n → 𝕜) (V.StratumFiber n) =>
      V.totalSpaceHomeomorph ⟨n, p⟩) =
      {p : TotalSpace Unit V.Fiber | V.rank p.proj = n} := by
  ext ⟨x, v⟩
  refine ⟨fun ⟨q, hq⟩ => ?_, fun hx => ⟨⟨⟨x, hx⟩, v⟩, rfl⟩⟩
  have hx : q.proj.1 = x := congrArg TotalSpace.proj hq
  exact hx ▸ q.proj.2

/-- Inclusion of each fibre into the glued variable-rank total space is an inducing map. -/
theorem totalSpaceMk_isInducing (x : X) :
    IsInducing (TotalSpace.mk x : V.Fiber x → TotalSpace Unit V.Fiber) := by
  rw [← V.totalSpaceHomeomorph.symm.isInducing.of_comp_iff]
  exact (IsEmbedding.sigmaMk (σ := fun n => TotalSpace (Fin n → 𝕜) (V.StratumFiber n))
    (i := V.rank x)).isInducing.comp (FiberBundle.totalSpaceMk_isInducing (Fin (V.rank x) → 𝕜)
      (V.StratumFiber (V.rank x)) ⟨x, rfl⟩)

/-- A map into `TotalSpace Unit V.Fiber` is continuous if and only if its restrictions to all
clopen rank strata are continuous into the native stratum total spaces. -/
theorem continuous_mk_iff_rankStrata {Y : Type*} [TopologicalSpace Y] {b : Y → X}
    (hb : Continuous b) (s : ∀ y, V.Fiber (b y)) :
    Continuous (fun y => (⟨b y, s y⟩ : TotalSpace Unit V.Fiber)) ↔
      ∀ n : ℕ, Continuous (fun y : {y : Y // V.rank (b y) = n} =>
        (⟨⟨b y, y.2⟩, s y⟩ : TotalSpace (Fin n → 𝕜) (V.StratumFiber n))) := by
  constructor
  · intro hs n
    rw [(IsEmbedding.sigmaMk (σ := fun n => TotalSpace (Fin n → 𝕜) (V.StratumFiber n))
      (i := n)).continuous_iff]
    refine (V.totalSpaceHomeomorph.symm.continuous.comp (hs.comp continuous_subtype_val)).congr ?_
    rintro ⟨_, hy⟩; cases hy; rfl
  · intro hs
    refine continuous_of_cover_nhds (s := fun n : ℕ => {y : Y | V.rank (b y) = n})
      (fun y => ⟨V.rank (b y),
        ((V.rank.isLocallyConstant.isOpen_fiber _).preimage hb).mem_nhds rfl⟩) fun n => ?_
    rw [continuousOn_iff_continuous_domRestrict]
    exact (V.totalSpaceHomeomorph.continuous.comp (continuous_sigmaMk.comp (hs n))).congr
      fun _ => rfl

/-- The zero section of a variable-rank vector bundle is continuous. -/
@[fun_prop] theorem continuous_zeroSection :
    Continuous (fun x => (⟨x, 0⟩ : TotalSpace Unit V.Fiber)) :=
  (V.continuous_mk_iff_rankStrata continuous_id _).2 fun n =>
    (Bundle.Trivialization.continuous_zeroSection 𝕜
      (F := Fin n → 𝕜) (E := V.StratumFiber n)).congr fun _ => rfl

/-- Fibrewise addition of continuous maps over the same base map is continuous. -/
theorem continuous_add {Y : Type*} [TopologicalSpace Y] {b : Y → X} {s t : ∀ y, V.Fiber (b y)}
    (hs : Continuous (fun y => (⟨b y, s y⟩ : TotalSpace Unit V.Fiber)))
    (ht : Continuous (fun y => (⟨b y, t y⟩ : TotalSpace Unit V.Fiber))) :
    Continuous (fun y => (⟨b y, s y + t y⟩ : TotalSpace Unit V.Fiber)) := by
  have hb : Continuous b := V.continuous_proj.comp hs
  rw [V.continuous_mk_iff_rankStrata hb] at hs ht ⊢
  exact fun n => (hs n).add_totalSpace 𝕜 (ht n)

/-- Fibrewise scalar multiplication of a continuous map by a continuous scalar is continuous. -/
theorem continuous_smul {Y : Type*} [TopologicalSpace Y] {b : Y → X}
    {s : ∀ y, V.Fiber (b y)} {c : Y → 𝕜} (hc : Continuous c)
    (hs : Continuous (fun y => (⟨b y, s y⟩ : TotalSpace Unit V.Fiber))) :
    Continuous (fun y => (⟨b y, c y • s y⟩ : TotalSpace Unit V.Fiber)) := by
  have hb : Continuous b := V.continuous_proj.comp hs
  rw [V.continuous_mk_iff_rankStrata hb] at hs ⊢
  exact fun n => (hc.comp continuous_subtype_val).smul_totalSpace (hs n)

instance (x : X) : ContinuousSMul 𝕜 (V.Fiber x) where
  continuous_smul := (V.totalSpaceMk_isInducing x).continuous_iff.2 <|
    V.continuous_smul continuous_fst ((V.totalSpaceMk_isInducing x).continuous.comp continuous_snd)

instance (x : X) : IsTopologicalAddGroup (V.Fiber x) where
  continuous_add := (V.totalSpaceMk_isInducing x).continuous_iff.2 <|
    V.continuous_add ((V.totalSpaceMk_isInducing x).continuous.comp continuous_fst)
      ((V.totalSpaceMk_isInducing x).continuous.comp continuous_snd)
  continuous_neg := (V.totalSpaceMk_isInducing x).continuous_iff.2 <|
    (V.continuous_smul (continuous_const (y := (-1 : 𝕜)))
      (V.totalSpaceMk_isInducing x).continuous).congr fun _ => by simp

instance (x : X) : Module.Finite 𝕜 (V.Fiber x) :=
  @Module.Finite.equiv 𝕜 (Fin (V.rank x) → 𝕜) (V.Fiber x) _ _ _ _ _ _
    (pointIndexedCoreFiberEquiv 𝕜 (Fin (V.rank x) → 𝕜) (V.StratumFiber (V.rank x))
      ⟨x, rfl⟩).toLinearEquiv

/-- The `𝕜`-dimension of `V.Fiber x` equals `V.rank x`. -/
@[simp] theorem finrank_fiber (x : X) : Module.finrank 𝕜 (V.Fiber x) = V.rank x :=
  ((pointIndexedCoreFiberEquiv 𝕜 (Fin (V.rank x) → 𝕜) (V.StratumFiber (V.rank x))
    ⟨x, rfl⟩).toLinearEquiv.symm.finrank_eq).trans (Module.finrank_fin_fun 𝕜)

end TotalSpace

section Category

/-- A variable-rank bundle morphism: fibrewise linear maps with continuous total-space map. -/
@[ext]
structure Hom (V W : FiniteRankVectorBundle.{w} 𝕜 X) where
  /-- The linear map on the fibre over `x`. -/
  fiberMap (x : X) : V.Fiber x →ₗ[𝕜] W.Fiber x
  /-- Continuity of the induced map on total spaces. -/
  continuous_totalSpaceMap : Continuous (fun p : TotalSpace Unit V.Fiber =>
    (⟨p.proj, fiberMap p.proj p.2⟩ : TotalSpace Unit W.Fiber))

namespace Hom

variable {V W U : FiniteRankVectorBundle.{w} 𝕜 X}

/-- The bundled continuous map on total spaces induced by a bundle morphism. -/
def totalSpaceMap (f : Hom V W) : C(TotalSpace Unit V.Fiber, TotalSpace Unit W.Fiber) :=
  ⟨_, f.continuous_totalSpaceMap⟩

@[simp] theorem totalSpaceMap_mk (f : Hom V W) (x : X) (v : V.Fiber x) :
    f.totalSpaceMap ⟨x, v⟩ = ⟨x, f.fiberMap x v⟩ := (rfl)

@[simp] theorem proj_totalSpaceMap (f : Hom V W) (p : TotalSpace Unit V.Fiber) :
    (f.totalSpaceMap p).proj = p.proj := (rfl)

/-- Every bundle morphism restricts to a continuous linear map on each fibre. -/
theorem continuous_fiberMap (f : Hom V W) (x : X) : Continuous (f.fiberMap x) :=
  (W.totalSpaceMk_isInducing x).continuous_iff.2 <|
    f.continuous_totalSpaceMap.comp (V.totalSpaceMk_isInducing x).continuous

/-- The continuous linear map on the fibre over `x` induced by a bundle morphism. -/
def continuousLinearMap (f : Hom V W) (x : X) : V.Fiber x →L[𝕜] W.Fiber x :=
  ⟨f.fiberMap x, f.continuous_fiberMap x⟩

@[simp] theorem coe_continuousLinearMap (f : Hom V W) (x : X) :
    (f.continuousLinearMap x : V.Fiber x →ₗ[𝕜] W.Fiber x) = f.fiberMap x := (rfl)

instance : Zero (Hom V W) := ⟨⟨fun _ => 0, W.continuous_zeroSection.comp V.continuous_proj⟩⟩

instance : Add (Hom V W) :=
  ⟨fun f g => ⟨fun x => f.fiberMap x + g.fiberMap x,
    W.continuous_add f.continuous_totalSpaceMap g.continuous_totalSpaceMap⟩⟩

instance : Neg (Hom V W) :=
  ⟨fun f => ⟨fun x => -f.fiberMap x, by
    simpa only [neg_one_smul, LinearMap.neg_apply] using
      W.continuous_smul (continuous_const (y := (-1 : 𝕜))) f.continuous_totalSpaceMap⟩⟩

instance : Sub (Hom V W) := ⟨fun f g => f + -g⟩

instance : SMul ℕ (Hom V W) :=
  ⟨fun n f => ⟨fun x => n • f.fiberMap x, by
    simpa only [Nat.cast_smul_eq_nsmul, LinearMap.smul_apply] using
      W.continuous_smul (continuous_const (y := (n : 𝕜))) f.continuous_totalSpaceMap⟩⟩

instance : SMul ℤ (Hom V W) :=
  ⟨fun n f => ⟨fun x => n • f.fiberMap x, by
    simpa only [Int.cast_smul_eq_zsmul, LinearMap.smul_apply] using
      W.continuous_smul (continuous_const (y := (n : 𝕜))) f.continuous_totalSpaceMap⟩⟩

instance : AddCommGroup (Hom V W) :=
  Function.Injective.addCommGroup (fun f => f.fiberMap) (fun _ _ h => Hom.ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => funext fun _ => (sub_eq_add_neg _ _).symm)
    (fun _ _ => rfl) (fun _ _ => rfl)

end Hom

instance : Category (FiniteRankVectorBundle.{w} 𝕜 X) where
  Hom := Hom
  id _ := ⟨fun _ => LinearMap.id, continuous_id⟩
  comp f g := ⟨fun x => (g.fiberMap x).comp (f.fiberMap x),
    g.continuous_totalSpaceMap.comp f.continuous_totalSpaceMap⟩
  id_comp _ := Hom.ext (funext fun _ => LinearMap.id_comp _)
  comp_id _ := Hom.ext (funext fun _ => LinearMap.comp_id _)
  assoc _ _ _ := Hom.ext (funext fun _ => (LinearMap.comp_assoc _ _ _).symm)

variable {V W U : FiniteRankVectorBundle.{w} 𝕜 X}

/-- Morphisms of variable-rank vector bundles are determined by their fibrewise linear maps. -/
@[ext] theorem hom_ext {f g : V ⟶ W} (h : ∀ x, f.fiberMap x = g.fiberMap x) : f = g :=
  Hom.ext (funext h)

@[simp] theorem fiberMap_id (V : FiniteRankVectorBundle.{w} 𝕜 X) (x : X) :
    (𝟙 V : V ⟶ V).fiberMap x = LinearMap.id := (rfl)

@[simp] theorem fiberMap_comp (f : V ⟶ W) (g : W ⟶ U) (x : X) :
    (f ≫ g).fiberMap x = (g.fiberMap x).comp (f.fiberMap x) := (rfl)

@[simp] theorem totalSpaceMap_id (V : FiniteRankVectorBundle.{w} 𝕜 X) :
    (𝟙 V : V ⟶ V).totalSpaceMap = ContinuousMap.id _ := (rfl)

@[simp] theorem totalSpaceMap_comp (f : V ⟶ W) (g : W ⟶ U) :
    (f ≫ g).totalSpaceMap = g.totalSpaceMap.comp f.totalSpaceMap := (rfl)

instance : Preadditive (FiniteRankVectorBundle.{w} 𝕜 X) where
  homGroup V W := inferInstanceAs (AddCommGroup (Hom V W))
  add_comp _ _ _ _ _ h := hom_ext fun x => LinearMap.ext fun _ => (h.fiberMap x).map_add _ _
  comp_add _ _ _ _ _ _ := hom_ext fun _ => LinearMap.ext fun _ => rfl

@[simp] theorem fiberMap_zero (x : X) : (0 : V ⟶ W).fiberMap x = 0 := (rfl)

@[simp] theorem fiberMap_add (f g : V ⟶ W) (x : X) :
    (f + g).fiberMap x = f.fiberMap x + g.fiberMap x := (rfl)

@[simp] theorem fiberMap_neg (f : V ⟶ W) (x : X) :
    (-f).fiberMap x = -f.fiberMap x := (rfl)

@[simp] theorem fiberMap_sub (f g : V ⟶ W) (x : X) :
    (f - g).fiberMap x = f.fiberMap x - g.fiberMap x := by
  simp only [sub_eq_add_neg, fiberMap_add, fiberMap_neg]

@[simp] theorem fiberMap_nsmul (n : ℕ) (f : V ⟶ W) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := (rfl)

@[simp] theorem fiberMap_zsmul (n : ℤ) (f : V ⟶ W) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := (rfl)

/-- Passing to continuous maps of total spaces is faithful. -/
theorem totalSpaceMap_injective : Function.Injective (Hom.totalSpaceMap (V := V) (W := W)) :=
  fun _ _ h => hom_ext fun x => LinearMap.ext fun v =>
    TotalSpace.mk_inj.mp (congrArg (· ⟨x, v⟩) h)

/-- Faithful realization of variable-rank vector bundles by their glued total spaces. -/
-- Expose the object assignment so morphism types reduce to the glued total spaces.
@[expose] def totalSpaceFunctor : FiniteRankVectorBundle.{w} 𝕜 X ⥤ TopCat.{max u w} where
  obj V := TopCat.of (TotalSpace Unit V.Fiber)
  map f := TopCat.ofHom f.totalSpaceMap

@[simp] theorem totalSpaceFunctor_obj (V : FiniteRankVectorBundle.{w} 𝕜 X) :
    totalSpaceFunctor.obj V = TopCat.of (TotalSpace Unit V.Fiber) := (rfl)

@[simp] theorem totalSpaceFunctor_map_apply (f : V ⟶ W) (p : TotalSpace Unit V.Fiber) :
    totalSpaceFunctor.map f p = f.totalSpaceMap p := (rfl)

instance : (totalSpaceFunctor.{w} (𝕜 := 𝕜) (X := X)).Faithful where
  map_injective h := totalSpaceMap_injective (congrArg TopCat.Hom.hom h)

/-- Additive evaluation of a variable-rank vector bundle and its morphisms on the fibre at `x`. -/
-- Expose the object assignment so evaluated morphisms act on the actual fibres.
@[expose] def fiberFunctor (x : X) : FiniteRankVectorBundle.{w} 𝕜 X ⥤ ModuleCat.{w} 𝕜 where
  obj V := ModuleCat.of 𝕜 (V.Fiber x)
  map f := ModuleCat.ofHom (f.fiberMap x)

@[simp] theorem fiberFunctor_obj (x : X) (V : FiniteRankVectorBundle.{w} 𝕜 X) :
    (fiberFunctor x).obj V = ModuleCat.of 𝕜 (V.Fiber x) := (rfl)

@[simp] theorem fiberFunctor_map_apply (x : X) (f : V ⟶ W) (v : V.Fiber x) :
    (fiberFunctor x).map f v = f.fiberMap x v := (rfl)

instance (x : X) : (fiberFunctor.{w} (𝕜 := 𝕜) (X := X) x).Additive where
  map_add := by intros; rfl

/-- Bundle isomorphism from fibrewise linear equivalences with continuous total-space maps. -/
def isoMk (e : ∀ x, V.Fiber x ≃ₗ[𝕜] W.Fiber x)
    (h : Continuous (fun p : TotalSpace Unit V.Fiber =>
      (⟨p.proj, e p.proj p.2⟩ : TotalSpace Unit W.Fiber)))
    (h' : Continuous (fun p : TotalSpace Unit W.Fiber =>
      (⟨p.proj, (e p.proj).symm p.2⟩ : TotalSpace Unit V.Fiber))) : V ≅ W where
  hom := ⟨fun x => (e x).toLinearMap, h⟩
  inv := ⟨fun x => (e x).symm.toLinearMap, h'⟩
  hom_inv_id := hom_ext fun x => LinearMap.ext (e x).symm_apply_apply
  inv_hom_id := hom_ext fun x => LinearMap.ext (e x).apply_symm_apply

@[simp] theorem fiberMap_isoMk_hom (e : ∀ x, V.Fiber x ≃ₗ[𝕜] W.Fiber x) (h h') (x : X) :
    (isoMk e h h').hom.fiberMap x = (e x).toLinearMap := (rfl)

@[simp] theorem fiberMap_isoMk_inv (e : ∀ x, V.Fiber x ≃ₗ[𝕜] W.Fiber x) (h h') (x : X) :
    (isoMk e h h').inv.fiberMap x = (e x).symm.toLinearMap := (rfl)

end Category

section Constructors

/-- Bundled `VectorBundle` instances on a single rank-`m` stratum. -/
structure StratumBundle (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    {B : Type*} [TopologicalSpace B] (m : ℕ) (E : B → Type w)
    [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)] where
  /-- Total-space topology on the stratum. -/
  top : TopologicalSpace (TotalSpace (Fin m → 𝕜) E)
  /-- Fibre-bundle structure on the stratum. -/
  fb : letI := top; FiberBundle (Fin m → 𝕜) E
  /-- Vector-bundle structure on the stratum. -/
  vb : letI := top; letI := fb; VectorBundle 𝕜 (Fin m → 𝕜) E

section OfFixedRank

variable (𝕜) (n : ℕ) (E : X → Type w) [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)]
  [FiberBundle (Fin n → 𝕜) E] [VectorBundle 𝕜 (Fin n → 𝕜) E]

/-- Auxiliary stratum bundle structure used by `ofFixedRank`. -/
noncomputable def ofFixedRankStratum (m : ℕ) :
    StratumBundle 𝕜 m (fun x : {x : X // LocallyConstant.const X n x = m} => E x.1) :=
  if hm : n = m then by
    subst hm
    let inc : C({x : X // LocallyConstant.const X n x = n}, X) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    exact ⟨FiberwiseEquiv.totalSpaceTopology (Fin n → 𝕜) (E₁ := (inc : _ → X) *ᵖ E)
        (fun x => ContinuousLinearEquiv.refl 𝕜 (E x.1)),
      FiberwiseEquiv.fiberBundle (Fin n → 𝕜) (E₁ := (inc : _ → X) *ᵖ E)
        (fun x => ContinuousLinearEquiv.refl 𝕜 (E x.1)),
      FiberwiseEquiv.vectorBundle (𝕜 := 𝕜) (Fin n → 𝕜) (E₁ := (inc : _ → X) *ᵖ E)
        (fun x => ContinuousLinearEquiv.refl 𝕜 (E x.1))⟩
  else
    let S := {x : X // LocallyConstant.const X n x = m}
    have : IsEmpty S := ⟨fun x => hm ((congrFun (LocallyConstant.coe_const n) x.1).symm.trans x.2)⟩
    ⟨FiberwiseEquiv.totalSpaceTopology (Fin m → 𝕜)
        (E₁ := Bundle.Trivial S (Fin m → 𝕜)) isEmptyElim,
      FiberwiseEquiv.fiberBundle (Fin m → 𝕜)
        (E₁ := Bundle.Trivial S (Fin m → 𝕜)) isEmptyElim,
      FiberwiseEquiv.vectorBundle (𝕜 := 𝕜) (Fin m → 𝕜)
        (E₁ := Bundle.Trivial S (Fin m → 𝕜)) isEmptyElim⟩

/-- Embed a constant-rank Mathlib `VectorBundle 𝕜 (Fin n → 𝕜) E` into `FiniteRankVectorBundle`
with literally the same fibre family `E`. -/
-- Expose `rank` and `Fiber` projections so the dependent fibre family reduces to `E`.
@[expose, implicit_reducible]
noncomputable def ofFixedRank : FiniteRankVectorBundle.{w} 𝕜 X where
  rank := LocallyConstant.const X n
  Fiber := E
  addCommGroupFiber := inferInstance
  moduleFiber := inferInstance
  topologicalSpaceFiber := inferInstance
  topologicalSpaceStratum m := (ofFixedRankStratum 𝕜 n E m).top
  fiberBundleStratum m := (ofFixedRankStratum 𝕜 n E m).fb
  vectorBundleStratum m := (ofFixedRankStratum 𝕜 n E m).vb

@[simp] theorem rank_ofFixedRank : (ofFixedRank 𝕜 n E).rank = LocallyConstant.const X n := (rfl)

@[simp] theorem fiber_ofFixedRank (x : X) : (ofFixedRank 𝕜 n E).Fiber x = E x := (rfl)

private theorem topologicalSpaceStratum_ofFixedRank_self :
    (ofFixedRank 𝕜 n E).topologicalSpaceStratum n =
      FiberwiseEquiv.totalSpaceTopology (Fin n → 𝕜)
        (E₁ := ((⟨Subtype.val, continuous_subtype_val⟩ :
          C({x : X // LocallyConstant.const X n x = n}, X)) : _ → X) *ᵖ E)
        (E₂ := (ofFixedRank 𝕜 n E).StratumFiber n)
        (fun x => ContinuousLinearEquiv.refl 𝕜 (E x.1)) := by
  dsimp only [ofFixedRank]; rw [ofFixedRankStratum, dite_eq_left_iff.2 fun h => (h rfl).elim]

/-- Homeomorphism from the total space of `ofFixedRank 𝕜 n E` to `TotalSpace (Fin n → 𝕜) E`. -/
noncomputable def ofFixedRankHomeomorph :
    TotalSpace Unit (ofFixedRank 𝕜 n E).Fiber ≃ₜ TotalSpace (Fin n → 𝕜) E where
  toFun p := ⟨p.proj, p.2⟩
  invFun p := ⟨p.proj, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    let inc : C({x : X // LocallyConstant.const X n x = n}, X) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    have hglued : Continuous fun q : (ofFixedRank 𝕜 n E).GluedTotalSpace =>
        (⟨q.2.proj.1, q.2.2⟩ : TotalSpace (Fin n → 𝕜) E) := by
      refine continuous_sigma fun m => ?_
      by_cases hm : n = m
      · subst hm
        let tStr := FiberwiseEquiv.totalSpaceTopology (Fin n → 𝕜) (E₁ := (inc : _ → X) *ᵖ E)
          (E₂ := (ofFixedRank 𝕜 n E).StratumFiber n) (fun x => ContinuousLinearEquiv.refl 𝕜 (E x.1))
        have hc : @Continuous _ _ tStr _
            (fun q : TotalSpace (Fin n → 𝕜) ((ofFixedRank 𝕜 n E).StratumFiber n) =>
              (⟨q.proj.1, q.2⟩ : TotalSpace (Fin n → 𝕜) E)) :=
          @Continuous.congr _ _ tStr _ _ _
            ((Pullback.continuous_lift (Fin n → 𝕜) E (inc : _ → X)).comp
              (FiberwiseEquiv.continuous_totalSpace_to (Fin n → 𝕜)
                (E₁ := (inc : _ → X) *ᵖ E) (E₂ := (ofFixedRank 𝕜 n E).StratumFiber n)
                (fun x => ContinuousLinearEquiv.refl 𝕜 (E x.1)))) fun _ => rfl
        exact topologicalSpaceStratum_ofFixedRank_self 𝕜 n E ▸ hc
      · have : IsEmpty (TotalSpace (Fin m → 𝕜) ((ofFixedRank 𝕜 n E).StratumFiber m)) :=
          ⟨fun p => hm ((congrFun (LocallyConstant.coe_const n) p.proj.1).symm.trans p.proj.2)⟩
        exact continuous_of_discreteTopology
    exact (hglued.comp (ofFixedRank 𝕜 n E).totalSpaceHomeomorph.symm.continuous).congr fun _ => rfl
  continuous_invFun := by
    let inc : C({x : X // LocallyConstant.const X n x = n}, X) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    apply ((ofFixedRank 𝕜 n E).continuous_mk_iff_rankStrata
      (FiberBundle.continuous_proj (Fin n → 𝕜) E) (fun p => p.2)).2 fun m => ?_
    by_cases hm : n = m
    · subst hm
      refine (topologicalSpaceStratum_ofFixedRank_self 𝕜 n E).symm ▸
        (FiberwiseEquiv.continuous_totalSpace_iff (Fin n → 𝕜)
          (E₁ := (inc : _ → X) *ᵖ E) (E₂ := (ofFixedRank 𝕜 n E).StratumFiber n)
          (fun x => ContinuousLinearEquiv.refl 𝕜 (E x.1))).2 ?_
      rw [(inducing_pullbackTotalSpaceEmbedding (Fin n → 𝕜) E (inc : _ → X)).continuous_iff]
      simp only [Function.comp_def, pullbackTotalSpaceEmbedding, continuous_prodMk]
      exact ⟨((FiberBundle.continuous_proj (Fin n → 𝕜) E).comp
        continuous_subtype_val).subtype_mk fun y => y.2, continuous_subtype_val⟩
    · have : IsEmpty {y : TotalSpace (Fin n → 𝕜) E // (ofFixedRank 𝕜 n E).rank y.proj = m} :=
        ⟨fun y => hm ((congrFun (LocallyConstant.coe_const n) y.1.proj).symm.trans y.2)⟩
      exact continuous_of_discreteTopology

@[simp] theorem ofFixedRankHomeomorph_apply (p : TotalSpace Unit (ofFixedRank 𝕜 n E).Fiber) :
    ofFixedRankHomeomorph 𝕜 n E p = ⟨p.proj, p.2⟩ := (rfl)

@[simp] theorem ofFixedRankHomeomorph_symm_apply (p : TotalSpace (Fin n → 𝕜) E) :
    (ofFixedRankHomeomorph 𝕜 n E).symm p = ⟨p.proj, p.2⟩ := (rfl)

end OfFixedRank

variable (𝕜 X) in
/-- The rank-zero vector bundle with fibre `PUnit.{w + 1}` in fibre universe `w`. -/
noncomputable def zero : FiniteRankVectorBundle.{w} 𝕜 X :=
  let e : (Fin 0 → 𝕜) ≃L[𝕜] PUnit.{w + 1} :=
    { LinearEquiv.ofSubsingleton (Fin 0 → 𝕜) PUnit.{w + 1} with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  letI := FiberwiseEquiv.totalSpaceTopology (Fin 0 → 𝕜) (E₁ := Bundle.Trivial X _) fun _ => e
  letI := FiberwiseEquiv.fiberBundle (Fin 0 → 𝕜) (E₁ := Bundle.Trivial X _) fun _ => e
  haveI := FiberwiseEquiv.vectorBundle (𝕜 := 𝕜) (Fin 0 → 𝕜) (E₁ := Bundle.Trivial X _) fun _ => e
  ofFixedRank 𝕜 0 (fun _ : X => PUnit.{w + 1})

@[simp] theorem rank_zero : (zero.{w} 𝕜 X).rank = LocallyConstant.const X 0 := (rfl)

/-- The rank-zero bundle `zero 𝕜 X` is a zero object in `FiniteRankVectorBundle.{w} 𝕜 X`. -/
theorem isZero_zero : IsZero (zero.{w} 𝕜 X) := by
  rw [IsZero.iff_id_eq_zero]
  refine hom_ext fun x => LinearMap.ext fun _ => ?_
  have : Subsingleton ((zero.{w} 𝕜 X).Fiber x) := inferInstanceAs (Subsingleton PUnit.{w + 1})
  exact Subsingleton.elim _ _

noncomputable instance : HasZeroObject (FiniteRankVectorBundle.{w} 𝕜 X) :=
  ⟨⟨zero.{w} 𝕜 X, isZero_zero⟩⟩

section MapFibers

variable (V : FiniteRankVectorBundle.{w} 𝕜 X) {E₂ : X → Type w'}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  (e : ∀ x, V.Fiber x ≃L[𝕜] E₂ x)

/-- Transport the fibres of a variable-rank vector bundle along fibrewise continuous linear
equivalences into another universe `w'`. -/
-- Expose `rank` and `Fiber` projections so the transported fibre family reduces to `E₂`.
@[expose, implicit_reducible]
def mapFibers : FiniteRankVectorBundle.{w'} 𝕜 X where
  rank := V.rank
  Fiber := E₂
  addCommGroupFiber := inferInstance
  moduleFiber := inferInstance
  topologicalSpaceFiber := inferInstance
  topologicalSpaceStratum n :=
    FiberwiseEquiv.totalSpaceTopology (Fin n → 𝕜) (E₁ := V.StratumFiber n) (fun y => e y.1)
  fiberBundleStratum n :=
    FiberwiseEquiv.fiberBundle (Fin n → 𝕜) (E₁ := V.StratumFiber n) (fun y => e y.1)
  vectorBundleStratum n :=
    FiberwiseEquiv.vectorBundle (𝕜 := 𝕜) (Fin n → 𝕜) (E₁ := V.StratumFiber n) (fun y => e y.1)

@[simp] theorem rank_mapFibers : (V.mapFibers e).rank = V.rank := (rfl)

@[simp] theorem fiber_mapFibers (x : X) : (V.mapFibers e).Fiber x = E₂ x := (rfl)

/-- Total-space homeomorphism induced by `mapFibers`, applying `(e x).symm` on fibre `x`. -/
def mapFibersHomeomorph : TotalSpace Unit (V.mapFibers e).Fiber ≃ₜ TotalSpace Unit V.Fiber where
  toFun p := ⟨p.proj, (e p.proj).symm p.2⟩
  invFun p := ⟨p.proj, e p.proj p.2⟩
  left_inv p := TotalSpace.mk_inj.2 <| (e p.proj).apply_symm_apply p.2
  right_inv p := TotalSpace.mk_inj.2 <| (e p.proj).symm_apply_apply p.2
  continuous_toFun :=
    (V.continuous_mk_iff_rankStrata (V.mapFibers e).continuous_proj _).2 fun n =>
      (FiberwiseEquiv.continuous_totalSpace_to (Fin n → 𝕜) (E₁ := V.StratumFiber n)
        (E₂ := (V.mapFibers e).StratumFiber n) (fun y => e y.1)).comp <|
        ((V.mapFibers e).continuous_mk_iff_rankStrata (V.mapFibers e).continuous_proj
          (fun p => p.2)).1 continuous_id n
  continuous_invFun :=
    ((V.mapFibers e).continuous_mk_iff_rankStrata V.continuous_proj _).2 fun n =>
      (FiberwiseEquiv.continuous_totalSpace_iff (Fin n → 𝕜) (E₁ := V.StratumFiber n)
        (E₂ := (V.mapFibers e).StratumFiber n) (fun y => e y.1)).2 <|
        ((V.continuous_mk_iff_rankStrata V.continuous_proj (fun p => p.2)).1
          continuous_id n).congr fun p =>
            TotalSpace.mk_inj.2 ((e p.1.proj).symm_apply_apply p.1.2).symm

@[simp] theorem mapFibersHomeomorph_apply (p : TotalSpace Unit (V.mapFibers e).Fiber) :
    V.mapFibersHomeomorph e p = ⟨p.proj, (e p.proj).symm p.2⟩ := (rfl)

@[simp] theorem mapFibersHomeomorph_symm_apply (p : TotalSpace Unit V.Fiber) :
    (V.mapFibersHomeomorph e).symm p = ⟨p.proj, e p.proj p.2⟩ := (rfl)

end MapFibers

section ULift

section Obj

variable (V : FiniteRankVectorBundle.{w} 𝕜 X)

/-- Lift the fibres of a variable-rank vector bundle from `Type w` to `Type (max w w')`. -/
-- Expose `rank` and `Fiber` projections so lifted fibres reduce to `ULift (V.Fiber x)`.
@[expose, implicit_reducible]
def ulift : FiniteRankVectorBundle.{max w w'} 𝕜 X :=
  V.mapFibers fun x => (ContinuousLinearEquiv.ulift (R₁ := 𝕜) (M₁ := V.Fiber x)).symm

@[simp] theorem rank_ulift : (ulift.{w, w'} V).rank = V.rank := (rfl)

@[simp] theorem fiber_ulift (x : X) : (ulift.{w, w'} V).Fiber x = ULift.{w'} (V.Fiber x) := (rfl)

/-- Total-space homeomorphism for `ulift.{w, w'} V`, applying `ULift.down` on every fibre. -/
def uliftHomeomorph : TotalSpace Unit (ulift.{w, w'} V).Fiber ≃ₜ TotalSpace Unit V.Fiber :=
  V.mapFibersHomeomorph fun x => (ContinuousLinearEquiv.ulift (R₁ := 𝕜) (M₁ := V.Fiber x)).symm

@[simp] theorem uliftHomeomorph_apply (p : TotalSpace Unit (ulift.{w, w'} V).Fiber) :
    uliftHomeomorph.{w, w'} V p = ⟨p.proj, p.2.down⟩ := (rfl)

@[simp] theorem uliftHomeomorph_symm_apply (p : TotalSpace Unit V.Fiber) :
    (uliftHomeomorph.{w, w'} V).symm p = ⟨p.proj, ULift.up p.2⟩ := (rfl)

end Obj

variable (𝕜 X) in
/-- Fully faithful additive functor lifting the fibre universe of variable-rank vector bundles. -/
-- Expose the object assignment so composed functors see the lifted bundles.
@[expose] def uliftFunctor :
    FiniteRankVectorBundle.{w} 𝕜 X ⥤ FiniteRankVectorBundle.{max w w'} 𝕜 X where
  obj V := ulift.{w, w'} V
  map {V W} f :=
    { fiberMap x := (ULift.moduleEquiv : ULift.{w'} (W.Fiber x) ≃ₗ[𝕜] W.Fiber x).symm.toLinearMap
        |>.comp ((f.fiberMap x).comp
          (ULift.moduleEquiv : ULift.{w'} (V.Fiber x) ≃ₗ[𝕜] V.Fiber x).toLinearMap)
      continuous_totalSpaceMap :=
        ((uliftHomeomorph.{w, w'} W).symm.continuous.comp <|
          f.totalSpaceMap.continuous.comp (uliftHomeomorph.{w, w'} V).continuous).congr fun _ => by
            simp only [Function.comp_apply, uliftHomeomorph_apply, Hom.totalSpaceMap_mk,
              uliftHomeomorph_symm_apply]; rfl }

@[simp] theorem uliftFunctor_obj (V : FiniteRankVectorBundle.{w} 𝕜 X) :
    (uliftFunctor.{w, w'} 𝕜 X).obj V = ulift.{w, w'} V := (rfl)

@[simp] theorem fiberMap_uliftFunctor_map {V W : FiniteRankVectorBundle.{w} 𝕜 X}
    (f : V ⟶ W) (x : X) :
    ((uliftFunctor.{w, w'} 𝕜 X).map f).fiberMap x =
      (ULift.moduleEquiv : ULift.{w'} (W.Fiber x) ≃ₗ[𝕜] W.Fiber x).symm.toLinearMap.comp
        ((f.fiberMap x).comp
          (ULift.moduleEquiv : ULift.{w'} (V.Fiber x) ≃ₗ[𝕜] V.Fiber x).toLinearMap) := (rfl)

instance : (uliftFunctor.{w, w'} 𝕜 X).Additive where
  map_add := by intros; exact hom_ext fun _ => LinearMap.ext fun _ => rfl

instance : (uliftFunctor.{w, w'} 𝕜 X).Faithful where
  map_injective {V W _ _} h := hom_ext fun x => LinearMap.ext fun v =>
    congrArg ULift.down
      (congrArg (fun φ : ulift.{w, w'} V ⟶ ulift.{w, w'} W => φ.fiberMap x (ULift.up v)) h)

instance : (uliftFunctor.{w, w'} 𝕜 X).Full where
  map_surjective {V W} φ :=
    let ψ : ulift.{w, w'} V ⟶ ulift.{w, w'} W := φ
    ⟨{ fiberMap x := (ULift.moduleEquiv : ULift.{w'} (W.Fiber x) ≃ₗ[𝕜] W.Fiber x).toLinearMap.comp
        ((ψ.fiberMap x).comp
          (ULift.moduleEquiv : ULift.{w'} (V.Fiber x) ≃ₗ[𝕜] V.Fiber x).symm.toLinearMap)
       continuous_totalSpaceMap := ((uliftHomeomorph.{w, w'} W).continuous.comp <|
         ψ.totalSpaceMap.continuous.comp (uliftHomeomorph.{w, w'} V).symm.continuous).congr
         fun _ => by
           simp only [Function.comp_apply, uliftHomeomorph_symm_apply, Hom.totalSpaceMap_mk,
             uliftHomeomorph_apply]; rfl },
      hom_ext fun _ => LinearMap.ext fun _ => rfl⟩

end ULift

end Constructors

end FiniteRankVectorBundle

end TauCeti

namespace CategoryTheory.Iso

open TauCeti

universe w v u

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X] {V W : FiniteRankVectorBundle.{w} 𝕜 X}

/-- Isomorphic variable-rank vector bundles have equal locally constant rank functions. -/
theorem finiteRankVectorBundle_rank_eq (e : V ≅ W) : V.rank = W.rank := by
  ext x
  rw [← V.finrank_fiber x, ← W.finrank_fiber x]
  exact ((FiniteRankVectorBundle.fiberFunctor x).mapIso e).toLinearEquiv.finrank_eq

end CategoryTheory.Iso
