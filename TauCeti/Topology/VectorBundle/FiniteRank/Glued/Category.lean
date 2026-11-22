/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Glued.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Preadditive category and functors for variable-rank bundles

Continuous fibrewise-linear morphisms `VariableRankBundle.Hom`, their `Category` and
`Preadditive` structures (`VariableRankBundle.category`, `VariableRankBundle.preadditive`),
`totalSpaceFunctor`, `fiberFunctor`, `isoMk`, `isoOfTotalSpaceHomeomorph`, and
`CategoryTheory.Iso.variableRankBundle_rank_eq` over the glued total-space topology of
`TauCeti.Topology.VectorBundle.FiniteRank.Glued.Basic`.
-/

public section
open Bundle CategoryTheory Topology
namespace TauCeti
namespace VariableRankBundle
universe u v w b
attribute [local instance] addCommGroupFiber moduleFiber instTopologicalSpaceTotalSpace

variable {B : Type b} {𝕜 : Type v} {X : Type u} {Fiber : B → X → Type w}
  [NontriviallyNormedField 𝕜] [TopologicalSpace X] [VariableRankBundle B 𝕜 X Fiber]

/-- A morphism of variable-rank bundles is a family of `𝕜`-linear maps on fibres whose induced map
on the glued total spaces is continuous. -/
@[ext] structure Hom (V W : B) where
  /-- The `𝕜`-linear map on the fibre over `x`. -/
  fiberMap (x : X) : Fiber V x →ₗ[𝕜] Fiber W x
  /-- Continuity of the induced map on total spaces in the glued bundle topologies. -/
  continuous_totalSpaceMap : Continuous (fun p : TotalSpace Unit (Fiber V) ↦
    (⟨p.proj, fiberMap p.proj p.snd⟩ : TotalSpace Unit (Fiber W)))

namespace Hom
variable {V W : B}
/-- The bundled continuous map of total spaces induced by a bundle morphism. -/
def totalSpaceMap (f : Hom V W) : C(TotalSpace Unit (Fiber V), TotalSpace Unit (Fiber W)) :=
  ⟨_, f.continuous_totalSpaceMap⟩
@[simp] theorem totalSpaceMap_mk (f : Hom V W) (x : X) (v : Fiber V x) :
    f.totalSpaceMap ⟨x, v⟩ = ⟨x, f.fiberMap x v⟩ := by rfl
@[simp] theorem proj_totalSpaceMap (f : Hom V W) (p : TotalSpace Unit (Fiber V)) :
    (f.totalSpaceMap p).proj = p.proj := by rfl
instance : Zero (Hom V W) := ⟨⟨fun _ ↦ 0, (continuous_zeroSection W).comp (continuous_proj V)⟩⟩
instance : Add (Hom V W) := ⟨fun f g ↦ ⟨fun x ↦ f.fiberMap x + g.fiberMap x,
  continuous_add W f.continuous_totalSpaceMap g.continuous_totalSpaceMap⟩⟩
instance : Neg (Hom V W) := ⟨fun f ↦ ⟨fun x ↦ -f.fiberMap x, by
  simpa only [neg_one_smul, LinearMap.neg_apply] using
    continuous_smul W (continuous_const (y := (-1 : 𝕜))) f.continuous_totalSpaceMap⟩⟩
instance : Sub (Hom V W) := ⟨fun f g ↦ f + -g⟩
instance : SMul ℕ (Hom V W) := ⟨fun n f ↦ ⟨fun x ↦ n • f.fiberMap x, by
  simpa only [Nat.cast_smul_eq_nsmul, LinearMap.smul_apply] using
    continuous_smul W (continuous_const (y := (n : 𝕜))) f.continuous_totalSpaceMap⟩⟩
instance : SMul ℤ (Hom V W) := ⟨fun n f ↦ ⟨fun x ↦ n • f.fiberMap x, by
  simpa only [Int.cast_smul_eq_zsmul, LinearMap.smul_apply] using
    continuous_smul W (continuous_const (y := (n : 𝕜))) f.continuous_totalSpaceMap⟩⟩
/-- Bundle morphisms form an abelian group under fibrewise operations. -/
instance : AddCommGroup (Hom V W) :=
  Function.Injective.addCommGroup (fun f ↦ f.fiberMap) (fun _ _ h ↦ Hom.ext h) rfl (fun _ _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ _ ↦ funext fun _ ↦ (sub_eq_add_neg _ _).symm)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
end Hom

/-- The category structure on a `VariableRankBundle` type `B`, with morphisms `Hom`. -/
-- Expose `Hom`, `id`, and `comp` so concrete category instances reduce `V ⟶ W` to `Hom V W`.
@[expose, instance_reducible] def category : Category B where
  Hom := Hom
  id _ := { fiberMap _ := LinearMap.id, continuous_totalSpaceMap := continuous_id }
  comp f g :=
    { fiberMap x := (g.fiberMap x).comp (f.fiberMap x)
      continuous_totalSpaceMap := g.continuous_totalSpaceMap.comp f.continuous_totalSpaceMap }
  id_comp _ := Hom.ext (funext fun _ ↦ LinearMap.ext fun _ ↦ rfl)
  comp_id _ := Hom.ext (funext fun _ ↦ LinearMap.ext fun _ ↦ rfl)
  assoc _ _ _ := Hom.ext (funext fun _ ↦ LinearMap.ext fun _ ↦ rfl)
attribute [local instance] category

/-- The preadditive structure on a `VariableRankBundle` category `B`. -/
-- Expose `homGroup` so morphism arithmetic reduces to the pointwise `Hom` group operations.
@[expose, instance_reducible] def preadditive : Preadditive B where
  homGroup P Q := inferInstanceAs (AddCommGroup (Hom P Q))
  add_comp _ _ _ _ _ h := Hom.ext (funext fun x ↦ LinearMap.ext fun _ ↦ (h.fiberMap x).map_add _ _)
  comp_add _ _ _ _ _ _ := Hom.ext (funext fun _ ↦ LinearMap.ext fun _ ↦ rfl)
attribute [local instance] preadditive

variable {V W U : B}

/-- Bundle morphisms are determined by their linear maps on every fibre. -/
@[ext] theorem hom_ext {f g : V ⟶ W} (h : ∀ x, f.fiberMap x = g.fiberMap x) : f = g :=
  Hom.ext (funext h)
@[simp] theorem fiberMap_id (V : B) (x : X) : (𝟙 V : V ⟶ V).fiberMap x = LinearMap.id := by rfl
@[simp] theorem fiberMap_comp (f : V ⟶ W) (g : W ⟶ U) (x : X) :
    (f ≫ g).fiberMap x = (g.fiberMap x).comp (f.fiberMap x) := by rfl
@[simp] theorem totalSpaceMap_id (V : B) :
    (𝟙 V : V ⟶ V).totalSpaceMap = ContinuousMap.id _ := by rfl
@[simp] theorem totalSpaceMap_comp (f : V ⟶ W) (g : W ⟶ U) :
    (f ≫ g).totalSpaceMap = g.totalSpaceMap.comp f.totalSpaceMap := by rfl
/-- Passing to the induced continuous maps on glued total spaces is faithful. -/
theorem totalSpaceMap_injective : Function.Injective (Hom.totalSpaceMap (V := V) (W := W)) :=
  fun _ _ h ↦ hom_ext fun x ↦ LinearMap.ext fun v ↦
    TotalSpace.mk_inj.mp (congrArg (fun k ↦ k ⟨x, v⟩) h)
@[simp] theorem fiberMap_zero (x : X) : (0 : V ⟶ W).fiberMap x = 0 := by rfl
@[simp] theorem fiberMap_add (f g : V ⟶ W) (x : X) :
    (f + g).fiberMap x = f.fiberMap x + g.fiberMap x := by rfl
@[simp] theorem fiberMap_neg (f : V ⟶ W) (x : X) : (-f).fiberMap x = -f.fiberMap x := by rfl
@[simp] theorem fiberMap_sub (f g : V ⟶ W) (x : X) :
    (f - g).fiberMap x = f.fiberMap x - g.fiberMap x := by
  simp only [sub_eq_add_neg, fiberMap_add, fiberMap_neg]
@[simp] theorem fiberMap_nsmul (n : ℕ) (f : V ⟶ W) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := by rfl
@[simp] theorem fiberMap_zsmul (n : ℤ) (f : V ⟶ W) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := by rfl

variable (B) in
/-- Realize variable-rank bundles and their morphisms as topological spaces and continuous maps. -/
-- Expose the object assignment so morphism types reduce to the glued total spaces.
@[expose] def totalSpaceFunctor : B ⥤ TopCat.{max u w} where
  obj V := TopCat.of (TotalSpace Unit (Fiber V))
  map f := TopCat.ofHom f.totalSpaceMap
@[simp] theorem totalSpaceFunctor_obj (V : B) :
    (totalSpaceFunctor B).obj V = TopCat.of (TotalSpace Unit (Fiber V)) := by rfl
@[simp] theorem totalSpaceFunctor_map_apply (f : V ⟶ W) (p : TotalSpace Unit (Fiber V)) :
    (totalSpaceFunctor B).map f p = f.totalSpaceMap p := by rfl
instance : (totalSpaceFunctor B).Faithful where
  map_injective h := totalSpaceMap_injective (congrArg TopCat.Hom.hom h)

variable (B) in
/-- Evaluate a variable-rank bundle and its morphisms on the fibre at `x`. -/
-- Expose the object assignment so evaluated morphisms act on `Fiber V x`.
@[expose] def fiberFunctor (x : X) : B ⥤ ModuleCat.{w} 𝕜 where
  obj V := ModuleCat.of 𝕜 (Fiber V x)
  map f := ModuleCat.ofHom (f.fiberMap x)
@[simp] theorem fiberFunctor_obj (x : X) (V : B) :
    (fiberFunctor B x).obj V = ModuleCat.of 𝕜 (Fiber V x) := by rfl
@[simp] theorem fiberFunctor_map_apply (x : X) (f : V ⟶ W) (v : Fiber V x) :
    (fiberFunctor B x).map f v = f.fiberMap x v := by rfl
instance (x : X) : (fiberFunctor B x).Additive where map_add := by intros; rfl

section Iso
variable (e : ∀ x, Fiber V x ≃ₗ[𝕜] Fiber W x)
/-- Construct an isomorphism of variable-rank bundles from fibrewise linear equivalences whose
forward and inverse total-space maps are continuous. -/
def isoMk (h : Continuous (fun p : TotalSpace Unit (Fiber V) ↦
      (⟨p.proj, e p.proj p.snd⟩ : TotalSpace Unit (Fiber W))))
    (h' : Continuous (fun p : TotalSpace Unit (Fiber W) ↦
      (⟨p.proj, (e p.proj).symm p.snd⟩ : TotalSpace Unit (Fiber V)))) : V ≅ W where
  hom := ⟨fun x ↦ (e x).toLinearMap, h⟩
  inv := ⟨fun x ↦ (e x).symm.toLinearMap, h'⟩
  hom_inv_id := hom_ext fun x ↦ LinearMap.ext (e x).symm_apply_apply
  inv_hom_id := hom_ext fun x ↦ LinearMap.ext (e x).apply_symm_apply
@[simp] theorem fiberMap_isoMk_hom (h h') (x : X) :
    (isoMk e h h').hom.fiberMap x = (e x).toLinearMap := by rfl
@[simp] theorem fiberMap_isoMk_inv (h h') (x : X) :
    (isoMk e h h').inv.fiberMap x = (e x).symm.toLinearMap := by rfl

variable (H : TotalSpace Unit (Fiber V) ≃ₜ TotalSpace Unit (Fiber W))
  (hH : ∀ x v, H ⟨x, v⟩ = ⟨x, e x v⟩)
/-- Construct an isomorphism `V ≅ W` from fibrewise linear equivalences `e` that agree with a
glued total-space homeomorphism `H`. -/
def isoOfTotalSpaceHomeomorph : V ≅ W :=
  isoMk e (H.continuous.congr fun ⟨x, v⟩ ↦ hH x v)
    (H.symm.continuous.congr fun ⟨x, w⟩ ↦ by
      have h := congrArg H.symm (hH x ((e x).symm w))
      rw [H.symm_apply_apply, LinearEquiv.apply_symm_apply] at h; exact h.symm)
@[simp] theorem fiberMap_isoOfTotalSpaceHomeomorph_hom (x : X) :
    (isoOfTotalSpaceHomeomorph e H hH).hom.fiberMap x = (e x).toLinearMap := by rfl
@[simp] theorem fiberMap_isoOfTotalSpaceHomeomorph_inv (x : X) :
    (isoOfTotalSpaceHomeomorph e H hH).inv.fiberMap x = (e x).symm.toLinearMap := by rfl
end Iso
end VariableRankBundle
end TauCeti

namespace CategoryTheory.Iso
open TauCeti TauCeti.VariableRankBundle
universe u v w b
attribute [local instance] VariableRankBundle.category VariableRankBundle.addCommGroupFiber
  VariableRankBundle.moduleFiber
/-- Isomorphic variable-rank bundles have the same locally constant rank function, even on
noncompact or disconnected bases. -/
theorem variableRankBundle_rank_eq {B : Type b} {𝕜 : Type v} {X : Type u} {Fiber : B → X → Type w}
    [NontriviallyNormedField 𝕜] [TopologicalSpace X] [VariableRankBundle B 𝕜 X Fiber] {V W : B}
    (e : V ≅ W) : rank V = rank W := by
  ext x; exact (finrank_fiber V x).symm.trans
    ((((fiberFunctor B x).mapIso e).toLinearEquiv.finrank_eq).trans (finrank_fiber W x))
end CategoryTheory.Iso
