/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Topology.Category.TopCat.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic

/-!
# The preadditive category of variable-rank topological vector bundles

Objects of `TauCeti.FiniteRankBundle.{w} 𝕜 X` form a preadditive category whose morphisms are
fibrewise `𝕜`-linear maps continuous on the glued total spaces `TotalSpace Unit B.Fiber`. Neither
rank boundedness across components, compactness or separation of `X`, nor completeness of `𝕜` is
assumed.

Because every fibre embeds into the glued total space
(`TauCeti.FiniteRankBundle.isEmbedding_totalSpaceMk`), each bundle morphism induces a continuous
linear map on every fibre (`TauCeti.FiniteRankBundle.Hom.continuousLinearMap`).
`TauCeti.FiniteRankBundle.totalSpaceFunctor` faithfully realizes bundles and morphisms in `TopCat`,
while `TauCeti.FiniteRankBundle.fiberFunctor` additively evaluates at each base point in
`ModuleCat 𝕜` and is jointly faithful (`TauCeti.FiniteRankBundle.hom_ext_of_fiberFunctor`).

Isomorphic bundles have equal locally constant rank
(`CategoryTheory.Iso.finiteRankBundle_rank_eq`), and `TauCeti.FiniteRankBundle.isoMk` constructs
categorical isomorphisms from fibrewise linear equivalences with continuous forward and inverse
total-space maps.
-/

public section

open Bundle CategoryTheory Topology

namespace TauCeti.FiniteRankBundle

universe w u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

/-- A morphism of variable-rank topological vector bundles is a `𝕜`-linear map on each fibre whose
induced map on the glued total spaces is continuous. -/
@[ext]
structure Hom (B₁ B₂ : FiniteRankBundle.{w} 𝕜 X) where
  /-- The linear map on the fibre over `x`. -/
  fiberMap (x : X) : B₁.Fiber x →ₗ[𝕜] B₂.Fiber x
  /-- Continuity on the glued total spaces. -/
  continuous_totalSpaceMap : Continuous (fun p : TotalSpace Unit B₁.Fiber ↦
    (⟨p.proj, fiberMap p.proj p.2⟩ : TotalSpace Unit B₂.Fiber))

namespace Hom

variable {B₁ B₂ B₃ : FiniteRankBundle.{w} 𝕜 X}

/-- The continuous map of glued total spaces induced by a bundle morphism. -/
def totalSpaceMap (f : Hom B₁ B₂) : C(TotalSpace Unit B₁.Fiber, TotalSpace Unit B₂.Fiber) :=
  ⟨_, f.continuous_totalSpaceMap⟩

@[simp]
theorem totalSpaceMap_mk (f : Hom B₁ B₂) (x : X) (v : B₁.Fiber x) :
    f.totalSpaceMap ⟨x, v⟩ = ⟨x, f.fiberMap x v⟩ := (rfl)

@[simp]
theorem proj_totalSpaceMap (f : Hom B₁ B₂) (p : TotalSpace Unit B₁.Fiber) :
    (f.totalSpaceMap p).proj = p.proj := (rfl)

/-- Every bundle morphism is continuous on each fibre, without assuming `CompleteSpace 𝕜`. -/
theorem continuous_fiberMap (f : Hom B₁ B₂) (x : X) : Continuous (f.fiberMap x) := by
  rw [(B₂.isEmbedding_totalSpaceMk x).isInducing.continuous_iff]
  exact f.continuous_totalSpaceMap.comp (B₁.continuous_totalSpaceMk x)

/-- The continuous linear map induced by a bundle morphism on the fibre over `x`. -/
def continuousLinearMap (f : Hom B₁ B₂) (x : X) : B₁.Fiber x →L[𝕜] B₂.Fiber x :=
  ⟨f.fiberMap x, f.continuous_fiberMap x⟩

@[simp]
theorem coe_continuousLinearMap (f : Hom B₁ B₂) (x : X) :
    (f.continuousLinearMap x : B₁.Fiber x →ₗ[𝕜] B₂.Fiber x) = f.fiberMap x := (rfl)

@[simp]
theorem continuousLinearMap_apply (f : Hom B₁ B₂) (x : X) (v : B₁.Fiber x) :
    f.continuousLinearMap x v = f.fiberMap x v := (rfl)

end Hom

instance : Category (FiniteRankBundle.{w} 𝕜 X) where
  Hom := Hom
  id _ :=
    { fiberMap _ := LinearMap.id
      continuous_totalSpaceMap := continuous_id }
  comp f g :=
    { fiberMap x := (g.fiberMap x).comp (f.fiberMap x)
      continuous_totalSpaceMap := g.continuous_totalSpaceMap.comp f.continuous_totalSpaceMap }
  id_comp _ := by ext x v; rfl
  comp_id _ := by ext x v; rfl
  assoc _ _ _ := by ext x v; rfl

variable {B₁ B₂ B₃ : FiniteRankBundle.{w} 𝕜 X}

/-- Bundle morphisms are determined by their linear maps on every fibre. -/
@[ext]
theorem hom_ext {f g : B₁ ⟶ B₂} (h : ∀ x, f.fiberMap x = g.fiberMap x) : f = g :=
  Hom.ext (funext h)

@[simp]
theorem fiberMap_id (B : FiniteRankBundle.{w} 𝕜 X) (x : X) :
    (𝟙 B : B ⟶ B).fiberMap x = LinearMap.id := (rfl)

@[simp]
theorem fiberMap_comp (f : B₁ ⟶ B₂) (g : B₂ ⟶ B₃) (x : X) :
    (f ≫ g).fiberMap x = (g.fiberMap x).comp (f.fiberMap x) := (rfl)

@[simp]
theorem totalSpaceMap_id (B : FiniteRankBundle.{w} 𝕜 X) :
    (𝟙 B : B ⟶ B).totalSpaceMap = ContinuousMap.id _ := (rfl)

@[simp]
theorem totalSpaceMap_comp (f : B₁ ⟶ B₂) (g : B₂ ⟶ B₃) :
    (f ≫ g).totalSpaceMap = g.totalSpaceMap.comp f.totalSpaceMap := (rfl)

/-- Passing to the continuous map of glued total spaces is faithful. -/
theorem totalSpaceMap_injective :
    Function.Injective (Hom.totalSpaceMap (B₁ := B₁) (B₂ := B₂)) := by
  intro f g h
  refine hom_ext fun x ↦ LinearMap.ext fun v ↦ ?_
  exact TotalSpace.mk_inj.mp (congrArg (fun k ↦ k ⟨x, v⟩) h)

namespace Hom

instance : Zero (B₁ ⟶ B₂) where
  zero := ⟨fun _ ↦ 0, B₂.continuous_zeroSection.comp B₁.continuous_proj⟩

instance : Add (B₁ ⟶ B₂) where
  add f g := ⟨fun x ↦ f.fiberMap x + g.fiberMap x,
    B₂.continuous_add f.continuous_totalSpaceMap g.continuous_totalSpaceMap⟩

instance : Neg (B₁ ⟶ B₂) where
  neg f := ⟨fun x ↦ -f.fiberMap x, by
    simpa only [neg_one_smul, LinearMap.neg_apply] using
      B₂.continuous_smul (continuous_const (y := (-1 : 𝕜))) f.continuous_totalSpaceMap⟩

instance : Sub (B₁ ⟶ B₂) where
  sub f g := f + -g

instance : SMul ℕ (B₁ ⟶ B₂) where
  smul n f := ⟨fun x ↦ n • f.fiberMap x, by
    simpa only [Nat.cast_smul_eq_nsmul, LinearMap.smul_apply] using
      B₂.continuous_smul (continuous_const (y := (n : 𝕜))) f.continuous_totalSpaceMap⟩

instance : SMul ℤ (B₁ ⟶ B₂) where
  smul n f := ⟨fun x ↦ n • f.fiberMap x, by
    simpa only [Int.cast_smul_eq_zsmul, LinearMap.smul_apply] using
      B₂.continuous_smul (continuous_const (y := (n : 𝕜))) f.continuous_totalSpaceMap⟩

instance : AddCommGroup (B₁ ⟶ B₂) :=
  Function.Injective.addCommGroup (fun f ↦ f.fiberMap) (fun _ _ h ↦ Hom.ext h)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ funext fun _ ↦ (sub_eq_add_neg _ _).symm)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end Hom

/-- Variable-rank topological vector bundles form a preadditive category under pointwise fibre
operations. -/
instance : Preadditive (FiniteRankBundle.{w} 𝕜 X) where
  add_comp _ _ _ f g h := hom_ext fun x ↦ LinearMap.ext fun _ ↦ (h.fiberMap x).map_add _ _
  comp_add _ _ _ _ _ _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

@[simp]
theorem fiberMap_zero (x : X) : (0 : B₁ ⟶ B₂).fiberMap x = 0 := (rfl)

@[simp]
theorem fiberMap_add (f g : B₁ ⟶ B₂) (x : X) :
    (f + g).fiberMap x = f.fiberMap x + g.fiberMap x := (rfl)

@[simp]
theorem fiberMap_neg (f : B₁ ⟶ B₂) (x : X) : (-f).fiberMap x = -f.fiberMap x := (rfl)

@[simp]
theorem fiberMap_sub (f g : B₁ ⟶ B₂) (x : X) :
    (f - g).fiberMap x = f.fiberMap x - g.fiberMap x := by
  simp only [sub_eq_add_neg, fiberMap_add, fiberMap_neg]

@[simp]
theorem fiberMap_nsmul (n : ℕ) (f : B₁ ⟶ B₂) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := (rfl)

@[simp]
theorem fiberMap_zsmul (n : ℤ) (f : B₁ ⟶ B₂) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := (rfl)

/-- Realize variable-rank bundles and morphisms as glued total spaces and continuous maps. -/
-- Expose the object assignment so morphism types reduce to the glued total spaces.
@[expose]
def totalSpaceFunctor : FiniteRankBundle.{w} 𝕜 X ⥤ TopCat.{max u w} where
  obj B := TopCat.of (TotalSpace Unit B.Fiber)
  map f := TopCat.ofHom f.totalSpaceMap

@[simp]
theorem totalSpaceFunctor_obj (B : FiniteRankBundle.{w} 𝕜 X) :
    totalSpaceFunctor.obj B = TopCat.of (TotalSpace Unit B.Fiber) := (rfl)

@[simp]
theorem totalSpaceFunctor_map_apply (f : B₁ ⟶ B₂) (p : TotalSpace Unit B₁.Fiber) :
    totalSpaceFunctor.map f p = f.totalSpaceMap p := (rfl)

instance : (totalSpaceFunctor.{w} (𝕜 := 𝕜) (X := X)).Faithful where
  map_injective h := totalSpaceMap_injective (congrArg TopCat.Hom.hom h)

/-- Evaluate a variable-rank bundle and its morphisms on the fibre at `x`. -/
-- Expose the object assignment so evaluated morphisms act directly on `B.Fiber x`.
@[expose]
def fiberFunctor (x : X) : FiniteRankBundle.{w} 𝕜 X ⥤ ModuleCat.{w} 𝕜 where
  obj B := ModuleCat.of 𝕜 (B.Fiber x)
  map f := ModuleCat.ofHom (f.fiberMap x)

@[simp]
theorem fiberFunctor_obj (x : X) (B : FiniteRankBundle.{w} 𝕜 X) :
    (fiberFunctor x).obj B = ModuleCat.of 𝕜 (B.Fiber x) := (rfl)

@[simp]
theorem fiberFunctor_map_apply (x : X) (f : B₁ ⟶ B₂) (v : B₁.Fiber x) :
    (fiberFunctor x).map f v = f.fiberMap x v := (rfl)

instance (x : X) : (fiberFunctor.{w} (𝕜 := 𝕜) x).Additive where
  map_add := by intros; rfl

/-- The fibre evaluation functors are jointly faithful, including over an empty base. -/
theorem hom_ext_of_fiberFunctor {f g : B₁ ⟶ B₂}
    (h : ∀ x : X, (fiberFunctor x).map f = (fiberFunctor x).map g) : f = g :=
  hom_ext fun x ↦ congrArg ModuleCat.Hom.hom (h x)

/-- A bundle morphism that is bijective on every fibre forces equality of locally constant ranks. -/
theorem rank_eq_of_bijective (f : B₁ ⟶ B₂) (hf : ∀ x, Function.Bijective (f.fiberMap x)) :
    B₁.rank = B₂.rank := by
  ext x
  calc
    B₁.rank x = Module.finrank 𝕜 (B₁.Fiber x) := (B₁.finrank_fiber x).symm
    _ = Module.finrank 𝕜 (B₂.Fiber x) := (LinearEquiv.ofBijective (f.fiberMap x) (hf x)).finrank_eq
    _ = B₂.rank x := B₂.finrank_fiber x

/-- Construct an isomorphism in `FiniteRankBundle.{w} 𝕜 X` from fibrewise linear equivalences
whose forward and inverse total-space maps are continuous. -/
def isoMk (e : ∀ x, B₁.Fiber x ≃ₗ[𝕜] B₂.Fiber x)
    (h : Continuous (fun p : TotalSpace Unit B₁.Fiber ↦
      (⟨p.proj, e p.proj p.2⟩ : TotalSpace Unit B₂.Fiber)))
    (h' : Continuous (fun p : TotalSpace Unit B₂.Fiber ↦
      (⟨p.proj, (e p.proj).symm p.2⟩ : TotalSpace Unit B₁.Fiber))) : B₁ ≅ B₂ where
  hom := ⟨fun x ↦ (e x).toLinearMap, h⟩
  inv := ⟨fun x ↦ (e x).symm.toLinearMap, h'⟩
  hom_inv_id := hom_ext fun x ↦ LinearMap.ext (e x).symm_apply_apply
  inv_hom_id := hom_ext fun x ↦ LinearMap.ext (e x).apply_symm_apply

@[simp]
theorem fiberMap_isoMk_hom (e : ∀ x, B₁.Fiber x ≃ₗ[𝕜] B₂.Fiber x) (h h') (x : X) :
    (isoMk e h h').hom.fiberMap x = (e x).toLinearMap := (rfl)

@[simp]
theorem fiberMap_isoMk_inv (e : ∀ x, B₁.Fiber x ≃ₗ[𝕜] B₂.Fiber x) (h h') (x : X) :
    (isoMk e h h').inv.fiberMap x = (e x).symm.toLinearMap := (rfl)

end TauCeti.FiniteRankBundle

namespace CategoryTheory.Iso

open TauCeti

universe w u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X] {B₁ B₂ : FiniteRankBundle.{w} 𝕜 X}

/-- Isomorphic variable-rank bundles have the same locally constant rank. -/
theorem finiteRankBundle_rank_eq (e : B₁ ≅ B₂) : B₁.rank = B₂.rank :=
  FiniteRankBundle.rank_eq_of_bijective e.hom fun x ↦
    ((FiniteRankBundle.fiberFunctor x).mapIso e).toLinearEquiv.bijective

end CategoryTheory.Iso
