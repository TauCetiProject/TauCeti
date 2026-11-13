/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Category
public import TauCeti.Topology.VectorBundle.Section
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

import TauCeti.Topology.VectorBundle.Smul

/-!
# Additive structure on variable-rank bundle atlases

Continuous fibrewise-linear maps between `TauCeti.FiniteRankAtlas` objects form abelian
groups under pointwise operations, and composition is bilinear. Thus these
variable-rank bundle atlases form a preadditive category, without a bounded-rank or
finite-cover hypothesis on the base.

The continuity criterion `TauCeti.FiniteRankAtlas.continuous_mk_iff_rankStrata` reduces a map
into a reconstructed total space to maps into its native vector-bundle cores on the
clopen rank strata. Fibrewise arithmetic is continuous by this criterion and the
native bundle trivializations. Evaluation at any base point is an additive
functor to `ModuleCat`.
-/

public section

open Bundle CategoryTheory Topology

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]
  (A : FiniteRankAtlas 𝕜 X)
  {Y : Type*} [TopologicalSpace Y] {b : Y → X}

/-- Sums of continuous maps lying over the same base map are continuous, even when
the rank of the target bundle is unbounded. -/
theorem continuous_add {s t : ∀ y, A.Fiber (b y)}
    (hs : Continuous (fun y => (⟨b y, s y⟩ : TotalSpace Unit A.Fiber)))
    (ht : Continuous (fun y => (⟨b y, t y⟩ : TotalSpace Unit A.Fiber))) :
    Continuous (fun y => (⟨b y, s y + t y⟩ : TotalSpace Unit A.Fiber)) := by
  have hb : Continuous b := A.continuous_proj.comp hs
  rw [A.continuous_mk_iff_rankStrata hb] at hs ht ⊢
  intro n
  exact (hs n).add_totalSpace 𝕜 (ht n)

/-- Continuous scalar multiples of maps into a variable-rank total space are continuous. -/
theorem continuous_smul {s : ∀ y, A.Fiber (b y)} {c : Y → 𝕜}
    (hc : Continuous c)
    (hs : Continuous (fun y => (⟨b y, s y⟩ : TotalSpace Unit A.Fiber))) :
    Continuous (fun y => (⟨b y, c y • s y⟩ : TotalSpace Unit A.Fiber)) := by
  have hb : Continuous b := A.continuous_proj.comp hs
  rw [A.continuous_mk_iff_rankStrata hb] at hs ⊢
  intro n
  exact (hc.comp continuous_subtype_val).smul_totalSpace (hs n)

variable {A} {D : FiniteRankAtlas 𝕜 X}

namespace Hom

instance : Zero (A ⟶ D) where
  zero := ⟨fun _ => 0, D.continuous_zeroSection.comp A.continuous_proj⟩

instance : Add (A ⟶ D) where
  add f g := ⟨fun x => f.fiberMap x + g.fiberMap x,
    D.continuous_add f.continuous_totalSpaceMap g.continuous_totalSpaceMap⟩

instance : Neg (A ⟶ D) where
  neg f := ⟨fun x => -f.fiberMap x, by
    simpa only [neg_one_smul, LinearMap.neg_apply] using
      D.continuous_smul (continuous_const (y := (-1 : 𝕜)))
        f.continuous_totalSpaceMap⟩

instance : Sub (A ⟶ D) where
  sub f g := f + -g

instance : SMul ℕ (A ⟶ D) where
  smul n f := ⟨fun x => n • f.fiberMap x, by
    simpa only [Nat.cast_smul_eq_nsmul, LinearMap.smul_apply] using
      D.continuous_smul (continuous_const (y := (n : 𝕜)))
        f.continuous_totalSpaceMap⟩

instance : SMul ℤ (A ⟶ D) where
  smul n f := ⟨fun x => n • f.fiberMap x, by
    simpa only [Int.cast_smul_eq_zsmul, LinearMap.smul_apply] using
      D.continuous_smul (continuous_const (y := (n : 𝕜)))
        f.continuous_totalSpaceMap⟩

/-- Bundle morphisms form an abelian group under fibrewise operations. -/
instance : AddCommGroup (A ⟶ D) :=
  Function.Injective.addCommGroup (fun f => f.fiberMap) (fun _ _ h => Hom.ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => by
      funext x; exact (sub_eq_add_neg _ _).symm)
    (fun _ _ => rfl) (fun _ _ => rfl)

end Hom

/-- The category of variable-rank bundle atlases is preadditive: composition is
bilinear on the abelian groups of continuous fibrewise-linear maps. -/
instance : Preadditive (FiniteRankAtlas 𝕜 X) where
  add_comp _ _ _ f g h := hom_ext fun x => LinearMap.ext fun _ =>
    (h.fiberMap x).map_add _ _
  comp_add _ _ _ f g h := hom_ext fun x => LinearMap.ext fun _ => rfl

@[simp] theorem fiberMap_zero (x : X) :
    (0 : A ⟶ D).fiberMap x = 0 := (rfl)

@[simp] theorem fiberMap_add (f g : A ⟶ D) (x : X) :
    (f + g).fiberMap x = f.fiberMap x + g.fiberMap x := (rfl)

@[simp] theorem fiberMap_neg (f : A ⟶ D) (x : X) :
    (-f).fiberMap x = -f.fiberMap x := (rfl)

@[simp] theorem fiberMap_sub (f g : A ⟶ D) (x : X) :
    (f - g).fiberMap x = f.fiberMap x - g.fiberMap x := by
  simp only [sub_eq_add_neg, fiberMap_add, fiberMap_neg]

@[simp] theorem fiberMap_nsmul (n : ℕ) (f : A ⟶ D) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := (rfl)

@[simp] theorem fiberMap_zsmul (n : ℤ) (f : A ⟶ D) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := (rfl)

/-- Evaluation on a fibre preserves the addition of bundle morphisms. -/
instance (x : X) : (fiberFunctor (𝕜 := 𝕜) x).Additive where
  map_add := by intros; rfl

end TauCeti.FiniteRankAtlas
