/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Category

/-!
# Preadditive structure on variable-rank bundle atlases

`TauCeti.FiniteRankAtlas 𝕜 X` inherits its pointwise morphism arithmetic and `Preadditive` structure
from `TauCeti.VariableRankBundle.preadditive` in `TauCeti.Topology.VectorBundle.FiniteRank.Glued`.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

/-- Composition of bundle-atlas morphisms is bilinear on the pointwise abelian hom groups. -/
instance : Preadditive (FiniteRankAtlas 𝕜 X) := VariableRankBundle.preadditive

section Continuity

variable {A : FiniteRankAtlas 𝕜 X} {Y : Type*} [TopologicalSpace Y] {b : Y → X}

/-- Sums of continuous maps lying over the same base map are continuous, even when
the rank of the target bundle is unbounded. -/
theorem continuous_add {s t : ∀ y, A.Fiber (b y)}
    (hs : Continuous (fun y => (⟨b y, s y⟩ : Bundle.TotalSpace Unit A.Fiber)))
    (ht : Continuous (fun y => (⟨b y, t y⟩ : Bundle.TotalSpace Unit A.Fiber))) :
    Continuous (fun y => (⟨b y, s y + t y⟩ : Bundle.TotalSpace Unit A.Fiber)) :=
  VariableRankBundle.continuous_add A hs ht

/-- Continuous scalar multiples of maps into a variable-rank total space are continuous. -/
theorem continuous_smul {s : ∀ y, A.Fiber (b y)} {c : Y → 𝕜}
    (hc : Continuous c)
    (hs : Continuous (fun y => (⟨b y, s y⟩ : Bundle.TotalSpace Unit A.Fiber))) :
    Continuous (fun y => (⟨b y, c y • s y⟩ : Bundle.TotalSpace Unit A.Fiber)) :=
  VariableRankBundle.continuous_smul A hc hs

end Continuity

variable {A D : FiniteRankAtlas 𝕜 X}

theorem fiberMap_zero (x : X) :
    (0 : A ⟶ D).fiberMap x = 0 := (rfl)

theorem fiberMap_add (f g : A ⟶ D) (x : X) :
    (f + g).fiberMap x = f.fiberMap x + g.fiberMap x := (rfl)

theorem fiberMap_neg (f : A ⟶ D) (x : X) :
    (-f).fiberMap x = -f.fiberMap x := (rfl)

theorem fiberMap_sub (f g : A ⟶ D) (x : X) :
    (f - g).fiberMap x = f.fiberMap x - g.fiberMap x :=
  VariableRankBundle.fiberMap_sub f g x

theorem fiberMap_nsmul (n : ℕ) (f : A ⟶ D) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := (rfl)

theorem fiberMap_zsmul (n : ℤ) (f : A ⟶ D) (x : X) :
    (n • f).fiberMap x = n • f.fiberMap x := (rfl)

end TauCeti.FiniteRankAtlas
