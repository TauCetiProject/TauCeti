/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Defs

/-!
# Cochains: extensionality and basic bounds

* `Cochain.ext_edges`: a cochain is determined by its values on edges;
* nonnegativity of the defect, the costs, the gauge distance and `h1`;
* `Cochain.gaugeDist_le_cost`, `h1_le`, `le_h1`: the infima defining `gaugeDist` and `h1`.
-/

public section

open Finset

namespace TauCeti.CoboundaryExpansion

variable {V : Type*} [LinearOrder V] {G : Type*} [Group G] {X : TwoComplex V}

namespace Cochain

/-- Two cochains that agree on the edges are equal. -/
theorem ext_edges {α β : Cochain X G}
    (h : ∀ u v, ({u, v} : Finset V) ∈ X.edges → α.toFun u v = β.toFun u v) : α = β := by
  obtain ⟨f, hf, hf1⟩ := α
  obtain ⟨g, hg, hg1⟩ := β
  congr
  funext u v
  by_cases he : ({u, v} : Finset V) ∈ X.edges
  · exact h u v he
  · exact (hf1 u v he).trans (hg1 u v he).symm

/-- The defect is nonnegative. -/
theorem defect_nonneg [Fintype V] (ℓ : GroupNorm G) (α : Cochain X G) : 0 ≤ α.defect ℓ :=
  sum_nonneg fun _ _ => apply_nonneg _ _

/-- The cost of a gauge is nonnegative. -/
theorem cost_nonneg [Fintype V] (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) :
    0 ≤ α.cost ℓ β :=
  sum_nonneg fun _ _ => apply_nonneg _ _

/-- The gauge distance is nonnegative. -/
theorem gaugeDist_nonneg [Fintype V] (ℓ : GroupNorm G) (α : Cochain X G) : 0 ≤ α.gaugeDist ℓ :=
  le_ciInf (cost_nonneg ℓ α)

/-- The gauge distance is at most the cost of any gauge. -/
theorem gaugeDist_le_cost [Fintype V] (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) :
    α.gaugeDist ℓ ≤ α.cost ℓ β :=
  ciInf_le ⟨0, by rintro _ ⟨β, rfl⟩; exact cost_nonneg ℓ α β⟩ β

end Cochain

/-- The Cheeger constant is nonnegative. -/
theorem h1_nonneg [Fintype V] (X : TwoComplex V) (ℓ : GroupNorm G) : 0 ≤ h1 X ℓ :=
  Real.sInf_nonneg <| by
    rintro _ ⟨α, -, rfl⟩
    exact div_nonneg (α.defect_nonneg ℓ) (α.gaugeDist_nonneg ℓ)

/-- Any cochain at positive gauge distance bounds the Cheeger constant from above. -/
theorem h1_le [Fintype V] (ℓ : GroupNorm G) (α : Cochain X G) (h : 0 < α.gaugeDist ℓ) :
    h1 X ℓ ≤ α.defect ℓ / α.gaugeDist ℓ :=
  csInf_le ⟨0, by rintro _ ⟨β, -, rfl⟩; exact div_nonneg (β.defect_nonneg ℓ) (β.gaugeDist_nonneg ℓ)⟩
    ⟨α, h, rfl⟩

/-- A uniform lower bound on `N / D` is a lower bound on the Cheeger constant. -/
theorem le_h1 [Fintype V] (ℓ : GroupNorm G) {c : ℝ} (hne : ∃ α : Cochain X G, 0 < α.gaugeDist ℓ)
    (h : ∀ α : Cochain X G, 0 < α.gaugeDist ℓ → c ≤ α.defect ℓ / α.gaugeDist ℓ) : c ≤ h1 X ℓ :=
  le_csInf (let ⟨α, hα⟩ := hne; ⟨_, α, hα, rfl⟩) fun _ ⟨α, hα, e⟩ => e ▸ h α hα

end TauCeti.CoboundaryExpansion
