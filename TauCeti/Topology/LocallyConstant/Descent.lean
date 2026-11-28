/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Descent of locally constant functions from open-fiber covers

Let `f : ∀ i : ι, Y i → X` be a family of maps whose images cover a topological space `X`, and let
`g : ∀ i : ι, Y i → Z` be functions whose fibers over every value `c : Z` are simultaneously the
preimages of a single open subset `W c ⊆ X`. Then the `g i` descend to a single locally constant
function `φ : LocallyConstant X Z` with `φ (f i y) = g i y` for all `i` and `y`. No topology on
the domains `Y i` is required.

## Main results

* `LocallyConstant.exists_comp_eq_of_isOpen_fiber`: descent of a family of functions along a
  jointly surjective family of maps when each value-fiber is pulled back from a common open set.
* `LocallyConstant.exists_comp_eq_of_isOpen_fiber_pair`: two-map specialization.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Cohomology/ProperBaseChange/SubringSplitting.lean` (`exists_locallyConstant_of_fibers`).
-/

@[expose] public section

namespace LocallyConstant

/-- Let a family of maps `f : ∀ i, Y i → X` cover a topological space `X`, and let
`g : ∀ i, Y i → Z` be functions such that for each `c : Z`, the fibers `g i ⁻¹' {c}` are the
preimages under `f i` of a single open set `W ⊆ X`. Then there is a locally constant function
`φ : LocallyConstant X Z` satisfying `φ (f i y) = g i y` for all `i` and `y`. -/
theorem exists_comp_eq_of_isOpen_fiber {X Z ι : Type*} {Y : ι → Type*} [TopologicalSpace X]
    {f : ∀ i, Y i → X} (h_cover : ∀ x : X, ∃ i, x ∈ Set.range (f i))
    (g : ∀ i, Y i → Z)
    (h_fiber : ∀ c : Z, ∃ W : Set X, IsOpen W ∧ ∀ i, g i ⁻¹' {c} = f i ⁻¹' W) :
    ∃ φ : LocallyConstant X Z, ∀ i y, φ (f i y) = g i y := by
  choose W hW_open hW_eq using h_fiber
  have h_val (x : X) : ∃ c : Z, ∀ k : Z, c = k ↔ x ∈ W k := by
    obtain ⟨i, y, rfl⟩ := h_cover x
    exact ⟨g i y, fun k ↦ Set.ext_iff.mp (hW_eq k i) y⟩
  choose φ hφ using h_val
  have h_pre (c : Z) : φ ⁻¹' {c} = W c := Set.ext fun x ↦ hφ x c
  have h_lc : IsLocallyConstant φ :=
    IsLocallyConstant.iff_isOpen_fiber.mpr fun c ↦ by simpa only [h_pre] using hW_open c
  exact ⟨⟨φ, h_lc⟩, fun i y ↦ (hφ (f i y) (g i y)).mpr ((hW_eq (g i y) i).subset rfl)⟩

/-- Two-map specialization of `LocallyConstant.exists_comp_eq_of_isOpen_fiber`: if the images of
`f₁ : X₁ → X` and `f₂ : X₂ → X` cover `X` and the fibers of `g₁ : X₁ → Z` and `g₂ : X₂ → Z` over
each `c : Z` are the preimages of a single open subset of `X`, then `g₁` and `g₂` descend to a
locally constant function on `X`. -/
theorem exists_comp_eq_of_isOpen_fiber_pair {X Z : Type*} {X₁ : Type u₁} {X₂ : Type u₂}
    [TopologicalSpace X] {f₁ : X₁ → X} {f₂ : X₂ → X}
    (h_cover : ∀ x : X, x ∈ Set.range f₁ ∨ x ∈ Set.range f₂)
    (g₁ : X₁ → Z) (g₂ : X₂ → Z)
    (h_fiber : ∀ c : Z, ∃ W : Set X, IsOpen W ∧ g₁ ⁻¹' {c} = f₁ ⁻¹' W ∧ g₂ ⁻¹' {c} = f₂ ⁻¹' W) :
    ∃ φ : LocallyConstant X Z, (∀ y, φ (f₁ y) = g₁ y) ∧ ∀ y, φ (f₂ y) = g₂ y := by
  let Y : Bool → Type (max u₁ u₂) := Bool.rec (ULift.{u₁} X₂) (ULift.{u₂} X₁)
  let f : ∀ b, Y b → X := Bool.rec (fun y ↦ f₂ y.down) (fun y ↦ f₁ y.down)
  let g : ∀ b, Y b → Z := Bool.rec (fun y ↦ g₂ y.down) (fun y ↦ g₁ y.down)
  have hcov : ∀ x : X, ∃ b, x ∈ Set.range (f b) := fun x ↦
    (h_cover x).elim
      (fun ⟨y, hy⟩ ↦ ⟨true, ⟨y⟩, hy⟩)
      (fun ⟨y, hy⟩ ↦ ⟨false, ⟨y⟩, hy⟩)
  have hfib : ∀ c : Z, ∃ W : Set X, IsOpen W ∧ ∀ b, g b ⁻¹' {c} = f b ⁻¹' W := fun c ↦ by
    obtain ⟨W, hW, h₁, h₂⟩ := h_fiber c
    refine ⟨W, hW, Bool.rec ?_ ?_⟩
    · ext ⟨y⟩; exact Set.ext_iff.mp h₂ y
    · ext ⟨y⟩; exact Set.ext_iff.mp h₁ y
  obtain ⟨φ, hφ⟩ := exists_comp_eq_of_isOpen_fiber hcov g hfib
  exact ⟨φ, fun y ↦ hφ true ⟨y⟩, fun y ↦ hφ false ⟨y⟩⟩

end LocallyConstant
