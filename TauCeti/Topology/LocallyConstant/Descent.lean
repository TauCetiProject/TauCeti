/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Descent of locally constant functions from open common-preimage covers

Let `f : ∀ i : ι, Y i → X` be a family of maps whose images cover a topological space `X`, and let
`g : ∀ i : ι, Y i → Z` be functions whose fibers over every value `c : Z` are simultaneously the
preimages of a single open subset `W c ⊆ X`. Then the `g i` descend to a unique locally constant
function `φ : LocallyConstant X Z` with `φ (f i y) = g i y` for all `i` and `y`. No topology on
the domains `Y i` is required.

## Main results

* `TauCeti.exists_locallyConstant_comp_eq_of_fiber_eq_preimage`: unique descent of a family of
  functions along a jointly surjective family of maps when each value-fiber is pulled back from a
  common open set.
* `TauCeti.exists_locallyConstant_comp_eq_of_fiber_eq_preimage_pair`: two-map specialization.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Cohomology/ProperBaseChange/SubringSplitting.lean` (`exists_locallyConstant_of_fibers`).
-/

@[expose] public section

namespace TauCeti

/-- Let a family of maps `f : ∀ i, Y i → X` cover a topological space `X`, and let
`g : ∀ i, Y i → Z` be functions such that for each `c : Z`, the fibers `g i ⁻¹' {c}` are the
preimages under `f i` of a single open set `W ⊆ X`. Then there is a unique locally constant
function `φ : LocallyConstant X Z` satisfying `φ (f i y) = g i y` for all `i` and `y`. -/
theorem exists_locallyConstant_comp_eq_of_fiber_eq_preimage {X Z ι : Type*} {Y : ι → Type*}
    [TopologicalSpace X] {f : ∀ i, Y i → X} (h_cover : ∀ x : X, ∃ i, x ∈ Set.range (f i))
    (g : ∀ i, Y i → Z)
    (h_fiber : ∀ c : Z, ∃ W : Set X, IsOpen W ∧ ∀ i, g i ⁻¹' {c} = f i ⁻¹' W) :
    ∃! φ : LocallyConstant X Z, ∀ i y, φ (f i y) = g i y := by
  choose W hW_open hW_eq using h_fiber
  have h_val (x : X) : ∃ c : Z, ∀ k : Z, c = k ↔ x ∈ W k := by
    obtain ⟨i, hx⟩ := h_cover x
    obtain ⟨y, rfl⟩ := Set.mem_range.mp hx
    refine ⟨g i y, fun k ↦ ?_⟩
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using Set.ext_iff.mp (hW_eq k i) y
  choose φ hφ using h_val
  have h_pre (c : Z) : φ ⁻¹' {c} = W c := Set.ext fun x ↦ by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hφ x c
  have h_lc : IsLocallyConstant φ :=
    IsLocallyConstant.iff_isOpen_fiber.mpr fun c ↦ by simpa only [h_pre] using hW_open c
  refine ⟨⟨φ, h_lc⟩, fun i y ↦ ?_, fun ψ hψ ↦ ?_⟩
  · rw [LocallyConstant.coe_mk]
    have hy : f i y ∈ W (g i y) :=
      (Set.mem_preimage.mp <| (hW_eq (g i y) i).subset (Set.mem_singleton (g i y)))
    exact (hφ (f i y) (g i y)).mpr hy
  · ext x
    obtain ⟨i, hx⟩ := h_cover x
    obtain ⟨y, rfl⟩ := Set.mem_range.mp hx
    rw [hψ i y, LocallyConstant.coe_mk]
    have hy : f i y ∈ W (g i y) :=
      (Set.mem_preimage.mp <| (hW_eq (g i y) i).subset (Set.mem_singleton (g i y)))
    exact ((hφ (f i y) (g i y)).mpr hy).symm

/-- Two-map specialization of `TauCeti.exists_locallyConstant_comp_eq_of_fiber_eq_preimage`: if the
images of `f₁ : X₁ → X` and `f₂ : X₂ → X` cover `X` and the fibers of `g₁ : X₁ → Z` and
`g₂ : X₂ → Z` over each `c : Z` are the preimages of a single open subset of `X`, then `g₁` and
`g₂` descend to a unique locally constant function on `X`. -/
theorem exists_locallyConstant_comp_eq_of_fiber_eq_preimage_pair {X Z X₁ X₂ : Type*}
    [TopologicalSpace X] {f₁ : X₁ → X} {f₂ : X₂ → X}
    (h_cover : ∀ x : X, x ∈ Set.range f₁ ∨ x ∈ Set.range f₂)
    (g₁ : X₁ → Z) (g₂ : X₂ → Z)
    (h_fiber : ∀ c : Z, ∃ W : Set X, IsOpen W ∧ g₁ ⁻¹' {c} = f₁ ⁻¹' W ∧ g₂ ⁻¹' {c} = f₂ ⁻¹' W) :
    ∃! φ : LocallyConstant X Z, (∀ y, φ (f₁ y) = g₁ y) ∧ ∀ y, φ (f₂ y) = g₂ y := by
  have hcov : ∀ x : X, ∃ _ : Unit, x ∈ Set.range (Sum.elim f₁ f₂) := fun x ↦
    ⟨(), by simpa only [Set.Sum.elim_range, Set.mem_union] using h_cover x⟩
  have hfib : ∀ c : Z, ∃ W : Set X, IsOpen W ∧
      ∀ _ : Unit, Sum.elim g₁ g₂ ⁻¹' {c} = Sum.elim f₁ f₂ ⁻¹' W := fun c ↦ by
    obtain ⟨W, hW, h₁, h₂⟩ := h_fiber c
    exact ⟨W, hW, fun _ ↦ by simp only [Set.preimage_sumElim, h₁, h₂]⟩
  obtain ⟨φ, hφ, huniq⟩ := exists_locallyConstant_comp_eq_of_fiber_eq_preimage (ι := Unit)
    (Y := fun _ ↦ X₁ ⊕ X₂) hcov (fun _ ↦ Sum.elim g₁ g₂) hfib
  refine ⟨φ, ⟨fun y ↦ by simpa only [Sum.elim_inl] using hφ () (.inl y),
    fun y ↦ by simpa only [Sum.elim_inr] using hφ () (.inr y)⟩, fun ψ ⟨h₁, h₂⟩ ↦ huniq ψ ?_⟩
  rintro ⟨⟩ (y | y)
  · simpa only [Sum.elim_inl] using h₁ y
  · simpa only [Sum.elim_inr] using h₂ y

end TauCeti
