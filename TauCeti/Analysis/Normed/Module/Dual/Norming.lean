/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.Semicontinuity.Lindelof
import Mathlib.Analysis.Normed.Module.DoubleDual
import TauCeti.Analysis.Normed.Operator.Norming

/-!
# Norming subsets of the continuous dual

On a separable subset of a seminormed space, any prescribed family of continuous linear
functionals recovering the norm has a countable subfamily with the same property.
The family need not be norm separable, and the space need not be complete.

A finite-dimensional subspace of a real or complex normed space has a finite norming set of
functionals in the dual unit ball, with any prescribed loss `A > 1`
(`Submodule.exists_finset_strongDual_norming`). This is the dual form of the operator statement
`Submodule.exists_finset_norming`, applied in the bidual.

The extraction uses Mathlib's `exists_countable_lowerSemicontinuous_isLUB`.
This is useful for reducing scalar measurability tests to countably many functions.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*,
  Volume I, §1.1, especially Corollary 1.1.10.
-/

public section

open Set TopologicalSpace

section Extraction

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A family of dual tests recovering the norm on a separable set contains a countable
subfamily recovering the norm on that same set. In particular, a prescribed 1-norming
subset of the dual unit ball admits countable norming tests. -/
theorem TopologicalSpace.IsSeparable.exists_countable_dual_norming_subset
    {s : Set E} (hs : IsSeparable s) {D : Set (StrongDual 𝕜 E)}
    (hD : ∀ x ∈ s, IsLUB ((fun φ : StrongDual 𝕜 E ↦ ‖φ x‖) '' D) ‖x‖) :
    ∃ D' ⊆ D, D'.Countable ∧
      ∀ x ∈ s, IsLUB ((fun φ : StrongDual 𝕜 E ↦ ‖φ x‖) '' D') ‖x‖ := by
  classical
  have := hs.secondCountableTopology
  let F : StrongDual 𝕜 E → s → ℝ := fun φ x ↦ ‖φ x‖
  have hF : IsLUB (F '' D) (fun x : s ↦ ‖(x : E)‖) := by
    rw [isLUB_pi]
    intro x
    simpa only [← image_comp, Function.comp_def, F] using hD x x.property
  obtain ⟨G, hGD, hGc, hG⟩ := exists_countable_lowerSemicontinuous_isLUB
    (𝓕 := F '' D) (by
      rintro _ ⟨φ, -, rfl⟩
      exact (φ.continuous.comp continuous_subtypeVal).norm.lowerSemicontinuous) hF
  choose φ hφD hφ using fun g : G ↦ hGD g.property
  have : Countable G := hGc.to_subtype
  have himage : F '' range φ = G := by
    ext g
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact hφ u ▸ u.property
    · intro hg
      exact ⟨φ ⟨g, hg⟩, mem_range_self _, hφ ⟨g, hg⟩⟩
  refine ⟨range φ, range_subset_iff.mpr hφD, countable_range _, ?_⟩
  intro x hx
  have := (isLUB_pi.mp hG) (⟨x, hx⟩ : s)
  rw [← himage] at this
  simpa only [← image_comp, Function.comp_def, F] using this

end Extraction

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The dual unit ball contains countably many tests recovering the norm on any separable
set in a real or complex seminormed space. No completeness assumption is needed. -/
theorem TopologicalSpace.IsSeparable.exists_countable_dual_norming
    {s : Set E} (hs : IsSeparable s) :
    ∃ D : Set (StrongDual 𝕜 E), D.Countable ∧ (∀ φ ∈ D, ‖φ‖ ≤ 1) ∧
      ∀ x ∈ s, IsLUB ((fun φ : StrongDual 𝕜 E ↦ ‖φ x‖) '' D) ‖x‖ := by
  have hnorm (x : E) :
      IsLUB ((fun φ : StrongDual 𝕜 E ↦ ‖φ x‖) '' {φ | ‖φ‖ ≤ 1}) ‖x‖ := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨φ, hφ, rfl⟩
      simpa using φ.le_of_opNorm_le hφ x
    · intro r hr
      obtain ⟨φ, hφ, hx⟩ := exists_dual_vector'' 𝕜 x
      have := hr (mem_image_of_mem (fun φ : StrongDual 𝕜 E ↦ ‖φ x‖) hφ)
      simpa [hx] using this
  obtain ⟨D, hD, hDc, hDn⟩ := hs.exists_countable_dual_norming_subset (fun x _ ↦ hnorm x)
  exact ⟨D, hDc, hD, hDn⟩

end RCLike

section Finite

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A finite-dimensional subspace of a normed space has a finite norming set of functionals in
the dual unit ball, with any loss `A > 1`. This also covers the zero subspace. -/
theorem Submodule.exists_finset_strongDual_norming (F : Submodule 𝕜 E) [FiniteDimensional 𝕜 F]
    {A : ℝ} (hA : 1 < A) :
    ∃ t : Finset (StrongDual 𝕜 E), (∀ g ∈ t, ‖g‖ ≤ 1) ∧ ∀ x ∈ F, ∃ g ∈ t, ‖x‖ ≤ A * ‖g x‖ := by
  -- Apply the operator statement to the image of `F` under the isometric bidual inclusion.
  let J := NormedSpace.inclusionInDoubleDualLi (E := E) 𝕜
  -- `J x` evaluates functionals at `x`; this holds by definition of the bidual inclusion.
  have hJ (x : E) (g : StrongDual 𝕜 E) : J x g = g x := rfl
  obtain ⟨t, ht, hnorm⟩ := (F.map J.toLinearMap).exists_finset_norming hA
  refine ⟨t, ht, fun x hx ↦ ?_⟩
  obtain ⟨g, hg, hxg⟩ := hnorm (J x) (Submodule.mem_map_of_mem hx)
  exact ⟨g, hg, by rwa [J.norm_map, hJ] at hxg⟩

end Finite
