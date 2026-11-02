/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Continuous barycentric coordinates of an affinely independent family

An affinely independent finite family `p` of points of a real normed space has continuous
barycentric coordinates: continuous affine functions `f i` on the whole space which read off the
weight of `p i` in every affine combination of `p`
(`AffineIndependent.exists_continuousAffineMap_apply_affineCombination`).

Mathlib's `continuous_barycentric_coord` gives this when the ambient space is finite-dimensional,
via an affine basis of the whole space. Here the ambient space is arbitrary: the algebraic
coordinates of an affine basis extending `p` need not be continuous, but their linear parts are
continuous on the finite-dimensional span of `p`, so the Hahn–Banach theorem
(`exists_extension_norm_eq`) extends them to continuous functionals on the whole space.

## Main results

* `AffineIndependent.exists_continuousAffineMap_apply_affineCombination`: continuous affine
  functions reading off the weights of affine combinations of an affinely independent finite
  family in a real normed space.
-/

public section

open Set Finset

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ι → E}

/-- **Continuous barycentric coordinates.** An affinely independent finite family `p` in a real
normed space has continuous affine coordinate functions `f i` on the whole space: `f i` reads off
the weight of `p i` in every affine combination of `p`, and so takes the value `1` at `p i` and
`0` at the other points of the family. -/
theorem AffineIndependent.exists_continuousAffineMap_apply_affineCombination
    (hp : AffineIndependent ℝ p) :
    ∃ f : ι → E →ᴬ[ℝ] ℝ, (∀ w : ι → ℝ, ∑ j, w j = 1 → ∀ i,
      f i (Finset.univ.affineCombination ℝ p w) = w i) ∧ (∀ i, f i (p i) = 1) ∧
      ∀ i j, i ≠ j → f i (p j) = 0 := by
  classical
  -- Algebraic coordinates: extend `p` to an affine basis `b` of the whole space.
  obtain ⟨t, hst, hti, hts⟩ := exists_subset_affineIndependent_affineSpan_eq_top
    (hp.range (k := ℝ))
  let b : AffineBasis t ℝ E := ⟨fun q => q, hti, by simpa using hts⟩
  let c : ι → E →ᵃ[ℝ] ℝ := fun i => b.coord ⟨p i, hst (mem_range_self i)⟩
  have hcp : ∀ i j, c i (p j) = if i = j then 1 else 0 := fun i j => by
    -- `b` is the inclusion of `t`, so the basis point at `p j` is `p j` by definition.
    rw [show p j = b ⟨p j, hst (mem_range_self j)⟩ from rfl, b.coord_apply]
    simp [hp.injective.eq_iff]
  have hc : ∀ w : ι → ℝ, ∑ j, w j = 1 → ∀ i, c i (Finset.univ.affineCombination ℝ p w) = w i := by
    intro w hw i
    rw [Finset.map_affineCombination _ _ _ hw,
      Finset.affineCombination_eq_linear_combination _ _ _ hw]
    simp [hcp]
  -- The linear parts of the `c i` are continuous on the finite-dimensional span of `p`; extend
  -- them to continuous functionals on the whole space.
  choose g hg using fun i => exists_extension_norm_eq (vectorSpan ℝ (range p))
    (((c i).linear.domRestrict (vectorSpan ℝ (range p))).toContinuousLinearMap)
  let f : ι → E →ᴬ[ℝ] ℝ := fun i =>
    (g i).toContinuousAffineMap + ContinuousAffineMap.const ℝ E (1 - g i (p i))
  have hf_apply : ∀ i x, f i x = g i x + (1 - g i (p i)) := fun i x => by
    rw [ContinuousAffineMap.add_apply, ContinuousLinearMap.coe_toContinuousAffineMap,
      ContinuousAffineMap.coe_const, Function.const_apply]
  have hcpi : ∀ i, c i (p i) = 1 := fun i => by simp [hcp]
  -- On the affine span of `p`, which contains every affine combination, `f i` agrees with `c i`.
  have hfc : ∀ i, ∀ x ∈ affineSpan ℝ (range p), f i x = c i x := fun i x hx => by
    have hv : x -ᵥ p i ∈ vectorSpan ℝ (range p) := by
      rw [← direction_affineSpan]
      exact AffineSubspace.vsub_mem_direction hx (subset_affineSpan ℝ _ (mem_range_self i))
    have h : g i (x -ᵥ p i) = (c i).linear (x -ᵥ p i) := (hg i).1 ⟨x -ᵥ p i, hv⟩
    rw [AffineMap.linear_apply_vsub, vsub_eq_sub, vsub_eq_sub, map_sub] at h
    rw [hf_apply]
    linarith [hcpi i]
  have hf : ∀ w : ι → ℝ, ∑ j, w j = 1 → ∀ i, f i (Finset.univ.affineCombination ℝ p w) = w i :=
    fun w hw i => (hfc i _ (affineCombination_mem_affineSpan hw p)).trans (hc w hw i)
  have hfp : ∀ i j, f i (p j) = if i = j then 1 else 0 := fun i j =>
    (hfc i _ (subset_affineSpan ℝ _ (mem_range_self j))).trans (hcp i j)
  exact ⟨f, hf, fun i => by simp [hfp], fun i j hij => by simp [hfp, hij]⟩
