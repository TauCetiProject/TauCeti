/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Smul
public import Mathlib.Analysis.Convex.Star
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Star-convex shrinking in a vector bundle

The radial core of a subset of a real vector bundle consists of those vectors whose whole
segment from zero lies in the subset. It is the largest fibrewise star-convex subset, and
it is open when the original subset is open. Thus every open neighbourhood of the zero
section contains an open fibrewise star-convex neighbourhood of that section, without any
metric, finite-dimensionality, or compactness assumption on the base or fibres.

This shrinking turns an arbitrary domain of injective tubular coordinates into a domain
preserved by radial contraction. Openness uses the closed projection from a product with
the compact interval, and joint continuity of fibrewise scalar multiplication.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24,
  for star-convex domains in tubular neighbourhoods.
-/

public section

open Bundle Set Topology

namespace TauCeti.VectorBundle

variable {B F : Type*} {E : B → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]

/-- The vectors whose radial segment from the zero vector stays in `U`. -/
def radialCore (U : Set (TotalSpace F E)) : Set (TotalSpace F E) :=
  {p | ∀ t ∈ Icc (0 : ℝ) 1, (⟨p.proj, t • p.2⟩ : TotalSpace F E) ∈ U}

/-- Membership in the radial core is tested along the whole closed radial segment. -/
theorem mem_radialCore {U : Set (TotalSpace F E)} {p : TotalSpace F E} :
    p ∈ radialCore U ↔
      ∀ t ∈ Icc (0 : ℝ) 1, (⟨p.proj, t • p.2⟩ : TotalSpace F E) ∈ U := Iff.rfl

/-- The radial core is contained in the original set. -/
theorem radialCore_subset (U : Set (TotalSpace F E)) : radialCore U ⊆ U := by
  intro p hp
  simpa using hp 1 ⟨zero_le_one, le_rfl⟩

/-- Enlarging a set enlarges its radial core. -/
theorem radialCore_mono {U W : Set (TotalSpace F E)} (h : U ⊆ W) :
    radialCore U ⊆ radialCore W := fun _ hp t ht => h (hp t ht)

/-- Taking the radial core preserves exactly the zero vectors in the original set. -/
@[simp] theorem zeroSection_mem_radialCore {U : Set (TotalSpace F E)} (x : B) :
    zeroSection F E x ∈ radialCore U ↔ zeroSection F E x ∈ U := by
  constructor
  · intro hx
    exact radialCore_subset U hx
  · intro hx t ht
    have ht0 : t • (0 : E x) = 0 := smul_zero t
    exact (congrArg (fun v : E x => (⟨x, v⟩ : TotalSpace F E) ∈ U) ht0).mpr hx

/-- Every fibre slice of the radial core is star-convex at zero. -/
theorem starConvex_radialCore (U : Set (TotalSpace F E)) (x : B) :
    StarConvex ℝ 0 {v : E x | (⟨x, v⟩ : TotalSpace F E) ∈ radialCore U} := by
  intro v hv a b ha hb hab
  simp only [smul_zero, zero_add, mem_ofPred_eq, mem_radialCore]
  intro t ht
  simpa only [smul_smul] using hv (t * b) ⟨mul_nonneg ht.1 hb, by nlinarith [ht.2]⟩

/-- A fibrewise star-convex subset of `U` lies in its radial core. This characterizes the
radial core as the largest such subset. -/
theorem subset_radialCore {U W : Set (TotalSpace F E)} (hWU : W ⊆ U)
    (hW : ∀ x, StarConvex ℝ 0 {v : E x | (⟨x, v⟩ : TotalSpace F E) ∈ W}) :
    W ⊆ radialCore U := by
  intro p hp t ht
  exact hWU ((hW p.proj).smul_mem hp ht.1 ht.2)

/-- Taking the radial core leaves a fibrewise star-convex set unchanged. -/
theorem radialCore_eq_self {U : Set (TotalSpace F E)}
    (hU : ∀ x, StarConvex ℝ 0 {v : E x | (⟨x, v⟩ : TotalSpace F E) ∈ U}) :
    radialCore U = U :=
  subset_antisymm (radialCore_subset U) (subset_radialCore Subset.rfl hU)

section Topology

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- The radial core of an open set is open. Compactness of the scalar interval gives one
neighbourhood on which all the radial segments remain in the original set. -/
theorem isOpen_radialCore {U : Set (TotalSpace F E)} (hU : IsOpen U) :
    IsOpen (radialCore U) := by
  let R : Icc (0 : ℝ) 1 × TotalSpace F E → TotalSpace F E :=
    fun p => ⟨p.2.proj, (p.1 : ℝ) • p.2.2⟩
  have hR : Continuous R :=
    (continuous_subtype_val.comp continuous_fst).smul_totalSpace continuous_snd
  have hclosed : IsClosed (Prod.snd '' (R ⁻¹' Uᶜ)) :=
    isClosedMap_snd_of_compactSpace _ (hU.isClosed_compl.preimage hR)
  convert hclosed.isOpen_compl using 1
  ext p
  simp only [mem_compl_iff, mem_image, mem_preimage, Prod.exists, R, mem_radialCore]
  simp

end Topology

end TauCeti.VectorBundle
