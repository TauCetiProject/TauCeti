/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Smooth nowhere-zero sections from continuous ones

Let `s` be a section of a smooth vector bundle with a continuous fibrewise inner product, which
is continuous and nowhere zero on a closed set `D`. Then some smooth global section is nowhere
zero on `D`. In each fibre over `D` the condition `0 < ⟪s x, v⟫` is convex in `v`, and near each
point of `D` it is satisfied by a smooth section through the value of `s` there; off `D` there
is no condition. Mathlib's gluing of local sections by a smooth partition of unity,
`exists_contMDiffSection_forall_mem_convex_of_local`, then gives a global smooth section
satisfying it on `D`. No manifold structure on `D` is needed.

## Main results

* `TauCeti.exists_contMDiffSection_inner_pos_on_of_continuousOn`: if `s` is continuous and
  nowhere zero on a closed set `D`, some smooth section `t` has `0 < ⟪s x, t x⟫` on `D`.
* `TauCeti.exists_contMDiffSection_ne_zero_on_of_continuousOn`: the same `t` is nowhere zero
  on `D`.
* `TauCeti.exists_contMDiffSection_inner_pos`,
  `TauCeti.exists_contMDiffSection_forall_ne_zero_of_continuous`: the case `D = univ`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 10.
-/

public section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContinuousRiemannianBundle F V]

/-- A section `s` which is continuous and nowhere zero on a closed set `D` has a smooth global
section `t` with `0 < ⟪s x, t x⟫` at every point of `D`. Nothing is required off `D`. -/
theorem exists_contMDiffSection_inner_pos_on_of_continuousOn {D : Set M} (hD : IsClosed D)
    {s : Π x, V x} (hs : ContinuousOn (fun x ↦ TotalSpace.mk' F x (s x)) D)
    (hne : ∀ x ∈ D, s x ≠ 0) :
    ∃ t : Cₛ^∞⟮I; F, V⟯, ∀ x ∈ D, 0 < inner ℝ (s x) (t x) := by
  refine exists_contMDiffSection_forall_mem_convex_of_local I V
    (fun x ↦ {v | x ∈ D → 0 < inner ℝ (s x) v}) (fun x ↦ ?_) fun x₀ ↦ ?_
  · by_cases hx : x ∈ D
    · simp only [hx, forall_const]
      exact (convex_Ioi (0 : ℝ)).linear_preimage (innerSL ℝ (s x)).toLinearMap
    · simpa [hx] using convex_univ
  by_cases hx₀ : x₀ ∈ D
  · obtain ⟨t, ht, heq⟩ := FiberBundle.exists_contMDiff_section_eq I F ∞ (s x₀)
    have hp : 0 < inner ℝ (s x₀) (t x₀) := by rw [heq]; exact real_inner_self_pos.mpr (hne x₀ hx₀)
    have he : ∀ᶠ x in 𝓝[D] x₀, 0 < inner ℝ (s x) (t x) :=
      ((hs.inner_bundle ht.continuous.continuousOn) x₀ hx₀).eventually (isOpen_Ioi.mem_nhds hp)
    exact ⟨_, eventually_nhdsWithin_iff.mp he, t, ht.contMDiffOn, fun _ hy ↦ hy⟩
  · exact ⟨Dᶜ, hD.isOpen_compl.mem_nhds hx₀, fun _ ↦ 0,
      (contMDiff_zeroSection ℝ V).contMDiffOn, fun _ hy hyD ↦ (hy hyD).elim⟩

/-- A section which is continuous and nowhere zero on a closed set `D` gives a smooth global
section nowhere zero on `D`. -/
theorem exists_contMDiffSection_ne_zero_on_of_continuousOn {D : Set M} (hD : IsClosed D)
    {s : Π x, V x} (hs : ContinuousOn (fun x ↦ TotalSpace.mk' F x (s x)) D)
    (hne : ∀ x ∈ D, s x ≠ 0) :
    ∃ t : Cₛ^∞⟮I; F, V⟯, ∀ x ∈ D, t x ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_contMDiffSection_inner_pos_on_of_continuousOn (I := I) hD hs hne
  exact ⟨t, fun x hx h ↦ by simpa [h] using ht x hx⟩

/-- A continuous nowhere-zero section `s` has a smooth section `t` with `0 < ⟪s x, t x⟫` at
every point. -/
theorem exists_contMDiffSection_inner_pos {s : Π x, V x}
    (hs : Continuous (fun x ↦ TotalSpace.mk' F x (s x))) (hne : ∀ x, s x ≠ 0) :
    ∃ t : Cₛ^∞⟮I; F, V⟯, ∀ x, 0 < inner ℝ (s x) (t x) := by
  obtain ⟨t, ht⟩ := exists_contMDiffSection_inner_pos_on_of_continuousOn (I := I) isClosed_univ
    hs.continuousOn fun x _ ↦ hne x
  exact ⟨t, fun x ↦ ht x (mem_univ x)⟩

/-- A vector bundle with a continuous fibrewise inner product and a continuous nowhere-zero
section has a smooth nowhere-zero section. -/
theorem exists_contMDiffSection_forall_ne_zero_of_continuous {s : Π x, V x}
    (hs : Continuous (fun x ↦ TotalSpace.mk' F x (s x))) (hne : ∀ x, s x ≠ 0) :
    ∃ t : Cₛ^∞⟮I; F, V⟯, ∀ x, t x ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_contMDiffSection_inner_pos (I := I) hs hne
  exact ⟨t, fun x h ↦ by simpa [h] using ht x⟩

end TauCeti
