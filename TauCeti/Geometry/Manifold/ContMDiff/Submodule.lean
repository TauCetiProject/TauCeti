/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.Algebra.Module.Complement

/-!
# Smoothness of maps into a closed complemented subspace

A map from a manifold into a normed space whose values lie in a closed complemented subspace `p`
is `C^n` as a map into `p` as soon as it is `C^n` into the ambient space: composing with a
continuous linear projection onto `p` reads it as a map into `p`. Every finite-dimensional
subspace of a normed space over a complete field is closed complemented
(`Submodule.ClosedComplemented.of_finiteDimensional`).

## Main results

* `ContMDiff.codRestrict_submodule`: a `C^n` map with values in a closed complemented subspace is
  `C^n` into that subspace.
-/

public section

open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω}

/-- A `C^n` map into a normed space whose values lie in a closed complemented subspace `p` is
`C^n` as a map into `p`. -/
theorem ContMDiff.codRestrict_submodule {p : Submodule 𝕜 F} (hp : p.ClosedComplemented)
    {f : M → F} (hf : ContMDiff I 𝓘(𝕜, F) n f) (h : ∀ x, f x ∈ p) :
    ContMDiff I 𝓘(𝕜, p) n (fun x ↦ (⟨f x, h x⟩ : p)) := by
  obtain ⟨P, hP⟩ := hp
  exact (P.contDiff.contMDiff.comp hf).congr fun x ↦ (hP ⟨f x, h x⟩).symm
