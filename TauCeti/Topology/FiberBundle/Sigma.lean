/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Fibre inclusions into disjoint unions of fibre bundles

In a disjoint union `Σ i, TotalSpace (F i) (E i)` of fibre bundles, including a single fibre
`E i b` into the `i`th summand is a topological inducing map
(`FiberBundle.isInducing_sigmaMk_totalSpaceMk`), and pulling back along any inducing map into
that disjoint union preserves inducingness of fibre inclusions
(`FiberBundle.isInducing_of_comp_eq_sigmaMk_totalSpaceMk`).

This is used to prove that single-fibre inclusions into glued variable-rank total spaces are
inducing.
-/

public section

open Bundle Topology

namespace FiberBundle

variable {ι : Type*} {B : ι → Type*} [∀ i, TopologicalSpace (B i)]

/-- Including a single fibre `E i b` into the disjoint union `Σ j, TotalSpace (F j) (E j)` of
fibre bundles is inducing. -/
theorem isInducing_sigmaMk_totalSpaceMk (F : ι → Type*) [∀ i, TopologicalSpace (F i)]
    (E : ∀ i, B i → Type*) [∀ i b, TopologicalSpace (E i b)]
    [∀ i, TopologicalSpace (TotalSpace (F i) (E i))] [∀ i, FiberBundle (F i) (E i)]
    (i : ι) (b : B i) :
    IsInducing (fun v : E i b ↦ (⟨i, ⟨b, v⟩⟩ : Σ j, TotalSpace (F j) (E j))) :=
  IsEmbedding.sigmaMk.isInducing.comp (FiberBundle.totalSpaceMk_isInducing (F i) (E i) b)

/-- If an inducing map `φ : Z → Σ j, TotalSpace (F j) (E j)` sends `g v` to `⟨i, ⟨b, v⟩⟩` for
all `v : E i b`, then `g : E i b → Z` is inducing. -/
theorem isInducing_of_comp_eq_sigmaMk_totalSpaceMk {F : ι → Type*} [∀ i, TopologicalSpace (F i)]
    {E : ∀ i, B i → Type*} [∀ i b, TopologicalSpace (E i b)]
    [∀ i, TopologicalSpace (TotalSpace (F i) (E i))] [∀ i, FiberBundle (F i) (E i)]
    {Z : Type*} [TopologicalSpace Z] (i : ι) (b : B i)
    {φ : Z → Σ j, TotalSpace (F j) (E j)} {g : E i b → Z}
    (hφ : IsInducing φ) (hcomp : ∀ v, φ (g v) = ⟨i, ⟨b, v⟩⟩) :
    IsInducing g := by
  have hfg : φ ∘ g = fun v : E i b ↦ (⟨i, ⟨b, v⟩⟩ : Σ j, TotalSpace (F j) (E j)) := funext hcomp
  rw [← hφ.of_comp_iff, hfg]
  exact isInducing_sigmaMk_totalSpaceMk F E i b

end FiberBundle
