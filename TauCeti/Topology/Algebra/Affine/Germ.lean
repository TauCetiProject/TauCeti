/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.AffineSpace.Generic
public import Mathlib.Topology.Separation.Basic

/-!
# Generic affine germs

A direction transverse to an affine subspace gives eventual avoidance on every
punctured scalar neighborhood, including at nonzero parameters and from exceptional
base points. Scalars form a division ring with a T1 topology; no order is required.
A preorder suffices for the right-neighborhood corollaries at zero. Neither affine
point torsor needs a topology, a norm, or a chosen origin.

For a finite family of affine maps `g` and directions `v`, each pair must make
`(x, t) ↦ t • v j +ᵥ g j x` surjective. One source arrangement `F` then makes all
these germs eventually generic simultaneously at every `F`-generic source point.
The affine maps `g j` themselves need not be surjective. A fixed direction transverse
to every nonempty exception also works from every base point.

Adapted from `Mei/Geometry/Affine/IncomingGerm.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
-/

public section

open Set Filter Topology

namespace AffineSubspace

variable {k V P : Type*} [DivisionRing k]
  [TopologicalSpace k] [T1Space k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- A transverse affine germ avoids an affine subspace on every punctured scalar
neighborhood, even from a base point in that subspace. No scalar order is required. -/
theorem eventually_smul_vadd_notMem_nhdsNE (S : AffineSubspace k P)
    {v : V} (hv : v ∉ S.direction) (x : P) (t₀ : k) :
    ∀ᶠ t : k in 𝓝[≠] t₀, t • v +ᵥ x ∉ S := by
  have h := S.subsingleton_preimage_lineMap (x := x) (y := v +ᵥ x)
    (by simpa using hv)
  simpa only [Set.mem_preimage, AffineMap.lineMap_vadd_apply, AffineSubspace.mem_coe] using
    h.finite.eventually_cofinite_notMem.filter_mono (nhdsNE_le_cofinite t₀)

/-- A transverse one-sided affine germ eventually avoids an affine subspace,
even when its base point lies in that subspace. -/
theorem eventually_smul_vadd_notMem [Preorder k] (S : AffineSubspace k P)
    {v : V} (hv : v ∉ S.direction) (x : P) :
    ∀ᶠ t : k in 𝓝[>] 0, t • v +ᵥ x ∉ S :=
  (S.eventually_smul_vadd_notMem_nhdsNE hv x 0).filter_mono
    (nhdsWithin_mono 0 fun _ ht => ne_of_gt ht)

end AffineSubspace

namespace TauCeti.ExceptionalArrangement

section FixedDirection

variable {k V P : Type*} [DivisionRing k] [TopologicalSpace k] [T1Space k]
  [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- A direction transverse to every nonempty exception gives a generic punctured
germ from every base point, including points in the exceptional arrangement. -/
theorem eventually_isGeneric_smul_vadd_nhdsNE (E : ExceptionalArrangement k P)
    {v : V} (hv : ∀ S ∈ E.exceptions, (S : Set P).Nonempty → v ∉ S.direction) (x : P) :
    ∀ᶠ t : k in 𝓝[≠] 0, E.IsGeneric (t • v +ᵥ x) := by
  simp_rw [isGeneric_iff]
  apply E.exceptions.eventually_all.mpr
  intro S hS
  by_cases hne : (S : Set P).Nonempty
  · exact S.eventually_smul_vadd_notMem_nhdsNE (hv S hS hne) x 0
  · exact Eventually.of_forall fun t ht => hne ⟨_, ht⟩

/-- A direction transverse to every nonempty exception gives a generic one-sided
germ from every base point. Only a scalar preorder is needed for the restriction. -/
theorem eventually_isGeneric_smul_vadd [Preorder k] (E : ExceptionalArrangement k P)
    {v : V} (hv : ∀ S ∈ E.exceptions, (S : Set P).Nonempty → v ∉ S.direction) (x : P) :
    ∀ᶠ t : k in 𝓝[>] 0, E.IsGeneric (t • v +ᵥ x) :=
  (E.eventually_isGeneric_smul_vadd_nhdsNE hv x).filter_mono
    (nhdsWithin_mono 0 fun _ ht => ne_of_gt ht)

end FixedDirection

section AffineFamilies

variable {k U V P Q ι : Type*} [DivisionRing k]
  [TopologicalSpace k] [T1Space k] [AddCommGroup U] [Module k U] [AddTorsor U P]
  [AddCommGroup V] [Module k V] [AddTorsor V Q] [Finite ι]

/-- For a finite family of affine maps and directions such that each map
`(x, t) ↦ t • v j +ᵥ g j x` is surjective, a source arrangement `F` makes the germs
eventually `E`-generic on the punctured neighborhood of zero simultaneously for all
`j` at every `F`-generic source point. The maps `g j` need not be surjective. -/
theorem exists_forall_eventually_isGeneric_smul_vadd_nhdsNE
    (E : ExceptionalArrangement k Q) (g : ι → P →ᵃ[k] Q) (v : ι → V)
    (hg : ∀ j, Function.Surjective (fun z : P × k => z.2 • v j +ᵥ g j z.1)) :
    ∃ F : ExceptionalArrangement k P, ∀ x, F.IsGeneric x →
      ∀ᶠ t : k in 𝓝[≠] 0, ∀ j, E.IsGeneric (t • v j +ᵥ g j x) := by
  classical
  let := Fintype.ofFinite ι
  let F : ExceptionalArrangement k P :=
    ⟨((Finset.univ.product E.exceptions).image
      (fun z : ι × AffineSubspace k Q => z.2.comap (g z.1))).erase ⊤,
      fun _ h => (Finset.mem_erase.mp h).1⟩
  refine ⟨F, fun x hx => eventually_all.mpr fun j => ?_⟩
  simp_rw [isGeneric_iff]
  apply E.exceptions.eventually_all.mpr
  intro S hS
  by_cases hv : v j ∈ S.direction
  · have hproper : S.comap (g j) ≠ ⊤ := by
      intro htop
      apply E.proper S hS
      apply top_unique
      intro y _
      obtain ⟨⟨z, t⟩, rfl⟩ := hg j y
      apply S.vadd_mem_of_mem_direction (S.direction.smul_mem t hv)
      exact AffineSubspace.mem_comap.mp (htop ▸ AffineSubspace.mem_top k U z)
    have hbase : g j x ∉ S := by
      intro hmem
      apply (isGeneric_iff.mp hx) (S.comap (g j))
      · exact Finset.mem_erase.mpr ⟨hproper, Finset.mem_image.mpr
          ⟨(j, S), Finset.mem_product.mpr ⟨Finset.mem_univ _, hS⟩, rfl⟩⟩
      · exact AffineSubspace.mem_comap.mpr hmem
    exact Eventually.of_forall fun t ht => hbase
      ((S.vadd_mem_iff_mem_of_mem_direction (S.direction.smul_mem t hv)).mp ht)
  · exact S.eventually_smul_vadd_notMem_nhdsNE hv (g j x) 0

/-- For a finite family of affine maps `g` and directions `v`, if each map
`(x, t) ↦ t • v j +ᵥ g j x` is surjective, there is a source arrangement `F` such
that at every `F`-generic `x`, all germs are eventually `E`-generic on the right
neighborhood of zero, simultaneously for all `j`. -/
theorem exists_forall_eventually_isGeneric_smul_vadd [Preorder k]
    (E : ExceptionalArrangement k Q) (g : ι → P →ᵃ[k] Q) (v : ι → V)
    (hg : ∀ j, Function.Surjective (fun z : P × k => z.2 • v j +ᵥ g j z.1)) :
    ∃ F : ExceptionalArrangement k P, ∀ x, F.IsGeneric x →
      ∀ᶠ t : k in 𝓝[>] 0, ∀ j, E.IsGeneric (t • v j +ᵥ g j x) := by
  obtain ⟨F, hF⟩ := E.exists_forall_eventually_isGeneric_smul_vadd_nhdsNE g v hg
  exact ⟨F, fun x hx => (hF x hx).filter_mono (nhdsWithin_mono 0 fun _ ht => ne_of_gt ht)⟩

end AffineFamilies

end TauCeti.ExceptionalArrangement
