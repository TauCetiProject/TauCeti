/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.AffineSpace.Generic
public import Mathlib.Topology.Separation.Basic

/-!
# Generic one-sided affine germs

A germ transverse to an affine subspace eventually avoids it, including when its
base point is exceptional. For a finite family of affine maps and directions
whose combined images cover the target, one source exceptional arrangement makes
all fixed germs simultaneously generic. The affine maps themselves need not be
surjective. Scalars carry a linear order and a T1 topology; neither affine point
space needs a topology, a norm, or a chosen origin.

Adapted from `Mei/Geometry/Affine/IncomingGerm.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
-/

public section

open Set Filter Topology

namespace AffineSubspace

variable {k V P : Type*} [Field k] [LinearOrder k]
  [TopologicalSpace k] [T1Space k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- A transverse affine germ eventually avoids an affine subspace, even
when its base point lies in that subspace. -/
theorem eventually_smul_vadd_notMem (S : AffineSubspace k P)
    {v : V} (hv : v ∉ S.direction) (x : P) :
    ∀ᶠ t : k in 𝓝[>] 0, t • v +ᵥ x ∉ S := by
  have h := S.subsingleton_preimage_lineMap (x := x) (y := v +ᵥ x)
    (by simpa using hv)
  simpa only [Set.mem_preimage, AffineMap.lineMap_vadd_apply, AffineSubspace.mem_coe] using
    h.finite.eventually_cofinite_notMem.filter_mono
      ((nhdsWithin_mono (0 : k) (fun _ ht => ne_of_gt ht)).trans (nhdsNE_le_cofinite 0))

end AffineSubspace

namespace TauCeti.ExceptionalArrangement

section AffineFamilies

variable {k U V P Q ι : Type*} [Field k] [LinearOrder k]
  [TopologicalSpace k] [T1Space k] [AddCommGroup U] [Module k U] [AddTorsor U P]
  [AddCommGroup V] [Module k V] [AddTorsor V Q] [Finite ι]

/-- If each affine family together with its germ direction covers the target,
one exceptional arrangement in the source makes all its straight germs generic.
The affine maps need not be surjective, and no perturbation of the directions
or finite-dimensionality assumption is required. -/
theorem exists_forall_eventually_isGeneric_smul_vadd
    (E : ExceptionalArrangement k Q) (g : ι → P →ᵃ[k] Q) (v : ι → V)
    (hg : ∀ j, Function.Surjective (fun z : P × k => z.2 • v j +ᵥ g j z.1)) :
    ∃ F : ExceptionalArrangement k P, ∀ x, F.IsGeneric x →
      ∀ᶠ t : k in 𝓝[>] 0, ∀ j, E.IsGeneric (t • v j +ᵥ g j x) := by
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
  · exact S.eventually_smul_vadd_notMem hv (g j x)

end AffineFamilies

end TauCeti.ExceptionalArrangement
