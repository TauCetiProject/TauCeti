/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Regularity of sections of covering trivializations

If a bundle projection is a `C^n` local diffeomorphism, every inverse branch of any topological
trivialization is `C^n` on its base set. In particular, a topological covering which is a
`C^n` local diffeomorphism has `C^n` local sections on the same evenly covered neighborhoods;
there is no need to shrink the neighborhood separately for each sheet. When `n = ∞`, these
sections are smooth.

For an individual trivialization, local invertibility is needed only on its source.
No manifold structure on the fiber of the trivialization is required.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 4, smooth coverings.
-/

public section

open Set
open scoped Manifold ContDiff

namespace Bundle.Trivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M B A : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace B] [ChartedSpace G B] [TopologicalSpace A]
  {p : M → B} {n : ℕ∞ω}

/-- Every inverse branch of a topological trivialization of a local diffeomorphism is `C^n`
on the entire base set of the trivialization. -/
theorem contMDiffOn_symm_prodMk_left (e : Trivialization A p)
    (hp : IsLocalDiffeomorphOn I J n p e.source) (a : A) :
    ContMDiffOn J I n (fun y ↦ e.toOpenPartialHomeomorph.symm (y, a)) e.baseSet := by
  have hcomp : ContMDiffOn J J n
      (p ∘ fun y ↦ e.toOpenPartialHomeomorph.symm (y, a)) e.baseSet :=
    contMDiffOn_id.congr fun y hy ↦ e.proj_symm_apply' hy
  intro y hy
  exact (hcomp y hy).of_comp_isLocalDiffeomorph
    (hp ⟨_, e.map_target (e.mem_target.mpr hy)⟩)
    (e.continuousOn_symm_prodMk_left y hy)

end Bundle.Trivialization

namespace IsCoveringMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M B : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace B] [ChartedSpace G B] {p : M → B} {n : ℕ∞ω}

/-- A covering which is a `C^n` local diffeomorphism admits evenly covered neighborhoods with
`C^n` sections, labeled by their values in the fiber at the center. When `n = ∞`, these sections
are smooth. -/
theorem exists_trivialization_contMDiffOn_symm (hcover : IsCoveringMap p)
    (hp : IsLocalDiffeomorph I J n p) {y : B} (hy : y ∈ range p) :
    ∃ t : Bundle.Trivialization (p ⁻¹' {y}) p,
      y ∈ t.baseSet ∧
      (∀ a : p ⁻¹' {y}, t.toOpenPartialHomeomorph.symm (y, a) = a) ∧
      ∀ a : p ⁻¹' {y},
        ContMDiffOn J I n (fun z ↦ t.toOpenPartialHomeomorph.symm (z, a)) t.baseSet := by
  have : Nonempty (p ⁻¹' {y}) := by
    obtain ⟨x, hx⟩ := hy
    exact ⟨⟨x, hx⟩⟩
  let h := hcover y
  let t := h.toTrivialization
  have hy : y ∈ t.baseSet := h.mem_toTrivialization_baseSet
  refine ⟨t, hy, ?_, fun a ↦ t.contMDiffOn_symm_prodMk_left
    (hp.isLocalDiffeomorphOn t.source) a⟩
  rintro ⟨a, ha⟩
  have ha : p a = y := ha
  subst y
  have hlabel : (t a).2 = ⟨a, rfl⟩ := h.toTrivialization_apply
  simpa only [hlabel] using t.symm_apply_mk_proj (t.mem_source.mpr hy)

end IsCoveringMap
