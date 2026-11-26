/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.GroupTheory.GroupAction.Defs
import TauCeti.Topology.Algebra.GroupAction.SliceChart

/-!
# Smooth transitions of orbit-space slice charts

Let a group `G` act on a manifold `M`, and let `τ : S → M` be a slice whose slice map
`(g, s) ↦ g • τ s` is injective on `G × U` and a `C^n` local diffeomorphism at every point of
`G × U`, for an open set `U ⊆ S`. Then `s ↦ [τ s]` is a chart of the orbit space `M ⧸ G`
(`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`). This file shows that the slice coordinate
of the orbit of a point inherits its regularity: for every map `f` into `M` that is `C^n` at `z`,
with `f z` in an orbit through `τ (U)`, the point of `U` on the orbit of `f z'` is given near `z`
by a function `t` that is `C^n` at `z` (`TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`). It
is the second component of the local inverse of the slice map applied to `f`.

Applied to the slice `σ` of a second such chart, with `f = σ`, this says that the transition maps
between these charts of `M ⧸ G` are `C^n`. For a free proper smooth action of a Lie group,
transverse slices through every point give such charts, and these smooth transitions are what
make the orbit space a smooth manifold (the quotient manifold theorem).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, proof of Theorem 21.10
  (the quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003, proof of
  Theorem 1.21.
-/

public section

open Function Set Filter Manifold Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners 𝕜 F K}
  {S : Type*} [TopologicalSpace S] [ChartedSpace K S]

/-- **Smooth transitions of slice charts.** Let the slice map `(g, s) ↦ g • τ s` be injective on
`G × U` and a `C^n` local diffeomorphism at every point of `G × U`, for an open set `U`, so that
`s ↦ [τ s]` is a chart of the orbit space. Let `f : P → M` be `C^n` at `z`, with `f z` in the orbit
of `τ s` for some `s ∈ U`. Then the point of `U` on the orbit of `f z'` is given near `z` by a map
`t` that is `C^n` at `z`: we have `t z = s`, and for `z'` near `z` the points `s' ∈ U` with
`[τ s'] = [f z']` are exactly `t z'`. Applied to the slice of another chart, this is
the smoothness of the chart transitions of the orbit space. -/
theorem exists_contMDiffAt_quotientMk_slice_eq_iff {n : ℕ∞ω} {τ : S → M} {U : Set S} (hU : IsOpen U)
    (hinj : InjOn (fun p : G × S ↦ p.1 • τ p.2) (univ ×ˢ U))
    (hloc : IsLocalDiffeomorphOn (I.prod J) I' n (fun p : G × S ↦ p.1 • τ p.2) (univ ×ˢ U))
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    {K' : Type*} [TopologicalSpace K'] {L : ModelWithCorners 𝕜 F' K'}
    {P : Type*} [TopologicalSpace P] [ChartedSpace K' P] {f : P → M} {z : P}
    (hf : ContMDiffAt L I' n f z) {s : S} (hs : s ∈ U)
    (hfs : Quotient.mk (MulAction.orbitRel G M) (τ s) = Quotient.mk _ (f z)) :
    ∃ t : P → S, ContMDiffAt L J n t z ∧ t z = s ∧ ∀ᶠ z' in 𝓝 z, t z' ∈ U ∧
      ∀ s' ∈ U, Quotient.mk (MulAction.orbitRel G M) (τ s') = Quotient.mk _ (f z') ↔ s' = t z' := by
  obtain ⟨g, hg⟩ :=
    MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hfs.symm))
  -- Invert the slice map near `(g, s)`, which it sends to `f z`.
  have hl := hloc ⟨(g, s), mem_univ _, hs⟩
  have hgs : (fun p : G × S ↦ p.1 • τ p.2) (g, s) = f z := hg
  have hq : ContMDiffAt L (I.prod J) n (hl.localInverse ∘ f) z :=
    hl.contMDiffAt_localInverse.comp_of_eq hf hgs.symm
  have hqz : (hl.localInverse ∘ f) z = (g, s) := by
    rw [comp_apply, ← hgs]
    exact hl.localInverse_left_inv hl.localInverse_mem_target
  refine ⟨fun z' ↦ (hl.localInverse (f z')).2, contMDiffAt_snd.comp z hq,
    congrArg Prod.snd hqz, ?_⟩
  have hmemU : ∀ᶠ z' in 𝓝 z, (hl.localInverse ∘ f) z' ∈ univ ×ˢ U :=
    hq.continuousAt.preimage_mem_nhds
      ((isOpen_univ.prod hU).mem_nhds (by rw [hqz]; exact ⟨mem_univ _, hs⟩))
  have hmemS : ∀ᶠ z' in 𝓝 z, f z' ∈ hl.localInverse.source :=
    hf.continuousAt.preimage_mem_nhds
      (hl.localInverse_open_source.mem_nhds (hgs ▸ hl.localInverse_mem_source))
  filter_upwards [hmemU, hmemS] with z' hzU hzS
  -- The local inverse writes `f z'` as `γ • τ (t z')` with `t z' ∈ U`.
  have hrel : (hl.localInverse (f z')).1 • τ (hl.localInverse (f z')).2 = f z' :=
    hl.localInverse_right_inv hzS
  have hqt : Quotient.mk (MulAction.orbitRel G M) (τ (hl.localInverse (f z')).2) =
      Quotient.mk _ (f z') :=
    Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2
      ⟨(hl.localInverse (f z')).1⁻¹, inv_smul_eq_iff.2 hrel.symm⟩))
  -- `τ s'` and `τ (t z')` lie on one orbit, so injectivity on `G × U` identifies them.
  exact ⟨hzU.2, fun s' hs' ↦ ⟨fun h' ↦
    MulAction.injOn_quotientMk_slice hinj hs' hzU.2 (h'.trans hqt.symm), fun h' ↦ h' ▸ hqt⟩⟩

end TauCeti
