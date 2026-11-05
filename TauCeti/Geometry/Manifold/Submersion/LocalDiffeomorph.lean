/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Submersion
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Composing submersions with local diffeomorphisms

Mathlib defines `Manifold.IsSubmersionAt` by a normal form in charts: around `x` there are charts
of the source and target in which the map reads as the projection `(u, v) ↦ u`. This file proves
that composing with a `C^n` **local diffeomorphism**, on either side, preserves this normal form at
a point, with the same complement. It is the submersion counterpart of
`TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph`.

Nothing has to be recombined. A partial diffeomorphism `Φ` of the source carries a chart `ψ` of
the maximal atlas to the chart `Φ ≫ ψ`, and `f ∘ Φ` read in it is `f` read in `ψ`. On the target,
a partial diffeomorphism `Θ` near `f x` pulls a chart `χ` back to `Θ⁻¹ ≫ χ`, and `Θ ∘ f` read in
it is `f` read in `χ`, once the source chart is shrunk so that `f` maps it into the source of `Θ`.

Precomposition with a local diffeomorphism `g` also reflects the normal form: `f` is a submersion
at `g x` as soon as `f ∘ g` is a submersion at `x`, because near `g x` the map `f` agrees with
`f ∘ g` composed with a local inverse of `g`, again a local diffeomorphism. This is how a map out
of a quotient manifold, such as the orbit space of a free properly discontinuous action, is shown
to be a submersion: the orbit projection is a local diffeomorphism, so it suffices to check the
lift of the map to the covering manifold.

The two composition proofs share their chart constructions with those for immersions in
`TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph`: both use
`IsLocalDiffeomorphAt.exists_mem_maximalAtlas_eqOn_extend_symm` and
`IsLocalDiffeomorphAt.exists_mem_maximalAtlas_comp_eqOn`, with the submersion normal form in place
of the immersion normal form.

## Main results

* `IsLocalDiffeomorphAt.isSubmersionAtOfComplement_comp`,
  `IsLocalDiffeomorphAt.comp_isSubmersionAtOfComplement`: the pointwise normal form with a
  fixed complement survives composing with a local diffeomorphism on the source or on the target.
* `IsLocalDiffeomorphAt.isSubmersionAtOfComplement_comp_iff`: precomposing with a local
  diffeomorphism at `x` neither creates nor destroys the normal form at `x`.
* `IsLocalDiffeomorphAt.isSubmersionAt_comp_iff`,
  `IsLocalDiffeomorphAt.comp_isSubmersionAt`: the same statements for `IsSubmersionAt`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 4,
  for submersions and their behaviour under composition.
-/

public section

noncomputable section

namespace IsLocalDiffeomorphAt

open Manifold Set Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
  {n : ℕ∞ω} {f : M → N}

/-! ### Precomposing with a local diffeomorphism -/

/-- Precomposing with a local diffeomorphism of the source preserves the submersion normal form at
a point, with the same complement: the domain chart is pulled back along a partial diffeomorphism
representing the local diffeomorphism. -/
theorem isSubmersionAtOfComplement_comp [IsManifold I n M']
    {g : M' → M} {x : M'} (hg : IsLocalDiffeomorphAt I I n g x)
    (h : IsSubmersionAtOfComplement F I J n f (g x)) :
    IsSubmersionAtOfComplement F I J n (f ∘ g) x := by
  obtain ⟨φ, hφ, hxφ, hφt, hgφ⟩ :=
    hg.exists_mem_maximalAtlas_eqOn_extend_symm h.domChart_mem_maximalAtlas h.mem_domChart_source
  exact .mk_of_continuousAt (h.contMDiffAt.continuousAt.comp hg.contMDiffAt.continuousAt) h.equiv
    φ h.codChart hxφ h.mem_codChart_source hφ h.codChart_mem_maximalAtlas fun u hu =>
      (congrArg (h.codChart.extend J ∘ f) (hgφ hu)).trans (h.writtenInCharts (hφt hu))

/-- **Submersions out of a local diffeomorphism.** If `g` is a local diffeomorphism at `x`, then
`f ∘ g` is a submersion at `x` with complement `F` exactly when `f` is a submersion at `g x` with
complement `F`. Near `g x`, the map `f` is `f ∘ g` composed with a local inverse of `g`. -/
theorem isSubmersionAtOfComplement_comp_iff [IsManifold I n M]
    [IsManifold I n M'] {g : M' → M} {x : M'} (hg : IsLocalDiffeomorphAt I I n g x) :
    IsSubmersionAtOfComplement F I J n (f ∘ g) x ↔ IsSubmersionAtOfComplement F I J n f (g x) := by
  refine ⟨fun h ↦ ?_, isSubmersionAtOfComplement_comp hg⟩
  -- Near `g x`, `f = (f ∘ g) ∘ g⁻¹` for the local inverse `g⁻¹`, which sends `g x` to `x`.
  have hinv := hg.localInverse_isLocalDiffeomorphAt
  have hx : hg.localInverse (g x) = x :=
    hg.localInverse_left_inv hg.localInverse_mem_target
  rw [← hx] at h
  refine (isSubmersionAtOfComplement_comp hinv h).congr_of_eventuallyEq ?_
  filter_upwards [hg.localInverse_eventuallyEq_right] with y hy
  simp only [Function.comp_apply] at hy ⊢
  rw [hy, id]

/-- Precomposing with a local diffeomorphism at `x` neither creates nor destroys being a
submersion at `x`. -/
theorem isSubmersionAt_comp_iff [IsManifold I n M] [IsManifold I n M']
    {g : M' → M} {x : M'} (hg : IsLocalDiffeomorphAt I I n g x) :
    IsSubmersionAt I J n (f ∘ g) x ↔ IsSubmersionAt I J n f (g x) :=
  ⟨fun h ↦ ((isSubmersionAtOfComplement_comp_iff hg).1
    h.isSubmersionAtOfComplement_complement).isSubmersionAt, fun h ↦
      (isSubmersionAtOfComplement_comp hg
        h.isSubmersionAtOfComplement_complement).isSubmersionAt⟩

/-! ### Postcomposing with a local diffeomorphism -/

/-- Postcomposing with a local diffeomorphism of the target preserves the submersion normal form at
a point, with the same complement: the codomain chart is pulled back along a partial
diffeomorphism representing the local diffeomorphism, after shrinking the domain chart so that the
submersion maps it into the source of that partial diffeomorphism. -/
theorem comp_isSubmersionAtOfComplement [IsManifold J n P]
    {k : N → P} {x : M} (hk : IsLocalDiffeomorphAt J J n k (f x))
    (h : IsSubmersionAtOfComplement F I J n f x) :
    IsSubmersionAtOfComplement F I J n (k ∘ f) x := by
  have hf : ContinuousAt f x := h.contMDiffAt.continuousAt
  obtain ⟨φ, hφ, ψ, hψ, hxφ, hψx, hφt, hfφ⟩ := hk.exists_mem_maximalAtlas_comp_eqOn hf
    h.domChart_mem_maximalAtlas h.mem_domChart_source h.codChart_mem_maximalAtlas
    h.mem_codChart_source
  exact .mk_of_continuousAt (hk.contMDiffAt.continuousAt.comp hf) h.equiv φ ψ hxφ hψx hφ hψ
    fun u hu => (hfφ hu).trans (h.writtenInCharts (hφt hu))

/-- Postcomposing with a local diffeomorphism of the target preserves being a submersion at a
point. -/
theorem comp_isSubmersionAt [IsManifold J n P] {k : N → P} {x : M}
    (hk : IsLocalDiffeomorphAt J J n k (f x)) (h : IsSubmersionAt I J n f x) :
    IsSubmersionAt I J n (k ∘ f) x :=
  (comp_isSubmersionAtOfComplement hk
    h.isSubmersionAtOfComplement_complement).isSubmersionAt

end IsLocalDiffeomorphAt
