/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Submersion
import all Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Submersion

/-!
# Composing submersions with local diffeomorphisms

Mathlib defines `Manifold.IsSubmersion` by a normal form in charts and lists the composition of
submersions as a `TODO` in `Mathlib/Geometry/Manifold/Submersion.lean`. This file treats the
local diffeomorphism case: composing with a `C^n` **local diffeomorphism**, on either side,
preserves the submersion normal form at a point, with the same complement.

Nothing has to be recombined. A partial diffeomorphism `Φ` of the source carries a chart `ψ` of
the maximal atlas to the chart `Φ ≫ ψ`, and `f ∘ Φ` read in it is `f` read in `ψ`. On the target,
a partial diffeomorphism `Θ` near `f x` pulls a chart `χ` back to `Θ⁻¹ ≫ χ`, and `Θ ∘ f` read in
it is `f` read in `χ`, once the source chart is shrunk so that `f` maps it into the source of `Θ`.

Precomposition can also be undone: if `q` is a local diffeomorphism at `x` and `f ∘ q` is a
submersion at `x`, then `f` is a submersion at `q x`, since near `q x` the map `f` is `f ∘ q`
composed with a local inverse of `q`. This is how submersions descend along quotient maps which
are local diffeomorphisms, such as orbit projections of free properly discontinuous actions.

## Main results

* `TauCeti.isSubmersionAtOfComplement_comp_isLocalDiffeomorphAt`,
  `TauCeti.isSubmersionAtOfComplement_isLocalDiffeomorphAt_comp`: the pointwise normal form with
  a fixed complement survives composing with a local diffeomorphism on the source or on the
  target.
* `TauCeti.isSubmersionOfComplement_comp_isLocalDiffeomorph`,
  `TauCeti.isSubmersionOfComplement_isLocalDiffeomorphAt_comp`: the corresponding statements for
  submersions with a fixed complement.
* `TauCeti.isSubmersionAtOfComplement_of_comp_isLocalDiffeomorphAt`: if `f ∘ q` is a submersion
  at `x` and `q` is a local diffeomorphism at `x`, then `f` is a submersion at `q x`.

The two composition proofs follow those for immersions in
`TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph`, with the submersion normal form in place of
the immersion normal form.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 4
  (submersions and local diffeomorphisms).
-/

public section

noncomputable section

namespace TauCeti

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
theorem isSubmersionAtOfComplement_comp_isLocalDiffeomorphAt [IsManifold I n M']
    {g : M' → M} {x : M'} (hg : IsLocalDiffeomorphAt I I n g x)
    (h : IsSubmersionAtOfComplement F I J n f (g x)) :
    IsSubmersionAtOfComplement F I J n (f ∘ g) x := by
  have hcont : ContinuousAt (f ∘ g) x := h.contMDiffAt.continuousAt.comp hg.contMDiffAt.continuousAt
  obtain ⟨Φ, hxΦ, hgΦ⟩ := hg
  have hψ := h.domChart_mem_maximalAtlas
  refine IsSubmersionAtOfComplement.mk_of_continuousAt hcont h.equiv
    (Φ.toOpenPartialHomeomorph.trans h.domChart) h.codChart ?_ h.mem_codChart_source ?_
    h.codChart_mem_maximalAtlas fun u hu => ?_
  · refine ⟨hxΦ, ?_⟩
    simpa [← hgΦ hxΦ] using h.mem_domChart_source
  · refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
    · exact (contMDiffOn_of_mem_maximalAtlas hψ).comp (Φ.contMDiffOn.mono inter_subset_left)
        fun y hy => hy.2
    · exact Φ.symm.contMDiffOn.comp ((contMDiffOn_symm_of_mem_maximalAtlas hψ).mono
        inter_subset_left) fun y hy => hy.2
  · -- Reading `f ∘ g` through the pulled-back chart reinstates `Φ⁻¹`, which `g = Φ` cancels.
    simp only [OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.trans_target,
      mem_inter_iff, mem_preimage] at hu
    obtain ⟨⟨hu₁, hu₂⟩, hu₃⟩ := hu
    have hu' : u ∈ (h.domChart.extend I).target := by
      rw [OpenPartialHomeomorph.extend_target]
      exact ⟨hu₁, hu₃⟩
    have hgΦ' : g (Φ.symm (h.domChart.symm (I.symm u))) = h.domChart.symm (I.symm u) := by
      rw [hgΦ (Φ.symm.toPartialEquiv.map_source hu₂)]
      exact Φ.toPartialEquiv.right_inv hu₂
    -- Unfold the extended pulled-back chart: its inverse is `Φ⁻¹ ∘ ψ⁻¹ ∘ I⁻¹`.
    calc _ = h.codChart.extend J (f (g (Φ.symm.toPartialEquiv (h.domChart.symm (I.symm u))))) :=
          rfl
      _ = h.codChart.extend J (f (h.domChart.symm (I.symm u))) := by rw [hgΦ']
      _ = _ := h.writtenInCharts hu'

/-- Precomposing a submersion with a fixed complement by a local diffeomorphism gives a submersion
with the same complement. -/
theorem isSubmersionOfComplement_comp_isLocalDiffeomorph [IsManifold I n M']
    {g : M' → M} (hg : IsLocalDiffeomorph I I n g) (h : IsSubmersionOfComplement F I J n f) :
    IsSubmersionOfComplement F I J n (f ∘ g) :=
  isSubmersionOfComplement_iff.2 fun x =>
    isSubmersionAtOfComplement_comp_isLocalDiffeomorphAt (hg x) (h.isSubmersionAt (g x))

/-- **Undoing a precomposition.** If `q` is a local diffeomorphism at `x` and `f ∘ q` is a
submersion at `x`, then `f` is a submersion at `q x`, with the same complement: near `q x`, the map
`f` is `f ∘ q` composed with a local inverse of `q`. -/
theorem isSubmersionAtOfComplement_of_comp_isLocalDiffeomorphAt [IsManifold I n M]
    {q : M' → M} {x : M'} (hq : IsLocalDiffeomorphAt I I n q x)
    (h : IsSubmersionAtOfComplement F I J n (f ∘ q) x) :
    IsSubmersionAtOfComplement F I J n f (q x) := by
  have h' : IsSubmersionAtOfComplement F I J n (f ∘ q) (hq.localInverse (q x)) := by
    rwa [hq.localInverse_left_inv hq.localInverse_mem_target]
  exact (isSubmersionAtOfComplement_comp_isLocalDiffeomorphAt
    hq.localInverse_isLocalDiffeomorphAt h').congr_of_eventuallyEq
    (hq.localInverse_eventuallyEq_right.fun_comp f)

/-! ### Postcomposing with a local diffeomorphism -/

/-- Postcomposing with a local diffeomorphism of the target preserves the submersion normal form at
a point, with the same complement: the codomain chart is pulled back along a partial
diffeomorphism representing the local diffeomorphism, after shrinking the domain chart so that the
submersion maps it into the source of that partial diffeomorphism. -/
theorem isSubmersionAtOfComplement_isLocalDiffeomorphAt_comp [IsManifold J n P]
    {k : N → P} {x : M} (hk : IsLocalDiffeomorphAt J J n k (f x))
    (h : IsSubmersionAtOfComplement F I J n f x) :
    IsSubmersionAtOfComplement F I J n (k ∘ f) x := by
  have hfx : ContinuousAt f x := h.contMDiffAt.continuousAt
  have hcont : ContinuousAt (k ∘ f) x := hk.contMDiffAt.continuousAt.comp hfx
  obtain ⟨Θ, hxΘ, hkΘ⟩ := hk
  -- The points mapped into the source of `Θ` form a neighbourhood `W` of `x`.
  set W := interior (f ⁻¹' Θ.source)
  have hxW : x ∈ W := mem_interior_iff_mem_nhds.2
    (hfx.preimage_mem_nhds (Θ.open_source.mem_nhds hxΘ))
  have hχ := h.codChart_mem_maximalAtlas
  refine IsSubmersionAtOfComplement.mk_of_continuousAt hcont h.equiv (h.domChart.restr W)
    (Θ.symm.toOpenPartialHomeomorph.trans h.codChart) ?_ ?_
    (restr_mem_maximalAtlas _ h.domChart_mem_maximalAtlas isOpen_interior) ?_ fun u hu => ?_
  · exact ⟨h.mem_domChart_source, by rwa [interior_interior]⟩
  · simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage, Function.comp_apply]
    refine ⟨by rw [hkΘ hxΘ]; exact Θ.toPartialEquiv.map_source hxΘ, ?_⟩
    rw [hkΘ hxΘ]
    simpa [hkΘ hxΘ, Θ.toPartialEquiv.left_inv hxΘ] using h.mem_codChart_source
  · refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
    · exact (contMDiffOn_of_mem_maximalAtlas hχ).comp (Θ.symm.contMDiffOn.mono inter_subset_left)
        fun y hy => hy.2
    · exact Θ.contMDiffOn.comp ((contMDiffOn_symm_of_mem_maximalAtlas hχ).mono
        inter_subset_left) fun y hy => hy.2
  · -- On the shrunken chart `f` lands in the source of `Θ`, where `Θ⁻¹` cancels `k = Θ`.
    simp only [OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.restr_target,
      mem_inter_iff, mem_preimage] at hu
    obtain ⟨⟨hu₁, hu₂⟩, hu₃⟩ := hu
    have hu' : u ∈ (h.domChart.extend I).target := by
      rw [OpenPartialHomeomorph.extend_target]
      exact ⟨hu₁, hu₃⟩
    have hW : interior W ⊆ f ⁻¹' Θ.source := interior_subset.trans interior_subset
    have hfy : f (h.domChart.symm (I.symm u)) ∈ Θ.source := hW hu₂
    -- Unfold the extended charts: the restricted chart has the same inverse as `ψ`, and the
    -- pulled-back chart is `χ ∘ Θ⁻¹`.
    calc _ = h.codChart.extend J (Θ.toPartialEquiv.symm (k (f (h.domChart.symm (I.symm u))))) :=
          rfl
      _ = h.codChart.extend J (f (h.domChart.symm (I.symm u))) := by
          rw [hkΘ hfy, Θ.toPartialEquiv.left_inv hfy]
      _ = _ := h.writtenInCharts hu'

/-- Postcomposing a submersion with a fixed complement by a map which is a local diffeomorphism at
every point of its image gives a submersion with the same complement. -/
theorem isSubmersionOfComplement_isLocalDiffeomorphAt_comp [IsManifold J n P] {k : N → P}
    (hk : ∀ x, IsLocalDiffeomorphAt J J n k (f x)) (h : IsSubmersionOfComplement F I J n f) :
    IsSubmersionOfComplement F I J n (k ∘ f) :=
  isSubmersionOfComplement_iff.2 fun x =>
    isSubmersionAtOfComplement_isLocalDiffeomorphAt_comp (hk x) (h.isSubmersionAt x)

end TauCeti
