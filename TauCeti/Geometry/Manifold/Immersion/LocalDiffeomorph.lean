/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import all Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective

/-!
# Composing immersions with local diffeomorphisms

Mathlib defines `Manifold.IsImmersion` by a normal form in charts and lists the composition of
immersions as a `TODO` in `Mathlib/Geometry/Manifold/Immersion.lean`. The composition with a
diffeomorphism on either side is in `TauCeti.Geometry.Manifold.Immersion.Basic`. This file treats
the local version: composing with a `C^n` **local diffeomorphism**, on either side, preserves the
immersion normal form at a point, with the same complement.

As for diffeomorphisms, nothing has to be recombined. A partial diffeomorphism `Φ` of the source
carries a chart `ψ` of the maximal atlas to the chart `Φ ≫ ψ`, and `f ∘ Φ` read in it is `f` read
in `ψ`. On the target, a partial diffeomorphism `Θ` near `f x` pulls a chart `χ` back to
`Θ⁻¹ ≫ χ`, and `Θ ∘ f` read in it is `f` read in `χ`, once the source chart is shrunk so that `f`
maps it into the source of `Θ`.

Together with a topological embedding condition, this gives smooth embeddings: precomposing a
smooth embedding with a local diffeomorphism which is a topological embedding, or postcomposing
it with a map that is a local diffeomorphism along its image and a topological embedding on a set
containing the image, gives a smooth embedding. Charts of the maximal atlas and their inverses
are the basic examples of the latter
(`OpenPartialHomeomorph.isLocalDiffeomorphAt_of_mem_maximalAtlas` and
`OpenPartialHomeomorph.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas`).

## Main results

* `TauCeti.isImmersionAtOfComplement_comp_isLocalDiffeomorphAt`,
  `TauCeti.isImmersionAtOfComplement_isLocalDiffeomorphAt_comp`: the pointwise normal form with a
  fixed complement survives composing with a local diffeomorphism on the source or on the target.
* `TauCeti.isImmersionAtOfComplement_comp_isLocalDiffeomorphAt_iff`,
  `TauCeti.isImmersionAt_comp_isLocalDiffeomorphAt_iff`: on the source, precomposing with a local
  diffeomorphism also reflects the pointwise normal form, since a local inverse is again a local
  diffeomorphism.
* `TauCeti.isImmersion_comp_isLocalDiffeomorph`, `TauCeti.isImmersion_isLocalDiffeomorphAt_comp`:
  the corresponding statements for immersions.
* `TauCeti.isSmoothEmbedding_comp_isLocalDiffeomorph`,
  `TauCeti.isSmoothEmbedding_isLocalDiffeomorphAt_comp`: the corresponding statements for smooth
  embeddings.
* `Manifold.IsImmersion.codRestrict`: an immersion with image in an open subset is an immersion
  into that open submanifold.
* `Manifold.IsImmersion.isLocalDiffeomorph`: an immersion of a boundaryless manifold into a
  manifold modelled on a space of the same finite dimension is a local diffeomorphism.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 1, for immersions and their
  behaviour under composition.
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

/-- Precomposing with a local diffeomorphism of the source preserves the immersion normal form at a
point, with the same complement: the domain chart is pulled back along a partial diffeomorphism
representing the local diffeomorphism. -/
theorem isImmersionAtOfComplement_comp_isLocalDiffeomorphAt [IsManifold I n M']
    {g : M' → M} {x : M'} (hg : IsLocalDiffeomorphAt I I n g x)
    (h : IsImmersionAtOfComplement F I J n f (g x)) :
    IsImmersionAtOfComplement F I J n (f ∘ g) x := by
  have hcont : ContinuousAt (f ∘ g) x := h.continuousAt.comp hg.contMDiffAt.continuousAt
  obtain ⟨Φ, hxΦ, hgΦ⟩ := hg
  have hψ := h.domChart_mem_maximalAtlas
  refine IsImmersionAtOfComplement.mk_of_continuousAt hcont h.equiv
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

/-- Precomposing with a local diffeomorphism of the source preserves being an immersion at a
point. -/
theorem isImmersionAt_comp_isLocalDiffeomorphAt [IsManifold I n M']
    {g : M' → M} {x : M'} (hg : IsLocalDiffeomorphAt I I n g x)
    (h : IsImmersionAt I J n f (g x)) : IsImmersionAt I J n (f ∘ g) x :=
  (isImmersionAtOfComplement_comp_isLocalDiffeomorphAt hg
    h.isImmersionAtOfComplement_complement).isImmersionAt

/-- Precomposing an immersion with a fixed complement by a local diffeomorphism gives an immersion
with the same complement. -/
theorem isImmersionOfComplement_comp_isLocalDiffeomorph [IsManifold I n M']
    {g : M' → M} (hg : IsLocalDiffeomorph I I n g) (h : IsImmersionOfComplement F I J n f) :
    IsImmersionOfComplement F I J n (f ∘ g) :=
  fun x => isImmersionAtOfComplement_comp_isLocalDiffeomorphAt (hg x) (h (g x))

/-- Precomposing an immersion with a local diffeomorphism gives an immersion. -/
theorem isImmersion_comp_isLocalDiffeomorph [IsManifold I n M']
    {g : M' → M} (hg : IsLocalDiffeomorph I I n g) (h : IsImmersion I J n f) :
    IsImmersion I J n (f ∘ g) :=
  (isImmersionOfComplement_comp_isLocalDiffeomorph hg
    h.isImmersionOfComplement_complement).isImmersion

/-- Precomposing a smooth embedding with a local diffeomorphism which is a topological embedding
gives a smooth embedding. -/
theorem isSmoothEmbedding_comp_isLocalDiffeomorph [IsManifold I n M']
    {g : M' → M} (hg : IsLocalDiffeomorph I I n g) (hge : IsEmbedding g)
    (h : IsSmoothEmbedding I J n f) : IsSmoothEmbedding I J n (f ∘ g) :=
  ⟨isImmersion_comp_isLocalDiffeomorph hg h.isImmersion, h.isEmbedding.comp hge⟩

/-- Precomposing with a local diffeomorphism of the source neither creates nor destroys the
immersion normal form at a point: `f ∘ g` is an immersion at `x`, with complement `F`, exactly
when `f` is one at `g x`. -/
theorem isImmersionAtOfComplement_comp_isLocalDiffeomorphAt_iff [IsManifold I n M]
    [IsManifold I n M'] {g : M' → M} {x : M'} (hg : IsLocalDiffeomorphAt I I n g x) :
    IsImmersionAtOfComplement F I J n (f ∘ g) x ↔ IsImmersionAtOfComplement F I J n f (g x) := by
  refine ⟨fun h ↦ ?_, isImmersionAtOfComplement_comp_isLocalDiffeomorphAt hg⟩
  -- Near `g x`, `f` is `f ∘ g` composed with the local inverse of `g`, itself a local
  -- diffeomorphism.
  rw [← hg.localInverse_left_inv hg.localInverse_mem_target] at h
  exact (isImmersionAtOfComplement_comp_isLocalDiffeomorphAt
    hg.localInverse_isLocalDiffeomorphAt h).congr_of_eventuallyEq
    (hg.localInverse_eventuallyEq_right.fun_comp f)

/-- Precomposing with a local diffeomorphism of the source neither creates nor destroys
immersions at a point: `f ∘ g` is an immersion at `x` exactly when `f` is one at `g x`. -/
theorem isImmersionAt_comp_isLocalDiffeomorphAt_iff [IsManifold I n M] [IsManifold I n M']
    {g : M' → M} {x : M'} (hg : IsLocalDiffeomorphAt I I n g x) :
    IsImmersionAt I J n (f ∘ g) x ↔ IsImmersionAt I J n f (g x) :=
  ⟨fun h ↦ ((isImmersionAtOfComplement_comp_isLocalDiffeomorphAt_iff hg).1
    h.isImmersionAtOfComplement_complement).isImmersionAt,
    isImmersionAt_comp_isLocalDiffeomorphAt hg⟩

/-! ### Postcomposing with a local diffeomorphism -/

/-- Postcomposing with a local diffeomorphism of the target preserves the immersion normal form at
a point, with the same complement: the codomain chart is pulled back along a partial
diffeomorphism representing the local diffeomorphism, after shrinking the domain chart so that the
immersion maps it into the source of that partial diffeomorphism. -/
theorem isImmersionAtOfComplement_isLocalDiffeomorphAt_comp [IsManifold J n P]
    {k : N → P} {x : M} (hk : IsLocalDiffeomorphAt J J n k (f x))
    (h : IsImmersionAtOfComplement F I J n f x) :
    IsImmersionAtOfComplement F I J n (k ∘ f) x := by
  have hcont : ContinuousAt (k ∘ f) x := hk.contMDiffAt.continuousAt.comp h.continuousAt
  obtain ⟨Θ, hxΘ, hkΘ⟩ := hk
  -- The points mapped into the source of `Θ` form a neighbourhood `W` of `x`.
  set W := interior (f ⁻¹' Θ.source)
  have hxW : x ∈ W := mem_interior_iff_mem_nhds.2
    (h.continuousAt.preimage_mem_nhds (Θ.open_source.mem_nhds hxΘ))
  have hχ := h.codChart_mem_maximalAtlas
  refine IsImmersionAtOfComplement.mk_of_continuousAt hcont h.equiv (h.domChart.restr W)
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

/-- Postcomposing with a local diffeomorphism of the target preserves being an immersion at a
point. -/
theorem isImmersionAt_isLocalDiffeomorphAt_comp [IsManifold J n P] {k : N → P} {x : M}
    (hk : IsLocalDiffeomorphAt J J n k (f x))
    (h : IsImmersionAt I J n f x) : IsImmersionAt I J n (k ∘ f) x :=
  (isImmersionAtOfComplement_isLocalDiffeomorphAt_comp hk
    h.isImmersionAtOfComplement_complement).isImmersionAt

/-- Postcomposing an immersion with a fixed complement by a map which is a local diffeomorphism at
every point of its image gives an immersion with the same complement. -/
theorem isImmersionOfComplement_isLocalDiffeomorphAt_comp [IsManifold J n P] {k : N → P}
    (hk : ∀ x, IsLocalDiffeomorphAt J J n k (f x)) (h : IsImmersionOfComplement F I J n f) :
    IsImmersionOfComplement F I J n (k ∘ f) :=
  fun x => isImmersionAtOfComplement_isLocalDiffeomorphAt_comp (hk x) (h x)

/-- Postcomposing an immersion with a map which is a local diffeomorphism at every point of its
image gives an immersion. -/
theorem isImmersion_isLocalDiffeomorphAt_comp [IsManifold J n P] {k : N → P}
    (hk : ∀ x, IsLocalDiffeomorphAt J J n k (f x))
    (h : IsImmersion I J n f) : IsImmersion I J n (k ∘ f) :=
  (isImmersionOfComplement_isLocalDiffeomorphAt_comp hk
    h.isImmersionOfComplement_complement).isImmersion

/-- Postcomposing a smooth embedding with a map which is a local diffeomorphism at every point of
its image, and a topological embedding on a set containing the image, gives a smooth embedding. -/
theorem isSmoothEmbedding_isLocalDiffeomorphAt_comp [IsManifold J n P] {k : N → P} {s : Set N}
    (hk : ∀ x, IsLocalDiffeomorphAt J J n k (f x))
    (hfs : range f ⊆ s) (hks : IsEmbedding (s.domRestrict k)) (h : IsSmoothEmbedding I J n f) :
    IsSmoothEmbedding I J n (k ∘ f) :=
  ⟨isImmersion_isLocalDiffeomorphAt_comp hk h.isImmersion,
    hks.comp (h.isEmbedding.codRestrict s fun x => hfs (mem_range_self x))⟩

/-! ### Codomain restriction and the inverse function theorem -/

/-- An immersion with image in an open subset `U` stays an immersion into the open submanifold
`U`. -/
theorem _root_.Manifold.IsImmersion.codRestrict [IsManifold J n N] (hf : IsImmersion I J n f)
    (U : TopologicalSpace.Opens N) (h : ∀ x, f x ∈ U) :
    IsImmersion I J n fun x ↦ (⟨f x, h x⟩ : U) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact IsImmersionOfComplement.isImmersion (F := E') fun x ↦ isEmptyElim x
  have : Nonempty U := ⟨⟨f hM.some, h _⟩⟩
  -- Read `f` through the inverse of the inclusion `U → N`, a partial diffeomorphism with
  -- target `U`.
  let Φ := ((isLocalDiffeomorph_subtype_val (I := J) (n := n) (U := U)).isLocalDiffeomorphOn
    univ).partialDiffeomorphOfInjOn isOpen_univ Subtype.val_injective.injOn
  have hk (x : M) : IsLocalDiffeomorphAt J J n Φ.symm (f x) :=
    Φ.symm.isLocalDiffeomorphAt J J n (by simpa [Φ] using h x)
  have hcomp : Φ.symm ∘ f = fun x ↦ (⟨f x, h x⟩ : U) := funext fun x ↦
    (congrArg Φ.symm (by simp [Φ] : f x = Φ ⟨f x, h x⟩)).trans (Φ.left_inv (by simp [Φ]))
  exact hcomp ▸ isImmersion_isLocalDiffeomorphAt_comp hk hf

section InverseFunctionTheorem

variable {𝕂 : Type*} [RCLike 𝕂] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  [FiniteDimensional 𝕂 F] {K : ModelWithCorners 𝕂 F H}
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕂 F'] [FiniteDimensional 𝕂 F']
  {K' : ModelWithCorners 𝕂 F' G}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace G Y]
  [IsManifold K n X] [IsManifold K' n Y] [BoundarylessManifold K X]

/-- An immersion of a boundaryless manifold into a manifold modelled on a space of the same
finite dimension is a local diffeomorphism. -/
theorem _root_.Manifold.IsImmersion.isLocalDiffeomorph {g : X → Y} (hg : IsImmersion K K' n g)
    (hd : Module.finrank 𝕂 F = Module.finrank 𝕂 F') (hn : 1 ≤ n) :
    IsLocalDiffeomorph K K' n g := by
  have := FiniteDimensional.complete 𝕂 F
  refine isLocalDiffeomorph_of_mfderiv_eq hg.contMDiff hn fun y ↦ ?_
  let L := (mfderiv K K' g y : TangentSpace K y →ₗ[𝕂] TangentSpace K' (g y))
  have hinj : Function.Injective L :=
    (hg.isDiffImmersionAt (by rintro rfl; simp at hn) y).mfderiv_injective
  exact ⟨(LinearEquiv.ofInjectiveOfFinrankEq L hinj hd).toContinuousLinearEquiv,
    ContinuousLinearMap.ext fun v ↦
      LinearMap.congr_fun (LinearEquiv.coe_ofInjectiveOfFinrankEq L hinj hd) v⟩

end InverseFunctionTheorem

end TauCeti
