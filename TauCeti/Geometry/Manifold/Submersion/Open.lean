/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Submersion.Split
public import TauCeti.Topology.Maps.LocalSections
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Openness, regular values and equal-dimension local diffeomorphisms for submersions

When the source model has no boundary, a `C^n` submersion admits a `C^n` local section through
every point of its domain (`Manifold.IsSubmersionAt.exists_contMDiffOn_section`), hence is an open
map (`Manifold.IsSubmersion.isOpenMap`). Neither smoothness order `n ≥ 1` nor finite dimensionality
is required for openness. Between manifolds sharing a model `I`, every `C^n` local diffeomorphism is
immediately a `C^n` submersion (`IsLocalDiffeomorph.isSubmersion_sameModel`).

When `n ≠ 0`, the derivative of a submersion is surjective at every point, so every point of the
codomain is a regular value (`Manifold.IsSubmersion.isRegularValue`) and a submersion in either
factor makes two maps transverse (`TauCeti.transverse_of_isSubmersion_left`,
`TauCeti.transverse_of_isSubmersion_right`). On a nonempty finite-dimensional source the target
dimension is at most the source dimension (`Manifold.IsSubmersion.finrank_le`), with equality on a
boundaryless source manifold (`BoundarylessManifold I M`) for `1 ≤ n` if and only if the submersion
is a local diffeomorphism (`Manifold.IsSubmersion.isLocalDiffeomorph_iff_finrank_eq`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 4.28 (submersions are open maps) and Corollary 4.13 (submersions between manifolds of
  equal dimension are local diffeomorphisms).
-/

public section

open Function Filter Set Manifold Module
open scoped Manifold ContDiff Topology

namespace Manifold

section General

variable {𝕜 E F H G M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N}

/-- **Submersions from boundaryless models are open maps.** Around every point of `M` the
normal-form charts supply a local section of `f`, which forces images of neighbourhoods to remain
neighbourhoods. -/
theorem IsSubmersion.isOpenMap [I.Boundaryless] (hf : IsSubmersion I J n f) : IsOpenMap f := by
  refine IsOpenMap.of_local_sections fun x ↦ ?_
  obtain ⟨U, hU, hxU, s, hsx, hs, hfs⟩ := (hf.isSubmersionAt x).exists_contMDiffOn_section
  exact ⟨s, hs.continuousOn.continuousAt (hU.mem_nhds hxU), hsx,
    eventually_of_mem (hU.mem_nhds hxU) hfs⟩

/-- Between manifolds sharing the model `I`, a `C^n` local diffeomorphism at `x` is a `C^n`
submersion at `x` (including for `n = 0`, infinite-dimensional models, and models with
boundary). -/
theorem _root_.IsLocalDiffeomorphAt.isSubmersionAt_sameModel {M' : Type*}
    [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I n M] [IsManifold I n M']
    {g : M → M'} {x : M} (hg : IsLocalDiffeomorphAt I I n g x) :
    IsSubmersionAt I I n g x :=
  (hg.isSubmersionAtOfComplement_comp (F := Unit)
    (IsSubmersionOfComplement.id.isSubmersionAt (g x))).isSubmersionAt

/-- Between manifolds sharing the model `I`, a `C^n` local diffeomorphism is a `C^n` submersion
(including for `n = 0`, infinite-dimensional models, and models with boundary). -/
theorem _root_.IsLocalDiffeomorph.isSubmersion_sameModel {M' : Type*}
    [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I n M] [IsManifold I n M']
    {g : M → M'} (hg : IsLocalDiffeomorph I I n g) :
    IsSubmersion I I n g :=
  (isSubmersionOfComplement_iff (F := Unit).mpr fun x ↦
    (hg x).isSubmersionAtOfComplement_comp
      (IsSubmersionOfComplement.id.isSubmersionAt (g x))).isSubmersion

/-- Every point of the codomain is a regular value of a differentiable submersion. -/
theorem IsSubmersion.isRegularValue (hf : IsSubmersion I J n f) (hn : n ≠ 0) (c : N) :
    TauCeti.IsRegularValue I J f c :=
  TauCeti.isRegularValue_iff.mpr fun x _ ↦
    TauCeti.isRegularPoint_iff.mpr (hf.surjective_mfderiv hn x)

/-- At any point of a differentiable submersion from a finite-dimensional model, the target model
dimension is at most the source model dimension. -/
theorem IsSubmersionAt.finrank_le [FiniteDimensional 𝕜 E] {x : M}
    (hf : IsSubmersionAt I J n f x) (hn : n ≠ 0) :
    finrank 𝕜 F ≤ finrank 𝕜 E :=
  LinearMap.finrank_le_finrank_of_surjective (hf.surjective_mfderiv hn)

/-- For a differentiable submersion from a nonempty finite-dimensional manifold, the target model
dimension is at most the source model dimension. -/
theorem IsSubmersion.finrank_le [FiniteDimensional 𝕜 E] [Nonempty M]
    (hf : IsSubmersion I J n f) (hn : n ≠ 0) :
    finrank 𝕜 F ≤ finrank 𝕜 E :=
  let ⟨x⟩ := ‹Nonempty M›
  (hf.isSubmersionAt x).finrank_le hn

end General

section EqualDimension

variable {𝕜 E F H G M N : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {n : ℕ∞ω}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J n N]
  {f : M → N}

/-- A `C^n` local diffeomorphism (`1 ≤ n`) from a manifold modeled on a boundaryless
finite-dimensional space is a `C^n` submersion, even across distinct models `I` and `J`. -/
theorem _root_.IsLocalDiffeomorph.isSubmersion [I.Boundaryless]
    (hf : IsLocalDiffeomorph I J n f) (hn : 1 ≤ n) :
    IsSubmersion I J n f := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact (isSubmersionOfComplement_iff.mpr fun x ↦ isEmptyElim x :
      IsSubmersionOfComplement E I J n f).isSubmersion
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have e₀ := (hf x₀).mfderivToContinuousLinearEquiv hn0
  have : FiniteDimensional 𝕜 F := by
    have : Module.Finite 𝕜 (TangentSpace J (f x₀)) :=
      Module.Finite.of_surjective e₀.toLinearMap e₀.surjective
    exact this
  exact (hf.contMDiff.isSubmersionOfComplement_of_surjective_mfderiv hn fun x ↦
    ((hf x).mfderivToContinuousLinearEquiv hn0).surjective).isSubmersion

/-- A `C^n` submersion (`1 ≤ n`) from a boundaryless finite-dimensional manifold into a manifold of
the same finite model dimension is a `C^n` local diffeomorphism. -/
theorem IsSubmersion.isLocalDiffeomorph [BoundarylessManifold I M] (hf : IsSubmersion I J n f)
    (hd : finrank 𝕜 E = finrank 𝕜 F) (hn : 1 ≤ n) :
    IsLocalDiffeomorph I J n f := fun x ↦ by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hsurj : Surjective (mfderiv I J f x).toLinearMap := hf.surjective_mfderiv hn0 x
  have : FiniteDimensional 𝕜 F := by
    have : Module.Finite 𝕜 (TangentSpace J (f x)) :=
      Module.Finite.of_surjective (mfderiv I J f x).toLinearMap hsurj
    exact this
  have := FiniteDimensional.completeSpace 𝕜 E
  exact TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv hf.contMDiff.contMDiffOn isOpen_univ
    (mem_univ x) BoundarylessManifold.isInteriorPoint hn
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hsurj) hd

/-- On a nonempty boundaryless finite-dimensional manifold, a `C^n` submersion (`1 ≤ n`) is a local
diffeomorphism if and only if the source and target models have the same dimension. -/
theorem IsSubmersion.isLocalDiffeomorph_iff_finrank_eq [BoundarylessManifold I M] [Nonempty M]
    (hf : IsSubmersion I J n f) (hn : 1 ≤ n) :
    IsLocalDiffeomorph I J n f ↔ finrank 𝕜 E = finrank 𝕜 F := by
  refine ⟨fun h ↦ ?_, fun hd ↦ hf.isLocalDiffeomorph hd hn⟩
  obtain ⟨x⟩ := ‹Nonempty M›
  exact ((h x).mfderivToContinuousLinearEquiv
    (ne_of_gt (zero_lt_one.trans_le hn))).toLinearEquiv.finrank_eq

end EqualDimension

end Manifold

namespace TauCeti

section Transversality

variable {𝕜 EX HX X EY HY Y EN HN N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  [NormedAddCommGroup EY] [NormedSpace 𝕜 EY] [TopologicalSpace HY]
  [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] [TopologicalSpace HN]
  {IX : ModelWithCorners 𝕜 EX HX} {IY : ModelWithCorners 𝕜 EY HY}
  {IN : ModelWithCorners 𝕜 EN HN}
  [TopologicalSpace X] [ChartedSpace HX X]
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace N] [ChartedSpace HN N]
  {n : ℕ∞ω} {f : X → N} {g : Y → N}

/-- A differentiable submersion in the first factor is transverse to any map in the second
factor. -/
theorem transverse_of_isSubmersion_left (hf : Manifold.IsSubmersion IX IN n f) (hn : n ≠ 0)
    (p : X × Y) (_ : f p.1 = g p.2) :
    (mfderiv IX IN f p.1).range ⊔
      (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.2)).range = ⊤ := by
  rw [LinearMap.range_eq_top.mpr (hf.surjective_mfderiv hn p.1), top_sup_eq]

/-- A differentiable submersion in the second factor is transverse to any map in the first
factor. -/
theorem transverse_of_isSubmersion_right (hg : Manifold.IsSubmersion IY IN n g) (hn : n ≠ 0)
    (p : X × Y) (_ : f p.1 = g p.2) :
    (mfderiv IX IN f p.1).range ⊔
      (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.2)).range = ⊤ := by
  have hsurj : Surjective
      (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.2)) :=
    (tangentSpaceCast IN (g p.2) (f p.1)).surjective.comp (hg.surjective_mfderiv hn p.2)
  rw [LinearMap.range_eq_top.mpr hsurj, sup_top_eq]

end Transversality

end TauCeti
