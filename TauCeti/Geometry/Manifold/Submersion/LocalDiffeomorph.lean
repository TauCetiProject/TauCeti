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
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.IsManifold.InteriorChart
import TauCeti.Geometry.Manifold.Submersion.Basic
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Local diffeomorphisms and submersions

Mathlib defines `Manifold.IsSubmersionAt` by a normal form in charts: around `x` there are charts
of the source and target in which the map reads as the projection `(u, v) ↦ u`. This file proves
that composing with a `C^n` **local diffeomorphism**, on either side, preserves this normal form at
a point, with the same complement, and that every `C^n` local diffeomorphism (`n ≠ 0`) between
boundaryless manifolds is itself a submersion with trivial complement `PUnit.{1}` (and hence so is
every `C^n` diffeomorphism). It is the submersion counterpart of
`TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph`.

Nothing has to be recombined when composing. A partial diffeomorphism `Φ` of the source carries a
chart `ψ` of the maximal atlas to the chart `Φ ≫ ψ`, and `f ∘ Φ` read in it is `f` read in `ψ`. On
the target, a partial diffeomorphism `Θ` near `f x` pulls a chart `χ` back to `Θ⁻¹ ≫ χ`, and `Θ ∘ f`
read in it is `f` read in `χ`, once the source chart is shrunk so that `f` maps it into the source
of `Θ`.

Precomposition with a local diffeomorphism `g` also reflects the normal form: `f` is a submersion
at `g x` as soon as `f ∘ g` is a submersion at `x`, because near `g x` the map `f` agrees with
`f ∘ g` composed with a local inverse of `g`, again a local diffeomorphism. This is how a map out
of a quotient manifold, such as the orbit space of a free properly discontinuous action, is shown
to be a submersion: the orbit projection is a local diffeomorphism, so it suffices to check the
lift of the map to the covering manifold.

For a `C^n` local diffeomorphism `f : M → N` (`n ≠ 0`) between boundaryless manifolds, `mfderiv`
identifies the model spaces `E ≃L[𝕜] E'`, so pulling back a target chart along a representing
partial diffeomorphism yields a source chart in which `f` reads as `u ↦ (L u).1` with complement
`PUnit.{1}`.

## Main results

* `IsLocalDiffeomorphAt.isSubmersionAtOfComplement_comp`,
  `IsLocalDiffeomorphAt.comp_isSubmersionAtOfComplement`: the pointwise normal form with a
  fixed complement survives composing with a local diffeomorphism on the source or on the target.
* `IsLocalDiffeomorph.isSubmersion_comp`, `IsLocalDiffeomorph.comp_isSubmersion`: the global
  statements, for composing with a local diffeomorphism everywhere.
* `Manifold.IsSubmersion.isLocalDiffeomorph_iff_finrank_eq`: a submersion with boundaryless
  source is a local diffeomorphism exactly when source and target have the same dimension.
* `IsLocalDiffeomorphAt.isSubmersionAtOfComplement_comp_iff`: precomposing with a local
  diffeomorphism at `x` neither creates nor destroys the normal form at `x`.
* `IsLocalDiffeomorphAt.isSubmersionAt_comp_iff`,
  `IsLocalDiffeomorphAt.comp_isSubmersionAt`: the same statements for `IsSubmersionAt`.
* `IsLocalDiffeomorphAt.isSubmersionAtOfComplement`, `IsLocalDiffeomorphAt.isSubmersionAt`: a `C^n`
  local diffeomorphism at `x` (`n ≠ 0`) between boundaryless manifolds is a submersion at `x` with
  complement `PUnit.{1}`.
* `IsLocalDiffeomorph.isSubmersionOfComplement`, `IsLocalDiffeomorph.isSubmersion`: every `C^n`
  local diffeomorphism (`n ≠ 0`) between boundaryless manifolds is a submersion.
* `Diffeomorph.isSubmersionOfComplement`, `Diffeomorph.isSubmersion`: every `C^n` diffeomorphism
  (`n ≠ 0`) between boundaryless manifolds is a submersion.

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
  have hcont : ContinuousAt (f ∘ g) x :=
    h.contMDiffAt.continuousAt.comp hg.contMDiffAt.continuousAt
  obtain ⟨Φ, hxΦ, hgΦ⟩ := hg
  have hψ := h.domChart_mem_maximalAtlas
  refine IsSubmersionAtOfComplement.mk_of_continuousAt hcont h.equiv
    (Φ.toOpenPartialHomeomorph.trans h.domChart) h.codChart ?_ h.mem_codChart_source ?_
    h.codChart_mem_maximalAtlas fun u hu => ?_
  · refine ⟨hxΦ, ?_⟩
    simpa [← hgΦ hxΦ] using h.mem_domChart_source
  · exact Φ.trans_mem_maximalAtlas hψ
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
  have hfc : ContinuousAt f x := h.contMDiffAt.continuousAt
  have hcont : ContinuousAt (k ∘ f) x := hk.contMDiffAt.continuousAt.comp hfc
  obtain ⟨Θ, hxΘ, hkΘ⟩ := hk
  -- The points mapped into the source of `Θ` form a neighbourhood `W` of `x`.
  set W := interior (f ⁻¹' Θ.source)
  have hxW : x ∈ W := mem_interior_iff_mem_nhds.2
    (hfc.preimage_mem_nhds (Θ.open_source.mem_nhds hxΘ))
  have hχ := h.codChart_mem_maximalAtlas
  refine IsSubmersionAtOfComplement.mk_of_continuousAt hcont h.equiv (h.domChart.restr W)
    (Θ.symm.toOpenPartialHomeomorph.trans h.codChart) ?_ ?_
    (restr_mem_maximalAtlas _ h.domChart_mem_maximalAtlas isOpen_interior) ?_ fun u hu => ?_
  · exact ⟨h.mem_domChart_source, by rwa [interior_interior]⟩
  · simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage, Function.comp_apply]
    refine ⟨by rw [hkΘ hxΘ]; exact Θ.toPartialEquiv.map_source hxΘ, ?_⟩
    rw [hkΘ hxΘ]
    simpa [hkΘ hxΘ, Θ.toPartialEquiv.left_inv hxΘ] using h.mem_codChart_source
  · exact Θ.symm.trans_mem_maximalAtlas hχ
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

/-- Postcomposing with a local diffeomorphism of the target preserves being a submersion at a
point. -/
theorem comp_isSubmersionAt [IsManifold J n P] {k : N → P} {x : M}
    (hk : IsLocalDiffeomorphAt J J n k (f x)) (h : IsSubmersionAt I J n f x) :
    IsSubmersionAt I J n (k ∘ f) x :=
  (comp_isSubmersionAtOfComplement hk
    h.isSubmersionAtOfComplement_complement).isSubmersionAt

end IsLocalDiffeomorphAt

/-! ### Local diffeomorphisms and diffeomorphisms as submersions -/

section LocalDiffeomorph

open Function Set
open OpenPartialHomeomorph (transHomeomorph_source transHomeomorph_target trans_source trans_target
  extend_target extendTrans_source extendTrans_target extendTrans_symm_apply)
open scoped Manifold ContDiff

variable {𝕜 E E' H G M N : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J n N]

/-- A `C^n` local diffeomorphism at `x` (`n ≠ 0`) between boundaryless manifolds is a submersion at
`x` with complement `PUnit.{1}`. -/
theorem IsLocalDiffeomorphAt.isSubmersionAtOfComplement {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    Manifold.IsSubmersionAtOfComplement PUnit.{1} I J n f x := by
  have hcont : ContinuousAt f x := hf.contMDiffAt.continuousAt
  obtain ⟨L₀⟩ : Nonempty (E ≃L[𝕜] E') := ⟨(tangentSpaceCastModel I x).symm.trans <|
    (hf.mfderivToContinuousLinearEquiv hn).trans (tangentSpaceCastModel J (f x))⟩
  obtain ⟨Θ, hxΘ, hfΘ⟩ := hf; let ψ := chartAt G (f x)
  have hψ : ψ ∈ IsManifold.maximalAtlas J n N := IsManifold.chart_mem_maximalAtlas (f x)
  let Ξ := Θ.toOpenPartialHomeomorph.trans (ψ.extendTrans J L₀.symm.toHomeomorph)
  let φ := Ξ.trans I.interiorChart.symm
  have hΞ : ContMDiffOn I 𝓘(𝕜, E) n Ξ Ξ.source :=
    (ψ.contMDiffOn_extendTrans hψ L₀.symm.contDiff).comp (Θ.contMDiffOn.mono inter_subset_left)
      fun _ hz ↦ hz.2
  have hΞs : ContMDiffOn 𝓘(𝕜, E) I n Ξ.symm Ξ.target :=
    Θ.symm.contMDiffOn.comp ((ψ.contMDiffOn_extendTrans_symm hψ L₀.contDiff).mono
      inter_subset_left) fun _ hz ↦ hz.2
  have hφ := Ξ.trans_interiorChart_symm_mem_maximalAtlas hΞ hΞs
  have hxφ : x ∈ φ.source := by
    simp only [φ, Ξ, trans_source, extendTrans_source, OpenPartialHomeomorph.symm_source,
      ModelWithCorners.interiorChart_target, I.range_eq_univ, interior_univ, preimage_univ,
      inter_univ, PartialDiffeomorph.toOpenPartialHomeomorph_source,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, mem_inter_iff, mem_preimage]
    exact ⟨hxΘ, by rw [← hfΘ hxΘ]; exact mem_chart_source G (f x)⟩
  let L : E ≃L[𝕜] E' × PUnit.{1} := L₀.trans (ContinuousLinearEquiv.prodUnique 𝕜 E' PUnit.{1}).symm
  refine .mk_of_continuousAt hcont L φ ψ hxφ (mem_chart_source G (f x)) hφ hψ fun u hu ↦ ?_
  have huΞ : u ∈ Ξ.target := by
    rwa [OpenPartialHomeomorph.extend_trans_interiorChart_symm_target] at hu
  simp only [Ξ, ContinuousLinearEquiv.toHomeomorph_symm, Homeomorph.symm_symm, trans_target,
    extendTrans_target, extendTrans_symm_apply, PartialDiffeomorph.toOpenPartialHomeomorph_target,
    ContinuousLinearEquiv.coe_toHomeomorph, mem_inter_iff, mem_preimage] at huΞ
  have huΨ : L₀ u ∈ (ψ.extend J).target := by simpa [extend_target, J.range_eq_univ] using huΞ.1
  have hyΘ : (ψ.extend J).symm (L₀ u) ∈ Θ.target := by simpa using huΞ.2
  have hsymm : (φ.extend I).symm u = Θ.toPartialEquiv.symm ((ψ.extend J).symm (L₀ u)) := by
    dsimp only [φ]
    rw [OpenPartialHomeomorph.extend_trans_interiorChart_symm_symm]
    simp [Ξ]
  dsimp only [comp_apply]
  rw [hsymm, hfΘ (Θ.toPartialEquiv.map_target hyΘ), Θ.toPartialEquiv.right_inv hyΘ]
  exact (ψ.extend J).right_inv huΨ

/-- A `C^n` local diffeomorphism at `x` (`n ≠ 0`) between boundaryless manifolds is a submersion at
`x`. -/
theorem IsLocalDiffeomorphAt.isSubmersionAt {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) : Manifold.IsSubmersionAt I J n f x :=
  (hf.isSubmersionAtOfComplement hn).isSubmersionAt

/-- A `C^n` local diffeomorphism (`n ≠ 0`) between boundaryless manifolds is a submersion with
complement `PUnit.{1}`. -/
theorem IsLocalDiffeomorph.isSubmersionOfComplement {f : M → N}
    (hf : IsLocalDiffeomorph I J n f) (hn : n ≠ 0) :
    Manifold.IsSubmersionOfComplement PUnit.{1} I J n f :=
  Manifold.isSubmersionOfComplement_iff.mpr fun x ↦ (hf x).isSubmersionAtOfComplement hn

/-- A `C^n` local diffeomorphism (`n ≠ 0`) between boundaryless manifolds is a submersion. -/
theorem IsLocalDiffeomorph.isSubmersion {f : M → N}
    (hf : IsLocalDiffeomorph I J n f) (hn : n ≠ 0) : Manifold.IsSubmersion I J n f :=
  (hf.isSubmersionOfComplement hn).isSubmersion

/-- A `C^n` diffeomorphism (`n ≠ 0`) between boundaryless manifolds is a submersion with complement
`PUnit.{1}`. -/
theorem Diffeomorph.isSubmersionOfComplement (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) :
    Manifold.IsSubmersionOfComplement PUnit.{1} I J n Φ :=
  Φ.isLocalDiffeomorph.isSubmersionOfComplement hn

/-- A `C^n` diffeomorphism (`n ≠ 0`) between boundaryless manifolds is a submersion. -/
theorem Diffeomorph.isSubmersion (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) :
    Manifold.IsSubmersion I J n Φ := Φ.isLocalDiffeomorph.isSubmersion hn

end LocalDiffeomorph

namespace IsLocalDiffeomorph

open Manifold
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
  {n : ℕ∞ω} {f : M → N}

/-- Precomposing a submersion with a local diffeomorphism of the source gives a submersion. -/
theorem isSubmersion_comp [IsManifold I n M'] {g : M' → M} (hg : IsLocalDiffeomorph I I n g)
    (h : IsSubmersion I J n f) : IsSubmersion I J n (f ∘ g) :=
  (isSubmersionOfComplement_iff.mpr fun x ↦ (hg x).isSubmersionAtOfComplement_comp
    (h.isSubmersionOfComplement_complement.isSubmersionAt (g x))).isSubmersion

/-- Postcomposing a submersion with a local diffeomorphism of the target gives a submersion. -/
theorem comp_isSubmersion [IsManifold J n P] {k : N → P} (hk : IsLocalDiffeomorph J J n k)
    (h : IsSubmersion I J n f) : IsSubmersion I J n (k ∘ f) :=
  (isSubmersionOfComplement_iff.mpr fun x ↦ (hk (f x)).comp_isSubmersionAtOfComplement
    (h.isSubmersionOfComplement_complement.isSubmersionAt x)).isSubmersion

end IsLocalDiffeomorph

namespace Manifold.IsSubmersion

open Module
open scoped Manifold ContDiff

variable {𝕂 : Type*} [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E] [FiniteDimensional 𝕂 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F] [FiniteDimensional 𝕂 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕂 E H} {J : ModelWithCorners 𝕂 F G} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N] {f : M → N}

/-- A `C^n` submersion, `1 ≤ n`, with boundaryless source between manifolds modelled on spaces of
the same finite dimension is a `C^n` local diffeomorphism: its surjective differentials are
injective. -/
theorem isLocalDiffeomorph_of_finrank_eq (h : IsSubmersion I J n f) (hn : 1 ≤ n)
    (hdim : finrank 𝕂 E = finrank 𝕂 F) : IsLocalDiffeomorph I J n f := fun x ↦ by
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕂 E
  have hinj : Function.Injective (mfderiv I J f x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (mfderiv I J f x).toLinearMap) hdim).2
      (h.surjective_mfderiv (zero_lt_one.trans_le hn).ne' x)
  exact TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv (s := Set.univ) h.contMDiff.contMDiffOn
    isOpen_univ (Set.mem_univ x) BoundarylessManifold.isInteriorPoint hn hinj hdim

/-- A `C^n` submersion, `1 ≤ n`, out of a nonempty boundaryless manifold with finite-dimensional
model is a `C^n` local diffeomorphism exactly when the source and target models have the same
dimension. -/
theorem isLocalDiffeomorph_iff_finrank_eq [Nonempty M] (h : IsSubmersion I J n f) (hn : 1 ≤ n) :
    IsLocalDiffeomorph I J n f ↔ finrank 𝕂 E = finrank 𝕂 F := by
  refine ⟨fun hf ↦ ?_, h.isLocalDiffeomorph_of_finrank_eq hn⟩
  obtain ⟨x⟩ := ‹Nonempty M›
  exact ((hf x).mfderivToContinuousLinearEquiv
    (zero_lt_one.trans_le hn).ne').toLinearEquiv.finrank_eq

end Manifold.IsSubmersion
